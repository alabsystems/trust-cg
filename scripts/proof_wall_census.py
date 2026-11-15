#!/usr/bin/env python3
"""Reduce opcode-inventory census traces into the proof-wall census.

Measure: compile each unit through the rustc bridge with certificates on and
the census knob set, keeping stderr per unit, for example

    trustc -Ztrust-verify=off -Zcodegen-backend=<backend> \\
        "-Ztrust-ir-cg-args=opcode-inventory-trace solve-trace" \\
        --edition=2021 --crate-type bin --target aarch64-apple-darwin \\
        -Cpanic=abort -Copt-level=3 -o out/p3_gcd p3_gcd.rs 2> logs/p3_gcd.stderr.txt

(`opcode-inventory-trace` prints one `[TCG-OPCODE-INVENTORY] v1` summary line
per verified function and one row line per emitted instruction that blocks
proof promotion, with its verifier reason; `solve-trace` adds one
`TCG_SOLVE_TRACE promotion_result` line per live formal replay, counted with
the first verification of the function whose census lines follow it), then
reduce:

    python3 scripts/proof_wall_census.py logs/*.stderr.txt --json census.json \\
        --markdown census.md

Each log's unit name is its file name up to the first `.`. Every blocking row is
put in exactly one class (CLASSES, first match wins), keyed on its opcode and
the stable reason prefixes the verifier writes. `--compare BEFORE AFTER` prints
the per-class change between two reduced JSON files. Each
`[TCG-SOURCE-BOUND-MEMORY] v1` line (`solve-trace`; one per memory row a
source-bound owner bound, first verification counted) is tallied by binding
kind and outcome, and each `[TCG-SOURCE-BOUND-MEMORY] v1\tunbound` line (a
function with memory rows the memory-leaf checker did not bind) by its
refusal.

A census is testing evidence about which rows a corpus reached, not a proof and
not a measurement of time. The knobs are diagnostics that change no verdict.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

TAG = "[TCG-OPCODE-INVENTORY] v1"
FORMAT = "trust-cg.proof-wall-census.v1"

# The AArch64 pair-memory opcodes. Their evidence is blocked on AY/Clean
# capability owned elsewhere (ledger L07-P2), so they are counted as one class
# whatever their row's reason, which the class-by-reason table still shows.
PAIR_MEMORY = frozenset(
    f"AArch64::{op}"
    for op in ("StpPreIndex", "LdpPostIndex", "LdpRI", "StpRI", "NeonStpQPost", "NeonLdpQPost")
)

# (class, predicate over (opcode, status, detail)), in precedence order.
REGISTRY = "no operand-exact evidence: registry name lookup is not proof credit"
STATISTICAL = "no complete evidence: statistical sampling is not proof credit"
INSTRUCTION_DERIVED = "no checked certificate: an instruction-derived obligation is not proof credit"
# The clause an uncredited scalar or pair memory row carries LAST, after its
# lane's reason and the Formal-only bound-memory note, when the word-bound
# memory-effect decomposition of its word judged it (`with_memory_effect`).
MEMORY_EFFECT = "word-bound memory effect (a refutation check; its certificates are recorded, never credit)"
MEMORY_EFFECT_EVERY_PART = "every part has a Clean-checked certificate"
MEMORY_EFFECT_REPLAY_NOT_REQUESTED = "live replay not requested: the diagnostic `memory-effect-replay` knob is off"
# The clause an uncredited memory row carries when a source-bound owner bound
# it (`aarch64_memory_source_binding`): a frame record of a source-bound frame,
# or a scalar access of a source-bound memory leaf, without a Clean-checked
# certificate of every memory-effect part.
SOURCE_BOUND_MEMORY = (
    "source-bound memory row (credited only when every memory-effect part has a Clean-checked "
    "certificate of its exact query)"
)
# One line per bound memory row, printed under `solve-trace`.
SOURCE_BOUND_TAG = "[TCG-SOURCE-BOUND-MEMORY] v1"
# The Formal-only bound-memory rule's note (owner ruling 2026-09-29,
# `bound_memory_authority`) and the status phrases the census keys on.
BOUND_MEMORY_FORMAL_ONLY = (
    "bound-memory rows are credited only by a checker-accepted certificate of their form theorem "
    "(owner ruling 2026-09-29)"
)
CHECKER_IDENTITY_MISS = "a checker-identity miss, not a proof gap"
BOUND_MEMORY_REFUTATION_NOT_RUN = (
    "no in-process refutation check ran and held on this row (the pair lane's concrete-word "
    "obligation, or the instruction-derived obligation of a general-purpose scalar load or store), "
    "so nothing ties this instruction to the certified form"
)
BOUND_MEMORY_BINDING_MISMATCH = "the certified form is not the form of the word this row's refutation check judged"
CERTIFICATE_REPLAY_OFF = (
    "certificates are replayed only under the proof-promotion policy (SourceBoundReplay); "
    "this walk is evaluation-only"
)


def memory_effect_clause(detail: str) -> str | None:
    """The memory-effect clause of a row, without its leading constant, or None."""
    marker = f"; {MEMORY_EFFECT}: "
    return detail.split(marker, 1)[1] if marker in detail else None


CLASSES = (
    # A memory row a source-bound owner bound to its source (a frame record
    # or a leaf access) that is not credited: some part of its word has no
    # Clean-checked certificate. Its own row keeps every other reason.
    ("source-bound-memory-uncertified", lambda op, st, d: SOURCE_BOUND_MEMORY in d),
    # An uncredited memory row every part of whose word-bound memory-effect
    # decomposition has a Clean-checked certificate. Still not credit: the
    # Formal-only rule admits only a replayed certificate of the row's form
    # theorem. Every other memory row keeps the class of its lane's reason.
    (
        "memory-effect-checked",
        lambda op, st, d: MEMORY_EFFECT_EVERY_PART in (memory_effect_clause(d) or ""),
    ),
    ("pair-memory", lambda op, st, d: op in PAIR_MEMORY),
    ("registry-name-lookup", lambda op, st, d: d.startswith(REGISTRY)),
    ("statistical-only", lambda op, st, d: d.startswith(STATISTICAL)),
    ("instruction-derived-uncertified", lambda op, st, d: d.startswith(INSTRUCTION_DERIVED)),
    ("ay-unknown-timeout", lambda op, st, d: st == "failed" and d.startswith("Unknown:")),
    (
        "no-checked-replay",
        lambda op, st, d: st == "unverified" and "needs independently replayed proof" in d,
    ),
    ("refuted", lambda op, st, d: st == "failed"),
    ("no-mapping", lambda op, st, d: st == "unverified"),
)
CLASS_ORDER = tuple(name for name, _ in CLASSES) + ("precondition", "other")

# Live formal replay outcomes (`TCG_SOLVE_TRACE promotion_result ... result=X`):
# `SolverUnsat` is an AY unsat the independent checker did not accept.
REPLAY = re.compile(r"TCG_SOLVE_TRACE promotion_result obligation=(\".*?\"|\S+) result=(\w+)")
REPLAY_CLASS = {
    "Verified": "checked-proof",
    "SolverUnsat": "checker-rejection",
    "Timeout": "ay-unknown-timeout",
    "Unknown": "ay-unknown-timeout",
    "Error": "ay-error",
    "CounterExample": "counterexample",
}


def classify(opcode: str, status: str, detail: str) -> str:
    for name, predicate in CLASSES:
        if predicate(opcode, status, detail):
            return name
    return "other"


def memory_effect_key(clause: str) -> str:
    """How far a memory-effect clause's parts got: every part checked; `k`
    parts checked and the first part without a certificate with the kind of
    reason (the AY outcome's name, or the refusal); or undecided in process."""
    if MEMORY_EFFECT_EVERY_PART in clause:
        return MEMORY_EFFECT_EVERY_PART
    if "` is undecided in process:" in clause:
        return "is undecided in process"
    counted = re.search(r"; (\d+) of \d+ parts have a Clean-checked certificate(.*)$", clause)
    if not counted:
        return "(unparsed)"
    checked, tail = counted.groups()
    first = re.search(r"the first without one is `([^`]+)` \((.*)\)$", tail)
    if first:
        part = re.sub(r"\d+", "N", first.group(1))
        why = re.split(r"[(:]", first.group(2), maxsplit=1)[0].strip()
        return f"{checked} parts checked; first without one: {part} ({why})"
    return f"{checked} parts checked{tail}"


def bound_memory_key(detail: str) -> str | None:
    """Why the Formal-only bound-memory rule left a row uncredited, or None
    for a row that carries no bound-memory note."""
    if BOUND_MEMORY_FORMAL_ONLY not in detail:
        return None
    note = (
        detail.split(BOUND_MEMORY_FORMAL_ONLY, 1)[1]
        .split(f"; {MEMORY_EFFECT}: ", 1)[0]
        .split(f"; {SOURCE_BOUND_MEMORY}: ", 1)[0]
    )
    if CHECKER_IDENTITY_MISS in note:
        return "checker-identity miss"
    if CERTIFICATE_REPLAY_OFF in note:
        return "certificate replay off"
    if "no form theorem binds this instruction" in note:
        return "no form theorem binds it"
    if BOUND_MEMORY_REFUTATION_NOT_RUN in note:
        return "no refutation check ran"
    if BOUND_MEMORY_BINDING_MISMATCH in note:
        return "form is not the judged word's"
    head = re.sub(r"`[^`]*`", "`_`", note).strip("; ")
    return re.sub(r"\d+", "N", head.split(":", 1)[-1].strip())[:120] or "(empty)"


def source_bound_key(detail: str) -> str | None:
    """How far a source-bound memory row's parts got, or None for a row
    without the source-bound clause."""
    marker = f"{SOURCE_BOUND_MEMORY}: "
    if marker not in detail:
        return None
    clause = detail.split(marker, 1)[1]
    if "` is undecided in process:" in clause:
        return "is undecided in process"
    counted = re.search(r"(\d+) of \d+ parts have a Clean-checked certificate(.*)$", clause)
    if counted:
        checked, tail = counted.groups()
        first = re.search(r"the first without one is `([^`]+)` \((.*)\)$", tail)
        if first:
            part = re.sub(r"\d+", "N", first.group(1))
            why = re.split(r"[(:]", first.group(2), maxsplit=1)[0].strip()
            return f"{checked} parts checked; first without one: {part} ({why})"
        return f"{checked} parts checked"
    refused = re.search(r"receipt \d+ refused \((.*)\)$", clause)
    if refused:
        return f"receipt refused ({refused.group(1)})"
    return re.sub(r"\d+", "N", re.sub(r"`[^`]*`", "`_`", clause))[:120]


def reason_key(detail: str) -> str:
    """The row's reason with instance-specific text dropped: the prefix for the
    credit-withdrawal reasons (for an instruction-derived row, with how it was
    decided), else the text before any backquote, digit run collapsed. A
    memory row's bound-memory status and memory-effect clause follow it, after
    ` · ` (never `|`, which would split a Markdown table cell). A frame
    record's reason is the source-bound clause alone."""
    if detail.startswith(f"{SOURCE_BOUND_MEMORY}: "):
        return f"{SOURCE_BOUND_MEMORY} · source-bound memory: {source_bound_key(detail)}"
    lane = (
        detail.split(f"; {BOUND_MEMORY_FORMAL_ONLY}", 1)[0]
        .split(f"; {MEMORY_EFFECT}: ", 1)[0]
        .split(f"; {SOURCE_BOUND_MEMORY}: ", 1)[0]
    )
    if lane.startswith(INSTRUCTION_DERIVED):
        decided = re.search(r"` (holds \(.*?\)|is undecided)(?:; it binds|:)", lane)
        key = f"{INSTRUCTION_DERIVED}: {decided.group(1) if decided else '(unparsed)'}"
    else:
        key = next((prefix for prefix in (REGISTRY, STATISTICAL) if lane.startswith(prefix)), None)
        if key is None:
            head = lane.split("`", 1)[0].strip().rstrip(":")
            key = re.sub(r"\d+", "N", head) or "(empty)"
    bound = bound_memory_key(detail)
    if bound is not None:
        key += f" · bound memory: {bound}"
    clause = memory_effect_clause(detail)
    if clause is not None:
        key += f" · memory effect: {memory_effect_key(clause)}"
    bound_source = source_bound_key(detail)
    if bound_source is not None:
        key += f" · source-bound memory: {bound_source}"
    return key


def unbound_reason(reason: str) -> str:
    """A memory-leaf refusal with instance text dropped: an unsupported
    instruction keeps only its opcode's name (`instruction 3: Call { .. }`
    becomes `instruction: Call`), and digit runs collapse."""
    head, sep, tail = reason.partition(": instruction ")
    if sep:
        opcode = re.match(r"(?:InstId\(\d+\)|\d+): ([A-Za-z0-9_]+)", tail)
        head += ": instruction: " + (opcode.group(1) if opcode else "?")
    head = re.sub(r"`[^`]*`", "`_`", head)
    return re.sub(r"\d+", "N", head)[:160] or "(empty)"


def source_bound_outcome(outcome: str) -> str:
    """The class of a `[TCG-SOURCE-BOUND-MEMORY]` line's outcome: its leading
    words, before any `:` or `(`."""
    head = re.split(r"[:(;]", outcome, maxsplit=1)[0].strip()
    return head or "(empty)"


def parse_fields(line: str) -> tuple[str, dict[str, str]] | None:
    if not line.startswith(TAG + "\t"):
        return None
    parts = line[len(TAG) + 1 :].split("\t")
    kind, fields = parts[0], {}
    for part in parts[1:]:
        key, sep, value = part.partition("=")
        if not sep:
            return None
        fields[key] = value
    return kind, fields


def unit_name(path: Path) -> str:
    return path.name.split(".", 1)[0]


def reduce(logs: list[tuple[str, str]]) -> dict:
    """Reduce (unit, stderr text) pairs into the census document.

    A function's lines are contiguous: its `summary` line, then its
    `precondition` or `row` lines. The bridge can verify one symbol more than
    once in a compile (a retry, or a trapping stub after a refused body), so
    only the FIRST verification of each (unit, function) is counted; later
    ones are tallied in `repeat_verifications`, and those whose summary
    differs from the first in `repeat_summary_differs`.

    A live formal replay line carries no function name. It is printed while
    its function is verified, before that function's census lines, so it is
    attributed to the next `summary` line in its log: counted when that
    summary is a first verification, and tallied in `ignored_replays` when it
    is a repeat or when no summary follows. The attribution is by stream
    position; functions verified concurrently can interleave their lines."""
    functions: dict[tuple[str, str], dict] = {}
    rows: dict[tuple[str, str, str], tuple[str, str, str]] = {}
    preconditions: dict[tuple[str, str], str] = {}
    repeats = 0
    repeats_differ = 0
    malformed = 0
    replays: dict[str, int] = defaultdict(int)
    replay_names: dict[tuple[str, str], int] = defaultdict(int)
    ignored_replays = 0
    # First line per (unit, function, instruction) of each bound memory row,
    # and per (unit, function) of each function the memory-leaf checker did
    # not bind although it has memory rows.
    bound: dict[tuple[str, str, str], tuple[str, str, str]] = {}
    unbound: dict[tuple[str, str], tuple[str, int]] = {}
    for unit, text in logs:
        current: tuple[str, str] | None = None
        pending: list[tuple[str, str]] = []
        for line in text.splitlines():
            if line.startswith(SOURCE_BOUND_TAG + "\tunbound\t"):
                fields = dict(
                    part.partition("=")[::2]
                    for part in line[len(SOURCE_BOUND_TAG) + len("\tunbound\t") :].split("\t")
                )
                unbound.setdefault(
                    (unit, fields.get("function", "")),
                    (unbound_reason(fields.get("reason", "")), int(fields.get("memory_rows", "0") or 0)),
                )
                continue
            if line.startswith(SOURCE_BOUND_TAG + "\t"):
                fields = dict(
                    part.partition("=")[::2] for part in line[len(SOURCE_BOUND_TAG) + 1 :].split("\t")
                )
                key = (unit, fields.get("function", ""), fields.get("inst", ""))
                kind = fields.get("binding", "").split(":", 1)[0]
                bound.setdefault(
                    key, (kind, source_bound_outcome(fields.get("outcome", "")), fields.get("opcode", ""))
                )
                continue
            match = REPLAY.search(line)
            if match:
                pending.append((REPLAY_CLASS.get(match.group(2), "other"), match.group(1).strip('"')))
                continue
            parsed = parse_fields(line)
            if parsed is None:
                continue
            kind, fields = parsed
            function = fields.get("function", "")
            if kind == "summary":
                key = (unit, function)
                value = {
                    "rows": int(fields["rows"]),
                    "blocking": int(fields["blocking"]),
                    "promotable": fields["promotable"] == "true",
                }
                if key in functions:
                    repeats += 1
                    repeats_differ += functions[key] != value
                    current = None
                    ignored_replays += len(pending)
                else:
                    functions[key] = value
                    current = key
                    for outcome, name in pending:
                        replays[outcome] += 1
                        replay_names[(outcome, name)] += 1
                pending = []
                continue
            if current != (unit, function):
                if current is None and (unit, function) not in functions:
                    malformed += 1
                continue
            if kind == "precondition":
                preconditions.setdefault((unit, function), fields.get("detail", ""))
            elif kind == "row":
                key = (unit, function, fields["index"])
                if key in rows:
                    malformed += 1
                    continue
                rows[key] = (fields["opcode"], fields["status"], fields.get("detail", ""))
        ignored_replays += len(pending)

    by_class: dict[str, dict] = {c: {"functions": set(), "instances": 0, "opcodes": set()} for c in CLASS_ORDER}
    by_opcode: dict[tuple[str, str], dict] = defaultdict(lambda: {"functions": set(), "instances": 0})
    by_reason: dict[tuple[str, str], int] = defaultdict(int)
    refused: set[tuple[str, str]] = set()
    for (unit, function, _index), (opcode, status, detail) in rows.items():
        cls = classify(opcode, status, detail)
        entry = by_class[cls]
        entry["functions"].add((unit, function))
        entry["instances"] += 1
        entry["opcodes"].add(opcode)
        cell = by_opcode[(cls, opcode)]
        cell["functions"].add((unit, function))
        cell["instances"] += 1
        by_reason[(cls, reason_key(detail))] += 1
        refused.add((unit, function))
    for key in preconditions:
        by_class["precondition"]["functions"].add(key)
        by_class["precondition"]["instances"] += 1
        refused.add(key)

    unbound_rows: dict[str, dict] = defaultdict(lambda: {"functions": 0, "memory_rows": 0})
    for (_unit, _function), (reason, count) in unbound.items():
        unbound_rows[reason]["functions"] += 1
        unbound_rows[reason]["memory_rows"] += count
    bound_rows: dict[tuple[str, str], dict] = defaultdict(lambda: {"rows": 0, "functions": set()})
    for (unit, function, _inst), (kind, outcome, _opcode) in bound.items():
        cell = bound_rows[(kind, outcome)]
        cell["rows"] += 1
        cell["functions"].add((unit, function))

    units = sorted({unit for unit, _ in functions} | {unit for unit, _, _ in rows} | {u for u, _ in logs})
    per_unit = []
    for unit in units:
        unit_functions = [key for key in functions if key[0] == unit]
        per_unit.append(
            {
                "unit": unit,
                "functions": len(unit_functions),
                "refused": sum(1 for key in refused if key[0] == unit),
                "blocking_rows": sum(1 for key in rows if key[0] == unit),
            }
        )
    return {
        "format": FORMAT,
        "units": len(units),
        "functions": len(functions),
        "promotable_functions": sum(1 for key, value in functions.items() if value["promotable"] and key not in refused),
        "refused_functions": len(refused),
        "blocking_rows": len(rows),
        "repeat_verifications": repeats,
        "repeat_summary_differs": repeats_differ,
        "ignored_replays": ignored_replays,
        "malformed_lines": malformed,
        "classes": [
            {
                "class": cls,
                "functions": len(by_class[cls]["functions"]),
                "instances": by_class[cls]["instances"],
                "opcodes": len(by_class[cls]["opcodes"]),
            }
            for cls in CLASS_ORDER
        ],
        "opcodes": [
            {
                "class": cls,
                "opcode": opcode,
                "functions": len(cell["functions"]),
                "instances": cell["instances"],
            }
            for (cls, opcode), cell in sorted(
                by_opcode.items(), key=lambda item: (CLASS_ORDER.index(item[0][0]), -item[1]["instances"], item[0][1])
            )
        ],
        "reasons": [
            {"class": cls, "reason": reason, "instances": count}
            for (cls, reason), count in sorted(
                by_reason.items(), key=lambda item: (CLASS_ORDER.index(item[0][0]), -item[1], item[0][1])
            )
        ],
        "replays": [
            {"outcome": outcome, "count": replays[outcome]} for outcome in sorted(replays)
        ],
        "replay_obligations": [
            {"outcome": outcome, "obligation": name, "count": count}
            for (outcome, name), count in sorted(replay_names.items())
        ],
        "per_unit": per_unit,
        "source_bound_memory": [
            {"binding": kind, "outcome": outcome, "rows": cell["rows"], "functions": len(cell["functions"])}
            for (kind, outcome), cell in sorted(bound_rows.items())
        ],
        "source_bound_memory_unbound": [
            {"reason": reason, "functions": cell["functions"], "memory_rows": cell["memory_rows"]}
            for reason, cell in sorted(unbound_rows.items(), key=lambda item: (-item[1]["functions"], item[0]))
        ],
    }


def markdown(census: dict) -> str:
    out = [
        f"Units: {census['units']}. Functions verified: {census['functions']}. "
        f"Promotable: {census['promotable_functions']}. Refused: {census['refused_functions']}. "
        f"Blocking rows: {census['blocking_rows']}. Repeat verifications ignored: "
        f"{census['repeat_verifications']} ({census['repeat_summary_differs']} with a different summary). "
        f"Live replays ignored: {census['ignored_replays']}. "
        f"Malformed lines: {census['malformed_lines']}.",
        "",
        "| Class | Refused functions | Instances | Distinct opcodes |",
        "| --- | ---: | ---: | ---: |",
    ]
    for row in census["classes"]:
        out.append(f"| {row['class']} | {row['functions']} | {row['instances']} | {row['opcodes']} |")
    out += ["", "| Class | Opcode | Functions | Instances |", "| --- | --- | ---: | ---: |"]
    for row in census["opcodes"]:
        out.append(f"| {row['class']} | `{row['opcode']}` | {row['functions']} | {row['instances']} |")
    out += ["", "| Class | Reason | Instances |", "| --- | --- | ---: |"]
    for row in census["reasons"]:
        out.append(f"| {row['class']} | {row['reason']} | {row['instances']} |")
    out += ["", "| Live formal replay outcome | Count |", "| --- | ---: |"]
    for row in census["replays"] or [{"outcome": "(none)", "count": 0}]:
        out.append(f"| {row['outcome']} | {row['count']} |")
    out += [
        "",
        "| Source-bound memory binding | Outcome | Rows | Functions |",
        "| --- | --- | ---: | ---: |",
    ]
    for row in census.get("source_bound_memory") or [
        {"binding": "(none)", "outcome": "-", "rows": 0, "functions": 0}
    ]:
        out.append(f"| {row['binding']} | {row['outcome']} | {row['rows']} | {row['functions']} |")
    out += [
        "",
        "| Memory-leaf refusal (functions with memory rows, unbound) | Functions | Memory rows |",
        "| --- | ---: | ---: |",
    ]
    for row in census.get("source_bound_memory_unbound") or [
        {"reason": "(none)", "functions": 0, "memory_rows": 0}
    ]:
        out.append(f"| {row['reason']} | {row['functions']} | {row['memory_rows']} |")
    out += ["", "| Unit | Functions | Refused | Blocking rows |", "| --- | ---: | ---: | ---: |"]
    for row in census["per_unit"]:
        out.append(f"| {row['unit']} | {row['functions']} | {row['refused']} | {row['blocking_rows']} |")
    return "\n".join(out) + "\n"


def compare(before: dict, after: dict) -> str:
    for doc in (before, after):
        if doc.get("format") != FORMAT:
            raise ValueError(f"not a {FORMAT} document")
    b = {row["class"]: row for row in before["classes"]}
    a = {row["class"]: row for row in after["classes"]}
    out = [
        "| Class | Functions before | Functions after | Instances before | Instances after | Change |",
        "| --- | ---: | ---: | ---: | ---: | ---: |",
    ]
    for cls in CLASS_ORDER:
        fb, fa = b.get(cls, {}).get("functions", 0), a.get(cls, {}).get("functions", 0)
        ib, ia = b.get(cls, {}).get("instances", 0), a.get(cls, {}).get("instances", 0)
        out.append(f"| {cls} | {fb} | {fa} | {ib} | {ia} | {ia - ib:+d} |")
    out.append(
        f"| total (blocking rows) | {before['refused_functions']} | {after['refused_functions']} | "
        f"{before['blocking_rows']} | {after['blocking_rows']} | {after['blocking_rows'] - before['blocking_rows']:+d} |"
    )
    return "\n".join(out) + "\n"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("logs", nargs="*", type=Path, help="per-unit stderr logs")
    ap.add_argument("--json", type=Path, help="write the reduced census JSON here")
    ap.add_argument("--markdown", type=Path, help="write the markdown tables here")
    ap.add_argument("--compare", nargs=2, type=Path, metavar=("BEFORE", "AFTER"),
                    help="print the per-class change between two reduced JSON files")
    args = ap.parse_args(argv)
    if args.compare:
        before, after = (json.loads(path.read_text(encoding="utf-8")) for path in args.compare)
        sys.stdout.write(compare(before, after))
        return 0
    if not args.logs:
        ap.error("give per-unit stderr logs, or --compare BEFORE AFTER")
    census = reduce([(unit_name(p), p.read_text(encoding="utf-8", errors="replace")) for p in args.logs])
    if census["functions"] == 0:
        print("proof_wall_census: no census lines found (was opcode-inventory-trace set?)", file=sys.stderr)
        return 1
    if args.json:
        args.json.write_text(json.dumps(census, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    text = markdown(census)
    if args.markdown:
        args.markdown.write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
