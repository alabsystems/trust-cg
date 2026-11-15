#!/usr/bin/env python3
"""Check maintained Markdown file links and development-record structure.

Uses only Python's standard library; it runs no Cargo or Targo command.
Archived reports retain historical references and are outside the live-link gate.
The AArch64 acceptance template and trusted-base ledger are also checked for
structure: every row, field, milestone gate, island citation and closure-ledger
gap assignment must be present and consistent, and each island's LOC and
status must agree between the ledger's index and its section. Each closure gap
needs one index row, one section and one valid section status, and the
ledger's declared completion cannot hide an unresolved gap. This is
about the completeness of the record's shape, never about the truth of the
evidence a filled record cites.
"""

from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
import re
import sys
from typing import Optional
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]
DIAGNOSTICS_CENSUS = Path(__file__).resolve().parent / "generate_diagnostics_inventory.py"
PUBLIC_DOCS = (
    "README.md", "ARCHITECTURE.md", "CONTRIBUTING.md",
    "LIMITATIONS.md", "SOUNDNESS_CHECK.md", "metrics-contract.md",
    "rustc-mir-coverage-inventory.md", "trust-cg-full-replacement-ledger.md",
)
ACCEPTANCE_TEMPLATE = "docs/aarch64-acceptance-report-template.md"
CLOSURE_LEDGER = "docs/aarch64-completion-audit-2026-09-17.md"
TRUSTED_BASE_LEDGER = "docs/trusted-base-ledger.md"
DEVELOPMENT_DOCS = (
    "CLAUDE.md", "ROADMAP.md", "docs/README.md", "docs/archive/README.md",
    "docs/linux-aarch64-completion.md", "docs/darwin-aarch64-completion.md",
    "docs/completion-progress.md",
    ACCEPTANCE_TEMPLATE, TRUSTED_BASE_LEDGER,
)
LINK = re.compile(r"\]\((?:<([^>]+)>|([^\s()]+))(?:\s+\"[^\"]*\")?\)")
HTML_LINK = re.compile(r"\b(?:href|src)=[\"']([^\"']+)[\"']")

# The completion contract's fourteen rows and the fields every closure record
# must state (docs/linux-aarch64-completion.md, "How the owner can verify").
ACCEPTANCE_ROWS = tuple(f"L{number:02d}" for number in range(1, 15))
ACCEPTANCE_ROW_FIELDS = (
    "Contract", "Revisions", "Identities", "Commands", "Denominator",
    "Positive outcomes", "Negative controls", "Independent checks", "Artifacts",
    "Remaining trusted base", "Ledger gaps", "Milestone gates", "Verdict",
)
# The July roadmap's M4-M6 acceptance predicates and its G3 island ledger. A
# template that drops one lets a closure record omit a governing gate.
MILESTONE_GATES = (
    "M4-CACHEDVERIFIED-DEFAULT", "M4-UNCHECKED-OPT-IN",
    "M4-PUBLISHED-BYTES-CERTIFIED", "M4-JIT-PINS", "M4-JIT-LATENCY",
    "M5-ENC5", "M5-ENC4-BINDING", "M5-PACKED-COVERED", "M5-G1B-VECTOR",
    "M6-GATE-SB", "M6-COMPLETE5", "M6-NO-STATISTICAL", "M6-NO-UNCHECKED-JIT",
    "M6-SOUNDNESS-GREEN", "M6-ENC10-META", "M6-DOCS-TRUTH", "G3-ISLAND-LEDGER",
)
ISLAND_FIELDS = ("Location", "LOC", "Trusted for", "Mitigations", "Status", "Shrinks when")
ISLAND_STATUSES = ("TRUSTED", "PARTIAL", "CHECKER", "DEBT", "ORACLE", "RETIRED")
ISLAND_ID = re.compile(r"\bTB-\d{2}\b")
# An island's LOC is a `wc -l` count or the explicit words "not measured"; the
# section's LOC field must start with the same value as the index row.
ISLAND_LOC = re.compile(r"(not measured|\d{1,3}(?:,\d{3})*)(?![\d,])")
# The ledger rules require a retired island to name the replacing commit.
RETIRED_STATUS = re.compile(r"RETIRED [0-9a-f]{7,40}\b")
GATE_ID = re.compile(r"\b(?:M[4-6](?:-[A-Z0-9]+)+|G3-ISLAND-LEDGER)\b")
ROW_ID = re.compile(r"\bL(\d{2})\b(?:\s*[–-]\s*L(\d{2})\b)?")
FIELD = re.compile(r"^- \*\*([^*]+):\*\*(.*)$")
GAP_ID = re.compile(r"\b(?:L\d{2}-P\d+|C-\d{2}|X-[A-Z]+-P\d+)\b")
GAP_RANGE = re.compile(r"\b((?:L\d{2}|X-[A-Z]+)-P)(\d+)\s*[–-]\s*\1(\d+)\b")


def check_links() -> list[str]:
    errors = []
    # Development-only documents are deliberately absent from public snapshots.
    paths = [ROOT / name for name in PUBLIC_DOCS]
    paths.extend(ROOT / name for name in DEVELOPMENT_DOCS if (ROOT / name).exists())
    for path in paths:
        if not path.is_file():
            errors.append(f"missing maintained document: {path.relative_to(ROOT)}")
            continue
        fenced = False
        for line_number, line in enumerate(path.read_text().splitlines(), 1):
            if line.lstrip().startswith(("```", "~~~")):
                fenced = not fenced
                continue
            if fenced:
                continue
            targets = [a or b for a, b in LINK.findall(line)] + HTML_LINK.findall(line)
            for target in targets:
                parsed = urlsplit(target)
                if parsed.scheme or parsed.netloc or not parsed.path:
                    continue
                destination = path.parent / unquote(parsed.path)
                if not destination.exists():
                    errors.append(f"{path.relative_to(ROOT)}:{line_number}: missing {target}")
    return errors


def _sections(text: str, heading: re.Pattern) -> list[tuple[re.Match, list[str]]]:
    """Split text at lines matching `heading`; a body ends at any `#` heading."""
    sections: list[tuple[re.Match, list[str]]] = []
    current = None
    for line in text.splitlines():
        match = heading.match(line)
        if match:
            current = (match, [])
            sections.append(current)
        elif line.startswith("#"):
            current = None
        elif current is not None:
            current[1].append(line)
    return sections


def _fields(lines: list[str]) -> tuple[dict[str, str], list[str]]:
    """Collect `- **Name:** text` list fields with their indented continuations."""
    fields: dict[str, str] = {}
    duplicates: list[str] = []
    name = None
    for line in lines:
        match = FIELD.match(line)
        if match:
            name = match.group(1)
            if name in fields:
                duplicates.append(name)
            fields[name] = match.group(2).strip()
        elif name is not None and line.startswith("  ") and line.strip():
            fields[name] += " " + line.strip()
        else:
            name = None
    return fields, duplicates


def _table_rows(text: str, first_cell: re.Pattern) -> list[list[str]]:
    rows = []
    for line in text.splitlines():
        if not line.startswith("|"):
            continue
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if cells and first_cell.fullmatch(cells[0]):
            rows.append(cells)
    return rows


def _row_ids(text: str) -> set[str]:
    rows = set()
    for match in ROW_ID.finditer(text):
        first = int(match.group(1))
        last = int(match.group(2)) if match.group(2) else first
        rows.update(f"L{number:02d}" for number in range(first, last + 1))
    return rows


def _gap_ids(text: str) -> set[str]:
    gaps = set(GAP_ID.findall(text))
    for match in GAP_RANGE.finditer(text):
        prefix, first, last = match.group(1), int(match.group(2)), int(match.group(3))
        gaps.update(f"{prefix}{number}" for number in range(first, last + 1))
    return gaps


def closure_ledger_gap_ids(text: str) -> set[str]:
    """Gap IDs in the closure ledger's gap index table."""
    return {cells[0] for cells in _table_rows(text, GAP_ID)}


def closure_ledger_errors(text: str) -> list[str]:
    """Check gap accounting, without treating a closure label as proof.

    Each gap has one index row (its ID column feeds the acceptance template's
    assignment check) and one section whose single `Status:` line is its only
    status record. Totals are not restated; `closure_ledger.py counts`
    computes them.
    """
    errors: list[str] = []
    status_pattern = re.compile(r"(?:OPEN|PARTIAL)(?: [0-9a-f]{7,40})?|(?:CLOSED|WITHDRAWN) [0-9a-f]{7,40}")
    index: set[str] = set()
    for cells in _table_rows(text, GAP_ID):
        gap = cells[0]
        if len(cells) < 5 or not all(cells[:5]):
            errors.append(f"gap index row {gap} lacks a required column")
            continue
        if gap in index:
            errors.append(f"duplicate gap index row {gap}")
        index.add(gap)
    if not index:
        errors.append("gap index has no gap rows")

    sections: dict[str, list[str]] = {}
    for match, lines in _sections(text, re.compile(r"^### (" + GAP_ID.pattern + r")\s")):
        gap = match.group(1)
        if gap in sections:
            errors.append(f"duplicate gap section {gap}")
        sections[gap] = lines
    for gap in sorted(index - sections.keys()):
        errors.append(f"gap {gap} has an index row but no section")
    for gap in sorted(sections.keys() - index):
        errors.append(f"gap {gap} has a section but no index row")
    unresolved = 0
    for gap, lines in sections.items():
        declarations = [line.removeprefix("Status:").strip() for line in lines if line.startswith("Status:")]
        if len(declarations) != 1:
            errors.append(f"gap {gap} needs exactly one section status")
            continue
        status = declarations[0]
        if not status_pattern.fullmatch(status):
            errors.append(f"gap {gap} has invalid status {status!r}; CLOSED/WITHDRAWN require a commit")
        if status.split()[:1] not in (["CLOSED"], ["WITHDRAWN"]):
            unresolved += 1

    headline = re.findall(r"^Status: \*\*([A-Z ]+)\*\*", text, re.MULTILINE)
    if len(headline) != 1:
        errors.append("closure ledger needs exactly one status headline")
    elif unresolved and headline[0] != "OPEN":
        errors.append("closure ledger cannot declare completion with unresolved gaps")
    return errors


def trusted_base_ledger_errors(text: str) -> tuple[set[str], list[str]]:
    """Return the ledger's island IDs and its structural errors."""
    errors: list[str] = []
    index: dict[str, str] = {}
    index_loc: dict[str, str] = {}
    for cells in _table_rows(text, ISLAND_ID):
        if len(cells) != 4 or not all(cells):
            errors.append(f"island index row {cells[0]} must have ID, island, LOC and status")
            continue
        island, _, loc, status = cells
        if island in index:
            errors.append(f"duplicate island index row {island}")
        index[island] = status
        index_loc[island] = loc
        if not ISLAND_LOC.fullmatch(loc):
            errors.append(f"island {island} LOC must be a wc -l count or 'not measured', got {loc!r}")
    if not index:
        errors.append("island index has no TB-NN rows")
    for island, status in index.items():
        if status.split()[0] not in ISLAND_STATUSES:
            errors.append(f"island {island} index status {status!r} is not one of {', '.join(ISLAND_STATUSES)}")
        elif status.split()[0] == "RETIRED" and not RETIRED_STATUS.match(status):
            errors.append(f"island {island} index status must name the replacing commit as 'RETIRED <commit>', got {status!r}")
    sections = {}
    for match, lines in _sections(text, re.compile(r"^### (TB-\d{2}) — \S")):
        island = match.group(1)
        if island in sections:
            errors.append(f"duplicate island section {island}")
        sections[island] = lines
    for island in sorted(set(index) - set(sections)):
        errors.append(f"island {island} has an index row but no section")
    for island in sorted(set(sections) - set(index)):
        errors.append(f"island {island} has a section but no index row")
    for island, lines in sorted(sections.items()):
        fields, duplicates = _fields(lines)
        for name in duplicates:
            errors.append(f"island {island} repeats field {name}")
        for name in ISLAND_FIELDS:
            if not fields.get(name):
                errors.append(f"island {island} lacks field {name}")
        status = fields.get("Status", "")
        word_match = re.match(r"[A-Z]+", status)
        word = word_match.group(0) if word_match else ""
        if island in index and word != index[island].split()[0]:
            errors.append(f"island {island} section status {word!r} disagrees with index {index[island]!r}")
        if word == "RETIRED" and not RETIRED_STATUS.match(status):
            errors.append(f"island {island} section status must name the replacing commit as 'RETIRED <commit>', got {status!r}")
        loc_match = ISLAND_LOC.match(fields.get("LOC", ""))
        if island in index_loc and fields.get("LOC") and (
            loc_match is None or loc_match.group(1) != index_loc[island]
        ):
            errors.append(
                f"island {island} section LOC {fields['LOC']!r} does not start with the index LOC {index_loc[island]!r}"
            )
    return set(index), errors


def acceptance_template_errors(
    text: str, islands: set[str], ledger_gaps: Optional[set[str]] = None,
) -> list[str]:
    """Check the template's rows, fields, gate mapping and citations.

    With `ledger_gaps`, every closure-ledger gap must be assigned to a record
    and every assigned gap must exist in the closure ledger.
    """
    errors: list[str] = []
    sections = _sections(text, re.compile(r"^## (L\d{2}) — \S"))
    order = [match.group(1) for match, _ in sections]
    if order != list(ACCEPTANCE_ROWS):
        errors.append(f"row sections must be exactly {ACCEPTANCE_ROWS[0]}..{ACCEPTANCE_ROWS[-1]} in order, found {order}")
    row_gates: dict[str, set[str]] = {}
    cited: set[str] = set()
    for match, lines in sections:
        row = match.group(1)
        fields, duplicates = _fields(lines)
        for name in duplicates:
            errors.append(f"row {row} repeats field {name}")
        for name in ACCEPTANCE_ROW_FIELDS:
            if not fields.get(name):
                errors.append(f"row {row} lacks field {name}")
        base = set(ISLAND_ID.findall(fields.get("Remaining trusted base", "")))
        if fields.get("Remaining trusted base") and not base:
            errors.append(f"row {row} names no trusted-base island")
        for island in sorted(base - islands):
            errors.append(f"row {row} cites unknown trusted-base island {island}")
        cited |= base
        row_gates[row] = set(GATE_ID.findall(fields.get("Milestone gates", "")))
        verdict = fields.get("Verdict", "")
        if verdict and not verdict.startswith("OPEN"):
            errors.append(f"row {row} verdict must stay OPEN in the template, got {verdict!r}")
    for island in sorted(islands - cited):
        errors.append(f"trusted-base island {island} is cited by no row")
    mapped: dict[str, set[str]] = {}
    for cells in _table_rows(text, GATE_ID):
        gate = cells[0]
        if len(cells) != 5 or not all(cells):
            errors.append(f"milestone gate row {gate} must have gate, source, predicate, rows and state")
            continue
        if gate in mapped:
            errors.append(f"duplicate milestone gate row {gate}")
        rows = _row_ids(cells[3])
        if not rows:
            errors.append(f"milestone gate {gate} maps to no row")
        for row in sorted(rows - set(ACCEPTANCE_ROWS)):
            errors.append(f"milestone gate {gate} maps to unknown row {row}")
        mapped[gate] = rows
    for gate in MILESTONE_GATES:
        if gate not in mapped:
            errors.append(f"milestone gate {gate} is not mapped to any row")
    for row in ACCEPTANCE_ROWS:
        expected = {gate for gate, rows in mapped.items() if row in rows}
        listed = row_gates.get(row, set())
        for gate in sorted(expected - listed):
            errors.append(f"row {row} omits milestone gate {gate} that maps to it")
        for gate in sorted(listed - expected):
            errors.append(f"row {row} lists milestone gate {gate} that does not map to it")
    if ledger_gaps is not None:
        assigned: set[str] = set()
        for _, lines in _sections(text, re.compile(r"^#+ ")):
            assigned |= _gap_ids(_fields(lines)[0].get("Ledger gaps", ""))
        for gap in sorted(ledger_gaps - assigned):
            errors.append(f"closure-ledger gap {gap} is assigned to no record")
        for gap in sorted(assigned - ledger_gaps):
            errors.append(f"assigned gap {gap} is not in the closure ledger")
    verdicts = {cells[0]: cells[1] for cells in _table_rows(text, re.compile(r"L\d{2}")) if len(cells) == 2}
    for row in ACCEPTANCE_ROWS:
        if verdicts.get(row) != "OPEN":
            errors.append(f"acceptance verdict table must list {row} as OPEN, got {verdicts.get(row)!r}")
    return errors


def acceptance_document_errors(root: Path = ROOT) -> list[str]:
    """Structure check for the AArch64 acceptance template and trusted-base ledger.

    These and the closure ledger live in the development `docs/` tree, which
    public snapshots omit entirely. Without `docs/` there is nothing to check;
    with it, all three documents are required.
    """
    if not (root / "docs").is_dir():
        return []
    documents = (ACCEPTANCE_TEMPLATE, TRUSTED_BASE_LEDGER, CLOSURE_LEDGER)
    paths = {name: root / name for name in documents}
    missing = [name for name, path in paths.items() if not path.is_file()]
    if missing:
        return [f"missing maintained document: {name}" for name in missing]
    islands, ledger_errors = trusted_base_ledger_errors(paths[TRUSTED_BASE_LEDGER].read_text())
    errors = [f"{TRUSTED_BASE_LEDGER}: {error}" for error in ledger_errors]
    closure_text = paths[CLOSURE_LEDGER].read_text()
    gaps = closure_ledger_gap_ids(closure_text)
    errors.extend(f"{CLOSURE_LEDGER}: {error}" for error in closure_ledger_errors(closure_text))
    template_errors = acceptance_template_errors(paths[ACCEPTANCE_TEMPLATE].read_text(), islands, gaps)
    errors.extend(f"{ACCEPTANCE_TEMPLATE}: {error}" for error in template_errors)
    return errors

def diagnostics_census_errors(root: Path = ROOT) -> list[str]:
    """Drift in the generated `[TCG-*]` code census of docs/diagnostics.md.

    docs/ is withheld from public snapshots (publish/manifest.txt), so the gate
    applies whenever that directory exists; a missing census document inside it
    is an error, not a skip.
    """
    if not (root / "docs").is_dir():
        return []
    spec = importlib.util.spec_from_file_location("generate_diagnostics_inventory", DIAGNOSTICS_CENSUS)
    if spec is None or spec.loader is None:
        raise OSError(f"cannot load {DIAGNOSTICS_CENSUS}")
    census = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = census
    spec.loader.exec_module(census)
    return census.check_errors(root)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--links", action="store_true", help="check maintained document file links and acceptance-document structure only")
    mode.add_argument("--check", action="store_true",
                      help="check maintained links, acceptance-document structure and the diagnostic code census (default)")
    args = parser.parse_args()
    try:
        errors = check_links()
        errors.extend(acceptance_document_errors())
        if not args.links:
            errors.extend(diagnostics_census_errors())
    except (OSError, ValueError, KeyError) as error:
        print(f"documentation check failed: {error}", file=sys.stderr)
        return 2
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print("Maintained file links, development records and the diagnostic code census are current."
          if not args.links else "Maintained document file links are valid.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
