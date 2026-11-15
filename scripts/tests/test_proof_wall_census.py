"""Pin the proof-wall census reducer's input and output formats.

`scripts/proof_wall_census.py` classifies the opcode-inventory census lines the
certificate builder prints under `opcode-inventory-trace`. These tests pin the
line format it parses against the Rust source that writes it, the reason
prefixes it keys on against the verifier's constants, the class precedence, the
deduplication, and the exact shape of the JSON and markdown it writes. They
measure nothing.
"""

import importlib.util
import io
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest
from contextlib import redirect_stdout

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("proof_wall_census", ROOT / "scripts" / "proof_wall_census.py")
CENSUS = importlib.util.module_from_spec(SPEC)
sys.modules["proof_wall_census"] = CENSUS
SPEC.loader.exec_module(CENSUS)

VERIFIER = ROOT / "crates" / "trust-cg-verify" / "src" / "function_verifier.rs"

TAG = CENSUS.TAG


def row(function, index, opcode, status, detail):
    return (
        f"{TAG}\trow\tfunction={function}\tindex={index}\topcode={opcode}\t"
        f"status={status}\tdetail={detail}"
    )


def summary(function, rows, blocking, promotable):
    return (
        f"{TAG}\tsummary\tfunction={function}\trows={rows}\tblocking={blocking}\t"
        f"promotable={'true' if promotable else 'false'}"
    )


SAMPLE = "\n".join(
    [
        "noise before the census",
        summary("f", 5, 4, False),
        row("f", 0, "AArch64::StpPreIndex", "unverified", CENSUS.STATISTICAL + ": `pair` found no counterexample in 100000 sampled inputs"),
        row("f", 1, "AArch64::Movz", "unverified", CENSUS.REGISTRY + ": query `movz #imm16, lsl #0` in Constant Materialization selects a theorem by name"),
        row("f", 2, "AArch64::AddRI", "unverified", CENSUS.STATISTICAL + ": `RECONSTRUCTED add` found no counterexample in 100000 sampled inputs"),
        row("f", 3, "AArch64::Csinv", "unverified", "no proof mapping for opcode Csinv"),
        # The same function verified again in one compile: only the first
        # verification counts, whatever the repeat's rows or replays say.
        'TCG_SOLVE_TRACE promotion_result obligation="Source-bound AArch64 frame" result=Verified',
        summary("f", 5, 4, False),
        row("f", 1, "AArch64::Bl", "unverified", CENSUS.REGISTRY + ": query `branch26 bl == s+a` in Mach-O Emission selects a theorem by name"),
        row("f", 4, "AArch64::Movz", "unverified", CENSUS.REGISTRY + ": query `movz #imm16, lsl #0` in Constant Materialization selects a theorem by name"),
        # A function's live replays precede its census lines.
        'TCG_SOLVE_TRACE promotion_result obligation="Source-bound AArch64 frame" result=SolverUnsat',
        'TCG_SOLVE_TRACE promotion_result obligation="Source-bound AArch64 frame" result=Timeout',
        summary("g", 2, 1, False),
        row("g", 0, "AArch64::TailCall", "unverified", CENSUS.REGISTRY + ": query `branch26 bl == s+a` in Mach-O Emission selects a theorem by name"),
        summary("h", 3, 0, True),
        summary("k", 0, 0, False),
        f"{TAG}\tprecondition\tfunction=k\tdetail=invalid instruction reference 9 in machine block 0",
        # A replay no summary follows belongs to no counted verification.
        'TCG_SOLVE_TRACE promotion_result obligation="Source-bound AArch64 frame" result=Error',
    ]
)


class ReasonPrefixesMatchTheVerifier(unittest.TestCase):
    """The reducer keys on text the verifier writes; drift must fail here."""

    def setUp(self):
        self.source = VERIFIER.read_text(encoding="utf-8")

    def constant(self, name, source=None):
        match = re.search(rf'pub const {name}: &str =\s*"([^"]*)";', source or self.source)
        self.assertIsNotNone(match, name)
        # A Rust string continuation (`\` then a newline) drops the newline and
        # the next line's leading whitespace.
        return re.sub(r"\\\n\s*", "", match.group(1))

    def test_prefixes_are_the_verifier_constants(self):
        self.assertEqual(self.constant("REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT"), CENSUS.REGISTRY)
        self.assertEqual(self.constant("STATISTICAL_EVIDENCE_IS_NOT_CREDIT"), CENSUS.STATISTICAL)
        self.assertEqual(self.constant("INSTRUCTION_DERIVED_IS_NOT_CREDIT"), CENSUS.INSTRUCTION_DERIVED)
        self.assertEqual(self.constant("MEMORY_EFFECT_IS_NOT_CREDIT"), CENSUS.MEMORY_EFFECT)
        self.assertEqual(self.constant("MEMORY_EFFECT_EVERY_PART_CHECKED"), CENSUS.MEMORY_EFFECT_EVERY_PART)
        self.assertEqual(
            self.constant("MEMORY_EFFECT_REPLAY_NOT_REQUESTED"), CENSUS.MEMORY_EFFECT_REPLAY_NOT_REQUESTED
        )
        authority = (VERIFIER.parent / "bound_memory_authority.rs").read_text(encoding="utf-8")
        for name, value in (
            ("BOUND_MEMORY_FORMAL_ONLY", CENSUS.BOUND_MEMORY_FORMAL_ONLY),
            ("CHECKER_IDENTITY_MISS", CENSUS.CHECKER_IDENTITY_MISS),
            ("CERTIFICATE_REPLAY_OFF", CENSUS.CERTIFICATE_REPLAY_OFF),
            ("BOUND_MEMORY_REFUTATION_NOT_RUN", CENSUS.BOUND_MEMORY_REFUTATION_NOT_RUN),
            ("BOUND_MEMORY_BINDING_MISMATCH", CENSUS.BOUND_MEMORY_BINDING_MISMATCH),
        ):
            self.assertEqual(self.constant(name, authority), value)

    def test_memory_effect_row_phrases_are_the_verifiers(self):
        # The fragments `memory_effect_clause` and `memory_effect_key` parse,
        # as `with_memory_effect` writes them.
        for fragment in (
            '"{previous}; {MEMORY_EFFECT_IS_NOT_CREDIT}: `{label}` {decided}; {certificates}"',
            "parts have a Clean-checked certificate; the first \\\n                         without one is `{}` ({why})",
            "parts have a Clean-checked certificate (no live replay under this \\\n                 verification policy)",
            "parts have a Clean-checked certificate ({MEMORY_EFFECT_REPLAY_NOT_REQUESTED})",
            '"is undecided in process: part `{part}`: {reason}"',
        ):
            self.assertIn(fragment, self.source)

    def test_source_bound_memory_phrases_are_the_binding_modules(self):
        binding = (VERIFIER.parent / "aarch64_memory_source_binding.rs").read_text(encoding="utf-8")
        self.assertEqual(self.constant("SOURCE_BOUND_MEMORY_NOT_CREDITED", binding), CENSUS.SOURCE_BOUND_MEMORY)
        self.assertEqual(self.constant("SOURCE_BOUND_MEMORY_TRACE_TAG", binding), CENSUS.SOURCE_BOUND_TAG)
        for fragment in (
            "{checked} of {parts} parts have a Clean-checked certificate; the first without \\\n                 one is `{first}` ({why})",
            "0 of {parts} parts credited: receipt {index} refused ({why})",
            "\\tfunction={}\\tinst={index}\\topcode=AArch64::{:?}\\t\\\n         word={:#010x}\\tbinding={binding}\\tparts={}\\toutcome={outcome}",
        ):
            self.assertIn(fragment, binding)
        self.assertIn(
            '"{SOURCE_BOUND_MEMORY_TRACE_TAG}\\tunbound\\tfunction={}\\tmemory_rows={rows}\\treason={}"',
            binding,
        )
        for fragment in (
            '"{previous}; {SOURCE_BOUND_MEMORY_NOT_CREDITED}: {clause}"',
            '"{SOURCE_BOUND_MEMORY_NOT_CREDITED}: the frame theorem has a checked \\\n                         proof; {clause}"',
        ):
            self.assertIn(fragment, self.source)

    def test_tag_and_line_format_are_the_verifier_census_lines(self):
        self.assertEqual(self.constant("OPCODE_INVENTORY_TRACE_TAG") + " v1", TAG)
        for fragment in (
            "v1\\tsummary\\tfunction={function}\\trows={}\\tblocking={}\\tpromotable={}",
            "v1\\tprecondition\\tfunction={function}\\tdetail={}",
            "v1\\trow\\tfunction={function}\\tindex={}\\topcode={}\\tstatus={}\\tdetail={}",
        ):
            self.assertIn(fragment, self.source)


class Reduce(unittest.TestCase):
    def setUp(self):
        self.census = CENSUS.reduce([("unit", SAMPLE)])

    def test_totals_deduplicate_and_count_preconditions(self):
        c = self.census
        self.assertEqual(c["format"], "trust-cg.proof-wall-census.v1")
        self.assertEqual((c["units"], c["functions"], c["blocking_rows"]), (1, 4, 5))
        self.assertEqual((c["refused_functions"], c["promotable_functions"]), (3, 1))
        self.assertEqual((c["repeat_verifications"], c["repeat_summary_differs"], c["malformed_lines"]), (1, 0, 0))
        self.assertEqual(c["ignored_replays"], 2)

    def test_every_row_lands_in_exactly_one_class_in_precedence_order(self):
        classes = {row["class"]: row for row in self.census["classes"]}
        self.assertEqual(tuple(classes), CENSUS.CLASS_ORDER)
        self.assertEqual(classes["pair-memory"]["instances"], 1)
        self.assertEqual(classes["registry-name-lookup"]["instances"], 2)
        self.assertEqual(classes["registry-name-lookup"]["functions"], 2)
        self.assertEqual(classes["statistical-only"]["instances"], 1)
        self.assertEqual(classes["no-mapping"]["instances"], 1)
        self.assertEqual(classes["precondition"]["functions"], 1)
        self.assertEqual(sum(row["instances"] for row in self.census["classes"]), 6)

    def test_pair_memory_wins_over_its_reason(self):
        self.assertEqual(CENSUS.classify("AArch64::StpPreIndex", "unverified", CENSUS.STATISTICAL), "pair-memory")
        self.assertEqual(CENSUS.classify("AArch64::LdpRI", "failed", "Unknown: timeout"), "pair-memory")
        self.assertEqual(CENSUS.classify("AArch64::Movz", "failed", "Unknown: timeout"), "ay-unknown-timeout")
        self.assertEqual(CENSUS.classify("AArch64::Movz", "failed", "counterexample x=1"), "refuted")
        self.assertEqual(
            CENSUS.classify("AArch64::AddRR", "unverified", "source-bound arithmetic needs independently replayed proof"),
            "no-checked-replay",
        )
        self.assertEqual(
            CENSUS.classify("AArch64::Movz", "unverified", CENSUS.INSTRUCTION_DERIVED + ": `x`"),
            "instruction-derived-uncertified",
        )

    def test_memory_effect_clause_keeps_the_lane_class_unless_every_part_is_checked(self):
        lane = CENSUS.STATISTICAL + ": `RECONSTRUCTED PairMemory_STP_pre_8B_off-16 -> StpPreIndex (real-operand, decoded-word: both transfers and base writeback)` found no counterexample in 100000 sampled inputs"
        note = (
            "; " + CENSUS.BOUND_MEMORY_FORMAL_ONLY + "; form theorem `PairMem[stp.pre.gpr.w8]`: the bound-memory "
            "certificate set credits nothing on this host: x (" + CENSUS.CHECKER_IDENTITY_MISS + ")"
        )
        head = "; " + CENSUS.MEMORY_EFFECT + ": `A64 memory effect StpPreIndex 0xa9bf7bfd` holds in process: all 6 parts exactly; "
        checked = lane + note + head + CENSUS.MEMORY_EFFECT_EVERY_PART + " (6 parts)"
        unchecked = lane + note + head + "0 of 6 parts have a Clean-checked certificate; the first without one is `address lane 1` (AY Unknown(\"(:reason-unknown (incomplete self-check-rejected))\"))"
        unreplayed = lane + note + head + "0 of 6 parts have a Clean-checked certificate (no live replay under this verification policy)"
        unrequested = lane + note + head + "0 of 6 parts have a Clean-checked certificate (" + CENSUS.MEMORY_EFFECT_REPLAY_NOT_REQUESTED + ")"
        refused = lane + note + head + "2 of 3 parts have a Clean-checked certificate; the first without one is `load lane 0 half 0` (replay refused: TCG_REFINE_SOLVER=0)"
        scalar = (
            CENSUS.INSTRUCTION_DERIVED + ": `A64 instruction word LdrRI 0xf9400801` holds (decided in-process for every "
            "input by term identity or exact bit routing); it binds the re-derived word"
            "; " + CENSUS.BOUND_MEMORY_FORMAL_ONLY + "; form theorem `ScalarMem[ldr.ui.gpr.w8.zx]`: " + CENSUS.CERTIFICATE_REPLAY_OFF
            + "; " + CENSUS.MEMORY_EFFECT + ": `A64 memory effect LdrRI 0xf9400801` is undecided in process: part `fields`: x"
            "; 0 of 3 parts have a Clean-checked certificate (not replayed: a part is undecided in process)"
        )
        self.assertEqual(CENSUS.classify("AArch64::StpPreIndex", "unverified", checked), "memory-effect-checked")
        self.assertEqual(CENSUS.classify("AArch64::LdrRI", "unverified", scalar.replace("is undecided in process: part `fields`: x", "holds in process: all 3 parts exactly").replace("0 of 3 parts have a Clean-checked certificate (not replayed: a part is undecided in process)", CENSUS.MEMORY_EFFECT_EVERY_PART + " (3 parts)")), "memory-effect-checked")
        self.assertEqual(CENSUS.classify("AArch64::StpPreIndex", "unverified", unchecked), "pair-memory")
        self.assertEqual(CENSUS.classify("AArch64::LdrRI", "unverified", scalar), "instruction-derived-uncertified")
        self.assertEqual(CENSUS.classify("AArch64::LdpRI", "unverified", unrequested), "pair-memory")
        # The clause's own constant must open it: the phrase elsewhere is not a clause.
        self.assertEqual(CENSUS.classify("AArch64::StpRI", "unverified", lane + " " + CENSUS.MEMORY_EFFECT_EVERY_PART), "pair-memory")
        prefix = CENSUS.STATISTICAL + " · bound memory: checker-identity miss · memory effect: "
        self.assertEqual(CENSUS.reason_key(checked), prefix + CENSUS.MEMORY_EFFECT_EVERY_PART)
        self.assertEqual(
            CENSUS.reason_key(unchecked), prefix + "0 parts checked; first without one: address lane N (AY Unknown)"
        )
        self.assertEqual(
            CENSUS.reason_key(unreplayed), prefix + "0 parts checked (no live replay under this verification policy)"
        )
        self.assertEqual(
            CENSUS.reason_key(unrequested),
            prefix + "0 parts checked (" + CENSUS.MEMORY_EFFECT_REPLAY_NOT_REQUESTED + ")",
        )
        self.assertEqual(
            CENSUS.reason_key(refused), prefix + "2 parts checked; first without one: load lane N half N (replay refused)"
        )
        self.assertEqual(
            CENSUS.reason_key(scalar),
            CENSUS.INSTRUCTION_DERIVED
            + ": holds (decided in-process for every input by term identity or exact bit routing)"
            + " · bound memory: certificate replay off · memory effect: is undecided in process",
        )
        # A malformed pair: no form binds it, and no decomposition admits it.
        unbound = (
            "no proof mapping for opcode StpRI; " + CENSUS.BOUND_MEMORY_FORMAL_ONLY
            + "; no form theorem binds this instruction: operand 0 is not a register"
        )
        self.assertEqual(
            CENSUS.reason_key(unbound), "no proof mapping for opcode StpRI · bound memory: no form theorem binds it"
        )
        # A register-offset store binds a form but no refutation check ran on it.
        unrefuted = (
            CENSUS.REGISTRY + ": query `store` in Memory selects a theorem by name; "
            + CENSUS.BOUND_MEMORY_FORMAL_ONLY + "; form theorem `ScalarMem[str.ro.gpr.w8]: STR`: "
            + CENSUS.BOUND_MEMORY_REFUTATION_NOT_RUN
        )
        self.assertEqual(CENSUS.reason_key(unrefuted), CENSUS.REGISTRY + " · bound memory: no refutation check ran")

    def test_a_bound_memory_row_is_its_own_class_and_names_its_parts(self):
        clause = (
            "; " + CENSUS.SOURCE_BOUND_MEMORY + ": `A64 memory effect LdrRI 0xf9400001` bound to source "
            "access 0, LIR instruction lir0.0; holds in process: all 3 parts exactly; 0 of 3 parts have a "
            "Clean-checked certificate; the first without one is `fields` (AY Unknown(\"(:reason-unknown "
            "(incomplete self-check-rejected))\"))"
        )
        scalar = (
            CENSUS.INSTRUCTION_DERIVED + ": `A64 instruction word LdrRI 0xf9400001` holds (decided in-process for every "
            "input by term identity or exact bit routing); it binds the re-derived word"
            "; " + CENSUS.BOUND_MEMORY_FORMAL_ONLY + "; form theorem `ScalarMem[ldr.ui.gpr.w8.zx]`: " + CENSUS.CERTIFICATE_REPLAY_OFF
            + clause
        )
        frame = (
            CENSUS.SOURCE_BOUND_MEMORY + ": the frame theorem has a checked proof; `A64 memory effect StpPreIndex "
            "0xa9bf7bfd` bound to the source-bound frame's save record; holds in process: all 6 parts exactly; "
            "0 of 6 parts credited: receipt 2 refused (a receipt judged another query (a stale or foreign certificate))"
        )
        self.assertEqual(CENSUS.classify("AArch64::LdrRI", "unverified", scalar), "source-bound-memory-uncertified")
        self.assertEqual(CENSUS.classify("AArch64::StpPreIndex", "unverified", frame), "source-bound-memory-uncertified")
        self.assertEqual(
            CENSUS.reason_key(scalar),
            CENSUS.INSTRUCTION_DERIVED
            + ": holds (decided in-process for every input by term identity or exact bit routing)"
            + " · bound memory: certificate replay off · source-bound memory: 0 parts checked; first without one: "
            "fields (AY Unknown)",
        )
        self.assertEqual(
            CENSUS.reason_key(frame),
            CENSUS.SOURCE_BOUND_MEMORY
            + " · source-bound memory: receipt refused (a receipt judged another query (a stale or foreign certificate))",
        )

    def test_source_bound_trace_lines_are_tallied_once_per_row(self):
        def bound(function, inst, binding, outcome):
            return (
                f"{CENSUS.SOURCE_BOUND_TAG}\tfunction={function}\tinst={inst}\topcode=AArch64::LdrRI\t"
                f"word=0xf9400001\tbinding={binding}\tparts=3\toutcome={outcome}"
            )

        text = "\n".join(
            [
                bound("f", 0, "leaf-access:lir0.0", "credited (every part)"),
                bound("f", 1, "leaf-access:lir0.1", "uncredited: `A64 memory effect` x; 0 of 3 parts"),
                summary("f", 3, 1, False),
                # A repeat verification of the same rows is not counted again.
                bound("f", 0, "leaf-access:lir0.0", "uncredited: x"),
                bound("g", 0, "frame-record:save", "credited (frame theorem and every part)"),
                bound("g", 3, "frame-record:restore", "form-credited (parts not replayed)"),
                summary("g", 5, 0, True),
            ]
        )
        text += "\n" + "\n".join(
            [
                f"{CENSUS.SOURCE_BOUND_TAG}\tunbound\tfunction=h\tmemory_rows=3\treason=LIR source is "
                "outside the memory-leaf domain: requires one block without stack, EH or aggregate ABI metadata",
                f"{CENSUS.SOURCE_BOUND_TAG}\tunbound\tfunction=k\tmemory_rows=2\treason=machine body is "
                "outside the memory-leaf domain: instruction InstId(7): Bl",
                summary("h", 9, 9, False),
                summary("k", 4, 2, False),
                # A repeat of `h` is not counted again.
                f"{CENSUS.SOURCE_BOUND_TAG}\tunbound\tfunction=h\tmemory_rows=3\treason=other",
            ]
        )
        census = CENSUS.reduce([("u", text)])
        self.assertEqual(
            census["source_bound_memory_unbound"],
            [
                {
                    "reason": "LIR source is outside the memory-leaf domain: requires one block without stack, "
                    "EH or aggregate ABI metadata",
                    "functions": 1,
                    "memory_rows": 3,
                },
                {
                    "reason": "machine body is outside the memory-leaf domain: instruction: Bl",
                    "functions": 1,
                    "memory_rows": 2,
                },
            ],
        )
        self.assertEqual(
            census["source_bound_memory"],
            [
                {"binding": "frame-record", "outcome": "credited", "rows": 1, "functions": 1},
                {"binding": "frame-record", "outcome": "form-credited", "rows": 1, "functions": 1},
                {"binding": "leaf-access", "outcome": "credited", "rows": 1, "functions": 1},
                {"binding": "leaf-access", "outcome": "uncredited", "rows": 1, "functions": 1},
            ],
        )
        self.assertIn("| leaf-access | uncredited | 1 | 1 |", CENSUS.markdown(census))

    def test_instruction_derived_reasons_keep_how_they_were_decided(self):
        exact = (
            CENSUS.INSTRUCTION_DERIVED
            + ": `A64 instruction word Movz 0xd2824680` holds (decided in-process for every input "
            "by term identity or exact bit routing); it binds the re-derived word to this "
            "instruction's operands"
        )
        sampled = (
            CENSUS.INSTRUCTION_DERIVED
            + ": `A64 instruction word CmpRI 0xf100003f` holds (decided in-process; a location "
            "needed the evaluator: Statistical(100000)); it binds the re-derived word"
        )
        undecided = CENSUS.INSTRUCTION_DERIVED + ": `A64 instruction word B 0x14000000` is undecided: Nzcv: x"
        self.assertEqual(
            CENSUS.reason_key(exact),
            CENSUS.INSTRUCTION_DERIVED
            + ": holds (decided in-process for every input by term identity or exact bit routing)",
        )
        self.assertEqual(
            CENSUS.reason_key(sampled),
            CENSUS.INSTRUCTION_DERIVED
            + ": holds (decided in-process; a location needed the evaluator: Statistical(100000))",
        )
        self.assertEqual(CENSUS.reason_key(undecided), CENSUS.INSTRUCTION_DERIVED + ": is undecided")

    def test_opcode_and_replay_tables(self):
        opcodes = [(r["class"], r["opcode"], r["functions"], r["instances"]) for r in self.census["opcodes"]]
        self.assertEqual(
            opcodes,
            [
                ("pair-memory", "AArch64::StpPreIndex", 1, 1),
                ("registry-name-lookup", "AArch64::Movz", 1, 1),
                ("registry-name-lookup", "AArch64::TailCall", 1, 1),
                ("statistical-only", "AArch64::AddRI", 1, 1),
                ("no-mapping", "AArch64::Csinv", 1, 1),
            ],
        )
        self.assertEqual(
            self.census["replays"],
            [{"outcome": "ay-unknown-timeout", "count": 1}, {"outcome": "checker-rejection", "count": 1}],
        )

    def test_replays_count_with_the_first_verification_only(self):
        replay = 'TCG_SOLVE_TRACE promotion_result obligation="Source-bound AArch64 frame" result={}'
        text = "\n".join(
            [
                replay.format("Verified"),
                summary("f", 1, 0, True),
                # The retry of `f` replays again: not counted.
                replay.format("Verified"),
                replay.format("SolverUnsat"),
                summary("f", 1, 0, True),
                replay.format("Timeout"),
                summary("g", 1, 0, True),
            ]
        )
        # A second log starts with nothing pending from the first.
        census = CENSUS.reduce([("u", text + "\n" + replay.format("Unknown")), ("v", summary("f", 1, 0, True))])
        self.assertEqual(
            census["replays"],
            [{"outcome": "ay-unknown-timeout", "count": 1}, {"outcome": "checked-proof", "count": 1}],
        )
        self.assertEqual((census["ignored_replays"], census["repeat_verifications"], census["functions"]), (3, 1, 3))

    def test_repeats_and_malformed_lines_are_counted_not_merged(self):
        text = "\n".join(
            [
                # A row before any summary, and a duplicate index in one verification.
                row("f", 0, "AArch64::Movz", "unverified", "no proof mapping for opcode Movz"),
                summary("f", 1, 1, False),
                row("f", 0, "AArch64::Movz", "unverified", "no proof mapping for opcode Movz"),
                row("f", 0, "AArch64::Movz", "unverified", CENSUS.REGISTRY + ": q"),
                # A repeat with a different summary (a trapping stub).
                summary("f", 1, 0, True),
            ]
        )
        census = CENSUS.reduce([("u", text)])
        self.assertEqual(
            (census["blocking_rows"], census["repeat_verifications"], census["repeat_summary_differs"], census["malformed_lines"]),
            (1, 1, 1, 2),
        )
        self.assertEqual(census["refused_functions"], 1)


class Output(unittest.TestCase):
    def test_markdown_tables_have_the_pinned_headers(self):
        text = CENSUS.markdown(CENSUS.reduce([("unit", SAMPLE)]))
        self.assertTrue(
            text.startswith(
                "Units: 1. Functions verified: 4. Promotable: 1. Refused: 3. Blocking rows: 5. "
                "Repeat verifications ignored: 1 (0 with a different summary). Live replays ignored: 2. "
                "Malformed lines: 0."
            )
        )
        for header in (
            "| Class | Refused functions | Instances | Distinct opcodes |",
            "| Class | Opcode | Functions | Instances |",
            "| Class | Reason | Instances |",
            "| Live formal replay outcome | Count |",
            "| Source-bound memory binding | Outcome | Rows | Functions |",
            "| Memory-leaf refusal (functions with memory rows, unbound) | Functions | Memory rows |",
            "| Unit | Functions | Refused | Blocking rows |",
        ):
            self.assertIn(header, text)
        self.assertIn("| registry-name-lookup | 2 | 2 | 2 |", text)
        self.assertIn(f"| registry-name-lookup | {CENSUS.REGISTRY} | 2 |", text)

    def test_cli_writes_json_and_compare_reports_the_change(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            (tmp / "p3_gcd.stderr.txt").write_text(SAMPLE, encoding="utf-8")
            after = SAMPLE.replace(CENSUS.REGISTRY, CENSUS.INSTRUCTION_DERIVED)
            (tmp / "after").mkdir()
            (tmp / "after" / "p3_gcd.stderr.txt").write_text(after, encoding="utf-8")
            for name, log in (("before", tmp / "p3_gcd.stderr.txt"), ("after", tmp / "after" / "p3_gcd.stderr.txt")):
                self.assertEqual(
                    CENSUS.main([str(log), "--json", str(tmp / f"{name}.json"), "--markdown", str(tmp / f"{name}.md")]),
                    0,
                )
            doc = json.loads((tmp / "before.json").read_text(encoding="utf-8"))
            self.assertEqual(doc["per_unit"], [{"unit": "p3_gcd", "functions": 4, "refused": 3, "blocking_rows": 5}])
            out = io.StringIO()
            with redirect_stdout(out):
                self.assertEqual(CENSUS.main(["--compare", str(tmp / "before.json"), str(tmp / "after.json")]), 0)
            self.assertIn("| registry-name-lookup | 2 | 0 | 2 | 0 | -2 |", out.getvalue())
            self.assertIn("| instruction-derived-uncertified | 0 | 2 | 0 | 2 | +2 |", out.getvalue())

    def test_no_census_lines_is_an_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            log = Path(tmp) / "empty.stderr.txt"
            log.write_text("error: aborting due to 1 previous error\n", encoding="utf-8")
            self.assertEqual(CENSUS.main([str(log)]), 1)


if __name__ == "__main__":
    unittest.main()
