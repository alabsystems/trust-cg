"""Structure gate for the AArch64 acceptance template and trusted-base ledger."""

from __future__ import annotations

import importlib.util
import re
import shutil
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
CHECKER_PATH = ROOT / "scripts" / "check_documentation.py"
SPEC = importlib.util.spec_from_file_location("check_documentation", CHECKER_PATH)
assert SPEC is not None and SPEC.loader is not None
CHECKER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CHECKER
SPEC.loader.exec_module(CHECKER)

DOCUMENTS = (CHECKER.ACCEPTANCE_TEMPLATE, CHECKER.TRUSTED_BASE_LEDGER, CHECKER.CLOSURE_LEDGER)
# Public snapshots omit the whole development docs/ tree (publish/manifest.txt)
# but still run scripts/tests. In a development checkout docs/ exists, so these
# tests run and a missing document fails them instead of skipping.
DEVELOPMENT_TREE = (ROOT / "docs").is_dir()
requires_development_docs = unittest.skipUnless(
    DEVELOPMENT_TREE, "public snapshot: development docs/ is not published"
)


def read_document(name: str) -> str:
    return (ROOT / name).read_text() if DEVELOPMENT_TREE else ""


TEMPLATE = read_document(CHECKER.ACCEPTANCE_TEMPLATE)
LEDGER = read_document(CHECKER.TRUSTED_BASE_LEDGER)
GAPS = CHECKER.closure_ledger_gap_ids(read_document(CHECKER.CLOSURE_LEDGER))


def replace_once(text: str, old: str, new: str) -> str:
    assert text.count(old) == 1, old
    return text.replace(old, new)


def without_section(text: str, heading: str) -> str:
    """Drop one heading and its body up to the next heading of any level."""
    pattern = re.compile(rf"^{re.escape(heading)}.*?(?=^#)", re.MULTILINE | re.DOTALL)
    result, count = pattern.subn("", text)
    assert count == 1, heading
    return result


@requires_development_docs
class RepositoryDocumentTests(unittest.TestCase):
    def test_committed_documents_pass(self) -> None:
        self.assertEqual(CHECKER.acceptance_document_errors(ROOT), [])

    def test_ledger_indexes_every_island_section(self) -> None:
        islands, errors = CHECKER.trusted_base_ledger_errors(LEDGER)
        self.assertEqual(errors, [])
        self.assertEqual(islands, {f"TB-{number:02d}" for number in range(1, 26)})

    def test_closure_ledger_gap_index_is_read(self) -> None:
        # The closure ledger never removes a gap (it marks it WITHDRAWN), so its
        # 2026-09-17 count is a lower bound.
        self.assertGreaterEqual(len(GAPS), 218)
        self.assertIn("L07-P11", GAPS)
        self.assertIn("X-DARWIN-P12", GAPS)

    def test_every_governing_gate_is_mapped(self) -> None:
        rows = CHECKER._table_rows(TEMPLATE, CHECKER.GATE_ID)
        self.assertEqual({cells[0] for cells in rows}, set(CHECKER.MILESTONE_GATES))


@requires_development_docs
class TemplateRejectionTests(unittest.TestCase):
    def errors(self, template: str, ledger: str = LEDGER) -> list[str]:
        islands, ledger_errors = CHECKER.trusted_base_ledger_errors(ledger)
        return ledger_errors + CHECKER.acceptance_template_errors(template, islands, GAPS)

    def assertRejected(self, template: str, fragment: str, ledger: str = LEDGER) -> None:
        errors = self.errors(template, ledger)
        self.assertTrue(any(fragment in error for error in errors), (fragment, errors))

    def test_missing_row_section_is_rejected(self) -> None:
        template = without_section(TEMPLATE, "## L07 — ")
        self.assertRejected(template, "row sections must be exactly L01..L14")

    def test_missing_row_field_is_rejected(self) -> None:
        template = replace_once(
            TEMPLATE,
            "- **Negative controls:** memory-order mutation controls; destructor-count",
            "Memory-order mutation controls; destructor-count",
        )
        self.assertRejected(template, "row L03 lacks field Negative controls")

    def test_row_without_trusted_base_island_is_rejected(self) -> None:
        template = replace_once(
            TEMPLATE,
            "- **Remaining trusted base:** TB-02, TB-16, TB-17.",
            "- **Remaining trusted base:** to be decided.",
        )
        self.assertRejected(template, "row L08 names no trusted-base island")

    def test_unknown_island_citation_is_rejected(self) -> None:
        template = replace_once(
            TEMPLATE,
            "- **Remaining trusted base:** TB-20, TB-22, TB-23.",
            "- **Remaining trusted base:** TB-20, TB-22, TB-23, TB-99.",
        )
        self.assertRejected(template, "row L14 cites unknown trusted-base island TB-99")

    def test_island_cited_by_no_row_is_rejected(self) -> None:
        ledger = replace_once(
            LEDGER,
            "| TB-24 | Self-host bootstrap boundary | not measured | TRUSTED |\n",
            "| TB-24 | Self-host bootstrap boundary | not measured | TRUSTED |\n"
            "| TB-26 | Uncited island | 10 | TRUSTED |\n",
        )
        ledger += (
            "\n### TB-26 — Uncited island\n\n- **Location:** x.\n- **LOC:** 10.\n"
            "- **Trusted for:** x.\n- **Mitigations:** none.\n- **Status:** TRUSTED.\n"
            "- **Shrinks when:** never.\n"
        )
        self.assertRejected(TEMPLATE, "trusted-base island TB-26 is cited by no row", ledger)

    def test_dropped_milestone_gate_is_rejected(self) -> None:
        template = "\n".join(
            line for line in TEMPLATE.splitlines() if not line.startswith("| M6-DOCS-TRUTH |")
        )
        self.assertRejected(template, "milestone gate M6-DOCS-TRUTH is not mapped to any row")

    def test_row_omitting_a_mapped_gate_is_rejected(self) -> None:
        template = replace_once(
            TEMPLATE,
            "- **Milestone gates:** M4-JIT-LATENCY, M5-G1B-VECTOR, M6-GATE-SB, M6-COMPLETE5,",
            "- **Milestone gates:** M4-JIT-LATENCY, M5-G1B-VECTOR, M6-COMPLETE5,",
        )
        self.assertRejected(template, "row L14 omits milestone gate M6-GATE-SB")

    def test_row_listing_an_unmapped_gate_is_rejected(self) -> None:
        template = replace_once(
            TEMPLATE,
            "- **Ledger gaps:** L01-P1 – L01-P11, C-11.\n- **Milestone gates:** G3-ISLAND-LEDGER.",
            "- **Ledger gaps:** L01-P1 – L01-P11, C-11.\n- **Milestone gates:** M6-GATE-SB, G3-ISLAND-LEDGER.",
        )
        self.assertRejected(template, "row L01 lists milestone gate M6-GATE-SB that does not map to it")

    def test_gate_mapped_to_unknown_row_is_rejected(self) -> None:
        template, count = re.subn(
            r"^(\| M6-ENC10-META \|[^|]*\|[^|]*\|) L13 \|",
            r"\1 L13, L15 |",
            TEMPLATE,
            count=1,
            flags=re.MULTILINE,
        )
        self.assertEqual(count, 1)
        self.assertRejected(template, "milestone gate M6-ENC10-META maps to unknown row L15")

    def test_unassigned_closure_ledger_gap_is_rejected(self) -> None:
        template = replace_once(
            TEMPLATE,
            "- **Ledger gaps:** L05-P1 – L05-P12, C-04, C-05, C-11.",
            "- **Ledger gaps:** L05-P1 – L05-P12, C-04, C-11.",
        )
        self.assertRejected(template, "closure-ledger gap C-05 is assigned to no record")

    def test_truncated_gap_range_is_rejected(self) -> None:
        template = replace_once(
            TEMPLATE,
            "- **Ledger gaps:** L10-P1 – L10-P12, C-11.",
            "- **Ledger gaps:** L10-P1 – L10-P11, C-11.",
        )
        self.assertRejected(template, "closure-ledger gap L10-P12 is assigned to no record")

    def test_unknown_gap_is_rejected(self) -> None:
        template = replace_once(
            TEMPLATE,
            "- **Ledger gaps:** L01-P1 – L01-P11, C-11.",
            "- **Ledger gaps:** L01-P1 – L01-P11, L01-P99, C-11.",
        )
        self.assertRejected(template, "assigned gap L01-P99 is not in the closure ledger")

    def test_claimed_pass_in_template_is_rejected(self) -> None:
        template = replace_once(
            TEMPLATE,
            "- **Ledger gaps:** L05-P1 – L05-P12, C-04, C-05, C-11.\n- **Milestone gates:** G3-ISLAND-LEDGER.\n- **Verdict:** OPEN.",
            "- **Ledger gaps:** L05-P1 – L05-P12, C-04, C-05, C-11.\n- **Milestone gates:** G3-ISLAND-LEDGER.\n- **Verdict:** PASS.",
        )
        self.assertRejected(template, "row L05 verdict must stay OPEN")

    def test_verdict_table_pass_is_rejected(self) -> None:
        template = replace_once(TEMPLATE, "| L12 | OPEN |", "| L12 | PASS |")
        self.assertRejected(template, "acceptance verdict table must list L12 as OPEN")


@requires_development_docs
class LedgerRejectionTests(unittest.TestCase):
    def errors(self, ledger: str) -> list[str]:
        return CHECKER.trusted_base_ledger_errors(ledger)[1]

    def assertRejected(self, ledger: str, fragment: str) -> None:
        errors = self.errors(ledger)
        self.assertTrue(any(fragment in error for error in errors), (fragment, errors))

    def test_unknown_status_is_rejected(self) -> None:
        ledger = replace_once(
            LEDGER,
            "| TB-03 | TrustIR semantic encoding in the verifier | 1,703 | TRUSTED |",
            "| TB-03 | TrustIR semantic encoding in the verifier | 1,703 | PROVEN |",
        )
        self.assertRejected(ledger, "island TB-03 index status 'PROVEN' is not one of")

    def test_section_status_must_match_index(self) -> None:
        ledger = replace_once(
            LEDGER,
            "- **Status:** TRUSTED.\n- **Shrinks when:** obligations consume the canonical TrustIR semantics (L08-P1).",
            "- **Status:** PARTIAL.\n- **Shrinks when:** obligations consume the canonical TrustIR semantics (L08-P1).",
        )
        self.assertRejected(ledger, "island TB-03 section status 'PARTIAL' disagrees with index 'TRUSTED'")

    def test_missing_island_section_is_rejected(self) -> None:
        ledger = without_section(LEDGER, "### TB-10 — ")
        self.assertRejected(ledger, "island TB-10 has an index row but no section")

    def test_missing_island_field_is_rejected(self) -> None:
        ledger = replace_once(
            LEDGER,
            "- **Shrinks when:** its certificates are also kernel-checked by TB-17.",
            "Its certificates could also be kernel-checked by TB-17.",
        )
        self.assertRejected(ledger, "island TB-18 lacks field Shrinks when")

    def test_unmeasured_loc_must_be_explicit(self) -> None:
        ledger = replace_once(
            LEDGER,
            "| TB-06 | Exact affine evaluator | 1,484 | CHECKER |",
            "| TB-06 | Exact affine evaluator | about 1.5k | CHECKER |",
        )
        self.assertRejected(ledger, "island TB-06 LOC must be a wc -l count or 'not measured'")

    def test_section_loc_must_match_index(self) -> None:
        ledger = replace_once(LEDGER, "- **LOC:** 1,484.", "- **LOC:** 1,500.")
        self.assertRejected(ledger, "island TB-06 section LOC '1,500.' does not start with the index LOC '1,484'")

    def test_section_loc_prefix_of_a_larger_count_is_rejected(self) -> None:
        ledger = replace_once(LEDGER, "- **LOC:** 1,484.", "- **LOC:** 1,4840.")
        self.assertRejected(ledger, "island TB-06 section LOC '1,4840.' does not start with the index LOC")

    def retire_tb06(self, status: str) -> str:
        ledger = replace_once(
            LEDGER,
            "| TB-06 | Exact affine evaluator | 1,484 | CHECKER |",
            f"| TB-06 | Exact affine evaluator | 1,484 | {status} |",
        )
        return replace_once(
            ledger,
            "- **Status:** CHECKER.\n- **Shrinks when:** the normal-form",
            f"- **Status:** {status}.\n- **Shrinks when:** the normal-form",
        )

    def test_retired_island_without_commit_is_rejected(self) -> None:
        ledger = self.retire_tb06("RETIRED")
        self.assertRejected(ledger, "island TB-06 index status must name the replacing commit")
        self.assertRejected(ledger, "island TB-06 section status must name the replacing commit")

    def test_retired_island_with_commit_is_accepted(self) -> None:
        self.assertEqual(self.errors(self.retire_tb06("RETIRED 0123abcd")), [])


class PresenceTests(unittest.TestCase):
    def test_public_snapshot_without_docs_tree_is_accepted(self) -> None:
        with tempfile.TemporaryDirectory(prefix="trust-cg-docs-") as temporary:
            self.assertEqual(CHECKER.acceptance_document_errors(Path(temporary)), [])

    def test_docs_tree_without_the_documents_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory(prefix="trust-cg-docs-") as temporary:
            root = Path(temporary)
            (root / "docs").mkdir()
            self.assertEqual(
                CHECKER.acceptance_document_errors(root),
                [f"missing maintained document: {name}" for name in DOCUMENTS],
            )

    @requires_development_docs
    def test_partial_document_set_is_rejected(self) -> None:
        for present in DOCUMENTS:
            with self.subTest(present=present), tempfile.TemporaryDirectory(prefix="trust-cg-docs-") as temporary:
                root = Path(temporary)
                (root / "docs").mkdir()
                shutil.copy2(ROOT / present, root / present)
                self.assertEqual(
                    CHECKER.acceptance_document_errors(root),
                    [f"missing maintained document: {name}" for name in DOCUMENTS if name != present],
                )

    @requires_development_docs
    def test_copied_documents_pass_in_another_root(self) -> None:
        with tempfile.TemporaryDirectory(prefix="trust-cg-docs-") as temporary:
            root = Path(temporary)
            (root / "docs").mkdir()
            for name in DOCUMENTS:
                shutil.copy2(ROOT / name, root / name)
            self.assertEqual(CHECKER.acceptance_document_errors(root), [])

    @requires_development_docs
    def test_closure_ledger_without_gap_rows_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory(prefix="trust-cg-docs-") as temporary:
            root = Path(temporary)
            (root / "docs").mkdir()
            for name in DOCUMENTS:
                shutil.copy2(ROOT / name, root / name)
            (root / CHECKER.CLOSURE_LEDGER).write_text("# Empty ledger\n")
            errors = CHECKER.acceptance_document_errors(root)
            self.assertIn(f"{CHECKER.CLOSURE_LEDGER}: gap index has no gap rows", errors)

    @requires_development_docs
    def test_declared_completion_with_open_gaps_fails_the_maintained_document_gate(self) -> None:
        with tempfile.TemporaryDirectory(prefix="trust-cg-docs-") as temporary:
            root = Path(temporary)
            (root / "docs").mkdir()
            for name in DOCUMENTS:
                shutil.copy2(ROOT / name, root / name)
            path = root / CHECKER.CLOSURE_LEDGER
            text, count = re.subn(r"(?m)^Status: \*\*OPEN\*\*", "Status: **ALL GAPS RESOLVED**", path.read_text())
            self.assertEqual(count, 1)
            path.write_text(text)
            self.assertIn(
                f"{CHECKER.CLOSURE_LEDGER}: closure ledger cannot declare completion with unresolved gaps",
                CHECKER.acceptance_document_errors(root),
            )


if __name__ == "__main__":
    unittest.main()
