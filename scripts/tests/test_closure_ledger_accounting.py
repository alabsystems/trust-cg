"""Completion accounting rejects hidden open gaps and contradictory gap records."""

import importlib.util
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("closure_checker", ROOT / "scripts/check_documentation.py")
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)

LEDGER = """# Closure ledger

Status: **OPEN** — rows open.

| ID | Row | Platform | Effort | Title |
| --- | --- | --- | --- | --- |
| L01-P1 | L01 | both | S | First |
| L01-P2 | L01 | both | S | Second |
| C-01 | all | both | S | Third |
| X-HOST-P1 | L14 | both | S | Fourth |

### L01-P1 First
Status: OPEN

### L01-P2 Second
Status: PARTIAL abc1234

### C-01 Third
Status: CLOSED abc1234

### X-HOST-P1 Fourth
Status: WITHDRAWN abc1234
"""


class ClosureLedgerTests(unittest.TestCase):
    def rejected(self, text, fragment):
        errors = CHECKER.closure_ledger_errors(text)
        self.assertTrue(any(fragment in error for error in errors), errors)

    def test_consistent_ledger_and_commitless_partial_pass(self):
        self.assertEqual(CHECKER.closure_ledger_errors(LEDGER), [])
        self.assertEqual(CHECKER.closure_ledger_errors(LEDGER.replace("PARTIAL abc1234", "PARTIAL")), [])

    def test_missing_or_duplicate_headline_is_rejected(self):
        line = "Status: **OPEN** — rows open."
        self.rejected(LEDGER.replace(line, ""), "status headline")
        self.rejected(LEDGER + "\n" + line, "status headline")

    def test_completion_cannot_hide_partial_or_open_gaps(self):
        self.rejected(LEDGER.replace("**OPEN**", "**CLOSED**"), "cannot declare completion")
        only_partial = LEDGER.replace("Status: OPEN", "Status: CLOSED abc1234")
        self.rejected(only_partial.replace("**OPEN**", "**ALL GAPS RESOLVED**"), "cannot declare completion")

    def test_resolved_gap_header_does_not_require_contract_row_closure(self):
        text = LEDGER.replace("Status: OPEN", "Status: CLOSED abc1234")
        text = text.replace("PARTIAL abc1234", "CLOSED abc1234")
        text = text.replace("**OPEN** — rows open", "**ALL GAPS RESOLVED** — rows open")
        self.assertEqual(CHECKER.closure_ledger_errors(text), [])

    def test_closed_and_withdrawn_require_commit(self):
        for word in ["CLOSED", "WITHDRAWN"]:
            with self.subTest(word=word):
                self.rejected(LEDGER.replace(word + " abc1234", word), "require a commit")

    def test_unknown_or_empty_status_cannot_disappear_from_totals(self):
        self.rejected(LEDGER.replace("Status: OPEN", "Status: DONE"), "invalid status")
        self.rejected(LEDGER.replace("Status: OPEN", "Status:"), "invalid status")
        self.rejected(LEDGER.replace("| S | First |", "| | First |"), "required column")

    def test_each_gap_has_exactly_one_index_row_and_section(self):
        row = "| L01-P1 | L01 | both | S | First |"
        self.rejected(LEDGER + "\n" + row, "duplicate gap index row")
        self.rejected(LEDGER.replace(row, ""), "section but no index row")
        self.rejected(LEDGER.replace("### L01-P1 First", "### unindexed"), "index row but no section")
        self.rejected(LEDGER + "\n### L01-P1 Duplicate\nStatus: OPEN\n", "duplicate gap section")

    def test_each_gap_has_exactly_one_status(self):
        self.rejected(LEDGER.replace("Status: OPEN", ""), "exactly one section status")
        self.rejected(LEDGER.replace("Status: OPEN", "Status: OPEN\nStatus: OPEN"), "exactly one section status")


if __name__ == "__main__":
    unittest.main()
