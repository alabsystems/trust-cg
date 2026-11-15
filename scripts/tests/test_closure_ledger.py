"""Unit tests for scripts/closure_ledger.py on a synthetic ledger."""

from __future__ import annotations

import importlib.util
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("closure_ledger", ROOT / "scripts" / "closure_ledger.py")
ledger = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ledger)

HEAD = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "--short", "HEAD"],
                      capture_output=True, text=True, check=True).stdout.strip()

SAMPLE = """# Ledger

Status: **OPEN** — all L01–L14 rows open. This is the
maintained closure ledger.

| ID | Row | Platform | Effort | Title |
| --- | --- | --- | --- | --- |
| L01-P1 | L01 | both | L | First gap |
| C-01 | L02 | both | — | Critic gap |

### C-01 [L02] Critic gap

Status: OPEN

Body.

## L01: ABI (1 gaps)

### L01-P1 First gap

Status: OPEN
Platform: both · Effort: L · Category: implementation

Body.

## Refuted claims (not gaps)

- none
"""


class ClosureLedgerTests(unittest.TestCase):
    def write(self, text=SAMPLE):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        path = Path(directory.name) / "ledger.md"
        path.write_text(text)
        return path

    def test_set_updates_only_the_section_status(self):
        path = self.write()
        ledger.main(["--ledger", str(path), "set", "L01-P1", f"CLOSED {HEAD}", "--note", "done"])
        text = path.read_text()
        self.assertIn(f"Status: CLOSED {HEAD}  \nNote: done", text)
        # The index row and the headline carry no status or totals to rewrite.
        self.assertIn("| L01-P1 | L01 | both | L | First gap |", text)
        self.assertIn("Status: **OPEN** — all L01–L14 rows open.", text)
        self.assertEqual(ledger.counts(text), {"OPEN": 1, "PARTIAL": 0, "CLOSED": 1, "WITHDRAWN": 0})

    def test_set_replaces_a_previous_note(self):
        path = self.write()
        ledger.main(["--ledger", str(path), "set", "C-01", f"PARTIAL {HEAD}", "--note", "one"])
        ledger.main(["--ledger", str(path), "set", "C-01", f"CLOSED {HEAD}", "--note", "two"])
        text = path.read_text()
        self.assertEqual(text.count("Note:"), 1)
        self.assertIn("Note: two", text)

    def test_closed_requires_an_existing_commit(self):
        path = self.write()
        for status in ("CLOSED", "CLOSED 0000000deadbeef", "DONE abc"):
            with self.subTest(status=status), self.assertRaises(SystemExit):
                ledger.main(["--ledger", str(path), "set", "L01-P1", status])
        self.assertEqual(path.read_text(), SAMPLE)

    def test_unknown_gap_is_refused(self):
        path = self.write()
        with self.assertRaises(SystemExit):
            ledger.main(["--ledger", str(path), "set", "L09-P9", "OPEN"])

    def test_add_appends_index_row_and_section_before_refuted_claims(self):
        path = self.write()
        ledger.main(["--ledger", str(path), "add", "L01-P2", "--row", "L01", "--platform", "linux",
                     "--effort", "S", "--category", "evidence", "--title", "New gap",
                     "--description", "What is missing.", "--evidence", "file.rs:1"])
        text = path.read_text()
        self.assertIn("| C-01 | L02 | both | — | Critic gap |\n| L01-P2 | L01 | linux | S | New gap |", text)
        self.assertLess(text.index("### L01-P2 New gap"), text.index("## Refuted claims"))
        self.assertIn("## Gaps recorded after the audit", text)
        self.assertEqual(ledger.counts(text)["OPEN"], 3)
        with self.assertRaises(SystemExit):
            ledger.main(["--ledger", str(path), "add", "L01-P2", "--row", "L01", "--platform", "linux",
                         "--effort", "S", "--category", "evidence", "--title", "Dup",
                         "--description", "x"])


if __name__ == "__main__":
    unittest.main()
