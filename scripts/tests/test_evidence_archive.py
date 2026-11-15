"""Evidence-archive verification and the development-record wiring.

Every case builds synthetic archives; no real report is read.
"""

from __future__ import annotations

import contextlib
import gzip
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]


def load(name: str):
    spec = importlib.util.spec_from_file_location(f"_test_{name}", ROOT / f"scripts/{name}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


evidence = load("check_evidence_archive")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run_main(argv: list[str]) -> tuple[int, str, str]:
    stdout, stderr = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
        status = evidence.main(argv)
    return status, stdout.getvalue(), stderr.getvalue()


class ArchiveTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="trust-cg-evidence-")
        self.base = Path(self.temporary.name)
        self.archive = self.base / "2026-09-18-example"
        self.write("README.md", b"# Example\n\nClaim and boundary.\n")
        self.plain = b'{"passed": 3, "failed": 0}\n'
        self.log = b"test result: ok. 3 passed\n" * 50
        self.write("report.json", self.plain)
        self.write("records/run.stdout.log.gz", gzip.compress(self.log, mtime=0))
        self.write("nested/one.log", b"nested log\n")
        self.entries = [self.plain_entry("report.json", self.plain), self.gzip_entry("records/run.stdout.log.gz", self.log)]
        self.write_inventory(self.entries)
        self.write("nested/inventory.json", json.dumps([self.plain_entry("one.log", b"nested log\n")]).encode())

    def tearDown(self):
        self.temporary.cleanup()

    def reset(self) -> None:
        self.tearDown()
        self.setUp()

    def write(self, relative: str, data: bytes) -> Path:
        path = self.archive / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        return path

    def write_inventory(self, entries, wrap: bool = True) -> None:
        document = {"source": "0" * 40, "artifacts": entries} if wrap else entries
        self.write("inventory.json", json.dumps(document).encode())

    @staticmethod
    def plain_entry(path: str, data: bytes) -> dict:
        return {"path": path, "sha256": sha(data), "bytes": len(data)}

    def gzip_entry(self, path: str, decoded: bytes) -> dict:
        stored = (self.archive / path).read_bytes()
        return {"path": path, "sha256": sha(decoded), "bytes": len(decoded),
                "stored_sha256": sha(stored), "stored_bytes": len(stored)}

    def errors(self) -> list[str]:
        return evidence.archive_errors(self.archive)

    def assertRefused(self, fragment: str) -> None:
        errors = self.errors()
        self.assertTrue(any(fragment in error for error in errors), errors)
        status, _, stderr = run_main([str(self.archive)])
        self.assertEqual(status, 1)
        self.assertIn(fragment, stderr)

    def test_complete_archive_with_nested_inventory_passes(self):
        self.assertEqual(self.errors(), [])
        status, stdout, _ = run_main([str(self.archive)])
        self.assertEqual(status, 0)
        self.assertIn("1 archive(s)", stdout)

    def test_list_form_inventory_and_sha256sums_are_accepted(self):
        self.write_inventory(self.entries, wrap=False)
        self.assertEqual(self.errors(), [])
        (self.archive / "inventory.json").unlink()
        stored = (self.archive / "records/run.stdout.log.gz").read_bytes()
        self.write("SHA256SUMS", (
            f"{sha(self.plain)}  report.json\n{sha(stored)} *records/run.stdout.log.gz\n"
        ).encode())
        self.assertEqual(self.errors(), [])

    def test_changed_plain_bytes_are_refused(self):
        self.write("report.json", self.plain.replace(b"0", b"1"))
        self.assertRefused("report.json: SHA-256/length mismatch")

    def test_changed_stored_or_decoded_identity_is_refused(self):
        self.write("records/run.stdout.log.gz", gzip.compress(self.log + b"x", mtime=0))
        self.assertRefused("stored SHA-256/length mismatch")
        self.reset()
        entry = dict(self.entries[1], sha256=sha(b"other"))
        self.write_inventory([self.entries[0], entry])
        self.assertRefused("decoded SHA-256/length mismatch")

    def test_decoding_reads_at_most_one_byte_past_the_recorded_length(self):
        entry = dict(self.entries[1], bytes=10)
        self.write_inventory([self.entries[0], entry])
        self.assertRefused("decoded SHA-256/length mismatch")
        self.assertEqual(
            evidence.decoded_digest(self.archive / "records/run.stdout.log.gz", 10)[1], 11)

    def test_undecodable_or_unknown_encoding_is_refused(self):
        corrupt = b"\x1f\x8b not really gzip"
        self.write("records/run.stdout.log.gz", corrupt)
        entry = dict(self.entries[1], stored_sha256=sha(corrupt), stored_bytes=len(corrupt))
        self.write_inventory([self.entries[0], entry])
        self.assertRefused("gzip member cannot be decoded")
        self.reset()
        entry = dict(self.plain_entry("report.json", self.plain),
                     stored_sha256=sha(self.plain), stored_bytes=len(self.plain))
        self.write_inventory([entry, self.entries[1]])
        self.assertRefused("no known encoding")

    def test_unlisted_and_missing_files_are_refused(self):
        self.write("records/extra.stderr.log", b"unlisted\n")
        self.assertRefused("records/extra.stderr.log is not listed by any inventory")
        (self.archive / "records/extra.stderr.log").unlink()
        (self.archive / "report.json").unlink()
        self.assertRefused("report.json: listed file is missing")

    def test_names_that_differ_only_in_case_are_refused(self):
        # The shape ff4c27eca archived: `readelf -S` and `readelf -s` records
        # whose names differ in case alone. A case-insensitive filesystem keeps
        # one file under both names, so each listed digest can still match it.
        upper = "records/Run.stdout.log.gz"
        if not (self.archive / upper).exists():
            self.write(upper, (self.archive / "records/run.stdout.log.gz").read_bytes())
        self.write_inventory(self.entries + [self.gzip_entry(upper, self.log)])
        self.assertRefused(
            "records/Run.stdout.log.gz, records/run.stdout.log.gz are one file on a case-insensitive filesystem"
        )

    def test_entry_shape_is_exact(self):
        report, log = self.entries
        without_stored_bytes = {key: value for key, value in log.items() if key != "stored_bytes"}
        cases = {
            "unsafe or missing artifact path '../escape'": [dict(report, path="../escape"), log],
            "unsafe or missing artifact path '/tmp/x'": [dict(report, path="/tmp/x"), log],
            "unsafe or missing artifact path 'records//x'": [dict(report, path="records//x"), log],
            "needs a 64-hex sha256 and a byte count": [dict(report, bytes=True), log],
            "must appear together": [report, without_stored_bytes],
            "artifact entry is not an object": ["report.json", log],
        }
        for fragment, entries in cases.items():
            with self.subTest(fragment):
                self.write_inventory(entries)
                self.assertRefused(fragment)

    def test_duplicate_entries_and_malformed_inventories_are_refused(self):
        self.write_inventory(self.entries + [self.entries[0]])
        self.assertRefused("duplicate artifact report.json")
        self.write("inventory.json", b"{not json")
        self.assertRefused("invalid JSON")
        self.write_inventory([])
        self.assertRefused("expected a non-empty artifact list")

    def test_sha256sums_mismatch_malformed_and_empty_are_refused(self):
        (self.archive / "inventory.json").unlink()
        stored = (self.archive / "records/run.stdout.log.gz").read_bytes()
        good = f"{sha(stored)}  records/run.stdout.log.gz\n"
        for fragment, text in (
            ("SHA-256 mismatch: report.json", good + f"{sha(b'other')}  report.json\n"),
            ("malformed SHA256SUMS line", good + "not-a-hash  report.json\n"),
            ("lists no artifacts", "\n"),
        ):
            with self.subTest(fragment):
                self.write("SHA256SUMS", text.encode())
                self.assertRefused(fragment)

    def test_readme_and_top_level_inventory_are_required(self):
        (self.archive / "README.md").unlink()
        self.assertRefused("missing README.md")
        self.reset()
        (self.archive / "inventory.json").unlink()
        self.assertRefused("missing top-level inventory.json or SHA256SUMS")
        self.assertEqual(evidence.archive_errors(self.base / "absent"),
                         [f"{self.base / 'absent'}: not an archive directory"])

    @unittest.skipUnless(hasattr(os, "symlink"), "symlinks unavailable")
    def test_symlinks_are_refused(self):
        os.symlink(self.archive / "report.json", self.archive / "alias.json")
        self.assertRefused("alias.json: archive member is not a regular file")
        (self.archive / "alias.json").unlink()
        os.symlink(self.archive / "records", self.archive / "linked")
        self.assertRefused("symlinked directory in archive")

    def test_main_requires_a_target_and_reports_unreadable_input(self):
        with contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as raised:
                evidence.main([])
        self.assertEqual(raised.exception.code, 2)
        (self.archive / "records/run.stdout.log.gz").chmod(0)
        try:
            status, _, stderr = run_main([str(self.archive)])
        finally:
            (self.archive / "records/run.stdout.log.gz").chmod(0o644)
        if os.geteuid() != 0:
            self.assertEqual(status, 2)
            self.assertIn("evidence archive check failed", stderr)


if __name__ == "__main__":
    unittest.main()
