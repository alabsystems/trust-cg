"""Fault-injection controls for diagnostic capture completeness and query bytes."""

from __future__ import annotations

import copy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest


SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
SPEC = importlib.util.spec_from_file_location(
    "export_x86_qualification_matrix", SCRIPTS / "export_x86_qualification_matrix.py"
)
EXPORT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(EXPORT)


def capture(records: list[dict]) -> bytes:
    header = {"kind": "header", "format": EXPORT.FORMAT, "proof_credit": False,
              "verifier_source_sha256": "a" * 64}
    payloads = [json.dumps({**record, "sequence": index})
                for index, record in enumerate(records)]
    footer = {
        "kind": "footer", "records": len(records),
        "queries": sum(record["kind"] == "query" for record in records),
        "refusals": sum(record["kind"] == "refusal" for record in records),
        "records_sha256": EXPORT.digest(("\n".join(payloads) + "\n").encode()),
    }
    return ("running 1 test\n" + "\n".join(
        EXPORT.PREFIX + payload for payload in [json.dumps(header), *payloads, json.dumps(footer)]
    ) + "\ntest result: ok\n").encode()


class QualificationExportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.records = []
        for family, filename in EXPORT.FAMILIES.items():
            for label, query in EXPORT.snapshot_queries((EXPORT.FIXTURES / filename).read_bytes(), filename):
                cls.records.append({
                    "kind": "query", "family": family, "label": label, "class": "canonical",
                    "source_bound": True, "expected": "unsat", "smt2": query.decode(),
                })
            # These small synthetic controls test transport only. They are not
            # claims about the Rust wrong-lowering builders or AY outcomes.
            cls.records.append({
                "kind": "query", "family": family, "label": "transport-control",
                "class": "wrong-lowering", "source_bound": False, "expected": "sat",
                "smt2": "(set-option :timeout 30000)\n(assert true)\n(check-sat)\n(exit)",
            })
        cls.records.append({
            "kind": "query", "family": "body", "label": "transport-spelling",
            "class": "encoding", "source_bound": False, "expected": "unsat",
            "smt2": "(set-option :timeout 30000)\n(assert false)\n(check-sat)\n(exit)\n",
        })
        cls.records.append({
            "kind": "refusal", "family": "slice6", "label": "transport-refusal",
            "class": "encoding", "source_bound": False, "reason": "synthetic refusal",
        })

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.input = self.directory / "capture.stdout"
        self.input.write_bytes(capture(self.records))
        self.verifier = self.directory / "verifier"
        self.verifier.write_bytes(b"synthetic transport executable bytes")
        self.out = self.directory / "export"

    def test_exact_queries_and_encoding_newline_survive_export(self):
        manifest = EXPORT.export(self.out, self.input, self.verifier)
        self.assertFalse(manifest["proof_credit"])
        self.assertIn("authenticated separately", manifest["authority"])
        self.assertEqual(len(manifest["snapshots"]), 13)
        self.assertEqual(len(manifest["refusals"]), 1)
        self.assertEqual(self.out.stat().st_mode & 0o777, 0o700)
        for source, exported in zip(
            (record for record in self.records if record["kind"] == "query"),
            manifest["queries"], strict=True,
        ):
            data = (self.out / exported["file"]).read_bytes()
            self.assertEqual(data, source["smt2"].encode())
            self.assertEqual(EXPORT.digest(data), exported["query_sha256"])

    def test_missing_footer_is_refused_before_destination_creation(self):
        self.input.write_bytes(b"\n".join(self.input.read_bytes().splitlines()[:-2]) + b"\n")
        with self.assertRaisesRegex(ValueError, "completion footer"):
            EXPORT.export(self.out, self.input, self.verifier)
        self.assertFalse(self.out.exists())

    def test_changed_record_bytes_without_new_digest_are_refused(self):
        data = self.input.read_bytes().replace(b"transport-spelling", b"changed-spelling")
        with self.assertRaisesRegex(ValueError, "digest mismatch"):
            EXPORT.read_capture(data)

    def test_deleted_canonical_query_with_valid_footer_is_refused(self):
        records = copy.deepcopy(self.records)
        del records[0]
        _, records = EXPORT.read_capture(capture(records))
        with self.assertRaisesRegex(ValueError, "canonical matrix differs"):
            EXPORT.bind_snapshots(records)

    def test_changed_canonical_query_with_valid_footer_is_refused(self):
        records = copy.deepcopy(self.records)
        records[0]["smt2"] = records[0]["smt2"].replace(":timeout 30000", ":timeout 30001")
        _, records = EXPORT.read_capture(capture(records))
        with self.assertRaisesRegex(ValueError, "canonical matrix differs"):
            EXPORT.bind_snapshots(records)

    def test_duplicate_record_with_valid_footer_is_refused(self):
        records = self.records + [self.records[0]]
        with self.assertRaisesRegex(ValueError, "duplicate matrix record"):
            EXPORT.read_capture(capture(records))

    def test_missing_negative_family_is_refused(self):
        records = [record for record in self.records if not (
            record["family"] == "memory" and record["class"] == "wrong-lowering")]
        _, records = EXPORT.read_capture(capture(records))
        with self.assertRaisesRegex(ValueError, "missing actual wrong-lowering"):
            EXPORT.bind_snapshots(records)

    def test_wrong_expected_verdict_or_authority_tag_is_refused(self):
        for field, value in (("expected", "sat"), ("source_bound", False)):
            with self.subTest(field=field):
                records = copy.deepcopy(self.records)
                records[0][field] = value
                with self.assertRaises(ValueError):
                    EXPORT.read_capture(capture(records))

    def test_existing_destination_is_preserved(self):
        self.out.mkdir()
        sentinel = self.out / "sentinel"
        sentinel.write_text("preserve")
        with self.assertRaises(FileExistsError):
            EXPORT.export(self.out, self.input, self.verifier)
        self.assertEqual(sentinel.read_text(), "preserve")

    def test_broken_destination_symlink_is_preserved(self):
        self.out.symlink_to(self.directory / "missing", target_is_directory=True)
        with self.assertRaises(FileExistsError):
            EXPORT.export(self.out, self.input, self.verifier)
        self.assertTrue(self.out.is_symlink())


if __name__ == "__main__":
    unittest.main()
