#!/usr/bin/python3
"""Exercise maintained consumer CLI refusal before any output/artifact copy.

Run explicitly with a real exact compiler configuration. These negative controls
never load the fake backend fixtures or compile a target Rust crate.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

CONFIGURATION = None
DRIVER = None
RECORD_DIRECTORY = None

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

class ConsumerBackendPreflight(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if CONFIGURATION is None:
            raise unittest.SkipTest("Run explicitly with --configuration for real compiler identity checks")
        cls.configuration = json.loads(CONFIGURATION.read_text())
        cls.compiler = Path(cls.configuration["toolchain"]) / "bin/trustc"
        cls.compiler_sha256 = sha(cls.compiler)
        cls.target = cls.configuration["target"]
        cls.records = []
        cls.driver_sha256 = sha(DRIVER)
        cls.configuration_sha256 = sha(CONFIGURATION)

    def run_case(self, case, transform, expected_message):
        with tempfile.TemporaryDirectory(prefix="consumer-backend-" + case + "-") as temporary:
            directory = Path(temporary)
            library_backend = directory / "library-backend.not-loaded"
            library_backend.write_bytes(b"test-only library receipt fixture; never loaded")
            candidate_backend = directory / "consumer-backend.not-loaded"
            candidate_backend.write_bytes(b"test-only coherent expected bytes; never loaded")
            library_record = directory / "build.json"
            library_record.write_text(json.dumps({
                "complete": True, "build_passed": True, "target": self.target,
                "execution": {"command": [str(self.compiler), "--target", self.target]},
                "backend": {"path": str(library_backend), "sha256": sha(library_backend)},
                "backend_source_head": "test-only-receipt",
                "compiler_sha256": self.compiler_sha256,
            }) + "\n")
            candidate_record = directory / "backend-build.json"
            candidate = {
                "qualified": True, "source_unchanged": True, "exit_code": 0,
                "compiler_sha256": self.compiler_sha256, "head": "test-only-receipt",
                "backend": {"path": str(candidate_backend), "sha256": sha(candidate_backend),
                            "immutable_for_subsequent_reproductions": True},
            }
            transform(candidate, candidate_record, candidate_backend)
            if not candidate_record.exists():
                candidate_record.write_text(json.dumps(candidate) + "\n")
            expected_output = directory / "consumer-output"
            before_library = sha(library_record)
            before_library_backend = sha(library_backend)
            command = ["python3", str(DRIVER), "--configuration", str(CONFIGURATION),
                       str(library_record), "--backend-build", str(candidate_record),
                       "--label", "consumer-output"]
            result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, timeout=60)
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn(expected_message, result.stdout)
            self.assertFalse(expected_output.exists(), "Refusal must precede output creation/library copying")
            self.assertEqual(sha(library_record), before_library)
            self.assertEqual(sha(library_backend), before_library_backend)
            row = {"case": case, "command": command, "returncode": result.returncode,
                   "expected_refusal_found": True, "output_absent": True,
                   "library_receipt_unchanged": True, "library_backend_fixture_unchanged": True,
                   "no_target_compile_or_backend_load_attempted": True}
            if RECORD_DIRECTORY:
                log = RECORD_DIRECTORY / (case + ".log")
                log.write_text(result.stdout)
                row.update(log=str(log), log_sha256=sha(log))
            self.records.append(row)

    def test_bad_receipt_refuses_before_output(self):
        def malformed(candidate, record, artifact):
            record.write_text("{ malformed receipt\n")
        self.run_case("bad-receipt", malformed, "JSONDecodeError")

    def test_incoherent_receipt_refuses_before_output(self):
        def incoherent(candidate, record, artifact):
            candidate["source_unchanged"] = False
        self.run_case("incoherent-receipt", incoherent, "consumer backend must be a successful source-coherent build")

    def test_mismatched_compiler_refuses_before_output(self):
        def mismatch(candidate, record, artifact):
            candidate["compiler_sha256"] = "0" * 64
        self.run_case("mismatched-compiler", mismatch, "consumer backend and exact library compiler identities differ")

    def test_tampered_artifact_refuses_before_output(self):
        def tamper(candidate, record, artifact):
            artifact.write_bytes(b"replacement bytes after receipt hash was captured")
        self.run_case("tampered-artifact", tamper, "sealed consumer backend artifact differs from its receipt")

    @classmethod
    def tearDownClass(cls):
        assert sha(DRIVER) == cls.driver_sha256
        assert sha(CONFIGURATION) == cls.configuration_sha256
        if RECORD_DIRECTORY:
            (RECORD_DIRECTORY / "results.json").write_text(json.dumps({
                "schema": "trust-cg.consumer-backend-negative-preflights.v1",
                "driver": str(DRIVER), "driver_sha256": cls.driver_sha256,
                "configuration_sha256": cls.configuration_sha256,
                "compiler_sha256": cls.compiler_sha256,
                "driver_and_configuration_unchanged": True,
                "all_four_required_cases_passed": len(cls.records) == 4,
                "cases": cls.records,
                "scope": "Actual maintained consumer CLI refuses four bad backend-receipt boundaries before creating consumer output. Real compiler identity preflight only; no target Rust compilation, fake backend loading, runtime/std/sysroot/proof qualification.",
            }, indent=2) + "\n")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--configuration", type=Path, required=True)
    parser.add_argument("--driver", type=Path, default=Path(__file__).resolve().parents[1] / "real_std_sysroot_consumers.py")
    parser.add_argument("--record-directory", type=Path)
    args, remaining = parser.parse_known_args()
    CONFIGURATION = args.configuration.resolve()
    DRIVER = args.driver.resolve()
    if args.record_directory:
        RECORD_DIRECTORY = args.record_directory.resolve()
        RECORD_DIRECTORY.mkdir(parents=True)
    unittest.main(argv=[__file__, *remaining])
