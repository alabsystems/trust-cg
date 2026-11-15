#!/usr/bin/python3
"""Preflight and backend-selection boundaries for the real-library driver."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import runpy

SCRIPTS = Path(__file__).resolve().parents[1]
DRIVER = SCRIPTS / "real_std_sysroot.py"
WRAPPER = SCRIPTS / "real_std_sysroot_wrapper.py"
REPOSITORY = Path(subprocess.check_output(["git", "-C", str(SCRIPTS), "rev-parse", "--show-toplevel"], text=True).strip())
COMMIT = subprocess.check_output(["git", "-C", str(REPOSITORY), "rev-parse", "HEAD"], text=True).strip()
TARGET = "aarch64-unknown-linux-gnu"
HELPERS = runpy.run_path(str(DRIVER))

class RealSysrootBoundaries(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.out = Path(self.temporary.name)
        self.toolchain = self.out / "toolchain"
        (self.toolchain / "bin").mkdir(parents=True)
        self.compiler = self.toolchain / "bin/trustc"
        self.compiler.write_text("#!/usr/bin/python3\nimport sys\nif '-vV' in sys.argv:\n print(" + repr("binary: trustc\ncommit-hash: " + COMMIT + "\nhost: " + TARGET) + ")\nelif '--print=target-list' in sys.argv:\n print(" + repr(TARGET) + ")\n")
        self.compiler.chmod(0o755)
        (self.toolchain / "bin/targo").write_text("fixture")
        self.config = {"repository": str(REPOSITORY), "output": str(self.out / "library-output"),
                       "toolchain": str(self.toolchain), "compiler_source": str(REPOSITORY),
                       "compiler_commit": COMMIT, "target": TARGET}

    def driver(self, configuration):
        path = self.out / "configuration.json"
        path.write_text(json.dumps(configuration))
        return subprocess.run([sys.executable, str(DRIVER), "--configuration", str(path), "prepare"], capture_output=True, text=True)

    def wrapper(self, options, lane="full-cg"):
        (self.out / "invocations").mkdir(exist_ok=True)
        path = self.out / "wrapper.json"
        path.write_text(json.dumps({"lane": lane, "opt": 0, "target": TARGET,
                                   "backend": {"path": str(self.out / "sealed-backend.so")},
                                   "invocations": str(self.out / "invocations" / lane)}))
        environment = dict(os.environ, STD_CORRECTNESS_CONFIG=str(path))
        return subprocess.run([sys.executable, str(WRAPPER), str(self.compiler), *options], env=environment, capture_output=True, text=True)

    def test_help_needs_no_configuration_and_environment_cannot_select_one(self):
        environment = dict(os.environ, STD_SYSROOT_DRIVER_CONFIGURATION="/missing/configuration.json")
        for name in ["real_std_sysroot.py", "real_std_sysroot_consumers.py", "real_std_body_census.py"]:
            result = subprocess.run([sys.executable, str(SCRIPTS / name), "--help"], env=environment, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
        result = subprocess.run([sys.executable, str(DRIVER), "prepare"], env=environment, capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn("--configuration", result.stderr)

    def test_compiler_commit_mismatch_rejects_before_source_creation(self):
        configuration = dict(self.config, compiler_commit="0" * 40)
        result = self.driver(configuration)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("compiler -vV and configured source commit differ", result.stderr)
        self.assertFalse(Path(configuration["output"]).exists())

    def test_unknown_target_rejects_before_source_creation(self):
        configuration = dict(self.config, target="unknown-target")
        result = self.driver(configuration)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("configured target is not supported", result.stderr)
        self.assertFalse(Path(configuration["output"]).exists())

    def test_print_on_real_crate_cannot_take_llvm_lane(self):
        result = self.wrapper(["--crate-name", "core", "input.rs", "--target", TARGET, "--print=file-names"])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("actual Rust crate may not bypass", result.stderr)

    def test_wrong_or_duplicate_target_rejects(self):
        for target_options in [["--target=x86_64-unknown-linux-gnu"], ["--target", TARGET, "--target", TARGET]]:
            result = self.wrapper(["--crate-name", "core", "input.rs", *target_options])
            self.assertNotEqual(result.returncode, 0)

    def test_real_target_crate_is_recorded_with_cg_backend(self):
        result = self.wrapper(["--crate-name", "core", "input.rs", "--target", TARGET])
        self.assertEqual(result.returncode, 0, result.stderr)
        (receipt,) = (self.out / "invocations" / "full-cg").glob("*.json")
        record = json.loads(receipt.read_text())
        self.assertTrue(record["target_crate"])
        self.assertEqual(record["backend"], "cg")
        self.assertIn("-Zcodegen-backend=" + str(self.out / "sealed-backend.so"), record["command"])

    def test_target_lanes_keep_canonical_exports_and_proof_policy(self):
        for lane in ("llvm", "full-cg", "full-cg-proof", "mixed"):
            with self.subTest(lane=lane):
                result = self.wrapper(["--crate-name", "alloc", "input.rs", "--target", TARGET], lane)
                self.assertEqual(result.returncode, 0, result.stderr)
                (receipt,) = (self.out / "invocations" / lane).glob("*.json")
                record = json.loads(receipt.read_text())
                self.assertTrue(record["canonical_query_providers_requested"])
                self.assertIn("-Ztrust-ir-lower=on", record["command"])
                self.assertEqual(record["backend"], "llvm" if lane == "llvm" else "cg")
                knobs = [arg for arg in record["command"] if arg.startswith("-Ztrust-ir-cg-args=")]
                self.assertEqual(len(knobs), 0 if lane == "llvm" else 1)
                if knobs:
                    self.assertEqual("no-proof-certs" in knobs[0], lane != "full-cg-proof")

    def test_named_cargo_probe_is_recorded_separately(self):
        result = self.wrapper(["-", "--crate-name", "___", "--print=file-names", "--target", TARGET])
        self.assertEqual(result.returncode, 0, result.stderr)
        (receipt,) = (self.out / "invocations" / "full-cg").glob("*.json")
        record = json.loads(receipt.read_text())
        self.assertFalse(record["target_crate"])
        self.assertEqual(record["backend"], "llvm")
        self.assertFalse(record["canonical_query_providers_requested"])
        self.assertNotIn("-Ztrust-ir-lower=on", record["command"])

class RequiredUnitAccounting(unittest.TestCase):
    def unit(self, name, source=None, platform=TARGET, kind="lib"):
        return {"pkg_id": "fixture#" + name, "platform": platform, "mode": "build",
                "features": ["std"], "target": {"name": name, "kind": [kind],
                "src_path": source or "/sources/" + name + "/lib.rs"}}

    def invocation(self, name, source=None, backend="cg", canonical=True, complete=True, code=0):
        return {"crate": name, "target": TARGET, "target_crate": True, "backend": backend,
                "cwd": "/sources", "complete": complete, "returncode": code,
                "command": ["trustc", source or "/sources/" + name + "/lib.rs",
                            "--cfg", 'feature="std"'] + (["-Ztrust-ir-lower=on"] if canonical else [])}

    def outcomes(self, units, invocations, lane="full-cg"):
        graph = {"version": 1, "units": units, "roots": [0]}
        return HELPERS["required_unit_outcomes"](graph, invocations, TARGET, lane)

    def test_dependency_failure_cannot_remove_unreached_unit(self):
        rows = self.outcomes([self.unit("core"), self.unit("std")],
                             [self.invocation("core", code=1)])
        self.assertEqual([row["outcome"] for row in rows], ["failed", "not_attempted"])
        self.assertFalse(all(row["outcome"] == "compiled" for row in rows))

    def test_same_crate_name_does_not_credit_another_source_version(self):
        rows = self.outcomes([self.unit("dep", "/version1/lib.rs"),
                              self.unit("dep", "/version2/lib.rs")],
                             [self.invocation("dep", "/version1/lib.rs")])
        self.assertEqual([row["outcome"] for row in rows], ["compiled", "not_attempted"])

    def test_llvm_fallback_noncanonical_or_incomplete_compile_cannot_pass(self):
        cases = [(self.invocation("core", backend="llvm"), "wrong_backend"),
                 (self.invocation("core", canonical=False), "noncanonical"),
                 (self.invocation("core", complete=False, code=None), "incomplete")]
        for invocation, expected in cases:
            with self.subTest(expected=expected):
                (row,) = self.outcomes([self.unit("core")], [invocation])
                self.assertEqual(row["outcome"], expected)

    def test_host_and_build_script_units_do_not_inflate_target_count(self):
        rows = self.outcomes([self.unit("core"), self.unit("tool", platform=None),
                              self.unit("build_script_build", kind="custom-build")],
                             [self.invocation("core")])
        self.assertEqual([(row["crate"], row["outcome"]) for row in rows], [("core", "compiled")])

    def test_missing_graph_or_missing_target_roots_refuses(self):
        for graph in [{"version": 1, "units": [], "roots": []},
                      {"version": 1, "units": [self.unit("host", platform=None)], "roots": [0]}]:
            with self.assertRaises(AssertionError):
                HELPERS["required_unit_outcomes"](graph, [], TARGET, "full-cg")
        with self.assertRaises(AssertionError):
            HELPERS["unit_graph_from_log"]('{"reason":"build-finished","success":true}\n')

    def test_log_parser_ignores_other_json_diagnostics(self):
        graph = {"version": 1, "units": [self.unit("core")], "roots": [0]}
        log = '{"reason":"build-finished","success":true}\n' + json.dumps(graph) + "\n"
        self.assertEqual(HELPERS["unit_graph_from_log"](log), graph)


if __name__ == "__main__":
    unittest.main()
