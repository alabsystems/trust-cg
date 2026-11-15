"""Contract controls for the standalone Linux x86-64 bridge diagnostic."""

from __future__ import annotations

import contextlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "check_linux_x86_64_bridge", ROOT / "scripts/check_linux_x86_64_bridge.py"
)
assert SPEC is not None and SPEC.loader is not None
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)

# Independent of the runner inventory: removing a required target or reducing
# its minimum must fail this test, rather than changing the expected result.
PINNED_TARGETS = (
    ("bridge_differential_x86", 21),
    ("m140_x86_scalar_pair_return_xback", 1),
    ("m141_x86_scalar_pair_arg_xback", 1),
    ("m144_x86_pair_arg_exhaustion_xback", 1),
    ("m145_x86_indirect_arg_xback", 2),
    ("m136_x86_c_abi_sse_aggregate", 2),
    ("m137_x86_c_abi_zst_packed_union", 4),
)


def transcript(passed: int, *, stdout: str = "", ignored: int = 0, filtered: int = 0) -> str:
    lines = [f"running {passed + ignored} tests"]
    lines.extend(f"test test_{index} ... ok" for index in range(passed))
    lines.extend(f"test ignored_{index} ... ignored" for index in range(ignored))
    if stdout:
        lines += ["", "successes:", "---- test_0 stdout ----", stdout, "", "successes:", "    test_0"]
    lines.append(
        f"test result: ok. {passed} passed; 0 failed; {ignored} ignored; "
        f"0 measured; {filtered} filtered out; finished in 0.01s"
    )
    return "\n".join(lines) + "\n"


def artifact(name: str, executable: Path) -> dict:
    return {
        "reason": "compiler-artifact", "manifest_path": str(GATE.MANIFEST),
        "target": {"name": name, "kind": ["test"]}, "profile": {"test": True},
        "filenames": [str(executable)], "executable": str(executable),
    }


class LinuxX86BridgeDiagnosticTests(unittest.TestCase):
    def test_inventory_and_host_identity_are_pinned(self) -> None:
        self.assertEqual(GATE.HOST, "x86_64-unknown-linux-gnu")
        self.assertEqual(GATE.SHARED.HOST, GATE.HOST)
        self.assertEqual(GATE.TARGETS, PINNED_TARGETS)
        self.assertEqual(GATE.CORPUS_CASE_FLOOR, 125)
        self.assertEqual(GATE.inventory_problems(), [])

    def test_inventory_rejects_shrunk_corpus_and_test_minimum(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            tests = Path(temporary)
            (tests / "support").mkdir()
            (tests / "support/host_target.rs").write_text(f'"{GATE.HOST}"\n')
            for name, minimum in PINNED_TARGETS:
                cases = ''.join(f'    name: "case_{i}",\n' for i in range(124)) if name == PINNED_TARGETS[0][0] else ''
                (tests / f"{name}.rs").write_text(
                    'const TARGET: &str = host_target_support::X86_64_TARGET;\n'
                    + '#[test]\nfn check() {}\n' * (minimum - (name == PINNED_TARGETS[1][0])) + cases
                )
            problems = GATE.inventory_problems(tests)
        self.assertTrue(any("corpus case inventory" in problem for problem in problems), problems)
        self.assertTrue(any("m140_x86_scalar_pair_return_xback: pinned minimum" in problem for problem in problems), problems)

    def test_libtest_requires_named_native_passes_without_skips(self) -> None:
        for name, minimum in PINNED_TARGETS:
            with self.subTest(name=name):
                good = GATE.classify_target(name, minimum, 0, transcript(minimum))
                self.assertEqual(good["status"], "pass", good)
                self.assertEqual(good["counts"]["passed"], minimum)
                for bad in (
                    GATE.classify_target(name, minimum, 0, transcript(max(0, minimum - 1))),
                    GATE.classify_target(name, minimum, 0, transcript(minimum, ignored=1)),
                    GATE.classify_target(name, minimum, 0, transcript(minimum, filtered=1)),
                    GATE.classify_target(name, minimum, 0, transcript(minimum, stdout="skipping: no std")),
                    GATE.classify_target(name, minimum, 0, transcript(minimum, stdout="TCG-PROOF-465 refused")),
                    GATE.classify_target(name, minimum, 124, transcript(minimum)),
                    GATE.classify_target(name, minimum, 0,
                                         f"running {minimum} tests\ntest result: ok. {minimum} passed; "
                                         "0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\n"),
                ):
                    self.assertEqual(bad["status"], "fail", bad)

    def test_corpus_fail_closed_notes_are_disclosed_not_called_admission(self) -> None:
        result = GATE.classify_target(
            "bridge_differential_x86", 21, 0,
            transcript(21, stdout="note: `case` (opt=0) trust-cg failed closed (safe)"),
        )
        self.assertEqual(result["status"], "pass", result)
        self.assertEqual(result["corpus_fail_closed_notes"], 1)

    def test_cargo_test_build_requires_exact_release_artifacts(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            target_dir = Path(temporary)
            deps = target_dir / "release/deps"
            deps.mkdir(parents=True)
            rows = []
            for name, _ in PINNED_TARGETS:
                path = deps / f"{name}-123"
                path.write_bytes(b"test executable")
                path.chmod(0o755)
                rows.append(artifact(name, path))
            completed = {"reason": "build-finished", "success": True}
            transcript_json = "\n".join(json.dumps(row) for row in [*rows, completed])
            good = GATE.classify_test_build(0, transcript_json, target_dir)
            self.assertEqual(good["status"], "pass", good)
            self.assertEqual(len(good["executables"]), len(PINNED_TARGETS))
            for bad_rows in (rows[:-1], [*rows, rows[0]],
                             [{**rows[0], "filenames": ["/tmp/other"]}, *rows[1:]]):
                bad = GATE.classify_test_build(
                    0, "\n".join(json.dumps(row) for row in [*bad_rows, completed]), target_dir,
                )
                self.assertEqual(bad["status"], "fail", bad)
            self.assertEqual(GATE.classify_test_build(1, transcript_json, target_dir)["status"], "fail")

    def test_preflight_refuses_non_native_host_before_toolchain_probe(self) -> None:
        with mock.patch.object(GATE.sys, "platform", "darwin"):
            with self.assertRaisesRegex(RuntimeError, "Linux x86_64"):
                GATE.preflight(Path("/tmp/cache"))

    def test_preflight_binds_host_std_and_real_targo_lane(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary).resolve()
            target_lib = base / "lib/rustlib" / GATE.HOST / "lib"
            target_lib.mkdir(parents=True)
            (target_lib / "libstd-fixture.rlib").write_bytes(b"std")
            tools = {name: str(base / name) for name in ("git", "env", "cc", "clang")}
            for path in tools.values():
                Path(path).write_bytes(b"host tool")
            toolchain = {
                "host": GATE.HOST, "targo": "/fixture/bin/targo",
                "target_lib_dir": str(target_lib), "compiler": "/fixture/bin/trustc",
            }
            probes = []

            def probe(command):
                probes.append(command)
                return "targo 1.0" if command[-2:] == ["--unverified", "--version"] else "fixture version"

            with mock.patch.object(GATE.sys, "platform", "linux"), \
                 mock.patch.object(GATE.platform, "machine", return_value="x86_64"), \
                 mock.patch.object(GATE.shutil, "which", side_effect=lambda name: tools.get(name)), \
                 mock.patch.object(GATE.TOOLCHAIN, "resolve", return_value=toolchain), \
                 mock.patch.object(GATE.SHARED, "probe", side_effect=probe), \
                 mock.patch.object(GATE.SHARED, "source_provenance", return_value={"source_fingerprint": "pinned"}), \
                 mock.patch.object(GATE, "inventory_problems", return_value=[]), \
                 mock.patch.dict(GATE.os.environ, {}, clear=True):
                result = GATE.preflight(base / "cache", "/fixture/bin/trustc")
                self.assertEqual(result["host"], GATE.HOST)
                self.assertEqual(result["targo_unverified_version"], "targo 1.0")
                self.assertIn(["/fixture/bin/targo", "--unverified", "--version"], probes)
                toolchain["host"] = "aarch64-unknown-linux-gnu"
                with self.assertRaisesRegex(RuntimeError, "pinned Trust compiler host"):
                    GATE.preflight(base / "cache")
                toolchain["host"] = GATE.HOST
                (target_lib / "libstd-fixture.rlib").unlink()
                with self.assertRaisesRegex(RuntimeError, "lacks native rust-std"):
                    GATE.preflight(base / "cache")
                (target_lib / "libstd-fixture.rlib").write_bytes(b"std")
                with mock.patch.dict(GATE.os.environ, {"RUSTFLAGS": "-C opt-level=0"}):
                    with self.assertRaisesRegex(RuntimeError, "ambient compiler/backend overrides"):
                        GATE.preflight(base / "cache")
        with mock.patch.object(GATE.sys, "platform", "linux"), \
             mock.patch.object(GATE.platform, "machine", return_value="aarch64"):
            with self.assertRaisesRegex(RuntimeError, "Linux x86_64"):
                GATE.preflight(Path("/tmp/cache"))

    def fixture_run(self, *, change_snapshot: bool = False, skip: bool = False) -> tuple[int, dict, list[list[str]]]:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary).resolve()
            output = base / "report"
            target_dir = base / "cargo"
            backend = target_dir / "release" / GATE.BACKEND_NAME
            provenance = {
                "host": GATE.HOST, "source_fingerprint": "pinned", "dirty": False,
                "tools": {"git": "/usr/bin/git", "env": "/usr/bin/env"},
                "toolchain": {"compiler": "/fixture/bin/trustc", "targo": "/fixture/bin/targo"},
            }
            commands = []

            def fake_run(command, log, _timeout):
                commands.append(list(command))
                if "build" in command:
                    backend.parent.mkdir(parents=True)
                    backend.write_bytes(b"fresh backend")
                    rows = [{
                        "reason": "compiler-artifact", "manifest_path": str(GATE.MANIFEST),
                        "target": {"name": "rustc_codegen_trust_cg", "kind": ["dylib"]},
                        "filenames": [str(backend)],
                    }, {"reason": "build-finished", "success": True}]
                elif "test" in command and "--no-run" in command:
                    deps = target_dir / "release/deps"
                    deps.mkdir(parents=True)
                    rows = []
                    for name, _ in PINNED_TARGETS:
                        path = deps / f"{name}-123"
                        path.write_bytes(b"test executable")
                        path.chmod(0o755)
                        rows.append(artifact(name, path))
                    rows.append({"reason": "build-finished", "success": True})
                else:
                    self.assertIn("--show-output", command)
                    self.assertIn(f"CARGO_TARGET_DIR={output / 'runtime-target'}", command)
                    name = Path(command[-3]).name.removesuffix("-123")
                    minimum = dict(PINNED_TARGETS)[name]
                    log.write_text(transcript(
                        minimum, stdout="skipping: no std" if skip and name == PINNED_TARGETS[0][0] else "",
                    ))
                    if change_snapshot and name == PINNED_TARGETS[0][0]:
                        snapshot = output / "runtime-target/release" / GATE.BACKEND_NAME
                        snapshot.chmod(0o644)
                        snapshot.write_bytes(b"tampered backend")
                    return {"returncode": 0, "interrupted_signal": None, "log": log.name}
                log.write_text("\n".join(json.dumps(row) for row in rows) + "\n")
                return {"returncode": 0, "interrupted_signal": None, "log": log.name}

            with mock.patch.object(GATE, "preflight", return_value=provenance), \
                 mock.patch.object(GATE.SHARED, "source_provenance", return_value={"source_fingerprint": "pinned"}), \
                 mock.patch.object(GATE.SHARED, "proof_tool_identities", return_value={"ay": {}, "clean": {}}), \
                 mock.patch.object(GATE.SHARED, "proof_tool_problems", return_value=[]), \
                 mock.patch.object(GATE.SHARED, "proof_tool_changes", return_value=[]), \
                 mock.patch.object(GATE, "run_step", side_effect=fake_run), \
                 contextlib.redirect_stdout(io.StringIO()):
                code = GATE.main(["--out", str(output), "--target-dir", str(target_dir)])
            report = json.loads((output / "report.json").read_text())
            return code, report, commands

    def test_orchestration_builds_once_and_runs_all_targets_against_snapshot(self) -> None:
        code, report, commands = self.fixture_run()
        self.assertEqual(code, 0, report)
        self.assertEqual(report["status"], "pass")
        self.assertEqual(len(report["targets"]), len(PINNED_TARGETS))
        self.assertEqual(len(commands), len(PINNED_TARGETS) + 2)
        self.assertEqual(report["backend_after_build"]["sha256"], report["backend_snapshot"]["sha256"])
        self.assertEqual(report["required_minimum_passes"], sum(minimum for _, minimum in PINNED_TARGETS))

    def test_runtime_skip_and_snapshot_mutation_fail_the_run(self) -> None:
        code, report, _ = self.fixture_run(skip=True)
        self.assertEqual(code, 1, report)
        self.assertEqual(report["status"], "fail")
        self.assertEqual(len(report["targets"]), len(PINNED_TARGETS))
        self.assertEqual(report["targets"][0]["status"], "fail")
        code, report, _ = self.fixture_run(change_snapshot=True)
        self.assertEqual(code, 1, report)
        self.assertEqual(report["status"], "fail")
        self.assertTrue(any("snapshot changed" in error for error in report["errors"]), report)

    def test_failed_preflight_report_is_host_bound_and_never_a_pass(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "report"
            with mock.patch.object(GATE, "preflight", side_effect=RuntimeError("controlled host refusal")), \
                 contextlib.redirect_stdout(io.StringIO()):
                code = GATE.main(["--out", str(output)])
            report = json.loads((output / "report.json").read_text())
        self.assertEqual(code, 1)
        self.assertEqual(report["status"], "fail")
        self.assertEqual(report["host"], GATE.HOST)
        self.assertEqual(report["required_targets"], dict(PINNED_TARGETS))
        self.assertEqual(report["targets"], [])


if __name__ == "__main__":
    unittest.main()
