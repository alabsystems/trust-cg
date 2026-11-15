#!/usr/bin/env python3
# Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
"""Real runner/process controls; NEVER a Trust compiler or native ABI test.

The executable stand-in only interprets runner arguments and writes Python
programs with controlled exit statuses. It does not parse or compile Rust,
load a backend, produce object code, or supply proof/ABI qualification.
Every run and its generated artifacts are retained at the printed directory.
"""

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parents[2]
RUNNERS = {
    "regclass": ROOT / "benchmarks/regclass-xback/run.sh",
    "sret": ROOT / "benchmarks/sret-xback/run.sh",
}
SUPERVISOR = ROOT / "scripts/run_with_timeout.py"
FIXTURE = r'''
import json
import os
from pathlib import Path
import signal
import sys

args = sys.argv[1:]
scenario = os.environ["RUNNER_CONTROL_SCENARIO"]
trace = Path(os.environ["RUNNER_CONTROL_TRACE"])
backend = "tcg" if any(a.startswith("-Zcodegen-backend=") for a in args) else "llvm"
kind = args[args.index("--crate-type") + 1]
callee = Path(args[args.index("-L") + 1]).name if kind == "bin" else None
with trace.open("a") as stream:
    stream.write(json.dumps({"phase": "compile-stand-in", "backend": backend,
                             "callee": callee, "kind": kind, "args": args}) + "\n")

def fail(status, tagged=True, crash=False):
    message = "[TCG-ARG-ABI] controlled refusal" if tagged else "unrelated compiler failure"
    print(json.dumps({"$message_type": "diagnostic", "message": message,
                      "level": "error", "code": None, "children": []}),
          file=sys.stderr, flush=True)
    if crash:
        os.kill(os.getpid(), signal.SIGTERM)
    raise SystemExit(status)

if backend == "tcg":
    if scenario == "cg_callee_decline" and kind == "rlib":
        fail(1)
    if scenario == "cg_caller_decline" and kind == "bin":
        fail(1)
    if scenario == "cg_unrelated":
        fail(1, tagged=False)
    if scenario == "cg_status101":
        fail(101)
    if scenario == "cg_signal":
        fail(1, crash=True)
if backend == "llvm" and kind == "rlib" and scenario == "llvm_callee_fail":
    fail(1)  # Even a tagged diagnostic may not decline the LLVM control.
oracle = backend == "llvm" and callee == "llvm"
if kind == "bin" and oracle and scenario == "llvm_caller_fail":
    fail(1)

if kind == "rlib":
    output = Path(args[args.index("--out-dir") + 1])
    # The sret runner requires this exact filename; regclass accepts *.rlib.
    (output / "libsretcallee.rlib").write_bytes(b"PROCESS STAND-IN, NOT A RUST LIBRARY\n")
else:
    output = Path(args[args.index("-o") + 1])
    status = 41 if ((oracle and scenario == "llvm_wrong") or
                    (not oracle and scenario == "cg_wrong")) else 42
    crash = ((oracle and scenario == "llvm_crash") or
             (not oracle and scenario == "cg_crash"))
    record = {"phase": "program-stand-in", "backend": backend, "callee": callee,
              "oracle": oracle, "status": status, "crash": crash}
    program = ("#!" + sys.executable + "\nimport json, os, signal\n"
               + "with open(" + repr(str(trace)) + ", 'a') as stream:\n"
               + "    stream.write(" + repr(json.dumps(record) + "\n") + ")\n"
               + ("os.kill(os.getpid(), signal.SIGTERM)\n" if crash else
                  "raise SystemExit(" + str(status) + ")\n"))
    output.write_text(program)
    output.chmod(0o700)
'''


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_identity():
    paths = [Path(__file__), SUPERVISOR,
             ROOT / "benchmarks/regclass-xback/refusal.py", *RUNNERS.values()]
    for runner in RUNNERS.values():
        paths.extend(sorted((runner.parent / "progs").glob("*.rs")))
    return {str(path): sha(path) for path in paths}


class RunnerProcessContract(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.artifacts = Path(tempfile.mkdtemp(prefix="trust-cg-runner-process-controls-"))
        cls.sequence = 0
        # Removed after the class unless TRUST_CG_KEEP_TEST_OBJECTS asks to keep it.
        if os.environ.get("TRUST_CG_KEEP_TEST_OBJECTS"):
            print(f"PROCESS CONTROLS ONLY; retained artifacts: {cls.artifacts}", flush=True)
        else:
            cls.addClassCleanup(shutil.rmtree, cls.artifacts, ignore_errors=True)

    def run_case(self, runner_name, scenario, missing=False):
        type(self).sequence += 1
        case = self.artifacts / f"{self.sequence:03}-{runner_name}-{scenario}"
        case.mkdir()
        temporary = case / "retained-runner-artifacts"
        temporary.mkdir()
        fixture = case / "not-a-compiler.py"
        fixture.write_text("#!" + sys.executable + "\n" + FIXTURE)
        fixture.chmod(0o700)
        backend = case / "not-a-backend.fixture"
        backend.write_text("PROCESS STAND-IN ONLY; NOT A LOADABLE BACKEND\n")
        trace = case / "process-trace.jsonl"
        compiler = case / "missing-compiler" if missing else fixture
        command = ["bash", str(RUNNERS[runner_name]), str(backend), str(compiler), "0"]
        env = {
            "PATH": str(Path(sys.executable).parent) + ":/usr/bin:/bin",
            "LANG": "C", "LC_ALL": "C", "TMPDIR": str(temporary),
            "RUNNER_CONTROL_SCENARIO": scenario,
            "RUNNER_CONTROL_TRACE": str(trace),
        }
        before = source_identity()
        (case / "command.json").write_text(json.dumps({
            "claim": "ordinary controlled processes, NOT compiler/native ABI qualification",
            "command": command, "environment": env, "cwd": str(ROOT),
            "outer_timeout_seconds": 45, "fixture_sha256": sha(fixture),
            "python": sys.executable, "python_sha256": sha(Path(sys.executable)),
            "source_before": before,
        }, indent=2) + "\n")
        started = time.monotonic()
        try:
            result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, timeout=45)
        except subprocess.TimeoutExpired as error:
            (case / "stdout").write_bytes(error.stdout or b"")
            (case / "stderr").write_bytes(error.stderr or b"")
            (case / "outer-timeout.json").write_text(json.dumps({
                "elapsed_seconds": time.monotonic() - started, "source_after": source_identity(),
            }) + "\n")
            raise
        (case / "stdout").write_bytes(result.stdout)
        (case / "stderr").write_bytes(result.stderr)
        after = source_identity()
        (case / "result.json").write_text(json.dumps({
            "returncode": result.returncode, "elapsed_seconds": time.monotonic() - started,
            "source_after": after, "stdout_sha256": sha(case / "stdout"),
            "stderr_sha256": sha(case / "stderr"),
        }, indent=2) + "\n")
        self.assertEqual(before, after, f"source changed during {case}")
        output = result.stdout.decode("utf-8")
        self.assertIn("retained artifacts:", output)
        self.assertEqual(len(list(temporary.iterdir())), 1)
        summary = re.search(r"(\d+) failure\(s\)(?:, (\d+) decline\(s\))?\s*$", output)
        self.assertIsNotNone(summary, f"{case}: {output}")
        failures, declines = int(summary[1]), int(summary[2] or 0)
        records = [json.loads(line) for line in trace.read_text().splitlines()] if trace.exists() else []
        return result.returncode, failures, declines, output, records

    def test_positive_all_four_directions_execute(self):
        for runner, oracles, matches, compiles, programs in [
            ("regclass", 4, 12, 24, 16), ("sret", 1, 3, 6, 4),
        ]:
            with self.subTest(runner=runner):
                status, fail, decline, output, records = self.run_case(runner, "pass")
                self.assertEqual((status, fail, decline), (0, 0, 0))
                self.assertEqual(output.count("ORACLE "), oracles)
                self.assertEqual(output.count("MATCH "), matches)
                self.assertEqual(sum(r["phase"] == "compile-stand-in" for r in records), compiles)
                self.assertEqual(sum(r["phase"] == "program-stand-in" for r in records), programs)
                directions = {(r["backend"], r["callee"]) for r in records
                              if r["phase"] == "program-stand-in"}
                self.assertEqual(directions, {("llvm", "llvm"), ("llvm", "tcg"),
                                              ("tcg", "llvm"), ("tcg", "tcg")})

    def test_only_regclass_allows_normal_abi_declines(self):
        for scenario, expected_declines in [("cg_callee_decline", 4), ("cg_caller_decline", 8)]:
            for runner in RUNNERS:
                with self.subTest(runner=runner, scenario=scenario):
                    status, fail, decline, output, _ = self.run_case(runner, scenario)
                    if runner == "regclass":
                        self.assertEqual((status, fail, decline), (0, 0, expected_declines))
                        self.assertEqual(output.count("ORACLE "), 4)
                        self.assertEqual(output.count("MATCH "), 4)
                    else:
                        self.assertNotEqual(status, 0)
                        self.assertGreater(fail, 0)
                        self.assertEqual(decline, 0)

    def test_tool_errors_panic_status_and_signal_never_decline(self):
        for scenario in ["cg_unrelated", "cg_status101", "cg_signal"]:
            for runner in RUNNERS:
                with self.subTest(runner=runner, scenario=scenario):
                    status, fail, decline, output, _ = self.run_case(runner, scenario)
                    self.assertNotEqual(status, 0)
                    self.assertGreater(fail, 0)
                    self.assertEqual(decline, 0)
                    self.assertNotIn("DECLINE ", output)

    def test_missing_compiler_is_not_a_decline(self):
        for runner in RUNNERS:
            with self.subTest(runner=runner):
                status, fail, decline, output, records = self.run_case(runner, "missing", missing=True)
                self.assertNotEqual(status, 0)
                self.assertGreater(fail, 0)
                self.assertEqual(decline, 0)
                self.assertEqual(records, [])
                self.assertNotIn("ORACLE ", output)

    def test_failed_wrong_or_crashing_llvm_cannot_be_replaced(self):
        for scenario in ["llvm_callee_fail", "llvm_caller_fail", "llvm_wrong", "llvm_crash"]:
            for runner in RUNNERS:
                with self.subTest(runner=runner, scenario=scenario):
                    status, fail, decline, output, records = self.run_case(runner, scenario)
                    self.assertNotEqual(status, 0)
                    self.assertGreater(fail, 0)
                    self.assertEqual(decline, 0)
                    self.assertNotIn("ORACLE ", output)
                    self.assertNotIn("MATCH ", output)
                    # A successful CG/CG stand-in really did run: absence of a
                    # replacement oracle cannot be explained by no candidate.
                    self.assertTrue(any(r["phase"] == "program-stand-in"
                                        and r["backend"] == r["callee"] == "tcg"
                                        and r["status"] == 42 and not r["crash"] for r in records))
                    self.assertIn("has no successful LLVM oracle", output)

    def test_wrong_or_crashing_built_cells_fail(self):
        for scenario, marker in [("cg_wrong", "MISMATCH "), ("cg_crash", "abnormal execution")]:
            for runner in RUNNERS:
                with self.subTest(runner=runner, scenario=scenario):
                    status, fail, decline, output, _ = self.run_case(runner, scenario)
                    self.assertNotEqual(status, 0)
                    self.assertGreater(fail, 0)
                    self.assertEqual(decline, 0)
                    self.assertIn("ORACLE ", output)
                    self.assertIn(marker, output)

    def test_actual_supervisor_timeout_is_not_a_decline(self):
        # Use the actual supervisor at a short explicit test-only deadline. The
        # production runner's 300/30-second limits are never patched or waived.
        case = self.artifacts / "supervisor-timeout"
        case.mkdir()
        command = [sys.executable, str(SUPERVISOR), "--grace-seconds", "0.1", "0.15",
                   sys.executable, "-c", "import time; time.sleep(10)"]
        before = source_identity()
        started = time.monotonic()
        result = subprocess.run(command, cwd=ROOT, capture_output=True, timeout=5)
        elapsed = time.monotonic() - started
        (case / "stdout").write_bytes(result.stdout)
        (case / "stderr").write_bytes(result.stderr)
        (case / "result.json").write_text(json.dumps({
            "claim": "supervisor process contract only", "command": command,
            "returncode": result.returncode, "elapsed_seconds": elapsed,
            "source_before": before, "source_after": source_identity(),
        }, indent=2) + "\n")
        self.assertEqual(before, source_identity())
        self.assertEqual(result.returncode, 124)
        self.assertIn(b"command exceeded 0.15s", result.stderr)
        self.assertLess(elapsed, 5)
        classifier = ROOT / "benchmarks/regclass-xback/refusal.py"
        diagnostic = case / "abi-diagnostic.jsonl"
        diagnostic.write_text(json.dumps({"$message_type": "diagnostic", "level": "error",
                                         "message": "[TCG-ARG-ABI] controlled refusal",
                                         "children": [], "code": None}) + "\n")
        refused = subprocess.run([sys.executable, str(classifier), str(result.returncode),
                                  str(diagnostic)], capture_output=True, timeout=5)
        self.assertEqual(refused.returncode, 1)


if __name__ == "__main__":
    unittest.main()
