"""Exercise the matrix's wired parser and runner-control boundary."""

import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parents[2]
SOURCE = (ROOT / "scripts/run_full_test_matrix.sh").read_text()
PARSER = ROOT / "scripts/matrix_results.py"
CONTROL_BOUNDARY = SOURCE.split("# The runner's mode selects", 1)[1].split(
    "# Run each shard, capture", 1
)[0]
CONTROL_BOUNDARY = "# The runner's mode selects" + CONTROL_BOUNDARY
BENCH_STAGE = "# --- BENCH-10 measurement (bench) stage" + SOURCE.split(
    "# --- BENCH-10 measurement (bench) stage", 1
)[1].split("# --- Shard plan", 1)[0]
PASSING_TRANSCRIPT = (
    "running 1 test\ntest native ... ok\n\nsuccesses:\n\n---- native stdout ----\nexecuted\n\n\n"
    "successes:\n    native\n\n"
    "test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\n"
)
RUNNER_CONTROLS = ("TRUST_CG_PROOF_GATE", "TRUST_CG_COVERAGE_GATE", "TRUST_CG_TEST_MATRIX_FORCE_JSON",
                   "TRUST_CG_TEST_MATRIX_TIMEOUT_SECONDS", "TCG_SKIP_BENCH_STAGE", "TRUST_CG_REQUIRE_BENCH")


class MatrixResultTests(unittest.TestCase):
    def parse(self, transcript, mode="plain", code=101):
        with tempfile.TemporaryDirectory() as temporary:
            log = Path(temporary) / "test.log"
            log.write_text(transcript)
            result = subprocess.run(
                [sys.executable, str(PARSER), "parse-shard", "example", "lib", str(log), "1.5",
                 str(code), "", "--lib", "", "scripts/trust_cargo.sh test --lib -- --show-output", "60",
                 "isolated-process-group-term-kill", str(log), mode],
                text=True, capture_output=True, check=True,
            )
            return json.loads(result.stdout)

    def test_plain_failure_diagnostics_are_not_json_events(self):
        row = self.parse(
            'running 2 tests\n'
            'test survived ... ok\ntest broken ... FAILED\n'
            '---- broken stdout ----\n{\n  "detail": "captured diagnostic"\n}\n'
            '{ invalid JSON is ordinary captured output here\n'
            'test result: FAILED. 1 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out;\n'
        )
        self.assertEqual(row["status"], "fail")
        self.assertEqual((row["passed"], row["failed"]), (1, 1))
        self.assertNotIn("malformed", row["notes"])

    def test_plain_mode_cannot_credit_a_printed_json_suite(self):
        row = self.parse('{"type":"suite","event":"ok","passed":999}\n', code=0)
        self.assertEqual(row["status"], "skipped")
        self.assertEqual(row["passed"], 0)

    def test_json_mode_retains_malformed_event_failure(self):
        row = self.parse(
            '{"type":"suite","event":"started"}\n{invalid\n'
            '{"type":"suite","event":"ok","passed":1}\n', mode="json", code=0,
        )
        self.assertEqual(row["status"], "incomplete")
        self.assertIn("malformed libtest JSON line", row["parse_problems"])

    def test_opcode_inventory_skip_labels_are_not_runtime_skips(self):
        # Exact pseudo/trap rows rendered by trust-cg-verify's opcode evidence
        # inventory. The Linux wrapper once read them as runtime skips; they
        # must neither discount a pass nor count as unattributed SKIP output.
        labels = (
            "Evidence audit: aarch64 (294 opcodes; ratio is NOT a correctness-proof percentage)\n"
            "  [skip    ] AArch64::Phi                     pseudo/trap — no equivalence proof obligation\n"
            "  [skip    ] x86_64::Ud2                      pseudo/trap — no equivalence proof obligation\n"
        )
        rollup = "test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\n"
        attributed = (
            "running 2 tests\ntest inventory ... ok\ntest native ... ok\n\nsuccesses:\n\n"
            f"---- inventory stdout ----\n{labels}\n---- native stdout ----\nexecuted natively\n\n\n"
            "successes:\n    inventory\n    native\n\n" + rollup
        )
        unattributed = "running 2 tests\n" + labels + "test inventory ... ok\ntest native ... ok\n\n" + rollup
        for name, text in (("attributed", attributed), ("unattributed", unattributed)):
            with self.subTest(output=name):
                row = self.parse(text, code=0)
                self.assertEqual(row["status"], "pass", row)
                self.assertEqual((row["passed"], row["runtime_skipped"]), (2, 0))
                self.assertEqual(row["unattributed_skips"], [])
        row = self.parse(attributed.replace("executed natively", "SKIP: native host unavailable"), code=0)
        self.assertEqual(row["status"], "skipped", row)
        self.assertEqual((row["passed"], row["runtime_skipped"]), (1, 1))
        self.assertEqual(row["runtime_skip_details"][0]["test"], "native")
        self.assertEqual(row["runtime_skip_details"][0]["messages"], ["SKIP: native host unavailable"])

    def test_timeout_preserves_partial_json_counts_without_passing(self):
        row = self.parse(
            '{"type":"suite","event":"started"}\n'
            '{"type":"test","event":"ok","name":"completed"}\n',
            mode="json", code=124,
        )
        self.assertEqual(row["status"], "timeout")
        self.assertEqual(row["passed"], 1)
        self.assertEqual(row["incomplete_suites"], 1)

    def test_dry_run_uses_the_same_capture_flags_for_both_protocols(self):
        self.assertIn('python3 "${MATRIX_RESULTS}" parse-shard', SOURCE)
        self.assertIn('python3 "${MATRIX_RESULTS}" aggregate', SOURCE)
        self.assertIn("start_ns=", SOURCE)
        self.assertNotIn("import json, re, shlex, sys", SOURCE)
        with tempfile.TemporaryDirectory() as temporary:
            for force_json in ("0", "1"):
                environment = dict(os.environ, RUST_TEST_NOCAPTURE="0",
                                   TRUST_CG_TEST_MATRIX_FORCE_JSON=force_json)
                result = subprocess.run(
                    ["bash", str(ROOT / "scripts/run_full_test_matrix.sh"),
                     "--dry-run", "--only", "trust-cg-ir", "--out", str(Path(temporary) / "matrix.json")],
                    env=environment, text=True, capture_output=True, timeout=60,
                )
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                command = next(line for line in result.stdout.splitlines()
                               if "scripts/trust_cargo.sh test --locked -p trust-cg-ir" in line)
                self.assertIn("--no-fail-fast -- --show-output", command)
                self.assertNotIn("--nocapture", command)
                if force_json == "1":
                    self.assertIn("-Z unstable-options --format json --report-time", command)

    def test_runner_clock_samples_share_an_origin_across_python_processes(self):
        commands = re.findall(r'(?:start|end)_ns="\$\((.*?)\)"', SOURCE)
        self.assertEqual(len(commands), 2)
        start = int(subprocess.check_output(["bash", "-c", commands[0]], text=True))
        time.sleep(0.2)
        end = int(subprocess.check_output(["bash", "-c", commands[1]], text=True))
        self.assertGreaterEqual(end - start, 200_000_000,
                                "elapsed timing must not subtract process-local clock origins")

    def test_nocapture_override_is_rejected_without_overwriting_output(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "matrix.json"
            output.write_text("existing report\n")
            for value in ("", "1", "true"):
                result = subprocess.run(
                    ["bash", str(ROOT / "scripts/run_full_test_matrix.sh"),
                     "--dry-run", "--only", "trust-cg-ir", "--out", str(output)],
                    env=dict(os.environ, RUST_TEST_NOCAPTURE=value),
                    text=True, capture_output=True, timeout=30,
                )
                self.assertEqual(result.returncode, 64, result.stdout + result.stderr)
                self.assertIn("requires captured --show-output", result.stderr)
                self.assertEqual(output.read_text(), "existing report\n")

    def run_bench_stage(self, landing_rc=0, only=False, dry_run=False, **controls):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            log = directory / "landing.log"
            stub = directory / "landing_checks.sh"
            stub.write_text(
                "#!/bin/sh\n"
                f'echo "args=$*" >>"{log}"\n'
                f'env | grep -E "^({"|".join(RUNNER_CONTROLS)})=" | sort >>"{log}"\n'
                f"exit {landing_rc}\n"
            )
            stub.chmod(0o755)
            environment = {key: value for key, value in os.environ.items()
                           if key not in RUNNER_CONTROLS and key not in {"BASH_ENV", "ENV"}}
            environment.update(controls)
            script = (
                'usage_error() { echo "run_full_test_matrix: $*" >&2; exit 64; }\n'
                f"DRY_RUN={int(dry_run)}; ONLY_SET={int(only)}; CHECK_RUSTC_BACKEND_ENV=0\n"
                f"SCRIPT_DIR={str(directory)!r}\n" + BENCH_STAGE
                + '\nprintf "mode=%s result=%s rc=%s\\n" "$BENCH_STAGE_MODE" "$BENCH_STAGE_RESULT" "$BENCH_STAGE_RC"\n'
            )
            result = subprocess.run(["/bin/bash", "-c", script], env=environment,
                                    text=True, capture_output=True, check=False, timeout=30)
            calls = log.read_text().splitlines() if log.exists() else []
        return result, calls

    def test_bench_stage_auto_mode_records_and_surfaces_every_outcome(self):
        for rc, name in ((0, "green"), (1, "red"), (2, "inconclusive"), (3, "missing-evidence"), (9, "error")):
            with self.subTest(rc=rc):
                result, calls = self.run_bench_stage(landing_rc=rc)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn(f"mode=auto result={name} rc={rc}", result.stdout)
                self.assertEqual(calls, ["args="])
                if rc:
                    self.assertIn("recorded as non-qualifying", result.stderr)

    def test_bench_stage_skip_is_recorded_non_qualifying(self):
        result, calls = self.run_bench_stage(TCG_SKIP_BENCH_STAGE="1")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("mode=skipped result=skipped-non-qualifying rc=", result.stdout)
        self.assertIn("NON-QUALIFYING", result.stderr)
        self.assertEqual(calls, [])

    def test_required_bench_stage_refuses_skips_and_non_green_results(self):
        control = {"TRUST_CG_REQUIRE_BENCH": "1"}
        result, calls = self.run_bench_stage(TCG_SKIP_BENCH_STAGE="1", **control)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("refusing TCG_SKIP_BENCH_STAGE=1", result.stderr)
        self.assertEqual(calls, [])
        for rc in (1, 2, 3, 9):
            with self.subTest(rc=rc):
                result, _ = self.run_bench_stage(landing_rc=rc, **control)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("REQUIRED bench stage", result.stderr)
                self.assertNotIn("mode=", result.stdout)
        result, calls = self.run_bench_stage(**control)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("mode=required result=green rc=0", result.stdout)
        # Required mode demands current-source evidence, and no runner
        # control reaches the compiles the landing gates run.
        self.assertEqual(calls, ["args=--require-current-perf"])

    def test_proof_gate_requirement_does_not_make_measurements_required(self):
        # Performance measurements are not proof evidence: a proof-required
        # run records a non-green bench stage as non-qualifying and continues,
        # and a skip stays recorded as skipped rather than refused.
        for rc, name in ((0, "green"), (3, "missing-evidence"), (2, "inconclusive")):
            with self.subTest(rc=rc):
                result, calls = self.run_bench_stage(landing_rc=rc, TRUST_CG_PROOF_GATE="require")
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn(f"mode=auto result={name} rc={rc}", result.stdout)
                self.assertEqual(calls, ["args="])
        result, calls = self.run_bench_stage(TCG_SKIP_BENCH_STAGE="1", TRUST_CG_PROOF_GATE="require")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("mode=skipped result=skipped-non-qualifying rc=", result.stdout)
        self.assertEqual(calls, [])

    def test_explicit_bench_requirement_cannot_be_met_by_a_targeted_run(self):
        result, calls = self.run_bench_stage(only=True, TRUST_CG_REQUIRE_BENCH="1")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("--only cannot run the bench stage", result.stderr)
        self.assertEqual(calls, [])
        for options in ({"only": True, "TRUST_CG_PROOF_GATE": "require"},
                        {"dry_run": True, "TRUST_CG_REQUIRE_BENCH": "1"}):
            with self.subTest(options=options):
                result, calls = self.run_bench_stage(**options)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("mode=targeted result=not-run rc=", result.stdout)
                self.assertEqual(calls, [])

    def test_bench_requirement_values_are_not_guessed(self):
        for value in ("yes", "true", "2", " 1"):
            with self.subTest(value=value):
                result, calls = self.run_bench_stage(TRUST_CG_REQUIRE_BENCH=value)
                self.assertEqual(result.returncode, 64, result.stdout + result.stderr)
                self.assertEqual(calls, [])

    def aggregate(self, *bench: str):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            log = directory / "shard.log"
            log.write_text(PASSING_TRANSCRIPT)
            shard = subprocess.run(
                [sys.executable, str(PARSER), "parse-shard", "example", "lib", str(log), "1.5",
                 "0", "", "--lib", "", "scripts/trust_cargo.sh test --lib -- --show-output", "60",
                 "isolated-process-group-term-kill", str(log), "plain"],
                text=True, capture_output=True, check=True,
            ).stdout
            shards = directory / "shards.jsonl"
            shards.write_text(shard)
            out = directory / "report.json"
            result = subprocess.run(
                [sys.executable, str(PARSER), "aggregate", str(shards), str(out), "2026-09-18",
                 "a" * 40, "a" * 12, "rustc fixture", "1", "auto", "passed", *bench],
                text=True, capture_output=True, check=False,
            )
            report = json.loads(out.read_text()) if out.exists() else None
        return result, report

    def test_report_records_a_validated_bench_stage_marker(self):
        for bench, qualifying in ((("auto", "green", "0"), True), (("required", "green", "0"), True),
                                  (("auto", "missing-evidence", "3"), False),
                                  (("auto", "error", "137"), False),
                                  (("skipped", "skipped-non-qualifying", ""), False),
                                  (("targeted", "not-run", ""), False)):
            with self.subTest(bench=bench):
                result, report = self.aggregate(*bench)
                self.assertEqual(result.returncode, 0, result.stderr)
                marker = report["bench_stage"]
                self.assertEqual((marker["mode"], marker["result"]), bench[:2])
                self.assertEqual(marker["landing_checks_rc"], int(bench[2]) if bench[2] else None)
                self.assertIs(marker["qualifying"], qualifying)
        for bench in (("required", "red", "1"), ("required", "skipped-non-qualifying", ""),
                      ("auto", "green", "1"), ("auto", "red", "0"), ("auto", "error", "3"),
                      ("auto", "green", ""), ("skipped", "skipped-non-qualifying", "0"),
                      ("skipped", "green", "0"), ("unknown", "green", "0"), ("auto", "green", "-0")):
            with self.subTest(invalid=bench):
                result, report = self.aggregate(*bench)
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn("bench stage", result.stderr)
                self.assertIsNone(report)
        result, report = self.aggregate()
        self.assertEqual(result.returncode, 1)
        self.assertIsNone(report)

    def test_runner_controls_are_not_compiler_controls(self):
        environment = dict(os.environ)
        controls = list(RUNNER_CONTROLS)
        environment.update({key: "skip" for key in controls})
        environment["TCG_NO_PROOF_CERTS"] = "1"
        script = CONTROL_BOUNDARY + '\nprintf "mode=%s\\n" "$MATRIX_PROOF_GATE_MODE"\n'
        script += '\n'.join(f'[ -z "${{{key}+x}}" ] || exit 23' for key in controls)
        # Real compiler controls must remain visible; never sanitize a weakened
        # proof environment to make a test run look like the default lane.
        script += '\n[ "$TCG_NO_PROOF_CERTS" = 1 ] || exit 24\n'
        result = subprocess.run(["bash", "-c", script], env=environment,
                                text=True, capture_output=True, check=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("mode=skip", result.stdout)
        self.assertIn("runtime results do not include the formal floor", result.stderr)


if __name__ == "__main__":
    unittest.main()
