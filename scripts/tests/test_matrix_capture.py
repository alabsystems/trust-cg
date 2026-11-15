"""Exercise real stable/nightly libtest capture and fail-closed result accounting."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import matrix_results as matrix
import trust_toolchain


FIXTURE = Path(__file__).parent / "fixtures" / "libtest_skip_protocol.rs"


def plain_suite(name="checked", output="", *, outcome="ok", label="libtest"):
    counts = (int(outcome == "ok"), int(outcome == "FAILED"), int(outcome == "ignored"))
    return (
        f"Running {label}\nrunning 1 test\ntest {name} ... {outcome}\n"
        f"\n---- {name} stdout ----\n{output}\n"
        f"test result: {'FAILED' if counts[1] else 'ok'}. {counts[0]} passed; "
        f"{counts[1]} failed; {counts[2]} ignored; 0 measured; 0 filtered out; finished in 0.00s\n"
    )


def json_events(*events):
    return "\n".join(json.dumps(event) for event in events)


class MatrixCaptureTests(unittest.TestCase):
    def parse(self, text, *, mode="plain", rc=0, capture=True):
        return matrix.parse_log(text.splitlines(), mode=mode, rc=rc, capture_available=capture)

    def test_runtime_skip_is_not_a_pass_and_repeated_messages_do_not_add_tests(self):
        result = self.parse(plain_suite(output="SKIP: missing cc\nSKIP: missing cc\nSKIP runtime half: missing target"))
        self.assertEqual(result["status"], "skipped")
        self.assertEqual((result["passed"], result["libtest_passed"], result["runtime_skipped"]), (0, 1, 1))
        self.assertEqual(result["runtime_skip_details"][0]["test"], "checked")
        self.assertEqual(len(result["runtime_skip_details"][0]["messages"]), 2)

    def test_partial_skip_never_overrides_a_failure(self):
        result = self.parse(plain_suite(output="SKIP: optional probe", outcome="FAILED"), rc=101)
        self.assertEqual((result["status"], result["failed"], result["runtime_skipped"]), ("fail", 1, 0))
        self.assertEqual(result["runtime_skip_details"][0]["libtest_status"], "failed")

    def test_legacy_formal_campaign_opt_out_is_a_runtime_skip(self):
        output = ("checked: external-solver campaign not requested; "
                  "set TRUST_CG_RUN_FORMAL_PROOF_TESTS=1 to run")
        for mode in ("plain", "json"):
            with self.subTest(mode=mode):
                text = plain_suite(output=output) if mode == "plain" else json_events(
                    {"type": "suite", "event": "started", "test_count": 1},
                    {"type": "test", "event": "ok", "name": "checked", "stdout": output},
                    {"type": "suite", "event": "ok", "passed": 1},
                )
                result = self.parse(text, mode=mode)
                self.assertEqual(result["status"], "skipped")
                self.assertEqual((result["passed"], result["runtime_skipped"]), (0, 1))
                self.assertEqual(result["runtime_skip_details"][0]["test"], "checked")

    def test_same_test_name_in_two_binaries_has_two_distinct_identities(self):
        result = self.parse(plain_suite(label="first", output="SKIP: no host") + plain_suite(label="second", output="SKIP: no checker"))
        self.assertEqual(result["runtime_skipped"], 2)
        self.assertEqual([row["suite_index"] for row in result["runtime_skip_details"]], [0, 1])
        self.assertEqual([row["suite"] for row in result["runtime_skip_details"]], ["Running first", "Running second"])

    def test_legacy_external_certificate_opt_out_is_not_proof_credit(self):
        message = ("external certificate campaign not requested; "
                   "set TRUST_CG_RUN_EXTERNAL_CERT_TESTS=1 with explicit "
                   "AY_SOLVER_PATH and TCG_EXTERNAL_CLEAN_CHECKER paths to run")
        for prefix in ("", "SKIP: "):
            for mode in ("plain", "json"):
                with self.subTest(prefix=prefix, mode=mode):
                    output = prefix + message
                    text = plain_suite(output=output) if mode == "plain" else json_events(
                        {"type": "suite", "event": "started", "test_count": 1},
                        {"type": "test", "event": "ok", "name": "checked", "stdout": output},
                        {"type": "suite", "event": "ok", "passed": 1},
                    )
                    result = self.parse(text, mode=mode)
                    self.assertEqual(result["status"], "skipped")
                    self.assertEqual((result["passed"], result["runtime_skipped"]), (0, 1))

    def test_captured_metadata_and_timeout_diagnostics_cannot_forge_events(self):
        result = self.parse(plain_suite(output=(
            'test result: ok. 999 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;\n'
            '{"type":"suite","event":"ok","passed":999}\n'
            'Running fake binary\nrun_with_timeout: command exceeded 15s\n'
        )))
        self.assertEqual((result["status"], result["passed"], result["suites"]), ("pass", 1, 1))

    def test_json_captured_diagnostic_does_not_become_a_wrapper_timeout(self):
        text = json_events(
            {"type": "suite", "event": "started", "test_count": 1},
            {"type": "test", "event": "ok", "name": "control", "stdout": "run_with_timeout: command exceeded 15s\n"},
            {"type": "suite", "event": "ok", "passed": 1},
        )
        result = self.parse(text, mode="json")
        self.assertEqual((result["status"], result["passed"]), ("pass", 1))

    def test_absent_capture_cannot_credit_unqualified_passes(self):
        result = self.parse(plain_suite(), capture=False)
        self.assertEqual((result["passed"], result["unclassified_passes"], result["libtest_passed"]), (0, 1, 1))
        self.assertEqual(result["status"], "incomplete")
        self.assertEqual(result["runtime_skip_reporting"], "unavailable")

    def test_stable_timeout_preserves_raw_events_but_missing_stdout_is_unclassified(self):
        result = self.parse("running 2 tests\ntest completed ... ok\ntest hangs ... ", rc=124)
        self.assertEqual((result["status"], result["passed"], result["libtest_passed"], result["unclassified_passes"]), ("timeout", 0, 1, 1))
        self.assertEqual(result["incomplete_suites"], 1)
        self.assertEqual(result["runtime_skip_reporting"], "partial")

    def test_json_timeout_preserves_already_captured_named_results(self):
        text = json_events(
            {"type": "suite", "event": "started", "test_count": 3},
            {"type": "test", "event": "ok", "name": "completed", "stdout": "real execution"},
            {"type": "test", "event": "ok", "name": "skipped", "stdout": "SKIP: no checker"},
            {"type": "test", "event": "started", "name": "hangs"},
        )
        result = self.parse(text, mode="json", rc=124)
        self.assertEqual((result["status"], result["passed"], result["runtime_skipped"]), ("timeout", 1, 1))
        self.assertEqual(result["incomplete_suites"], 1)

    def test_rollups_without_named_results_and_duplicate_events_are_incomplete(self):
        for text in (
            json_events({"type": "suite", "event": "started", "test_count": 999},
                        {"type": "suite", "event": "ok", "passed": 999}),
            json_events({"type": "suite", "event": "started", "test_count": 1},
                        {"type": "test", "event": "ok", "name": "same"},
                        {"type": "test", "event": "ok", "name": "same"},
                        {"type": "suite", "event": "ok", "passed": 1}),
        ):
            with self.subTest(text=text):
                self.assertEqual(self.parse(text, mode="json")["status"], "incomplete")

    def test_malformed_json_cannot_pass(self):
        result = self.parse('{invalid\n', mode="json")
        self.assertEqual(result["status"], "incomplete")
        self.assertIn("malformed libtest JSON line", result["parse_problems"])

    def test_unattributed_skip_is_not_silently_lost(self):
        result = self.parse("SKIP: escaped subprocess output\n" + plain_suite())
        self.assertEqual(result["status"], "incomplete")
        self.assertEqual(result["unattributed_skips"], ["SKIP: escaped subprocess output"])

    def test_ignored_doc_tests_remain_distinct_and_non_green(self):
        text = plain_suite() + "Doc-tests example\nrunning 1 test\ntest src/lib.rs - item (line 1) ... ignored\ntest result: ok. 0 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out; finished in 0.00s\n"
        result = self.parse(text)
        self.assertEqual((result["passed"], result["doc_ignored"], result["test_ignored"]), (1, 1, 0))
        self.assertEqual(result["status"], "skipped")

    def test_zero_tests_are_not_an_execution_pass(self):
        result = self.parse("running 0 tests\ntest result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 17 filtered out; finished in 0.00s\n")
        self.assertEqual((result["status"], result["passed"], result["filtered"]), ("skipped", 0, 17))

    def test_compile_failure_is_incomplete_not_an_observed_test_failure(self):
        result = self.parse("error: could not compile example\n", rc=101)
        self.assertEqual((result["status"], result["passed"], result["failed"]), ("incomplete", 0, 0))

    def test_shard_cli_preserves_metadata_and_rejects_nocapture_override(self):
        with tempfile.TemporaryDirectory() as temporary:
            log = Path(temporary) / "captured.log"
            log.write_text(plain_suite())
            args = ["example", "lib", str(log), "1.5", "0", "reviewed fixture",
                    "--lib --features=one,two --features one", "",
                    "scripts/trust_cargo.sh test --lib -- --show-output", "60", "process-group", str(log), "plain"]
            with mock.patch.dict(os.environ, {"RUST_TEST_NOCAPTURE": "0"}):
                row = matrix.parse_shard(args)
            self.assertEqual(row["schema"], matrix.SHARD_SCHEMA)
            self.assertEqual(row["feature_set"], ["one", "two"])
            self.assertEqual(row["input_identifiers"]["selectors"], ["--lib"])
            self.assertEqual((row["status"], row["passed"], row["combined_log"]), ("pass", 1, str(log)))
            self.assertEqual(row["time_s"], 1.5)
            for invalid_elapsed in ("nan", "inf", "-inf", "-0.000001"):
                invalid_args = list(args)
                invalid_args[3] = invalid_elapsed
                with self.assertRaisesRegex(ValueError, "invalid shard elapsed time"):
                    matrix.parse_shard(invalid_args)
            with mock.patch.dict(os.environ, {"RUST_TEST_NOCAPTURE": "1"}):
                row = matrix.parse_shard(args)
            self.assertEqual((row["status"], row["passed"], row["unclassified_passes"]), ("incomplete", 0, 1))

    def test_real_stable_and_nightly_protocols_agree(self):
        # Both protocols come from the installed Trust compiler (the repository
        # builds with it; the stock rustc and nightly-2026-04-20 lanes are
        # retired), driven in its explicit unverified frontend lane: the plain
        # protocol and the unstable JSON one its -dev libtest also speaks.
        # The harness names the package compiler (BRIDGE_PROBE_TRUSTC); without it
        # the PATH trustc/targo pair is resolved.
        try:
            trust = trust_toolchain.resolve(os.environ.get("BRIDGE_PROBE_TRUSTC") or None)
        except trust_toolchain.ToolchainError as error:
            self.skipTest(f"the pinned Trust compiler is unavailable ({error}); cross-protocol comparison was not run")
        compiler = [trust["compiler"], *trust["compiler_flags"]]
        commands = [
            ("plain", compiler, ["--show-output"]),
            ("json", compiler, ["-Z", "unstable-options", "--format", "json", "--show-output"]),
        ]
        with tempfile.TemporaryDirectory() as temporary:
            results = []
            for mode, compiler, options in commands:
                with self.subTest(mode=mode):
                    binary = Path(temporary) / (mode + (".exe" if os.name == "nt" else ""))
                    subprocess.run(compiler + ["--test", str(FIXTURE), "-o", str(binary)], check=True, capture_output=True, text=True, timeout=60)
                    run = subprocess.run([str(binary), *options], capture_output=True, text=True, timeout=30)
                    self.assertEqual(run.returncode, 101)
                    result = self.parse(run.stdout + run.stderr, mode=mode, rc=run.returncode)
                    self.assertEqual(result["parse_problems"], [])
                    self.assertEqual((result["passed"], result["libtest_passed"], result["failed"], result["ignored"], result["runtime_skipped"]), (2, 3, 1, 1, 1))
                    self.assertEqual(result["status"], "fail")
                    results.append(result)
            self.assertEqual(results[0], results[1])


class MatrixAggregateTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.input = self.directory / "shards.jsonl"
        self.output = self.directory / "report.json"
        self.output.write_text("previous report\n")
        self.row = {
            **matrix.parse_log(plain_suite(output="SKIP: missing host").splitlines(),
                               mode="plain", rc=0, capture_available=True),
            "schema": matrix.SHARD_SCHEMA, "crate": "example", "shard": "all",
            "rc": 0, "time_s": 1.5,
        }

    def aggregate(self, rows, expected="1", bench=("targeted", "not-run", "")):
        self.input.write_text("\n".join(json.dumps(row) for row in rows) + "\n")
        return matrix.aggregate([str(self.input), str(self.output), "2026-09-09",
                                 "commit", "short", "rustc test", expected, "skip", "skipped", *bench])

    def test_current_schema_preserves_skips_and_invocation_counts(self):
        result = self.aggregate([self.row])
        self.assertEqual(result["schema"], matrix.REPORT_SCHEMA)
        self.assertEqual(result["bench_stage"], {
            "mode": "targeted", "result": "not-run", "landing_checks_rc": None, "qualifying": False,
        })
        self.assertEqual(result["totals"]["passed"], 0)
        self.assertEqual(result["totals"]["libtest_passed"], 1)
        self.assertEqual(result["totals"]["runtime_skipped"], 1)
        self.assertEqual(result["totals"]["outcome_counts"]["skipped"], 1)
        self.assertEqual(json.loads(self.output.read_text()), result)

    def test_invalid_rows_never_replace_previous_report(self):
        changes = [
            {"schema": "trust-cg.test-matrix-shard.v1"}, {"status": "pass"},
            {"passed": 1}, {"ignored": 1}, {"incomplete_suites": 2},
            {"filtered": -1}, {"time_s": float("nan")}, {"time_s": -1},
            {"rc": "0"}, {"timeout_detected": 0}, {"parse_problems": ""},
            {"runtime_skip_reporting": "legacy"},
            {"parse_problems": ["missing output"]},
        ]
        for change in changes:
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.aggregate([{**self.row, **change}])
            self.assertEqual(self.output.read_text(), "previous report\n")
        for bench in (("required", "missing-evidence", "3"), ("skipped", "green", "0")):
            with self.subTest(bench=bench), self.assertRaises(ValueError):
                self.aggregate([self.row], bench=bench)
            self.assertEqual(self.output.read_text(), "previous report\n")

    def test_missing_and_duplicate_shards_are_rejected(self):
        for rows, expected in (([], "0"), ([self.row], "2"), ([self.row, self.row], "2")):
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                self.aggregate(rows, expected)
            self.assertEqual(self.output.read_text(), "previous report\n")

    def test_failed_atomic_replace_preserves_destination_and_cleans_owned_temporary(self):
        with mock.patch.object(matrix.os, "replace", side_effect=OSError("write interrupted")):
            with self.assertRaises(OSError):
                self.aggregate([self.row])
        self.assertEqual(self.output.read_text(), "previous report\n")
        self.assertEqual(sorted(path.name for path in self.directory.iterdir()), ["report.json", "shards.jsonl"])


if __name__ == "__main__":
    unittest.main()
