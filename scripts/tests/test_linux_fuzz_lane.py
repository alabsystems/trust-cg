from __future__ import annotations

import argparse
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "run_linux_fuzz_lane.py"
SPEC = importlib.util.spec_from_file_location("run_linux_fuzz_lane", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
LANE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(LANE)


# The shape of a libFuzzer transcript that ran its whole -max_total_time budget
# with -print_final_stats=1 (lines as libFuzzer prints them).
CLEAN_RUN = (
    "INFO: Running with entropic power schedule (0xFF, 100).\n"
    "INFO: Seed: 20260924\n"
    "INFO: Loaded 1 modules   (91234 inline 8-bit counters): 91234 [0xaaaa, 0xbbbb),\n"
    "INFO:        0 files found in /out/libfuzzer/fuzz_encode_instruction/corpus\n"
    "#2\tINITED cov: 212 ft: 213 corp: 1/1b exec/s: 0 rss: 61Mb\n"
    "#3\tNEW    cov: 230 ft: 240 corp: 2/3b lim: 4 exec/s: 0 rss: 62Mb L: 2/2 MS: 1 InsertByte-\n"
    "#262144\tpulse  cov: 1805 ft: 7310 corp: 812/31Kb lim: 4096 exec/s: 43690 rss: 410Mb\n"
    "#9876543\tDONE   cov: 1820 ft: 7402 corp: 830/32Kb lim: 4096 exec/s: 16433 rss: 433Mb\n"
    "Done 9876543 runs in 601 second(s)\n"
    "stat::number_of_executed_units: 9876543\n"
    "stat::average_exec_per_sec:     16433\n"
    "stat::new_units_added:          2211\n"
    "stat::slowest_unit_time_sec:    0\n"
    "stat::peak_rss_mb:              433\n"
)

CRASH_RUN = (
    "INFO: Seed: 20260924\n"
    "#2\tINITED cov: 212 ft: 213 corp: 1/36b exec/s: 0 rss: 61Mb\n"
    "thread '<unnamed>' panicked at fuzz_targets/fuzz_encode_instruction.rs:151:9:\n"
    "planted fuzz-lane negative control\n"
    "==1234== ERROR: libFuzzer: deadly signal\n"
    "MS: 0 ; base unit: 0000000000000000000000000000000000000000\n"
    "artifact_prefix='/out/artifacts/'; Test unit written to /out/artifacts/crash-3e8a\n"
    "stat::number_of_executed_units: 2\n"
    "stat::average_exec_per_sec:     0\n"
    "stat::new_units_added:          0\n"
    "stat::slowest_unit_time_sec:    0\n"
    "stat::peak_rss_mb:              61\n"
)


LEAK_RUN = (
    "INFO: Seed: 20260924\n"
    "#2\tINITED cov: 212 ft: 213 corp: 1/33b exec/s: 0 rss: 61Mb\n"
    "==1234==ERROR: LeakSanitizer: detected memory leaks\n"
    "Direct leak of 4096 byte(s) in 1 object(s) allocated from:\n"
    "INFO: a leak has been found in the initial corpus.\n"
    "artifact_prefix='/out/artifacts/'; Test unit written to /out/artifacts/leak-7f00\n"
    "stat::number_of_executed_units: 2\n"
)

ASAN_RUN = (
    "INFO: Seed: 20260924\n"
    "==1234==ERROR: AddressSanitizer: heap-buffer-overflow on address 0xf000 at pc 0x1 bp 0x2 sp 0x3\n"
    "READ of size 1 at 0xf000 thread T0\n"
    "artifact_prefix='/out/artifacts/'; Test unit written to /out/artifacts/crash-a5a5\n"
    "stat::number_of_executed_units: 1\n"
)


def runlog(**overrides) -> dict:
    log = {
        "driver": "trust-ir-jit-diff", "status": "ok", "reason": None, "duration_secs": 7200,
        "runs": 50, "timeouts": 0, "crashes": 0, "miscompiles": 0, "repros": [],
        "started_at": "2026-09-24T20:00:00Z", "finished_at": "2026-09-24T20:05:00Z",
        "seed_start": 1, "requested_runs": 50,
        # 50 seeds x 6 scalar rows + 50 seeds x 6 control-shape rows + 6
        # consumer-shape seeds x 4 rows; every control and consumer row has an
        # oracle value.
        "rows_checked": 624, "rows_executed": 624, "rows_refused": 0,
        "rows_oracle_compared": 550, "rows_cross_level_only": 74, "scalar_rows_per_seed": 6,
        "seeds_incomplete": 0, "oracle_error_samples": ["interp_err: division by zero"],
    }
    log.update(overrides)
    return log


class LibFuzzerClassificationTests(unittest.TestCase):
    def test_complete_clean_run_passes_with_parsed_figures(self):
        verdict = LANE.classify_libfuzzer(0, CLEAN_RUN, [])
        self.assertEqual(verdict["status"], "pass", verdict)
        self.assertEqual(verdict["executions"], 9876543)
        self.assertEqual(verdict["done_runs"], 9876543)
        self.assertEqual(verdict["done_seconds"], 601)
        self.assertEqual(verdict["exec_per_second"], 16433)
        self.assertEqual(verdict["new_units"], 2211)
        self.assertEqual(verdict["peak_rss_mb"], 433)
        self.assertEqual((verdict["coverage"], verdict["features"]), (1820, 7402))
        self.assertEqual(verdict["corpus_units"], 830)
        self.assertEqual(verdict["corpus_bytes"], 32 * 1024)
        self.assertEqual(verdict["last_status_event"], "DONE")

    def test_corpus_sizes_in_bytes_and_megabytes(self):
        self.assertEqual(LANE.parse_libfuzzer("#9\tNEW    cov: 1 ft: 2 corp: 3/90b lim: 4\n")["corpus_bytes"], 90)
        self.assertEqual(LANE.parse_libfuzzer("#9\tpulse  cov: 1 ft: 2 corp: 3/2Mb lim: 4\n")["corpus_bytes"], 2 << 20)

    def test_crash_report_and_artifact_fail_even_with_a_zero_exit(self):
        verdict = LANE.classify_libfuzzer(0, CRASH_RUN, ["crash-3e8a"])
        self.assertEqual(verdict["status"], "fail")
        self.assertIn("crash", verdict["failure_kinds"])
        self.assertEqual(verdict["failure_artifacts"], ["crash-3e8a"])
        self.assertTrue(any("no 'Done N runs" in error for error in verdict["errors"]), verdict)

    def test_a_failure_artifact_alone_fails_a_green_transcript(self):
        for name, kind in (("crash-ab12", "crash"), ("timeout-ab12", "timeout"), ("oom-ab12", "oom"), ("leak-ab12", "leak")):
            with self.subTest(name=name):
                verdict = LANE.classify_libfuzzer(0, CLEAN_RUN, [name])
                self.assertEqual(verdict["status"], "fail")
                self.assertIn(kind, verdict["failure_kinds"])

    def test_every_failure_report_fails(self):
        for line, kind in (
            ("==7== ERROR: libFuzzer: timeout after 25 seconds", "timeout"),
            ("==7== ERROR: libFuzzer: out-of-memory (used: 4097Mb; exceeds: 4096Mb)", "oom"),
            ("==7== ERROR: libFuzzer: malloc(123) exceeds limit", "oom"),
            ("==7==ERROR: LeakSanitizer: detected memory leaks", "leak"),
            ("==7==ERROR: AddressSanitizer: heap-buffer-overflow on address", "crash"),
            ("==7== ERROR: libFuzzer: fuzz target exited", "exit"),
            ("thread '<unnamed>' panicked at src/lib.rs:1:1:", "crash"),
        ):
            with self.subTest(kind=kind, line=line):
                verdict = LANE.classify_libfuzzer(0, CLEAN_RUN + line + "\n", [])
                self.assertEqual(verdict["status"], "fail")
                self.assertIn(kind, verdict["failure_kinds"])

    def test_nonzero_exit_incomplete_run_and_unknown_artifacts_fail(self):
        self.assertEqual(LANE.classify_libfuzzer(1, CLEAN_RUN, [])["status"], "fail")
        self.assertEqual(LANE.classify_libfuzzer(0, CLEAN_RUN.split("Done ")[0], [])["status"], "fail")
        self.assertEqual(LANE.classify_libfuzzer(0, "", [])["status"], "fail")
        no_units = CLEAN_RUN.replace("number_of_executed_units: 9876543", "number_of_executed_units: 0")
        self.assertEqual(LANE.classify_libfuzzer(0, no_units, [])["status"], "fail")
        verdict = LANE.classify_libfuzzer(0, CLEAN_RUN, ["mystery"])
        self.assertEqual(verdict["status"], "fail")
        self.assertTrue(any("unrecognized artifacts" in error for error in verdict["errors"]))

    def test_a_slow_unit_fails_a_green_transcript(self):
        verdict = LANE.classify_libfuzzer(0, CLEAN_RUN, ["slow-unit-ab12"])
        self.assertEqual(verdict["status"], "fail", verdict)
        self.assertIn("slow", verdict["failure_kinds"])
        self.assertEqual(verdict["slow_unit_artifacts"], ["slow-unit-ab12"])

    def test_a_run_that_stopped_before_its_budget_fails(self):
        self.assertEqual(LANE.classify_libfuzzer(0, CLEAN_RUN, [], budget_seconds=600)["status"], "pass")
        # One second of rounding is tolerated; less than the budget is not.
        self.assertEqual(LANE.classify_libfuzzer(0, CLEAN_RUN, [], budget_seconds=602)["status"], "pass")
        short = CLEAN_RUN.replace("Done 9876543 runs in 601 second(s)", "Done 2 runs in 0 second(s)")
        verdict = LANE.classify_libfuzzer(0, short, [], budget_seconds=600)
        self.assertEqual(verdict["status"], "fail")
        self.assertIn("ran 0 s of its 600 s budget", verdict["errors"])
        self.assertEqual(LANE.classify_libfuzzer(0, CLEAN_RUN, [], budget_seconds=603)["status"], "fail")

    def test_campaign_command_pins_seed_budget_and_limits(self):
        args = argparse.Namespace(
            libfuzzer_seed=7, libfuzzer_timeout_seconds=25, libfuzzer_slow_unit_seconds=10,
            libfuzzer_rss_limit_mb=4096,
        )
        command = LANE.libfuzzer_command(Path("/bin/target"), Path("/work"), args, 600)
        self.assertEqual(command[0], "/bin/target")
        for flag in ("-seed=7", "-max_total_time=600", "-timeout=25", "-report_slow_units=10",
                     "-rss_limit_mb=4096", "-detect_leaks=1", "-print_final_stats=1",
                     "-artifact_prefix=/work/artifacts/"):
            self.assertIn(flag, command)
        self.assertEqual(command[-1], "/work/corpus")


class JitDiffClassificationTests(unittest.TestCase):
    def test_complete_seed_range_without_defects_passes(self):
        verdict = LANE.classify_jit_diff(0, runlog(), 1, 50)
        self.assertEqual(verdict["status"], "pass", verdict)
        self.assertFalse(verdict["planted_detected"])

    def test_short_range_defects_and_malformed_logs_fail(self):
        for label, log, code in (
            ("expired before the range", runlog(runs=49), 0),
            ("miscompile", runlog(miscompiles=1, repros=[{"seed": 7, "summary": "miscompile seed=7"}]), 0),
            ("crash", runlog(crashes=1), 0),
            ("timeout", runlog(timeouts=1), 0),
            ("repro without a count", runlog(repros=[{"seed": 3, "summary": "x"}]), 0),
            ("unavailable", runlog(status="unavailable", reason="JIT only supported on aarch64/x86_64 hosts"), 0),
            ("other driver", runlog(driver="trust-ir-gen"), 0),
            ("other seed range", runlog(seed_start=2), 0),
            ("no requested range", runlog(requested_runs=None), 0),
            ("nonzero exit", runlog(), 1),
            ("malformed counts", runlog(crashes="0"), 0),
            ("a refused JIT level", runlog(rows_executed=623, rows_refused=1, refusal_samples=["compile_jit_err: x"]), 0),
            ("a row neither executed nor refused", runlog(rows_executed=623), 0),
            ("fewer rows than seeds x rows per seed",
             runlog(rows_checked=599, rows_executed=599, rows_oracle_compared=525), 0),
            ("a seed that checked fewer rows", runlog(seeds_incomplete=1, incomplete_seed_samples=[17]), 0),
            ("no rows per seed", runlog(scalar_rows_per_seed=0), 0),
            ("interpreter and cross-level rows that do not add up", runlog(rows_cross_level_only=73), 0),
            ("no row compared against the interpreter",
             runlog(rows_oracle_compared=0, rows_cross_level_only=624), 0),
            ("no row counts", runlog(rows_checked=None), 0),
            ("no per-seed count", runlog(seeds_incomplete=None), 0),
        ):
            with self.subTest(label=label):
                self.assertEqual(LANE.classify_jit_diff(code, log, 1, 50)["status"], "fail")
        self.assertEqual(LANE.classify_jit_diff(0, None, 1, 50)["status"], "fail")

    def test_interpreter_compared_and_cross_level_rows_are_reported_apart(self):
        verdict = LANE.classify_jit_diff(0, runlog(), 1, 50)
        self.assertEqual((verdict["rows_oracle_compared"], verdict["rows_cross_level_only"]), (550, 74))
        self.assertEqual(verdict["oracle_error_samples"], ["interp_err: division by zero"])
        self.assertEqual(verdict["seeds_incomplete"], 0)

    def test_the_lane_derives_every_seeds_rows_itself(self):
        self.assertEqual(LANE.jit_expected_rows(1, 10000), (60000, 5000, 60000))
        self.assertEqual(LANE.jit_expected_rows(1, 50), (300, 24, 300))
        self.assertEqual(LANE.jit_expected_rows(0, 8), (48, 4, 48))
        self.assertEqual(LANE.jit_expected_rows(9, 7), (42, 0, 42))
        for label, overrides in (
            ("one row per seed", {"scalar_rows_per_seed": 1, "rows_checked": 124, "rows_executed": 124,
                                  "rows_oracle_compared": 110, "rows_cross_level_only": 14}),
            ("five rows per seed", {"scalar_rows_per_seed": 5, "rows_checked": 524, "rows_executed": 524,
                                    "rows_oracle_compared": 450, "rows_cross_level_only": 74}),
            ("five rows per seed claimed as six", {"rows_checked": 524, "rows_executed": 524,
                                                   "rows_oracle_compared": 450, "rows_cross_level_only": 74}),
            ("a missing consumer row", {"rows_checked": 623, "rows_executed": 623, "rows_cross_level_only": 73}),
            ("one interpreter-compared row", {"rows_oracle_compared": 325, "rows_cross_level_only": 299}),
            ("under half interpreter-compared", {"rows_oracle_compared": 473, "rows_cross_level_only": 151}),
        ):
            with self.subTest(label=label):
                verdict = LANE.classify_jit_diff(0, runlog(**overrides), 1, 50)
                self.assertEqual(verdict["status"], "fail", verdict)
        verdict = LANE.classify_jit_diff(0, runlog(rows_oracle_compared=474, rows_cross_level_only=150), 1, 50)
        self.assertEqual(verdict["status"], "pass", verdict)
        self.assertEqual(verdict["interpreter_compared_scalar_rows"], 150)

    def test_row_policy_matches_the_driver(self):
        driver = (ROOT / "crates" / "trust-cg-fuzz" / "src" / "bin" / f"{LANE.JIT_DRIVER}.rs").read_text()
        self.assertIn(f"const SCALAR_ROWS_PER_SEED: u32 = {LANE.JIT_SCALAR_ROWS_PER_SEED};", driver)
        self.assertIn(f"if seed % {LANE.JIT_CONSUMER_EVERY} == 0 {{", driver)
        self.assertIn(f"let consumer_rows: [[i64; 4]; {LANE.JIT_CONSUMER_ROWS}] =", driver)
        # Every seed's control-shape module runs on the scalar rows.
        self.assertEqual(LANE.JIT_CONTROL_ROWS_PER_SEED, LANE.JIT_SCALAR_ROWS_PER_SEED)
        self.assertIn("gen_control_module(seed)", driver)

    def test_a_planted_log_never_passes_as_the_campaign(self):
        verdict = LANE.classify_jit_diff(0, runlog(planted_miscompile_seed=1), 1, 50)
        self.assertEqual(verdict["status"], "fail")

    def test_planted_run_detects_only_the_tagged_planted_seed(self):
        planted = runlog(
            planted_miscompile_seed=1, miscompiles=1,
            repros=[{"seed": 1, "summary": f"miscompile seed=1 {LANE.JIT_CONTROL_TAG} interp=3 O2_jit=4"}],
        )
        verdict = LANE.classify_jit_diff(0, planted, 1, 50, planted_seed=1)
        self.assertEqual(verdict["status"], "fail")
        self.assertTrue(verdict["planted_detected"])
        self.assertEqual(verdict["genuine_repros"], [])
        untagged = runlog(planted_miscompile_seed=1, miscompiles=1, repros=[{"seed": 1, "summary": "miscompile seed=1"}])
        self.assertFalse(LANE.classify_jit_diff(0, untagged, 1, 50, planted_seed=1)["planted_detected"])
        missed = runlog(planted_miscompile_seed=1)
        self.assertFalse(LANE.classify_jit_diff(0, missed, 1, 50, planted_seed=1)["planted_detected"])


class NegativeControlTests(unittest.TestCase):
    def test_libfuzzer_control_requires_a_crash_with_the_planted_input(self):
        detector = LANE.classify_libfuzzer(1, CRASH_RUN, ["crash-3e8a"])
        marker = {"crash-3e8a": LANE.LIBFUZZER_CONTROL_MARKER + b"\x00"}
        self.assertEqual(LANE.classify_negative_control("libfuzzer", detector, CRASH_RUN, marker)["status"], "pass")
        other = {"crash-3e8a": b"some other input"}
        self.assertEqual(LANE.classify_negative_control("libfuzzer", detector, CRASH_RUN, other)["status"], "fail")
        missing_panic = CRASH_RUN.replace(LANE.LIBFUZZER_CONTROL_PANIC, "an unrelated panic")
        missing = LANE.classify_libfuzzer(1, missing_panic, ["crash-3e8a"])
        self.assertEqual(LANE.classify_negative_control("libfuzzer", missing, missing_panic, marker)["status"], "fail")
        # A detector that passed the planted run means the lane cannot see failures.
        clean = LANE.classify_libfuzzer(0, CLEAN_RUN, [])
        self.assertEqual(LANE.classify_negative_control("libfuzzer", clean, CLEAN_RUN, {})["status"], "fail")

    def test_leak_control_requires_a_leak_report_and_the_planted_input(self):
        detector = LANE.classify_libfuzzer(1, LEAK_RUN, ["leak-7f00"], budget_seconds=60)
        self.assertIn("leak", detector["failure_kinds"])
        planted = {"leak-7f00": LANE.LIBFUZZER_LEAK_MARKER + b"\x00"}
        self.assertEqual(LANE.classify_negative_control("libfuzzer-leak", detector, LEAK_RUN, planted)["status"], "pass")
        # An ambient detect_leaks=0 runs the planted input clean for the whole
        # budget: the detector passes it, and the control must fail the lane.
        clean = LANE.classify_libfuzzer(0, CLEAN_RUN, [], budget_seconds=600)
        self.assertEqual(clean["status"], "pass")
        self.assertEqual(LANE.classify_negative_control("libfuzzer-leak", clean, CLEAN_RUN, {})["status"], "fail")
        # A crash of the planted input is not a leak report.
        crash = LANE.classify_libfuzzer(1, CRASH_RUN, ["crash-3e8a"])
        crashed = {"crash-3e8a": LANE.LIBFUZZER_LEAK_MARKER}
        self.assertEqual(LANE.classify_negative_control("libfuzzer-leak", crash, CRASH_RUN, crashed)["status"], "fail")
        other = {"leak-7f00": LANE.LIBFUZZER_CONTROL_MARKER}
        self.assertEqual(LANE.classify_negative_control("libfuzzer-leak", detector, LEAK_RUN, other)["status"], "fail")

    def test_asan_control_requires_a_heap_overflow_report_and_the_planted_input(self):
        detector = LANE.classify_libfuzzer(1, ASAN_RUN, ["crash-a5a5"], budget_seconds=60)
        planted = {"crash-a5a5": LANE.LIBFUZZER_ASAN_MARKER + b"\x00"}
        self.assertEqual(LANE.classify_negative_control("libfuzzer-asan", detector, ASAN_RUN, planted)["status"], "pass")
        # The planted panic is a crash, but not the sanitizer report this control needs.
        crash = LANE.classify_libfuzzer(1, CRASH_RUN, ["crash-3e8a"])
        crashed = {"crash-3e8a": LANE.LIBFUZZER_ASAN_MARKER}
        self.assertEqual(LANE.classify_negative_control("libfuzzer-asan", crash, CRASH_RUN, crashed)["status"], "fail")
        clean = LANE.classify_libfuzzer(0, CLEAN_RUN, [], budget_seconds=600)
        self.assertEqual(LANE.classify_negative_control("libfuzzer-asan", clean, CLEAN_RUN, {})["status"], "fail")

    def test_panic_fuzz_control_requires_one_failed_test_with_its_signature(self):
        text = (
            "running 1 test\n"
            f"thread 'x' panicked at tests/panic_fuzz_lower.rs:9:9:\n{LANE.PROPTEST_CONTROL_SIGNATURE}: deliberate\n"
            "test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 5 filtered out; finished in 0.01s\n"
        )
        detector = LANE.FLOOR.classify_result(101, text)
        self.assertEqual(LANE.classify_negative_control("panic-fuzz", detector, text)["status"], "pass")
        self.assertEqual(
            LANE.classify_negative_control("panic-fuzz", detector, text.replace(LANE.PROPTEST_CONTROL_SIGNATURE, "x"))["status"],
            "fail",
        )
        passing = "running 1 test\ntest result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 5 filtered out; finished in 0.01s\n"
        detector = LANE.FLOOR.classify_result(0, passing)
        self.assertEqual(LANE.classify_negative_control("panic-fuzz", detector, passing)["status"], "fail")

    def test_jit_control_requires_the_planted_detection(self):
        detected = {"status": "fail", "planted_detected": True, "genuine_repros": []}
        self.assertEqual(LANE.classify_negative_control("jit-diff", detected)["status"], "pass")
        for detector in (
            {"status": "pass", "planted_detected": False, "genuine_repros": []},
            {"status": "fail", "planted_detected": False, "genuine_repros": []},
            {"status": "fail", "planted_detected": True, "genuine_repros": [{"seed": 2}]},
        ):
            with self.subTest(detector=detector):
                self.assertEqual(LANE.classify_negative_control("jit-diff", detector)["status"], "fail")
        self.assertEqual(LANE.classify_negative_control("unknown", detected)["status"], "fail")


class LaneVerdictTests(unittest.TestCase):
    def complete_report(self, **overrides) -> dict:
        report = {
            "builds": [{"status": "pass"}, {"status": "pass"}, {"status": "pass"}],
            "panic_fuzz": [{"status": "pass"} for _ in LANE.PANIC_FUZZ_FAMILIES],
            "libfuzzer": [{"status": "pass"} for _ in LANE.LIBFUZZER_TARGETS],
            "jit_diff": {"status": "pass"},
            "negative_controls": {kind: {"status": "pass"} for kind in LANE.NEGATIVE_CONTROLS},
            "errors": [], "qualifying": True,
        }
        report.update(overrides)
        return report

    def test_complete_passing_report_passes_and_exit_follows_qualification(self):
        report = self.complete_report()
        report["status"] = LANE.overall_status(report)
        self.assertEqual(report["status"], "pass")
        self.assertEqual(LANE.exit_code(report), 0)
        report["qualifying"] = False
        self.assertEqual(LANE.exit_code(report), 3)
        report["status"] = "fail"
        self.assertEqual(LANE.exit_code(report), 1)

    def test_any_failed_or_missing_section_fails(self):
        for label, overrides in (
            ("a failed build", {"builds": [{"status": "fail"}]}),
            ("a failed family", {"panic_fuzz": [{"status": "fail"}] + [{"status": "pass"}] * (len(LANE.PANIC_FUZZ_FAMILIES) - 1)}),
            ("a missing family", {"panic_fuzz": [{"status": "pass"}]}),
            ("a missing libFuzzer target", {"libfuzzer": [{"status": "pass"}]}),
            ("no JIT run", {"jit_diff": None}),
            ("a failed control", {"negative_controls": {
                kind: {"status": "fail" if kind == "libfuzzer-leak" else "pass"} for kind in LANE.NEGATIVE_CONTROLS
            }}),
            ("a missing control", {"negative_controls": {
                kind: {"status": "pass"} for kind in LANE.NEGATIVE_CONTROLS if kind != "libfuzzer-asan"
            }}),
            ("a lane error", {"errors": ["source changed while the lane was running"]}),
        ):
            with self.subTest(label=label):
                self.assertEqual(LANE.overall_status(self.complete_report(**overrides)), "fail")

    def default_settings(self) -> dict:
        return {
            name: LANE.DEFAULTS[name]
            for name in (*LANE.QUALIFYING_MINIMUMS, *LANE.QUALIFYING_MAXIMUMS, "toolchain")
        }

    def clean_provenance(self) -> dict:
        return {
            "source": {"dirty": False}, "nightly_commit": LANE.FUZZ_TOOLCHAIN_COMMIT,
            "stable_toolchain": {
                "pinned_channel": "1.97.1", "rustc_release": "1.97.1", "rustc_commit": LANE.STABLE_RUSTC_COMMIT,
                "cargo": "cargo 1.97.1 (c980f4866 2026-06-30)",
            },
            "cargo_config": {"problems": []},
        }

    def test_only_the_defaults_on_clean_source_and_the_pinned_nightly_qualify(self):
        self.assertEqual(LANE.qualification_problems(self.default_settings(), self.clean_provenance()), [])
        for name, minimum in LANE.QUALIFYING_MINIMUMS.items():
            self.assertEqual(LANE.DEFAULTS[name], minimum)
        for name, maximum in LANE.QUALIFYING_MAXIMUMS.items():
            self.assertEqual(LANE.DEFAULTS[name], maximum)
        self.assertEqual(LANE.DEFAULTS["toolchain"], LANE.FUZZ_TOOLCHAIN)
        self.assertRegex(LANE.FUZZ_TOOLCHAIN, r"^nightly-\d{4}-\d{2}-\d{2}$")
        self.assertRegex(LANE.FUZZ_TOOLCHAIN_COMMIT, r"^[0-9a-f]{40}$")

    def test_every_setting_outside_its_bound_is_non_qualifying(self):
        provenance = self.clean_provenance()
        for label, overrides in (
            ("a short libFuzzer budget", {"fuzz_seconds": 10}),
            ("fewer proptest cases", {"proptest_cases": 64}),
            ("fewer JIT seeds", {"jit_runs": 5}),
            ("a laxer slow-unit bound", {"libfuzzer_slow_unit_seconds": 3600}),
            ("a laxer per-input timeout", {"libfuzzer_timeout_seconds": 1200}),
            ("a larger RSS limit", {"libfuzzer_rss_limit_mb": 65536}),
            ("the floating nightly", {"toolchain": "nightly"}),
        ):
            with self.subTest(label=label):
                problems = LANE.qualification_problems({**self.default_settings(), **overrides}, provenance)
                self.assertEqual(len(problems), 1, problems)

    def test_dirty_source_or_another_compiler_is_non_qualifying(self):
        settings = self.default_settings()
        for label, provenance in (
            ("a dirty tree", {**self.clean_provenance(), "source": {"dirty": True}}),
            ("no cleanliness verdict", {"nightly_commit": LANE.FUZZ_TOOLCHAIN_COMMIT}),
            ("another commit under the pinned name", {**self.clean_provenance(), "nightly_commit": "0" * 40}),
            ("no provenance", None),
            ("another stable rustc", {**self.clean_provenance(), "stable_toolchain": {
                **self.clean_provenance()["stable_toolchain"], "rustc_release": "1.99.0-nightly"}}),
            ("no stable commit", {**self.clean_provenance(), "stable_toolchain": {
                **self.clean_provenance()["stable_toolchain"], "rustc_commit": None}}),
            ("another commit under the stable name", {**self.clean_provenance(), "stable_toolchain": {
                **self.clean_provenance()["stable_toolchain"], "rustc_commit": "8" * 40}}),
            ("rust-toolchain.toml moved without the lane", {**self.clean_provenance(), "stable_toolchain": {
                **self.clean_provenance()["stable_toolchain"], "pinned_channel": "1.98.0",
                "rustc_release": "1.98.0", "cargo": "cargo 1.98.0 (x 2026-09-01)"}}),
            ("another stable cargo", {**self.clean_provenance(), "stable_toolchain": {
                **self.clean_provenance()["stable_toolchain"], "cargo": "cargo 1.99.0-nightly (x 2026-08-05)"}}),
            ("no pinned channel", {**self.clean_provenance(), "stable_toolchain": {
                **self.clean_provenance()["stable_toolchain"], "pinned_channel": None}}),
            ("a Cargo config problem", {**self.clean_provenance(), "cargo_config": {"problems": ["/x: [env]"]}}),
            ("no Cargo config audit", {**{k: v for k, v in self.clean_provenance().items() if k != "cargo_config"}}),
        ):
            with self.subTest(label=label):
                self.assertTrue(LANE.qualification_problems(settings, provenance))


class EnvironmentTests(unittest.TestCase):
    AMBIENT = {
        "PATH": "/usr/bin", "HOME": "/home/fuzz", "CARGO_TARGET_DIR": "/t", "CARGO_HOME": "/c",
        "RUSTUP_HOME": "/r", "AY_SOLVER_PATH": "/ay", "TCG_EXTERNAL_CLEAN_CHECKER": "/clean",
        "ASAN_OPTIONS": "detect_leaks=0", "LSAN_OPTIONS": "suppressions=/x", "UBSAN_OPTIONS": "halt_on_error=0",
        "MSAN_OPTIONS": "x", "TSAN_OPTIONS": "x", "HWASAN_OPTIONS": "x", "ASAN_SYMBOLIZER_PATH": "/s",
        "RUSTFLAGS": "-Zsanitizer=none", "CARGO_ENCODED_RUSTFLAGS": "-Cpanic=abort", "RUSTC_WRAPPER": "sccache",
        "RUSTUP_TOOLCHAIN": "nightly", "CARGO_BUILD_RUSTFLAGS": "-Coverflow-checks=off",
        "CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUSTFLAGS": "-Cdebug-assertions=off",
        "CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUNNER": "valgrind",
        "CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS": "false", "CARGO_UNSTABLE_BUILD_STD": "std",
        "LLVM_PROFILE_FILE": "/p", "LD_PRELOAD": "/libfake.so", "PROPTEST_CASES": "1", "PROPTEST_FORK": "true",
        "RUST_TEST_THREADS": "8", "RUST_MIN_STACK": "4096", "RUST_BACKTRACE": "full",
        "TCG_NO_PROOF_CERTS": "1", "TRUST_CG_PANIC_FUZZ_NEGATIVE_CONTROL": "1",
    }

    def test_ambient_controls_are_removed_recorded_and_replaced_by_pinned_values(self):
        environment, removed = LANE.controlled_environment(dict(self.AMBIENT), offline=True)
        kept = {"PATH", "HOME", "CARGO_TARGET_DIR", "CARGO_HOME", "RUSTUP_HOME", "AY_SOLVER_PATH",
                "TCG_EXTERNAL_CLEAN_CHECKER"}
        self.assertEqual(set(removed), set(self.AMBIENT) - kept)
        self.assertEqual(removed["ASAN_OPTIONS"], "detect_leaks=0")
        for name in kept:
            self.assertEqual(environment[name], self.AMBIENT[name])
        for name, value in LANE.PINNED_ENVIRONMENT.items():
            self.assertEqual(environment[name], value)
        self.assertEqual(environment["CARGO_NET_OFFLINE"], "true")
        self.assertEqual(set(environment), kept | set(LANE.PINNED_ENVIRONMENT) | {"CARGO_NET_OFFLINE"})

    def test_c_toolchain_and_cargo_config_variables_are_removed_and_rustup_never_installs(self):
        ambient = {
            "PATH": "/usr/bin", "CFLAGS": "-O0", "CXXFLAGS": "-DPROBE=1", "CPPFLAGS": "-DX", "LDFLAGS": "-L/x",
            "CC": "clang", "CXX": "clang++", "CC_aarch64_unknown_linux_gnu": "x", "TARGET_CFLAGS": "-O0",
            "HOST_CC": "gcc", "LD_LIBRARY_PATH": "/empty", "CUSTOM_LIBFUZZER_PATH": "/libFuzzer.a",
            "CARGO_ALIAS_PROBE": "version", "CARGO_ENV_PROBE": "1", "CARGO_SOURCE_CRATES_IO_REPLACE_WITH": "v",
            "CARGO_TERM_COLOR": "never", "RUSTUP_AUTO_INSTALL": "1", "CARGO_TERM_QUIET": "true",
            # The GCC driver's own search and option variables.
            "COMPILER_PATH": "/evil", "GCC_EXEC_PREFIX": "/evil/", "CCC_OVERRIDE_OPTIONS": "+-O0",
            "LD_RUN_PATH": "/evil", "COLLECT_GCC_OPTIONS": "-O0",
            # Variables Cargo sets for its children.
            "CARGO_MANIFEST_DIR": "/x", "CARGO_PKG_NAME": "x", "CARGO_MAKEFLAGS": "-j1",
            "CARGO_FEATURE_NEGATIVE_CONTROL": "1",
        }
        environment, removed = LANE.controlled_environment(ambient, offline=False)
        self.assertEqual(set(removed), set(ambient) - {"PATH", "CARGO_TERM_COLOR"})
        self.assertEqual(environment["CARGO_TERM_COLOR"], "never")
        self.assertEqual(environment["RUSTUP_AUTO_INSTALL"], "0")
        self.assertEqual(LANE.CONFIG_AUDIT.environment_problems(environment), [])

    def test_a_build_tools_own_config_prefix_is_scrubbed_like_cargos(self):
        ambient = {"PATH": "/usr/bin", "TARGO_BUILD_RUSTFLAGS": "--cfg x", "TARGO_TERM_COLOR": "never",
                   "TARGO_PKG_NAME": "x"}
        prefixes = LANE.CONFIG_AUDIT.environment_prefixes("targo")
        environment, removed = LANE.controlled_environment(ambient, offline=False, prefixes=prefixes)
        self.assertEqual(set(removed), {"TARGO_BUILD_RUSTFLAGS", "TARGO_PKG_NAME"})
        self.assertEqual(LANE.CONFIG_AUDIT.environment_problems(environment, prefixes), [])
        # The lane's own stock Cargo does not read them.
        self.assertEqual(LANE.controlled_environment(ambient, offline=False)[1], {})

    def test_the_instrumented_binaries_get_leak_detection_stated_in_full(self):
        options = dict(item.split("=", 1) for item in LANE.LIBFUZZER_ENVIRONMENT["ASAN_OPTIONS"].split(":"))
        self.assertEqual(options["detect_leaks"], "1")
        self.assertEqual(set(LANE.LIBFUZZER_ENVIRONMENT), {"ASAN_OPTIONS"})
        self.assertFalse(any(LANE.scrubbed(name) for name in ("PATH", "HOME", "CARGO_TARGET_DIR", "CARGO_HOME")))


class InventoryTests(unittest.TestCase):
    def test_libfuzzer_targets_are_the_fuzz_crate_bins(self):
        manifest = (ROOT / "fuzz" / "Cargo.toml").read_text()
        bins = re.findall(r'^\[\[bin\]\]\nname = "([^"]+)"', manifest, re.MULTILINE)
        self.assertEqual(sorted(bins), sorted(LANE.LIBFUZZER_TARGETS))
        for target in LANE.LIBFUZZER_TARGETS:
            self.assertTrue((ROOT / "fuzz" / "fuzz_targets" / f"{target}.rs").is_file())
        self.assertRegex(manifest, rf"(?m)^{re.escape(LANE.LIBFUZZER_CONTROL_FEATURE)} = \[\]$")

    def test_planted_markers_match_their_sources(self):
        target = (ROOT / "fuzz" / "fuzz_targets" / f"{LANE.LIBFUZZER_CONTROL_TARGET}.rs").read_text()
        self.assertIn(f'NEGATIVE_CONTROL_MARKER: &[u8] = b"{LANE.LIBFUZZER_CONTROL_MARKER.decode()}";', target)
        self.assertIn(f'NEGATIVE_LEAK_MARKER: &[u8] = b"{LANE.LIBFUZZER_LEAK_MARKER.decode()}";', target)
        self.assertIn(f'NEGATIVE_ASAN_MARKER: &[u8] = b"{LANE.LIBFUZZER_ASAN_MARKER.decode()}";', target)
        self.assertIn("fn planted_leak()", target)
        self.assertIn("fn planted_heap_overflow_read()", target)
        markers = [marker for marker, _, _ in LANE.LIBFUZZER_CONTROLS.values()]
        for marker in markers:
            self.assertEqual([other for other in markers if other.startswith(marker)], [marker])
        self.assertIn(f'panic!("{LANE.LIBFUZZER_CONTROL_PANIC}")', target)
        self.assertIn(f'#[cfg(feature = "{LANE.LIBFUZZER_CONTROL_FEATURE}")]', target)
        driver = (ROOT / "crates" / "trust-cg-fuzz" / "src" / "bin" / f"{LANE.JIT_DRIVER}.rs").read_text()
        self.assertIn(f'const PLANTED_MISCOMPILE_TAG: &str = "{LANE.JIT_CONTROL_TAG}";', driver)
        lower = (ROOT / "crates" / "trust-cg-lower" / "tests" / "panic_fuzz_lower.rs").read_text()
        self.assertIn(f"fn {LANE.PROPTEST_CONTROL[2]}()", lower)
        self.assertIn(LANE.PROPTEST_CONTROL_SIGNATURE, lower)
        self.assertIn(LANE.PROPTEST_CONTROL_ENV, lower)

    def test_panic_fuzz_families_are_pinned_floor_targets(self):
        evidence = (ROOT / "scripts" / "run_panic_fuzz_evidence.sh").read_text()
        for package, target in LANE.PANIC_FUZZ_FAMILIES:
            with self.subTest(target=target):
                self.assertIn((package, target), LANE.FLOOR.TARGETS)
                self.assertIn((package, target), LANE.FLOOR.TARGET_MINIMUM_PASSES)
        # The older panic-fuzz evidence script names the same libFuzzer targets.
        for target in LANE.LIBFUZZER_TARGETS:
            self.assertIn(f'    "{target}"\n', evidence)


class StableToolchainAndProbeTests(unittest.TestCase):
    def test_the_stable_identity_is_read_against_the_lanes_own_stock_pin(self):
        # STOCK EXCEPTION: the repository pins Trust; the lane pins its stock channel.
        self.assertEqual(LANE.pinned_stable_channel(), "1.97.1")
        self.assertIn('channel = "trust"', (ROOT / "rust-toolchain.toml").read_text())
        self.assertEqual(LANE.PINNED_ENVIRONMENT["RUSTUP_TOOLCHAIN"], LANE.STABLE_TOOLCHAIN)
        verbose = "rustc 1.97.1 (8bab26f4f 2026-07-14)\nbinary: rustc\ncommit-hash: " + "8" * 40 + "\nrelease: 1.97.1\n"
        identity = LANE.stable_identity(verbose, "cargo 1.97.1 (c980f4866 2026-06-30)")
        self.assertEqual(identity["rustc_release"], "1.97.1")
        self.assertEqual(identity["rustc_commit"], "8" * 40)
        self.assertEqual(identity["pinned_channel"], "1.97.1")

    def test_the_stable_pin_is_the_lanes_explicit_stock_exception(self):
        self.assertEqual(LANE.STABLE_TOOLCHAIN, LANE.pinned_stable_channel())
        self.assertRegex(LANE.STABLE_RUSTC_COMMIT, r"^[0-9a-f]{40}$")
        source = (ROOT / "scripts" / "run_linux_fuzz_lane.py").read_text()
        self.assertIn("STOCK EXCEPTION (Trust lacks an ASan runtime", source)

    def test_every_family_must_report_the_lanes_case_count(self):
        self.assertEqual(set(LANE.PANIC_FUZZ_FAMILIES), set(LANE.FLOOR.PROPTEST_CASE_DEFAULTS))
        for package, target in LANE.PANIC_FUZZ_FAMILIES:
            with self.subTest(target=target):
                self.assertEqual(LANE.proptest_probe_lines(package, target, 10000),
                                 ("panic-fuzz proptest cases: configured=10000 run=10000",))
        self.assertEqual(LANE.proptest_probe_lines("trust-cg-lower", "aarch64_variadic_abi", 10000), ())

    def test_a_trust_build_of_cargo_is_recognized_by_its_trust_line(self):
        self.assertTrue(LANE.is_trust_build("cargo 1.99.0-dev (a62ae50d8 2026-09-16)\nrelease: 1.99.0-dev\ntrust: 0.1.0\n"))
        self.assertFalse(LANE.is_trust_build("cargo 1.97.1 (c980f4866 2026-06-30)\nrelease: 1.97.1\n"))
        self.assertFalse(LANE.is_trust_build("cargo 1.97.1\nnote: trust: no\n"))
        # The Linux floor has no stock lane, so the check lives with the lane that has one.
        self.assertFalse(hasattr(LANE.FLOOR, "is_trust_build"))

    def test_the_lane_refuses_a_trust_build_of_cargo(self):
        def probe(command, environment=None):
            if Path(command[0]).name == "rustc":
                return "rustc 1.97.1\nhost: aarch64-unknown-linux-gnu\nrelease: 1.97.1\n"
            if command[1:] == ["-vV"]:
                return "cargo 1.99.0-dev (a62ae50d8 2026-09-16)\nrelease: 1.99.0-dev\ntrust: 0.1.0\n"
            raise AssertionError(f"probed past the identity check: {command}")

        with tempfile.TemporaryDirectory() as temp:
            for name in ("git", "cargo", "rustc", "rustup"):
                tool = Path(temp) / name
                tool.write_text("#!/bin/sh\nexit 1\n")
                tool.chmod(0o700)
            # The Linux-host check runs first; pin it so the refusal under test
            # is reached on any development host.
            with mock.patch.object(LANE, "probe", side_effect=probe), \
                    mock.patch.object(LANE.sys, "platform", "linux"), \
                    self.assertRaisesRegex(RuntimeError, "Trust build of Cargo"):
                LANE.preflight(LANE.FUZZ_TOOLCHAIN, {"PATH": temp})


class CommandLineTests(unittest.TestCase):
    def test_a_cargo_config_problem_refuses_the_lane_before_any_cargo_command(self):
        # preflight's version probes (`cargo fuzz --version` could be an
        # [alias]) run only after the audit.
        audit = {"files": [], "environment": {}, "problems": ["/home/x/.cargo/config.toml: [env]"]}
        with tempfile.TemporaryDirectory() as temp:
            out = Path(temp) / "lane"
            with mock.patch.object(LANE, "preflight", side_effect=AssertionError("probed")), \
                    mock.patch.object(LANE.CONFIG_AUDIT, "audit", return_value=audit), \
                    mock.patch.object(LANE, "run_logged", side_effect=AssertionError("a child ran")), \
                    contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(LANE.main(["--out", str(out)]), 1)
            report = json.loads((out / "report.json").read_text())
        self.assertEqual(report["status"], "fail")
        self.assertIn("cargo config: /home/x/.cargo/config.toml: [env]", report["errors"])
        self.assertEqual(report["cargo_config"], audit)
        self.assertNotIn("provenance", report)
        self.assertFalse(report["qualifying"])
        output = io.StringIO()
        with mock.patch.object(LANE, "prerequisite_problems", side_effect=AssertionError("probed")), \
                mock.patch.object(LANE.CONFIG_AUDIT, "audit", return_value=audit), \
                contextlib.redirect_stdout(output):
            self.assertEqual(LANE.main(["--check-prerequisites"]), 1)
        self.assertIn("a Cargo config would change what the lane runs", output.getvalue())

    def test_list_is_read_only(self):
        output = io.StringIO()
        with mock.patch.object(LANE, "preflight", side_effect=AssertionError("probed")), contextlib.redirect_stdout(output):
            self.assertEqual(LANE.main(["--list"]), 0)
        lines = output.getvalue().splitlines()
        self.assertEqual(len([line for line in lines if line.startswith("libfuzzer ")]), len(LANE.LIBFUZZER_TARGETS))
        self.assertEqual(len([line for line in lines if line.startswith("panic-fuzz ")]), len(LANE.PANIC_FUZZ_FAMILIES))
        self.assertEqual(len([line for line in lines if line.startswith("negative-control ")]), 5)
        self.assertIn(f"toolchain {LANE.FUZZ_TOOLCHAIN} {LANE.FUZZ_TOOLCHAIN_COMMIT}", lines)

    def test_output_inside_the_source_tree_is_refused(self):
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(LANE.main(["--out", str(ROOT / "fuzz-lane-output")]), 1)
        self.assertFalse((ROOT / "fuzz-lane-output").exists())

    def test_more_than_four_libfuzzer_processes_is_a_usage_error(self):
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
            LANE.main(["--parallel", "5", "--list"])
        self.assertEqual(raised.exception.code, 2)

    def test_preflight_failure_is_retained_and_cannot_pass(self):
        with tempfile.TemporaryDirectory() as temp:
            out = Path(temp) / "lane"
            with mock.patch.object(LANE, "preflight", side_effect=RuntimeError("required Linux host is aarch64-unknown-linux-gnu")), \
                    contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(LANE.main(["--out", str(out)]), 1)
            report = json.loads((out / "report.json").read_text())
        self.assertEqual(report["status"], "fail")
        self.assertIn("required Linux host is aarch64-unknown-linux-gnu", report["errors"])
        self.assertFalse(report["qualifying"])
        self.assertIn("no provenance was recorded", report["non_qualifying_reasons"])

    def test_prerequisite_check_names_what_is_missing(self):
        with mock.patch.object(LANE, "prerequisite_problems", return_value=(["cargo-fuzz is not installed"], {})), \
                contextlib.redirect_stdout(io.StringIO()) as output, mock.patch.object(LANE, "preflight", side_effect=AssertionError):
            self.assertEqual(LANE.main(["--check-prerequisites"]), 1)
        self.assertIn("cargo-fuzz is not installed", output.getvalue())
        found = {"nightly_commit": LANE.FUZZ_TOOLCHAIN_COMMIT, "cargo_fuzz": "cargo-fuzz 0.13.2"}
        with mock.patch.object(LANE, "prerequisite_problems", return_value=([], found)), \
                contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(LANE.main(["--check-prerequisites"]), 0)
        self.assertIn(LANE.FUZZ_TOOLCHAIN, output.getvalue())

    def test_prerequisites_refuse_a_toolchain_other_than_the_pin(self):
        with mock.patch.object(LANE, "probe", side_effect=RuntimeError("not probed")), \
                mock.patch.object(LANE.shutil, "which", return_value="/usr/bin/tool"):
            problems, _ = LANE.prerequisite_problems("nightly", {"PATH": "/usr/bin"})
        self.assertTrue(any("is not the pinned" in problem for problem in problems), problems)


if __name__ == "__main__":
    unittest.main()
