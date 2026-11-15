"""Regression coverage for measurement classification and baseline isolation."""

from __future__ import annotations

import copy
import importlib.util
import json
import re
import statistics
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("perf_ratchet", ROOT / "scripts/check_perf_ratchet.py")
ratchet = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ratchet)
ratchet_gates = sys.modules["check_gates"]
# The contract corpus, in order: fixtures measure exactly it (a subset is never evidence).
P = ratchet_gates.corpus_programs()


MIB = 1 << 20
FLOOR = 10 * MIB
CROSS_CHECK = {"sampler_floor_bytes": FLOOR, "rusage_covers_allocation": True, "agree": True,
               "time_wrapper_present": True}
CHECKER = {"tool": "clean", "candidates": [
    {"path": "/pkg/store/clean/current/bin/clean", "route": "aterm-packaged",
     "sha256": "cc" * 32, "runs": True, "probe": "--version", "version": "clean 0.9.0"}]}


def lane(times, ok=None):
    """A lane record shaped like the harness's: raw samples and their median."""
    record = {"times_s": list(times), "median_s": statistics.median(times) if times else None}
    if ok is not None:
        record["ok"] = ok
    else:
        record.update(exit=0, nondet_exit=None)  # successful runtime stand-in
    return record


N_RSS = ratchet_gates.RSS_CONTRACT_N


def rss_samples(value, n=N_RSS):
    """N retained sampler records that all read VALUE (a failed sample reads None)."""
    return [{"bytes": value, "status": "ok" if value else "signaled", "returncode": 0,
             "wall_s": 0.1} for _ in range(n)]


def sync_rss_samples(row):
    """Make a row's retained RSS samples read its stamped per-lane readings:
    tests edit the stamped readings, the samples follow as N identical ones."""
    samples = row.setdefault("rss_samples", {})
    for field, kind in ratchet_gates.RSS_SAMPLE_KIND.items():
        samples[kind] = {lane: rss_samples(value) for lane, value in (row.get(field) or {}).items()}
    return row


def program(size=(3_000_000, 3_000_000), rss=(40 * MIB, 40 * MIB),
            compile_rss=(200 * MIB, 205 * MIB, 200 * MIB), verdict="MATCH",
            runtime=(1.0, 0.9), compile=(1.0, 0.9), category="scalar", cold=None,
            emitted=(2_000, 2_000)):
    """One per-program row shaped like the harness's: raw runtime and compile
    samples for every lane, every size reading, and N retained samples behind
    every peak-RSS reading (their median is the stamped reading)."""
    compile_lanes = {f"llvm_o{opt}": lane([compile[0]] * 3, ok=True) for opt in "023"}
    compile_lanes["bridge_warm"] = lane([compile[1]] * 3, ok=True)
    if cold is not None:
        compile_lanes["bridge_cold"] = lane([cold] * 3, ok=True)
    return sync_rss_samples({
        "category": category, "verdict": verdict, "label": None, "ratios": {},
        "run": {"llvm_o3": lane([runtime[0]] * 5), "bridge": lane([runtime[1]] * 5)},
        "compile": compile_lanes,
        "size_bytes": dict(zip(("llvm_o3", "bridge"), size)),
        "emitted_size_bytes": dict(zip(("llvm_o3", "bridge"), emitted)),
        "peak_rss_bytes": dict(zip(("llvm_o3", "bridge"), rss)),
        "compile_peak_rss_bytes": dict(zip(("llvm_o2", "llvm_o3", "bridge"), compile_rss)),
    })


def restamp(data):
    """Recompute every stamped aggregate from the per-program table with the
    harness's own functions, after a test edits the table or the sampler (an
    edited stamped RSS reading carries its retained samples with it)."""
    for row in data["programs"].values():
        if isinstance(row, dict) and "rss_samples" in row:
            sync_rss_samples(row)
    data["aggregates"].update(ratchet_gates.table_aggregates(data))
    return data


def results():
    provenance = dict.fromkeys(ratchet.MANDATORY_PROVENANCE, "recorded")
    provenance.update(
        git_dirty=False, quiet=True, tcg_env={}, n_compile=3, n_run=5, n_rss=N_RSS,
        cache={"mode": "warm"}, host_arch="aarch64", host_model="test-host",
        target="aarch64-apple-darwin", load_status="QUIET",
        provenance_complete=True, rss_sampling={"cross_check": dict(CROSS_CHECK)},
        proof_checker=copy.deepcopy(CHECKER), bridge_cg_args=[], proof_checker_degraded=[],
    )
    data = {
        "provenance": provenance,
        "headline_eligible": True,
        "programs": {name: program() for name in P},
        "aggregates": {},
    }
    return restamp(data)


def linux_legacy(data):
    """Make a fixture comparable with the committed aarch64 Linux evidence rows."""
    data["provenance"].update(host_arch="aarch64", host_model="spark-d5a4",
                              target="aarch64-unknown-linux-gnu")
    return data


class FloorBoundRssTests(unittest.TestCase):
    """gates.json version 4 (ruling OD-32): a floor-bound comparison yields no ratio."""

    def test_floor_bound_programs_keep_no_rss_ratio_on_the_ledger_row(self):
        data = results()
        first, second = P[0], P[1]
        data["programs"][first]["peak_rss_bytes"] = {"llvm_o3": 15 * MIB, "bridge": 16 * MIB}
        restamp(data)
        ratios = ratchet._row_program_ratios(data)
        self.assertIsNone(ratios[first]["rss_vs_llvm_o3"])
        self.assertEqual(ratios[second]["rss_vs_llvm_o3"], 1.0)
        self.assertIsNone(data["aggregates"]["rss_geomean_vs_llvm_o3"])
        self.assertEqual(data["aggregates"]["program_rss_floor_bound_count"], 1)

    def test_an_uncalibrated_sampler_keeps_no_rss_ratio(self):
        data = results()
        data["provenance"]["rss_sampling"] = {}
        restamp(data)
        ratios = ratchet._row_program_ratios(data)
        self.assertTrue(all(row["rss_vs_llvm_o3"] is None for row in ratios.values()))
        self.assertIsNone(data["aggregates"]["rss_geomean_vs_llvm_o3"])


class GateTests(unittest.TestCase):
    def test_standalone_checker_rejects_invalid_ratios(self):
        with tempfile.TemporaryDirectory(prefix="trust-cg-gates-") as temporary:
            path = Path(temporary) / "results.json"
            for value in (0, -1, float("nan")):
                data = results()
                data["aggregates"]["runtime_geomean_vs_llvm_o3"] = value
                path.write_text(json.dumps(data), encoding="utf-8")
                result = subprocess.run(
                    [sys.executable, str(ROOT / "benchmarks/beat-llvm/contract/check_gates.py"), str(path)],
                    capture_output=True, text=True, check=False,
                )
                with self.subTest(value=value):
                    self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                    self.assertNotIn("PASS", result.stdout)
                    self.assertIn("finite positive ratio", result.stderr)

    def test_malformed_predicates_never_pass(self):
        for predicate in ("", " ", ".a", ".a ==", ".a == true and", ".a and true"):
            with self.subTest(predicate=predicate), self.assertRaises(ValueError):
                ratchet.evaluate(predicate, {"a": True})

    def test_conjunction_still_checks_later_comparisons(self):
        self.assertFalse(ratchet.evaluate(".a == true and .b <= 1.0", {"a": True, "b": 2}))
        self.assertTrue(ratchet.evaluate(".a == true and .b <= 1.0", {"a": True, "b": 1}))

    def test_numeric_stamps_cannot_impersonate_booleans(self):
        self.assertFalse(ratchet.evaluate(".a == true", {"a": 1}))
        self.assertFalse(ratchet.evaluate(".a == false", {"a": 0}))

    def test_nonnumeric_thresholds_fail_closed(self):
        for value in (None, True, False, "0.5", float("nan"), float("inf"), -float("inf")):
            with self.subTest(value=value):
                self.assertFalse(ratchet.evaluate(".a <= 1.0", {"a": value}))


class PerfRatchetTests(unittest.TestCase):
    def test_missing_and_null_measurements_are_unmeasured(self):
        for value in ({}, {"compile_cold_geomean_vs_llvm_o2": None}):
            data = results()
            data["aggregates"].update(value)
            row = ratchet.condense(data, "sample.json")
            self.assertIsNone(row["gates"]["G2_M1_compile_cold_vs_O2"])

    def test_failed_runtime_cannot_be_headline_evidence_or_a_baseline(self):
        eligibility = json.loads(ratchet.GATES.read_text())["eligibility"]
        self.assertTrue(ratchet_gates.evidence_eligible(results(), eligibility))
        for change in ({"exit": -9}, {"exit": 126}, {"exit": 7},
                       {"nondet_exit": 7}, {"error": {"kind": "timeout"}}):
            with self.subTest(change=change):
                data = results()
                data["programs"][P[0]]["run"]["bridge"].update(change)
                data["headline_eligible"] = True
                restamp(data)
                self.assertFalse(ratchet_gates.evidence_eligible(data, eligibility))
                row = ratchet.condense(data, "failed-runtime.json")
                self.assertFalse(row["evidence"])
                self.assertIsNone(row["runtime_geomean_vs_llvm_o3"])

    def test_partially_measured_gate_cannot_be_a_failed_measurement(self):
        data = results()
        data["programs"][P[4]]["run"]["bridge"]["times_s"] = []  # one program lacks its runtime
        restamp(data)
        row = ratchet.condense(data, "sample.json")
        self.assertIsNone(row["runtime_worst_vs_llvm_o3"])
        self.assertIsNone(row["gates"]["G1c_GATE_SB_M6"])

    def test_measured_failure_is_preserved(self):
        data = results()
        data["programs"] = {name: program(cold=3.0) for name in P}
        restamp(data)
        row = ratchet.condense(data, "sample.json")
        self.assertIs(row["gates"]["G2_M1_compile_cold_vs_O2"], False)

    def test_headline_stamp_cannot_override_provenance(self):
        for field, value in (("git_dirty", True), ("quiet", False), ("n_compile", 1),
                             ("n_run", 1), ("provenance_complete", False),
                             ("load_threshold_overridden", True),
                             ("tcg_env", {"TCG_NO_PROOF_CERTS": "1"})):
            data = results()
            data["provenance"][field] = value
            self.assertFalse(ratchet.condense(data, "sample.json")["evidence"])
        data = results()
        data["headline_eligible"] = "false"
        self.assertFalse(ratchet.condense(data, "sample.json")["evidence"])

    def test_host_and_target_boundaries_keep_ratchets_comparable(self):
        row = ratchet.condense(results(), "current.json")
        baseline = copy.deepcopy(row)
        baseline.update(source_results="baseline.json", runtime_geomean_vs_llvm_o3=0.1)
        thresholds = json.loads(ratchet.BASELINE.read_text())["thresholds"]
        self.assertTrue(ratchet.ratchet_check(row, [baseline], thresholds))
        for field in ("host_arch", "host_model", "target"):
            unrelated = copy.deepcopy(baseline)
            unrelated[field] = "other"
            with self.subTest(field=field):
                self.assertEqual(ratchet.ratchet_check(row, [unrelated], thresholds), [])

    def test_cpu_model_rows_keep_their_legacy_baselines(self):
        """host_model became the CPU model; a new row must still be compared with
        the committed rows keyed on the machine identity (hostname / hw.model)."""
        thresholds = json.loads(ratchet.BASELINE.read_text())["thresholds"]
        legacy = ratchet.condense(results(), "legacy.json")
        legacy.update(host_model="spark-d5a4", runtime_geomean_vs_llvm_o3=0.1)
        for field in ("host_model_source", "legacy_host_model"):
            legacy.pop(field)  # rows condensed before these fields existed
        data = results()
        data["provenance"].update(host_model="Cortex-X925 + Cortex-A725",
                                  host_model_source="lscpu Model name",
                                  legacy_host_model="spark-d5a4")
        row = ratchet.condense(data, "current.json")
        self.assertEqual(row["legacy_host_model"], "spark-d5a4")
        self.assertTrue(ratchet.comparable(row, legacy))
        self.assertTrue(ratchet.ratchet_check(row, [legacy], thresholds))
        # ...and an old-format row appended later still meets the new rows.
        newer = copy.deepcopy(row)
        newer.update(source_results="newer.json", runtime_geomean_vs_llvm_o3=0.1)
        old_row = copy.deepcopy(legacy)
        old_row.update(source_results="old.json", runtime_geomean_vs_llvm_o3=0.9)
        self.assertTrue(ratchet.comparable(old_row, newer))
        self.assertTrue(ratchet.ratchet_check(old_row, [newer], thresholds))
        for change in ({"legacy_host_model": "other-host"}, {"legacy_host_model": None},
                       {"host_arch": "x86_64"}, {"target": "x86_64-apple-darwin"}):
            other = copy.deepcopy(row)
            other.update(change)
            with self.subTest(change=change):
                self.assertFalse(ratchet.comparable(other, legacy))
                self.assertEqual(ratchet.ratchet_check(other, [legacy], thresholds), [])
        # Two CPU-model rows are matched on the CPU model, not on the hostname.
        moved = copy.deepcopy(newer)
        moved.update(host_model="Apple M4 Max")
        self.assertFalse(ratchet.comparable(row, moved))

    def test_committed_dgx_baselines_stay_comparable(self):
        """The committed aarch64 Linux evidence rows (host_model "spark-d5a4")
        remain baselines for a CPU-model row from the same host."""
        ledger = ratchet.read_ledger()
        data = results()
        data["provenance"].update(host_arch="aarch64", target="aarch64-unknown-linux-gnu",
                                  host_model="Cortex-X925 + Cortex-A725",
                                  host_model_source="lscpu Model name",
                                  legacy_host_model="spark-d5a4")
        row = ratchet.condense(data, "current.json")
        baselines = [r for r in ledger if r.get("evidence") is True and ratchet.comparable(row, r)]
        self.assertTrue(baselines)
        self.assertTrue(all(r["host_model"] == "spark-d5a4" for r in baselines))

    def test_malformed_metrics_are_rejected_before_condensation(self):
        self.assertEqual(ratchet.validate(results(), "sample"), [])
        for field, value in (("coverage_pct", float("nan")), ("match_count", True),
                             ("runtime_geomean_vs_llvm_o3", 0),
                             ("runtime_geomean_vs_llvm_o3", -float("inf"))):
            data = results()
            data["aggregates"][field] = value
            with self.subTest(field=field, value=value):
                self.assertTrue(ratchet.validate(data, "sample"))
        for data in ([], {"provenance": {}}, {"provenance": {}, "aggregates": []}):
            self.assertTrue(ratchet.validate(data, "sample"))

    def test_current_evidence_requires_head_clean_trees_and_recomputed_eligibility(self):
        eligibility = json.loads(ratchet.GATES.read_text())["eligibility"]
        self.assertEqual(ratchet.current_evidence_problems(results(), "recorded", [], eligibility), [])
        cases = (
            ("stale source", {"git_sha": "0" * 40}, [], "is not HEAD"),
            ("dirty measurement", {"git_dirty": True}, [], "measured tree had tracked edits"),
            ("unstamped dirtiness", {"git_dirty": None}, [], "measured tree had tracked edits"),
            ("edited checkout", {}, [" M crates/x.rs"], "tracked edit(s)"),
            ("loaded machine", {"load_status": "LOADED"}, [], "not headline-eligible"),
            ("proof-weakened", {"tcg_env": {"TCG_NO_PROOF_CERTS": "1"}}, [], "not headline-eligible"),
        )
        for name, changes, edits, expected in cases:
            data = results()
            data["provenance"].update(changes)
            with self.subTest(case=name):
                problems = ratchet.current_evidence_problems(data, "recorded", edits, eligibility)
                self.assertTrue(any(expected in problem for problem in problems), problems)
        self.assertTrue(ratchet.current_evidence_problems({}, "recorded", [], eligibility))

    def test_current_source_counts_tracked_edits_like_the_harness(self):
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary).resolve()
            subprocess.run(["git", "init", "-q", str(repo)], check=True)
            tracked = repo / "tracked.rs"
            tracked.write_text("fn a() {}\n")
            subprocess.run(["git", "-C", str(repo), "add", "tracked.rs"], check=True)
            subprocess.run([
                "git", "-C", str(repo), "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                "-c", "core.hooksPath=/dev/null", "-c", "commit.gpgsign=false", "commit", "-qm", "fixture",
            ], check=True)
            head = subprocess.run(["git", "-C", str(repo), "rev-parse", "HEAD"],
                                  capture_output=True, text=True, check=True).stdout.strip()
            (repo / "untracked.txt").write_text("local note\n")
            self.assertEqual(ratchet.current_source(repo), (head, []))
            tracked.write_text("fn b() {}\n")
            self.assertEqual(ratchet.current_source(repo), (head, [" M tracked.rs"]))

    def test_require_current_fails_a_ratchet_green_but_stale_results_file(self):
        with tempfile.TemporaryDirectory(prefix="trust-cg-ratchet-") as temporary:
            path = Path(temporary) / "results.json"
            path.write_text(json.dumps(results()), encoding="utf-8")
            command = [sys.executable, str(ROOT / "scripts/check_perf_ratchet.py"), str(path)]
            green = subprocess.run(command, capture_output=True, text=True, check=False)
            stale = subprocess.run([*command, "--require-current"], capture_output=True, text=True, check=False)
        self.assertEqual(green.returncode, 0, green.stdout + green.stderr)
        self.assertEqual(stale.returncode, ratchet.NOT_CURRENT_EXIT, stale.stdout + stale.stderr)
        self.assertIn("NOT CURRENT", stale.stderr)
        self.assertIn("is not HEAD", stale.stderr)

    def test_parity_and_retention_provenance_is_condensed(self):
        data = results()
        data["provenance"].update(
            host_model="Apple M4 Max", host_model_source="sysctl machdep.cpu.brand_string",
            machine_model="Mac16,5", cpu_features=["FEAT_LSE", "neon"],
            cpu_features_sha256="ab" * 32,
            cpu_policy={"target_cpu": "default", "target_feature": "default",
                        "lane_parity": True, "llvm_default_target_cpu": "apple-m1",
                        "bridge_extra_flags": ["-Zcodegen-backend=x"]},
            affinity={"policy": "pinned", "core": 4, "selection": "explicit --pin-core",
                      "heterogeneous": True, "method": "os.sched_setaffinity"},
            rss_sampling={"method": "getrusage", "ru_maxrss_unit": "KiB",
                          "cross_check": {"sampler_floor_bytes": 9437184, "agree": True}},
        )
        data["retention"] = {"dir": "reports/perf/2026-09-18-abcdef012345"}
        row = ratchet.condense(data, "sample.json")
        self.assertEqual(row["host_model"], "Apple M4 Max")
        self.assertEqual(row["machine_model"], "Mac16,5")
        self.assertEqual(row["cpu_features_count"], 2)
        self.assertEqual(row["cpu_features_sha256"], "ab" * 32)
        self.assertEqual(row["cpu_policy"], {"target_cpu": "default", "target_feature": "default",
                                             "lane_parity": True,
                                             "llvm_default_target_cpu": "apple-m1"})
        self.assertEqual(row["affinity"], {"policy": "pinned", "core": 4,
                                           "selection": "explicit --pin-core",
                                           "heterogeneous": True})
        self.assertEqual(row["rss_sampling"], {"method": "getrusage", "ru_maxrss_unit": "KiB",
                                               "method_id": None, "sampler_identity": None,
                                               "sampler_floor_bytes": 9437184,
                                               "cross_check_agree": True})
        self.assertEqual(row["retained_dir"], "reports/perf/2026-09-18-abcdef012345")
        json.dumps(row)  # the ledger row stays serialisable

    def test_results_without_parity_provenance_condense_to_null(self):
        data = results()
        data["provenance"].pop("rss_sampling")
        restamp(data)
        self.assertEqual(ratchet.validate(data, "sample"), [])
        row = ratchet.condense(data, "sample.json")
        for field in ("host_model_source", "machine_model", "legacy_host_model",
                      "cpu_features_count", "cpu_features_sha256", "cpu_policy", "affinity",
                      "rss_sampling", "retained_dir"):
            with self.subTest(field=field):
                self.assertIsNone(row[field])
        data["provenance"].update(cpu_policy="default", affinity=[], rss_sampling="rusage",
                                  cpu_features="neon")
        data["retention"] = "reports/perf/x"
        row = ratchet.condense(data, "sample.json")
        for field in ("cpu_policy", "affinity", "rss_sampling", "cpu_features_count",
                      "retained_dir"):
            with self.subTest(malformed=field):
                self.assertIsNone(row[field])

    def test_parity_provenance_cannot_make_a_row_evidence(self):
        data = results()
        data["provenance"].update(provenance_complete=False,
                                  affinity={"policy": "pinned", "core": 0})
        self.assertFalse(ratchet.condense(data, "sample.json")["evidence"])

    def test_coverage_cannot_hide_missing_corpus_rows(self):
        for changes in ({"match_count": 17}, {"coverage_pct": 99.0},
                        {"total_programs": 0, "match_count": 0}):
            data = results()
            data["aggregates"].update(changes)
            with self.subTest(changes=changes):
                self.assertTrue(ratchet.validate(data, "sample"))
        data = results()
        data["programs"][P[17]]["verdict"] = "INCOMPLETE"
        data["aggregates"].update(match_count=17, incomplete_count=1, coverage_pct=94.4)
        restamp(data)
        self.assertEqual(ratchet.validate(data, "sample"), [])


class ResourceGateTests(unittest.TestCase):
    """Size and peak-RSS predicates (gates.json version 2) and their ratchet."""

    def thresholds(self):
        return json.loads(ratchet.BASELINE.read_text())["thresholds"]

    def test_an_all_refused_row_renders_unmeasured_not_none(self):
        # The first aarch64-apple-darwin row (2026-09-28) had every program
        # fail closed, so no compile geomean exists; the badge printed "Nonex".
        data = results()
        for name in P:
            data["programs"][name] = program(verdict="INCOMPLETE")
        row = ratchet.condense(restamp(data), "refused.json")
        self.assertEqual((row["match_count"], row["coverage_pct"]), (0, 0.0))
        self.assertIsNone(row["compile_warm_geomean_vs_llvm_o2"])
        badge = "\n".join(ratchet._badge_block([row]))
        self.assertNotIn("None", badge)
        self.assertIn("**compile (warm) vs LLVM -O2:** not measured  ·  **vs -O3:** not measured",
                      badge)
        self.assertIn("aarch64, `aarch64-apple-darwin`)", badge.splitlines()[0])
        self.assertIn("| G5 coverage (M6) | intent-to-treat coverage >= 80% | fail |", badge)
        measured = "\n".join(ratchet._badge_block([ratchet.condense(results(), "m.json")]))
        self.assertRegex(measured, r"\*\*compile \(warm\) vs LLVM -O2:\*\* [0-9.]+x  ·  "
                                   r"\*\*vs -O3:\*\* [0-9.]+x")

    def test_predicates_are_preregistered_versioned_and_badged(self):
        gates = json.loads(ratchet.GATES.read_text())
        self.assertEqual(gates["version"], 4)
        self.assertEqual([r["version"] for r in gates["revisions"]], [1, 2, 3, 4])
        self.assertEqual(gates["results_schema"], "trust-cg-bench-v2")
        for name in ("S1_size_linked_parity_vs_O3", "S2_size_linked_SB_vs_O3",
                     "S3_size_emitted_parity_vs_O3", "S4_size_emitted_SB_vs_O3",
                     "R1_program_rss_no_resolved_loss", "R2_compile_rss_parity_vs_O2"):
            self.assertIn(name, gates["gates"])
        self.assertIn("resource_measurement_complete == true", gates["eligibility"])
        ratchet._assert_badge_matches_contract()
        row = ratchet.condense(results(), "sample.json")
        self.assertEqual(row["gates_version"], 4)
        self.assertEqual(row["ledger_row_schema"], ratchet.LEDGER_ROW_SCHEMA)
        self.assertEqual(row["n_rss"], N_RSS)
        self.assertTrue(row["evidence"])
        for name in ("S1_size_linked_parity_vs_O3", "S2_size_linked_SB_vs_O3",
                     "S3_size_emitted_parity_vs_O3", "S4_size_emitted_SB_vs_O3",
                     "R1_program_rss_no_resolved_loss"):
            self.assertIs(row["gates"][name], True, name)
        # 200 MiB bridge vs 200 MiB -O2: parity, and nothing is floor-bound.
        self.assertIs(row["gates"]["R2_compile_rss_parity_vs_O2"], True)
        self.assertEqual(row["compile_rss_geomean_vs_llvm_o2"], 1.0)

    def test_existing_gate_predicates_are_unchanged(self):
        gates = json.loads(ratchet.GATES.read_text())["gates"]
        self.assertEqual(gates["G1a_scalar_runtime_M2"]["predicate"],
                         ".aggregates.scalar_runtime_geomean_vs_llvm_o3 != null and "
                         ".aggregates.scalar_runtime_geomean_vs_llvm_o3 <= 1.30")
        self.assertEqual(gates["G2_M1_compile_warm_vs_O2"]["predicate"],
                         ".aggregates.compile_warm_geomean_vs_llvm_o2 != null and "
                         ".aggregates.compile_warm_geomean_vs_llvm_o2 <= 1.00 and "
                         ".provenance.cache.mode == \"warm\"")
        self.assertEqual(gates["G1c_GATE_SB_M6"]["predicate"],
                         ".aggregates.runtime_geomean_vs_llvm_o3 != null and "
                         ".aggregates.runtime_geomean_vs_llvm_o3 < 1.00 and "
                         ".aggregates.runtime_worst_vs_llvm_o3 <= 1.50 and "
                         ".aggregates.coverage_pct >= 80")

    def test_a_missing_reading_nulls_the_aggregate_and_the_evidence(self):
        for field, lane in (("peak_rss_bytes", "bridge"), ("compile_peak_rss_bytes", "llvm_o2"),
                            ("size_bytes", "llvm_o3")):
            data = results()
            data["programs"][P[3]][field][lane] = None
            restamp(data)
            with self.subTest(field=field, lane=lane):
                aggregates = data["aggregates"]
                self.assertFalse(aggregates["resource_measurement_complete"])
                self.assertEqual(aggregates["resource_missing"], [f"{P[3]}.{field}.{lane}"])
                self.assertEqual(ratchet.validate(data, "sample"), [])  # consistent, recordable
                row = ratchet.condense(data, "sample.json")
                self.assertFalse(row["evidence"])
        data = results()
        data["programs"][P[3]]["peak_rss_bytes"]["bridge"] = None
        restamp(data)
        self.assertIsNone(data["aggregates"]["rss_geomean_vs_llvm_o3"])
        self.assertIsNone(data["aggregates"]["program_rss_resolved_loss_count"])
        self.assertIsNone(ratchet.condense(data, "x.json")["gates"]["R1_program_rss_no_resolved_loss"])
        # The other resource aggregates are still complete over every MATCH row.
        self.assertEqual(data["aggregates"]["size_geomean_vs_llvm_o3"], 1.0)

    def test_nonpositive_or_non_integer_readings_are_missing(self):
        for value in (0, -1, 1.5, True, "40"):
            data = results()
            data["programs"][P[0]]["peak_rss_bytes"]["llvm_o3"] = value
            restamp(data)
            with self.subTest(value=value):
                self.assertIsNone(data["aggregates"]["rss_geomean_vs_llvm_o3"])

    def test_stamped_aggregates_must_match_the_table(self):
        for key, value in (("rss_geomean_vs_llvm_o3", 0.5), ("resource_missing", []),
                           ("program_rss_resolved_loss_count", 0),
                           ("runtime_geomean_vs_llvm_o3", 0.8), ("runtime_worst_vs_llvm_o3", 0.8),
                           ("compile_warm_geomean_vs_llvm_o2", 0.5), ("coverage_pct", 90.0),
                           ("size_geomean_vs_llvm_o3", 1.0)):
            data = results()
            data["programs"][P[5]]["peak_rss_bytes"]["bridge"] = 80 * MIB  # a resolved loss
            data["programs"][P[6]]["size_bytes"]["bridge"] = 3_000_056
            restamp(data)
            data["aggregates"][key] = value
            if key == "resource_missing":
                data["programs"][P[6]]["size_bytes"]["bridge"] = None
            with self.subTest(key=key):
                problems = ratchet.validate(data, "sample")
                self.assertTrue(any("disagrees with its recomputation" in p for p in problems), problems)
        # probe2 B: rows with no runtime samples cannot carry a stamped geomean.
        data = results()
        for row in data["programs"].values():
            del row["run"]
        self.assertEqual(data["aggregates"]["runtime_geomean_vs_llvm_o3"], 0.9)
        problems = ratchet.validate(data, "s")
        self.assertTrue(any("aggregates.runtime_geomean_vs_llvm_o3" in p for p in problems), problems)
        restamp(data)
        self.assertIsNone(data["aggregates"]["runtime_geomean_vs_llvm_o3"])
        self.assertFalse(ratchet.condense(data, "s.json")["evidence"])  # missing samples
        data = results()
        del data["programs"][P[1]]
        self.assertTrue(any("aggregates.total_programs" in p for p in ratchet.validate(data, "s")))

    def test_r1_passes_only_when_every_comparison_is_resolved(self):
        bound = 2 * FLOOR
        table = {
            "both_at_floor": program(rss=(FLOOR, FLOOR + 4096)),          # parity unresolved
            "above_floor_bridge": program(rss=(FLOOR, FLOOR + MIB)),      # +10%: a loss
            "doubled_at_bound": program(rss=(FLOOR, bound)),              # 2x: a loss
            "within_band": program(rss=(60 * MIB, 62 * MIB)),              # +3.3%: parity band
            "beyond_band": program(rss=(60 * MIB, 64 * MIB)),              # +6.7%: loss
            "win": program(rss=(60 * MIB, 30 * MIB)),
        }
        agg = ratchet_gates.resource_aggregates(table, CROSS_CHECK)
        self.assertEqual(agg["rss_floor_bound_bytes"], bound)
        self.assertEqual(agg["program_rss_floor_bound_count"], 3)
        self.assertEqual(agg["program_rss_resolved_losses"],
                         ["above_floor_bridge", "beyond_band", "doubled_at_bound"])
        self.assertEqual(agg["program_rss_resolved_loss_count"], 3)

        def r1(rows):
            data = results()
            data["programs"] = rows
            restamp(data)
            return ratchet.condense(data, "x.json")["gates"]["R1_program_rss_no_resolved_loss"]

        names = [P[index] for index in range(18)]
        # Every comparison at the floor, none a loss: unmeasured.
        self.assertIsNone(r1({n: program(rss=(FLOOR, FLOOR)) for n in names}))
        # One resolved comparison and the rest at the floor (crafted/08): still
        # unmeasured — a program at the floor is not a measured parity.
        rows = {n: program(rss=(FLOOR, int(FLOOR * 1.04))) for n in names}
        rows[P[0]] = program(rss=(40 * MIB, 40 * MIB))
        self.assertIsNone(r1(rows))
        # Every comparison resolved and none a loss: PASS.
        self.assertIs(r1({n: program(rss=(40 * MIB, 41 * MIB)) for n in names}), True)
        # A loss fails R1 even when every other comparison is at the floor.
        rows = {n: program(rss=(FLOOR, FLOOR)) for n in names}
        rows[P[0]] = program(rss=(FLOOR, bound))
        self.assertIs(r1(rows), False)
        # A bridge reading only 4% over the floor is within the band: no loss.
        self.assertEqual(ratchet_gates.resource_aggregates(
            {"x": program(rss=(FLOOR, int(FLOOR * 1.04)))}, CROSS_CHECK)["program_rss_resolved_losses"], [])
        # Compiler readings at or below the bound are counted (R2 then fails).
        low = ratchet_gates.resource_aggregates(
            {"x": program(compile_rss=(bound, 200 * MIB, 200 * MIB))}, CROSS_CHECK)
        self.assertEqual(low["compile_rss_floor_bound_count"], 1)
        data = results()
        data["programs"][P[0]]["compile_peak_rss_bytes"]["llvm_o2"] = bound
        restamp(data)
        self.assertIs(ratchet.condense(data, "x.json")["gates"]["R2_compile_rss_parity_vs_O2"], False)

    def test_an_uncalibrated_sampler_qualifies_no_rss_reading(self):
        for change in ({"agree": False}, {"rusage_covers_allocation": False},
                       {"sampler_floor_bytes": None}, {"sampler_floor_bytes": 0}):
            data = results()
            data["provenance"]["rss_sampling"]["cross_check"].update(change)
            restamp(data)
            with self.subTest(change=change):
                self.assertIsNone(data["aggregates"]["rss_sampler_floor_bytes"])
                self.assertIsNone(data["aggregates"]["program_rss_resolved_loss_count"])
                self.assertEqual(ratchet.validate(data, "sample"), [])
                self.assertFalse(ratchet.condense(data, "x.json")["evidence"])
        # No /usr/bin/time at all: the cross-check is absent, not failed.
        data = results()
        data["provenance"]["rss_sampling"]["cross_check"].update(agree=None, time_wrapper_present=False)
        restamp(data)
        self.assertTrue(ratchet.condense(data, "x.json")["evidence"])
        # A present /usr/bin/time whose output was unusable is a failed cross-check.
        for present in (True, None):
            data = results()
            data["provenance"]["rss_sampling"]["cross_check"].update(agree=None,
                                                                    time_wrapper_present=present)
            restamp(data)
            with self.subTest(time_wrapper_present=present):
                self.assertIsNone(data["aggregates"]["rss_sampler_floor_bytes"])
                self.assertFalse(ratchet.condense(data, "x.json")["evidence"])

    def test_no_match_rows_measure_nothing(self):
        data = results()
        for row in data["programs"].values():
            row["verdict"] = "INCOMPLETE"
        data["aggregates"].update(match_count=0, incomplete_count=18, coverage_pct=0.0,
                                  runtime_geomean_vs_llvm_o3=None, runtime_worst_vs_llvm_o3=None,
                                  compile_warm_geomean_vs_llvm_o2=None)
        restamp(data)
        self.assertEqual(ratchet.validate(data, "sample"), [])
        row = ratchet.condense(data, "x.json")
        for name in ("S1_size_linked_parity_vs_O3", "R1_program_rss_no_resolved_loss",
                     "R2_compile_rss_parity_vs_O2"):
            self.assertIsNone(row["gates"][name], name)  # unmeasured, never a vacuous pass

    def test_size_and_memory_can_regress(self):
        baseline = ratchet.condense(results(), "baseline.json")
        cases = {
            "size_geomean_vs_llvm_o3": (1.04, 1.06),
            "rss_geomean_vs_llvm_o3": (1.09, 1.11),
            "compile_rss_geomean_vs_llvm_o2": (1.09, 1.11),
            "program_rss_resolved_loss_count": (0, 1),
        }
        for metric, (tolerated, regressed) in cases.items():
            for value, red in ((tolerated, False), (regressed, True)):
                row = ratchet.condense(results(), "current.json")
                row[metric] = value
                with self.subTest(metric=metric, value=value):
                    fails = ratchet.ratchet_check(row, [baseline], self.thresholds())
                    self.assertEqual(bool(fails), red, fails)
                    if red:
                        self.assertTrue(any(metric in f for f in fails))

    def test_a_metric_the_baseline_measured_cannot_go_missing(self):
        """Built through the real path: one missing reading in the table nulls
        the aggregate through the shared aggregation, the row condenses as
        non-evidence, and the ratchet still reports the metric missing (probe2 A)."""
        baseline = ratchet.condense(results(), "baseline.json")
        self.assertTrue(baseline["evidence"])

        def drop_size(data):
            data["programs"][P[7]]["size_bytes"]["bridge"] = None

        def drop_program_rss(data):
            data["programs"][P[7]]["peak_rss_bytes"]["bridge"] = None

        def drop_compile_rss(data):
            data["programs"][P[7]]["compile_peak_rss_bytes"]["llvm_o2"] = None

        def drop_runtime(data):
            data["programs"][P[7]]["run"]["bridge"]["times_s"] = []

        cases = ((drop_size, ["size_geomean_vs_llvm_o3"]),
                 (drop_program_rss, ["rss_geomean_vs_llvm_o3", "program_rss_resolved_loss_count"]),
                 (drop_compile_rss, ["compile_rss_geomean_vs_llvm_o2"]),
                 (drop_runtime, ["runtime_geomean_vs_llvm_o3"]))
        for drop, metrics in cases:
            data = results()
            drop(data)
            restamp(data)
            with self.subTest(drop=drop.__name__):
                self.assertEqual(ratchet.validate(data, "current"), [])
                row = ratchet.condense(data, "current.json")
                self.assertFalse(row["evidence"])
                fails = ratchet.ratchet_check(row, [baseline], self.thresholds())
                for metric in metrics:
                    self.assertTrue(any(f.startswith(metric) and "not measured" in f for f in fails),
                                    (metric, fails))
        # Baselines that never measured RSS (every committed Linux row) do not block.
        legacy = dict(baseline, source_results="legacy.json")
        for metric in ("rss_geomean_vs_llvm_o3", "compile_rss_geomean_vs_llvm_o2",
                       "program_rss_resolved_loss_count", "size_geomean_vs_llvm_o3"):
            legacy[metric] = None
        row = ratchet.condense(results(), "current.json")
        self.assertEqual(ratchet.ratchet_check(row, [legacy], self.thresholds()), [])

    def test_ineligible_rows_are_still_regression_checked(self):
        """crafted/02, 03, 04, 16: a new ineligibility condition must not exempt a
        1.5x runtime regression from the ratchet."""
        baseline = ratchet.condense(results(), "baseline.json")

        def no_checker(d):
            d["provenance"]["proof_checker"]["candidates"] = []

        def unrunnable_checker(d):
            d["provenance"]["proof_checker"]["candidates"][0]["runs"] = False

        def degraded(d):
            d["provenance"]["proof_checker_degraded"] = ["p00:O3"]

        def null_rss(d):
            d["programs"][P[3]]["peak_rss_bytes"]["bridge"] = None

        def time_unusable(d):
            d["provenance"]["rss_sampling"]["cross_check"].update(agree=None, time_wrapper_present=True)

        def benign_knob(d):
            d["provenance"]["bridge_cg_args"] = ["time"]

        def loaded(d):
            d["provenance"].update(quiet=False, load_status="LOADED")

        for change in (no_checker, unrunnable_checker, degraded, null_rss, time_unusable,
                       benign_knob, loaded):
            data = results()
            for row in data["programs"].values():
                row["run"]["bridge"] = lane([1.5] * 5)
            change(data)
            restamp(data)
            with self.subTest(change=change.__name__):
                self.assertEqual(ratchet.validate(data, "current"), [])
                row = ratchet.condense(data, "current.json")
                self.assertFalse(row["evidence"])
                fails = ratchet.ratchet_check(row, [baseline], self.thresholds())
                self.assertTrue(any(f.startswith("runtime_geomean_vs_llvm_o3") and "regression" in f
                                    for f in fails), fails)

    def test_ineligible_regression_exits_red_from_the_command_line(self):
        data = linux_legacy(results())
        for row in data["programs"].values():
            row["run"]["bridge"] = lane([1.5] * 5)
        data["provenance"]["proof_checker"]["candidates"] = []
        restamp(data)
        with tempfile.TemporaryDirectory(prefix="trust-cg-ratchet-") as temporary:
            path = Path(temporary) / "regressed.json"
            path.write_text(json.dumps(data), encoding="utf-8")
            result = subprocess.run([sys.executable, str(ROOT / "scripts/check_perf_ratchet.py"),
                                     str(path)], capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("RED: runtime_geomean_vs_llvm_o3", result.stderr)

    def run_ratchet(self, data, *extra):
        with tempfile.TemporaryDirectory(prefix="trust-cg-ratchet-") as temporary:
            path = Path(temporary) / "results.json"
            path.write_text(json.dumps(data), encoding="utf-8")
            return subprocess.run([sys.executable, str(ROOT / "scripts/check_perf_ratchet.py"),
                                   *extra, str(path)], capture_output=True, text=True, check=False)

    def test_runs_that_are_not_like_with_like_are_inconclusive(self):
        """Round-2 b1/b2: a loaded single-program --progs run and an n=1 run are not
        compared with 18-program contract-N baselines: INCONCLUSIVE (exit 2), not
        a false RED; a stale file under --require-current is NOT CURRENT first."""
        subset = linux_legacy(results())
        subset["programs"] = {P[0]: program(runtime=(1.0, 1.2))}
        subset["provenance"].update(quiet=False, load_status="LOADED")
        restamp(subset)
        small_n = linux_legacy(results())
        small_n["provenance"].update(n_compile=1, n_run=1)
        for row in small_n["programs"].values():
            row["run"] = {"llvm_o3": lane([1.0]), "bridge": lane([1.12])}
        restamp(small_n)
        for name, data in (("subset", subset), ("small_n", small_n)):
            with self.subTest(case=name):
                self.assertEqual(ratchet.validate(data, name), [])
                row = ratchet.condense(data, f"{name}.json")
                self.assertIsNotNone(ratchet.comparability_problem(row))
                self.assertEqual(ratchet.ratchet_check(row, ratchet.read_ledger(), self.thresholds()), [])
                result = self.run_ratchet(data)
                self.assertEqual(result.returncode, ratchet.INCONCLUSIVE_EXIT, result.stdout + result.stderr)
                self.assertIn("INCONCLUSIVE", result.stderr)
                self.assertNotIn("RED", result.stderr)
                result = self.run_ratchet(data, "--require-current")
                self.assertEqual(result.returncode, ratchet.NOT_CURRENT_EXIT, result.stdout + result.stderr)
                self.assertIn("is not HEAD", result.stderr)
                self.assertNotIn("RED", result.stderr)
        # A genuine full-corpus, contract-N regression stays RED, loaded or not.
        full = linux_legacy(results())
        full["provenance"].update(quiet=False, load_status="LOADED")
        for row in full["programs"].values():
            row["run"]["bridge"] = lane([1.5] * 5)
        restamp(full)
        result = self.run_ratchet(full)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("RED: runtime_geomean_vs_llvm_o3", result.stderr)
        # ...but under --require-current a stale file is NOT CURRENT before any verdict.
        result = self.run_ratchet(full, "--require-current")
        self.assertEqual(result.returncode, ratchet.NOT_CURRENT_EXIT, result.stdout + result.stderr)

    def test_a_subset_run_is_never_evidence_or_a_baseline(self):
        """Round-2 probe_r2b: a quiet --progs subset once counted as evidence and,
        appended, became the best baseline for every later full run."""
        subset = results()
        subset["programs"] = {P[0]: program(runtime=(1.0, 0.5))}
        restamp(subset)
        row = ratchet.condense(subset, "subset.json")
        self.assertFalse(row["evidence"])
        self.assertFalse(row["corpus_complete"])
        self.assertFalse(ratchet_gates.evidence_eligible(
            subset, json.loads(ratchet.GATES.read_text())["eligibility"]))
        full = results()
        for data_row in full["programs"].values():
            data_row["run"]["bridge"] = lane([0.83] * 5)
        restamp(full)
        full_row = ratchet.condense(full, "full.json")
        self.assertTrue(full_row["evidence"])
        # Even a subset row wrongly marked evidence is not the same program set.
        forged = dict(row, evidence=True)
        self.assertEqual(ratchet.ratchet_check(full_row, [forged], self.thresholds()), [])
        # A differently sized corpus is not the same set either (legacy rows: by count).
        legacy = dict(full_row, source_results="legacy.json", runtime_geomean_vs_llvm_o3=0.5,
                      total_programs=8)
        legacy.pop("program_set_sha256")
        self.assertEqual(ratchet.ratchet_check(full_row, [legacy], self.thresholds()), [])
        legacy["total_programs"] = 18
        self.assertTrue(ratchet.ratchet_check(full_row, [legacy], self.thresholds()))

    def test_coverage_is_compared_from_counts_not_rounded_stamps(self):
        """Round-2: an identical 16/18 against a legacy row stamped 88.9 read as a drop."""
        new = results()
        for name in P[:2]:
            new["programs"][name]["verdict"] = "INCOMPLETE"
        restamp(new)
        row = ratchet.condense(new, "new.json")
        legacy = dict(row, source_results="legacy.json", coverage_pct=88.9, evidence=True)
        legacy.pop("program_set_sha256")
        self.assertEqual(ratchet.ratchet_check(row, [legacy], self.thresholds()), [])
        better = dict(legacy, match_count=17, coverage_pct=94.4, incomplete_count=1)
        fails = ratchet.ratchet_check(row, [better], self.thresholds())
        self.assertTrue(any(f.startswith("coverage_pct: 88.9% < best committed 94.4%") for f in fails),
                        fails)

    def test_rss_baselines_come_only_from_rows_of_the_version_that_introduced_rss(self):
        """Round-2 probe_r2c: the v1 Darwin row (0.995, /usr/bin/time -l) was an RSS
        baseline for v2 rows. A metric a version introduced or redefined uses only
        baselines of that version or later: version 3 made peak RSS a median of
        N samples, so neither a v1 nor a single-sample v2 row is its baseline."""
        current = results()
        for data_row in current["programs"].values():
            data_row["peak_rss_bytes"] = {"llvm_o3": 40 * MIB, "bridge": 46 * MIB}
        restamp(current)
        row = ratchet.condense(current, "v3.json")
        v1 = dict(ratchet.condense(results(), "v1.json"), rss_geomean_vs_llvm_o3=0.995,
                  compile_rss_geomean_vs_llvm_o2=0.9, program_rss_resolved_loss_count=0)
        v1.pop("gates_version")
        self.assertEqual(ratchet.ratchet_check(row, [v1], self.thresholds()), [])
        v2 = dict(v1, gates_version=2, source_results="v2-baseline.json")
        self.assertEqual(ratchet.ratchet_check(row, [v2], self.thresholds()), [])
        v3 = dict(v1, gates_version=3, source_results="v3-baseline.json")
        fails = ratchet.ratchet_check(row, [v3], self.thresholds())
        self.assertTrue(any(f.startswith("rss_geomean_vs_llvm_o3") for f in fails), fails)
        # The version-1 row is still a baseline for metrics whose method did not change.
        slower = results()
        for data_row in slower["programs"].values():
            data_row["run"]["bridge"] = lane([1.5] * 5)
        restamp(slower)
        fails = ratchet.ratchet_check(ratchet.condense(slower, "slow.json"), [v1], self.thresholds())
        self.assertTrue(any(f.startswith("runtime_geomean_vs_llvm_o3") for f in fails), fails)

    def test_stamps_agree_within_a_relative_tolerance(self):
        """A stamp computed with another platform's libm may differ in the last
        bits; it is accepted within 1e-12 relative, and refused beyond it."""
        for scale, accepted in ((1 + 1e-15, True), (1 + 1e-13, True), (1 + 1e-9, False)):
            data = results()
            data["aggregates"]["size_geomean_vs_llvm_o3"] *= scale
            data["aggregates"]["by_category"]["scalar"]["runtime_geomean_vs_llvm_o3"] *= scale
            with self.subTest(scale=scale):
                problems = ratchet.validate(data, "s")
                self.assertEqual(problems == [], accepted, problems)
        self.assertTrue(ratchet_gates.same_value(0.9, 0.9 * (1 + 1e-14)))
        self.assertFalse(ratchet_gates.same_value(True, 1))
        self.assertFalse(ratchet_gates.same_value(1, 2))
        self.assertFalse(ratchet_gates.same_value(float("nan"), float("nan")))
        self.assertFalse(ratchet_gates.same_value(0.0, 1e-300))
        self.assertFalse(ratchet_gates.same_value([1.0], [1.0, 2.0]))

    def corpus(self, names):
        """Patch the contract corpus (progs/manifest.json) to NAMES for one test."""
        temporary = tempfile.TemporaryDirectory(prefix="trust-cg-manifest-")
        self.addCleanup(temporary.cleanup)
        manifest = Path(temporary.name) / "manifest.json"
        manifest.write_text(json.dumps({"programs": {name: {} for name in names}}), encoding="utf-8")
        patcher = mock.patch.object(ratchet_gates, "MANIFEST", manifest)
        patcher.start()
        self.addCleanup(patcher.stop)

    def test_rss_method_change_requires_an_eligible_explicit_lineage(self):
        old = ratchet.condense(results(), "old.json")
        data = results()
        data["provenance"]["rss_sampling"]["method"] = "native Linux rusage v1"
        code, written, _, messages = self.run_main([old], data, "--append")
        self.assertEqual(code, 2, messages)
        self.assertEqual(written, [old])
        self.assertIn("RSS sampling method changed", messages)
        code, written, _, messages = self.run_main(
            [old], data, "--append", "--new-lineage", "Native sampler lowers the real fork floor")
        self.assertEqual(code, 0, messages)
        self.assertEqual(written[-1]["new_lineage"]["rss_method"], "native Linux rusage v1")
        loaded = copy.deepcopy(data)
        loaded["provenance"].update(quiet=False, load_status="LOADED")
        code, written, _, _ = self.run_main([old], loaded, "--append", "--new-lineage", "loaded")
        self.assertEqual(code, 2)
        self.assertEqual(written, [old])

    def test_method_change_preserves_other_regressions_and_new_method_rss_regressions(self):
        old = ratchet.condense(results(), "old.json")
        data = results()
        data["provenance"]["rss_sampling"]["method"] = "native Linux rusage v1"
        native = ratchet.condense(data, "native.json")
        for row in data["programs"].values():
            row["run"]["bridge"] = lane([1.5] * 5)
        restamp(data)
        code, written, _, messages = self.run_main([old], data, "--append", "--new-lineage", "native")
        self.assertEqual(code, 1, messages)
        self.assertIn("runtime_geomean_vs_llvm_o3", messages)
        self.assertEqual(written, [old])
        # Old-method RSS cannot judge the new method, but the retained native
        # baseline must still catch a genuine new RSS loss.
        for row in data["programs"].values():
            row["run"]["bridge"] = lane([0.9] * 5)
            row["peak_rss_bytes"]["bridge"] = 80 * MIB
        restamp(data)
        code, written, _, messages = self.run_main([old, native], data, "--append")
        self.assertEqual(code, 1, messages)
        self.assertIn("rss_geomean_vs_llvm_o3", messages)
        self.assertEqual(written, [old, native])

    def test_shared_programs_do_not_compare_different_rss_methods(self):
        data = results()
        old = ratchet.condense(data, "old.json")
        data["provenance"]["rss_sampling"]["method"] = "native Linux rusage v1"
        for row in data["programs"].values():
            row["peak_rss_bytes"]["bridge"] = 80 * MIB
        restamp(data)
        row = ratchet.condense(data, "native.json")
        self.assertEqual(ratchet.shared_program_regressions(row, [old], self.thresholds()), [])
        old["rss_sampling"]["method"] = "native Linux rusage v1"
        self.assertTrue(ratchet.shared_program_regressions(row, [old], self.thresholds()))

    def test_native_method_id_changes_cannot_inherit_a_prior_rss_baseline(self):
        data = results()
        data["provenance"]["rss_sampling"].update(method="native rusage", method_id="linux-native-rusage-v1")
        old = ratchet.condense(data, "native-v1.json")
        data["provenance"]["rss_sampling"]["method_id"] = "linux-native-rusage-v2"
        row = ratchet.condense(data, "native-v2.json")
        self.assertIsNotNone(ratchet.lineage_problem(row, [old]))
        # Changing just the executable identity cannot clear a method's RSS
        # regression baseline or demand another baseline declaration.
        row["rss_sampling"]["method_id"] = "linux-native-rusage-v1"
        row["rss_sampling"]["sampler_identity"] = {"binary_sha256": "ab" * 32}
        self.assertIsNone(ratchet.lineage_problem(row, [old]))

    def test_unchanged_python_method_keeps_legacy_darwin_baselines(self):
        data = results()
        data["provenance"]["rss_sampling"]["method"] = "single-child Python rusage"
        old = ratchet.condense(data, "legacy-python.json")
        data["provenance"]["rss_sampling"]["method_id"] = "python-rusage-v1"
        row = ratchet.condense(data, "current-python.json")
        self.assertIsNone(ratchet.lineage_problem(row, [old]))

    def corpus_run(self, names, runtime=0.9):
        data = linux_legacy(results())
        data["programs"] = {name: program(runtime=(1.0, runtime)) for name in names}
        return restamp(data)

    def run_main(self, ledger_rows, data, *argv, name="results.json"):
        """check_perf_ratchet.main() in process, on a temporary ledger (the
        committed ratchet/ledger.jsonl and LEDGER.md are never touched)."""
        with tempfile.TemporaryDirectory(prefix="trust-cg-ledger-") as temporary:
            ledger = Path(temporary) / "ledger.jsonl"
            ledger.write_text("".join(json.dumps(r, sort_keys=True) + "\n" for r in ledger_rows))
            view = Path(temporary) / "LEDGER.md"
            path = Path(temporary) / name
            path.write_text(json.dumps(data), encoding="utf-8")
            with mock.patch.object(ratchet, "LEDGER", ledger), mock.patch.object(ratchet, "LEDGER_MD", view), \
                    mock.patch.object(ratchet, "REPO", Path(temporary)), \
                    mock.patch.object(sys, "argv", ["check_perf_ratchet.py", *argv, str(path)]), \
                    mock.patch("sys.stdout"), mock.patch("sys.stderr") as stderr:
                with self.assertRaises(SystemExit) as stop:
                    ratchet.main()
            written = [json.loads(line) for line in ledger.read_text().splitlines() if line.strip()]
            rendered = view.read_text() if view.exists() else ""
        messages = "".join(str(c.args[0]) for c in stderr.write.call_args_list)
        return stop.exception.code, written, rendered, messages

    def test_a_changed_corpus_never_passes_silently(self):
        """Round-3: adding a 19th program (or removing one) made every baseline a
        different set, and an 18-program lineage then skipped all regression
        checks: a 1.5x (or 3x) regression printed SKIPPED and exited 0."""
        base = linux_legacy(results())
        new_format = ratchet.condense(base, "baseline-v2.json")
        legacy = {k: v for k, v in new_format.items()
                  if k not in ("program_set_sha256", "corpus_complete", "program_ratios", "gates_version")}
        legacy["source_results"] = "baseline-v1.json"
        added, removed = P + ["z9_added"], P[:-1]
        for label, names in (("added", added), ("removed", removed)):
            self.corpus(names)
            for ratio in (1.5, 3.0):
                row = ratchet.condense(self.corpus_run(names, ratio), f"{label}.json")
                self.assertTrue(row["evidence"] and row["corpus_complete"])
                with self.subTest(change=label, ratio=ratio, baseline="per-program"):
                    fails = ratchet.ratchet_check(row, [new_format], self.thresholds())
                    shared = len(set(names) & set(P))
                    self.assertTrue(any(f.startswith("runtime_geomean_vs_llvm_o3 over the "
                                                     f"{shared} programs shared") for f in fails), fails)
                with self.subTest(change=label, ratio=ratio, baseline="legacy"):
                    self.assertEqual(ratchet.ratchet_check(row, [legacy], self.thresholds()), [])
                    self.assertIn("program set changed", ratchet.lineage_problem(row, [legacy]))
            clean = ratchet.condense(self.corpus_run(names, 0.9), f"{label}-clean.json")
            with self.subTest(change=label, regression=False):
                self.assertEqual(ratchet.ratchet_check(clean, [new_format, legacy], self.thresholds()), [])
                self.assertIsNotNone(ratchet.lineage_problem(clean, [new_format, legacy]))
        # A host/target with no evidence rows at all keeps the pre-existing SKIPPED.
        other = dict(new_format, host_model="another-cpu", legacy_host_model="another-box")
        self.assertIsNone(ratchet.lineage_problem(clean, [other]))

    def test_a_changed_corpus_through_the_command_line(self):
        base = linux_legacy(results())
        legacy = {k: v for k, v in ratchet.condense(base, "baseline-v1.json").items()
                  if k not in ("program_set_sha256", "corpus_complete", "program_ratios", "gates_version")}
        names = P + ["z9_added"]
        self.corpus(names)
        regressed = self.corpus_run(names, 1.5)
        # Legacy baselines cannot compare shared programs: INCONCLUSIVE, never 0, never appended.
        code, written, _, messages = self.run_main([legacy], regressed, "--append")
        self.assertEqual(code, ratchet.INCONCLUSIVE_EXIT, messages)
        self.assertIn("program set changed", messages)
        self.assertEqual(len(written), 1)
        # A new lineage is appended only with an explicit, recorded reason ...
        code, _, _, messages = self.run_main([legacy], regressed, "--new-lineage", "z9 added")
        self.assertEqual(code, 2, messages)  # --new-lineage needs --append
        code, _, _, _ = self.run_main([legacy], regressed, "--append", "--new-lineage", "  ")
        self.assertEqual(code, 2)
        clean = self.corpus_run(names, 0.9)
        code, written, rendered, messages = self.run_main(
            [legacy], clean, "--append", "--new-lineage", "BENCH-3: z9_added joins the corpus",
            name="declared.json")
        self.assertEqual(code, 0, messages)
        self.assertEqual(len(written), 2)
        declared = written[-1]
        self.assertEqual(declared["new_lineage"]["reason"], "BENCH-3: z9_added joins the corpus")
        self.assertEqual(declared["new_lineage"]["replaces_program_sets"], ["legacy:18-programs"])
        self.assertIs(declared["new_lineage"]["shared_programs_compared"], False)
        self.assertIn("could not be checked for a regression", messages)
        self.assertIn("NEW LINEAGE: BENCH-3: z9_added joins the corpus", rendered)
        # ... after which the new set's regressions are RED against its own lineage.
        code, _, _, messages = self.run_main(written, regressed, name="later.json")
        self.assertEqual(code, 1, messages)
        self.assertIn("RED: runtime_geomean_vs_llvm_o3", messages)
        # Declaring a lineage where none changed is refused.
        self.corpus(P)
        code, _, _, messages = self.run_main([legacy], linux_legacy(results()), "--append",
                                             "--new-lineage", "nothing changed")
        self.assertEqual(code, 2, messages)

    def test_only_an_evidence_row_can_declare_a_lineage(self):
        """Round-4 sequence C: a LOADED row declared the lineage, an eligible 3x
        row then passed and became the set's first evidence baseline. The
        declaring row must itself be evidence; a non-evidence declaration
        (even one already in a ledger) settles nothing."""
        base = linux_legacy(results())
        legacy = {k: v for k, v in ratchet.condense(base, "baseline-v1.json").items()
                  if k not in ("program_set_sha256", "corpus_complete", "program_ratios", "gates_version")}
        names = P + ["p9_new_kernel"]
        self.corpus(names)

        def run19(ratio, loaded=False):
            data = self.corpus_run(names, ratio)
            if loaded:
                data["provenance"].update(quiet=False, load_status="LOADED")
                data["headline_eligible"] = False
            return data

        # Sequence C.
        code, written, _, messages = self.run_main(
            [legacy], run19(0.86, loaded=True), "--append", "--new-lineage", "p9 added (BENCH-3)",
            name="c1.json")
        self.assertEqual(code, 2, messages)
        self.assertIn("needs an eligible EVIDENCE row", messages)
        self.assertEqual(written, [legacy])
        for step, extra in (("c2.json", ()), ("c3.json", ("--append",))):
            code, written, _, messages = self.run_main([legacy], run19(3.0), *extra, name=step)
            with self.subTest(step=step):
                self.assertEqual(code, ratchet.INCONCLUSIVE_EXIT, messages)
                self.assertEqual(written, [legacy])
        # A non-evidence declaration already in a ledger (as the refuted version
        # could append) does not settle the lineage either.
        stale = ratchet.condense(run19(0.86, loaded=True), "old-declaration.json")
        stale["new_lineage"] = {"reason": "p9 added", "replaces_program_sets": ["legacy:18-programs"]}
        self.assertFalse(stale["evidence"])
        code, written, _, messages = self.run_main([legacy, stale], run19(3.0), "--append",
                                                   name="c4.json")
        self.assertEqual(code, ratchet.INCONCLUSIVE_EXIT, messages)
        self.assertEqual(len(written), 2)
        # Sequence D: an eligible row declares it, and becomes the baseline a
        # later 1.5x regression is RED against.
        code, written, rendered, messages = self.run_main(
            [legacy, stale], run19(0.86), "--append", "--new-lineage", "p9 added", name="d1.json")
        self.assertEqual(code, 0, messages)
        self.assertTrue(written[-1]["evidence"])
        self.assertEqual(written[-1]["new_lineage"]["reason"], "p9 added")
        code, _, _, messages = self.run_main(written, run19(1.5), name="d2.json")
        self.assertEqual(code, 1, messages)
        self.assertIn("RED: runtime_geomean_vs_llvm_o3", messages)
        # A second declaration for a settled lineage is refused.
        code, _, _, messages = self.run_main(written, run19(0.86), "--append", "--new-lineage",
                                             "again", name="d3.json")
        self.assertEqual(code, 2, messages)

    def test_duplicate_keys_are_refused(self):
        """A JSON object with two same-named program rows would be read with the
        last one silently winning; the ratchet and the checker refuse it."""
        data = results()
        text = json.dumps(data)
        good = json.dumps(data["programs"][P[0]])
        bad = copy.deepcopy(data["programs"][P[0]])
        bad["run"]["bridge"] = lane([9.0] * 5)
        text = text.replace(f'"{P[0]}": {good}', f'"{P[0]}": {json.dumps(bad)}, "{P[0]}": {good}', 1)
        with tempfile.TemporaryDirectory(prefix="trust-cg-dup-") as temporary:
            path = Path(temporary) / "dup.json"
            path.write_text(text, encoding="utf-8")
            for script in ("scripts/check_perf_ratchet.py", "benchmarks/beat-llvm/contract/check_gates.py"):
                result = subprocess.run([sys.executable, str(ROOT / script), str(path)],
                                        capture_output=True, text=True, check=False)
                with self.subTest(script=script):
                    self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                    self.assertIn("duplicate keys", result.stderr)

    def test_cosmetic_identity_differences_are_normalised(self):
        baseline = ratchet.condense(linux_legacy(results()), "baseline.json")
        data = linux_legacy(results())
        for row in data["programs"].values():
            row["run"]["bridge"] = lane([1.5] * 5)
        data["provenance"]["target"] = "aarch64-unknown-linux-gnu "
        data["provenance"]["host_model"] = " spark-d5a4"
        restamp(data)
        row = ratchet.condense(data, "spaced.json")
        self.assertEqual(row["target"], "aarch64-unknown-linux-gnu")
        fails = ratchet.ratchet_check(row, [baseline], self.thresholds())
        self.assertTrue(any(f.startswith("runtime_geomean_vs_llvm_o3") for f in fails), fails)
        # A raw stored row with stray whitespace still matches too.
        spaced = dict(baseline, target="aarch64-unknown-linux-gnu  ", source_results="spaced-base.json")
        self.assertTrue(ratchet.comparable(ratchet.condense(linux_legacy(results()), "x.json"), spaced))

    def test_gates_read_the_recomputed_aggregates_not_the_stamps(self):
        """A stamp inside the 1e-12 tolerance must not flip a threshold: an exact
        size geomean just above 1.00 stamped as 1.0 still fails S2."""
        data = results()
        for index, row in enumerate(data["programs"].values()):
            row["size_bytes"] = {"llvm_o3": 10**12, "bridge": 10**12 + (1 if index == 0 else 0)}
        restamp(data)
        exact = data["aggregates"]["size_geomean_vs_llvm_o3"]
        self.assertGreater(exact, 1.0)
        data["aggregates"]["size_geomean_vs_llvm_o3"] = 1.0
        self.assertEqual(ratchet.validate(data, "s"), [])  # within the tolerance
        row = ratchet.condense(data, "s.json")
        self.assertEqual(row["size_geomean_vs_llvm_o3"], exact)
        self.assertIs(row["gates"]["S2_size_linked_SB_vs_O3"], False)
        with tempfile.TemporaryDirectory(prefix="trust-cg-gates-") as temporary:
            path = Path(temporary) / "results.json"
            path.write_text(json.dumps(data), encoding="utf-8")
            result = subprocess.run(
                [sys.executable, str(ROOT / "benchmarks/beat-llvm/contract/check_gates.py"), str(path)],
                capture_output=True, text=True, check=False)
        self.assertRegex(result.stdout, r"fail\s+S2_size_linked_SB_vs_O3")

    def test_gates_compare_exact_values_not_rounded_stamps(self):
        """crafted/11: 14 of 18 bridge binaries 200 bytes larger gives an exact
        size geomean of 1.0000187; stamped rounded to 1.0 it passed S2."""
        data = results()
        for index, row in enumerate(data["programs"].values()):
            row["size_bytes"] = {"llvm_o3": 4355384, "bridge": 4355384 + (200 if index < 14 else -100)}
        restamp(data)
        size = data["aggregates"]["size_geomean_vs_llvm_o3"]
        self.assertGreater(size, 1.0)
        self.assertEqual(round(size, 3), 1.0)
        row = ratchet.condense(data, "x.json")
        self.assertEqual(row["size_geomean_vs_llvm_o3"], size)
        self.assertIs(row["gates"]["S2_size_linked_SB_vs_O3"], False)
        self.assertIs(row["gates"]["S1_size_linked_parity_vs_O3"], True)
        # The same for the other thresholded aggregates.
        for runtime, compile_ratio, gate, expected in (
                ((1.0, 1.2996), (1.0, 0.5), "G1a_scalar_runtime_M2", True),
                ((1.0, 1.3004), (1.0, 0.5), "G1a_scalar_runtime_M2", False),
                ((1.0, 0.5), (1.0, 1.0004), "G2_M1_compile_warm_vs_O2", False),
                ((1.0, 0.9996), (1.0, 0.5), "G1c_GATE_SB_M6", True)):
            data = results()
            data["programs"] = {P[i]: program(runtime=runtime, compile=compile_ratio)
                                for i in range(18)}
            restamp(data)
            with self.subTest(gate=gate, runtime=runtime, compile=compile_ratio):
                self.assertIs(ratchet.condense(data, "x.json")["gates"][gate], expected)
        data = results()
        data["programs"][P[0]] = program(runtime=(1.0, 1.5004))
        restamp(data)
        self.assertGreater(data["aggregates"]["runtime_worst_vs_llvm_o3"], 1.5)
        self.assertIs(ratchet.condense(data, "x.json")["gates"]["G1c_GATE_SB_M6"], False)
        # Coverage is exact too; the legacy one-decimal form is still accepted on ledger rows.
        data = results()
        data["programs"][P[17]]["verdict"] = "INCOMPLETE"
        restamp(data)
        self.assertEqual(data["aggregates"]["coverage_pct"], 100.0 * 17 / 18)
        self.assertEqual(ratchet.measurement_issues(dict(data["aggregates"], coverage_pct=94.4)), [])

    def test_proof_weakening_backend_knobs_are_rejected(self):
        for knobs in (["no-proof-certs"], ["no-proof-certs=on"], ["refine-solver=0"],
                      ["time", "refine-solver=off"], ["no-proof-cache,time"], [7],
                      ["time no-proof-certs"], ["time\trefine-solver=0"], ["no-proof-certs=YES"]):
            data = results()
            data["provenance"]["bridge_cg_args"] = knobs
            with self.subTest(knobs=knobs):
                problems = ratchet.validate(data, "sample")
                self.assertTrue(any("proof-weakening" in p for p in problems), problems)
        for knobs in (["no-proof-certs=0"], ["refine-solver"], ["time"]):
            data = results()
            data["provenance"]["bridge_cg_args"] = knobs
            with self.subTest(knobs=knobs):
                self.assertEqual(ratchet.validate(data, "sample"), [])
                row = ratchet.condense(data, "x.json")
                self.assertFalse(row["evidence"])  # any knob is a diagnostic lane
                self.assertEqual(row["bridge_cg_args"], knobs)

    def test_a_resolved_loss_moving_to_another_program_is_red(self):
        def with_loss(name, source):
            data = results()
            data["programs"][name]["peak_rss_bytes"]["bridge"] = 80 * MIB
            return ratchet.condense(restamp(data), source)
        baseline = with_loss(P[1], "baseline.json")
        self.assertEqual(baseline["program_rss_resolved_losses"], [P[1]])
        same = with_loss(P[1], "same.json")
        self.assertEqual(ratchet.ratchet_check(same, [baseline], self.thresholds()), [])
        moved = with_loss(P[2], "moved.json")
        fails = ratchet.ratchet_check(moved, [baseline], self.thresholds())
        self.assertTrue(any(f"new resolved peak-RSS losses [{P[2]!r}]" in f for f in fails), fails)

    def test_results_before_the_recomputed_aggregates_are_not_current_evidence(self):
        def run(data):
            with tempfile.TemporaryDirectory(prefix="trust-cg-ratchet-") as temporary:
                path = Path(temporary) / "old.json"
                path.write_text(json.dumps(data), encoding="utf-8")
                return subprocess.run([sys.executable, str(ROOT / "scripts/check_perf_ratchet.py"),
                                       str(path)], capture_output=True, text=True, check=False)

        data = results()
        for key in ratchet_gates.RESOURCE_AGGREGATE_KEYS:
            data["aggregates"].pop(key)
        result = run(data)
        self.assertEqual(result.returncode, ratchet.NOT_CURRENT_EXIT, result.stdout + result.stderr)
        self.assertIn("predates the recomputed fail-closed aggregates", result.stderr)
        # An old-format file with a MISMATCH is still P0 (crafted/13), not "not current".
        data["programs"][P[5]]["verdict"] = "MISMATCH"
        data["aggregates"].update(match_count=17, mismatch_count=1, coverage_pct=94.4)
        result = run(data)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("mismatch_count=1", result.stderr)
        self.assertNotIn("NOT CURRENT", result.stderr)

    def test_a_row_without_a_usable_proof_checker_is_not_evidence(self):
        for checker in (None, {}, {"candidates": []}, "clean", {"candidates": None}):
            data = results()
            if checker is None:
                data["provenance"].pop("proof_checker")
            else:
                data["provenance"]["proof_checker"] = checker
            with self.subTest(checker=checker):
                self.assertFalse(ratchet.condense(data, "x.json")["evidence"])

    def test_a_degraded_proof_checker_is_not_evidence(self):
        data = results()
        data["provenance"]["proof_checker_degraded"] = ["p00:O3"]
        row = ratchet.condense(data, "x.json")
        self.assertFalse(row["evidence"])
        self.assertTrue(row["proof_checker_degraded"])

    def test_standalone_checker_reports_resource_gates(self):
        def check(data):
            with tempfile.TemporaryDirectory(prefix="trust-cg-gates-") as temporary:
                path = Path(temporary) / "results.json"
                path.write_text(json.dumps(data), encoding="utf-8")
                return subprocess.run(
                    [sys.executable, str(ROOT / "benchmarks/beat-llvm/contract/check_gates.py"), str(path)],
                    capture_output=True, text=True, check=False)

        result = check(results())
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        for name in ("S1_size_linked_parity_vs_O3", "S2_size_linked_SB_vs_O3",
                     "S3_size_emitted_parity_vs_O3", "S4_size_emitted_SB_vs_O3",
                     "R1_program_rss_no_resolved_loss", "R2_compile_rss_parity_vs_O2"):
            self.assertRegex(result.stdout, rf"PASS\s+{name}")
        # crafted/07: an unmeasured gate prints "unmeasured", never "fail".
        data = results()
        for row in data["programs"].values():
            row["peak_rss_bytes"] = {"llvm_o3": FLOOR, "bridge": FLOOR}
        restamp(data)
        result = check(data)
        self.assertRegex(result.stdout, r"unmeasured\s+R1_program_rss_no_resolved_loss")
        self.assertNotRegex(result.stdout, r"fail\s+R1_program_rss_no_resolved_loss")
        self.assertRegex(result.stdout, r"unmeasured\s+G2_M1_compile_cold_vs_O2")



class EmittedSizeAndMedianRssTests(unittest.TestCase):
    """gates.json version 3: emitted-code size (S3/S4) and median-of-N peak RSS."""

    def thresholds(self):
        return json.loads(ratchet.BASELINE.read_text())["thresholds"]

    def test_emitted_size_is_its_own_gated_aggregate(self):
        data = results()
        for name in P:
            data["programs"][name]["emitted_size_bytes"] = {"llvm_o3": 1000, "bridge": 1080}
        restamp(data)
        agg = data["aggregates"]
        self.assertAlmostEqual(agg["emitted_size_geomean_vs_llvm_o3"], 1.08, places=12)
        self.assertAlmostEqual(agg["emitted_size_worst_vs_llvm_o3"], 1.08, places=12)
        # The linked file is unchanged, so S1/S2 cannot see what S3/S4 see.
        self.assertEqual(agg["size_geomean_vs_llvm_o3"], 1.0)
        row = ratchet.condense(data, "x.json")
        self.assertIs(row["gates"]["S2_size_linked_SB_vs_O3"], True)
        self.assertIs(row["gates"]["S3_size_emitted_parity_vs_O3"], True)
        self.assertIs(row["gates"]["S4_size_emitted_SB_vs_O3"], False)
        self.assertAlmostEqual(row["program_ratios"][P[0]]["emitted_size_vs_llvm_o3"], 1.08)

    def test_a_missing_emitted_size_nulls_s3_s4_and_the_evidence(self):
        data = results()
        data["programs"][P[2]]["emitted_size_bytes"]["bridge"] = None
        restamp(data)
        self.assertIsNone(data["aggregates"]["emitted_size_geomean_vs_llvm_o3"])
        self.assertEqual(data["aggregates"]["resource_missing"],
                         [f"{P[2]}.emitted_size_bytes.bridge"])
        row = ratchet.condense(data, "x.json")
        self.assertFalse(row["evidence"])
        self.assertIsNone(row["gates"]["S3_size_emitted_parity_vs_O3"])
        self.assertIsNone(row["gates"]["S4_size_emitted_SB_vs_O3"])

    def test_rss_readings_are_the_median_of_the_retained_samples(self):
        row = program()
        samples = [41, 40, 44, 39, 40]
        row["rss_samples"]["program"]["bridge"] = [
            {"bytes": value * MIB, "status": "ok"} for value in samples]
        self.assertEqual(ratchet_gates.resource_reading(row, "peak_rss_bytes", "bridge"), 40 * MIB)
        self.assertAlmostEqual(
            ratchet_gates.relative_spread([value * MIB for value in samples]), 5 / 40)
        # One failed sample: no reading, never the median of the survivors.
        row["rss_samples"]["program"]["bridge"][3]["bytes"] = None
        self.assertIsNone(ratchet_gates.resource_reading(row, "peak_rss_bytes", "bridge"))
        # An even number of samples has no reading (its median is not a reading).
        row["rss_samples"]["program"]["bridge"] = [{"bytes": 40 * MIB}] * 4
        self.assertIsNone(ratchet_gates.resource_reading(row, "peak_rss_bytes", "bridge"))
        # No sample list at all: missing, whatever the stamp says.
        del row["rss_samples"]["compiler"]["llvm_o2"]
        self.assertIsNone(ratchet_gates.resource_reading(row, "compile_peak_rss_bytes", "llvm_o2"))

    def test_a_stamped_rss_reading_must_equal_its_samples_median(self):
        data = results()
        data["programs"][P[4]]["peak_rss_bytes"]["bridge"] = 41 * MIB  # samples still read 40
        problems = ratchet.validate(data, "sample")
        self.assertTrue(any(f"{P[4]}.peak_rss_bytes.bridge" in p and "median of its samples" in p
                            for p in problems), problems)
        # The gates read the samples' median, not the edited stamp.
        self.assertEqual(ratchet_gates.table_aggregates(data)["rss_geomean_vs_llvm_o3"], 1.0)

    def test_r1_band_widens_with_the_sample_spread(self):
        def row_with(bridge_samples, llvm=60):
            readings = [int(v * MIB) for v in bridge_samples]
            row = program(rss=(llvm * MIB, sorted(readings)[2]))
            row["rss_samples"]["program"]["bridge"] = [{"bytes": v} for v in readings]
            return row

        # +8% on a quiet lane (spread 0): beyond max(5%, 0) -> a loss.
        quiet = ratchet_gates.resource_aggregates({"x": row_with([64.8] * 5)}, CROSS_CHECK)
        # The same +8% median on a lane whose samples spread 6%: the band is 12% -> parity.
        noisy = ratchet_gates.resource_aggregates(
            {"x": row_with([63.0, 64.8, 64.8, 66.6, 64.8])}, CROSS_CHECK)
        self.assertEqual(quiet["program_rss_resolved_losses"], ["x"])
        self.assertEqual(noisy["program_rss_resolved_losses"], [])
        self.assertAlmostEqual(noisy["program_rss_max_rel_spread"], (66.6 - 63.0) / 64.8, places=6)

    def test_a_noisy_rss_comparison_is_unresolved_never_parity(self):
        def row_with(bridge_samples, llvm=50):
            readings = [int(v * MIB) for v in bridge_samples]
            row = program(rss=(llvm * MIB, sorted(readings)[2]))
            row["rss_samples"]["program"]["bridge"] = [{"bytes": v} for v in readings]
            return row

        def r1(rows):
            return ratchet_gates.resource_aggregates(rows, CROSS_CHECK)

        # One outlier of five: the median (+80%) ignores it, but the range-based
        # band (1 + 2 x 1.0 = 3x) would read parity. The comparison is noisy,
        # so R1 is unmeasured, never a pass.
        outlier = r1({"x": row_with([90, 90, 90, 90, 180])})
        self.assertEqual(outlier["program_rss_max_rel_spread"], 1.0)
        self.assertEqual(outlier["program_rss_resolved_losses"], [])
        self.assertIsNone(outlier["program_rss_resolved_loss_count"])
        # The same median on quiet samples is a loss.
        self.assertEqual(r1({"x": row_with([90] * 5)})["program_rss_resolved_loss_count"], 1)
        # A noisy comparison beyond even its widened band is still a loss:
        # spread 0.3, band 1.6x, median 4x.
        far = r1({"x": row_with([200, 200, 200, 200, 260])})
        self.assertEqual(far["program_rss_resolved_losses"], ["x"])
        self.assertEqual(far["program_rss_resolved_loss_count"], 1)
        # A spread at the cap resolves (band 1.5x, parity); one noisy program
        # among resolved parities leaves R1 unmeasured.
        self.assertEqual(r1({"x": row_with([50, 50, 50, 50, 62.5])})
                         ["program_rss_resolved_loss_count"], 0)
        mixed = r1({"x": row_with([50, 50, 50, 50, 70]), "y": row_with([50] * 5)})
        self.assertEqual(mixed["program_rss_floor_bound_count"], 0)
        self.assertIsNone(mixed["program_rss_resolved_loss_count"])
        # Through the ledger row: the outlier makes the whole-corpus R1 unmeasured.
        data = results()
        data["programs"][P[0]] = row_with([90, 90, 90, 90, 180])
        data["aggregates"].update(ratchet_gates.table_aggregates(data))
        self.assertIsNone(ratchet.condense(data, "x.json")["gates"]["R1_program_rss_no_resolved_loss"])

    def test_a_run_with_no_match_row_is_held_to_the_provenance_rss_n_only(self):
        # The Darwin production lane today: every program refused, none MATCH.
        data = results()
        for row in data["programs"].values():
            row["verdict"] = "INCOMPLETE"
        restamp(data)
        self.assertEqual(data["aggregates"]["match_count"], 0)
        self.assertIsNone(data["aggregates"]["rss_min_samples"])
        self.assertTrue(ratchet.condense(data, "x.json")["evidence"])
        data["provenance"]["n_rss"] = 3
        self.assertFalse(ratchet.condense(data, "x.json")["evidence"])

    def test_evidence_needs_the_contract_rss_n_in_provenance_and_every_lane(self):
        data = results()
        self.assertEqual(data["aggregates"]["rss_min_samples"], N_RSS)
        self.assertTrue(ratchet.condense(data, "x.json")["evidence"])
        for n in (None, 3, "5"):
            data = results()
            data["provenance"]["n_rss"] = n
            with self.subTest(n_rss=n):
                self.assertFalse(ratchet.condense(data, "x.json")["evidence"])
        data = results()
        for row in data["programs"].values():
            for kind in row["rss_samples"].values():
                for lane_name in kind:
                    kind[lane_name] = kind[lane_name][:3]
        data["aggregates"].update(ratchet_gates.table_aggregates(data))
        self.assertEqual(data["aggregates"]["rss_min_samples"], 3)
        self.assertFalse(ratchet.condense(data, "x.json")["evidence"])

    def test_a_row_below_the_rss_n_is_inconclusive_not_red(self):
        data = results()
        data["provenance"]["n_rss"] = 3
        row = ratchet.condense(data, "x.json")
        self.assertIn("peak-RSS sample count below the contract N", ratchet.comparability_problem(row))
        baseline = dict(ratchet.condense(results(), "b.json"), runtime_geomean_vs_llvm_o3=0.1)
        self.assertEqual(ratchet.ratchet_check(row, [baseline], self.thresholds()), [])
        # A schema-1 row (condensed before n_rss existed) is not held to it.
        legacy = dict(row)
        legacy.pop("ledger_row_schema")
        legacy.pop("n_rss")
        self.assertIsNone(ratchet.comparability_problem(legacy))

    def test_emitted_size_regressions_are_red_against_version_3_baselines_only(self):
        grown = results()
        for name in P:
            grown["programs"][name]["emitted_size_bytes"] = {"llvm_o3": 1000, "bridge": 1100}
        row = ratchet.condense(restamp(grown), "grown.json")
        v3 = dict(ratchet.condense(results(), "v3.json"))
        fails = ratchet.ratchet_check(row, [v3], self.thresholds())
        self.assertTrue(any(f.startswith("emitted_size_geomean_vs_llvm_o3") for f in fails), fails)
        v2 = dict(v3, gates_version=2, source_results="v2.json")
        self.assertEqual(ratchet.ratchet_check(row, [v2], self.thresholds()), [])
        # A shared-program comparison after a corpus change sees it too.
        changed = results()
        del changed["programs"][P[17]]
        for name in P[:17]:
            changed["programs"][name]["emitted_size_bytes"] = {"llvm_o3": 1000, "bridge": 1100}
        changed_row = ratchet.condense(restamp(changed), "changed.json")
        fails = ratchet.shared_program_regressions(changed_row, [v3], self.thresholds())
        self.assertTrue(any(f.startswith("emitted_size_geomean_vs_llvm_o3") for f in fails), fails)

    def test_results_without_version_3_aggregates_are_not_current(self):
        data = results()
        for key in ("emitted_size_geomean_vs_llvm_o3", "emitted_size_worst_vs_llvm_o3"):
            data["aggregates"].pop(key)
        self.assertTrue(ratchet.predates_table_aggregates(data))
        with tempfile.TemporaryDirectory(prefix="trust-cg-ratchet-") as temporary:
            path = Path(temporary) / "v2.json"
            path.write_text(json.dumps(data), encoding="utf-8")
            result = subprocess.run([sys.executable, str(ROOT / "scripts/check_perf_ratchet.py"),
                                     str(path)], capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, ratchet.NOT_CURRENT_EXIT, result.stdout + result.stderr)
        self.assertIn("gates.json version 3", result.stderr)

    def test_committed_schema_1_rows_stay_readable(self):
        ledger = ratchet.read_ledger()
        # The ledger is append-only, so its schema-1 rows (condensed before
        # `ledger_row_schema` existed) stay in it whatever is appended later.
        legacy = [row for row in ledger if "ledger_row_schema" not in row]
        self.assertTrue(legacy)
        self.assertIn("| emitted size |", ratchet.render_md(legacy))
        for row in legacy:
            problem = ratchet.comparability_problem(row)
            self.assertFalse(problem and "peak-RSS" in problem, problem)
        result = subprocess.run([sys.executable, str(ROOT / "scripts/check_perf_ratchet.py"),
                                 "--check-ledger"], capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
