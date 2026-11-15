"""Regression coverage for the wasm32 row family of the perf ledger
(benchmarks/wasm-vs-llvm, scripts/wasm_perf_ratchet.py)."""

from __future__ import annotations

import copy
import importlib.util
import json
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("perf_ratchet_wasm", ROOT / "scripts/check_perf_ratchet.py")
ratchet = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ratchet)
wasm = ratchet.wasm
contract = wasm.contract
B1, TCG, B2 = contract.B1, contract.TCG, contract.B2
P = contract.corpus_programs()
THRESHOLDS = json.loads((ROOT / "ratchet/perf_baseline.json").read_text())["wasm32_thresholds"]


def lane(file=1000, code=800, insns=500, local_count=10, memops=20, dyn=10_000, dyn_mem=500,
         calls=50, stack=64, time_ms=1.0, acc="2a"):
    """One lane record shaped like the harness's (run.py + wasmtool.mjs measure/time)."""
    return {
        "compile_s": 0.5,
        "static": {"file_bytes": file, "code_bytes": code, "static_insns": insns,
                   "declared_locals": local_count, "static_memops": memops},
        "dynamic": {"dyn_insns": dyn, "dyn_memops": dyn_mem, "dyn_calls": calls, "dyn_loop_heads": 3},
        "stack": {"sp_init": 1 << 20, "sp_min_written": (1 << 20) - stack, "touch_min": (1 << 20) - stack,
                  "stack_hwm": stack, "stack_hwm_written": stack},
        "loop_acc": acc, "loop_trap": None,
        "differential": {"checks": 40, "disagreements": 0, "soft_signed_zero": 0, "soft_cases": [],
                         "missing_exports": []},
        "timing": {mode: {"reps": 8, "samples_ms": [time_ms] * 5} for mode in contract.MODES},
    }


def program(scale=2.0, time_scale=1.5, verdict="MATCH", stack=(64, 128)):
    """A program row whose trust-cg lane is SCALE times B1 on every count."""
    b1 = lane(stack=stack[0])
    tcg = lane(file=int(1000 * scale), code=int(800 * scale), insns=int(500 * scale),
               local_count=int(10 * scale), memops=int(20 * scale), dyn=int(10_000 * scale),
               dyn_mem=int(500 * scale), calls=50, stack=stack[1], time_ms=1.0 * time_scale)
    b2 = lane(file=800, code=640, dyn=9_000, time_ms=0.9)
    return {"verdict": verdict, "reason": None, "workload": {"calls": 40, "status": "ok"},
            "lanes": {B1: b1, TCG: tcg, B2: b2}}


def restamp(data):
    data["aggregates"] = contract.table_aggregates(data)
    return data


def results(names=None, **row_kwargs):
    provenance = {field: "recorded" for field in contract.MANDATORY_PROVENANCE}
    provenance.update(
        schema=contract.RESULTS_SCHEMA, contract_version=2, git_dirty=False, untracked_count=0,
        tcg_env={}, bridge_cg_args=["no-proof-certs"], target=contract.TARGET, opt_level="2",
        host_arch="arm64", host_model="test-cpu", engine="node v26 / V8 14", quiet=True,
        load_status="QUIET", load_threshold_overridden=False, runaway_processes=[],
        dylib_stale_source=None, n_run=5, modes=list(contract.MODES), provenance_complete=True,
        corpus_manifest_sha256=contract.manifest_sha256(), timestamp_utc="2026-10-01T00:00:00+00:00",
        git_sha="a" * 40, rustc_version="rustc 1.99.0-dev", wasm_ld_version="LLD 22",
        sysroot_sha256="s" * 64, grid_sha256="g" * 64, wasm_opt_version="wasm-opt version 132",
        loadavg_before=0.5, loadavg_after=0.5, load_threshold=7.0,
    )
    data = {"schema": contract.RESULTS_SCHEMA, "row_family": contract.ROW_FAMILY,
            "provenance": provenance, "headline_eligible": True,
            "programs": {name: program(**row_kwargs) for name in (names or P)}, "aggregates": {}}
    return restamp(data)


def evidence_row(data, name):
    row = wasm.condense(data, name)
    assert row["evidence"], row["ineligible_reasons"]
    return row


def check(data, name="r.json"):
    return wasm.validate(data, name, ratchet.weakening_flags)


class WasmResultsTests(unittest.TestCase):
    def test_an_eligible_fixture_is_evidence(self):
        data = results()
        self.assertEqual(check(data), [])
        row = wasm.condense(data, "r.json")
        self.assertTrue(row["evidence"], row["ineligible_reasons"])
        self.assertTrue(row["corpus_complete"])
        self.assertAlmostEqual(row["wasm_file_bytes_geomean_vs_llvm_o2"], 2.0)
        self.assertAlmostEqual(row["wasm_stack_hwm_total_vs_llvm_o2"], 2.0)
        self.assertAlmostEqual(row["wasm_time_turbofan_geomean_vs_llvm_o2"], 1.5)
        self.assertEqual(row["program_metric_names"][0], "file_bytes")
        self.assertEqual(row["program_metrics"][P[0]][0], [2000, 1000])
        self.assertEqual(wasm._pairs_of(row)[P[0]]["time_turbofan"], [1.5, 1.0])
        self.assertEqual(row["gates_proposed"]["WSB5_coverage"], True)
        self.assertEqual(row["gates_proposed"]["WSB1_file_bytes_vs_B1"], False)

    def test_wasm_results_are_routed_to_the_wasm_family(self):
        self.assertTrue(wasm.is_wasm_results(results()))
        self.assertFalse(wasm.is_wasm_results({"schema": "trust-cg-bench-v2"}))
        self.assertTrue(wasm.is_wasm_row(wasm.condense(results(), "r.json")))

    def test_a_mismatch_is_rejected_never_ratcheted(self):
        data = results()
        data["programs"][P[3]]["verdict"] = "MISMATCH"
        restamp(data)
        problems = check(data)
        self.assertTrue(any("mismatch_count=1" in p and "stop-the-line" in p for p in problems), problems)

    def test_missing_provenance_is_rejected(self):
        for field in ("dylib_sha256", "engine", "sysroot_sha256", "grid_sha256", "bridge_cg_args"):
            data = results()
            del data["provenance"][field]
            with self.subTest(field=field):
                self.assertTrue(any("missing mandatory provenance" in p and field in p for p in check(data)))

    def test_the_lane_knob_is_required_and_other_weakening_is_rejected(self):
        cases = {
            "lane knob absent": ([], {}),
            "extra proof-weakening knob": (["no-proof-certs", "no-proof-cache"], {}),
            "refine solver off": (["no-proof-certs", "refine-solver=off"], {}),
            "weakening environment": (["no-proof-certs"], {"TCG_NO_PROOF_CACHE": "1"}),
        }
        for label, (args, env) in cases.items():
            data = results()
            data["provenance"].update(bridge_cg_args=args, tcg_env=env)
            with self.subTest(case=label):
                self.assertTrue(check(data), label)
        data = results()
        self.assertEqual(check(data), [])

    def test_a_non_wasm_target_or_schema_is_rejected(self):
        data = results()
        data["provenance"]["target"] = "aarch64-apple-darwin"
        self.assertTrue(any("is not wasm32" in p for p in check(data)))
        data = results()
        data["schema"] = "trust-cg-wasm-bench-v0"
        self.assertTrue(any("schema" in p for p in check(data)))

    def test_stamped_aggregates_must_match_the_table(self):
        data = results()
        data["aggregates"]["wasm_file_bytes_geomean_vs_llvm_o2"] = 1.9
        self.assertTrue(any("disagrees with its recomputation" in p for p in check(data)))
        data = results()
        del data["aggregates"]["wasm_dyn_insns_geomean_vs_llvm_o2"]
        self.assertTrue(any("is missing" in p for p in check(data)))
        data = results()
        data["programs"][P[0]]["verdict"] = "PASS"
        self.assertTrue(any("verdict must be one of" in p for p in check(data)))

    def test_the_headline_stamp_cannot_override_provenance(self):
        edits = {
            "loaded": {"quiet": False, "load_status": "LOADED"},
            "dirty": {"git_dirty": True},
            "stale dylib": {"dylib_stale_source": "crates/rustc-codegen-trust-cg/src/lib.rs"},
            "runaway": {"runaway_processes": [{"pid": 1}]},
            "threshold override": {"load_threshold_overridden": True},
            "few samples": {"n_run": 3},
            "fewer modes": {"modes": ["turbofan"]},
            "other manifest": {"corpus_manifest_sha256": "0" * 64},
            "diagnostic env": {"tcg_env": {"TCG_TRACE": "1"}},
        }
        for label, edit in edits.items():
            data = results()
            data["provenance"].update(edit)
            with self.subTest(case=label):
                self.assertTrue(data["headline_eligible"])
                self.assertFalse(wasm.condense(data, "r.json")["evidence"])
        data = results()
        data["headline_eligible"] = False
        self.assertFalse(wasm.condense(data, "r.json")["evidence"])

    def test_aggregates_are_fail_closed(self):
        data = results()
        del data["programs"][P[5]]["lanes"][TCG]["dynamic"]
        agg = contract.table_aggregates(data)
        self.assertIsNone(agg["wasm_dyn_insns_geomean_vs_llvm_o2"])
        self.assertIsNone(agg["wasm_dyn_calls_total_vs_llvm_o2"])
        self.assertIsNotNone(agg["wasm_file_bytes_geomean_vs_llvm_o2"])
        self.assertFalse(agg["deterministic_complete"])
        self.assertIn(f"{P[5]}:dyn_insns", agg["readings_missing"])
        self.assertFalse(wasm.condense(restamp(data), "r.json")["evidence"])
        # A missing timing sample nulls only the timing aggregates.
        data = results()
        data["programs"][P[2]]["lanes"][B1]["timing"]["liftoff"]["samples_ms"] = []
        agg = contract.table_aggregates(data)
        self.assertIsNone(agg["wasm_time_liftoff_geomean_vs_llvm_o2"])
        self.assertTrue(agg["deterministic_complete"])
        self.assertFalse(agg["timing_complete"])

    def test_a_program_without_a_workload_leaves_only_the_dynamic_scope(self):
        data = results()
        data["programs"][P[1]]["workload"] = {"calls": 0, "status": "empty"}
        for lane_name in (B1, TCG, B2):
            for key in ("dynamic", "stack", "timing"):
                data["programs"][P[1]]["lanes"][lane_name].pop(key)
        agg = contract.table_aggregates(data)
        self.assertEqual(agg["workload_excluded"], [P[1]])
        self.assertEqual(agg["workload_program_count"], len(P) - 1)
        self.assertTrue(agg["deterministic_complete"] and agg["timing_complete"])
        pairs = wasm._pairs_of(wasm.condense(restamp(data), "r.json"))
        self.assertNotIn("dyn_insns", pairs[P[1]])
        self.assertIn("file_bytes", pairs[P[1]])

    def test_counts_that_can_be_zero_aggregate_as_totals(self):
        data = results()
        data["programs"][P[0]] = program(stack=(0, 32))
        agg = contract.table_aggregates(data)
        total_b1 = 64 * (len(P) - 1)
        self.assertAlmostEqual(agg["wasm_stack_hwm_total_vs_llvm_o2"], (128 * (len(P) - 1) + 32) / total_b1)
        self.assertEqual(agg["wasm_stack_hwm_worse_count"], len(P))
        # A zero reading of a geomean metric is unusable, not a ratio.
        data["programs"][P[0]]["lanes"][B1]["static"]["file_bytes"] = 0
        self.assertIsNone(contract.table_aggregates(data)["wasm_file_bytes_geomean_vs_llvm_o2"])

    def test_b2_is_context_over_agreeing_programs_only(self):
        data = results()
        data["programs"][P[4]]["lanes"][B2]["differential"]["disagreements"] = 2
        agg = contract.table_aggregates(data)
        self.assertEqual(agg["b2_excluded"], [P[4]])
        self.assertAlmostEqual(agg["llvm_o2_wasmopt_file_bytes_geomean_vs_llvm_o2"], 0.8)
        self.assertAlmostEqual(agg["wasm_file_bytes_geomean_vs_llvm_o2_wasmopt"], 2.5)
        self.assertEqual(agg["b2_absent_count"], 0)
        # Without any B2 lane the context is unmeasured (absent, not excluded:
        # no B2 module disagreed), and evidence does not need it.
        data = results()
        for row in data["programs"].values():
            row["lanes"].pop(B2)
        restamp(data)
        self.assertIsNone(data["aggregates"]["wasm_file_bytes_geomean_vs_llvm_o2_wasmopt"])
        self.assertEqual(data["aggregates"]["b2_excluded"], [])
        self.assertEqual(data["aggregates"]["b2_absent_count"], len(P))
        self.assertEqual(data["aggregates"]["b2_program_count"], 0)
        self.assertTrue(wasm.condense(data, "r.json")["evidence"])

    def test_incomplete_rows_carry_a_kind_and_only_typed_refusals_can_be_evidence(self):
        for kind, evidence in (("refused", True), ("compile_failed", False), ("b1_failed", False), ("harness", False)):
            data = results()
            data["programs"][P[3]] = {"verdict": "INCOMPLETE", "incomplete_kind": kind, "reason": kind,
                                      "lanes": {}, "workload": None}
            restamp(data)
            with self.subTest(kind=kind):
                self.assertEqual(check(data), [])
                row = wasm.condense(data, "r.json")
                self.assertEqual(row["evidence"], evidence, row["ineligible_reasons"])
                self.assertEqual(row["incomplete_unrefused"], [] if evidence else [P[3]])
                self.assertEqual(row["coverage_pct"], 100.0 * (len(P) - 1) / len(P))
        data = results()
        data["programs"][P[3]] = {"verdict": "INCOMPLETE", "reason": "?", "lanes": {}, "workload": None}
        self.assertTrue(any("needs an incomplete_kind" in p for p in check(restamp(data))))
        # --check-ledger refuses an evidence row that carries one.
        row = wasm.condense(results(), "r.json")
        self.assertTrue(any("not typed refusals" in p for p in
                            wasm.row_problems(dict(row, incomplete_unrefused=[P[0]]), ratchet.weakening_flags)))

    def test_a_match_row_needs_a_clean_differential(self):
        for edit in ({"disagreements": 1}, {"disagreements": None, "run_failure": {"stage": "timeout"}},
                     {"missing_exports": ["f"]}):
            data = results()
            data["programs"][P[2]]["lanes"][TCG]["differential"].update(edit)
            with self.subTest(edit=edit):
                self.assertTrue(any("differential is not clean" in p for p in check(restamp(data))))

    def test_signed_zero_differences_are_allowed_only_where_the_manifest_lists_them(self):
        listed = contract.soft_zero_allowed()
        self.assertEqual(listed["c7_minmax"], {"max64", "min32"})
        self.assertEqual(contract.manifest_problems(json.loads(contract.MANIFEST.read_text())["programs"]), [])
        self.assertTrue(contract.manifest_problems({"x": {"sha256": "0", "soft_signed_zero": {"f": " "}}}))
        data = results()
        diff = data["programs"]["c7_minmax"]["lanes"][TCG]["differential"]
        diff.update(soft_signed_zero=2, soft_cases=[
            {"export": "max64", "args": ["0", "-0"], "oracle": "-0", "candidate": "0"},
            {"export": "min32", "args": ["-0", "0"], "oracle": "0", "candidate": "-0"}])
        restamp(data)
        self.assertEqual(check(data), [])
        row = wasm.condense(data, "r.json")
        self.assertEqual(row["soft_signed_zero_total"], 2)
        self.assertTrue(row["evidence"], row["ineligible_reasons"])
        # On an export, or a program, the manifest does not list: a malformed table.
        for program, export in (("c7_minmax", "maximum32"), (P[0], "f")):
            data = results()
            data["programs"][program]["lanes"][TCG]["differential"].update(
                soft_signed_zero=1, soft_cases=[{"export": export, "args": ["0"], "oracle": "-0", "candidate": "0"}])
            with self.subTest(program=program, export=export):
                self.assertTrue(any("does not list under soft_signed_zero" in p for p in check(restamp(data))))

    def test_proposed_gates_read_unmeasured_when_their_input_is_null(self):
        data = results()
        del data["programs"][P[0]]["lanes"][TCG]["stack"]
        verdicts = contract.gate_verdicts(restamp(data))
        self.assertIsNone(verdicts["WSB4_stack_hwm_vs_B1"])
        self.assertFalse(verdicts["WSB1_file_bytes_vs_B1"])
        better = results(scale=0.9, time_scale=0.8, stack=(64, 60))
        verdicts = contract.gate_verdicts(better)
        self.assertTrue(all(verdicts.values()), verdicts)


class WasmRatchetTests(unittest.TestCase):
    def test_deterministic_metrics_ratchet_with_zero_tolerance(self):
        base = evidence_row(results(), "base.json")
        same = wasm.condense(results(), "same.json")
        self.assertEqual(wasm.ratchet_check(same, [base], THRESHOLDS), [])
        worse = results()
        worse["programs"][P[7]]["lanes"][TCG]["static"]["code_bytes"] += 1
        fails = wasm.ratchet_check(wasm.condense(restamp(worse), "worse.json"), [base], THRESHOLDS)
        self.assertTrue(any(f.startswith("wasm_code_bytes_geomean_vs_llvm_o2") for f in fails), fails)
        better = results()
        better["programs"][P[7]]["lanes"][TCG]["static"]["code_bytes"] -= 1
        self.assertEqual(wasm.ratchet_check(wasm.condense(restamp(better), "b.json"), [base], THRESHOLDS), [])

    def test_timing_has_a_noise_floor(self):
        base = evidence_row(results(time_scale=1.5), "base.json")
        within = wasm.condense(results(time_scale=1.6), "within.json")
        self.assertEqual(wasm.ratchet_check(within, [base], THRESHOLDS), [])
        beyond = wasm.condense(results(time_scale=1.8), "beyond.json")
        fails = wasm.ratchet_check(beyond, [base], THRESHOLDS)
        self.assertEqual(sorted(f.split(":")[0] for f in fails),
                         sorted(contract.metric_key(m) for m in contract.TIMING))

    def test_timing_compares_only_the_same_host_and_engine(self):
        base = evidence_row(results(time_scale=1.0), "base.json")
        for field, value in (("engine", "node v27 / V8 15"), ("host_model", "other-cpu"), ("host_arch", "x86_64")):
            data = results(time_scale=3.0)
            data["provenance"][field] = value
            with self.subTest(field=field):
                self.assertEqual(wasm.ratchet_check(wasm.condense(data, "n.json"), [base], THRESHOLDS), [])
        # ... while the deterministic metrics, host-independent, are still compared.
        data = results(scale=2.5)
        data["provenance"]["engine"] = "node v27 / V8 15"
        fails = wasm.ratchet_check(wasm.condense(data, "n.json"), [base], THRESHOLDS)
        self.assertTrue(any(f.startswith("wasm_file_bytes") for f in fails), fails)

    def test_a_toolchain_change_has_no_baseline(self):
        base = evidence_row(results(), "base.json")
        for field, value in (("rustc_version", "rustc 1.100"), ("wasm_ld_version", "LLD 23"),
                             ("sysroot_sha256", "t" * 64), ("grid_sha256", "h" * 64), ("contract_version", 3),
                             ("measurement_sha256", "m" * 64)):
            data = results(scale=3.0, time_scale=3.0)
            data["provenance"][field] = value
            with self.subTest(field=field):
                self.assertEqual(wasm.ratchet_check(wasm.condense(data, "t.json"), [base], THRESHOLDS), [])

    def test_only_evidence_rows_are_baselines(self):
        loaded = results(scale=1.0)
        loaded["provenance"].update(quiet=False, load_status="LOADED")
        base = wasm.condense(loaded, "loaded.json")
        self.assertFalse(base["evidence"])
        self.assertEqual(wasm.ratchet_check(wasm.condense(results(scale=3.0), "n.json"), [base], THRESHOLDS), [])

    def test_ineligible_rows_are_still_regression_checked(self):
        base = evidence_row(results(), "base.json")
        regressed = results(scale=2.2)
        regressed["provenance"].update(quiet=False, load_status="LOADED")
        row = wasm.condense(regressed, "loaded.json")
        self.assertFalse(row["evidence"])
        self.assertTrue(wasm.ratchet_check(row, [base], THRESHOLDS))

    def test_a_coverage_drop_is_red(self):
        base = evidence_row(results(), "base.json")
        data = results()
        data["programs"][P[0]] = {"verdict": "INCOMPLETE", "incomplete_kind": "refused",
                                  "reason": "trust-cg refused ['TCG-X']", "lanes": {}, "workload": None}
        fails = wasm.ratchet_check(wasm.condense(restamp(data), "c.json"), [base], THRESHOLDS)
        self.assertTrue(any(f.startswith("coverage_pct") for f in fails), fails)

    def test_a_metric_the_baseline_measured_cannot_go_missing(self):
        base = evidence_row(results(), "base.json")
        data = results()
        del data["programs"][P[0]]["lanes"][TCG]["stack"]
        fails = wasm.ratchet_check(wasm.condense(restamp(data), "m.json"), [base], THRESHOLDS)
        self.assertTrue(any(f.startswith("wasm_stack_hwm_total_vs_llvm_o2: not measured") for f in fails), fails)

    def test_runs_that_are_not_like_with_like_are_inconclusive(self):
        base = evidence_row(results(), "base.json")
        subset = wasm.condense(results(names=P[:3], scale=4.0), "subset.json")
        self.assertIn("not the corpus", wasm.comparability_problem(subset))
        self.assertEqual(wasm.ratchet_check(subset, [base], THRESHOLDS), [])
        few = results(scale=4.0)
        few["provenance"]["n_run"] = 2
        self.assertIn("below the contract N", wasm.comparability_problem(wasm.condense(few, "few.json")))
        modes = results()
        modes["provenance"]["modes"] = ["turbofan"]
        self.assertIn("engine modes", wasm.comparability_problem(wasm.condense(modes, "modes.json")))

    def test_a_changed_corpus_compares_shared_programs(self):
        base = evidence_row(results(), "base.json")
        names = P + ["z9_added"]
        with self.corpus(names):
            regressed = wasm.condense(results(names=names, scale=2.5), "added.json")
            self.assertTrue(regressed["corpus_complete"])
            fails = wasm.ratchet_check(regressed, [base], THRESHOLDS)
            self.assertTrue(any(f"over the {len(P)} programs shared" in f for f in fails), fails)
            clean = evidence_row(results(names=names), "clean.json")
            self.assertEqual(wasm.ratchet_check(clean, [base], THRESHOLDS), [])
            self.assertIn("program set changed", wasm.lineage_problem(clean, [base]))
            self.assertIsNone(wasm.lineage_problem(clean, [base], "z9 added"))

    def corpus(self, names):
        return corpus(self, names)


def corpus(test, names):
    """Patch the corpus manifest to NAMES for a `with` block (the committed
    manifest is never touched); `results()` stamps the patched digest."""
    temporary = tempfile.TemporaryDirectory(prefix="trust-cg-wasm-manifest-")
    test.addCleanup(temporary.cleanup)
    manifest = Path(temporary.name) / "manifest.json"
    manifest.write_text(json.dumps({"programs": {name: {} for name in names}}), encoding="utf-8")
    return mock.patch.object(contract, "MANIFEST", manifest)


class WasmCommandLineTests(unittest.TestCase):
    def run_main(self, ledger_rows, data, *argv, name="results.json"):
        """check_perf_ratchet.main() in process on a temporary ledger and view."""
        with tempfile.TemporaryDirectory(prefix="trust-cg-wasm-ledger-") as temporary:
            ledger = Path(temporary) / "ledger.jsonl"
            ledger.write_text("".join(json.dumps(r, sort_keys=True) + "\n" for r in ledger_rows))
            view = Path(temporary) / "LEDGER.md"
            path = Path(temporary) / name
            path.write_text(json.dumps(data), encoding="utf-8")
            with mock.patch.object(ratchet, "LEDGER", ledger), mock.patch.object(ratchet, "LEDGER_MD", view), \
                    mock.patch.object(ratchet, "REPO", Path(temporary)), \
                    mock.patch.object(sys, "argv", ["check_perf_ratchet.py", *argv, str(path)]), \
                    mock.patch("sys.stdout") as stdout, mock.patch("sys.stderr") as stderr:
                with self.assertRaises(SystemExit) as stop:
                    ratchet.main()
            written = [json.loads(line) for line in ledger.read_text().splitlines() if line.strip()]
            rendered = view.read_text() if view.exists() else ""
        messages = "".join(str(c.args[0]) for c in stderr.write.call_args_list + stdout.write.call_args_list)
        return stop.exception.code, written, rendered, messages

    def native_row(self):
        return next(r for r in ratchet.read_ledger() if r.get("evidence"))

    def test_append_records_a_row_and_renders_the_wasm_section(self):
        native = self.native_row()
        loaded = results()
        loaded["provenance"].update(quiet=False, load_status="LOADED")
        code, written, rendered, messages = self.run_main([native], loaded, "--append", name="w1.json")
        self.assertEqual(code, 0, messages)
        self.assertEqual(len(written), 2)
        self.assertEqual(written[-1]["row_family"], "wasm32")
        self.assertFalse(written[-1]["evidence"])
        self.assertIn("## wasm32 vs rustc+LLVM", rendered)
        self.assertIn("GATE-WASM-SB (PROPOSED", rendered)
        self.assertIn("| w1.json |", rendered)
        # The native badge still describes the latest NATIVE row.
        self.assertIn(f"`{native['git_sha'][:9]}", rendered.split("## wasm32")[0])
        self.assertEqual(rendered.split("## wasm32")[0].rstrip("\n"),
                         ratchet.render_md([native]).rstrip("\n"))
        # The same source is never appended twice.
        code, written, _, messages = self.run_main(written, loaded, "--append", name="w1.json")
        self.assertEqual((code, len(written)), (0, 2), messages)
        self.assertIn("not duplicating", messages)

    def test_a_mismatch_exits_red_and_is_not_appended(self):
        data = results()
        data["programs"][P[0]]["verdict"] = "MISMATCH"
        code, written, _, messages = self.run_main([], restamp(data), "--append")
        self.assertEqual(code, 1, messages)
        self.assertEqual(written, [])
        self.assertIn("REJECT", messages)

    def test_a_regression_exits_red_and_is_not_appended(self):
        base = evidence_row(results(), "base.json")
        code, written, _, messages = self.run_main([base], results(scale=2.1), "--append", name="r.json")
        self.assertEqual(code, 1, messages)
        self.assertEqual(len(written), 1)
        self.assertIn("RED: wasm_file_bytes_geomean_vs_llvm_o2", messages)

    def test_a_subset_is_inconclusive_and_not_appended(self):
        code, written, _, messages = self.run_main([], results(names=P[:2]), "--append")
        self.assertEqual(code, ratchet.INCONCLUSIVE_EXIT, messages)
        self.assertEqual(written, [])

    def test_a_new_lineage_needs_an_evidence_row_and_a_changed_set(self):
        base = evidence_row(results(), "base.json")
        names = P + ["z9_added"]
        with corpus(self, names):
            loaded = results(names=names)
            loaded["provenance"].update(quiet=False, load_status="LOADED")
            code, written, _, messages = self.run_main([base], loaded, "--append", "--new-lineage", "z9")
            self.assertEqual(code, 2, messages)
            self.assertEqual(len(written), 1)
            code, written, _, messages = self.run_main([base], results(names=names), "--append")
            self.assertEqual(code, ratchet.INCONCLUSIVE_EXIT, messages)
            code, written, rendered, messages = self.run_main(
                [base], results(names=names), "--append", "--new-lineage", "z9 joins the corpus", name="l.json")
            self.assertEqual(code, 0, messages)
            self.assertEqual(written[-1]["new_lineage"]["reason"], "z9 joins the corpus")
            self.assertIn("NEW LINEAGE: z9 joins the corpus", rendered)
        code, _, _, messages = self.run_main([base], results(), "--append", "--new-lineage", "nothing changed")
        self.assertEqual(code, 2, messages)

    def test_require_current_refuses_a_stale_or_ineligible_file(self):
        code, _, _, messages = self.run_main([], results(), "--require-current")
        self.assertEqual(code, ratchet.NOT_CURRENT_EXIT, messages)
        self.assertIn("is not HEAD", messages)

    def test_check_ledger_validates_wasm_rows_by_their_own_rules(self):
        good = wasm.condense(results(), "good.json")
        self.assertEqual(wasm.row_problems(good, ratchet.weakening_flags), [])
        bad = dict(good, mismatch_count=1, bridge_cg_args=["no-proof-certs", "no-proof-cache"])
        problems = wasm.row_problems(bad, ratchet.weakening_flags)
        self.assertTrue(any("mismatch_count" in p for p in problems))
        self.assertTrue(any("no-proof-cache" in p for p in problems))
        with tempfile.TemporaryDirectory(prefix="trust-cg-wasm-ledger-") as temporary:
            ledger = Path(temporary) / "ledger.jsonl"
            for rows, expected in (([self.native_row(), good], 0), ([self.native_row(), bad], 1)):
                ledger.write_text("".join(json.dumps(r, sort_keys=True) + "\n" for r in rows))
                with mock.patch.object(ratchet, "LEDGER", ledger), \
                        mock.patch.object(sys, "argv", ["check_perf_ratchet.py", "--check-ledger"]), \
                        mock.patch("sys.stdout"):
                    with self.assertRaises(SystemExit) as stop:
                        ratchet.main()
                self.assertEqual(stop.exception.code, expected)

    def test_native_paths_never_see_wasm_rows(self):
        native = self.native_row()
        row = wasm.condense(results(), "w.json")
        self.assertEqual(ratchet.render_md([native]) + "\n" + "\n".join(wasm.render_section([row])),
                         ratchet.render_md([native, row]))
        self.assertFalse(ratchet.comparable(native, row))
        self.assertNotIn(row, ratchet._host_evidence(native, [row]))


class WasmContractTests(unittest.TestCase):
    def test_contract_json_agrees_with_the_executable_definition(self):
        doc = contract.load_contract()
        self.assertEqual(doc["version"], 2)
        self.assertEqual(doc["revisions"][-1]["version"], doc["version"])
        self.assertEqual(doc["results_schema"], contract.RESULTS_SCHEMA)
        self.assertEqual(sorted(doc["metrics"]), sorted(m for m, _, _ in contract.METRICS))
        self.assertEqual(sorted(doc["engine_modes"]), sorted(contract.MODES))
        self.assertEqual(doc["required_bridge_cg_args"], contract.REQUIRED_BRIDGE_CG_ARGS)
        self.assertEqual(doc["n_run_min"], contract.N_RUN_MIN)
        produced = set(contract.table_aggregates(results()))
        for name, gate in doc["gates"].items():
            fields = set(re.findall(r"\.aggregates\.([A-Za-z0-9_]+)", gate["predicate"]))
            with self.subTest(gate=name):
                self.assertTrue(fields and fields <= produced, fields - produced)
        self.assertEqual({key for key, _ in wasm.GATE_LABELS}, set(doc["gates"]))
        self.assertEqual(json.loads((ROOT / "ratchet/perf_baseline.json").read_text())["wasm32_thresholds"]
                         ["deterministic_max_regress_pct"], 0)

    def test_the_measurement_digest_follows_the_measuring_code(self):
        self.assertIn("measurement_sha256", contract.MANDATORY_PROVENANCE)
        self.assertIn("measurement_sha256", wasm.TOOLCHAIN_KEY)
        here = contract.MANIFEST.parent.parent
        digest = contract.measurement_sha256()
        with tempfile.TemporaryDirectory(prefix="trust-cg-wasm-measure-") as temporary:
            root = Path(temporary)
            for name in contract.MEASUREMENT_FILES:
                (root / name).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(here / name, root / name)
            self.assertEqual(contract.measurement_sha256(root), digest)
            for name in contract.MEASUREMENT_FILES:
                with self.subTest(changed=name):
                    original = (root / name).read_bytes()
                    (root / name).write_bytes(original + b"\n")
                    self.assertNotEqual(contract.measurement_sha256(root), digest)
                    (root / name).write_bytes(original)

    def test_the_committed_corpus_matches_its_manifest(self):
        manifest = json.loads(contract.MANIFEST.read_text())
        sources = sorted((contract.MANIFEST.parent).glob("*.rs"))
        self.assertEqual(sorted(p.stem for p in sources), sorted(manifest["programs"]))
        self.assertEqual(len(sources), 144)
        for path in sources:
            text = path.read_text()
            with self.subTest(program=path.stem):
                self.assertEqual(contract.hashlib.sha256(path.read_bytes()).hexdigest(),
                                 manifest["programs"][path.stem]["sha256"])
                self.assertIn("#![no_std]", text)
                self.assertNotRegex(text, r"/private/|/Users/|scratchpad")


def _uleb(value):
    out = bytearray()
    while True:
        byte = value & 0x7F
        value >>= 7
        out.append(byte | (0x80 if value else 0))
        if not value:
            return bytes(out)


def _f64_module(body):
    """A module exporting `f: (f64) -> f64` with BODY (no locals)."""
    def section(sid, payload):
        return bytes([sid]) + _uleb(len(payload)) + payload
    fn = b"\x00" + bytes(body) + b"\x0b"
    return (b"\x00asm\x01\x00\x00\x00" + section(1, bytes([1, 0x60, 1, 0x7C, 1, 0x7C]))
            + section(3, bytes([1, 0])) + section(7, bytes([1, 1]) + b"f" + bytes([0, 0]))
            + section(10, bytes([1]) + _uleb(len(fn)) + fn))


F64_ZERO = [0x44] + [0] * 8
CANDIDATES = {
    "agree": [0x20, 0, 0x9A],                       # f64.neg x
    "signzero": F64_ZERO + [0x20, 0, 0xA1],         # 0.0 - x: +0 where f64.neg gives -0
    "hang": [0x03, 0x40, 0x0C, 0, 0x0B, 0x20, 0, 0x9A],  # loop br 0 end
    "invalid": [0x20, 0, 0x42, 0, 0x7C],            # f64 + i64.add: fails validation
    "start_trap": None,                             # instantiation traps (start function)
}


def _start_trap_module():
    def section(sid, payload):
        return bytes([sid]) + _uleb(len(payload)) + payload
    neg = b"\x00\x20\x00\x9a\x0b"
    trap = b"\x00\x00\x0b"
    return (b"\x00asm\x01\x00\x00\x00" + section(1, bytes([2, 0x60, 1, 0x7C, 1, 0x7C, 0x60, 0, 0]))
            + section(3, bytes([2, 0, 1])) + section(7, bytes([1, 1]) + b"f" + bytes([0, 0]))
            + section(8, bytes([1])) + section(10, bytes([2]) + _uleb(len(neg)) + neg + _uleb(len(trap)) + trap))


@unittest.skipUnless(shutil.which("node"), "node is not installed")
class WasmHarnessVerdictTests(unittest.TestCase):
    """run.py's per-program verdicts through the real wasmtool.mjs, with the
    compiles replaced by hand-built modules (B1: f64.neg)."""

    @classmethod
    def setUpClass(cls):
        spec = importlib.util.spec_from_file_location("wasm_vs_llvm_run", ROOT / "benchmarks/wasm-vs-llvm/run.py")
        cls.driver = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.driver)

    def verdict(self, candidate, soft_zero=()):
        run = self.driver
        modules = {"oracle": _f64_module([0x20, 0, 0x9A])}
        modules["candidate"] = _start_trap_module() if candidate == "start_trap" else _f64_module(CANDIDATES[candidate])

        class Harness(run.Harness):
            def __init__(self):
                self.wasm_opt = None
                self.node = shutil.which("node")

            def compile(self, src, out, bridge):
                out.write_bytes(modules["candidate" if bridge else "oracle"])
                return 0.01, None

            def node_tool(self, flags, *args, timeout):
                # A short candidate budget floor keeps the hang case fast.
                return super().node_tool(flags, *args, "--budget-floor-ms", "1500", timeout=timeout)

        with tempfile.TemporaryDirectory(prefix="trust-cg-wasm-verdict-") as work:
            return Harness().build_and_measure("x", None, Path(work), soft_zero=soft_zero)

    def test_a_trust_cg_module_that_does_not_run_where_b1_did_is_a_mismatch(self):
        for candidate, stage in (("hang", "timeout"), ("invalid", "compile"), ("start_trap", "instantiate")):
            with self.subTest(candidate=candidate):
                row = self.verdict(candidate)
                self.assertEqual(row["verdict"], "MISMATCH", row["reason"])
                self.assertEqual(row["lanes"][TCG]["differential"]["run_failure"]["stage"], stage)
                self.assertIn(f"{stage} failure where B1 ran", row["reason"])
        hang = self.verdict("hang")["lanes"][TCG]["differential"]["run_failure"]
        self.assertEqual((hang["completed_calls"], hang["call"]), (0, "f(0)"))

    def test_signed_zero_is_a_disagreement_unless_the_export_is_listed(self):
        row = self.verdict("signzero")
        self.assertEqual(row["verdict"], "MISMATCH", row["reason"])
        self.assertIn("f(0): oracle=-0 candidate=0", row["reason"])
        row = self.verdict("signzero", soft_zero={"f": "unspecified by the source"})
        self.assertEqual(row["verdict"], "MATCH", row["reason"])
        diff = row["lanes"][TCG]["differential"]
        self.assertEqual(diff["soft_signed_zero"], 1)
        self.assertEqual(diff["soft_cases"], [{"export": "f", "args": ["0"], "oracle": "-0", "candidate": "0"}])
        # The listed export's accumulators fold -0 to +0, so the workload agrees.
        self.assertEqual(row["lanes"][TCG]["loop_acc"], row["lanes"][B1]["loop_acc"])

    def test_an_agreeing_module_matches_and_a_b1_failure_is_not_blamed_on_trust_cg(self):
        row = self.verdict("agree")
        self.assertEqual(row["verdict"], "MATCH", row["reason"])
        self.assertNotIn("incomplete_kind", row)
        self.assertEqual(self.driver.classify({"lanes": {B1: {}, TCG: {"differential": {"harness_fault": "x",
                                                                                         "disagreements": None}}}}),
                         ("INCOMPLETE", "harness: x"))


@unittest.skipUnless(shutil.which("node"), "node is not installed")
class WasmToolTests(unittest.TestCase):
    def test_decoder_loop_builder_and_instrumenter_selftest(self):
        result = subprocess.run(["node", str(ROOT / "benchmarks/wasm-vs-llvm/wasmtool.mjs"), "selftest"],
                                capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(json.loads(result.stdout)["selftest"], "OK")


if __name__ == "__main__":
    unittest.main()
