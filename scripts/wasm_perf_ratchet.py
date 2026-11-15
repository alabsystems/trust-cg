#!/usr/bin/env python3
"""scripts/wasm_perf_ratchet.py — the `wasm32` row family of the perf ledger.

Author: Andrew Yates <andrewyates.name@gmail.com>
Copyright 2026 Andrew Yates | License: Apache-2.0

scripts/check_perf_ratchet.py stays the one writer of ratchet/ledger.jsonl and
benchmarks/LEDGER.md. It routes a results JSON of schema trust-cg-wasm-bench-v2
(benchmarks/wasm-vs-llvm/run.py) here for its reject rules, its condensed row,
its regression checks and its section of the rendered view; native rows never
see wasm rows and wasm rows never see native ones.

REJECT (the row never enters the ledger):
  - a mandatory provenance field is missing, or the target is not wasm32;
  - a proof-weakening TCG_* environment or backend knob other than the one
    the lane requires: the wasm32 lane emits no proof certificates and the
    bridge refuses it without `no-proof-certs` ([TCG-PROOF-465]), so that knob
    is part of the lane's definition and must be recorded; any other weakening
    knob (no-proof-cache, refine-solver=off) is rejected as for native rows;
  - mismatch_count != 0 (a grid disagreement, a trust-cg module that did not
    compile, instantiate or return where B1 ran, or a differing workload
    accumulator): stop-the-line, never ratchetable;
  - a stamped aggregate that disagrees with its recomputation from the
    per-program table (wasm_contract.table_aggregates), or a malformed table
    (an INCOMPLETE row without its kind, a MATCH row whose differential is not
    clean, a signed-zero allowance the corpus manifest does not list).

RATCHET (exit 1 on regression; thresholds in ratchet/perf_baseline.json under
`wasm32_thresholds`, so changing one is a reviewed commit):
  - the deterministic metrics (sizes, static and dynamic counts, stack
    high-water) against evidence rows with the same toolchain key (target,
    opt level, rustc, wasm-ld, sysroot digest, grid digest, contract version,
    and the digest of the measuring code): they do not depend on the host or
    the engine, and a change to how they are counted starts a new key;
  - the timing metrics against evidence rows with the same toolchain key AND
    the same host and engine (node/V8): a node upgrade or another host has no
    timing baseline until its first evidence row;
  - coverage below the best same-key evidence row;
  - a metric a baseline measured that the new row does not.
Every comparison is computed over the programs both rows measured, from the
per-program pairs each row keeps, so a corpus change never hides a
regression on the programs that stayed. A run that is not like-with-like (a
program subset, fewer than N timing samples, fewer engine modes) is
INCONCLUSIVE; a full-corpus run whose program set differs from every same-key
evidence baseline is INCONCLUSIVE until `--append --new-lineage '<reason>'`
on an eligible evidence row records the new lineage. Ineligible rows are
recorded with `evidence: false`, are never baselines, and are still
regression-checked.
"""

import json
import sys
from datetime import datetime, timezone
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "benchmarks" / "wasm-vs-llvm" / "contract"))
import wasm_contract as contract  # noqa: E402

ROW_FAMILY = contract.ROW_FAMILY
LEDGER_ROW_SCHEMA = 1
LANE_KNOB_FLAGS = {f"-Ztrust-ir-cg-args={knob}" for knob in contract.REQUIRED_BRIDGE_CG_ARGS}
TOOLCHAIN_KEY = ("target", "opt_level", "rustc_version", "wasm_ld_version", "sysroot_sha256",
                 "grid_sha256", "contract_version", "measurement_sha256")
TIMING_KEY = TOOLCHAIN_KEY + ("host_arch", "host_model", "engine")
RATCHETED = contract.DETERMINISTIC + contract.TIMING
# Aggregates condensed onto the row as stamped (validate() checked them).
ROW_AGGREGATES = (
    "total_programs", "match_count", "mismatch_count", "incomplete_count", "incomplete_unrefused",
    "coverage_pct", "soft_signed_zero_total",
    "workload_program_count", "workload_excluded", "b2_program_count", "b2_excluded", "b2_absent_count",
    "deterministic_complete", "timing_complete", "readings_missing",
    "wasm_file_bytes_smaller_count", "wasm_time_turbofan_faster_count", "wasm_stack_hwm_worse_count",
    f"wasm_compile_geomean_vs_{contract.B1}",
    *(contract.metric_key(m) for m in RATCHETED),
    *(f"wasm_time_{mode}_worst_vs_{contract.B1}" for mode in contract.MODES),
    *(f"wasm_time_{mode}_median_geomean_vs_{contract.B1}" for mode in contract.MODES),
    *(contract.metric_key(m, contract.B2) for m in contract.B2_METRICS),
    *(f"{contract.B2}_{m}_{contract.METRIC[m][1]}_vs_{contract.B1}" for m in contract.B2_METRICS),
)


def is_wasm_results(results):
    return isinstance(results, dict) and (results.get("schema") == contract.RESULTS_SCHEMA
                                          or results.get("row_family") == ROW_FAMILY)


def is_wasm_row(row):
    return isinstance(row, dict) and row.get("row_family") == ROW_FAMILY


def lane_flag_problems(tcg_env, cg_args, weakening_flags):
    """Proof-weakening flags other than the lane's own required knob, and a
    missing required knob (provenance that does not describe the lane)."""
    problems = []
    flags = [flag for flag in weakening_flags(tcg_env, cg_args) if flag not in LANE_KNOB_FLAGS]
    if flags:
        problems.append(f"proof-weakening env/knobs {flags} beyond the wasm32 lane's required "
                        f"{contract.REQUIRED_BRIDGE_CG_ARGS} — never ledger rows")
    if not isinstance(cg_args, list) or not all(k in cg_args for k in contract.REQUIRED_BRIDGE_CG_ARGS):
        problems.append(f"bridge_cg_args {cg_args!r} does not record the lane's required knobs "
                        f"{contract.REQUIRED_BRIDGE_CG_ARGS}: the wasm32 lane compiles only with them")
    return problems


def validate(results, name, weakening_flags):
    """Hard reject rules for a wasm32 results file; a list of problems."""
    if not isinstance(results, dict):
        return [f"{name}: results must be an object"]
    if results.get("schema") != contract.RESULTS_SCHEMA:
        return [f"{name}: schema {results.get('schema')!r} is not {contract.RESULTS_SCHEMA}"]
    prov = results.get("provenance")
    if not isinstance(prov, dict):
        return [f"{name}: no provenance object — numbers without stamps are not evidence"]
    problems = []
    missing = [field for field in contract.MANDATORY_PROVENANCE if field not in prov]
    if missing:
        problems.append(f"{name}: missing mandatory provenance fields {missing}")
    if prov.get("target") != contract.TARGET:
        problems.append(f"{name}: target {prov.get('target')!r} is not {contract.TARGET}")
    env = prov.get("tcg_env")
    if not isinstance(env, dict):
        problems.append(f"{name}: tcg_env must be an object")
        env = {}
    problems.extend(f"{name}: {p}" for p in lane_flag_problems(env, prov.get("bridge_cg_args"), weakening_flags))
    if not isinstance(results.get("programs"), dict) or not isinstance(results.get("aggregates"), dict):
        return problems + [f"{name}: programs and aggregates must be objects"]
    mismatches = contract.table_aggregates(results)["mismatch_count"]
    if mismatches != 0 or results["aggregates"].get("mismatch_count") != 0:
        problems.append(f"{name}: mismatch_count={mismatches} — P0 stop-the-line, not ratchetable")
    problems.extend(f"{name}: {p}" for p in contract.table_issues(results))
    return problems


# Timing pairs are kept to 0.1 microsecond on the row (far below the timing
# floor); deterministic pairs are exact integers.
TIMING_DIGITS = 4


def program_metrics(results):
    """{program: [[trust-cg, B1] or null per RATCHETED metric]}: the pairs a
    later row is compared on, positional to keep the row small (the metric
    order is stamped beside it as `program_metric_names`). A metric outside a
    program's scope is null."""
    out = {name: [None] * len(RATCHETED) for name in sorted(results.get("programs") or {})
           if contract.in_scope(results["programs"][name], "file_bytes")}
    for index, metric in enumerate(RATCHETED):
        for name, pair in contract.program_pairs(results, metric).items():
            if contract.METRIC[metric][0] == "timing":
                pair = [None if v is None else round(v, TIMING_DIGITS) for v in pair]
            out[name][index] = pair
    return out


def _pairs_of(row):
    """{program: {metric: pair}} from a row's positional program metrics."""
    names = row.get("program_metric_names") or []
    out = {}
    for program, pairs in (row.get("program_metrics") or {}).items():
        out[program] = {m: p for m, p in zip(names, pairs or []) if p is not None}
    return out


def condense(results, source_name):
    """The ledger row, condensed field for field from validated results."""
    p = results["provenance"]
    agg = contract.table_aggregates(results)
    reasons = contract.evidence_problems(results)
    names = sorted(results.get("programs") or {})
    return {
        "row_family": ROW_FAMILY,
        "ledger_row_schema": LEDGER_ROW_SCHEMA,
        "source_results": source_name,
        "timestamp_utc": p["timestamp_utc"],
        "git_sha": p["git_sha"],
        "git_dirty": p["git_dirty"],
        "dylib_sha256": p["dylib_sha256"],
        "host_arch": " ".join(str(p["host_arch"]).split()),
        "host_model": " ".join(str(p["host_model"]).split()),
        "target": p["target"],
        "opt_level": p["opt_level"],
        "load_status": p["load_status"],
        "tcg_env": p["tcg_env"],
        "bridge_cg_args": p["bridge_cg_args"],
        "engine": p["engine"],
        "rustc_version": p["rustc_version"],
        "wasm_ld_version": p["wasm_ld_version"],
        "wasm_opt_version": p["wasm_opt_version"],
        "sysroot_sha256": p["sysroot_sha256"],
        "grid_sha256": p["grid_sha256"],
        "contract_version": p["contract_version"],
        "measurement_sha256": p["measurement_sha256"],
        "corpus_manifest_sha256": p["corpus_manifest_sha256"],
        "n_run": p["n_run"],
        "modes": sorted(p["modes"]) if isinstance(p["modes"], list) else p["modes"],
        "program_set_sha256": contract.program_set_sha256(names),
        "corpus_complete": contract.full_corpus(results),
        # Recomputed from the results, never the headline stamp.
        "evidence": not reasons,
        "ineligible_reasons": reasons,
        **{key: agg[key] for key in ROW_AGGREGATES},
        "gates_proposed": contract.gate_verdicts(results),
        "program_metric_names": list(RATCHETED),
        "program_metrics": program_metrics(results),
    }


def row_problems(row, weakening_flags):
    """--check-ledger: a committed wasm32 row's condensed invariants."""
    problems = lane_flag_problems(row.get("tcg_env") or {}, row.get("bridge_cg_args"), weakening_flags)
    if row.get("mismatch_count") != 0:
        problems.append("mismatch_count != 0")
    if row.get("target") != contract.TARGET:
        problems.append(f"target {row.get('target')!r}")
    for metric in RATCHETED:
        key, value = contract.metric_key(metric), row.get(contract.metric_key(metric))
        # A total of trust-cg's counts may legitimately be 0; a geomean of ratios may not.
        floor_ok = (lambda v: v > 0) if contract.METRIC[metric][1] == "geomean" else (lambda v: v >= 0)
        if value is not None and not (type(value) in (int, float) and floor_ok(value)):
            problems.append(f"{key} must be a {'positive' if contract.METRIC[metric][1] == 'geomean' else 'non-negative'} number or null")
    if row.get("evidence") and row.get("ineligible_reasons"):
        problems.append("an evidence row lists ineligibility reasons")
    if row.get("evidence") and row.get("incomplete_unrefused"):
        problems.append("an evidence row has INCOMPLETE programs that are not typed refusals")
    return problems


def comparability_problem(row):
    if row.get("corpus_complete") is not True:
        return (f"program set is not the corpus ({row.get('total_programs')} programs; a --progs "
                "subset or another corpus)")
    if type(row.get("n_run")) is not int or row["n_run"] < contract.N_RUN_MIN:
        return f"timing samples per lane {row.get('n_run')!r} below the contract N ({contract.N_RUN_MIN})"
    if sorted(row.get("modes") or []) != sorted(contract.MODES):
        return f"engine modes {row.get('modes')!r} are not the contract's {list(contract.MODES)}"
    return None


def _same(row, base, key):
    return all(row.get(k) is not None and base.get(k) == row.get(k) for k in key)


def evidence_baselines(row, ledger, key=TOOLCHAIN_KEY):
    return [r for r in ledger if is_wasm_row(r) and r.get("evidence") is True
            and r.get("corpus_complete") is True and r.get("source_results") != row.get("source_results")
            and _same(row, r, key)]


def shared_value(row, base, metric):
    """(row value, baseline value, shared count) of METRIC over the programs
    both rows measured it on, or None when the baseline has no such value."""
    cur, old = _pairs_of(row), _pairs_of(base)
    shared = sorted(name for name in old if metric in (old[name] or {}) and name in cur)
    if not shared:
        return None
    how = contract.METRIC[metric][1]
    base_value = contract.aggregate({n: old[n][metric] for n in shared}, how)
    if base_value is None:
        return None
    value = contract.aggregate({n: (cur[n] or {}).get(metric, [None, None]) for n in shared}, how)
    return value, base_value, len(shared)


def ratchet_check(row, ledger, thresholds):
    """Regression failures against the evidence baselines (empty when none)."""
    problem = comparability_problem(row)
    if problem:
        print(f"perf-ratchet: wasm32: INCONCLUSIVE: {problem} — no regression verdict")
        return []
    if not row.get("evidence"):
        print("perf-ratchet: wasm32 row is NOT evidence — it cannot become a baseline, but it is "
              "still regression-checked.")
    fails = []
    for metrics, key, floor_key, label in (
            (contract.DETERMINISTIC, TOOLCHAIN_KEY, "deterministic_max_regress_pct", "toolchain"),
            (contract.TIMING, TIMING_KEY, "time_geomean_max_regress_pct", "toolchain, host and engine")):
        baselines = evidence_baselines(row, ledger, key)
        if not baselines:
            print(f"perf-ratchet: wasm32: no evidence baseline with the same {label} — "
                  f"{', '.join(metrics)} regression check SKIPPED loudly; this row is the first "
                  "candidate baseline when appended.")
            continue
        floor = thresholds[floor_key]
        for metric in metrics:
            worst = None
            for base in baselines:
                compared = shared_value(row, base, metric)
                if compared is None:
                    continue
                value, base_value, count = compared
                if value is None:
                    fails.append(f"{contract.metric_key(metric)}: not measured over the {count} programs "
                                 f"{base.get('source_results')} measured it on")
                    break
                pct = 100.0 * (value - base_value) / base_value
                if worst is None or pct > worst[0]:
                    worst = (pct, value, base_value, count, base.get("source_results"))
            if worst and worst[0] > floor:
                pct, value, base_value, count, source = worst
                fails.append(f"{contract.metric_key(metric)}: {value:.6g} vs {base_value:.6g} over the {count} "
                             f"programs shared with {source} — regression {pct:.3f}% > floor {floor}%")
    baselines = evidence_baselines(row, ledger)
    if thresholds.get("coverage_drop_is_red", True) and baselines:
        best = max(100.0 * b["match_count"] / b["total_programs"] for b in baselines if b.get("total_programs"))
        current = 100.0 * row["match_count"] / row["total_programs"] if row.get("total_programs") else 0.0
        if current < best:
            fails.append(f"coverage_pct: {current:.1f}% < best committed {best:.1f}%")
    return fails


def lineage_problem(row, ledger, new_lineage=None):
    """Why ROW's program set has no same-key evidence lineage, or None."""
    baselines = evidence_baselines(row, ledger)
    if not baselines or new_lineage or any(b.get("program_set_sha256") == row.get("program_set_sha256")
                                           for b in baselines):
        return None
    return (f"program set changed: this run measured {row.get('total_programs')} programs "
            f"({str(row.get('program_set_sha256'))[:16]}), every same-toolchain evidence baseline another "
            "set; declare the new lineage with --append --new-lineage '<reason>'")


def lineage_record(row, ledger, reason):
    return {
        "reason": reason.strip(),
        "replaces_program_sets": sorted({b.get("program_set_sha256") for b in evidence_baselines(row, ledger)}),
        "declared_utc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
    }


def _f(value, digits=3):
    if value is None:
        return "—"
    return str(round(value, digits)) if isinstance(value, float) else str(value)


GATE_LABELS = (
    ("WSB1_file_bytes_vs_B1", "file bytes geomean < 1.00x B1"),
    ("WSB2_time_turbofan_vs_B1", "TurboFan time geomean < 1.00x B1, every program <= 1.50x"),
    ("WSB3_time_default_vs_B1", "default-tiering time geomean < 1.00x B1, every program <= 1.50x"),
    ("WSB4_stack_hwm_vs_B1", "stack high-water total <= 1.00x B1"),
    ("WSB5_coverage", "every corpus program compiles and matches"),
)


def render_section(rows):
    """The wasm32 section of benchmarks/LEDGER.md (empty without wasm32 rows)."""
    if not rows:
        return []
    r = rows[-1]
    k = contract.metric_key
    lines = [
        "## wasm32 vs rustc+LLVM (`benchmarks/wasm-vs-llvm`)",
        "",
        "Rows of the `wasm32` family: the trust-cg wasm32 lane (rustc bridge, `-C opt-level=2`, "
        "`-Ztrust-ir-cg-args=no-proof-certs`, which the lane requires) against **B1** = rustc+LLVM "
        "`-C opt-level=2` without wasm-opt; **B2** = B1 + `wasm-opt -O2` is context only. Ratios are "
        "trust-cg / B1. Contract: `benchmarks/wasm-vs-llvm/contract/contract.json`; thresholds: "
        "`ratchet/perf_baseline.json` (`wasm32_thresholds`). These rows make no proof claim.",
        "",
        f"### Latest wasm32 row ({r['timestamp_utc'][:10]}, `{r['git_sha'][:9]}"
        f"{'-dirty' if r.get('git_dirty') else ''}`, {r.get('host_arch')}, {r.get('engine')})",
        "",
        "This is evidence for the recorded revision and host, not a measurement of the current checkout.",
        "",
        f"- **evidence: {'YES' if r.get('evidence') else 'no'}** ({r.get('load_status')})"
        + ("" if r.get("evidence") else
           "; not evidence: " + "; ".join(str(x) for x in (r.get("ineligible_reasons") or []))),
        f"- **coverage:** {_f(r.get('coverage_pct'), 1)}% ({r.get('match_count')}/{r.get('total_programs')} "
        f"MATCH, {r.get('mismatch_count')} MISMATCH); {r.get('workload_program_count')} programs with a "
        f"workload (dynamic, stack and timing scope); {r.get('soft_signed_zero_total')} signed-zero differences "
        "on exports the corpus manifest lists",
        f"- **size vs B1:** file {_f(r.get(k('file_bytes')))}x, code {_f(r.get(k('code_bytes')))}x, "
        f"static instructions {_f(r.get(k('static_insns')))}x (geomeans); declared locals "
        f"{_f(r.get(k('declared_locals')))}x, static memory ops {_f(r.get(k('static_memops')))}x (totals); "
        f"smaller than B1 on {r.get('wasm_file_bytes_smaller_count')} programs",
        f"- **dynamic vs B1:** instructions {_f(r.get(k('dyn_insns')))}x (geomean); memory ops "
        f"{_f(r.get(k('dyn_memops')))}x, calls {_f(r.get(k('dyn_calls')))}x, stack high-water "
        f"{_f(r.get(k('stack_hwm')))}x (totals); stack above B1 on {r.get('wasm_stack_hwm_worse_count')} programs",
        f"- **time vs B1 (min of N):** default {_f(r.get(k('time_default')))}x, TurboFan "
        f"{_f(r.get(k('time_turbofan')))}x (worst {_f(r.get('wasm_time_turbofan_worst_vs_llvm_o2'))}x), "
        f"Liftoff {_f(r.get(k('time_liftoff')))}x; faster than B1 on "
        f"{r.get('wasm_time_turbofan_faster_count')} programs (TurboFan)",
        f"- **B2 context:** trust-cg / B2 file {_f(r.get(k('file_bytes', contract.B2)))}x, TurboFan "
        f"{_f(r.get(k('time_turbofan', contract.B2)))}x; B2 / B1 file "
        f"{_f(r.get('llvm_o2_wasmopt_file_bytes_geomean_vs_llvm_o2'))}x",
        "",
        "| GATE-WASM-SB (PROPOSED, not owner-approved; reported, never enforced) | status |",
        "|---|---|",
    ]
    gates = r.get("gates_proposed") or {}
    for key, label in GATE_LABELS:
        v = gates.get(key)
        lines.append(f"| {label} | {'PASS' if v else ('fail' if v is not None else '—')} |")
    lines += [
        "",
        "| date (UTC) | sha | arch | evidence | load | match/total | mismatch | file | code | insns | locals "
        "| static mem | dyn insns | dyn mem | dyn calls | stack | default | turbofan | liftoff | B2 file | source |",
        "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|",
    ]
    for r in rows:
        lines.append(
            f"| {r['timestamp_utc'][:10]} | {r['git_sha'][:9]}{'-dirty' if r.get('git_dirty') else ''} "
            f"| {r.get('host_arch')} | {'YES' if r.get('evidence') else 'no'} | {r.get('load_status')} "
            f"| {r.get('match_count')}/{r.get('total_programs')} | {r.get('mismatch_count')} "
            + "".join(f"| {_f(r.get(k(m)))} " for m in RATCHETED)
            + f"| {_f(r.get(k('file_bytes', contract.B2)))} | {r['source_results']}"
            + (f" — NEW LINEAGE: {r['new_lineage'].get('reason')}" if isinstance(r.get("new_lineage"), dict) else "")
            + " |")
    lines.append("")
    return lines
