#!/usr/bin/env python3
"""scripts/check_perf_ratchet.py — BENCH-5 perf ratchet + committed baseline ledger.

The committed institutional memory for performance numbers. One condensed row per
stamped harness run lives in ratchet/ledger.jsonl (append-only, machine-generated —
never hand-typed, so numbers cannot be transcribed optimistically); a human-readable
view is regenerated into benchmarks/LEDGER.md on every append. That generated
view is a local operator artifact and is not part of the public source snapshot.

What it enforces (contract: metrics-contract.md):
  REJECT (exit 1, row never enters the ledger):
    - tcg_env shows a proof-weakening flag (TCG_NO_PROOF_CERTS set, TCG_REFINE_SOLVER=0,
      TCG_NO_PROOF_CACHE set) — the measurement institution must not launder gate-off runs;
    - mandatory provenance fields missing (contract section 8: numbers without stamps
      are not evidence);
    - mismatch_count != 0 — P0 stop-the-line is NOT ratchetable.
    - the stamped size/RSS aggregates disagree with their recomputation from the
      per-program table, or the table does not hold the counted programs.
  RATCHET (exit 1 on regression; thresholds live in ratchet/perf_baseline.json so
  tightening them is an explicit reviewed commit):
    - runtime geomean vs LLVM -O3 regresses more than the noise floor vs the BEST
      committed EVIDENCE row;
    - warm compile geomean vs LLVM -O2 regresses more than its floor;
    - linked size, emitted-code size, program peak-RSS and compiler peak-RSS
      geomeans regress more than their floors;
    - a program gains a resolved peak-RSS loss (more resolved losses than the
      best committed evidence row);
    - coverage_pct drops below the best committed evidence coverage (both
      recomputed from their counts);
    - a metric the baselines measured is missing from the new row.
  Comparisons are like-with-like: baselines are evidence rows of the same host,
  target and program set, and a metric a gates.json version introduced or
  redefined (peak RSS in version 2; emitted-code size and median-of-N peak RSS
  in version 3) is compared only with rows of that version or later. A row
  that measured a --progs subset or used fewer samples than the contract N
  (compile, run, or peak RSS for a row of ledger schema 2) is INCONCLUSIVE
  (exit 2), neither GREEN nor RED.

wasm32 rows: a results file of schema trust-cg-wasm-bench-v2
(benchmarks/wasm-vs-llvm/run.py) goes through scripts/wasm_perf_ratchet.py
instead: its own reject rules (the lane's required no-proof-certs knob is
recorded, every other weakening knob rejected), a `row_family: "wasm32"` row,
deterministic metrics ratcheted with zero tolerance per toolchain, timing per
host and engine, and its own LEDGER.md section. Native and wasm32 rows never
serve as each other's baselines, and the native badge reads native rows only.

Ledger row schema: rows condensed since gates.json version 3 carry
`ledger_row_schema: 2`, `n_rss`, the emitted-code size aggregates and the
peak-RSS sample spreads; older rows have no `ledger_row_schema` (schema 1) and
stay readable: every reader treats a field they lack as unmeasured.
  Evidence = headline_eligible rows only (quiet machine, clean tree, default env/N,
  complete readings, a runnable undegraded proof checker, no backend knob).
  Non-evidence rows are recorded with "evidence": false and are NEVER used as a
  ratchet baseline (a LOADED row has no valid noise floor, contract section 2),
  but they ARE regression-checked: being ineligible never exempts a measured
  regression, which is RED whether or not the row is evidence. While no
  comparable evidence baseline exists the regression check is SKIPPED loudly;
  the reject rules above still run.

Usage:
  check_perf_ratchet.py                     # validate newest benchmarks/beat-llvm/results/*.json
  check_perf_ratchet.py <results.json>      # validate a specific results file
  check_perf_ratchet.py --append <results.json>   # validate, append, and render the local LEDGER.md view
                                                  # (a wasm32 results file is routed to its row family)
  check_perf_ratchet.py --append --new-lineage '<reason>' <results.json>
      # record an explicit decision that a changed contract corpus starts a new
      # baseline lineage for this host/target (corpus or RSS-method change,
      # shown in LEDGER.md); unchanged metrics still use prior baselines
  check_perf_ratchet.py --render                  # re-render LEDGER.md from the ledger (no append)
  check_perf_ratchet.py --check-render            # read-only: is the committed LEDGER.md stale?
      # A renderer change (new columns or gates) leaves the committed view stale
      # until the next --append or --render rewrites it from ratchet/ledger.jsonl.
  check_perf_ratchet.py --check-ledger      # re-validate every committed ledger row
  check_perf_ratchet.py --require-current [<results.json>]
      # additionally require CURRENT-SOURCE ELIGIBLE evidence: the results were
      # measured at this checkout's HEAD, from a tree without tracked edits, the
      # checkout still has no tracked edits, and eligibility recomputed from
      # provenance holds. A row that passes the ratchet can still be stale.

Exit: 0 OK (or regression check skipped — loudly); 1 REJECT/regression/MISMATCH;
      2 tooling error (missing files, unparseable JSON) or INCONCLUSIVE: the results
      are not like-with-like with the evidence baselines (a --progs subset, another
      corpus, or sample counts below the contract N), so they get no regression
      verdict and are not appended; also a full-corpus run whose program set
      differs from every evidence baseline of its host/target (the corpus
      changed) until `--append --new-lineage '<reason>'` records a new lineage
      (programs shared with baselines that kept per-program ratios are still
      compared, and a regression there is RED); 3 not current evidence:
      under --require-current, results that are not current-source eligible
      evidence (a file not measured at HEAD from a clean tree is reported before
      any regression verdict), and always, results that predate the current
      fail-closed aggregates (gates.json version 3: emitted-code size and
      median-of-N peak RSS), which no current harness writes; that includes
      results written under version 2.
"""
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
RESULTS_DIR = REPO / "benchmarks" / "beat-llvm" / "results"
LEDGER = REPO / "ratchet" / "ledger.jsonl"
BASELINE = REPO / "ratchet" / "perf_baseline.json"
LEDGER_MD = REPO / "benchmarks" / "LEDGER.md"
GATES = REPO / "benchmarks" / "beat-llvm" / "contract" / "gates.json"

sys.path.insert(0, str(REPO / "benchmarks" / "beat-llvm" / "contract"))
from check_gates import (  # noqa: E402
    RSS_CONTRACT_N, RSS_FLOOR_BOUND_FACTOR, complete_geomean, evaluate, evidence_eligible,
    full_corpus, gate_verdict, measurement_issues, predates_table_aggregates, program_ratios,
    program_set_sha256, recomputed_view, resource_reading, rss_cross_check, rss_sampler_floor,
    table_issues,
)

# Contract section 8: every one of these provenance fields is mandatory.
MANDATORY_PROVENANCE = [
    "git_sha", "git_dirty", "git_diff_sha256", "untracked_count",
    "dylib_path", "dylib_sha256", "dylib_mtime", "rustc_version", "rustc_path",
    "target", "host_arch", "host_model", "ncpu", "tcg_env", "cache",
    "loadavg_before", "loadavg_after", "load_threshold", "quiet", "load_status",
    "n_compile", "n_run", "warmup_runs", "timestamp_utc", "harness", "schema",
    "dylib_build_command", "cc_version", "linker_version", "os", "aggregation",
    "corpus_manifest_sha256", "provenance_complete",
]

# The wasm32 row family (benchmarks/wasm-vs-llvm): its own reject rules,
# condensed row, ratchet and LEDGER.md section; this script stays the one
# writer of the ledger and its view.
sys.path.insert(0, str(REPO / "scripts"))
import wasm_perf_ratchet as wasm  # noqa: E402

PROOF_WEAKENING = ("TCG_NO_PROOF_CERTS", "TCG_NO_PROOF_CACHE")
# The same opt-outs as tracked backend knobs (-Ztrust-ir-cg-args, recorded as
# provenance.bridge_cg_args): trustc refuses the TCG_* environment, so this is
# how a proof-weakened lane would be spelled now. Boolean spellings follow the
# backend's grammar (rustc-codegen-trust-cg/src/knobs.rs).
KNOB_ON = {None, "1", "true", "on", "yes"}
KNOB_OFF = {"0", "false", "off", "no"}
PROOF_WEAKENING_KNOBS = {"no-proof-certs": KNOB_ON, "no-proof-cache": KNOB_ON,
                         "refine-solver": KNOB_OFF}


def die(code, msg):
    print(f"perf-ratchet: {'REJECT/RED' if code == 1 else 'TOOLING'}: {msg}", file=sys.stderr)
    sys.exit(code)


def _unique_keys(pairs):
    """object_pairs_hook refusing duplicate keys: json.load keeps the last of
    two same-named entries, so a file could carry a hidden second program row."""
    keys = [key for key, _ in pairs]
    duplicates = sorted({key for key in keys if keys.count(key) > 1})
    if duplicates:
        raise ValueError(f"duplicate keys {duplicates}")
    return dict(pairs)


def load_json(p):
    try:
        with open(p, encoding="utf-8") as source:
            return json.load(source, object_pairs_hook=_unique_keys)
    except (OSError, ValueError) as e:
        die(2, f"cannot read {p}: {e}")


def weakening_flags(tcg_env, cg_args=()):
    flags = [k for k in PROOF_WEAKENING if k in tcg_env]
    if tcg_env.get("TCG_REFINE_SOLVER") == "0":
        flags.append("TCG_REFINE_SOLVER=0")
    for arg in cg_args if isinstance(cg_args, (list, tuple)) else [cg_args]:
        # A list that is not a list of strings cannot be shown harmless.
        if not isinstance(arg, str):
            flags.append(f"-Ztrust-ir-cg-args={arg!r}")
            continue
        # trustc documents the value as a space-separated knob list; commas are
        # split too, so no spelling can hide a knob inside a longer item.
        for item in filter(None, re.split(r"[\s,]+", arg)):
            key, _, value = item.partition("=")
            value = value.lower() if "=" in item else None
            if key in PROOF_WEAKENING_KNOBS and value in PROOF_WEAKENING_KNOBS[key]:
                flags.append(f"-Ztrust-ir-cg-args={item}")
    return flags


def validate(results, name):
    """Hard reject rules — apply to every row, evidence or not. Returns list of problems."""
    problems = []
    if not isinstance(results, dict):
        return [f"{name}: results must be an object"]
    prov = results.get("provenance")
    if not isinstance(prov, dict):
        return [f"{name}: no provenance object — numbers without stamps are not evidence"]
    missing = [f for f in MANDATORY_PROVENANCE if f not in prov]
    if missing:
        problems.append(f"{name}: missing mandatory provenance fields {missing}")
    env = prov.get("tcg_env")
    if not isinstance(env, dict):
        problems.append(f"{name}: tcg_env must be an object")
        env = {}
    flags = weakening_flags(env, prov.get("bridge_cg_args") or [])
    if flags:
        problems.append(f"{name}: proof-weakening env/knobs {flags} — gate-off runs are never "
                        f"ledger rows (contract section 1)")
    agg = results.get("aggregates", {})
    if not isinstance(agg, dict):
        return problems + [f"{name}: aggregates must be an object"]
    if agg.get("mismatch_count", 1) != 0:
        problems.append(f"{name}: mismatch_count={agg.get('mismatch_count')} — P0 stop-the-line, "
                        f"not ratchetable")
    problems.extend(f"{name}: {problem}" for problem in measurement_issues(agg))
    problems.extend(f"{name}: {problem}" for problem in table_issues(results))
    return problems


def _identity(value):
    """A host or target identity with cosmetic whitespace removed, so a stray
    space does not read as a different machine (and a new lineage)."""
    return " ".join(value.split()) if isinstance(value, str) else value


# Per-program ratios kept on the ledger row, so a later row whose program set
# changed can still be compared on the programs both measured.
ROW_PROGRAM_METRICS = ("runtime_vs_llvm_o3", "compile_warm_vs_llvm_o2", "size_vs_llvm_o3",
                       "emitted_size_vs_llvm_o3", "rss_vs_llvm_o3", "compile_rss_vs_llvm_o2")
# The condensed row's own format. Schema 2 (gates.json version 3) adds
# `n_rss`, the emitted-code size aggregates and per-program ratio, and the
# peak-RSS sample statistics; a row without the field is schema 1.
LEDGER_ROW_SCHEMA = 2


def _row_program_ratios(results):
    """{program: {metric: exact ratio or None}} over the MATCH rows.

    A program's peak-RSS ratio is None when either reading is at or below the
    floor bound, or the sampler is uncalibrated: a floor-bound comparison
    resolves nothing (gates version 4, ruling OD-32)."""
    floor = rss_sampler_floor(rss_cross_check(results))
    bound = None if floor is None else RSS_FLOOR_BOUND_FACTOR * floor
    out = {}
    for name, row in sorted((results.get("programs") or {}).items()):
        if not isinstance(row, dict) or row.get("verdict") != "MATCH":
            continue
        ratios = program_ratios(row)

        def reading(field, lane, base, resolved_above=None):
            # The recomputed reading: recorded bytes for size, the median of
            # the retained samples for peak RSS (check_gates.resource_reading).
            a, b = resource_reading(row, field, lane), resource_reading(row, field, base)
            if a is None or b is None:
                return None
            if resolved_above is not None and (resolved_above is False
                                               or a <= resolved_above or b <= resolved_above):
                return None
            return a / b

        out[name] = {
            "runtime_vs_llvm_o3": ratios.get("runtime_vs_llvm_o3"),
            "compile_warm_vs_llvm_o2": ratios.get("compile_warm_vs_llvm_o2"),
            "size_vs_llvm_o3": reading("size_bytes", "bridge", "llvm_o3"),
            "emitted_size_vs_llvm_o3": reading("emitted_size_bytes", "bridge", "llvm_o3"),
            "rss_vs_llvm_o3": reading("peak_rss_bytes", "bridge", "llvm_o3",
                                      False if bound is None else bound),
            "compile_rss_vs_llvm_o2": reading("compile_peak_rss_bytes", "bridge", "llvm_o2"),
        }
    return out


def condense(results, source_name):
    """The ledger row: condensed from the results JSON, field-for-field (never hand-typed).
    Aggregates and gate verdicts come from the per-program table's recomputation
    (validate() already refused a stamp that disagrees beyond the tolerance)."""
    results = recomputed_view(results)
    p = results["provenance"]
    a = results["aggregates"]
    gates = load_json(GATES)
    # A gate whose INPUT is absent from the results is UNMEASURED, not failed
    # (check_gates.gate_verdict, shared with the standalone checker): an
    # absent `--cold` lane once read "fail" on every row. The stamped
    # aggregates are exact (validate() checked them against the table), so a
    # threshold is never met by rounding.
    gate_verdicts = {name: gate_verdict(g["predicate"], results)
                     for name, g in gates["gates"].items()}
    noise = compile_noise(results)
    return {
        "ledger_row_schema": LEDGER_ROW_SCHEMA,
        "source_results": source_name,
        "timestamp_utc": p["timestamp_utc"],
        "git_sha": p["git_sha"],
        "git_dirty": p["git_dirty"],
        "dylib_sha256": p["dylib_sha256"],
        "host_arch": _identity(p["host_arch"]),
        "host_model": _identity(p["host_model"]),
        "target": _identity(p["target"]),
        "load_status": p["load_status"],
        "tcg_env": p["tcg_env"],
        # Like-with-like: the program set measured, and whether it is exactly
        # the contract corpus (a `--progs` subset is never evidence).
        "program_set_sha256": program_set_sha256(results.get("programs") or {}),
        "corpus_complete": full_corpus(results),
        "program_ratios": _row_program_ratios(results),
        "bridge_cg_args": p.get("bridge_cg_args") or [],
        "proof_checker_degraded": bool(p.get("proof_checker_degraded")),
        "n_compile": p["n_compile"],
        "n_run": p["n_run"],
        "n_rss": p.get("n_rss"),
        # Recheck the eligibility contract against provenance, rather than
        # trusting a truthy headline stamp on a dirty or loaded run.
        "evidence": evidence_eligible(results, gates["eligibility"]),
        "total_programs": a["total_programs"],
        "match_count": a["match_count"],
        "incomplete_count": a["incomplete_count"],
        "mismatch_count": a["mismatch_count"],
        "nondet_failclosed_count": a.get("nondet_failclosed_count", 0),
        "nondet_candidate_count": a.get("nondet_candidate_count", 0),
        "coverage_pct": a["coverage_pct"],
        "runtime_geomean_vs_llvm_o3": a.get("runtime_geomean_vs_llvm_o3"),
        "scalar_runtime_geomean_vs_llvm_o3": a.get("scalar_runtime_geomean_vs_llvm_o3"),
        "runtime_worst_vs_llvm_o3": a.get("runtime_worst_vs_llvm_o3"),
        "compile_warm_geomean_vs_llvm_o2": a.get("compile_warm_geomean_vs_llvm_o2"),
        "compile_warm_geomean_vs_llvm_o3": a.get("compile_warm_geomean_vs_llvm_o3"),
        "compile_cold_geomean_vs_llvm_o2": a.get("compile_cold_geomean_vs_llvm_o2"),
        "size_geomean_vs_llvm_o3": a.get("size_geomean_vs_llvm_o3"),
        "rss_geomean_vs_llvm_o3": a.get("rss_geomean_vs_llvm_o3"),
        # Size and peak RSS (gates.json version 2), condensed as stamped; the
        # stamp was checked against the per-program table by `validate`.
        "size_worst_vs_llvm_o3": a.get("size_worst_vs_llvm_o3"),
        # Emitted-code size (gates.json version 3): the linked image's code and
        # read-only data the linker map attributes to the program's objects.
        "emitted_size_geomean_vs_llvm_o3": a.get("emitted_size_geomean_vs_llvm_o3"),
        "emitted_size_worst_vs_llvm_o3": a.get("emitted_size_worst_vs_llvm_o3"),
        "compile_rss_geomean_vs_llvm_o2": a.get("compile_rss_geomean_vs_llvm_o2"),
        "compile_rss_geomean_vs_llvm_o3": a.get("compile_rss_geomean_vs_llvm_o3"),
        "resource_measurement_complete": a.get("resource_measurement_complete"),
        "rss_floor_bound_bytes": a.get("rss_floor_bound_bytes"),
        "program_rss_floor_bound_count": a.get("program_rss_floor_bound_count"),
        "program_rss_resolved_loss_count": a.get("program_rss_resolved_loss_count"),
        "program_rss_resolved_losses": a.get("program_rss_resolved_losses"),
        "compile_rss_floor_bound_count": a.get("compile_rss_floor_bound_count"),
        # Median-of-N peak RSS (gates.json version 3): the fewest samples behind
        # any reading, and the largest relative sample spread per kind.
        "rss_min_samples": a.get("rss_min_samples"),
        "program_rss_max_rel_spread": a.get("program_rss_max_rel_spread"),
        "compile_rss_max_rel_spread": a.get("compile_rss_max_rel_spread"),
        **parity_provenance(results),
        "gates_version": gates.get("version", 1),
        "gates": gate_verdicts,
        # BENCH-11: the row's own compile noise, so a gate decided within it is
        # labelled as such rather than read as a fact (see `compile_noise`).
        "compile_noise_spread_geomean": noise["spread_geomean"],
        "compile_geomean_uncertainty_pct": noise["uncertainty_pct"],
        "compile_gate_margins": compile_gate_margins(a, noise["uncertainty_pct"]),
    }


def _pick(value, keys):
    return {key: value.get(key) for key in keys} if isinstance(value, dict) else None


def parity_provenance(results):
    """CPU/target-parity, RSS-sampling and retention provenance for the row.

    Condensed field-for-field from what the harness stamped. A results file
    from a harness that predates these fields condenses to None rather than
    being rejected: whether they are required for evidence is decided by the
    harness's own `provenance_complete` stamp, which `evidence_eligible`
    already checks. Since these fields exist, `host_model` is the CPU model
    (see benchmarks/beat-llvm/hostinfo.py); older rows carry a hostname or a
    machine model there. `legacy_host_model` is the value the older harness
    would have stamped on the same host, so `comparable` can keep matching a
    CPU-model row to those baselines (see `ratchet_check`).
    """
    p = results.get("provenance") or {}
    features = p.get("cpu_features")
    rss = p.get("rss_sampling")
    cross = rss.get("cross_check") if isinstance(rss, dict) else None
    retention = results.get("retention")
    return {
        "host_model_source": p.get("host_model_source"),
        "machine_model": p.get("machine_model"),
        "legacy_host_model": p.get("legacy_host_model"),
        "cpu_features_count": len(features) if isinstance(features, list) else None,
        "cpu_features_sha256": p.get("cpu_features_sha256"),
        "cpu_policy": _pick(p.get("cpu_policy"), (
            "target_cpu", "target_feature", "lane_parity", "llvm_default_target_cpu")),
        "affinity": _pick(p.get("affinity"), ("policy", "core", "selection", "heterogeneous")),
        "rss_sampling": None if not isinstance(rss, dict) else {
            "method": rss.get("method"),
            "method_id": rss.get("method_id"),
            "sampler_identity": _pick(rss.get("sampler_identity"), (
                "source_sha256", "binary_sha256")),
            "ru_maxrss_unit": rss.get("ru_maxrss_unit"),
            "sampler_floor_bytes": cross.get("sampler_floor_bytes") if isinstance(cross, dict) else None,
            "cross_check_agree": cross.get("agree") if isinstance(cross, dict) else None,
        },
        "retained_dir": retention.get("dir") if isinstance(retention, dict) else None,
    }


# The two compile gates whose value the noise estimate qualifies. gates.json
# stays the authority for the VERDICT; this only says how far from the line the
# value sits relative to the row's own measurement noise.
COMPILE_GATE_THRESHOLDS = {
    "G2_M1_compile_warm_vs_O2": ("compile_warm_geomean_vs_llvm_o2", 1.00),
    "G2_endstate_compile_warm_vs_O3": ("compile_warm_geomean_vs_llvm_o3", 1.00),
}


def compile_noise(results):
    """Within-row compile-time noise, from data the row already carries.

    Every program's warm bridge lane is N (default 3) timed compiles; the
    per-program ratio is a median of those. The max/min spread of the N times
    is a per-program noise indicator; its geomean over the corpus is stamped as
    `compile_noise_spread_geomean`. A crude uncertainty for the corpus geomean
    of medians follows: each median is uncertain by about half the spread, and
    the geomean of P independent programs shrinks that by sqrt(P):
        uncertainty_pct ~= ((spread_geomean - 1) / 2) / sqrt(P) * 100
    Measured on this box (identical dylibs, n=25 interleaved) the within-run
    resolution is ~1%, which is what this formula gives for spread ~1.09 over
    18 programs. Between-run drift is LARGER (~3%) and is not captured here —
    compare rows, not one row, for anything under that."""
    import math
    programs = results.get("programs") or {}
    items = programs.items() if isinstance(programs, dict) else [(x.get("name") or x.get("stem"), x) for x in programs]
    spreads = []
    for _, row in items:
        times = (((row or {}).get("compile") or {}).get("bridge_warm") or {}).get("times_s") or []
        times = [t for t in times if t]
        if len(times) >= 2:
            spreads.append(max(times) / min(times))
    if not spreads:
        return {"spread_geomean": None, "uncertainty_pct": None}
    spread_geomean = math.exp(sum(math.log(x) for x in spreads) / len(spreads))
    uncertainty_pct = ((spread_geomean - 1) / 2) / math.sqrt(len(spreads)) * 100
    return {"spread_geomean": round(spread_geomean, 3), "uncertainty_pct": round(uncertainty_pct, 2)}


def compile_gate_margins(aggregates, uncertainty_pct):
    """For each compile gate: how far the row's value is from the threshold, in
    percent, and whether that distance is inside the row's own uncertainty."""
    out = {}
    for gate, (metric, threshold) in COMPILE_GATE_THRESHOLDS.items():
        value = aggregates.get(metric)
        if value is None:
            out[gate] = None
            continue
        margin_pct = round((value - threshold) / threshold * 100, 2)
        within = None if uncertainty_pct is None else abs(margin_pct) <= uncertainty_pct
        out[gate] = {"margin_pct": margin_pct, "within_noise": within}
    return out


def read_ledger():
    if not LEDGER.is_file():
        return []
    rows = []
    for i, line in enumerate(LEDGER.read_text().splitlines()):
        if not line.strip():
            continue
        try:
            rows.append(json.loads(line))
        except json.JSONDecodeError as e:
            die(2, f"ledger line {i + 1} unparseable: {e}")
    return rows


def _legacy_identity_row(row):
    """A row condensed before `host_model` named the CPU: its `host_model` is
    the machine identity the harness stamped then (Mac `hw.model`, else the
    hostname), and it has no `host_model_source`."""
    return not row.get("host_model_source")


def comparable(row, baseline):
    """Whether `baseline` measured the same host and target as `row`.

    The identity is (host_arch, host_model, target). When `host_model` became
    the CPU model, committed baselines kept the machine identity they were
    stamped with; a new row matches those through its `legacy_host_model`
    (and an old-format row matches new rows the same way), so changing the
    key never silently drops a host's baselines and skips its regression
    check.
    """
    def key(r, name):
        return _identity(r.get(name))

    if not all(key(row, k) and key(baseline, k) == key(row, k) for k in ("host_arch", "target")):
        return False
    if key(row, "host_model") and key(baseline, "host_model") == key(row, "host_model"):
        return True
    if _legacy_identity_row(baseline) and not _legacy_identity_row(row):
        legacy = key(row, "legacy_host_model")
        return bool(legacy) and key(baseline, "host_model") == legacy
    if _legacy_identity_row(row) and not _legacy_identity_row(baseline):
        legacy = key(baseline, "legacy_host_model")
        return bool(legacy) and key(row, "host_model") == legacy
    return False


# Contract-default sample counts; every evidence baseline has at least these.
MIN_N_COMPILE, MIN_N_RUN, MIN_N_RSS = 3, 5, RSS_CONTRACT_N
# Metrics a gates.json version introduced or redefined: only rows condensed
# under that version or later measured them the same way, so only those rows
# are their baselines. v1 Darwin rows carry a program RSS geomean from
# /usr/bin/time -l; version 2 read one RSS sample per lane; version 3 reads the
# median of RSS_CONTRACT_N samples (with a spread-aware R1 band) and adds
# emitted-code size.
METRIC_MIN_GATES_VERSION = {
    "rss_geomean_vs_llvm_o3": 3,
    "compile_rss_geomean_vs_llvm_o2": 3,
    "program_rss_resolved_loss_count": 3,
    "emitted_size_geomean_vs_llvm_o3": 3,
}


def comparability_problem(row):
    """Why ROW cannot be compared like-with-like against the ledger's evidence
    baselines (all of which measured the whole contract corpus at the contract
    N), or None. Such a row gets no regression verdict either way: it is
    INCONCLUSIVE, never GREEN and never a false RED."""
    if row.get("corpus_complete") is not True:
        return (f"program set is not the contract corpus ({row.get('total_programs')} programs; "
                "a --progs subset or a different corpus)")
    n_compile, n_run = row.get("n_compile"), row.get("n_run")
    if type(n_compile) is not int or type(n_run) is not int:
        return f"sample counts are not integers (compile {n_compile!r}, run {n_run!r})"
    if n_compile < MIN_N_COMPILE or n_run < MIN_N_RUN:
        return (f"sample counts below the contract N (compile {n_compile} < {MIN_N_COMPILE} "
                f"or run {n_run} < {MIN_N_RUN})")
    if (row.get("ledger_row_schema") or 1) >= 2:
        n_rss = row.get("n_rss")
        if type(n_rss) is not int or n_rss < MIN_N_RSS:
            return f"peak-RSS sample count below the contract N ({n_rss!r} < {MIN_N_RSS})"
    return None


def same_program_set(row, baseline):
    """Whether BASELINE measured the program set ROW measured. Rows condensed
    before the digest existed were all full-corpus runs of their time and are
    matched on their program count."""
    if baseline.get("program_set_sha256"):
        return baseline["program_set_sha256"] == row.get("program_set_sha256")
    return baseline.get("total_programs") == row.get("total_programs")


def program_set_label(row):
    """How a row's program set is named in messages and lineage records."""
    return row.get("program_set_sha256") or f"legacy:{row.get('total_programs')}-programs"


def _host_evidence(row, ledger):
    """This host/target's evidence rows (a row recorded as a program subset is
    never one, whatever its evidence stamp)."""
    return [r for r in ledger if r.get("evidence") is True and r.get("corpus_complete") is not False
            and comparable(row, r) and r.get("source_results") != row.get("source_results")]


RSS_METRICS = {"rss_geomean_vs_llvm_o3", "compile_rss_geomean_vs_llvm_o2",
               "program_rss_resolved_loss_count"}


def rss_method(row):
    """Keep old rows' absent method distinct from any explicitly stamped one.

    Use the versioned native method ID. The unchanged Darwin Python path
    matches older rows through its description, which predates method_id.
    Native image hashes are retained
    provenance, not an excuse to drop otherwise comparable RSS baselines.
    """
    sampling = row.get("rss_sampling")
    if not isinstance(sampling, dict):
        return None
    identity = sampling.get("method_id")
    if isinstance(identity, str) and identity and identity != "python-rusage-v1":
        return identity
    return sampling.get("method")


def lineage_problem(row, ledger, new_lineage=None):
    """Why ROW's program set or RSS method cannot be ratcheted against its
    evidence lineage, or None.

    A contract-corpus change (a program added to or removed from
    progs/manifest.json) makes the new rows' program set differ from every
    committed baseline. Comparing them anyway would compare different
    corpora; skipping silently (as a host with no rows at all is skipped)
    would let a regressed row become the first baseline of the new set and
    lock the regression in. So it is INCONCLUSIVE until a new lineage is
    declared explicitly (`--append --new-lineage REASON` on an eligible
    evidence row, recorded on the row and shown by the renderer), after which
    that row is the set's first baseline. Shared programs are still compared
    where baselines carry per-program ratios (ratchet_check)."""
    # Only an EVIDENCE row of the same set settles a lineage: the declaring
    # row must be eligible evidence (main refuses --new-lineage otherwise), so
    # it is the new lineage's baseline. A non-evidence row carrying a
    # declaration settles nothing and cannot be exploited.
    host = _host_evidence(row, ledger)
    if not host or new_lineage:
        return None
    same_set = [r for r in host if same_program_set(row, r)]
    if any(rss_method(row) == rss_method(r) for r in same_set):
        return None
    if same_set:
        return ("RSS sampling method changed against every same-set evidence baseline; "
                "RSS regression is INCONCLUSIVE, and unchanged metrics remain checked. "
                "Declare the new lineage explicitly with --append --new-lineage '<reason>'")
    sets = sorted({program_set_label(r) for r in host})
    return (f"program set changed: this run measured {row.get('total_programs')} programs "
            f"({program_set_label(row)[:16]}), but every evidence baseline of this host/target "
            f"measured another set {[label[:16] for label in sets]}; no baseline can judge it. "
            "Declare the new lineage explicitly with --append --new-lineage '<reason>'")


def shared_program_regressions(row, baselines, thresholds):
    """Regressions over the programs ROW shares with each baseline that kept
    per-program ratios (rows condensed before they existed cannot be compared
    this way). A program-set change never hides a regression on the programs
    both runs measured."""
    current = row.get("program_ratios") or {}
    checks = (
        ("runtime_vs_llvm_o3", "runtime_geomean_vs_llvm_o3", thresholds["runtime_geomean_max_regress_pct"]),
        ("compile_warm_vs_llvm_o2", "compile_warm_geomean_vs_llvm_o2", thresholds["compile_warm_o2_max_regress_pct"]),
        ("size_vs_llvm_o3", "size_geomean_vs_llvm_o3", thresholds["size_geomean_max_regress_pct"]),
        ("emitted_size_vs_llvm_o3", "emitted_size_geomean_vs_llvm_o3",
         thresholds["emitted_size_geomean_max_regress_pct"]),
        ("rss_vs_llvm_o3", "rss_geomean_vs_llvm_o3", thresholds["program_rss_geomean_max_regress_pct"]),
        ("compile_rss_vs_llvm_o2", "compile_rss_geomean_vs_llvm_o2", thresholds["compile_rss_o2_max_regress_pct"]),
    )
    fails = []
    for per_program, aggregate, floor_pct in checks:
        minimum = METRIC_MIN_GATES_VERSION.get(aggregate, 1)
        worst = None
        for base in baselines:
            ratios = base.get("program_ratios")
            if not isinstance(ratios, dict) or (base.get("gates_version") or 1) < minimum:
                continue
            if aggregate in RSS_METRICS and rss_method(row) != rss_method(base):
                continue
            shared = sorted(name for name in ratios if name in current)
            if not shared:
                continue
            base_value = complete_geomean([(ratios[name] or {}).get(per_program) for name in shared])
            if base_value is None:
                continue
            value = complete_geomean([(current[name] or {}).get(per_program) for name in shared])
            if value is None:
                fails.append(f"{aggregate} over the {len(shared)} programs shared with "
                             f"{base.get('source_results')}: not measured")
                continue
            pct = 100.0 * (value - base_value) / base_value
            if worst is None or pct > worst[0]:
                worst = (pct, value, base_value, len(shared), base.get("source_results"))
        if worst and worst[0] > floor_pct:
            pct, value, base_value, count, source = worst
            fails.append(f"{aggregate} over the {count} programs shared with {source}: "
                         f"{_fmt(value, 4)} vs {_fmt(base_value, 4)} — regression {pct:.1f}% > "
                         f"noise floor {floor_pct}%")
    if thresholds.get("program_rss_new_resolved_loss_is_red", True):
        losses = set(row.get("program_rss_resolved_losses") or [])
        for base in baselines:
            ratios = base.get("program_ratios")
            if (not isinstance(ratios, dict)
                    or rss_method(row) != rss_method(base)
                    or (base.get("gates_version") or 1)
                    < METRIC_MIN_GATES_VERSION["program_rss_resolved_loss_count"]
                    or type(base.get("program_rss_resolved_loss_count")) is not int):
                continue
            new = sorted((losses & set(ratios)) - set(base.get("program_rss_resolved_losses") or []))
            if new:
                fails.append(f"program_rss_resolved_losses: new resolved peak-RSS losses {new} on "
                             f"programs shared with {base.get('source_results')}")
    return fails


def exact_coverage(row):
    """Coverage recomputed from the counts: legacy rows stamped it rounded to
    one decimal, so comparing stamps would read an identical 16/18 as a drop."""
    match, total = row.get("match_count"), row.get("total_programs")
    if type(match) is int and type(total) is int and total > 0:
        return 100.0 * match / total
    return row.get("coverage_pct")


def ratchet_check(row, ledger, thresholds):
    """Regression check vs the best committed EVIDENCE rows. Returns list of failures.

    Every validated like-with-like row is checked, evidence or not:
    ineligibility withholds evidence status (the row never becomes a baseline)
    but never exempts a measured regression. A regression on a non-evidence
    full-corpus row at the contract N (loaded host, unusable proof checker,
    incomplete readings, ...) is RED too; rerun on a quiet machine with a
    production configuration to clear it. A row that is not like-with-like
    (`comparability_problem`) is not compared at all: the caller reports it
    INCONCLUSIVE."""
    problem = comparability_problem(row)
    if problem:
        print(f"perf-ratchet: INCONCLUSIVE: {problem} — not comparable with the evidence "
              "baselines; no regression verdict")
        return []
    host = _host_evidence(row, ledger)
    evidence = [r for r in host if same_program_set(row, r)]
    if not row.get("evidence"):
        print("perf-ratchet: row is NOT evidence (load, source, provenance, configuration or "
              "sampling) — it cannot become a baseline, but it is still regression-checked: "
              "a regression is RED whether or not the row is evidence.")
    if not host:
        # Pre-existing behaviour, kept only for a host/target with no evidence
        # row at all: there is nothing to regress against.
        print("perf-ratchet: no comparable committed EVIDENCE baseline for this host/target "
              "— regression check SKIPPED loudly; this row becomes the first "
              "candidate baseline when appended.")
        return []
    if not evidence:
        # The program set changed against this host/target's lineage: compare
        # what both measured; the caller reports the rest INCONCLUSIVE unless a
        # new lineage is declared (lineage_problem).
        print("perf-ratchet: the program set differs from every evidence baseline of this "
              "host/target — comparing the programs they share where baselines kept "
              "per-program ratios.")
        return shared_program_regressions(row, host, thresholds)
    if any(rss_method(row) != rss_method(r) for r in evidence):
        print("perf-ratchet: RSS baselines with another sampling method are not comparable; "
              "runtime, compile time, size and coverage still use the prior evidence baselines. "
              "A method change needs an explicit eligible --new-lineage declaration.")
    fails = []
    checks = [
        ("runtime_geomean_vs_llvm_o3", thresholds["runtime_geomean_max_regress_pct"], min),
        ("compile_warm_geomean_vs_llvm_o2", thresholds["compile_warm_o2_max_regress_pct"], min),
        ("size_geomean_vs_llvm_o3", thresholds["size_geomean_max_regress_pct"], min),
        ("emitted_size_geomean_vs_llvm_o3", thresholds["emitted_size_geomean_max_regress_pct"], min),
        ("rss_geomean_vs_llvm_o3", thresholds["program_rss_geomean_max_regress_pct"], min),
        ("compile_rss_geomean_vs_llvm_o2", thresholds["compile_rss_o2_max_regress_pct"], min),
    ]
    def baselines(metric):
        minimum = METRIC_MIN_GATES_VERSION.get(metric, 1)
        return [r for r in evidence if (r.get("gates_version") or 1) >= minimum
                and (metric not in RSS_METRICS or rss_method(row) == rss_method(r))]

    for metric, floor_pct, best_fn in checks:
        vals = [r[metric] for r in baselines(metric) if r.get(metric) is not None]
        cur = row.get(metric)
        if not vals:
            continue
        if cur is None:
            # The baselines measured it; an evidence row without it cannot
            # show that it did not regress (fail closed, never skipped).
            fails.append(f"{metric}: not measured, but the committed evidence baseline "
                         f"measured it (best {best_fn(vals)})")
            continue
        best = best_fn(vals)
        regress_pct = 100.0 * (cur - best) / best
        if regress_pct > floor_pct:
            fails.append(f"{metric}: {_fmt(cur, 4)} vs best committed {_fmt(best, 4)} — regression "
                         f"{regress_pct:.1f}% > noise floor {floor_pct}%")
    if thresholds.get("program_rss_new_resolved_loss_is_red", True):
        measured = [r for r in baselines("program_rss_resolved_loss_count")
                    if type(r.get("program_rss_resolved_loss_count")) is int]
        cur = row.get("program_rss_resolved_loss_count")
        if measured and cur is None:
            fails.append("program_rss_resolved_loss_count: not measured, but the committed "
                         "evidence baseline measured it")
        elif measured:
            # Identity, not only the count: a loss moving from one program to
            # another is a new loss. Allowed are the losses every best
            # baseline row also had.
            best = min(r["program_rss_resolved_loss_count"] for r in measured)
            allowed = set.intersection(*(set(r.get("program_rss_resolved_losses") or [])
                                         for r in measured
                                         if r["program_rss_resolved_loss_count"] == best))
            new = sorted(set(row.get("program_rss_resolved_losses") or []) - allowed)
            if cur > best or new:
                fails.append(f"program_rss_resolved_loss_count: {cur} vs best committed {best}, "
                             f"new resolved peak-RSS losses {new} — a program's peak RSS "
                             f"now exceeds LLVM's by more than the parity band")
    if thresholds.get("coverage_drop_is_red", True):
        cov_vals = [exact_coverage(r) for r in evidence if exact_coverage(r) is not None]
        cur_cov = exact_coverage(row)
        if cov_vals and cur_cov is not None and cur_cov < max(cov_vals):
            fails.append(f"coverage_pct: {_fmt(cur_cov, 1)}% < best committed {_fmt(max(cov_vals), 1)}% "
                         f"— completeness regression (intent-to-treat denominator)")
    return fails


# The staged-gate badge (BENCH-10 done-criterion b): the LEDGER header auto-renders the
# current gate status so every workstream reads ONE source of truth for "how far from
# strictly-better". Order + human-readable target mirror metrics-contract.md §10 and
# benchmarks/beat-llvm/contract/gates.json (which must never drift from that section).
GATE_BADGE = [
    ("G1a_scalar_runtime_M2", "G1a scalar runtime (M2)", "scalar geomean <= 1.30x LLVM -O3"),
    ("G1b_vectorizable_M5", "G1b vectorizable (M5)", "each kernel <= 2.0x LLVM -O3"),
    ("G1c_GATE_SB_M6", "G1c / GATE-SB (M6)", "geomean < 1.00x AND worst <= 1.50x, coverage >= 80%"),
    ("G2_M1_compile_warm_vs_O2", "G2-M1 compile warm (M1)", "warm geomean <= 1.00x LLVM -O2"),
    ("G2_M1_compile_cold_vs_O2", "G2-M1 compile cold (M1)", "cold geomean <= 2.00x LLVM -O2"),
    ("G2_endstate_compile_warm_vs_O3", "G2 end-state warm", "warm geomean < 1.00x LLVM -O3"),
    ("G5_coverage_M6", "G5 coverage (M6)", "intent-to-treat coverage >= 80%"),
    ("S1_size_linked_parity_vs_O3", "S1 size parity", "linked file bytes geomean <= 1.10x LLVM -O3"),
    ("S2_size_linked_SB_vs_O3", "S2 size strictly-better", "linked file bytes geomean <= 1.00x LLVM -O3"),
    ("S3_size_emitted_parity_vs_O3", "S3 emitted size parity",
     "emitted-code bytes geomean <= 1.10x LLVM -O3"),
    ("S4_size_emitted_SB_vs_O3", "S4 emitted size strictly-better",
     "emitted-code bytes geomean <= 1.00x LLVM -O3"),
    ("R1_program_rss_no_resolved_loss", "R1 program peak RSS",
     "no program's median above LLVM -O3's beyond max(5%, 2x spread); unmeasured unless every "
     "program is above 2x the sampler floor"),
    ("R2_compile_rss_parity_vs_O2", "R2 compiler peak RSS",
     "geomean of medians <= 1.00x LLVM -O2, no floor-bound reading"),
]


def _assert_badge_matches_contract():
    """Fail loudly if GATE_BADGE and gates.json disagree.

    The comment above has always said these must never drift, but nothing
    checked, and they did: G2_M1_compile_cold_vs_O2 was defined in gates.json and
    stamped on every ledger row while the badge omitted it, so the rendered table
    silently showed 6 of 7 staged gates and read as more complete than it was.
    """
    contract = GATES
    try:
        declared = set(json.loads(contract.read_text(encoding="utf-8"))["gates"])
    except (OSError, ValueError, KeyError) as error:
        raise SystemExit(f"check_perf_ratchet: cannot read {contract}: {error}") from None
    badge = {key for key, _, _ in GATE_BADGE}
    if badge != declared:
        missing = ", ".join(sorted(declared - badge)) or "none"
        extra = ", ".join(sorted(badge - declared)) or "none"
        raise SystemExit(
            "check_perf_ratchet: GATE_BADGE has drifted from "
            f"{contract}\n  in gates.json but not the badge: {missing}"
            f"\n  in the badge but not gates.json: {extra}"
        )


def _fmt(value, digits=3):
    """Display rounding for the rendered view; ledger rows keep exact values."""
    if isinstance(value, float):
        return str(round(value, digits))
    return str(value)


def _badge_block(ledger):
    """Render historical staged-gate status from the latest recorded row.
    Gate verdicts are only headline-valid on an `evidence: YES` row; on a non-evidence
    row they are provisional and are labelled as such (never overstated)."""
    if not ledger:
        return ["## Latest recorded measurement", "", "_no rows yet — run the harness and append._", ""]
    r = ledger[-1]
    ev = bool(r.get("evidence"))
    gates = r.get("gates", {}) or {}
    rt = r.get("runtime_geomean_vs_llvm_o3")
    worst = _fmt(r.get("runtime_worst_vs_llvm_o3"))
    scal = r.get("scalar_runtime_geomean_vs_llvm_o3")
    scal = None if scal is None else _fmt(scal)
    # A null aggregate is unmeasured (every row refused, or the lane absent),
    # never the string "None".
    cw2, cw3 = (r.get(k) for k in ("compile_warm_geomean_vs_llvm_o2",
                                   "compile_warm_geomean_vs_llvm_o3"))
    cw2 = "not measured" if cw2 is None else f"{_fmt(cw2)}x"
    cw3 = "not measured" if cw3 is None else f"{_fmt(cw3)}x"
    unc = r.get("compile_geomean_uncertainty_pct")
    margins = r.get("compile_gate_margins") or {}
    cov = r.get("coverage_pct")
    # plain-language runtime standing vs LLVM -O3 (honest, data-driven — never rounded to a win)
    if rt is None:
        standing = "no runtime geomean recorded"
    elif rt < 1.0:
        standing = f"{_fmt(rt)}x — geomean *faster* than LLVM -O3 (but worst {worst}x; GATE-SB needs worst <= 1.50x)"
    else:
        standing = f"{_fmt(rt)}x — LLVM -O3 is {_fmt(rt)}x faster on the geomean (parity gap {round((rt - 1) * 100)}%)"
    lines = [
        f"## Latest recorded measurement ({r['timestamp_utc'][:10]}, "
        f"`{r['git_sha'][:9]}{'-dirty' if r.get('git_dirty') else ''}`, {r.get('host_arch')}"
        + (f", `{r['target']}`" if r.get("target") else "") + ")",
        "",
        "This is evidence for the recorded revision and host, not a measurement of the current checkout.",
        "",
        f"- **evidence: {'YES' if ev else 'no'}** ({r.get('load_status')}"
        + ("" if ev else " / ineligible provenance or sampling — gate verdicts below are PROVISIONAL, "
                        "tracking-only, never headline") + ")",
        f"- **runtime vs LLVM -O3:** {standing}"
        + (f"; scalar {scal}x" if scal is not None else ""),
        f"- **compile (warm) vs LLVM -O2:** {cw2}  ·  **vs -O3:** {cw3}"
        + (f"  ·  ±{unc}% within-row noise (BENCH-11; between-run drift is larger, ~3% on this box)"
           if unc is not None else ""),
        f"- **coverage:** {_fmt(cov, 1)}% ({r.get('match_count')}/{r.get('total_programs')} MATCH, "
        f"{r.get('mismatch_count')} MISMATCH); **distance to strictly-better (GATE-SB):** "
        "geomean < 1.00x AND every benchmark <= 1.50x at coverage >= 80%",
        "",
        "| staged gate | target (contract §10) | status |",
        "|---|---|---|",
    ]
    for key, label, target in GATE_BADGE:
        v = gates.get(key)
        mark = "PASS" if v else ("fail" if v is not None else "—")
        m = margins.get(key)
        if isinstance(m, dict):
            sign = "+" if m["margin_pct"] >= 0 else ""
            mark += f" ({sign}{m['margin_pct']}% from the line"
            mark += ", WITHIN this row's noise)" if m.get("within_noise") else ")"
        lines.append(f"| {label} | {target} | {mark} |")
    lines += [
        "",
        "> Badge reflects the latest recorded row only. A gate is headline-valid solely on an "
        "`evidence: YES` row (quiet machine, clean tree, at least 3 compiles/5 runs, 0 MISMATCH — "
        "the eligibility contract). Note `untracked_count` is recorded separately from "
        "`git_dirty`, so untracked files do not disqualify a row.",
        "",
    ]
    return lines


def render_md(ledger):
    """The view of every row: the native rows' badge and table, then the
    wasm32 family's section (absent while the ledger has no wasm32 row)."""
    wasm_rows = [r for r in ledger if wasm.is_wasm_row(r)]
    ledger = [r for r in ledger if not wasm.is_wasm_row(r)]
    lines = [
        "# benchmarks/LEDGER.md — generated local perf ledger view (BENCH-5)",
        "",
        "**Machine-generated** from `ratchet/ledger.jsonl` by `scripts/check_perf_ratchet.py "
        "--append` — never edit by hand (rows are condensed field-for-field from provenance-"
        "stamped results JSONs; hand-typed numbers are not evidence).",
        "",
        "`evidence: no` rows (load, source, provenance, or sampling restrictions) are context only —",
        "they are never ratchet baselines and never headline-eligible. Contract: "
        "`metrics-contract.md`; ratchet thresholds: `ratchet/perf_baseline.json`.",
        "",
    ]
    lines += _badge_block(ledger)
    lines += [
        "| date (UTC) | sha | arch | evidence | load | coverage | match/total | mismatch | nondet FC/cand | runtime geomean | scalar | worst | warm x-O2 | size | emitted size | rss | compile rss x-O2 | source |",
        "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|",
    ]
    for r in ledger:
        lines.append(
            f"| {r['timestamp_utc'][:10]} | {r['git_sha'][:9]}{'-dirty' if r['git_dirty'] else ''} "
            f"| {r['host_arch']} | {'YES' if r['evidence'] else 'no'} | {r['load_status']} "
            f"| {_fmt(r['coverage_pct'], 1)}% | {r['match_count']}/{r['total_programs']} "
            f"| {r['mismatch_count']} | {r['nondet_failclosed_count']}/{r.get('nondet_candidate_count', 0)} "
            f"| {_fmt(r.get('runtime_geomean_vs_llvm_o3'))} | {_fmt(r.get('scalar_runtime_geomean_vs_llvm_o3'))} "
            f"| {_fmt(r.get('runtime_worst_vs_llvm_o3'))} | {_fmt(r.get('compile_warm_geomean_vs_llvm_o2'))} "
            f"| {_fmt(r.get('size_geomean_vs_llvm_o3'))} "
            f"| {_fmt(r.get('emitted_size_geomean_vs_llvm_o3'))} | {_fmt(r.get('rss_geomean_vs_llvm_o3'))} "
            f"| {_fmt(r.get('compile_rss_geomean_vs_llvm_o2'))} | {r['source_results']}"
            + (f" — NEW LINEAGE: {r['new_lineage'].get('reason')}"
               if isinstance(r.get("new_lineage"), dict) else "") + " |")
    lines.append("")
    lines += wasm.render_section(wasm_rows)
    return "\n".join(lines)


NOT_CURRENT_EXIT = 3
INCONCLUSIVE_EXIT = 2


def current_source(repo=REPO):
    """HEAD and the tracked edits the harness would stamp as git_dirty."""
    def git(*args):
        try:
            result = subprocess.run(["git", "-C", str(repo), *args], capture_output=True,
                                    text=True, timeout=60, check=False)
        except (OSError, subprocess.TimeoutExpired) as error:
            die(2, f"cannot identify the current source: {error}")
        if result.returncode != 0:
            die(2, f"cannot identify the current source: git {' '.join(args)}: {result.stderr.strip()}")
        return result.stdout

    head = git("rev-parse", "HEAD").strip()
    # benchmarks/beat-llvm/run.py stamps git_dirty from non-"??" porcelain lines.
    edits = [line for line in git("status", "--porcelain").splitlines()
             if line.strip() and not line.startswith("??")]
    return head, edits


def current_evidence_problems(results, head, edits, eligibility):
    """Why RESULTS are not current-source eligible evidence; empty when they are."""
    problems = stale_source_problems(results, head, edits)
    if not evidence_eligible(results, eligibility):
        problems.append("results are not headline-eligible evidence (recomputed from provenance)")
    return problems


def stale_source_problems(results, head, edits):
    """Why RESULTS did not measure the current source (HEAD, no tracked edits)."""
    provenance = results.get("provenance") if isinstance(results, dict) else None
    provenance = provenance if isinstance(provenance, dict) else {}
    problems = []
    measured = provenance.get("git_sha")
    if measured != head:
        problems.append(f"measured source {measured!r} is not HEAD {head}")
    if provenance.get("git_dirty") is not False:
        problems.append("measured tree had tracked edits (or no git_dirty stamp)")
    if edits:
        problems.append(f"checkout has {len(edits)} tracked edit(s), so HEAD is not the "
                        f"current source (first: {edits[0].strip()})")
    return problems


def newest_results():
    if not RESULTS_DIR.is_dir():
        die(2, f"no results dir: {RESULTS_DIR}")
    files = sorted(RESULTS_DIR.glob("*.json"))  # excludes mismatch/ (quarantine subdir)
    if not files:
        die(2, f"no results JSONs in {RESULTS_DIR} — run benchmarks/beat-llvm/run.py first")
    return max(files, key=lambda p: p.stat().st_mtime)



def restamp_unmeasured(dry_run):
    """Flip a stamped `false` to `null` on rows where the gate's input was never
    produced.

    Before the verdict fix above, `bool(evaluate(...))` stamped an ABSENT input
    as a failed gate. The rows already in the ledger carry that frozen `false`,
    and `render_md` draws the badge from the row's stamp — so the fix alone
    leaves the committed table wrong. This is the narrowest correction that is
    sound from row data alone: a gate whose every predicate input is `None` ON
    THE ROW is unmeasured, and only that stamp changes. Nothing is recomputed
    from partial data — a gate whose input IS present keeps its stamp exactly.
    """
    gates = load_json(GATES)["gates"]
    fields = {name: set(re.findall(r"\.aggregates\.([A-Za-z0-9_]+)", g["predicate"]))
              for name, g in gates.items()}
    ledger = [json.loads(line) for line in LEDGER.read_text(encoding="utf-8").splitlines() if line.strip()]
    changes = []
    for i, row in enumerate(ledger):
        if wasm.is_wasm_row(row):
            continue
        for name, fs in fields.items():
            stamped = row.get("gates", {}).get(name)
            # "Unmeasured" means the row CONDENSES this input as a column and it is
            # None — the harness ran but never produced it. A field that is not a
            # row column at all (G1b's vectorizable_worst, G1a's scalar geomean on
            # pre-category rows) was measured from the results JSON and simply not
            # condensed; its stamp is real and must stand.
            if stamped is not None and fs and all(f in row and row[f] is None for f in fs):
                changes.append((i, row.get("git_sha", "?")[:9], name, stamped))
                if not dry_run:
                    row["gates"][name] = None
    for i, sha, name, old in changes:
        print(f"perf-ratchet: restamp row {i} {sha} {name}: {json.dumps(old)} -> null (input never produced)")
    if not changes:
        print("perf-ratchet: restamp: no unmeasured-as-failed stamps found")
        return 0
    if dry_run:
        print(f"perf-ratchet: restamp DRY RUN — {len(changes)} stamp(s) would change, nothing written")
        return 0
    with LEDGER.open("w", encoding="utf-8") as f:
        for row in ledger:
            f.write(json.dumps(row, sort_keys=True) + "\n")
    LEDGER_MD.write_text(render_md(ledger) + "\n")
    print(f"perf-ratchet: restamped {len(changes)} stamp(s); rewrote {LEDGER.relative_to(REPO)} and {LEDGER_MD.relative_to(REPO)}")
    return 0


def main():
    # Before anything renders: the badge is the ONE source of truth every
    # workstream reads, so a badge that silently omits a staged gate is worse
    # than no badge.
    _assert_badge_matches_contract()

    args = sys.argv[1:]
    if "--check-render" in args:
        # Read-only: whether the committed view matches what --render (and the
        # next --append) would write. A renderer change leaves the committed
        # LEDGER.md stale until then; this reports it without writing.
        rendered = render_md(read_ledger()) + "\n"
        current = LEDGER_MD.read_text(encoding="utf-8") if LEDGER_MD.is_file() else ""
        if current == rendered:
            print(f"perf-ratchet: {LEDGER_MD.relative_to(REPO)} matches the renderer")
            return 0
        print(f"perf-ratchet: {LEDGER_MD.relative_to(REPO)} is STALE against the renderer; "
              "the next --append (or --render) rewrites it", file=sys.stderr)
        sys.exit(1)
    if "--render" in args:
        ledger = read_ledger()
        LEDGER_MD.write_text(render_md(ledger) + "\n")
        print(f"perf-ratchet: rendered {LEDGER_MD.relative_to(REPO)} ({len(ledger)} rows)")
        return 0
    new_lineage = None
    for index, arg in enumerate(list(args)):
        if arg == "--new-lineage":
            if index + 1 >= len(args):
                die(2, "--new-lineage needs a reason")
            new_lineage = args[index + 1]
            args = args[:index] + args[index + 2:]
            break
        if arg.startswith("--new-lineage="):
            new_lineage = arg.split("=", 1)[1]
            args = args[:index] + args[index + 1:]
            break
    if new_lineage is not None and not new_lineage.strip():
        die(2, "--new-lineage needs a non-empty reason (it is recorded on the ledger row)")
    append = "--append" in args
    if new_lineage is not None and not append:
        die(2, "--new-lineage records a decision on the appended row; use it with --append")
    if "--restamp-unmeasured" in args:
        return restamp_unmeasured(dry_run="--dry-run" in args)
    check_ledger = "--check-ledger" in args
    require_current = "--require-current" in args
    args = [a for a in args if not a.startswith("--")]

    thresholds = load_json(BASELINE)["thresholds"] if BASELINE.is_file() else None
    if thresholds is None:
        die(2, f"missing {BASELINE} — the ratchet has no committed thresholds")

    ledger = read_ledger()

    if check_ledger:
        bad = 0
        for r in ledger:
            if wasm.is_wasm_row(r):
                problems = wasm.row_problems(r, weakening_flags)
                if problems:
                    print(f"perf-ratchet: LEDGER ROW INVALID {r.get('source_results')}: {'; '.join(problems)}")
                    bad += 1
                continue
            problems = measurement_issues(r)
            if problems:
                print(f"perf-ratchet: LEDGER ROW INVALID {r.get('source_results')}: {'; '.join(problems)}")
                bad += 1
            flags = weakening_flags(r.get("tcg_env", {}) or {}, r.get("bridge_cg_args") or [])
            if flags:
                print(f"perf-ratchet: LEDGER ROW INVALID {r.get('source_results')}: gate-off env {flags}")
                bad += 1
            if r.get("mismatch_count", 1) != 0:
                print(f"perf-ratchet: LEDGER ROW INVALID {r.get('source_results')}: mismatch_count != 0")
                bad += 1
        print(f"perf-ratchet: ledger check — {len(ledger)} rows, {bad} invalid; "
              f"{sum(1 for r in ledger if r.get('evidence'))} recorded evidence rows")
        print("perf-ratchet: checked condensed metrics and proof-weakening flags; "
              "historical eligibility and raw samples are not revalidated")
        sys.exit(1 if bad else 0)

    rpath = Path(args[0]) if args else newest_results()
    results = load_json(rpath)
    if wasm.is_wasm_results(results):
        return wasm_main(results, rpath, ledger, append=append, new_lineage=new_lineage,
                         require_current=require_current)
    if predates_table_aggregates(results):
        # A results file from before the recomputed aggregates cannot be
        # condensed. The hard REJECT rules still apply to it — a MISMATCH is
        # P0 in any format — and otherwise it is stale, not a regression:
        # missing current evidence (exit 3).
        hard = [problem for problem in validate(results, rpath.name)
                if "predate the recomputed" not in problem]
        if hard:
            for problem in hard:
                print(f"perf-ratchet: REJECT: {problem}", file=sys.stderr)
            sys.exit(1)
        print(f"perf-ratchet: NOT CURRENT: {rpath.name} predates the recomputed fail-closed "
              "aggregates of gates.json version 3 (emitted-code size, median-of-N peak RSS); "
              "rerun benchmarks/beat-llvm/run.py", file=sys.stderr)
        sys.exit(NOT_CURRENT_EXIT)
    problems = validate(results, rpath.name)
    if problems:
        for p in problems:
            print(f"perf-ratchet: REJECT: {p}", file=sys.stderr)
        sys.exit(1)

    def not_current(problems):
        for problem in problems:
            print(f"perf-ratchet: NOT CURRENT: {problem}", file=sys.stderr)
        print(f"perf-ratchet: {rpath.name} is not current-source eligible evidence; "
              "rerun benchmarks/beat-llvm/run.py on a quiet machine from the clean "
              "candidate checkout", file=sys.stderr)
        sys.exit(NOT_CURRENT_EXIT)

    if require_current:
        # A file measured at another source says nothing about HEAD, so its
        # staleness is reported before any regression verdict.
        head, edits = current_source()
        stale = stale_source_problems(results, head, edits)
        if stale:
            not_current(stale)

    row = condense(results, rpath.name)
    fails = ratchet_check(row, ledger, thresholds)
    if fails:
        for f in fails:
            print(f"perf-ratchet: RED: {f}", file=sys.stderr)
        print("perf-ratchet: regression vs the committed baseline — do not loosen the "
              "threshold in-run; find the regression or land an explicit reviewed baseline "
              "change (contract section 13).", file=sys.stderr)
        sys.exit(1)
    problem = comparability_problem(row)
    if problem:
        print(f"perf-ratchet: INCONCLUSIVE: {rpath.name}: {problem}; it cannot be compared "
              "like-with-like with the evidence baselines, so it gets no regression verdict "
              "and is not appended. Measure the whole corpus at the contract N.",
              file=sys.stderr)
        sys.exit(INCONCLUSIVE_EXIT)
    if new_lineage is not None and not row.get("evidence"):
        die(2, "--new-lineage needs an eligible EVIDENCE row: the declaring row becomes the new "
               "lineage's first baseline, so a loaded, small-N, subset or otherwise ineligible "
               "run cannot declare one (rerun on a quiet machine)")
    if new_lineage is not None and lineage_problem(row, ledger) is None:
        die(2, "--new-lineage is only for a program-set or RSS-method change against an existing evidence "
               "lineage of this host/target; this row already has a same-set evidence "
               "baseline, or its host/target has no baseline at all")
    problem = lineage_problem(row, ledger, new_lineage)
    if problem:
        print(f"perf-ratchet: INCONCLUSIVE: {rpath.name}: {problem}. Not appended.",
              file=sys.stderr)
        sys.exit(INCONCLUSIVE_EXIT)
    if new_lineage is not None:
        previous = _host_evidence(row, ledger)
        compared = any(isinstance(r.get("program_ratios"), dict)
                       and set(r["program_ratios"]) & set(row.get("program_ratios") or {})
                       for r in previous)
        row["new_lineage"] = {
            "reason": new_lineage.strip(),
            "replaces_program_sets": sorted({program_set_label(r) for r in previous}),
            "replaces_rss_methods": sorted({str(rss_method(r)) for r in previous}),
            "rss_method": rss_method(row),
            # Whether the shared programs could be checked against the old
            # lineage (only rows that kept per-program ratios allow it).
            "shared_programs_compared": compared,
            "declared_utc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        }
        print(f"perf-ratchet: NEW LINEAGE declared for this host/target's corpus/RSS method "
              f"({program_set_label(row)[:16]}): {new_lineage.strip()}")
        if not compared:
            print("perf-ratchet: WARNING: no baseline of the previous lineage kept per-program "
                  "ratios, so this row could not be checked for a regression against it; the "
                  "new lineage's baseline is whatever this row measured.", file=sys.stderr)

    print(f"perf-ratchet: OK {rpath.name} (evidence={row['evidence']}, "
          f"coverage {_fmt(row['coverage_pct'], 1)}%, runtime geomean "
          f"{_fmt(row['runtime_geomean_vs_llvm_o3'], 4)}, "
          f"warm-vs-O2 {_fmt(row['compile_warm_geomean_vs_llvm_o2'], 4)}, "
          f"mismatches {row['mismatch_count']})")

    if require_current:
        stale = current_evidence_problems(results, head, edits, load_json(GATES)["eligibility"])
        if stale:
            not_current(stale)
        print(f"perf-ratchet: CURRENT {rpath.name} measured HEAD {head[:12]} (eligible evidence)")

    if append:
        append_row(row, ledger)
    sys.exit(0)


def append_row(row, ledger):
    """Append ROW (never a duplicate of a recorded source) and re-render the view."""
    if any(r.get("source_results") == row["source_results"] for r in ledger):
        print(f"perf-ratchet: ledger already has a row for {row['source_results']} — not duplicating")
        return
    LEDGER.parent.mkdir(parents=True, exist_ok=True)
    with open(LEDGER, "a") as f:
        f.write(json.dumps(row, sort_keys=True) + "\n")
    ledger.append(row)
    LEDGER_MD.write_text(render_md(ledger) + "\n")
    print(f"perf-ratchet: appended to {LEDGER.relative_to(REPO)} and rendered "
          f"{LEDGER_MD.relative_to(REPO)} ({len(ledger)} rows)")


def wasm_main(results, rpath, ledger, *, append, new_lineage, require_current):
    """A wasm32 results file (benchmarks/wasm-vs-llvm/run.py) through the
    wasm32 row family's rules, with the same exits as a native file."""
    problems = wasm.validate(results, rpath.name, weakening_flags)
    if problems:
        for problem in problems:
            print(f"perf-ratchet: REJECT: {problem}", file=sys.stderr)
        sys.exit(1)
    if require_current:
        head, edits = current_source()
        stale = stale_source_problems(results, head, edits)
        if stale:
            for problem in stale:
                print(f"perf-ratchet: NOT CURRENT: {problem}", file=sys.stderr)
            sys.exit(NOT_CURRENT_EXIT)
    thresholds = (load_json(BASELINE) if BASELINE.is_file() else {}).get("wasm32_thresholds")
    if not isinstance(thresholds, dict):
        die(2, f"{BASELINE} has no wasm32_thresholds — the wasm32 ratchet has no committed thresholds")
    row = wasm.condense(results, rpath.name)
    fails = wasm.ratchet_check(row, ledger, thresholds)
    if fails:
        for f in fails:
            print(f"perf-ratchet: RED: {f}", file=sys.stderr)
        print("perf-ratchet: wasm32 regression vs the committed baseline — find the regression or land "
              "an explicit reviewed baseline change; never loosen the threshold in-run.", file=sys.stderr)
        sys.exit(1)
    problem = wasm.comparability_problem(row)
    if problem:
        print(f"perf-ratchet: INCONCLUSIVE: {rpath.name}: {problem}; not compared and not appended. "
              "Measure the whole corpus at the contract N and modes.", file=sys.stderr)
        sys.exit(INCONCLUSIVE_EXIT)
    if new_lineage is not None and not row["evidence"]:
        die(2, "--new-lineage needs an eligible EVIDENCE row (it becomes the lineage's first baseline)")
    if new_lineage is not None and wasm.lineage_problem(row, ledger) is None:
        die(2, "--new-lineage is only for a program-set change against an existing same-toolchain "
               "evidence lineage")
    problem = wasm.lineage_problem(row, ledger, new_lineage)
    if problem:
        print(f"perf-ratchet: INCONCLUSIVE: {rpath.name}: {problem}. Not appended.", file=sys.stderr)
        sys.exit(INCONCLUSIVE_EXIT)
    if new_lineage is not None:
        row["new_lineage"] = wasm.lineage_record(row, ledger, new_lineage)
    print(f"perf-ratchet: OK {rpath.name} (wasm32, evidence={row['evidence']}, coverage "
          f"{_fmt(row['coverage_pct'], 1)}%, file bytes {_fmt(row['wasm_file_bytes_geomean_vs_llvm_o2'], 4)}x, "
          f"TurboFan {_fmt(row['wasm_time_turbofan_geomean_vs_llvm_o2'], 4)}x B1, "
          f"mismatches {row['mismatch_count']})")
    if require_current and not row["evidence"]:
        for reason in row["ineligible_reasons"]:
            print(f"perf-ratchet: NOT CURRENT: {reason}", file=sys.stderr)
        sys.exit(NOT_CURRENT_EXIT)
    if append:
        append_row(row, ledger)
    sys.exit(0)


if __name__ == "__main__":
    main()
