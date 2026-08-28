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
  RATCHET (exit 1 on regression; thresholds live in ratchet/perf_baseline.json so
  tightening them is an explicit reviewed commit):
    - runtime geomean vs LLVM -O3 regresses more than the noise floor vs the BEST
      committed EVIDENCE row;
    - warm compile geomean vs LLVM -O2 regresses more than its floor;
    - coverage_pct drops below the best committed evidence coverage.
  Evidence = headline_eligible rows only (quiet machine, clean tree, default env/N).
  LOADED / dirty / smoke rows are recorded with "evidence": false and are NEVER used
  as a ratchet baseline (a LOADED row has no valid noise floor, contract section 2).
  While no evidence baseline exists (official quiet-machine baseline TODO), the
  regression check is SKIPPED loudly; the reject rules above still run.

Usage:
  check_perf_ratchet.py                     # validate newest benchmarks/beat-llvm/results/*.json
  check_perf_ratchet.py <results.json>      # validate a specific results file
  check_perf_ratchet.py --append <results.json>   # validate, append, and render the local LEDGER.md view
  check_perf_ratchet.py --render                  # re-render LEDGER.md from the ledger (no append)
  check_perf_ratchet.py --check-ledger      # re-validate every committed ledger row

Exit: 0 OK (or regression check skipped — loudly); 1 REJECT/regression/MISMATCH;
      2 tooling error (missing files, unparseable JSON).
"""
import json
import re
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
from check_gates import evaluate  # noqa: E402  (dependency-free predicate evaluator)

# Contract section 8: every one of these provenance fields is mandatory.
MANDATORY_PROVENANCE = [
    "git_sha", "git_dirty", "git_diff_sha256", "untracked_count",
    "dylib_path", "dylib_sha256", "dylib_mtime", "rustc_version", "rustc_path",
    "target", "host_arch", "host_model", "ncpu", "tcg_env", "cache",
    "loadavg_before", "loadavg_after", "load_threshold", "quiet", "load_status",
    "n_compile", "n_run", "warmup_runs", "timestamp_utc", "harness", "schema",
]

PROOF_WEAKENING = ("TCG_NO_PROOF_CERTS", "TCG_NO_PROOF_CACHE")


def die(code, msg):
    print(f"perf-ratchet: {'REJECT/RED' if code == 1 else 'TOOLING'}: {msg}", file=sys.stderr)
    sys.exit(code)


def load_json(p):
    try:
        return json.load(open(p))
    except (OSError, json.JSONDecodeError) as e:
        die(2, f"cannot read {p}: {e}")


def weakening_flags(tcg_env):
    flags = [k for k in PROOF_WEAKENING if k in tcg_env]
    if tcg_env.get("TCG_REFINE_SOLVER") == "0":
        flags.append("TCG_REFINE_SOLVER=0")
    return flags


def validate(results, name):
    """Hard reject rules — apply to every row, evidence or not. Returns list of problems."""
    problems = []
    prov = results.get("provenance")
    if not isinstance(prov, dict):
        return [f"{name}: no provenance object — numbers without stamps are not evidence"]
    missing = [f for f in MANDATORY_PROVENANCE if f not in prov]
    if missing:
        problems.append(f"{name}: missing mandatory provenance fields {missing}")
    flags = weakening_flags(prov.get("tcg_env", {}) or {})
    if flags:
        problems.append(f"{name}: proof-weakening env {flags} — gate-off runs are never "
                        f"ledger rows (contract section 1)")
    agg = results.get("aggregates", {})
    if agg.get("mismatch_count", 1) != 0:
        problems.append(f"{name}: mismatch_count={agg.get('mismatch_count')} — P0 stop-the-line, "
                        f"not ratchetable")
    return problems


def condense(results, source_name):
    """The ledger row: condensed from the results JSON, field-for-field (never hand-typed)."""
    p = results["provenance"]
    a = results["aggregates"]
    gates = load_json(GATES)
    # A gate whose INPUT is absent from the results is UNMEASURED, not failed.
    # `evaluate` returns False for `.x != null and ...` when `.x` is missing,
    # and `bool()` then stamped that as a fail — so G2_M1_compile_cold_vs_O2
    # read "fail" on every row for as long as nobody passed `--cold`, and the
    # one time it was measured (1.654x vs <= 2.00x) it passed. Stamp None here;
    # the badge renderer already draws None as "—".
    gate_verdicts = {}
    for name, g in gates["gates"].items():
        fields = set(re.findall(r"\.aggregates\.([A-Za-z0-9_]+)", g["predicate"]))
        if fields and all(field in a and a[field] is None for field in fields):
            gate_verdicts[name] = None
        else:
            gate_verdicts[name] = bool(evaluate(g["predicate"], results))
    noise = compile_noise(results)
    return {
        "source_results": source_name,
        "timestamp_utc": p["timestamp_utc"],
        "git_sha": p["git_sha"],
        "git_dirty": p["git_dirty"],
        "dylib_sha256": p["dylib_sha256"],
        "host_arch": p["host_arch"],
        "host_model": p["host_model"],
        "target": p["target"],
        "load_status": p["load_status"],
        "tcg_env": p["tcg_env"],
        "n_compile": p["n_compile"],
        "n_run": p["n_run"],
        "evidence": bool(results.get("headline_eligible", False)),
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
        "gates": gate_verdicts,
        # BENCH-11: the row's own compile noise, so a gate decided within it is
        # labelled as such rather than read as a fact (see `compile_noise`).
        "compile_noise_spread_geomean": noise["spread_geomean"],
        "compile_geomean_uncertainty_pct": noise["uncertainty_pct"],
        "compile_gate_margins": compile_gate_margins(a, noise["uncertainty_pct"]),
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


def ratchet_check(row, ledger, thresholds):
    """Regression check vs the best committed EVIDENCE rows. Returns list of failures."""
    evidence = [r for r in ledger if r.get("evidence")
                and r.get("host_arch") == row.get("host_arch")  # never aggregate across hosts
                and r.get("source_results") != row.get("source_results")]
    if not row.get("evidence"):
        print("perf-ratchet: row is NOT evidence (LOADED/dirty/non-default env or N) — "
              "regression check SKIPPED; reject rules still applied. Official baselines need "
              "a quiet machine.")
        return []
    if not evidence:
        print("perf-ratchet: no committed EVIDENCE baseline yet (official quiet-machine "
              "baseline TODO) — regression check SKIPPED loudly; this row becomes the first "
              "candidate baseline when appended.")
        return []
    fails = []
    checks = [
        ("runtime_geomean_vs_llvm_o3", thresholds["runtime_geomean_max_regress_pct"], min),
        ("compile_warm_geomean_vs_llvm_o2", thresholds["compile_warm_o2_max_regress_pct"], min),
    ]
    for metric, floor_pct, best_fn in checks:
        vals = [r[metric] for r in evidence if r.get(metric) is not None]
        cur = row.get(metric)
        if not vals or cur is None:
            continue
        best = best_fn(vals)
        regress_pct = 100.0 * (cur - best) / best
        if regress_pct > floor_pct:
            fails.append(f"{metric}: {cur} vs best committed {best} — regression "
                         f"{regress_pct:.1f}% > noise floor {floor_pct}%")
    if thresholds.get("coverage_drop_is_red", True):
        cov_vals = [r["coverage_pct"] for r in evidence if r.get("coverage_pct") is not None]
        if cov_vals and row.get("coverage_pct") is not None and row["coverage_pct"] < max(cov_vals):
            fails.append(f"coverage_pct: {row['coverage_pct']}% < best committed {max(cov_vals)}% "
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


def _badge_block(ledger):
    """Render the current staged-gate status from the LATEST committed row (BENCH-10).
    Gate verdicts are only headline-valid on an `evidence: YES` row; on a non-evidence
    row they are provisional and are labelled as such (never overstated)."""
    if not ledger:
        return ["## Current status", "", "_no rows yet — run the harness and append._", ""]
    r = ledger[-1]
    ev = bool(r.get("evidence"))
    gates = r.get("gates", {}) or {}
    rt = r.get("runtime_geomean_vs_llvm_o3")
    worst = r.get("runtime_worst_vs_llvm_o3")
    scal = r.get("scalar_runtime_geomean_vs_llvm_o3")
    cw2 = r.get("compile_warm_geomean_vs_llvm_o2")
    cw3 = r.get("compile_warm_geomean_vs_llvm_o3")
    unc = r.get("compile_geomean_uncertainty_pct")
    margins = r.get("compile_gate_margins") or {}
    cov = r.get("coverage_pct")
    # plain-language runtime standing vs LLVM -O3 (honest, data-driven — never rounded to a win)
    if rt is None:
        standing = "no runtime geomean recorded"
    elif rt < 1.0:
        standing = f"{rt}x — geomean *faster* than LLVM -O3 (but worst {worst}x; GATE-SB needs worst <= 1.50x)"
    else:
        standing = f"{rt}x — LLVM -O3 is {rt}x faster on the geomean (parity gap {round((rt - 1) * 100)}%)"
    lines = [
        f"## Current status — latest committed row ({r['timestamp_utc'][:10]}, "
        f"`{r['git_sha'][:9]}{'-dirty' if r.get('git_dirty') else ''}`, {r.get('host_arch')})",
        "",
        f"- **evidence: {'YES' if ev else 'no'}** ({r.get('load_status')}"
        + ("" if ev else " / dirty tree / non-default N — gate verdicts below are PROVISIONAL, "
                        "tracking-only, never headline") + ")",
        f"- **runtime vs LLVM -O3:** {standing}"
        + (f"; scalar {scal}x" if scal is not None else ""),
        f"- **compile (warm) vs LLVM -O2:** {cw2}x  ·  **vs -O3:** {cw3}x"
        + (f"  ·  ±{unc}% within-row noise (BENCH-11; between-run drift is larger, ~3% on this box)"
           if unc is not None else ""),
        f"- **coverage:** {cov}% ({r.get('match_count')}/{r.get('total_programs')} MATCH, "
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
        "> Badge reflects the latest row only. A gate is headline-valid solely on an "
        "`evidence: YES` row (quiet machine, clean tree, default N=3/5, 0 MISMATCH — "
        "contract §8). The first such row was minted 2026-08-20 (`19489f3a2`). The "
        "long-standing `-dirty` blocker is GONE: the local trust-ir redirect moved out of "
        "the tracked `.cargo/config.toml` into the gitignored `.cargo/local-siblings.toml` "
        "(applied via `scripts/use-local-siblings`), so a clean-tree build path exists and "
        "BENCH-10 is closed. Note `untracked_count` is recorded separately from "
        "`git_dirty`, so untracked files do not disqualify a row.",
        "",
    ]
    return lines


def render_md(ledger):
    lines = [
        "# benchmarks/LEDGER.md — generated local perf ledger view (BENCH-5)",
        "",
        "**Machine-generated** from `ratchet/ledger.jsonl` by `scripts/check_perf_ratchet.py "
        "--append` — never edit by hand (rows are condensed field-for-field from provenance-"
        "stamped results JSONs; hand-typed numbers are not evidence).",
        "",
        "`evidence: no` rows (LOADED machine / dirty tree / non-default N) are context only —",
        "they are never ratchet baselines and never headline-eligible. Contract: "
        "`metrics-contract.md`; ratchet thresholds: `ratchet/perf_baseline.json`.",
        "",
    ]
    lines += _badge_block(ledger)
    lines += [
        "| date (UTC) | sha | arch | evidence | load | coverage | match/total | mismatch | nondet FC/cand | runtime geomean | scalar | worst | warm x-O2 | size | source |",
        "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|",
    ]
    for r in ledger:
        lines.append(
            f"| {r['timestamp_utc'][:10]} | {r['git_sha'][:9]}{'-dirty' if r['git_dirty'] else ''} "
            f"| {r['host_arch']} | {'YES' if r['evidence'] else 'no'} | {r['load_status']} "
            f"| {r['coverage_pct']}% | {r['match_count']}/{r['total_programs']} "
            f"| {r['mismatch_count']} | {r['nondet_failclosed_count']}/{r.get('nondet_candidate_count', 0)} "
            f"| {r.get('runtime_geomean_vs_llvm_o3')} | {r.get('scalar_runtime_geomean_vs_llvm_o3')} "
            f"| {r.get('runtime_worst_vs_llvm_o3')} | {r.get('compile_warm_geomean_vs_llvm_o2')} "
            f"| {r.get('size_geomean_vs_llvm_o3')} | {r['source_results']} |")
    lines.append("")
    return "\n".join(lines)


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
    if "--render" in args:
        ledger = read_ledger()
        LEDGER_MD.write_text(render_md(ledger) + "\n")
        print(f"perf-ratchet: rendered {LEDGER_MD.relative_to(REPO)} ({len(ledger)} rows)")
        return 0
    append = "--append" in args
    if "--restamp-unmeasured" in args:
        return restamp_unmeasured(dry_run="--dry-run" in args)
    check_ledger = "--check-ledger" in args
    args = [a for a in args if not a.startswith("--")]

    thresholds = load_json(BASELINE)["thresholds"] if BASELINE.is_file() else None
    if thresholds is None:
        die(2, f"missing {BASELINE} — the ratchet has no committed thresholds")

    ledger = read_ledger()

    if check_ledger:
        bad = 0
        for r in ledger:
            flags = weakening_flags(r.get("tcg_env", {}) or {})
            if flags:
                print(f"perf-ratchet: LEDGER ROW INVALID {r.get('source_results')}: gate-off env {flags}")
                bad += 1
            if r.get("mismatch_count", 1) != 0:
                print(f"perf-ratchet: LEDGER ROW INVALID {r.get('source_results')}: mismatch_count != 0")
                bad += 1
        print(f"perf-ratchet: ledger check — {len(ledger)} rows, {bad} invalid; "
              f"{sum(1 for r in ledger if r.get('evidence'))} evidence rows")
        sys.exit(1 if bad else 0)

    rpath = Path(args[0]) if args else newest_results()
    results = load_json(rpath)
    problems = validate(results, rpath.name)
    if problems:
        for p in problems:
            print(f"perf-ratchet: REJECT: {p}", file=sys.stderr)
        sys.exit(1)

    row = condense(results, rpath.name)
    fails = ratchet_check(row, ledger, thresholds)
    if fails:
        for f in fails:
            print(f"perf-ratchet: RED: {f}", file=sys.stderr)
        print("perf-ratchet: regression vs the committed baseline — do not loosen the "
              "threshold in-run; find the regression or land an explicit reviewed baseline "
              "change (contract section 13).", file=sys.stderr)
        sys.exit(1)

    print(f"perf-ratchet: OK {rpath.name} (evidence={row['evidence']}, "
          f"coverage {row['coverage_pct']}%, runtime geomean {row['runtime_geomean_vs_llvm_o3']}, "
          f"warm-vs-O2 {row['compile_warm_geomean_vs_llvm_o2']}, "
          f"mismatches {row['mismatch_count']})")

    if append:
        if any(r.get("source_results") == row["source_results"] for r in ledger):
            print(f"perf-ratchet: ledger already has a row for {row['source_results']} — not duplicating")
        else:
            LEDGER.parent.mkdir(parents=True, exist_ok=True)
            with open(LEDGER, "a") as f:
                f.write(json.dumps(row, sort_keys=True) + "\n")
            ledger.append(row)
            LEDGER_MD.write_text(render_md(ledger) + "\n")
            print(f"perf-ratchet: appended to {LEDGER.relative_to(REPO)} and rendered "
                  f"{LEDGER_MD.relative_to(REPO)} ({len(ledger)} rows)")
    sys.exit(0)


if __name__ == "__main__":
    main()
