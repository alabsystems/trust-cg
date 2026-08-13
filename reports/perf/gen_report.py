#!/usr/bin/env python3
# GOAL-3 perf-baseline report generator.
#
# Reads reports/perf/results.csv (produced by run_bench.sh) and emits a markdown
# baseline report to a path passed as argv[1]. The note string in the filename is
# fixed by the caller (no Date::now / no wall-clock in the artifact).
#
# Author: Andrew Yates · Copyright 2026 Andrew Yates · License: Apache-2.0
import csv
import sys
import statistics


def f(x):
    try:
        return float(x)
    except (TypeError, ValueError):
        return None


def fmt(x, suffix=""):
    if x is None:
        return "—"
    if isinstance(x, float):
        return f"{x:.1f}{suffix}"
    return f"{x}{suffix}"


def ratio(a, b):
    # a/b, guarding zero/None
    if a is None or b is None or b == 0:
        return None
    return a / b


def main():
    csv_path = sys.argv[1]
    out_path = sys.argv[2]
    note = sys.argv[3] if len(sys.argv) > 3 else "baseline"

    rows = []
    with open(csv_path) as fh:
        for r in csv.DictReader(fh):
            rows.append(r)

    ok = [r for r in rows if r["bridge_status"] == "OK"]
    failed = [r for r in rows if r["bridge_status"] != "OK"]

    # per-row derived metrics for OK rows
    for r in ok:
        r["_lc1"] = f(r["llvm_o1_compile_ms"])
        r["_lc3"] = f(r["llvm_o3_compile_ms"])
        r["_bc"] = f(r["bridge_compile_ms"])
        r["_bcn"] = f(r["bridge_noproof_compile_ms"])
        r["_le1"] = f(r["llvm_o1_exec_ms"])
        r["_le3"] = f(r["llvm_o3_exec_ms"])
        r["_be"] = f(r["bridge_exec_ms"])
        # compile_ratio: bridge / llvm_o1 (apples-to-apples opt level)
        r["_cr"] = ratio(r["_bc"], r["_lc1"])
        # exec_ratio: bridge / llvm_o3 (the real exec-perf gap vs LLVM's best)
        r["_er3"] = ratio(r["_be"], r["_le3"])
        r["_er1"] = ratio(r["_be"], r["_le1"])
        # proof-cert overhead fraction
        if r["_bc"] and r["_bcn"]:
            r["_proof_overhead"] = (r["_bc"] - r["_bcn"]) / r["_bc"]
        else:
            r["_proof_overhead"] = None

    def med(key):
        vals = [r[key] for r in ok if r.get(key) is not None]
        return statistics.median(vals) if vals else None

    lines = []
    A = lines.append
    A(f"# GOAL-3 Performance Baseline — trust-cg x86 bridge vs LLVM ({note})")
    A("")
    A("**Author:** Andrew Yates · **Copyright:** 2026 Andrew Yates · "
      "**License:** Apache-2.0")
    A("")
    A("> MEASUREMENT ONLY. No compiler source was modified. This artifact + the "
      "bench harness (`reports/perf/`) are the only changes on this branch.")
    A("")
    A("## Method")
    A("")
    A("- **Host / target:** `x86_64-apple-darwin` (native execution; host is "
      "x86_64).")
    A("- **Toolchain:** `nightly-2026-04-20` (the bridge's pinned channel).")
    A("- **Base:** `origin/main` (HEAD ~26d1c2b).")
    A("- **Bridge:** release-built `librustc_codegen_trust_cg.dylib`, invoked via "
      "`-Zcodegen-backend=`. The bridge **hard-pins `OptLevel::O1`** "
      "(`lib.rs:1599`); there is no opt-level knob.")
    A("- **Compiler flags (all builds):** `-Coverflow-checks=off "
      "-Ccodegen-units=1 -Cpanic=abort --emit=obj`.")
    A("- **LLVM comparison points:** rustc default backend at `-Copt-level=1` "
      "(apples-to-apples vs the bridge's pinned O1) **and** `-Copt-level=3` "
      "(LLVM's best — the real exec-perf bar).")
    A("- **Compile time:** best-of-3 warm **wall-clock** of the `rustc` "
      "invocation (object emission only, no link).")
    A("- **Exec time:** each object is linked with `cc` (+ abort stubs for "
      "undefined `panic_*` symbols, mirroring the in-tree x86 tests) into a "
      "native Mach-O binary; the binary is run best-of-5 and timed by **child "
      "CPU time (user+sys)**, which is immune to co-scheduled load. Each kernel "
      "self-iterates to a measurable size.")
    A("- **Correctness oracle:** every program returns a checksum via its "
      "process exit code (`checksum & 0xff`). The bridge binary's exit code is "
      "compared against the LLVM binary's; a mismatch is flagged as a "
      "**CORRECTNESS bug**, not a perf result.")
    A("- **Proof-cert overhead:** the bridge runs per-compile proof/gate "
      "machinery **on by default** (`emit_proofs = TCG_NO_PROOF_CERTS unset`, "
      "`lib.rs:1628`). We compile twice — default (proofs ON) and "
      "`TCG_NO_PROOF_CERTS=1` (proofs OFF) — to isolate that cost.")
    A("")
    A(f"**Coverage:** {len(ok)} / {len(rows)} benchmarks compiled through the "
      f"bridge; {len(failed)} failed closed (listed below).")
    A("")

    # ---- main per-benchmark table ----
    A("## Per-benchmark results")
    A("")
    A("Compile times in ms (wall, best-of-3). Exec times in ms (CPU, best-of-5). "
      "`cmp_ratio` = bridge_compile / llvm_O1_compile (>1 = bridge slower to "
      "compile). `exec_ratio` = bridge_exec / llvm_O3_exec (>1 = bridge slower "
      "to run; this is the headline exec gap vs LLVM's best).")
    A("")
    hdr = ("| bench | llvm_c(O1) | llvm_c(O3) | bridge_c | bridge_c(noproof) | "
           "cmp_ratio | llvm_e(O1) | llvm_e(O3) | bridge_e | exec_ratio(vsO3) | "
           "exec_ratio(vsO1) | checksum |")
    A(hdr)
    A("|" + "---|" * 12)
    for r in ok:
        A("| {b} | {lc1} | {lc3} | {bc} | {bcn} | {cr} | {le1} | {le3} | {be} | "
          "{er3} | {er1} | {cs} |".format(
              b=r["bench"],
              lc1=fmt(r["_lc1"]), lc3=fmt(r["_lc3"]),
              bc=fmt(r["_bc"]), bcn=fmt(r["_bcn"]),
              cr=fmt(r["_cr"], "x"),
              le1=fmt(r["_le1"]), le3=fmt(r["_le3"]), be=fmt(r["_be"]),
              er3=fmt(r["_er3"], "x"), er1=fmt(r["_er1"], "x"),
              cs=("OK" if r["checksum_match"] == "YES"
                  else f"**MISMATCH (L={r['llvm_checksum']} "
                       f"B={r['bridge_checksum']})**"),
          ))
    A("")

    # ---- failed/fail-closed ----
    A("## Fail-closed / excluded benchmarks (coverage gaps)")
    A("")
    if not failed:
        A("None — every benchmark compiled through the bridge.")
    else:
        A("| bench | status |")
        A("|---|---|")
        for r in failed:
            A(f"| {r['bench']} | {r['bridge_status']} |")
    A("")
    A("These are excluded from the perf aggregates below (a perf number for a "
      "program the bridge cannot compile is meaningless). The status table "
      "above preserves each specific fail-closed diagnostic.")
    A("")

    # ---- correctness summary ----
    mism = [r for r in ok if r["checksum_match"] != "YES"]
    A("## Correctness")
    A("")
    if mism:
        A(f"**{len(mism)} CHECKSUM MISMATCH(es) — CORRECTNESS BUGS:**")
        for r in mism:
            A(f"- `{r['bench']}`: LLVM={r['llvm_checksum']} "
              f"BRIDGE={r['bridge_checksum']}")
    else:
        A(f"All {len(ok)} compiled benchmarks produced **identical checksums** "
          "under the bridge and LLVM. No miscompiles in this suite.")
    A("")

    # ---- aggregates ----
    A("## Aggregate medians (OK benchmarks only)")
    A("")
    A("| metric | median |")
    A("|---|---|")
    A(f"| llvm compile O1 (ms) | {fmt(med('_lc1'))} |")
    A(f"| llvm compile O3 (ms) | {fmt(med('_lc3'))} |")
    A(f"| bridge compile, proofs ON (ms) | {fmt(med('_bc'))} |")
    A(f"| bridge compile, proofs OFF (ms) | {fmt(med('_bcn'))} |")
    A(f"| **compile ratio** (bridge / llvm O1) | {fmt(med('_cr'), 'x')} |")
    A(f"| llvm exec O1 (ms) | {fmt(med('_le1'))} |")
    A(f"| llvm exec O3 (ms) | {fmt(med('_le3'))} |")
    A(f"| bridge exec (ms) | {fmt(med('_be'))} |")
    A(f"| **exec ratio** (bridge / llvm O3) | {fmt(med('_er3'), 'x')} |")
    A(f"| **exec ratio** (bridge / llvm O1) | {fmt(med('_er1'), 'x')} |")
    po = med("_proof_overhead")
    A(f"| proof-cert compile overhead (frac of bridge compile) | "
      f"{fmt(po*100 if po is not None else None, '%')} |")
    A("")

    # ---- top optimization targets ----
    A("## Top optimization targets (largest exec gap vs LLVM O3)")
    A("")
    A("Ranked by `exec_ratio(vsO3)` descending — these are where AY-proven "
      "optimization passes (regalloc quality, instruction selection, "
      "peephole/strength-reduction, missing O2/O3 passes) buy the most.")
    A("")
    ranked = sorted([r for r in ok if r.get("_er3") is not None],
                    key=lambda r: r["_er3"], reverse=True)
    A("| rank | bench | bridge_e | llvm_e(O3) | exec_ratio(vsO3) | "
      "exec_ratio(vsO1) |")
    A("|---|---|---|---|---|---|")
    for i, r in enumerate(ranked, 1):
        A(f"| {i} | {r['bench']} | {fmt(r['_be'])} | {fmt(r['_le3'])} | "
          f"{fmt(r['_er3'], 'x')} | {fmt(r['_er1'], 'x')} |")
    A("")

    # ---- where bridge is competitive ----
    A("## Where the bridge is already competitive or ahead")
    A("")
    comp_compile = sorted([r for r in ok if r.get("_cr") is not None],
                          key=lambda r: r["_cr"])
    A("**Compile time** (lowest bridge/llvm-O1 compile ratio first):")
    A("")
    A("| bench | bridge_c | llvm_c(O1) | cmp_ratio |")
    A("|---|---|---|---|")
    for r in comp_compile[:6]:
        A(f"| {r['bench']} | {fmt(r['_bc'])} | {fmt(r['_lc1'])} | "
          f"{fmt(r['_cr'], 'x')} |")
    A("")
    best_exec = sorted([r for r in ok if r.get("_er3") is not None],
                       key=lambda r: r["_er3"])
    A("**Exec time** (closest to / ahead of LLVM O3 first):")
    A("")
    A("| bench | bridge_e | llvm_e(O3) | exec_ratio(vsO3) |")
    A("|---|---|---|---|")
    for r in best_exec[:6]:
        A(f"| {r['bench']} | {fmt(r['_be'])} | {fmt(r['_le3'])} | "
          f"{fmt(r['_er3'], 'x')} |")
    A("")

    A("## The honest gap to \"strictly superior to LLVM in compile AND exec\"")
    A("")
    cr_med = med("_cr")
    er3_med = med("_er3")
    A(f"- **Compile:** median bridge/LLVM-O1 compile ratio = "
      f"{fmt(cr_med, 'x')}. " +
      ("The bridge is **faster** to compile than LLVM-O1 at the median."
       if (cr_med is not None and cr_med < 1.0) else
       "The bridge is **slower** to compile than LLVM-O1 at the median; the "
       "per-compile proof/gate machinery is the dominant tax (quantified "
       "above). With proofs OFF the gap narrows."))
    A(f"- **Exec:** median bridge/LLVM-O3 exec ratio = {fmt(er3_med, 'x')}. " +
      ("The bridge already matches/beats LLVM-O3 at the median."
       if (er3_med is not None and er3_med <= 1.05) else
       "LLVM-O3 is faster; closing this is the GOAL-3 exec work (ranked "
       "targets above)."))
    A("- **Coverage** is a precondition for \"strictly superior\": the "
      f"{len(failed)} fail-closed benchmark(s) must first compile at all.")
    A("")
    A("_Generated by `reports/perf/gen_report.py` from `results.csv`._")

    with open(out_path, "w") as fh:
        fh.write("\n".join(lines) + "\n")
    print(f"wrote {out_path}")


if __name__ == "__main__":
    main()
