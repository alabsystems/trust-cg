#!/usr/bin/env python3
"""Compare two beat-llvm results files program by program (Darwin re-measure).

Usage: compare.py <previous results.json> <current results.json>

Prints markdown: the aggregate fields both files carry, then one row per
program with the previous and current value of each ratio the campaign README
reports (runtime vs LLVM -O3, warm and cold compile vs -O2, linked size vs -O3,
compiler peak RSS vs -O2) and the absolute medians behind the runtime ratio.
It reads only the two files; it computes no new statistic beyond the ratio of
current to previous for each value.
"""
import json
import sys

AGG = [
    ("match_count", "MATCH"),
    ("incomplete_count", "INCOMPLETE"),
    ("mismatch_count", "MISMATCH"),
    ("coverage_pct", "coverage %"),
    ("runtime_geomean_vs_llvm_o3", "runtime geomean x -O3"),
    ("runtime_geomean_reliable_only", "runtime, resolvable rows x -O3"),
    ("runtime_reliable_program_count", "resolvable rows"),
    ("scalar_runtime_geomean_vs_llvm_o3", "scalar runtime x -O3"),
    ("runtime_worst_vs_llvm_o3", "worst runtime x -O3"),
    ("compile_warm_geomean_vs_llvm_o2", "warm compile x -O2"),
    ("compile_warm_geomean_vs_llvm_o3", "warm compile x -O3"),
    ("compile_cold_geomean_vs_llvm_o2", "cold compile x -O2"),
    ("size_geomean_vs_llvm_o3", "linked size x -O3"),
    ("size_worst_vs_llvm_o3", "worst linked size x -O3"),
    ("rss_geomean_vs_llvm_o3", "program peak RSS x -O3"),
    ("program_rss_floor_bound_count", "floor-bound programs"),
    ("compile_rss_geomean_vs_llvm_o2", "compiler peak RSS x -O2"),
    ("compile_rss_geomean_vs_llvm_o3", "compiler peak RSS x -O3"),
]


def fmt(v, digits=4):
    if v is None:
        return "null"
    if isinstance(v, float):
        return f"{v:.{digits}f}"
    return str(v)


def run_median(run, lane):
    """Median runtime of one lane of a program's `run` record, or None."""
    return (run.get(lane) or {}).get("median_s")


def main():
    prev = json.load(open(sys.argv[1]))
    cur = json.load(open(sys.argv[2]))
    pa, ca = prev["aggregates"], cur["aggregates"]
    print(f"previous: {sys.argv[1]}\ncurrent:  {sys.argv[2]}\n")
    print("| aggregate | previous | current |\n| --- | ---: | ---: |")
    for key, label in AGG:
        print(f"| {label} | {fmt(pa.get(key))} | {fmt(ca.get(key))} |")
    print()
    print("| category | previous x -O3 | current x -O3 |\n| --- | ---: | ---: |")
    for cat in sorted(set(pa.get("by_category", {})) | set(ca.get("by_category", {}))):
        p = pa.get("by_category", {}).get(cat, {})
        c = ca.get("by_category", {}).get(cat, {})
        print(f"| {cat} | {fmt(p.get('runtime_geomean_vs_llvm_o3'), 3)} | "
              f"{fmt(c.get('runtime_geomean_vs_llvm_o3'), 3)} |")
    print()
    head = ("| program | verdict prev/cur | LLVM -O3 run s prev/cur | bridge run s prev/cur "
            "| runtime x prev -> cur | bridge rel_spread prev/cur | warm x -O2 prev -> cur "
            "| cold x -O2 prev -> cur | size x prev -> cur | compiler RSS x -O2 prev -> cur |")
    print(head)
    print("| --- " + "| ---: " * 9 + "|")
    for name in sorted(set(prev["programs"]) | set(cur["programs"])):
        p = prev["programs"].get(name, {})
        c = cur["programs"].get(name, {})
        pr, cr = p.get("ratios", {}) or {}, c.get("ratios", {}) or {}
        prun, crun = p.get("run", {}) or {}, c.get("run", {}) or {}

        def spread(run):
            try:
                return fmt(run["bridge"]["rel_spread"], 2)
            except (KeyError, TypeError):
                return "-"

        def pair(key, digits=3):
            return f"{fmt(pr.get(key), digits)} -> {fmt(cr.get(key), digits)}"

        print(f"| {name} | {p.get('verdict')}/{c.get('verdict')} "
              f"| {fmt(run_median(prun, 'llvm_o3'))}/{fmt(run_median(crun, 'llvm_o3'))} "
              f"| {fmt(run_median(prun, 'bridge'))}/{fmt(run_median(crun, 'bridge'))} "
              f"| {pair('runtime_vs_llvm_o3')} | {spread(prun)}/{spread(crun)} "
              f"| {pair('compile_warm_vs_llvm_o2')} | {pair('compile_cold_vs_llvm_o2')} "
              f"| {pair('size_vs_llvm_o3', 4)} | {pair('compile_rss_vs_llvm_o2')} |")


if __name__ == "__main__":
    main()
