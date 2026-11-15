#!/usr/bin/env python3
"""Render the README's per-program tables from data/*.json (no measurement)."""
import json
import math
import sys
from pathlib import Path

DATA = Path(__file__).resolve().parents[1] / "data"


def geo(values):
    return math.exp(sum(math.log(v) for v in values) / len(values))


def main():
    attrib = json.loads((DATA / "attrib.json").read_text())
    runtime = json.loads((DATA / "runtime-ab.json").read_text())
    compile_ = json.loads((DATA / "compile-ab.json").read_text())
    print("| program | LLVM -O3 B | before B | after B | before x | after x | +loop-align x "
          "| runtime ms LLVM / before / after | after/before | run instr after/before "
          "| compile Ginstr before / after | after/before | load |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|")
    cols = {k: [] for k in ("sb", "sa", "sl", "rb", "ra", "rab", "iab", "cab")}
    for stem in sorted(attrib):
        a = attrib[stem]
        llvm = a["llvm_o3"]["emitted_bytes"]
        b, af, al = (a[k]["emitted_bytes"] for k in ("before", "after", "after_with_loop_head_align"))
        for lane in ("before", "after", "after_with_loop_head_align"):
            assert a[lane]["exit"] == a["llvm_o3"]["exit"], (stem, lane)
        r = runtime[stem]["lanes"]
        rl, rb, ra = (r[k]["wall_s"] * 1e3 for k in ("llvm_o3", "before", "after"))
        ib, ia = r["before"]["instructions"], r["after"]["instructions"]
        c = compile_[stem]["lanes"]
        cb, ca = c["before"]["instructions"], c["after"]["instructions"]
        load = runtime[stem]["load1"]
        cols["sb"].append(b / llvm); cols["sa"].append(af / llvm); cols["sl"].append(al / llvm)
        cols["rb"].append(rb / rl); cols["ra"].append(ra / rl); cols["rab"].append(ra / rb)
        cols["iab"].append(ia / ib); cols["cab"].append(ca / cb)
        print(f"| {stem} | {llvm} | {b} | {af} | {b / llvm:.3f} | {af / llvm:.3f} | {al / llvm:.3f} "
              f"| {rl:.2f} / {rb:.2f} / {ra:.2f} | {ra / rb:.3f} | {ia / ib:.5f} "
              f"| {cb / 1e9:.4f} / {ca / 1e9:.4f} | {ca / cb:.5f} | {min(load):.1f}-{max(load):.1f} |")
    print(f"| **geomean** | | | | **{geo(cols['sb']):.4f}** | **{geo(cols['sa']):.4f}** "
          f"| {geo(cols['sl']):.4f} | before {geo(cols['rb']):.4f}x, after {geo(cols['ra']):.4f}x LLVM "
          f"| {geo(cols['rab']):.4f} | {geo(cols['iab']):.5f} | | {geo(cols['cab']):.5f} | |")


if __name__ == "__main__":
    sys.exit(main())
