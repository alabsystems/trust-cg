#!/usr/bin/env python3
# Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
"""Render this record's per-program tables from the measurement JSON.

  tables.py runtime <bench.json> <ref lane> <before lane> <after lane>
      per program: cycles (min and median of the interleaved rounds),
      instructions retired and wall-time minimum, each as a ratio to the
      reference lane (LLVM -O3), with the load range of the rounds
  tables.py size <attrib.json> <before lane> <after lane>
      per program emitted-code bytes (size_attrib.py's definition) and the
      ratio to LLVM -O3, plus geomeans
  tables.py compile <compile.json> <before lane> <after lane>
      per program compiler instructions retired and peak RSS, after / before
  tables.py classes <ref lane> <lane> <bench.json>...
      per program: the lane's cycle ratios to the reference lane (minimum and
      median) in each run, and its class over all of them with the +-0.5%
      noise band: "faster" when every ratio is below 0.995, "slower" when
      every ratio is above 1.005, else "parity or mixed"

The JSON files are this record's measurements (bench.py, size_attrib.py and
ab_measure.py from reports/perf/2026-09-30-darwin-emitted-size/commands).
Numbers are measurements on one loaded host, not proofs.
"""
import json
import math
import sys


def gm(xs):
    return math.exp(sum(math.log(x) for x in xs) / len(xs))


def runtime(path, ref, before, after):
    d = json.load(open(path))
    print(f"| program | {before} cycles min / med | {after} cycles min / med | "
          f"{before} instr | {after} instr | {after} wall min | load |")
    print("|---|---:|---:|---:|---:|---:|---|")
    cols = {k: [] for k in ("bmin", "bmed", "amin", "amed", "bi", "ai", "aw")}
    for p in sorted(d):
        lanes = d[p]["lanes"]
        r, b, a = lanes[ref], lanes[before], lanes[after]
        v = {
            "bmin": b["cycles_min"] / r["cycles_min"],
            "bmed": b["cycles_med"] / r["cycles_med"],
            "amin": a["cycles_min"] / r["cycles_min"],
            "amed": a["cycles_med"] / r["cycles_med"],
            "bi": b["instructions_med"] / r["instructions_med"],
            "ai": a["instructions_med"] / r["instructions_med"],
            "aw": a["wall_s_min"] / r["wall_s_min"],
        }
        for k, x in v.items():
            cols[k].append(x)
        loads = d[p]["load1"]
        mark = " **" if max(v["amin"], v["amed"]) >= 1.0 else ""
        print(f"| {p}{mark} | {v['bmin']:.3f} / {v['bmed']:.3f} | {v['amin']:.3f} / {v['amed']:.3f} | "
              f"{v['bi']:.3f} | {v['ai']:.3f} | {v['aw']:.3f} | {min(loads):.1f}-{max(loads):.1f} |")
    print(f"| **geomean** | {gm(cols['bmin']):.4f} / {gm(cols['bmed']):.4f} | "
          f"{gm(cols['amin']):.4f} / {gm(cols['amed']):.4f} | {gm(cols['bi']):.4f} | "
          f"{gm(cols['ai']):.4f} | {gm(cols['aw']):.4f} | |")


def size(path, before, after):
    d = json.load(open(path))
    print(f"| program | LLVM -O3 B | {before} B | {after} B | {before} x | {after} x |")
    print("|---|---:|---:|---:|---:|---:|")
    rb, ra = [], []
    for p in sorted(d):
        llvm = d[p]["llvm_o3"]["emitted_bytes"]
        b = d[p][before]["emitted_bytes"]
        a = d[p][after]["emitted_bytes"]
        rb.append(b / llvm)
        ra.append(a / llvm)
        print(f"| {p} | {llvm} | {b} | {a} | {b / llvm:.3f} | {a / llvm:.3f} |")
    print(f"| **geomean** | | | | **{gm(rb):.4f}** | **{gm(ra):.4f}** |")


def compile_cost(path, before, after):
    d = json.load(open(path))
    print(f"| program | {before} Ginstr | {after} Ginstr | after/before | peak RSS after/before |")
    print("|---|---:|---:|---:|---:|")
    ri, rr = [], []
    for p in sorted(d):
        b = d[p]["lanes"][before]
        a = d[p]["lanes"][after]
        i = a["instructions"] / b["instructions"]
        r = a["peak_rss"] / b["peak_rss"]
        ri.append(i)
        rr.append(r)
        print(f"| {p} | {b['instructions'] / 1e9:.4f} | {a['instructions'] / 1e9:.4f} | {i:.4f} | {r:.3f} |")
    print(f"| **geomean** | | | **{gm(ri):.4f}** | **{gm(rr):.4f}** |")


BAND = 0.005


def classes(ref, lane, paths):
    runs = [json.load(open(p)) for p in paths]
    heads = " | ".join(f"run {i + 1} min / med" for i in range(len(runs)))
    print(f"| program | {heads} | class |")
    print("|---|" + "---:|" * len(runs) + "---|")
    counts = {}
    for p in sorted(runs[0]):
        vals, cells = [], []
        for d in runs:
            lanes = d[p]["lanes"]
            mn = lanes[lane]["cycles_min"] / lanes[ref]["cycles_min"]
            md = lanes[lane]["cycles_med"] / lanes[ref]["cycles_med"]
            vals += [mn, md]
            cells.append(f"{mn:.3f} / {md:.3f}")
        if max(vals) < 1 - BAND:
            cls = "faster"
        elif min(vals) > 1 + BAND:
            cls = "slower"
        else:
            cls = "parity or mixed"
        counts[cls] = counts.get(cls, 0) + 1
        print(f"| {p} | " + " | ".join(cells) + f" | {cls} |")
    print("| **count** | " + " | ".join("" for _ in runs) + " | "
          + ", ".join(f"{k} {v}" for k, v in sorted(counts.items())) + " |")


def main():
    mode = sys.argv[1]
    if mode == "runtime":
        runtime(*sys.argv[2:6])
    elif mode == "size":
        size(*sys.argv[2:5])
    elif mode == "compile":
        compile_cost(*sys.argv[2:5])
    elif mode == "classes":
        classes(sys.argv[2], sys.argv[3], sys.argv[4:])
    else:
        sys.exit(f"unknown mode {mode}")


if __name__ == "__main__":
    main()
