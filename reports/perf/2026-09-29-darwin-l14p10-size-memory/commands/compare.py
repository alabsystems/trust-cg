#!/usr/bin/env python3
"""Before/after table from two beat-llvm results JSONs (gates.json v3 fields).
Usage: compare.py <before.json> <after.json> > table.md"""
import json
import math
import sys

MIB = 1 << 20
before = json.load(open(sys.argv[1]))
after = json.load(open(sys.argv[2]))


def med(row, field, lane):
    v = (row.get(field) or {}).get(lane)
    return v


def geo(values):
    values = [v for v in values if v]
    return math.exp(sum(math.log(v) for v in values) / len(values)) if values else None


def f(v, d=3):
    return "—" if v is None else f"{v:.{d}f}"


rows = []
print("| program | emitted B LLVM -O3 | emitted B bridge | emitted x | linked x | compiler RSS MiB LLVM -O2 | bridge before | bridge after | x -O2 before | x -O2 after | program RSS x (after) |")
print("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
ratios = {"emitted": [], "linked": [], "crss_b": [], "crss_a": [], "prss": []}
for name in sorted(after["programs"]):
    a, b = after["programs"][name], before["programs"][name]
    el, eb = med(a, "emitted_size_bytes", "llvm_o3"), med(a, "emitted_size_bytes", "bridge")
    ebb = med(b, "emitted_size_bytes", "bridge")
    assert ebb == eb, (name, ebb, eb)  # emitted bytes are unchanged by the RSS work
    sl, sb = med(a, "size_bytes", "llvm_o3"), med(a, "size_bytes", "bridge")
    l2 = med(a, "compile_peak_rss_bytes", "llvm_o2")
    cb, ca = med(b, "compile_peak_rss_bytes", "bridge"), med(a, "compile_peak_rss_bytes", "bridge")
    l2b = med(b, "compile_peak_rss_bytes", "llvm_o2")
    pl, pb = med(a, "peak_rss_bytes", "llvm_o3"), med(a, "peak_rss_bytes", "bridge")
    r = dict(emitted=eb / el if el and eb else None, linked=sb / sl if sl and sb else None,
             crss_b=cb / l2b if cb and l2b else None, crss_a=ca / l2 if ca and l2 else None,
             prss=pb / pl if pb and pl else None)
    for k, v in r.items():
        ratios[k].append(v)
    print(f"| {name} | {el} | {eb} | {f(r['emitted'])} | {f(r['linked'], 5)} | {f(l2 / MIB if l2 else None, 1)} "
          f"| {f(cb / MIB if cb else None, 1)} | {f(ca / MIB if ca else None, 1)} | {f(r['crss_b'])} "
          f"| {f(r['crss_a'])} | {f(r['prss'])} |")
print(f"| **geomean** | | | **{f(geo(ratios['emitted']), 4)}** | {f(geo(ratios['linked']), 5)} | | | | "
      f"**{f(geo(ratios['crss_b']), 4)}** | **{f(geo(ratios['crss_a']), 4)}** | {f(geo(ratios['prss']), 4)} |")
print()
for label, res in (("before", before), ("after", after)):
    agg, prov = res["aggregates"], res["provenance"]
    print(f"- {label}: dylib `{prov['dylib_sha256'][:16]}…`, load {prov['loadavg_before']} → "
          f"{prov['loadavg_after']} ({prov['load_status']}), emitted-size geomean "
          f"{f(agg.get('emitted_size_geomean_vs_llvm_o3'), 5)} (worst {f(agg.get('emitted_size_worst_vs_llvm_o3'), 5)}), "
          f"linked {f(agg.get('size_geomean_vs_llvm_o3'), 5)}, compiler RSS vs -O2 "
          f"{f(agg.get('compile_rss_geomean_vs_llvm_o2'), 4)} (vs -O3 {f(agg.get('compile_rss_geomean_vs_llvm_o3'), 4)}), "
          f"program RSS {f(agg.get('rss_geomean_vs_llvm_o3'), 4)}; RSS samples/lane {agg.get('rss_min_samples')}, "
          f"largest spread program {f(agg.get('program_rss_max_rel_spread'), 4)} / compiler "
          f"{f(agg.get('compile_rss_max_rel_spread'), 4)}; runtime geomean {f(agg.get('runtime_geomean_vs_llvm_o3'), 4)}; "
          f"coverage {agg.get('match_count')}/{agg.get('total_programs')}")
