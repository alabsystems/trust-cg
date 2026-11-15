#!/usr/bin/env python3
"""Markdown tables for the record from one benchmarks/real-corpus/run.py results file.

Usage: real_corpus_tables.py <results.json>

Prints the outcome counts per lane and per kind, the named refusal codes, the
ratios over completed rows, and one line per row: lines of source, the LLVM
compile median, the production (proofs-on) outcome with its time to refusal or
its compile median, the named codes, the diagnostic outcome and ratios, and,
for a library row, the code bytes each lane emitted (a row whose LLVM object
holds no code compiles vacuously, and is marked). It reads only the file given
and computes nothing beyond ratios of its own medians.
"""
import json
import sys


def fmt(value, digits=3):
    if value is None:
        return "-"
    if isinstance(value, float):
        return f"{value:.{digits}f}"
    return f"{value:,}" if isinstance(value, int) else str(value)


def main():
    res = json.load(open(sys.argv[1]))
    prov = res["provenance"]
    print(f"revision `{prov['git_sha'][:12]}` dirty={prov['git_dirty']} load {prov['loadavg_before']} -> "
          f"{prov['loadavg_after']} (threshold {prov['load_threshold']}); eligible={res['eligible']}")
    for reason in res["ineligible_reasons"]:
        print(f"  not evidence: {reason}")
    print()
    for lane, agg in res["aggregates"].items():
        print(f"### {lane}: {agg['completed']} of {agg['rows']} completed ({agg['completion_pct']}%)\n")
        print("| outcome | rows |\n| --- | ---: |")
        for outcome, count in agg["counts"].items():
            if count:
                print(f"| {outcome} | {count} |")
        print("\n| kind | rows | completed | % |\n| --- | ---: | ---: | ---: |")
        for kind, v in agg["by_kind"].items():
            print(f"| {kind} | {v['rows']} | {v['completed']} | {v['completion_pct']} |")
        if agg["refused_rows_by_code"]:
            print("\nrefused rows by code: " + ", ".join(f"`{c}` {n}" for c, n in agg["refused_rows_by_code"].items()))
        if agg["ratios"]:
            print("\n| ratio vs LLVM over completed rows | geomean | worst | rows | missing |\n| --- | ---: | ---: | ---: | --- |")
            for key, v in agg["ratios"].items():
                print(f"| {key} | {fmt(v['geomean'])} | {fmt(v['worst'])} | {v['rows']} | {', '.join(v['missing']) or '-'} |")
        print()
    print("| row | lines | LLVM compile s | production outcome | production s (refusal, or median) | codes | diagnostic | diag compile x | diag instr x | diag runtime cycles x | code bytes LLVM / production / diagnostic |")
    print("| --- | ---: | ---: | --- | ---: | --- | --- | ---: | ---: | ---: | --- |")
    vacuous = []
    for r in res["rows"]:
        lanes = r.get("lanes") or {}
        llvm = (lanes.get("llvm") or {}).get("summary") or {}
        bridge = lanes.get("bridge") or {}
        diag = lanes.get("diagnostic") or {}
        bs = (bridge.get("summary") or {}).get("wall_s") or bridge.get("refusal_wall_s")
        dr = (r.get("ratios") or {}).get("diagnostic") or {}
        codes = " ".join(c.strip("[]") for c in (bridge.get("tcg_codes") or []))
        cb = ""
        if r.get("crate_type") == "lib" and lanes:
            cb = f"{fmt((lanes.get('llvm') or {}).get('code_bytes'))} / {fmt(bridge.get('code_bytes'))} / {fmt(diag.get('code_bytes'))}"
            if (lanes.get("llvm") or {}).get("code_bytes") == 0 and r.get("outcome") == "COMPILED":
                vacuous.append(r["id"])
        outcome = r["outcome"] + (f" ({r['reason'][:60]})" if r.get("reason") else "")
        print(f"| {r['id']} | {fmt(r.get('lines'))} | {fmt(llvm.get('wall_s'))} | {outcome} | {fmt(bs)} | {codes} | "
              f"{r.get('diagnostic_outcome', '')} | {fmt(dr.get('compile_wall_s'))} | {fmt(dr.get('compile_instructions'))} | "
              f"{fmt(dr.get('runtime_cycles'))} | {cb} |")
    print(f"\nproduction COMPILED rows whose LLVM object holds no code (vacuous): {vacuous or 'none'}")


if __name__ == "__main__":
    main()
