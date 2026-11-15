#!/usr/bin/env python3
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
"""Same-binary A/B of the compiler JIT's sealed link on the compile corpus.

Two `run.py measure --lane jit-compiler` documents of ONE compile_corpus
binary: the default (sealed link) and `TCG_NO_SEALED_JIT_LINK=1` (the link
re-runs every final-stream check). `run.py compare` would flag the frame-net
counters, which differ by design (the unsealed link runs the net a second
time), so this script checks what must hold and reports the rest:

  * every repetition of each side agrees with itself (verdicts, errors,
    emitted-code identity, frame-net counters);
  * the two sides agree on every module's verdict, error text and emitted
    code identity;
  * per (entry): sealed <= unsealed frame-net `analyzed + declined` <= 2 x
    sealed (the link's second run happens only on the unsealed side; a
    function the encoder takes through its exception-table branch is checked
    there on both sides, so such an entry is not doubled and is listed),
    `violations` equal;
  * instructions (steady state: the cheapest of repetitions 2..N) per origin.

Usage: analyze.py SEALED.json.gz UNSEALED.json.gz [--table out.md]
"""

import argparse
import gzip
import json
import statistics
from pathlib import Path

LANE = "jit-compiler"


def load(path):
    raw = Path(path).read_bytes()
    if path.endswith(".gz"):
        raw = gzip.decompress(raw)
    return json.loads(raw)


def module_bytes(rep):
    return [{k: m.get(k) for k in ("module", "verdict", "error", "output", "functions")} for m in rep["modules"]]


def steady(reps):
    pool = reps[1:] if len(reps) > 1 else reps
    return min(pool, key=lambda r: r["total"]["instructions"])


def net_runs(rep):
    fn = rep["frame_net"]
    return fn["analyzed"] + fn["declined"]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("sealed")
    ap.add_argument("unsealed")
    ap.add_argument("--table")
    args = ap.parse_args()
    a, b = load(args.sealed), load(args.unsealed)
    ea = {e["name"]: e for e in a["entries"] if LANE in e["lanes"]}
    eb = {e["name"]: e for e in b["entries"] if LANE in e["lanes"]}
    problems = []
    if set(ea) != set(eb):
        problems.append(f"entry sets differ: {sorted(set(ea) ^ set(eb))[:5]}")
    totals, per_entry, not_doubled = {}, [], []
    ok_entries = err_entries = 0
    for name in sorted(set(ea) & set(eb)):
        ra, rb = ea[name]["lanes"][LANE], eb[name]["lanes"][LANE]
        for side, reps in (("sealed", ra), ("unsealed", rb)):
            ids = [(r["verdict"], module_bytes(r), r["frame_net"]) for r in reps]
            if any(i != ids[0] for i in ids[1:]):
                problems.append(f"{side} {name}: repetitions disagree")
        if module_bytes(ra[0]) != module_bytes(rb[0]) or ra[0]["verdict"] != rb[0]["verdict"]:
            problems.append(f"{name}: sealed and unsealed differ in verdict, error or emitted code")
        if ra[0]["verdict"] == "ok":
            ok_entries += 1
            ns, nu = net_runs(ra[0]), net_runs(rb[0])
            if not ns <= nu <= 2 * ns:
                problems.append(f"{name}: frame-net runs sealed {ns} unsealed {nu}")
            elif nu != 2 * ns:
                not_doubled.append(f"{name} ({ns} / {nu})")
            if ra[0]["frame_net"]["violations"] != rb[0]["frame_net"]["violations"]:
                problems.append(f"{name}: frame-net violations differ")
        else:
            err_entries += 1
        sa, sb = steady(ra), steady(rb)
        ia, ib = sa["total"]["instructions"], sb["total"]["instructions"]
        ca, cb = sa["total"]["cycles"], sb["total"]["cycles"]
        origin = ea[name]["origin"]
        per_entry.append((origin, name, ra[0]["verdict"], ia, ib))
        for key in (origin, "ALL"):
            acc = totals.setdefault(key, [0, 0, 0, 0, []])
            acc[0] += ia
            acc[1] += ib
            acc[2] += ca
            acc[3] += cb
            if ib:
                acc[4].append(ia / ib)
    lines = [
        f"# Compiler JIT sealed link, same binary: sealed (default) / unsealed (`TCG_NO_SEALED_JIT_LINK=1`), lane `{LANE}`",
        "",
        (f"**Identity: PASS** — {ok_entries + err_entries} entries ({ok_entries} compiled, {err_entries} refused "
         "identically): same verdicts, error texts and emitted code on both sides and in every repetition; "
         "the unsealed side runs the frame net twice per function except where listed."
         if not problems else f"**{len(problems)} PROBLEMS**: " + "; ".join(problems[:20])),
        "",
        ("Entries whose frame-net runs are not doubled on the unsealed side (sealed / unsealed): "
         + (", ".join(not_doubled) if not_doubled else "none") + "."),
        "",
        "| origin | sealed instr | unsealed instr | sealed/unsealed | per-entry median | sealed cycles | unsealed cycles |",
        "|---|--:|--:|--:|--:|--:|--:|",
    ]
    for key in sorted(totals, key=lambda k: (k == "ALL", k)):
        ia, ib, ca, cb, ratios = totals[key]
        med = statistics.median(ratios) if ratios else float("nan")
        lines.append(f"| {key} | {ia / 1e6:,.0f} M | {ib / 1e6:,.0f} M | {ia / ib:.3f} | {med:.3f} | "
                     f"{ca / 1e6:,.0f} M | {cb / 1e6:,.0f} M |")
    text = "\n".join(lines) + "\n"
    if args.table:
        Path(args.table).write_text(text)
    print(text)
    return 1 if problems else 0


if __name__ == "__main__":
    raise SystemExit(main())
