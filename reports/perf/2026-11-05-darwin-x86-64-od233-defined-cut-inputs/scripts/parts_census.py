#!/usr/bin/env python3
"""OD-233 demand: every function stated in parts in a census stderr.log.

Reads [TCG-X86-BODY-TRACE] lines (V:7598-7672 on main 12ebba653): per
classified pair, a refusal line `fn=X <refusal>` or, for a built owner, the
optional `merged chains=`, (OD-233) `defined cut inputs bytes=B items=I`,
`stated in parts=N` and `bound rows=R replay=O`. The first three are not
terminal; an attempt ends at a refusal line or a `bound rows=` line.
(Review round 2026-11-06: before, the OD-233 line ended an attempt as a
refusal, so one attempt counted as two.)
Each function may be classified more than once (two codegen attempts); each
attempt is kept and the per-function outcome is the LAST trace line.

Usage: python3 -I parts_census.py STDERR.log OUT.json
"""
import json
import re
import sys
from collections import Counter, OrderedDict, defaultdict

TRACE = re.compile(r"^\[TCG-X86-BODY-TRACE\] fn=(\S+) (.*)$")
PARTS = re.compile(r"^stated in parts=(\d+)$")
BOUND = re.compile(r"^bound rows=(\d+) replay=(.*)$")
MERGED = re.compile(r"^merged chains=(\d+) absorbed=(\d+)$")
DEFINED = re.compile(r"^defined cut inputs bytes=(\d+) items=(\d+)$")

CUT_WORDS = (
    "cut point",
    "cut points",
    "a function stated in parts",
    "a part admits",
    "no cut plan",
    "regions)",
    "carried closed into cut",
    "into cut point",
)


def main(path, out):
    attempts = defaultdict(list)  # fn -> list of attempts (list of lines)
    pending = {}  # fn -> current attempt lines
    order = OrderedDict()
    outcome_lines = []  # (lineno, fn-less replay outcome lines)
    with open(path, errors="replace") as fh:
        for lineno, raw in enumerate(fh, 1):
            line = raw.rstrip("\n")
            m = TRACE.match(line)
            if not m:
                if line.startswith("[TCG-X86-BODY-TRACE] replay outcome="):
                    outcome_lines.append((lineno, line))
                continue
            fn, rest = m.group(1), m.group(2)
            order.setdefault(fn, None)
            cur = pending.setdefault(fn, [])
            cur.append((lineno, rest))
            # An attempt ends at a refusal line or a `bound rows=` line.
            if BOUND.match(rest) or not (
                PARTS.match(rest) or MERGED.match(rest) or DEFINED.match(rest)
            ):
                attempts[fn].append(cur)
                pending[fn] = []
    rows = []
    for fn in order:
        for k, att in enumerate(attempts[fn]):
            parts = None
            merged = None
            defined = None
            for _, rest in att:
                if (pm := PARTS.match(rest)):
                    parts = int(pm.group(1))
                if (mm := MERGED.match(rest)):
                    merged = (int(mm.group(1)), int(mm.group(2)))
                if (dm := DEFINED.match(rest)):
                    defined = (int(dm.group(1)), int(dm.group(2)))
            lineno, last = att[-1]
            bm = BOUND.match(last)
            if bm:
                kind = "bound"
                replay = bm.group(2)
                rows_n = int(bm.group(1))
                refusal = None
            else:
                kind = "refused"
                replay = None
                rows_n = None
                refusal = last
            rows.append(
                dict(
                    fn=fn,
                    attempt=k,
                    line=lineno,
                    parts=parts,
                    merged=merged,
                    defined=defined,
                    kind=kind,
                    rows=rows_n,
                    replay=replay,
                    refusal=refusal,
                    cut_text=bool(refusal and any(w in refusal for w in CUT_WORDS)),
                )
            )
    json.dump(dict(rows=rows, outcome_lines=outcome_lines), open(out, "w"), indent=1)
    # Summary.
    fns = OrderedDict()
    for r in rows:
        fns.setdefault(r["fn"], []).append(r)
    print(f"functions classified: {len(fns)}; attempts: {len(rows)}")
    inparts = {fn: rs for fn, rs in fns.items() if any(r["parts"] for r in rs)}
    print(f"functions stated in parts (any attempt): {len(inparts)}")
    agree = sum(
        1
        for rs in inparts.values()
        if len({(r["parts"], r["replay"], r["refusal"]) for r in rs}) == 1
    )
    print(f"  of them, attempts identical: {agree}")
    byreplay = Counter()
    byparts = Counter()
    for fn, rs in inparts.items():
        last = rs[-1]
        byreplay[last["replay"] if last["kind"] == "bound" else "refused:" + last["refusal"][:80]] += 1
        byparts[last["parts"]] += 1
    print("  outcome (last attempt):")
    for k, v in byreplay.most_common():
        print(f"    {v:4d}  {k}")
    print("  parts count histogram:", dict(sorted(byparts.items())))
    defining = {fn: rs[-1]["defined"] for fn, rs in inparts.items() if rs[-1]["defined"]}
    print(f"  of them, defining cut inputs (OD-233, last attempt): {len(defining)}")
    for fn, (b, i) in sorted(defining.items()):
        print(f"    bytes={b} items={i}  {fn}")
    cutref = OrderedDict()
    for fn, rs in fns.items():
        last = rs[-1]
        if last["kind"] == "refused" and last["cut_text"]:
            cutref[fn] = last["refusal"]
    print(f"functions whose last refusal mentions a cut / parts bound: {len(cutref)}")
    for fn, ref in cutref.items():
        print(f"    {fn}\n        {ref[:400]}")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
