#!/usr/bin/env python3
"""Slice 19 reference spelling (MEASUREMENT only): the design's smtq19
v19_pipeline over dumped queries, with
  * a one-path theorem (= S M) spelled as the single claim (= S M) (the Rust
    `normal::spelled_pair`): kept only if the claim left is an equation of two
    bit-vectors;
  * the Rust port's constant-field limit: a fold whose value needs more than 64
    bits, and a sign test whose all-ones constant is wider than 64 bits, are not
    applied.
usage: ref_spell.py <in-dir> <out-dir> <report.jsonl> --groups g1,g2 FILE...
Writes <out-dir>/<file> for every query (rewritten or not); emptied/declined
queries are not written.
"""
import argparse, json, os, sys
sys.path.insert(0, os.path.expanduser("~/tcg-scratch/s19-ay-design/scripts"))
import smtq19 as V
S = V.S

_fold = S.fold_const
def fold_const64(n):
    r = _fold(n)
    if r is not None and S.is_const(r) and S._const_val(r) >= (1 << 64):
        return None
    return r
S.fold_const = fold_const64

_rule = V.norm_rule19
def rule64(n):
    r = _rule(n)
    if r is not None and S.NODES[r][0] == "or":
        for a in S.NODES[r][1]:
            if S.NODES[a][0] == "=":
                for b in S.NODES[a][1]:
                    if S.is_const(b) and S.WIDTH[b] > 64:
                        return None
    return r
S.norm_rule = rule64

ap = argparse.ArgumentParser()
ap.add_argument("indir"); ap.add_argument("outdir"); ap.add_argument("report")
ap.add_argument("--groups", default="")
ap.add_argument("files", nargs="+")
a = ap.parse_args()
groups = [g for g in a.groups.split(",") if g]
os.makedirs(a.outdir, exist_ok=True)
with open(a.report, "w") as rep:
    for f in a.files:
        text = open(os.path.join(a.indir, f)).read()
        q = S.Query(text); th = S.Theorem(q)
        rec = {"query": f}
        if th.source == S.TRUE:
            r = V.v19_pipeline(th.defs, th.machine, groups)
            if r is None:
                rec["outcome"] = "emptied"
            else:
                d2, c2 = r
                out = S.emit(th.free, d2, S.TRUE, c2, q.options, q.logic or "QF_BV")
                rec["outcome"] = "unchanged" if out == text else "rewritten"
                open(os.path.join(a.outdir, f), "w").write(out)
        else:
            r = V.v19_pipeline(th.defs, S.mk("=", (th.source, th.machine)), groups)
            if r is None:
                rec["outcome"] = "emptied"
            else:
                d2, c2 = r
                op, args = S.NODES[c2]
                if op != "=" or not S.WIDTH[args[0]]:
                    rec["outcome"] = "declined"
                else:
                    out = S.emit(th.free, d2, args[0], args[1], q.options, q.logic or "QF_BV")
                    rec["outcome"] = "unchanged" if out == text else "rewritten"
                    open(os.path.join(a.outdir, f), "w").write(out)
        rep.write(json.dumps(rec) + "\n")
        print(rec["outcome"], f[:90], flush=True)
