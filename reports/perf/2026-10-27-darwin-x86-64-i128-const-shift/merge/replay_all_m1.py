#!/usr/bin/env python3
"""OD-215 lane (a copy of slice 23's replay_all.py over measure_m1.py): replay EVERY query of a probe run's q/ directory matching a prefix (whole, its
generalization, every claim and every claim's generalization), one-shot on AY 13556 + Clean at
the lane's 30 s deadline, through measure23.py's cached replay (one solver at a time, gated).
usage: replay_all.py <label> <q dir> <prefix>   -> one line per query on stdout"""
import glob, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import measure_m1 as M  # noqa: E402

label, q, prefix = sys.argv[1:4]
cache = M.load_cache()
def key(p):
    b = os.path.basename(p)[len(prefix):]
    parts = b.split('.')
    claim = next((int(x[5:]) for x in parts if x.startswith('claim')), 0)
    return (claim, 'gen' in parts, b)
for path in sorted(glob.glob(os.path.join(q, prefix + '*.smt2')), key=key):
    rec = M.replay(path, label, cache)
    print(f"{os.path.basename(path)}\t{rec['outcome']}\t{rec.get('ay_s')}\t{rec.get('clean_s', '-')}\t{rec['bytes']}")
