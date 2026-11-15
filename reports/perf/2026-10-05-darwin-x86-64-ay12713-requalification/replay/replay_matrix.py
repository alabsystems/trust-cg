#!/usr/bin/env python3
"""Replay a subset of an exported qualification matrix on one AY (strict Alethe + Clean).

usage: replay_matrix.py MATRIX_DIR AY OUT.tsv FAMILY[,FAMILY] CLASS[,CLASS] [workers]
Each row: family, class, label, outcome, wall s, cpu s, AY notes. `lane-timeout` marks a run
whose wall time exceeded the lane's 30 s deadline (the replay's supervisor would have killed
it), whatever AY answered after it.
"""
import concurrent.futures
import importlib.util
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("replay_one", os.path.join(HERE, "replay_one.py"))
sys.argv, saved = [sys.argv[0]], sys.argv
replay_one = importlib.util.module_from_spec(spec)
source = open(os.path.join(HERE, "replay_one.py")).read().replace("\nmain()\n", "\n")
exec(compile(source, "replay_one.py", "exec"), replay_one.__dict__)
sys.argv = saved


def main():
    matrix, ay, out, families, classes = sys.argv[1:6]
    workers = int(sys.argv[6]) if len(sys.argv) > 6 else 1
    families, classes = set(families.split(",")), set(classes.split(","))
    manifest = json.load(open(os.path.join(matrix, "manifest.json")))
    rows = [q for q in manifest["queries"] if q["family"] in families and q["class"] in classes]

    def run(q):
        smt2 = open(os.path.join(matrix, q["file"])).read()
        kind, wall, cpu, notes = replay_one.replay(ay, smt2)
        if wall > 30.0:
            kind = f"lane-timeout({kind})"
        return q, kind, wall, cpu, notes

    with open(out, "w") as o, concurrent.futures.ThreadPoolExecutor(workers) as pool:
        for q, kind, wall, cpu, notes in pool.map(run, rows):
            o.write(f"{q['family']}\t{q['class']}\t{q['label']}\t{kind}\t{wall:.1f}\t{cpu:.1f}\t{notes}\n")
            o.flush()
    print("MATRIX-DONE", len(rows))


main()
