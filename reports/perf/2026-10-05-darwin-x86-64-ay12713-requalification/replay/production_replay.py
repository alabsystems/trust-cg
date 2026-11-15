#!/usr/bin/env python3
"""Simulate trust-cg's source-bound live replay protocol (`replay_protocol_description`,
source-bound-replay-v2) on dumped body queries, for one AY:

  1. resident: `ay --incremental`, the query on stdin, verdict only, 30 s deadline;
     a resident timeout is final (never retried fresh);
  2. on `unsat` (or a bare `unknown`): fresh `ay -smt2 Q --strict-proofs --proof P
     --proof-format alethe`, its own 30 s deadline, then `clean cert verify-external`.

usage: production_replay.py AY DUMP_DIR OUT.tsv [sample_n] [seed] [workers]
Distinct query texts only (the dump holds one file per function).
"""
import concurrent.futures
import hashlib
import importlib.util
import os
import random
import resource
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ENV = {k: v for k, v in os.environ.items() if not k.startswith(("TCG_", "TRUST_CG_"))}
DEADLINE = 30.0

os.environ.setdefault("REPLAY_WALL_CAP", str(DEADLINE))
source = open(os.path.join(HERE, "replay_one.py")).read().replace("\nmain()\n", "\n")
replay_one = {}
exec(compile(source, "replay_one.py", "exec"), replay_one)


def resident(ay, path):
    t0 = time.time()
    child = subprocess.Popen([ay, "--incremental"], stdin=open(path), stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True, env=ENV, start_new_session=True)
    try:
        out, _ = child.communicate(timeout=DEADLINE)
    except subprocess.TimeoutExpired:
        os.killpg(child.pid, 9)
        child.communicate()
        return "deadline", time.time() - t0
    lines = [l.strip() for l in out.splitlines()]
    verdicts = [l for l in lines if l in ("sat", "unsat", "unknown")]
    verdict = verdicts[-1] if verdicts else "?"
    if verdict == "unknown":
        reasons = [l for l in lines if "reason-unknown" in l]
        verdict = "unknown " + (reasons[-1] if reasons else "(bare)")
    return verdict, time.time() - t0


def one(ay, path):
    verdict, rwall = resident(ay, path)
    if verdict == "unsat" or verdict == "unknown (bare)":
        kind, fwall, _, notes = replay_one["replay"](ay, open(path).read())
        return path, f"resident={verdict}", rwall, kind, fwall, notes[:200]
    return path, f"resident={verdict}", rwall, "-", 0.0, ""


def main():
    ay, dump, out = sys.argv[1:4]
    n = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    workers = int(sys.argv[6]) if len(sys.argv) > 6 else 1
    by_text = {}
    for name in sorted(os.listdir(dump)):
        if name.endswith(".smt2"):
            digest = hashlib.sha256(open(os.path.join(dump, name), "rb").read()).hexdigest()
            by_text.setdefault(digest, os.path.join(dump, name))
    paths = sorted(by_text.values())
    if n:
        paths = sorted(random.Random(seed).sample(paths, min(n, len(paths))))
    with open(out, "w") as o, concurrent.futures.ThreadPoolExecutor(workers) as pool:
        for path, rv, rwall, kind, fwall, notes in pool.map(lambda p: one(ay, p), paths):
            o.write(f"{os.path.basename(path)}\t{rv}\t{rwall:.1f}\t{kind}\t{fwall:.1f}\t{notes}\n")
            o.flush()
    print("PRODUCTION-REPLAY-DONE", len(paths), "of", len(by_text), "distinct")


main()
