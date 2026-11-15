#!/usr/bin/env python3
"""Time one query on an AY's RESIDENT route (`ay --incremental`, the query on stdin, verdict
only), the first step of trust-cg's source-bound replay (`replay_protocol_description`).

usage: resident_one.py AY QUERY.smt2 [wall_cap_s]
"""
import os
import resource
import subprocess
import sys
import time

ENV = {k: v for k, v in os.environ.items() if not k.startswith(("TCG_", "TRUST_CG_"))}


def main():
    ay, query = sys.argv[1], sys.argv[2]
    cap = float(sys.argv[3]) if len(sys.argv) > 3 else 120.0
    build = subprocess.run([ay, "--version"], capture_output=True, text=True).stdout.splitlines()[0]
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    t0 = time.time()
    child = subprocess.Popen([ay, "--incremental"], stdin=open(query), stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True, env=ENV, start_new_session=True)
    try:
        out, _ = child.communicate(timeout=cap)
        verdict = " | ".join(l.strip() for l in out.splitlines()
                             if l.strip() in ("sat", "unsat", "unknown") or "reason-unknown" in l)[:200]
    except subprocess.TimeoutExpired:
        os.killpg(child.pid, 9)
        child.communicate()
        verdict = f"NO-ANSWER-WITHIN-{cap:.0f}s"
    r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = (r1.ru_utime + r1.ru_stime) - (r0.ru_utime + r0.ru_stime)
    print(f"{os.path.basename(query)}\t{build.split('@')[0]}\tresident\t{verdict}\twall={time.time() - t0:.1f}\tcpu={cpu:.1f}",
          flush=True)


main()
