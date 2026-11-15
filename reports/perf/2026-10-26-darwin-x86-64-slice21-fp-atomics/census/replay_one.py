#!/usr/bin/env python3
"""Replay one SMT2 query on an AY (strict Alethe, as the lane) and, on unsat, Clean.

usage: replay_one.py AY QUERY.smt2 [timeout_ms] [repeats]
Prints one line per run: query, AY build, load, outcome, AY wall s, child CPU s, proof bytes,
Clean wall s, AY notes. A timeout_ms argument rewrites the query's `(set-option :timeout N)`
header. Copied from the AY 12713 record's `replay/replay_one.py`, with the proof size and
Clean's own time added; CLEAN defaults to the x86-stage1-ay13556 overlay's `bin/clean`
(Clean 5f09e36c, the same bytes as the 12713 overlay's).
"""
import json
import os
import re
import resource
import subprocess
import sys
import tempfile
import time

CLEAN = os.environ.get("CLEAN", "$HOME/.local/share/trust-overlays/x86-stage1-ay13556/bin/clean")
ENV = {k: v for k, v in os.environ.items() if not k.startswith(("TCG_", "TRUST_CG_"))}
WALL_CAP = float(os.environ.get("REPLAY_WALL_CAP", "310"))


def cpu():
    r = resource.getrusage(resource.RUSAGE_CHILDREN)
    return r.ru_utime + r.ru_stime


def replay(ay, smt2):
    with tempfile.TemporaryDirectory() as d:
        q, p = os.path.join(d, "q.smt2"), os.path.join(d, "q.alethe")
        open(q, "w").write(smt2)
        c0, t0 = cpu(), time.time()
        # AY does not always honour the query's `:timeout` (measured on build 12713: past
        # 900 s on a 300 s budget), so the wall cap kills its whole process group.
        child = subprocess.Popen([ay, "-smt2", q, "--strict-proofs", "--proof", p, "--proof-format", "alethe"],
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, env=ENV,
                                 start_new_session=True)
        try:
            stdout, stderr = child.communicate(timeout=WALL_CAP)
        except subprocess.TimeoutExpired:
            os.killpg(child.pid, 9)
            child.communicate()
            wall, used = time.time() - t0, cpu() - c0
            return f"NO-ANSWER-WITHIN-{WALL_CAP:.0f}s", wall, used, 0, 0.0, ""
        wall, used = time.time() - t0, cpu() - c0
        out = (stdout + stderr).splitlines()
        verdicts = [l.strip() for l in out if l.strip() in ("sat", "unsat", "unknown")]
        verdict = verdicts[-1] if verdicts else "?"
        notes = " | ".join(l.strip() for l in out
                           if "reason-unknown" in l or "unproved_steps" in l or "MODEL-UNCONFIRMED" in l
                           or "strict" in l)[:600]
        kind, size, clean_wall = verdict, 0, 0.0
        if verdict == "unsat":
            size = os.path.getsize(p) if os.path.exists(p) else 0
            if "unproved_steps=0" not in notes:
                kind = "HOLEY"
            else:
                cj = os.path.join(d, "cert.json")
                json.dump({"type": "alethe_certificate", "version": "1.0", "problem": smt2,
                           "proof": open(p).read()}, open(cj, "w"))
                c1 = time.time()
                c = subprocess.run([CLEAN, "cert", "verify-external", cj, "--verbose"],
                                   capture_output=True, text=True, timeout=900, env=ENV)
                clean_wall = time.time() - c1
                text = c.stdout + c.stderr
                kind = "VERIFIED" if ("verification: PASSED" in text and c.returncode == 0) else "CLEANFAIL"
        return kind, wall, used, size, clean_wall, notes


def main():
    ay, query = sys.argv[1], sys.argv[2]
    smt2 = open(query).read()
    if len(sys.argv) > 3 and sys.argv[3] != "-":
        smt2 = re.sub(r"\(set-option :timeout \d+\)", f"(set-option :timeout {sys.argv[3]})", smt2, count=1)
    repeats = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    build = subprocess.run([ay, "--version"], capture_output=True, text=True).stdout.splitlines()[0]
    for _ in range(repeats):
        load = os.getloadavg()[0]
        kind, wall, used, size, clean_wall, notes = replay(ay, smt2)
        print(f"{os.path.basename(query)}\t{build.split('@')[0]}\tload={load:.1f}\t{kind}\twall={wall:.1f}"
              f"\tcpu={used:.1f}\tproof={size}B\tclean={clean_wall:.1f}\t{notes}", flush=True)


main()
