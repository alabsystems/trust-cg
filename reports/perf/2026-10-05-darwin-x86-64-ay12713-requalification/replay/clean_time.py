#!/usr/bin/env python3
"""Time AY (strict Alethe proof) and then Clean on one query, separately.

usage: clean_time.py AY QUERY.smt2
"""
import json
import os
import subprocess
import sys
import tempfile
import time

CLEAN = "$HOME/.local/share/trust-overlays/x86-stage1-ay12713/bin/clean"
ENV = {k: v for k, v in os.environ.items() if not k.startswith(("TCG_", "TRUST_CG_"))}
ay, query = sys.argv[1], sys.argv[2]
smt2 = open(query).read()
with tempfile.TemporaryDirectory() as d:
    q, p = os.path.join(d, "q.smt2"), os.path.join(d, "q.alethe")
    open(q, "w").write(smt2)
    t0 = time.time()
    r = subprocess.run([ay, "-smt2", q, "--strict-proofs", "--proof", p, "--proof-format", "alethe"],
                       capture_output=True, text=True, timeout=600, env=ENV)
    t1 = time.time()
    size = os.path.getsize(p) if os.path.exists(p) else 0
    cj = os.path.join(d, "cert.json")
    json.dump({"type": "alethe_certificate", "version": "1.0", "problem": smt2,
               "proof": open(p).read() if size else ""}, open(cj, "w"))
    c = subprocess.run([CLEAN, "cert", "verify-external", cj, "--verbose"], capture_output=True,
                       text=True, timeout=600, env=ENV)
    t2 = time.time()
    verdict = "PASSED" if "verification: PASSED" in c.stdout + c.stderr else "FAILED"
    print(f"{os.path.basename(query)}\tay={t1 - t0:.1f}s\tproof={size}B\tclean={t2 - t1:.1f}s\t{verdict}")
