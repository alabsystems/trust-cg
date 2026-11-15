#!/usr/bin/env python3
"""OD-224 lane diagnostics: one-shot AY 13556 (+ Clean 5f09e36c) replays of given query files at a
given budget (the query's own `:timeout` option rewritten to it), one solver at a time through
probe_run.py's gate. Never a credit route. usage: exp.py <budget_s> <query.smt2>..."""
import os, re, sys, time
sys.path.insert(0, "$HOME/tcg-scratch/mulo-run/replay")
import probe_run as P
P.PROBE.clear()
AY = os.path.expanduser("~/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/ay")
CLEAN = os.path.expanduser("~/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/clean")
budget = float(sys.argv[1])
for path in sys.argv[2:]:
    P.gate(sys.stderr)
    text = re.sub(r"\(set-option :timeout \d+\)", f"(set-option :timeout {int(budget * 1000)})", open(path).read())
    t0 = time.time()
    rec = P.run_fresh(AY, CLEAN, text, budget, 180.0)
    print(f"{os.path.basename(path)}\t{rec['outcome']}\tverdict={rec.get('verdict')}\tay={rec.get('ay_s')}\tclean={rec.get('clean_s', '-')}\twall={round(time.time() - t0, 1)}\tload={os.getloadavg()[0]:.2f}", flush=True)
