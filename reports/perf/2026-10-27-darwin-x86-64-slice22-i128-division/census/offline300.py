#!/usr/bin/env python3
"""One-shot replays at a 300 s budget (the gap records' offline tool output): AY 13556 strict
Alethe, then Clean. usage: offline300.py <out.jsonl> <query>..."""
import json, os, re, sys, time
sys.path.insert(0, os.path.expanduser("~/tcg-scratch/s22-run/scripts"))
import probe_run as P
P.PROBE.clear()
AY = os.path.expanduser("~/.local/share/trust-overlays/x86-stage1-ay13556/bin/ay")
CLEAN = os.path.expanduser("~/.local/share/trust-overlays/x86-stage1-ay13556/bin/clean")
out = open(sys.argv[1], "a")
for q in sys.argv[2:]:
    P.gate(sys.stderr)
    text = re.sub(r"\(set-option :timeout \d+\)", "(set-option :timeout 300000)", open(q).read(), count=1)
    t0 = time.time(); load = round(os.getloadavg()[0], 2)
    rec = P.run_fresh(AY, CLEAN, text, 300.0, 300.0)
    rec.update({"query": os.path.basename(q), "budget_s": 300, "load1": load, "t": round(t0, 1)})
    out.write(json.dumps(rec) + "\n"); out.flush()
    print(os.path.basename(q), rec.get("outcome"), rec.get("ay_s"), rec.get("verdict"), rec.get("detail", "")[:200], flush=True)
