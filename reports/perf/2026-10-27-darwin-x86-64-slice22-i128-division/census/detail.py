#!/usr/bin/env python3
"""Per root of a measure.py stage: units, whole certified count, max AY s of certified wholes,
claims-credited units. usage: detail.py <label> <probe out dir>"""
import hashlib, json, os, sys
S = os.path.expanduser("~/tcg-scratch/s22-run")
cache = {}
for line in open(os.path.join(S, "data/replays.jsonl")):
    r = json.loads(line)
    p = cache.get(r["sha"])
    if p is None or (r["outcome"] == "certified" and p["outcome"] != "certified"):
        cache[r["sha"]] = r
q = os.path.join(sys.argv[2], "q")
for line in open(os.path.join(q, "index.tsv")):
    parts = line.rstrip("\n").split("\t")
    h, name = parts[0], parts[1]
    n = int(parts[2]) if len(parts) > 2 else 0
    stems = [f"{h}.part{k}" for k in range(1, n + 1)] if n else [h]
    recs = []
    for s in stems:
        sha = hashlib.sha256(open(os.path.join(q, s + ".smt2"), "rb").read()).hexdigest()
        recs.append(cache.get(sha, {"outcome": "unmeasured"}))
    cert = [r for r in recs if r["outcome"] == "certified"]
    mx = max((r.get("ay_s") or 0) for r in cert) if cert else None
    print(f"{name.split('4core')[-1][:60]:60s} units={len(stems):2d} whole-cert={len(cert):2d} max_ay={mx} "
          f"bytes={sum(os.path.getsize(os.path.join(q, s + '.smt2')) for s in stems)}")
