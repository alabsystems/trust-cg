#!/usr/bin/env python3
"""Slice 19 stage 3 (OD-197) on the real bytes: for every query of the 41 roots that does not
certify whole one-shot, replay its claims (the probe's S19_CLAIMS dump, `<query>.c<k>.smt2`)
one-shot in order, stopping at the first claim that does not certify, as the bridge's
x86_claims_verdict does. Results go to results/fresh.jsonl (measure.py's store, keyed by
sha256), so measure.py score --claims reads them.  usage: claims_seq.py <mapped> <claims dir>"""
import hashlib, json, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
mapped, claims_dir = sys.argv[1:3]
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
def fresh():
    out = {}
    for l in open(os.path.join(HERE, 'results', 'fresh.jsonl')):
        r = json.loads(l); out[r['sha']] = r
    return out
claims = sorted(os.listdir(claims_dir))
for f in sorted(os.listdir(mapped)):
    if not f.endswith('.smt2'):
        continue
    known = fresh()
    if known.get(sha(os.path.join(mapped, f)), {}).get('outcome') == 'certified':
        continue
    mine = sorted((c for c in claims if c.startswith(f[:-5] + '.c') and c[len(f) - 3:-5].isdigit()),
                  key=lambda c: int(c[len(f) - 3:-5]))
    if not mine:
        print(f'NO-SPLIT {f[:100]}', flush=True); continue
    for k, c in enumerate(mine):
        p = os.path.join(claims_dir, c)
        r = fresh().get(sha(p))
        if r is None:
            subprocess.run(['python3', os.path.join(HERE, 'measure.py'), 'run', '--single', p, 'claims'],
                           check=False)
            r = fresh().get(sha(p), {})
        print(f"{r.get('outcome','?'):12s} claim {k+1}/{len(mine)} ay={r.get('ay_s')} {f[:90]}", flush=True)
        if r.get('outcome') != 'certified':
            break
print('CLAIMS-SEQ-DONE', flush=True)
