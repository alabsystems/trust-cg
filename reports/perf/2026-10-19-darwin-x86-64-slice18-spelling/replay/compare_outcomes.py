#!/usr/bin/env python3
"""Real bytes against the design's measurement: per census single theorem, the one-shot and
resident outcomes of the re-dumped query (the real builder) beside the design's outcome for the
spelling the design expected for it (v17, v16 through the cascade, or today's), and the body
counts. usage: compare_outcomes.py <fresh.jsonl> <resident.jsonl> [label]"""
import json, sys, collections, os
fresh_path, resident_path = sys.argv[1:3]
D = os.path.expanduser('~/tcg-scratch/s18-design/data')
def load(p):
    return {json.loads(l)['query']: json.loads(l) for l in open(p)} if os.path.exists(p) else {}
fresh, res = load(fresh_path), load(resident_path)
rows = [json.loads(l) for l in open(f'{D}/classes.jsonl')]
singles = [r['query'] for r in rows if not r['failing_part']]
r17, r16 = load(f'{D}/respell_v17_single.jsonl'), load(f'{D}/respell_v16_single.jsonl')
d17f, d17r = load(f'{D}/r1_v17_12713_fresh.jsonl'), load(f'{D}/r7_v17_12713_resident.jsonl')
d16f, d16r = load(f'{D}/r14_v16_cascade_12713.jsonl'), load(f'{D}/r23_v16c_12713_resident.jsonl')
dof = load(f'{D}/r2_orig_12713_fresh.jsonl')
pairs = collections.Counter()
counts = collections.Counter()
for q in singles:
    if r17[q]['outcome'] == 'rewritten':
        df, dr = d17f.get(q), d17r.get(q)
    elif r16[q]['outcome'] == 'rewritten':
        df, dr = d16f.get(q), d16r.get(q)
    else:
        df, dr = dof.get(q), None
    design_one = df is not None and df['outcome'] == 'certified'
    design_res = design_one and dr is not None and dr['outcome'] == 'resident-unsat'
    real_one = q in fresh and fresh[q]['outcome'] == 'certified'
    real_res = real_one and q in res and res[q]['outcome'] == 'resident-unsat'
    counts['design one-shot'] += design_one
    counts['design resident'] += design_res
    counts['real one-shot'] += real_one
    counts['real resident'] += real_res
    pairs[(df['outcome'] if df else '-', fresh[q]['outcome'] if q in fresh else '-')] += 1
    if design_one != real_one:
        print(f"MOVED design={df['outcome'] if df else '-'} real={fresh[q]['outcome'] if q in fresh else '-'}"
              f" ay={fresh.get(q, {}).get('ay_s')} clean={fresh.get(q, {}).get('clean_s')} {q[:90]}")
print(dict(counts))
for (a, b), n in sorted(pairs.items()):
    print(f'  design {a:16s} real {b:16s} {n}')
