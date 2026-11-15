#!/usr/bin/env python3
"""Map a probe output dir (FNV-hash file names + index.tsv) onto the census dump's file names
(classes.jsonl: fn -> query / stem) and compare bytes against one or more reference dirs.

usage: compare_probe.py <probe out dir> <mapped dir to write> <ref dir> [<ref dir>...]
Writes every probe query under its census file name into <mapped dir>, and prints, per reference
dir, how many files are byte-identical, differ, or are missing on either side."""
import json, os, sys, shutil
probe, mapped, *refs = sys.argv[1:]
rows = [json.loads(l) for l in open(os.path.expanduser('~/tcg-scratch/s18-design/data/classes.jsonl'))]
byfn = {r['fn']: r for r in rows}
os.makedirs(mapped, exist_ok=True)
index = [l.rstrip('\n').split('\t') for l in open(os.path.join(probe, 'smt2', 'index.tsv'))]
names = {}
for rec in index:
    h, fn = rec[0], rec[1]
    r = byfn.get(fn)
    if r is None:
        print('UNMAPPED', fn); continue
    if len(rec) == 3:  # parts
        stem = r['stem'] if r['failing_part'] else r['query'][:-5]
        for k in range(1, int(rec[2]) + 1):
            names[f'{h}.part{k}.smt2'] = f'{stem}.part{k}.smt2'
    else:
        names[f'{h}.smt2'] = r['query']
for src, dst in names.items():
    shutil.copyfile(os.path.join(probe, 'smt2', src), os.path.join(mapped, dst))
got = set(names.values())
print(f'probe queries: {len(got)}')
for ref in refs:
    have = set(f for f in os.listdir(ref) if f.endswith('.smt2'))
    same = [f for f in sorted(got & have) if open(os.path.join(mapped, f)).read() == open(os.path.join(ref, f)).read()]
    diff = sorted((got & have) - set(same))
    print(f'{ref}: {len(have)} files; identical {len(same)}; differ {len(diff)}; only in probe {len(got - have)}; only in ref {len(have - got)}')
    for f in diff[:200]:
        print('  DIFF', f[:110])
