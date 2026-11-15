#!/usr/bin/env python3
"""Map a probe output dir (FNV-hash file names + index.tsv) onto the census dump's file names
(the bridge's `x86-body-dump=` naming: the function name, every byte outside [A-Za-z0-9_] a
`-`, at most 200 characters; `<name>.smt2` or `<name>.part<k>.smt2`) and compare bytes against
a reference dir.  usage: compare_probe.py <probe out dir> <mapped dir to write> <ref dir>"""
import os, sys, shutil
probe, mapped, ref = sys.argv[1:4]
os.makedirs(mapped, exist_ok=True)
def dump_name(fn):
    return ''.join(c if (c.isascii() and (c.isalnum() or c == '_')) else '-' for c in fn)[:200]
names = {}
for line in open(os.path.join(probe, 'smt2', 'index.tsv')):
    rec = line.rstrip('\n').split('\t')
    h, fn = rec[0], rec[1]
    stem = dump_name(fn)
    if len(rec) == 3:
        for k in range(1, int(rec[2]) + 1):
            names[f'{h}.part{k}.smt2'] = f'{stem}.part{k}.smt2'
    else:
        names[f'{h}.smt2'] = f'{stem}.smt2'
for src, dst in names.items():
    shutil.copyfile(os.path.join(probe, 'smt2', src), os.path.join(mapped, dst))
# Slice 19 (OD-197), a probe run with S19_CLAIMS=1: each claim split to <mapped>_claims/.
claims = 0
for src, dst in names.items():
    k = 1
    while os.path.exists(os.path.join(probe, 'smt2', src[:-5] + f'.c{k}.smt2')):
        os.makedirs(mapped.rstrip('/') + '_claims', exist_ok=True)
        shutil.copyfile(os.path.join(probe, 'smt2', src[:-5] + f'.c{k}.smt2'),
                        os.path.join(mapped.rstrip('/') + '_claims', dst[:-5] + f'.c{k}.smt2'))
        k += 1; claims += 1
if claims:
    print(f'claim queries: {claims}')
got = set(names.values())
have = set(f for f in os.listdir(ref) if f.endswith('.smt2'))
same = [f for f in sorted(got & have) if open(os.path.join(mapped, f)).read() == open(os.path.join(ref, f)).read()]
diff = sorted((got & have) - set(same))
print(f'probe queries: {len(got)}; ref {len(have)}; identical {len(same)}; differ {len(diff)}; only in probe {len(got - have)}; only in ref {len(have - got)}')
for f in diff: print('  DIFF', f[:120])
for f in sorted(got - have)[:20]: print('  PROBE-ONLY', f[:120])
for f in sorted(have - got)[:20]: print('  REF-ONLY', f[:120])
