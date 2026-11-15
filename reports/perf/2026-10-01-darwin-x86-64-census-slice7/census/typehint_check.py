#!/usr/bin/env python3
"""For each function the census refuses with 'inconsistent type hint for Value(N)',
print N's hinted type and the instruction that uses N (from the probe's LIR view)."""
import os, re, subprocess
names = [l.strip() for l in open(os.path.expanduser('~/tcg-scratch/s7native/typehint_names.txt')) if l.strip()]
out = subprocess.run(['zsh', os.path.expanduser('~/tcg-scratch/s7native/probe_fn.sh'), ''],
                     capture_output=True, text=True).stdout
blocks = out.split('==== ')
by_name = {}
for b in blocks[1:]:
    name = b.split('\n', 1)[0]
    by_name.setdefault(name, b)
kinds = {}
for n in names:
    b = by_name.get(n)
    if not b:
        print('MISSING', n[:80]); continue
    m = re.search(r'inconsistent type hint for Value\((\d+)\)', b)
    v = m.group(1)
    hint = re.search(r'\(Value\(' + v + r'\), ([^)]*\)?)\)', b.split('value_types', 1)[1])
    uses = [l.strip()[:140] for l in b.splitlines() if re.search(r'\bValue\(' + v + r'\)', l) and '=' in l and 'value_types' not in l]
    use = next((u for u in uses if not u.startswith(f'[Value({v})]')), uses[-1] if uses else '?')
    kind = hint.group(1) if hint else '?'
    kinds[kind.split('(')[0]] = kinds.get(kind.split('(')[0], 0) + 1
    print(f'{kind:20s} {use[:110]}')
print(kinds)
