#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows of the 2026-11-03 O2 census record (path relative to
~/tcg-scratch, bytes, sha256). A directory's row is its total bytes over its top-level files and
the SHA-256 of its manifest: one line `<sha256>  <name>` per file, sorted by name,
newline-terminated (as the OD-224 record's payloads_mulo.py)."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    ('o2-design/README.md', 'the O2 diagnosis and ranked route (first O2 measurement)'),
    ('s24a-design/README.md', 'the slice 24a design (the merged-chain quotient)'),
    ('runs/chain-7ee0.log', 'the bridge-and-census chain log for 7ee0def54'),
    ('runs/o2-7ee0.dylib', 'the bridge, 7ee0def54'),
    ('runs/knobs.dylib', 'the bridge, 85d236b37 (the knob lane)'),
    ('runs/gates-knobs.log', 'the knob lane gates (lane/gates_knobs.sh)'),
    ('runs/tippy-knobs.log', 'check_tippy.sh on this host (frontend unavailable)'),
    ('runs/chain-attrib.log', 'the attribution chain log'),
]
FILES.append(('runs/chain-attrib2.log', 'the second attribution chain log'))
for tag in ['o0-7ee0', 'o2-7ee0', 'o2k-plain', 'o2k-nbm', 'o2k-nrot', 'o2k-nifc', 'o2k-nall', 'o2k-b0', 'o2k-b1', 'o2k-nmax']:
    FILES += [
        (f'runs/census-{tag}.out', f'census {tag}: summary'),
        (f'runs/census-{tag}/failed_roots.jsonl', f'census {tag}: failed roots'),
        (f'runs/census-{tag}/stderr.log', f'census {tag}: body trace'),
        (f'runs/census-{tag}/obj/', f'census {tag}: emitted objects'),
    ]
for tag in ['cmp-o2-4d65-7ee0', 'cmp-o2k-plain', 'cmp-o2k-nbm', 'cmp-o2k-nrot', 'cmp-o2k-nifc', 'cmp-o2k-nall', 'cmp-o2k-b0', 'cmp-o2k-b1', 'cmp-o2k-nmax']:
    FILES.append((f'runs/{tag}/', f'census_compare.py output ({tag})'))


def digest(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


for rel, what in FILES:
    path = os.path.join(H, rel)
    if not os.path.exists(path):
        print(f'| `{rel}` ({what}) | MISSING | |')
        continue
    if os.path.isdir(path):
        names = sorted(n for n in os.listdir(path) if os.path.isfile(os.path.join(path, n)))
        manifest = ''.join(f'{digest(os.path.join(path, n))}  {n}\n' for n in names)
        size = sum(os.path.getsize(os.path.join(path, n)) for n in names)
        sha = hashlib.sha256(manifest.encode()).hexdigest()
        print(f'| `{rel}` ({what}) ({len(names)} files) | {size} | `{sha}` (manifest) |')
    else:
        print(f'| `{rel}` ({what}) | {os.path.getsize(path)} | `{digest(path)}` |')
