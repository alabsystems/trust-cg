#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows of the 2026-11-04 O2 loop census record (path relative to
~/tcg-scratch, bytes, sha256). A directory's row is its total bytes over its top-level files and
the SHA-256 of its manifest: one line `<sha256>  <name>` per file, sorted by name,
newline-terminated (as the 2026-11-03 record's payloads_o2.py)."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    ('s26-design/README.md', 'the slice 26 design (its section 7 is this measurement plan)'),
    ('runs/lk.dylib', 'the bridge, 65f5e6cdb (the OD-232 lane)'),
    ('runs/o2-s24a-f.dylib', 'the slice 24a baseline bridge, b342de091'),
    ('lk-run/logs/run.log', 'the lane run log (lane/run.sh)'),
]
for tag in ['o2-s24a-f', 'o2lk-plain', 'o2lk-k1', 'o2lk-k2', 'o2lk-k3', 'o2lk-k4', 'o2lk-k5']:
    FILES += [
        (f'runs/census-{tag}.out', f'census {tag}: summary'),
        (f'runs/census-{tag}/failed_roots.jsonl', f'census {tag}: failed roots'),
        (f'runs/census-{tag}/stderr.log', f'census {tag}: body trace'),
        (f'runs/census-{tag}/obj/', f'census {tag}: emitted objects'),
    ]
for tag in ['cmp-o2lk-plain-vs-s24a', 'cmp-o2lk-k1', 'cmp-o2lk-k2', 'cmp-o2lk-k3', 'cmp-o2lk-k4', 'cmp-o2lk-k5']:
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
