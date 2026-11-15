#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows of the 2026-11-06 O2 knob-ceiling census record (path relative
to ~/tcg-scratch, bytes, sha256). A directory's row is its total bytes over its top-level files and
the SHA-256 of its manifest: one line `<sha256>  <name>` per file, sorted by name,
newline-terminated (as the 2026-11-04 record's payloads_loop.py)."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    ('s26-design/README.md', 'the slice 26 design'),
    ('od233-design/README.md', 'the OD-233 design (its section 7 names slice_error_fail_rt)'),
    ('runs/o2-m301.dylib', 'the bridge, main b30110fcd'),
    ('knobs-m301/census.log', 'the run log (lane/census.sh)'),
]
for tag in ['o2-s25', 'o2-m301', 'o2k-m301-lr', 'o2k-m301-all', 'o2k-m301-allbm', 'o2lk-k3']:
    FILES += [
        (f'runs/census-{tag}.out', f'census {tag}: summary'),
        (f'runs/census-{tag}/failed_roots.jsonl', f'census {tag}: failed roots'),
        (f'runs/census-{tag}/refusals.jsonl', f'census {tag}: typed refusals'),
        (f'runs/census-{tag}/stderr.log', f'census {tag}: body trace'),
        (f'runs/census-{tag}/obj/', f'census {tag}: emitted objects'),
    ]
for tag in ['o2-m301', 'o2k-m301-lr', 'o2k-m301-all', 'o2k-m301-allbm']:
    FILES += [
        (f'runs/dump-{tag}/', f'census {tag}: dumped queries'),
        (f'knobs-m301/out/{tag}/root_classes.txt', f'census {tag}: first-refusal classes'),
    ]
FILES += [
    ('knobs-m301/out/o2-m301/vs-o2-s25/', 'census_compare.py: plain against slice 25'),
    ('knobs-m301/out/o2k-m301-lr/vs-o2-m301/', 'census_compare.py: lr against plain'),
    ('knobs-m301/out/o2k-m301-all/vs-o2-m301/', 'census_compare.py: all against plain'),
    ('knobs-m301/out/o2k-m301-allbm/vs-o2-m301/', 'census_compare.py: allbm against plain'),
    ('knobs-m301/out/o2k-m301-lr/followup/', 'census_s25.py: lr against plain'),
    ('knobs-m301/out/o2k-m301-all/followup/', 'census_s25.py: all against plain'),
    ('knobs-m301/out/o2k-m301-allbm/followup/', 'census_s25.py: allbm against plain'),
]


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
