#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes and the SHA-256 of its manifest: one
line `<sha256>  <name>` per file, sorted by name, newline-terminated."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    # The regression, measured.
    ('runs/census-s14/failed_roots.jsonl', 'slice 14\'s row (342), before the regression'),
    ('runs/census-s14/stderr.log', 'its body trace'),
    ('runs/census-main-2854ce/failed_roots.jsonl', 'main 2854ce3e3 (813), the regression'),
    ('runs/census-main-2854ce/stderr.log', 'its body trace'),
    ('runs/core-ir-2854ce/', 'the core trust-ir dump the probe reads'),
    # The owner over the dump, qualification.
    ('agep/cf5.tsv', 'the probe (`--cf`) over the dump with this owner'),
    ('agep/smt2-5/', 'the queries it built'),
    ('agep/qual2.log', 'host qualification on AY 12713'),
    ('agep/qdump2/', 'every query the qualification replayed'),
    # Census.
    ('runs/main-cb390.dylib', 'the baseline bridge, main `cb390e657`'),
    ('runs/census-main-cb390/failed_roots.jsonl', 'the baseline census'),
    ('runs/census-main-cb390/stderr.log', 'its body trace'),
    ('runs/census-main-cb390.out', 'its summary'),
    ('runs/agep.dylib', 'the ArrayGep bridge, `d12c627fb`'),
    ('runs/census-agep/failed_roots.jsonl', 'the ArrayGep census'),
    ('runs/census-agep/stderr.log', 'its body trace'),
    ('runs/census-agep.out', 'its summary'),
    ('runs/dump-agep/', 'its uncertified bodies\' queries'),
    ('agep/compare/', '`census_compare.py` of the two rows'),
    ('agep/logs/census_chain_kept.log', 'the census chain log'),
]
for f, what in FILES:
    p = os.path.join(H, f)
    label = f'`{f}`' + (f' ({what})' if what else '')
    if not os.path.exists(p):
        print(f'| {label} | MISSING | |')
        continue
    if os.path.isdir(p):
        names = sorted(n for n in os.listdir(p) if os.path.isfile(os.path.join(p, n)))
        blobs = [open(os.path.join(p, n), 'rb').read() for n in names]
        manifest = ''.join(f'{hashlib.sha256(b).hexdigest()}  {n}\n' for n, b in zip(names, blobs))
        size = sum(len(b) for b in blobs)
        print(f'| {label} ({len(names)} files) | {size} | `{hashlib.sha256(manifest.encode()).hexdigest()}` (manifest) |')
        continue
    data = open(p, 'rb').read()
    print(f'| {label} | {len(data)} | `{hashlib.sha256(data).hexdigest()}` |')
