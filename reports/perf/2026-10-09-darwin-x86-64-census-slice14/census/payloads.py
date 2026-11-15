#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes and the SHA-256 of its manifest: one
line `<sha256>  <name>` per file, sorted by name, newline-terminated. A path
that does not exist prints a row saying so, never a guessed digest."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    ('runs/census-s15-cf98/failed_roots.jsonl', 'the measurement row\'s failed roots (the slice-15 census)'),
    ('runs/census-s15-cf98/stderr.log', 'its body trace'),
    ('runs/core-ir-s9/', 'the slice-9 dump of `core`\'s trust-ir the probe reads'),
    ('scratch14/class_names.tsv', 'the 71 class functions (`census/classes.py`)'),
    ('scratch14/dump_base/', 'the probe over the 71 with the slice-12 owner (`--dump`)'),
    ('scratch14/dump_s14/', 'the probe over the 71 with the slice-14 owner (`--dump`), with the built queries'),
    ('scratch14/payloads/', 'logs: library gates, qualification runs, mutants, the native test, the end-to-end compile, offline replays'),
    ('scratch14/qdump/', 'every query the pre-merge slice-14 qualification replayed'),
    ('scratch14/payloads2/', 'logs of the gates after merging main 49b93b2ee'),
    ('scratch14/qdump2/', 'every query the post-merge slice-14 qualification replayed'),
    ('scratch14/exp/', 'the division-encoding experiments (inlined, paired, 300 s replays)'),
    ('runs/main-a902.dylib', 'the baseline bridge, main `a902ea9ef`'),
    ('runs/census-main-a902/failed_roots.jsonl', 'the baseline census'),
    ('runs/census-main-a902/stderr.log', 'its body trace'),
    ('runs/census-main-a902.out', 'its summary'),
    ('runs/s14.dylib', 'the slice-14 bridge, `ffdfb2b23`'),
    ('runs/census-s14/failed_roots.jsonl', 'the slice-14 census'),
    ('runs/census-s14/stderr.log', 'its body trace'),
    ('runs/census-s14.out', 'its summary'),
    ('runs/dump-s14/', 'its uncertified bodies\' queries'),
    ('s14/compare/', '`census_compare.py` of the two rows'),
    ('s14/logs/census_redo_kept.log', 'the census chain log'),
]


def digest(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


print('| Path | Bytes | SHA-256 |')
print('| --- | ---: | --- |')
for rel, note in FILES:
    path = os.path.join(H, rel)
    label = f'`{rel}`' + (f' ({note})' if note else '')
    if not os.path.exists(path):
        print(f'| {label} | - | (absent) |')
    elif os.path.isdir(path):
        manifest, total, count = [], 0, 0
        for root, _, files in os.walk(path):
            for name in files:
                full = os.path.join(root, name)
                manifest.append(f'{digest(full)}  {os.path.relpath(full, path)}')
                total += os.path.getsize(full)
                count += 1
        manifest.sort(key=lambda line: line.split('  ', 1)[1])
        text = ''.join(line + '\n' for line in manifest)
        print(f'| {label} ({count} files) | {total} | `{hashlib.sha256(text.encode()).hexdigest()}` (manifest) |')
    else:
        print(f'| {label} | {os.path.getsize(path)} | `{digest(path)}` |')
