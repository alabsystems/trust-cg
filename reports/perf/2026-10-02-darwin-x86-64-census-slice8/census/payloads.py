#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes and the SHA-256 of its manifest: one
line `<sha256>  <name>` per file, sorted by name, newline-terminated."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    'runs/core-ir-s7/',
    's8/core-ir-clean/core.trust_irbin',
    'runs/main-90cc.dylib',
    'runs/census-main-90cc/failed_roots.jsonl',
    'runs/census-main-90cc/stderr.log',
    'runs/census-main-90cc.out',
    'runs/s8.dylib',
    'runs/census-s8/provenance.json',
    'runs/census-s8/failed_roots.jsonl',
    'runs/census-s8/gap_table.md',
    'runs/census-s8/refusals.jsonl',
    'runs/census-s8/stderr.log',
    'runs/census-s8.out',
    's8/census_s8.log',
    's8/census-compare/promoted.txt',
    's8/census-compare/newly_failing.txt',
    's8/census-compare/body_trace_classes.tsv',
    's8/census-compare/slice8_transitions.tsv',
    's8/census-compare/compare.txt',
    's8/census-compare/promotions.txt',
    's8/census-compare/root_classes.md',
    's8/sig_s7.tsv',
    's8/sig_s8b.tsv',
    's8/bucket_s7.txt',
    's8/offline_transitions.txt',
    's8/qualification.txt',
    's8/gate_verify_full.txt',
    's8/gate_row_slice8.txt',
    's8/mutants.txt',
    's8/robustness_no_replay.txt',
    's8/robustness_replay.txt',
    's8/e2e_and_must_refuse.txt',
    's8/credited_O0.txt',
    's8/credited_O123.txt',
    's8/all_O0123.txt',
]
for f in FILES:
    p = os.path.join(H, f)
    if not os.path.exists(p):
        print(f'| `{f}` | MISSING | |')
        continue
    if os.path.isdir(p):
        names = sorted(os.listdir(p))
        blobs = [open(os.path.join(p, n), 'rb').read() for n in names]
        manifest = ''.join(f'{hashlib.sha256(b).hexdigest()}  {n}\n' for n, b in zip(names, blobs))
        size = sum(len(b) for b in blobs)
        print(f'| `{f}` ({len(names)} files) | {size} | `{hashlib.sha256(manifest.encode()).hexdigest()}` (manifest) |')
        continue
    data = open(p, 'rb').read()
    print(f'| `{f}` | {len(data)} | `{hashlib.sha256(data).hexdigest()}` |')
