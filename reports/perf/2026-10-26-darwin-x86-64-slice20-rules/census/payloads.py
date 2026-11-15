#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes and the SHA-256 of its manifest: one
line `<sha256>  <name>` per file, sorted by name, newline-terminated."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    # The design this slice implements.
    ('s20-design/README.md', 'the slice-20 design (§1-§8)'),
    ('s20-design/data/inscope.tsv', 'the 33 in-scope roots and their classes'),
    ('s20-design/data/names_roots.txt', 'census-ay13556\'s 106 failed roots'),
    ('s20-design/data/runs/control.tsv', 'the design probe\'s control run (main `376641c44`)'),
    ('s20-design/data/estimate_all.txt', 'the design\'s per-root estimate'),
    ('runs/core-ir-s20/', 'the census bridge\'s `core` trust-ir dump the probe reads'),
    # The probe over the 33 roots on this branch.
    ('s20-impl/bin/x86_body_probe_s20impl', 'the design\'s probe built from this branch (`probe/`)'),
    ('s20-impl/probe/branch.tsv', 'its verdicts over the 106 roots'),
    ('s20-impl/probe/branch.err', 'its stderr'),
    ('s20-impl/probe/branch.smt2/', 'its queries and index'),
    ('s20-impl/offline/replay_33.tsv', 'the 19 built roots\' 92 queries on AY 13556 + Clean, 30 s'),
    ('s20-impl/offline/roots33.txt', '`census/roots33.py` of that replay'),
    ('s20-impl/offline/shifts_30s.tsv', 'the three shift fixtures offline at 30 s, twice'),
    ('s20-impl/offline/shifts_300s.tsv', 'the same at 300 s'),
    ('s20-impl/offline/clean/', 'the two Clean rejections (AY proof, certificate, Clean output)'),
    # The libcall fix.
    ('s20-impl/libcall/before/', 'the 28 objects without the selector fix'),
    ('s20-impl/libcall/after/', 'the 28 objects with it'),
    ('s20-impl/libcall/after2/', 'the same, a second run'),
    ('s20-impl/libcall/before.sha256', 'their digests, before'),
    ('s20-impl/libcall/after.sha256', 'their digests, after'),
    ('s20-impl/libcall/e2e-i128-before.log', 'the native differential before'),
    ('s20-impl/libcall/e2e-i128-after.log', 'the native differential after'),
    # Fails-before.
    ('s20-impl/mutants/', 'the first mutant run (22 mutants; summary and each run\'s log)'),
    ('s20-impl/mutants2/', 'the mutant run on the final controls'),
    # Qualification, one test per process.
    ('s20-impl/qual1/', 'the first qualification run (before two fixtures were resized)'),
    ('s20-impl/qual2/', 'the second (the resized fixtures; the shifts\' second answers)'),
    ('s20-impl/qual3/', 'the third (the deadline-bound record read)'),
    ('s20-impl/qual4/', 'the gap lane with the production one-query theorems'),
    ('s20-impl/qual5/', 'the final run: all three lanes pass'),
    ('s20-impl/qual5x/', 'the explicit 300 s deadline-bound lane'),
    # Gates and fixtures.
    ('s20-impl/logs/gate-1.log', 'the solver-free body gate right after the merge (before the golden)'),
    ('s20-impl/logs/gate-q5.log', 'the solver-free body gate on the final controls'),
    ('s20-impl/logs/s20-fixtures-2.txt', 'the fixture printer (LIR, rows, theorems, variants)'),
    ('s20-impl/logs/golden-write-2.log', 'the golden rewrite run'),
    ('s20-impl/logs/codegen-gate-final.body.log', 'the codegen body end-to-end test, final tree'),
    ('s20-impl/logs/codegen-gate-final.mrc.log', 'the codegen must-refuse corpus, final tree'),
    ('s20-impl/logs/e2e-i128-final.log', 'the native i128 division differential, final tree'),
    ('s20-impl/logs/lower-lib.log', 'trust-cg-lower --lib'),
    ('runs/main-bf5d4b2.dylib', 'the landing baseline bridge, main `bf5d4b2c9`'),
    ('runs/census-main-bf5d4b2/failed_roots.jsonl', 'the landing baseline census'),
    ('runs/census-main-bf5d4b2/stderr.log', 'its body trace'),
    ('runs/census-main-bf5d4b2.out', 'its summary'),
    ('runs/s20.dylib', 'the slice-20 bridge, `104f7bf39`'),
    ('runs/census-s20/failed_roots.jsonl', 'the slice-20 census'),
    ('runs/census-s20/stderr.log', 'its body trace'),
    ('runs/census-s20.out', 'its summary'),
    ('runs/dump-s20/', 'its uncertified bodies\' queries'),
    ('s20/compare/', '`census_compare.py` of the two rows'),
    ('s20/logs/census_chain_kept.log', 'the census chain log'),
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
