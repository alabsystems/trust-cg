#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes over its top-level files and the SHA-256
of its manifest: one line `<sha256>  <name>` per file, sorted by name,
newline-terminated."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    # The design this slice implements.
    ('s21-design/README.md', 'the slice-21 design (§1-§7)'),
    ('s21-design/data/tables.md', 'the design\'s AY 13556 table of every fixture and spelling'),
    ('s21-design/data/names12.txt', 'the 12 roots'),
    ('s21-design/hw/x86_probe.out', 'the design\'s hardware probe (MXCSR, NaN rules, ucomisd, cvttsd2si, ld128, xchg)'),
    ('runs/core-ir-s20/', 'the census-s20 bridge\'s `core` trust-ir dump the probe reads'),
    # The 12 roots through the real builder.
    ('s21-run/bin/x86_body_probe_s21', 'the probe built from this branch (`probe/`)'),
    ('s21-run/probe/roots12.tsv', 'its verdicts over the 12 roots'),
    ('s21-run/probe/roots12.err', 'its stderr'),
    ('s21-run/probe/roots12.smt2/', 'the 12 roots\' queries and index'),
    ('s21-run/probe/replay12.txt', 'their replay on AY 13556 + Clean, 30 s'),
    # Fails-before.
    ('s21-run/mutants/', 'the mutant run (16 mutants; summary and each run\'s log)'),
    # Qualification, one test per process.
    ('s21-run/qual1/', 'the first qualification run (the credit lane stops at a TV-2 failure)'),
    ('s21-run/qual2/', 'the credit lane, its control check relaxed to the theorem\'s verdicts'),
    ('s21-run/qual3/', 'the run on the final owner: all three lanes pass'),
    ('s21-run/qual4/', 'the final run, the region fixtures replayed too: all three lanes pass'),
    # Gates and fixtures.
    ('s21-run/logs/gate1.log', 'the solver-free body suite before the golden digest was pinned'),
    ('s21-run/logs/gate2.log', 'the solver-free body suite on the final owner'),
    ('s21-run/logs/gate3.log', 'the solver-free body suite on the final code'),
    ('s21-run/logs/print21.log', 'the fixture printer (LIR, rows, theorems, variants, controls)'),
    ('s21-run/logs/codegen1.body.log', 'the codegen body end-to-end lane'),
    ('s21-run/logs/codegen1.identity.log', 'its replay identity (AY 13556), run with --nocapture'),
    ('s21-run/logs/codegen1.mrc.log', 'the must-refuse corpus'),
    ('s21-run/logs/e2e_atomics.log', 'the native atomics end-to-end (the RBX probe)'),
    ('s21-run/logs/lower.log', 'trust-cg-lower --lib'),
    ('s21-run/logs/tippy.log', 'the attempted tippy run (the 6808 package cannot resolve the workspace)'),
    ('runs/main-c4885af.dylib', 'the landing baseline bridge, main `c4885af82`'),
    ('runs/census-main-c4885af/failed_roots.jsonl', 'the landing baseline census'),
    ('runs/census-main-c4885af/stderr.log', 'its body trace'),
    ('runs/census-main-c4885af.out', 'its summary'),
    ('runs/s21.dylib', 'the slice-21 bridge, `401db9e46`'),
    ('runs/census-s21/failed_roots.jsonl', 'the slice-21 census'),
    ('runs/census-s21/stderr.log', 'its body trace'),
    ('runs/census-s21.out', 'its summary'),
    ('s21/compare/', '`census_compare.py` of the two rows'),
    ('s21/logs/census_chain_kept.log', 'the census chain log'),
]


def digest(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


for rel, what in FILES:
    path = os.path.join(H, rel)
    if os.path.isdir(path):
        names = sorted(n for n in os.listdir(path) if os.path.isfile(os.path.join(path, n)))
        manifest = ''.join(f'{digest(os.path.join(path, n))}  {n}\n' for n in names)
        size = sum(os.path.getsize(os.path.join(path, n)) for n in names)
        sha = hashlib.sha256(manifest.encode()).hexdigest()
        print(f'| `{rel}` ({what}) ({len(names)} files) | {size} | `{sha}` (manifest) |')
    else:
        print(f'| `{rel}` ({what}) | {os.path.getsize(path)} | `{digest(path)}` |')
