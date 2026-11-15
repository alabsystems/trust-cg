#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes and the SHA-256 of its manifest: one
line `<sha256>  <name>` per file, sorted by name, newline-terminated."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    # The class: the design's (slice 12's landing census) and current main's.
    ('s16-design/size_roots.tsv', 'the design\'s class: 101 size-refused functions, 103 bound-uncertified'),
    ('runs/census-main-a902/failed_roots.jsonl', 'main a902\'s core census (the census chain\'s baseline row)'),
    ('runs/census-main-a902/stderr.log', 'its body trace'),
    ('s16/payloads/class_main/', 'its class (`size_roots.py`): 121 size-refused, 94 bound-uncertified'),
    # The inputs.
    ('runs/core-ir-s9/', 'slice 9\'s core dump (the design\'s input)'),
    ('runs/core-ir-s16/', 'the fresh core dump from main a902\'s bridge (`census/dump_core_ir.sh`)'),
    # The probe.
    ('s16/payloads/probe/', 'the probe over slice 9\'s dump before the replanning commit'),
    ('s16/payloads/measure1/', '`census/measure_s16.py` over it'),
    ('s16/payloads/probe2/', 'the probe over slice 9\'s dump at the replanning commit'),
    ('s16/payloads/measure2/', '`census/measure_s16.py` over it'),
    ('s16/payloads/probe6/', 'the probe over the fresh dump, final spelling'),
    ('s16/payloads/measure6/', '`census/measure_s16.py` over it (the 121)'),
    ('s16/probe_run6/smt2/', 'its queries: 563 parts of 106 functions, one query each for the 94 controls, index'),
    # Offline certification.
    ('s16/payloads/replay_parts_core.tsv', 'the 563 parts on AY build 12713 with Clean, 30 s each'),
    ('s16/payloads/replay_parts_core_unnumbered.tsv', 'the 643 parts of the first spelling (no value numbering), same replay'),
    # Qualification.
    ('s16/payloads/qualification/host_qualification.log', 'host qualification, final tree'),
    ('s16/payloads/qualification/verifier_credits.log', 'verifier credit, final tree'),
    ('s16/payloads/qualification/queries/', 'every replayed qualification query'),
    ('s16/payloads/qualification/longchain_300s.tsv', 'LongChain\'s parts with a 300 s budget'),
    ('s16/payloads/qualification/inverted_branch_300s.tsv', 'the inverted-branch part, one-shot AY'),
    # Gates and fails-before.
    ('s16/payloads/gate_body.log', 'the whole x86 body library gate (solver-free), final tree'),
    ('s16/payloads/cli_emit_proofs.log', 'the CLI emit_proofs tests with AY and Clean'),
    ('s16/payloads/mutants_final/', '`fails-before/run_mutants.sh` on the final tree, with each run\'s log'),
    ('s16/payloads/mutants.txt', '`fails-before/run_mutants.sh` on `887f24723`'),
    ('s16/payloads/mutants/', 'its per-mutant logs'),
    ('runs/main-2854ce.dylib', 'the landing baseline bridge, main `2854ce3e3`'),
    ('runs/census-main-2854ce/failed_roots.jsonl', 'the landing baseline census'),
    ('runs/census-main-2854ce/stderr.log', 'its body trace'),
    ('runs/census-main-2854ce.out', 'its summary'),
    ('runs/s16.dylib', 'the slice-16 bridge, `5b5b1d105`'),
    ('runs/census-s16/failed_roots.jsonl', 'the slice-16 census'),
    ('runs/census-s16/stderr.log', 'its body trace'),
    ('runs/census-s16.out', 'its summary'),
    ('runs/dump-s16/', 'its uncertified bodies\' queries'),
    ('s16/compare/', '`census_compare.py` of the two rows'),
    ('s16/logs/census_chain_kept.log', 'the census chain log'),
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
