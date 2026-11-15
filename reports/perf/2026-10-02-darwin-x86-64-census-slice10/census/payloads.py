#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes and the SHA-256 of its manifest: one
line `<sha256>  <name>` per file, sorted by name, newline-terminated."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    ('runs/main-ac04.dylib', 'the baseline bridge, `main` `ac0481810`'),
    ('runs/census-main-ac04/provenance.json', ''),
    ('runs/census-main-ac04/failed_roots.jsonl', 'baseline failed roots'),
    ('runs/census-main-ac04/stderr.log', 'baseline body trace'),
    ('runs/census-main-ac04.out', 'baseline census summary'),
    ('runs/s10.dylib', 'the slice-10 bridge, `99c2ca5cf`'),
    ('runs/census-s10/provenance.json', ''),
    ('runs/census-s10/failed_roots.jsonl', 'slice-10 failed roots'),
    ('runs/census-s10/gap_table.md', ''),
    ('runs/census-s10/refusals.jsonl', ''),
    ('runs/census-s10/stderr.log', 'slice-10 body trace'),
    ('runs/census-s10.out', 'slice-10 census summary'),
    ('runs/dump-s10/', 'the uncertified bodies\' queries, `x86-body-dump`'),
    ('s10/logs/census_s10.log', '`census/census_s10.sh` log'),
    ('s10/payloads/main_roots.tsv', 'baseline roots by first refusal, `census/classes.py`'),
    ('s10/payloads/s10_roots.tsv', 'slice-10 roots by first refusal'),
    ('s10/payloads/compare.txt', '`census/census_compare.py` output'),
    ('s10/payloads/promoted.txt', ''),
    ('s10/payloads/newly_failing.txt', ''),
    ('s10/payloads/slice10_transitions.tsv', 'the 164 class functions'),
    ('s10/uncert_q/', 'the 83 uncertified queries, replayed offline'),
    ('s10/payloads/uncert_replay.tsv', 'their offline AY outcomes'),
    ('s10/variants4/', 'the respelled unsigned add/sub queries, `census/variants4.py`'),
    ('s10/variants4.tsv', 'their AY outcomes'),
    ('s10/payloads/spellings.tsv', 'the fixture spelling experiments, `census/variants*.py`'),
    ('s10/payloads/qualification_first.log', 'qualification with the first spellings'),
    ('s10/payloads/qualification_first_spellings_and_gate.log', ''),
    ('s10/payloads/qualification.log', '`fails-before/qualify.sh`, the chosen spellings'),
    ('s10/payloads/credit.log', '`verifier_credits_every_bound_slice_ten_row_with_the_replayed_body_theorem`'),
    ('s10/payloads/solver_free_body_suite.log', 'the solver-free body suite (148 tests)'),
    ('s10/payloads/mutants.txt', '`fails-before/run_mutants.sh` summary'),
    ('s10/payloads/gate_row.log', '`fails-before/gate_row.sh`, the committed sampler'),
    ('s10/payloads/needle_old_sampler.log', 'the needle refutation under the sampler of `99c2ca5cf`'),
    ('s10/payloads/robustness_no_replay.log', 'robustness probe, sampler only'),
    ('s10/payloads/robustness_replay.log', 'robustness probe with AY replay'),
    ('s10/logs/gates_stage1_merged.log', '`~/tcg-scratch/gates_stage1.sh` on the merged tree'),
    ('s10/payloads/qualification_merged.log', '`fails-before/qualify.sh` on the merged tree'),
    ('s10/logs/gates_full_rest.log', 'codegen library and CLI must-refuse corpus on the merged tree'),
    ('s10/payloads/codegen_lib_rerun.log', 'the codegen library rerun, full log'),
    ('s10/payloads/jit_envelope_alone.log', 'the JIT envelope test alone'),
    ('s10/logs/tippy.log', '`scripts/check_tippy.sh` with the managed `targo`'),
]
for f, what in FILES:
    p = os.path.join(H, f)
    label = f'`{f}`' + (f' ({what})' if what else '')
    if not os.path.exists(p):
        print(f'| {label} | MISSING | |')
        continue
    if os.path.isdir(p):
        names = sorted(os.listdir(p))
        blobs = [open(os.path.join(p, n), 'rb').read() for n in names]
        manifest = ''.join(f'{hashlib.sha256(b).hexdigest()}  {n}\n' for n, b in zip(names, blobs))
        size = sum(len(b) for b in blobs)
        print(f'| {label} ({len(names)} files) | {size} | `{hashlib.sha256(manifest.encode()).hexdigest()}` (manifest) |')
        continue
    data = open(p, 'rb').read()
    print(f'| {label} | {len(data)} | `{hashlib.sha256(data).hexdigest()}` |')
