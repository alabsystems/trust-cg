#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes and the SHA-256 of its manifest: one
line `<sha256>  <name>` per file, sorted by name, newline-terminated. A path
that does not exist prints a row saying so, never a guessed digest."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
MAIN = 's15-main-cf98'
S15 = 's15-cf98'
FILES = [
    ('runs/census-s13-12713/failed_roots.jsonl', 'the measurement row\'s failed roots (the slice-13 census)'),
    ('runs/census-s13-12713/stderr.log', 'its body trace'),
    ('s15/s13_roots.tsv', 'its roots by function and last trace (`census/roots_full.py`)'),
    (f'runs/{MAIN}.dylib', 'the baseline bridge, `main` `cf982f936`'),
    (f'runs/census-{MAIN}/provenance.json', ''),
    (f'runs/census-{MAIN}/failed_roots.jsonl', 'baseline failed roots'),
    (f'runs/census-{MAIN}/stderr.log', 'baseline body trace'),
    (f'runs/census-{MAIN}.out', 'baseline census summary'),
    (f'runs/dump-{MAIN}/', 'the baseline\'s uncertified bodies\' queries'),
    (f'runs/{S15}.dylib', 'the slice-15 bridge, `6770368eb`'),
    (f'runs/census-{S15}/provenance.json', ''),
    (f'runs/census-{S15}/failed_roots.jsonl', 'slice-15 failed roots'),
    (f'runs/census-{S15}/stderr.log', 'slice-15 body trace'),
    (f'runs/census-{S15}.out', 'slice-15 census summary'),
    (f'runs/dump-{S15}/', 'the slice-15 uncertified bodies\' queries (`x86-body-dump`)'),
    ('s15/logs/bridge_main.log', 'the baseline bridge build'),
    ('s15/logs/bridge_s15.log', 'the slice-15 bridge build'),
    ('s15/logs/census_main.log', '`census/census_s15.sh` log, baseline'),
    ('s15/logs/census_s15.log', '`census/census_s15.sh` log, slice 15'),
    ('s15/payloads/compare/', '`census/census_compare.py`, baseline to slice 15'),
    ('s15/payloads/compare_main_vs_s13/', '`census/census_compare.py`, slice-13 row to baseline'),
    ('s15/uncert15/', 'the 9 uncertified class queries, from the dump'),
    ('s15/payloads/uncert_replay_12713.tsv', 'their offline production-protocol outcomes'),
    ('s15/payloads/uncert_replay_12713.log', ''),
    ('s15/payloads/qualification.log', 'the slice-15 gate row and host qualification, 22 fixtures and 14 refutations'),
    ('s15/payloads/mutant_logs/', 'the rule mutants: `mutants.txt` (final), `mutants_first.txt` (the first run, a transcript copy of its summary: the file itself was overwritten by the rerun), `mutants_base.txt`, `mutants_alu.txt`, `mutants_lower.txt` and each mutant\'s test log'),
    ('s15/payloads/robustness_no_replay_first.log', 'robustness probe, sampler only, first run'),
    ('s15/payloads/robustness_replay.log', 'robustness probe with AY replay'),
    ('s15/payloads/e2e.log', 'the codegen end-to-end body test and must-refuse corpus'),
    ('s15/payloads/e2e_rerun.log', 'the end-to-end body test alone'),
    ('s15/payloads/e2e_without_slice9.log', 'the promotion test with slice 9 left out (diagnostic edit)'),
    ('s15/payloads/check_merged.log', 'every workspace library and test target type-checked'),
    ('s15/payloads/check_merged2.log', 'the same after the second merge'),
    ('s15/payloads/check_verify_after_fix.log', 'the verify crate after gating main\'s unused import'),
    ('s15/payloads/qualification_merged.log', 'the slice-15 row and qualification on the second merge'),
    ('s15/payloads/verify_body_serial.log', 'the verify body library, serially, with AY and Clean'),
    ('s15/payloads/rerun_slice9_memo.log', 'slice 9\'s qualification and the memo test rerun'),
    ('s15/payloads/libs_ilo.log', 'IR, lowering and optimizer libraries'),
    ('s15/payloads/libs_codegen.log', 'codegen library'),
    ('s15/payloads/cli_must_refuse.log', 'CLI must-refuse corpus'),
    ('s15/payloads/test_soundness_check.log', '`scripts/test_soundness_check.sh`'),
]


def digest(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


for rel, what in FILES:
    path = os.path.join(H, rel)
    label = f'`{rel}`' + (f' ({what})' if what else '')
    if rel.endswith('/'):
        if not os.path.isdir(path):
            print(f'| {label} | — | (absent) |')
            continue
        names = sorted(os.listdir(path))
        manifest = ''.join(f'{digest(os.path.join(path, n))}  {n}\n' for n in names)
        size = sum(os.path.getsize(os.path.join(path, n)) for n in names)
        sha = hashlib.sha256(manifest.encode()).hexdigest()
        print(f'| {label} ({len(names)} files) | {size} | `{sha}` (manifest) |')
    else:
        if not os.path.isfile(path):
            print(f'| {label} | — | (absent) |')
            continue
        print(f'| {label} | {os.path.getsize(path)} | `{digest(path)}` |')
