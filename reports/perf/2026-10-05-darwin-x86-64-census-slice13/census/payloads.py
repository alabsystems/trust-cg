#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes and the SHA-256 of its manifest: one
line `<sha256>  <name>` per file, sorted by name, newline-terminated."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    ('runs/main-6b10.dylib', 'the baseline bridge, `main` `6b108b81d`'),
    ('runs/census-main-6b10/provenance.json', ''),
    ('runs/census-main-6b10/failed_roots.jsonl', 'baseline failed roots'),
    ('runs/census-main-6b10/stderr.log', 'baseline body trace'),
    ('runs/census-main-6b10.out', 'baseline census summary'),
    ('runs/dump-main-6b10/', 'the baseline\'s uncertified bodies\' queries'),
    ('runs/ay12713.dylib', 'the build-12713 baseline bridge (the requalification\'s)'),
    ('runs/census-ay12713/failed_roots.jsonl', 'build-12713 baseline failed roots'),
    ('runs/census-ay12713/stderr.log', 'build-12713 baseline body trace'),
    ('runs/s13-12713.dylib', 'the slice-13 bridge, build 12713, from `90608b684`'),
    ('runs/census-s13-12713/provenance.json', ''),
    ('runs/census-s13-12713/failed_roots.jsonl', 'slice-13 failed roots'),
    ('runs/census-s13-12713/stderr.log', 'slice-13 body trace'),
    ('runs/census-s13-12713.out', 'slice-13 census summary'),
    ('runs/dump-s13-12713/', 'the uncertified bodies\' queries, `x86-body-dump`'),
    ('s13/logs/census_main.log', '`census/census_s13.sh` log, `main-6b10`'),
    ('s13/logs/census_s13_12713.log', '`census/census_s13_ay12713.sh` log, slice 13'),
    ('s13/logs/bridge_main.log', 'the `main-6b10` bridge build'),
    ('s13/logs/bridge_s13_12713.log', 'the slice-13 bridge build, build 12713'),
    ('s13/payloads/ay12713_roots.tsv', 'build-12713 baseline roots by function and last trace'),
    ('s13/payloads/classes_ay12713.txt', 'its class counts'),
    ('s13/uncert13/', 'the 9 uncertified class queries, from the dump'),
    ('s13/payloads/uncert_replay_12713.tsv', 'their offline production-protocol outcomes'),
    ('s13/payloads/uncert_replay_12713.log', ''),
    ('s13/payloads/main_roots.tsv', 'baseline roots by function and last trace, `census/roots_by_class.py`'),
    ('s13/payloads/classes.txt', 'the class counts, `census/split13.py`'),
    ('s13/payloads/classes/', 'the class files'),
    ('s13/payloads/compare/', '`census/census_compare.py` output'),
    ('s13/s11_roots.tsv', 'the slice-11 census\'s roots (the first measurement)'),
    ('s13/s9b_roots.tsv', 'the slice-9 census\'s roots'),
    ('s13/dump_escape.txt', 'the stored-address bodies, `census/dump_class.sh`'),
    ('s13/dump_params.txt', 'the stack-parameter bodies'),
    ('s13/dump_call.txt', 'the call bodies'),
    ('s13/dump_mem.txt', 'the memory-routine bodies'),
    ('s13/dump_atomic.txt', 'the atomic bodies'),
    ('s13/dump_boolload.txt', 'the bool-read bodies'),
    ('s13/sig_main.tsv', '`main`\'s owner over the cleaned `core` module (`--sig`)'),
    ('s13/sig_wip.tsv', 'the slice-13 owner over the same module'),
    ('s13/payloads/qualification.log', 'host qualification, 20 fixtures and 15 refutations'),
    ('s13/payloads/mutants.txt', '`fails-before/run_mutants.sh` summary, first run'),
    ('s13/payloads/mutants2.txt', 'the two sharpened controls'),
    ('s13/payloads/mutant_logs/', 'the per-mutant test logs'),
    ('s13/payloads/robustness_no_replay_first.log', 'robustness probe, sampler only, first run'),
    ('s13/payloads/robustness_no_replay.log', 'robustness probe, sampler only'),
    ('s13/payloads/robustness_replay.log', 'robustness probe with AY replay'),
    ('s13/payloads/e2e.log', 'the codegen end-to-end body test'),
    ('s13/payloads/test_soundness_check.log', '`scripts/test_soundness_check.sh`'),
    ('s13/payloads/gates_b10530.log', 'the branch gates on AY build 10530'),
    ('s13/payloads/flake_rerun.log', 'the memory credit test rerun alone'),
    ('s13/payloads/robustness_replay_19.log', 'robustness probe with replay, before `TwoAddrsToOut`'),
    ('s13/payloads/qualification_ay12713_trial.log', 'slice-13 qualification on build 12713, merged tree'),
    ('s13/payloads/e2e_ay12713_trial.log', 'the end-to-end test on build 12713, merged tree'),
    ('s13/payloads/robustness_replay_ay12713.log', 'robustness probe on build 12713, merged tree'),
    ('s13/payloads/gates_ay12713_trial.log', 'the build-12713 gates, merged tree, beside the requalification census'),
    ('s13/payloads/qualification_serial_ay12713_trial.log', 'their failed qualification tests rerun serially'),
    ('s13/payloads/build_x86_tests_trial.log', 'every x86 test target compiled, merged tree'),
    ('s13/payloads/verify_body_serial_ay12713_trial.log', 'the whole verify body library serially, build 12713'),
    ('s13/payloads/requal_tree_memo_envelope.log', 'the negative-memo and envelope tests on the requalification tree'),
    ('s13/payloads/merged_verify_ay12713.log', 'the verify tests on the merged tree, build 12713'),
    ('s13/payloads/merged_codegen_ay12713.log', 'the codegen tests on the merged tree, build 12713'),
    ('s13/payloads/test_soundness_check_merged.log', '`scripts/test_soundness_check.sh` on the merged tree'),
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
