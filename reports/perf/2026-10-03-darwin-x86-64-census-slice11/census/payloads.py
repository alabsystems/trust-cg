#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes and the SHA-256 of its manifest: one
line `<sha256>  <name>` per file, sorted by name, newline-terminated."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    ('runs/main-5495.dylib', 'the baseline bridge, `main` `5495c11b4`'),
    ('runs/census-main-5495/provenance.json', ''),
    ('runs/census-main-5495/failed_roots.jsonl', 'baseline failed roots'),
    ('runs/census-main-5495/stderr.log', 'baseline body trace'),
    ('runs/census-main-5495.out', 'baseline census summary'),
    ('runs/s11.dylib', 'the slice-11 bridge'),
    ('runs/census-s11/provenance.json', ''),
    ('runs/census-s11/failed_roots.jsonl', 'slice-11 failed roots'),
    ('runs/census-s11/gap_table.md', ''),
    ('runs/census-s11/refusals.jsonl', ''),
    ('runs/census-s11/stderr.log', 'slice-11 body trace'),
    ('runs/census-s11.out', 'slice-11 census summary'),
    ('runs/dump-s11/', 'the uncertified bodies\' queries, `x86-body-dump`'),
    ('s11/logs/census.log', '`census/census_s11.sh` log, both rows'),
    ('s11/payloads/compare/', '`census/census_compare.py` output'),
    ('s11/uncert_q/', 'the 21 uncertified class queries, from the dump'),
    ('s11/payloads/uncert_replay.tsv', 'their offline AY outcomes'),
    ('s11/ashr4/', 'the four former `bvashr` bodies\' slice-11 queries'),
    ('s11/payloads/ashr4_replay.tsv', 'their offline AY outcomes'),
    ('s11/cls_i128_param.txt', 'the class functions, `census/split_classes.py`'),
    ('s11/cls_i128_result.txt', ''),
    ('s11/cls_float_param.txt', ''),
    ('s11/cls_float_result.txt', ''),
    ('s11/cls_nonscalar_load.txt', ''),
    ('s11/cls_call_result.txt', ''),
    ('s11/dump_i128_param.txt', 'their LIR and pre-RA bodies, `census/dump_class.sh`'),
    ('s11/dump_float_param.txt', ''),
    ('s11/dump_float_result.txt', ''),
    ('s11/payloads/profile_i128_param.txt', '`census/profile.py`'),
    ('s11/payloads/profile_float_param.txt', ''),
    ('s11/payloads/profile_float_result.txt', ''),
    ('s11/sig_s11.tsv', 'the slice-11 owner over the cleaned `core` module (`--sig`)'),
    ('s11/payloads/class_verdicts.txt', '`census/class_verdicts.py`'),
    ('s11/smt_cls/', 'the bound class queries, offline'),
    ('s11/replay_cls.tsv', 'their offline AY outcomes'),
    ('s11/payloads/fp_replay.tsv', 'the floating-point probe (`fp/`)'),
    ('s11/payloads/qualification_first.log', 'qualification with the first spellings'),
    ('s11/payloads/qualification_second.log', 'after the constant CL count'),
    ('s11/payloads/qualification_slice1_first.log', 'slice 1 under the sign-extension spelling, before its records moved'),
    ('s11/variants1.tsv', 'spelling experiments, `census/variants.py`'),
    ('s11/variants2.tsv', '`census/variants2.py`'),
    ('s11/variants3.tsv', 'the census bodies respelled, `census/variants3.py`'),
    ('s11/orig31.tsv', 'the same bodies unchanged, control rerun'),
    ('s11/payloads/qualification_merged.log', '`fails-before/qualify.sh` on the merged tree'),
    ('s11/payloads/solver_free_body_suite.log', 'the solver-free body suite and `smt::`'),
    ('s11/payloads/wide_extract_before_fix.log', 'the same before the wide-`Extract` fix'),
    ('s11/payloads/mutants.txt', '`fails-before/run_mutants.sh` summary'),
    ('s11/payloads/gate_row.log', '`fails-before/gate_row.sh`'),
    ('s11/payloads/robustness_no_replay.log', 'robustness probe, sampler only'),
    ('s11/payloads/robustness_replay_first.log', 'robustness probe with AY replay, the first ground truth'),
    ('s11/payloads/robustness_replay.log', 'robustness probe with AY replay'),
    ('s11/logs/gates_stage1.log', '`~/tcg-scratch/gates_stage1.sh` on the merged tree'),
    ('s11/payloads/flake_rerun.log', 'its two failures rerun alone'),
    ('s11/payloads/e2e.log', 'the codegen end-to-end body test with output'),
    ('s11/logs/gates_full_rest.log', 'lower/opt/IR and codegen libraries and the CLI corpus (first run)'),
    ('s11/logs/gates_rest_libs.log', ''),
    ('s11/payloads/codegen_lib_first.log', 'the codegen library, first run (six out-of-lane devices in the lane)'),
    ('s11/payloads/codegen_six.log', 'those six (and one neighbour) after the move to a variable shift'),
    ('s11/logs/gates_rest_codegen2.log', 'the codegen library rerun'),
    ('s11/logs/gates_rest_cli.log', ''),
    ('s11/logs/test_soundness_check.log', '`scripts/test_soundness_check.sh`'),
    ('s11/logs/tippy.log', '`scripts/check_tippy.sh`'),
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
