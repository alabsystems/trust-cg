#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes and the SHA-256 of its manifest: one
line `<sha256>  <name>` per file, sorted by name, newline-terminated."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    # The class, measured first (the slice-9 census and dump).
    ('runs/census-s9b/failed_roots.jsonl', 'the slice-9 census the class was measured on'),
    ('runs/census-s9b/stderr.log', 'its body trace'),
    ('s12/payloads/roots.txt', 'the class roots, `census/loop_roots.py`'),
    ('s12/payloads/all.txt', 'the class functions'),
    ('s12/payloads/loops_main.tsv', 'the probe\'s `--loops` mode over the slice-9 dump'),
    ('s12/payloads/loop_profile.txt', '`census/loop_profile.py`'),
    ('s12/payloads/cf_main.tsv', 'the main owner over the dump (`--cf`)'),
    ('s12/payloads/cf_s12.tsv', 'the slice-12 owner over the dump, before the merges'),
    ('s12/payloads/newly_bound.txt', 'bound by slice 12 only, `census/newly_bound.py`'),
    ('s12/payloads/q2/', 'their queries'),
    ('s12/payloads/replay_q2.tsv', 'their offline outcomes on AY build 10530'),
    ('s12/payloads/replay_q2_12713.tsv', 'their offline outcomes on AY build 12713'),
    ('s12/payloads/final_probe/cf_final.tsv', 'the final owner over the dump (`--cf`)'),
    # Qualification.
    ('s12/payloads/qualification_b10530.log', 'host qualification on AY build 10530 (before the merges)'),
    ('s12/payloads/fixture_queries/', 'the fixture and refutation queries, build-10530 tree'),
    ('s12/payloads/qualification_12713.log', 'host qualification on AY build 12713 (final tree)'),
    ('s12/payloads/fixture_queries_12713/', 'the fixture and refutation queries, final tree'),
    ('s12/payloads/fixture_replay_12713.tsv', 'the fixture queries offline on build 12713, before the merges'),
    ('s12/payloads/earlyexit_long.tsv', 'EarlyExit with a 200 s budget'),
    # Fails-before and robustness.
    ('s12/payloads/mutants_premerge/', '`fails-before/run_mutants.sh` on `2316cdeac`'),
    ('s12/payloads/mutants.txt', '`fails-before/run_mutants.sh` on the final tree'),
    ('s12/payloads/robustness_no_replay_first.log', 'robustness probe, sampler only, no source retry'),
    ('s12/payloads/robustness_no_replay_second.log', 'robustness probe, sampler only, a fixed retry pool'),
    ('s12/payloads/robustness_no_replay_final.log', 'robustness probe, sampler only'),
    ('s12/payloads/robustness_replay.log', 'robustness probe with the AY replay'),
    # Census.
    ('runs/census-s13-12713/failed_roots.jsonl', 'the baseline: main `360eecafa` on AY build 12713 (slice 13\'s row)'),
    ('runs/census-s13-12713/stderr.log', 'its body trace'),
    ('runs/s12m.dylib', 'the merged tree\'s first bridge (`9d6308215`)'),
    ('runs/census-s12m/failed_roots.jsonl', 'its census'),
    ('runs/census-s12m/stderr.log', ''),
    ('s12/payloads/compare/', '`census/census_compare.py` against the baseline'),
    ('s12/payloads/refuted/', 'the two refuted bodies\' queries and counterexample'),
    ('s12/payloads/newly_failing/', 'the newly failing bodies\' queries'),
    ('s12/payloads/newly_failing.tsv', 'their offline outcomes'),
    ('runs/s12f.dylib', 'the second bridge (`55e42a730`)'),
    ('runs/census-s12f/failed_roots.jsonl', 'its census'),
    ('runs/census-s12f/stderr.log', ''),
    ('s12/payloads/compare_final/', '`census/census_compare.py`'),
    ('s12/payloads/refuted_final/', 'add_small\'s queries, counterexample and probe, before and after'),
    ('runs/s12z.dylib', 'the final bridge (`5bc8bd533`)'),
    ('runs/census-s12z/failed_roots.jsonl', 'the final census'),
    ('runs/census-s12z/stderr.log', 'its body trace'),
    ('runs/census-s12z.out', 'its summary'),
    ('runs/dump-s12z/', 'its uncertified bodies\' queries'),
    ('s12/payloads/compare_z/', '`census/census_compare.py` against the baseline'),
    # Landing: slice 12 merged with slice 15 and main `f6dcad152` (balanced conjunctions).
    ('runs/main-f6dc.dylib', 'main `f6dcad152`\'s bridge, the landing baseline'),
    ('runs/census-main-f6dc/failed_roots.jsonl', 'its census'),
    ('runs/census-main-f6dc/stderr.log', 'its body trace'),
    ('runs/census-main-f6dc.out', 'its summary'),
    ('runs/s12-land.dylib', 'the landing tree\'s bridge (`fca48f987`)'),
    ('runs/census-s12-land/failed_roots.jsonl', 'its census'),
    ('runs/census-s12-land/stderr.log', 'its body trace'),
    ('runs/census-s12-land.out', 'its summary'),
    ('runs/dump-s12-land/', 'its uncertified bodies\' queries'),
    ('s12/payloads/compare_land/', '`census/census_compare.py` against the landing baseline'),
    ('s12/logs/qual_9_11_alone.log', 'slice 9/11 host qualification on the landing tree, one process'),
    ('s12/logs/qual_live.log', 'slice 9 and 11 host qualification, each alone in its own process'),
    ('s12/logs/qual_9_11_ledger.log', 'slice 9/11 qualification and verifier credit on the updated ledger'),
    ('s12/logs/gates_land.log', '`gates_full_stage1.sh` and the rest on the landing tree'),
    ('s12/payloads/slotu128/', '`SlotU128` right-spine and balanced queries (300 s budget), paired runs on AY 12713, AY main and AY `8d6d17ad1`'),
    # Gates.
    ('s12/logs/gates_stage1_premerge_ay.log', '`gates_stage1.sh` on `2316cdeac` (AY build 10530)'),
    ('s12/logs/gates_rest_premerge.log', 'the IR, lowering, optimizer and codegen libraries there'),
    ('s12/logs/flake_rerun.log', 'the envelope JIT replay test rerun alone'),
    ('s12/logs/notest_compile.log', 'the `--lib --tests --keep-going` build there'),
    ('s12/logs/test_soundness_check.log', '`scripts/test_soundness_check.sh`'),
    ('s12/logs/tippy.log', '`scripts/check_tippy.sh` (cannot run here)'),
    ('s12/logs/gates_full_final.log', '`gates_full_stage1.sh` on the final tree (AY build 12713)'),
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
