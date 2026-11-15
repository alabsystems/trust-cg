#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes and the SHA-256 of its manifest: one
line `<sha256>  <name>` per file, sorted by name, newline-terminated."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    # The class (the design's).
    ('s17-design/data/functions.tsv', 'the design\'s class: 51 functions, the group of each'),
    ('s17-design/data/class51_names.txt', 'the 51 names the probe is restricted to'),
    # The inputs.
    ('runs/core-ir-s9/', 'slice 9\'s core dump (the design\'s input)'),
    ('runs/core-ir-s16/', 'the core dump of main a902\'s bridge (the slice-16 record\'s)'),
    ('runs/core-ir-2854ce/', 'the core dump of main 2854ce\'s bridge (`census/dump_core_ir.sh`)'),
    # The probe over the class, final code.
    ('s17/payloads/probe_control_s16/', 'the control: slice 16\'s probe over a902\'s dump'),
    ('s17/probe/fin_s16/', 'slice 17\'s probe over a902\'s dump (final code): verdicts, stderr'),
    ('s17/probe/fin_s16/smt2/', 'its 133 queries and index'),
    ('s17/probe/fin_2854ce/', 'the same over 2854ce\'s dump'),
    ('s17/probe/fin_2854ce/smt2/', 'its 116 queries and index'),
    ('s17/probe/control_2854ce/', 'the control over 2854ce\'s dump'),
    ('s17/probe/fin_s9/', 'the same over slice 9\'s dump'),
    ('s17/payloads/measure_fin_s16.txt', '`census/measure_s17.py` over a902\'s dump, with the certification'),
    ('s17/payloads/measure_fin_2854ce.txt', 'the same over 2854ce\'s dump'),
    ('s17/payloads/measure_fin_s9.txt', 'the same over slice 9\'s dump (no replay)'),
    ('s17/payloads/probe_control_s9/', 'the control over slice 9\'s dump'),
    ('s17/probe/agep_2854ce/', 'slice 17\'s probe after the `ArrayGep` merge over 2854ce\'s dump: verdicts, stderr'),
    ('s17/probe/agep_2854ce/smt2/', 'its 126 queries and index'),
    ('s17/payloads/measure_agep_2854ce.txt', '`census/measure_s17.py` over it, with the certification'),
    ('s17/probe/agep_s16/', 'the same over a902\'s dump (queries byte-identical to before the merge)'),
    ('s17/logs/lir_all_2854ce.txt', 'every function of 2854ce\'s main CGU: its LIR and the owner\'s verdict (after the merge)'),
    ('s17/payloads/arms_s16.tsv', '`census/select_arms.py` over the chain-spelling queries (arm counts)'),
    # The probe over the whole crate.
    ('s17/payloads/core_control/', 'slice 16\'s probe over every function of a902\'s dump'),
    ('s17/payloads/core_s17/', 'slice 17\'s probe over every function of a902\'s dump'),
    ('s17/probe/core_diff_s17/', 'the 327 queries the dead-byte rule changes (slice 17)'),
    ('s17/probe/core_diff_control/', 'the same 327 queries (slice 16)'),
    # Offline certification.
    ('s17/payloads/replay_class_s16.tsv', 'the class\'s queries, linear-chain select, AY 12713 with Clean, 30 s'),
    ('s17/payloads/replay_lowbit_s16.tsv', 'the same, low-bit select'),
    ('s17/payloads/replay_vn_s16.tsv', 'the same, low-bit select and value numbering'),
    ('s17/payloads/replay_fin_s16.tsv', 'the same, final code'),
    ('s17/payloads/replay_fin_2854ce.tsv', 'the final code\'s queries over 2854ce\'s dump'),
    ('s17/payloads/replay_agep_2854ce.tsv', 'the final code\'s queries over 2854ce\'s dump after the `ArrayGep` merge'),
    ('s17/payloads/replay_core_diff_s17.tsv', 'the 327 dead-byte queries (slice 17), 30 s'),
    ('s17/payloads/replay_core_diff_control.tsv', 'the same queries (slice 16), 30 s'),
    ('s17/selects/', 'the 256-arm select, linear chain and low-bit by hand'),
    ('s17/slow/', 'StoreThenIndexedRead plain (73 s) and with its constants substituted (3 s)'),
    # Qualification.
    ('s17/payloads/qualification_final/', 'slice 17\'s three tool-gated tests on the final code'),
    ('s17/payloads/qualification_agep/', 'the tool-gated tests of slices 12, 16 and 17 and of ArrayGep on the ArrayGep merge, one per process'),
    ('s17/payloads/qualification_agep/queries/', 'every replayed slice-17 qualification query on the merge'),
    ('s17/payloads/qualification/', 'the tool-gated tests of slices 12, 16 and 17 before the ArrayGep merge'),
    ('s17/payloads/qualification/queries/', 'the 16 fixtures\' canonical queries then, written without a solver'),
    ('s17/payloads/qualification_last_merge/', 'the same tests on the merge of 4c6ce87e8'),
    ('s17/payloads/qualification_lowbit_unnumbered/', 'the slice-17 tests before value numbering'),
    ('s17/payloads/qualification_vn/', 'the slice-17 tests before the bit-move substitution'),
    # Gates, fails-before, robustness.
    ('s17/payloads/gate_body.log', 'the whole x86 body library gate (solver-free), final code'),
    ('s17/payloads/gate_slice17.log', 'the slice-17 library gate, final code'),
    ('s17/payloads/mutants/', '`fails-before/run_mutants.sh` on the final code (15 mutants), with each run\'s log'),
    ('s17/payloads/mutants_agep_first/', 'its first run on the merge, before the byte-bound control was fixed'),
    ('s17/payloads/mutants_chain/', 'the 13 on the chain spelling, after the control fix'),
    ('s17/payloads/mutants_first/', 'the first run, before the "machine in bounds" control was fixed'),
    ('s17/payloads/robustness.log', 'the robustness probe, no replay'),
    ('s17/payloads/robustness_replay_final.log', 'the robustness probe, every theorem replayed, final code'),
    ('runs/main-6191f36.dylib', 'the landing baseline bridge, main `6191f3621`'),
    ('runs/census-main-6191f36/failed_roots.jsonl', 'the landing baseline census'),
    ('runs/census-main-6191f36/stderr.log', 'its body trace'),
    ('runs/census-main-6191f36.out', 'its summary'),
    ('runs/s17.dylib', 'the slice-17 bridge, `ac8424004`'),
    ('runs/census-s17/failed_roots.jsonl', 'the slice-17 census'),
    ('runs/census-s17/stderr.log', 'its body trace'),
    ('runs/census-s17.out', 'its summary'),
    ('runs/dump-s17/', 'its uncertified bodies\' queries'),
    ('s17/compare/', '`census_compare.py` of the two rows'),
    ('s17/logs/census_chain_kept.log', 'the census chain log'),
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
