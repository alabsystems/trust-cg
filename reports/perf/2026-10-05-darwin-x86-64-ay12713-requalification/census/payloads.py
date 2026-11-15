#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes and the SHA-256 of its manifest: one
line `<sha256>  <name>` per file, sorted by name, newline-terminated."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
R = 'runs/requal-12713'
FILES = [
    (f'{R}/overlays/x86-stage1-ay12713.overlay.json', 'the root overlay\'s manifest'),
    (f'{R}/overlays/x86-stage0-bridge-ay12713.overlay.json', 'the bridge overlay\'s manifest'),
    (f'{R}/overlays/x86-stage0-bridge-ay12713.trustc-wrapper', 'its rewritten `bin/trustc`'),
    (f'{R}/build_verify.log', 'the first overlay build of trust-cg-verify\'s lib tests'),
    (f'{R}/measure1.log', 'qualification under the old identity: every outcome printed'),
    (f'{R}/measure2.log', 'qualification and credit tests under the new tables'),
    (f'{R}/matrix_capture.txt', 'the qualification matrix capture (`TCG_X86_BODY_QUALIFICATION_MATRIX=1`)'),
    (f'{R}/matrix/', 'its export, `scripts/export_x86_qualification_matrix.py`'),
    (f'{R}/body_new.tsv', 'slice 1\'s matrix on build 12713, `replay/replay_matrix.py`'),
    (f'{R}/qdump/', 'the canonical queries the qualification replayed (`TCG_X86_BODY_QUALIFY_DUMP`)'),
    (f'{R}/inv/changed_replay.tsv', 'the changed fixtures offline, both AYs (`replay/investigate*.sh`)'),
    (f'{R}/inv/mulcommuted_new.tsv', '`Mul/commuted` offline, 300 s'),
    (f'{R}/inv/pairjoin_merged.tsv', '`PairJoin` merged offline'),
    (f'{R}/inv/pairjoin_clean_time.txt', 'its AY and Clean times'),
    (f'{R}/inv/subu128_bisect.tsv', '`SubU128` on builds 10530, 12515, 12519, 12713'),
    (f'{R}/inv/sub_new.err', '`SubU128` `--stats-full`, build 12713'),
    (f'{R}/inv/sub_old.err', 'the same, build 10530'),
    (f'{R}/inv/mul32_routes.tsv', 'the bridge\'s `mul32` query on both routes, both AYs'),
    (f'{R}/smoke-new/stderr.log', '`replay/smoke.sh` through the first overlay bridge'),
    (f'{R}/smoke-new/dump/', 'its dumped queries'),
    (f'{R}/prod_s11_sample_new.tsv', 'the live replay protocol on 40 of the slice-11 census\'s 381 uncertified texts'),
    (f'{R}/refut_new.tsv', 'every counterexample of `measure2`'),
    (f'{R}/cex_check.tsv', 'their z3 checks, `replay/check_all_cex.py`'),
    (f'{R}/bridge_build2.log', 'the census bridge\'s build (`build_bridge.sh`, at the requalification commit)'),
    ('runs/main-6b10.dylib', 'the baseline bridge, `main` `6b108b81d` (built by the slice-13 lane)'),
    ('runs/census-main-6b10/provenance.json', ''),
    ('runs/census-main-6b10/failed_roots.jsonl', 'baseline failed roots'),
    ('runs/census-main-6b10/stderr.log', 'baseline body trace'),
    ('runs/ay12713.dylib', 'the overlay bridge'),
    ('runs/census-ay12713/provenance.json', ''),
    ('runs/census-ay12713/failed_roots.jsonl', 'overlay-bridge failed roots'),
    ('runs/census-ay12713/stderr.log', 'overlay-bridge body trace'),
    ('runs/census-ay12713.out', 'overlay-bridge census summary'),
    ('runs/dump-ay12713/', 'the uncertified bodies\' queries, `x86-body-dump`'),
    (f'{R}/census.log', '`census/census_ay12713.sh` log'),
    (f'{R}/census_host.log', 'free disk, load and reclaimable pages each minute of the census'),
    (f'{R}/census_discarded_diskfull.log', 'the discarded first run\'s log (disk full 10:45-11:05)'),
    (f'{R}/negmemo_discarded/', 'the negative-memo entries that run wrote, moved out of the store'),
    (f'{R}/compare/', '`census/census_compare.py` output'),
    (f'{R}/newly/', 'the three newly failing bodies\' queries and both AYs\' routes on them (`routes.tsv`)'),
    (f'{R}/prod_census98_new.tsv', 'the live replay protocol, offline, on the 76 uncertified texts of the census'),
    (f'{R}/oneshot_resident_deadline.tsv', 'the one-shot route on the 34 of them whose resident route ran out'),
    (f'{R}/classes_base.txt', '`root_classes.py`, baseline'),
    (f'{R}/classes_new.txt', '`root_classes.py`, overlay bridge'),
    (f'{R}/gates_full_combined.log', '`~/tcg-scratch/gates_full_stage1.sh` on the overlay (its filtered output)'),
    (f'{R}/negmemo_overlay.log', 'the negative-memo controls on the overlay build, before the fixture record'),
    (f'{R}/gate_verify1.log', 'the verify step of `gates_stage1.sh`, complete output, after the fixture record'),
    (f'{R}/e2e.log', 'the codegen end-to-end body test with output'),
    (f'{R}/gates_alltargets.log', '`build --workspace --lib --tests --keep-going` of every test target'),
    (f'{R}/tippy.log', '`scripts/check_tippy.sh`'),
]
for f, what in FILES:
    p = os.path.join(H, f)
    label = f'`{f}`' + (f' ({what})' if what else '')
    if not os.path.exists(p):
        print(f'| {label} | MISSING | |')
        continue
    if os.path.isdir(p):
        names = sorted(os.listdir(p))
        blobs = [open(os.path.join(p, n), 'rb').read() for n in names
                 if os.path.isfile(os.path.join(p, n))]
        names = [n for n in names if os.path.isfile(os.path.join(p, n))]
        manifest = ''.join(f'{hashlib.sha256(b).hexdigest()}  {n}\n' for n, b in zip(names, blobs))
        size = sum(len(b) for b in blobs)
        print(f'| {label} ({len(names)} files) | {size} | `{hashlib.sha256(manifest.encode()).hexdigest()}` (manifest) |')
        continue
    data = open(p, 'rb').read()
    print(f'| {label} | {len(data)} | `{hashlib.sha256(data).hexdigest()}` |')
