#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes and the SHA-256 of its manifest: one
line `<sha256>  <name>` per file, sorted by name, newline-terminated."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    # The design and its measurement (the class, the Python spelling's queries and replays).
    ('s18-design/', 'the design: README, DESIGN-DRAFT, RULING-DRAFT'),
    ('s18-design/data/', 'the design\'s measurement data (classes, respellings, replays)'),
    ('s18-design/queries/orig/', 'census-s17\'s 361 dumped queries (`runs/dump-s17/`, copied)'),
    ('s18-design/queries/v17/', 'the design\'s Python v17 spelling of the singles'),
    ('s18-design/queries/v16/', 'the design\'s Python v16 spelling of the singles'),
    ('runs/census-s17/failed_roots.jsonl', 'the census row whose class this is'),
    ('runs/s17.dylib', 'census-s17\'s bridge (`ac8424004`)'),
    # The real bytes.
    ('runs/core-ir-s17/', 'the trust-ir dump of `core` from census-s17\'s bridge (`census/dump_core_ir.sh`)'),
    ('s18/redump/names125.txt', 'the 125 functions the probe is restricted to'),
    ('s18/redump/baseline/smt2/', 'the probe on main `190b3e53d` (control): its 361 queries and index'),
    ('s18/redump/baseline-ff44/smt2/', 'the probe on main `ff44162f3` (control)'),
    ('s18/redump/B/smt2/', 'the probe with stage 1: its 361 queries and index'),
    ('s18/redump/B_mapped/', 'the same under the census file names (`census/compare_probe.py`)'),
    ('s18/replay/b_12713_fresh.jsonl', 'stage 1\'s singles on AY 12713, one-shot'),
    ('s18/replay/b_12713_resident.jsonl', 'the resident leg'),
    ('s18/replay/chain_B.log', 'the chain\'s log'),
    ('s18/replay/b_13556_fresh.jsonl', 'stage 1\'s singles on AY build 13556 (`ebde49de3`), one-shot'),
    ('s18/replay/b_13556_resident.jsonl', 'the resident leg on 13556'),
    # The goldens and their review.
    ('s18/goldens-old/', 'the 14 goldens before slice 18 (main `190b3e53d`)'),
    ('s18/review/stage1/review.jsonl', 'stage 1\'s golden review: sweep and z3 per changed theorem'),
    ('s18/review/stage1/table.md', 'its per-file table'),
    ('s18/review/stage1/z3/', 'the 368 z3 equivalence queries'),
    # Gates and qualification.
    ('s18/logs/gate-B3.log', 'the solver-free body gate on stage 1'),
    ('s18/logs/slice18-B3.txt', 'the slice-18 tests\' custody and sweep counts on stage 1'),
    ('s18/logs/golden-write-B.log', 'the golden rewrite run (`TCG_X86_BODY_SNAPSHOT_WRITE=1`)'),
    ('s18/qual/stage1/', 'stage 1\'s qualification, one test per process: logs and summary'),
    ('s18/qual/stage1-rerun/', 'the re-run of the moved lanes with the updated tables'),
    ('s18/qual/stage1-gaps300/gaps300.jsonl', 'the six re-spelled gaps at a 300 s budget'),
    ('s18/mutants1/', 'stage 1\'s mutants (`fails-before/run_mutants.sh`): the summary and each run\'s log'),
    # Stage 2.
    ('s18-design/queries/v18fs/', 'the design\'s Python fold-and-bvsub-zero spelling of the singles'),
    ('s18/redump/C/smt2/', 'the probe with stage 2: its 361 queries and index'),
    ('s18/redump/C_mapped/', 'the same under the census file names'),
    ('s18/redump/C_diffs.txt', 'the 14 singles whose assertion differs from the design\'s'),
    ('s18/replay/c_12713_fresh.jsonl', 'stage 2\'s singles on AY 12713, one-shot'),
    ('s18/replay/c_12713_resident.jsonl', 'the resident leg'),
    ('s18/replay/c_13556_fresh.jsonl', 'stage 2\'s singles on AY build 13556, one-shot'),
    ('s18/replay/c_13556_resident.jsonl', 'the resident leg on 13556'),
    ('s18/replay/cno/cno.jsonl', 'can_not_overflow\'s query three times on a quiet host'),
    ('s18/goldens-s1/', 'the 14 goldens of stage 1'),
    ('s18/review/stage2/review.jsonl', 'stage 2\'s golden review: sweep and z3 per changed theorem'),
    ('s18/review/stage2/z3/', 'the 208 z3 equivalence queries'),
    ('s18/logs/gate-C4.log', 'the solver-free body gate on stage 2'),
    ('s18/logs/slice18-C4.txt', 'the slice-18 tests\' custody and sweep counts on stage 2'),
    ('s18/qual/stage2/', 'stage 2\'s qualification, one test per process'),
    ('s18/qual/stage2-rerun/', 'slice 12\'s lanes with the updated table'),
    ('s18/qual/stage2-gaps300/gaps300.jsonl', 'the two re-spelled slice-14 gaps at a 300 s budget'),
    ('s18/mutants2/', 'stage 2\'s mutants over the spelling controls (`filters.txt`)'),
    # Stage 3.
    ('s18-design/queries/v17p/', 'the design\'s Python second spelling of the parts'),
    ('s18/redump/D/smt2/', 'the probe with stage 3: its 344 queries and index'),
    ('s18/redump/D_parts/', 'its 253 parts under their region\'s original part name'),
    ('s18/redump/D_aligned.json', 'the region alignment of the parts'),
    ('s18/replay/d_12713_fresh.jsonl', 'stage 3\'s parts on AY 12713, one-shot'),
    ('s18/replay/d_12713_resident.jsonl', 'the resident leg'),
    ('s18/review/stage3/out/review.jsonl', 'the parts golden\'s review: sweep and z3 per changed part'),
    ('s18/qual/stage3/', 'the stage-3 code\'s qualification ledger, one test per process'),
    ('s18/mutants3/', 'stage 3\'s mutants over the slice-16 and slice-18 library tests'),
    ('s18/mutants3b/', 'the bit-move unit test unmutated and under `respell-no-bit-moves`'),
    ('s18/qual/stage3-rerun/', 'slice 16\'s host lane with the shrunk unrefuted record'),
    ('s18/logs/gate-D4.log', 'the solver-free body gate on stage 3 (the final code)'),
    ('s18/review/stage3/out/Q/', 'the parts golden\'s changed parts, old and new'),
    ('s18/review/stage3/out/z3/', 'their z3 equivalence queries, both directions'),
    # The constant folds against z3.
    ('s18/review/z3folds-test/', 'the local test that dumps the fold sweep\'s folds (never committed)'),
    ('s18/review/z3folds/folds.txt', 'its dump: 32651 folds'),
    ('s18/review/z3folds/', 'the z3 queries (`review/z3_folds.py`), the planted control and `result.log`'),
    ('runs/main-4a65bc3.dylib', 'the landing baseline bridge, main `4a65bc3cf`'),
    ('runs/census-main-4a65bc3/failed_roots.jsonl', 'the landing baseline census'),
    ('runs/census-main-4a65bc3/stderr.log', 'its body trace'),
    ('runs/census-main-4a65bc3.out', 'its summary'),
    ('runs/s18.dylib', 'the slice-18 bridge, `ab1f6051d`'),
    ('runs/census-s18/failed_roots.jsonl', 'the slice-18 census'),
    ('runs/census-s18/stderr.log', 'its body trace'),
    ('runs/census-s18.out', 'its summary'),
    ('runs/dump-s18/', 'its uncertified bodies\' queries'),
    ('s18/compare/', '`census_compare.py` of the two rows'),
    ('s18/newly_failing/', 'the newly failing queries and their offline replay on AY 12713 and 13556'),
    ('s18/logs/census_chain_kept.log', 'the census chain log'),
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
