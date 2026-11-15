#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes and the SHA-256 of its manifest: one
line `<sha256>  <name>` per file, sorted by name, newline-terminated."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    # The design and the class.
    ('s19-ay-design/', 'the design measurement: README'),
    ('s19-ay-design/data/', 'its data (classes, chains, replays)'),
    ('runs/census-ay13556/failed_roots.jsonl', 'the census row whose class this is'),
    ('runs/census-s20/failed_roots.jsonl', 'main fc03f94f2\'s census row (slice 20): the 41 still fail'),
    ('runs/census-s20/stderr.log', 'its body trace (the regression check\'s outcomes)'),
    ('runs/dump-s20/', 'its uncertified bodies\' queries (the probe control\'s reference)'),
    ('runs/core-ir-s20/', 'the trust-ir dump of `core` the probe reads'),
    ('s19/names41.txt', 'the 41 roots'),
    ('s19/names_wide.txt', 'the seven 128-bit add/sub functions'),
    ('s19/probe/x86_body_probe.rs', 'the probe (local only, never committed)'),
    # The real bytes.
    ('s19/redump/base20/smt2/', 'the probe on main fc03f94f2 (control): the 41 roots\' 208 queries'),
    ('s19/redump/s1/smt2/', 'stage 1 on bf5d4b2c9, before the wide-bits rule'),
    ('s19/redump/s1b/smt2/', 'stage 1 as committed'),
    ('s19/redump/s1b_mapped/', 'the same under the census file names'),
    ('s19/redump/s2b/smt2/', 'stage 2'),
    ('s19/redump/s2b_mapped/', 'the same under the census file names'),
    ('s19/redump/s3b/smt2/', 'stage 3 as first committed, with every split obligation\'s claims'),
    ('s19/redump/s3b_mapped_claims/', 'the claims under the census file names'),
    ('s19/redump/s3c/smt2/', 'the final code (the wide-bits rule without products), with claims'),
    ('s19/redump/s3c_mapped/', 'the same under the census file names'),
    ('s19/redump/s3c_mapped_claims/', 'its claims under the census file names'),
    ('s19/wide/', 'the seven wide functions on bf5d4b2c9: main\'s and stage 1\'s first bytes'),
    ('s19/redump/wide_base20_mapped/', 'the seven on main fc03f94f2'),
    ('s19/redump/wide_s1b_mapped/', 'the seven at stage 1 as committed'),
    ('s19/redump/wide_s3c_mapped/', 'the seven on the final code'),
    ('s19/sub128/', 'SubU128\'s query in slice 18\'s spelling, inlined, named, both claims'),
    ('s19/replay/results/fresh.jsonl', 'every one-shot replay, keyed by query SHA-256'),
    ('s19/replay/results/resident.jsonl', 'every resident replay'),
    ('s19/replay/results/wide.jsonl', 'the seven wide functions on bf5d4b2c9'),
    ('s19/logs/chain_meas2.log', 'the stage replays\' log'),
    ('s19/logs/chain_meas4.log', 'the claim replays\' log'),
    ('s19/logs/claims_resident.log', 'the claims\' resident leg'),
    # The whole core.
    ('s19/all/base20/smt2/', 'the probe over every function, main fc03f94f2'),
    ('s19/all/s3c/smt2/', 'the same, the final code'),
    ('s19/regress/s3c/changed.jsonl', 'every function whose bytes change, with its census-s20 outcome'),
    ('s19/regress/s3c/queries/', 'the census-certified ones\' new queries'),
    ('s19/logs/regress_s3c.log', 'their one-shot replay and the report'),
    # Goldens and review.
    ('s19/goldens-main20/', 'every golden on main fc03f94f2'),
    ('s19/goldens-s1m/', 'stage 1\'s goldens'),
    ('s19/goldens-s3m/', 'stage 2\'s and 3\'s goldens as first committed'),
    ('s19/goldens-final2/', 'the final goldens'),
    ('s19/review/stage1/review.jsonl', 'stage 1\'s golden review on bf5d4b2c9 (every file but slices 11 and 20)'),
    ('s19/review/stage1/z3/', 'its z3 queries'),
    ('s19/review/stage1m/out/review.jsonl', 'stage 1\'s review of slices 11 and 20 against main'),
    ('s19/review/stage1m/out/z3/', 'its z3 queries'),
    ('s19/review/stage2/review.jsonl', 'stage 2\'s golden review'),
    ('s19/review/stage2/z3/', 'its z3 queries'),
    # Controls, mutants, gates, qualification.
    ('s19/logs/slice19_s1m.txt', 'the slice-19 library tests on stage 1 (counts)'),
    ('s19/logs/slice19_s3m_stage23.txt', 'the stage-2 and stage-3 library tests (counts)'),
    ('s19/fails-before/stage1.txt', 'stage 1\'s mutants on bf5d4b2c9'),
    ('s19/mutants2/stage2.txt', 'stage 2\'s mutants on bf5d4b2c9'),
    ('s19/mutants3/stage12.txt', 'the wide-bits and two stage-2 mutants on fc03f94f2'),
    ('s19/mutants3/stage3.txt', 'stage 3\'s mutants'),
    ('s19/logs/gate_final.log', 'the solver-free body gate on stage 3 as first committed'),
    ('s19/qual/stage1/summary.txt', 'stage 1\'s qualification on bf5d4b2c9'),
    ('s19/qual/final/summary.txt', 'the final code\'s qualification'),
    ('s19/qual/final-rerun/summary.txt', 'the three moved lanes re-run with the updated records'),
    ('s19/logs/gate_final3.log', 'the solver-free body gate on the final code'),
    ('s19/logs/subset_final3.log', 'the slice-19, slice-18, slice-11 and golden tests on the final code'),
    ('s19/logs/gate_lower.log', 'trust-cg-lower --lib'),
    ('s19/logs/gate_codegen.log', 'the codegen gate'),
    ('s19/logs/gate_codegen_merged.log', 'the codegen gate after merging origin/main 5d732f441'),
    ('s19/logs/tippy_trust-cg-verify.log', 'the lint run the installed package refuses'),
    ('s19/logs/libtests_final.log', 'the fixture-solver library tests on the final code'),
    ('s19/logs/libcheck_main20.log', 'their failures run on main fc03f94f2'),
    ('s19/logs/libcheck_final4.log', 'and on the final code rebuilt'),
    ('runs/main-5d732f4.dylib', 'the landing baseline bridge, main `5d732f441`'),
    ('runs/census-main-5d732f4/failed_roots.jsonl', 'the landing baseline census'),
    ('runs/census-main-5d732f4/stderr.log', 'its body trace'),
    ('runs/census-main-5d732f4.out', 'its summary'),
    ('runs/s19.dylib', 'the slice-19 bridge, `427a6f3d6`'),
    ('runs/census-s19/failed_roots.jsonl', 'the slice-19 census'),
    ('runs/census-s19/stderr.log', 'its body trace'),
    ('runs/census-s19.out', 'its summary'),
    ('runs/dump-s19/', 'its uncertified bodies\' queries'),
    ('s19/compare/', '`census_compare.py` of the two rows'),
    ('s19/logs/census_chain_kept.log', 'the census chain log'),
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
