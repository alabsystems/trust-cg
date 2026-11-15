#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows of the OD-215 report (path relative to ~/tcg-scratch, bytes,
sha256): the lane's own payloads (i128sh-run, before the merge) and the merge's (i128sh-m1).

A directory's row is its total bytes over its top-level files and the SHA-256 of its manifest: one
line `<sha256>  <name>` per file, sorted by name, newline-terminated (slice 23's payloads23.py)."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    # The lane before the merge (head 3331ee136 for the gates; e0a052bc7 for the records).
    ('i128sh-run/final/summary.txt', 'the gates on 3331ee136 (one line per gate)'),
    ('i128sh-run/final/lower_lib.log', 'trust-cg-lower --lib'),
    ('i128sh-run/final/gate.log.summary', 'the x86 body suite'),
    ('i128sh-run/final/x86_source_bound_body.log', 'codegen --test x86_source_bound_body'),
    ('i128sh-run/final/e2e_x86_64_i128_const_shift.log', 'the native differential (O0-O3)'),
    ('i128sh-run/final/census_proxy3.log', 'the census proxy over core-ir-s22 (17 functions)'),
    ('i128sh-run/qual_v2/', 'the tool-gated lanes, one test per process (logs)'),
    ('i128sh-run/e2e_v1/const_shift_optout.log', 'the native differential with TCG_NO_X86_I128_CONST_SHIFT=1'),
    # The merge with origin/main e74f215c6 (merge commit 23565718e).
    ('i128sh-m1/logs/build_m1.log', 'the trust-cg-verify library test build on the merged tree'),
    ('i128sh-m1/testbin_m1', 'its test binary'),
    ('i128sh-m1/logs/golden_write_m1.log', 'every golden re-rendered (TCG_X86_BODY_SNAPSHOT_WRITE=1)'),
    ('i128sh-m1/logs/golden_write_m1.out', 'the digests it printed (each unchanged)'),
    ('i128sh-m1/goldens/origin_main/', 'every golden on origin/main e74f215c6'),
    ('i128sh-m1/goldens/bd2bbd3b9/', 'every golden on the branch before the merge'),
    ('i128sh-m1/goldens/merged_m1/', 'every golden re-rendered from the merged code'),
    ('i128sh-m1/review/out_vs_main.txt', 'the review against main (claims, validity, z3)'),
    ('i128sh-m1/review/out_vs_main/review.jsonl', 'its records'),
    ('i128sh-m1/review/out23_vs_main.txt', 'slice 23\'s strict review against main (names)'),
    ('i128sh-m1/review/out23_vs_branch.txt', 'slice 23\'s review against the branch'),
    ('i128sh-m1/review/out_vs_branch.txt', 'the claims review against the branch'),
    ('i128sh-m1/probe/x86_body_probe.rs', 'the probe source (s23-fix/probe\'s; never committed)'),
    ('i128sh-m1/probe/x86_body_probe_m1', 'the probe built from the merged tree'),
    ('i128sh-m1/logs/probe_build_m1.log', 'its build'),
    ('s23-fix/all/w5/cf.tsv', 'main\'s whole-core probe without the fold (slice 23\'s final head)'),
    ('s23-fix/all/w5/cf.err', 'its stderr (pairing records)'),
    ('i128sh-m1/all/m1/cf.tsv', 'the whole-core probe on the merged tree'),
    ('i128sh-m1/all/m1/cf.err', 'its stderr (pairing records)'),
    ('i128sh-m1/all/m1/smt2/', 'its queries'),
    ('i128sh-m1/all/m1off/cf.tsv', 'the same with TCG_NO_X86_I128_CONST_SHIFT=1'),
    ('i128sh-m1/all/m1off/smt2/', 'its queries'),
    ('i128sh-m1/logs/probe_diff_w5_m1off.txt', 'diff -r of main\'s queries and the fold-off run\'s (empty)'),
    ('i128sh-m1/all/cmp_w5_m1.txt', 'main against the merged tree, function by function'),
    ('i128sh-m1/all/cmp_w5_m1.changed.tsv', 'the 11 functions whose theorem bytes change'),
    ('i128sh-m1/all/cmp_w5_m1.cf_changed.tsv', 'the 17 functions whose selection changes'),
    ('i128sh-m1/all/cmp_w5_m1off.txt', 'main against the fold-off run'),
    ('i128sh-m1/all/pair_w5.txt', 'main\'s 30 paired owners (S23-PAIRING lines)'),
    ('i128sh-m1/all/pair_m1.txt', 'the merged tree\'s'),
    ('i128sh-m1/all/pair_m1off.txt', 'the fold-off run\'s'),
    ('i128sh-m1/logs/chain_probe_m1.txt', 'the probe chain\'s log'),
    ('i128sh-m1/stage/names20.txt', 'the 17 and slice 23\'s three roots'),
    ('i128sh-m1/stage/m1/q/', 'their units, claims, generalizations and arbiters, merged'),
    ('i128sh-m1/stage/m1off/q/', 'the same with the fold off (= main)'),
    ('i128sh-m1/replay/data/replays.jsonl', 'every one-shot replay (AY 13556, Clean 5f09e36c), keyed by the bytes\' sha256'),
    ('i128sh-m1/replay/chain_replay.txt', 'the replay chain\'s log'),
    ('i128sh-m1/replay/table_m1.md', 'every route per function'),
    ('i128sh-m1/replay/route_m1.md', 'the production route, merged'),
    ('i128sh-m1/replay/route_m1off.md', 'the production route, main'),
    ('i128sh-m1/logs/chain_gates_m1.txt', 'the gates chain\'s log'),
    ('i128sh-m1/logs/suite_m1.log', 'the solver-free x86 body suite'),
    ('i128sh-m1/qual_m1/summary.txt', 'the tool-gated lanes, one test per process'),
    ('i128sh-m1/logs/lower_m1.log', 'trust-cg-lower --lib'),
    ('i128sh-m1/logs/codegen_m1.log', 'the codegen targets'),
    ('i128sh-m1/logs/codegen_body_nocapture_m1.log', 'codegen x86_source_bound_body with --nocapture (the replay identity)'),
    ('i128sh-m1/logs/census_proxy_m1.log', 'the census proxy over core-ir-s23 on the merged code'),
    ('i128sh-m1/logs/fmt_m1.log', 'check_fmt.sh'),
    ('i128sh-m1/logs/doc_m1.log', 'check_documentation.py --check'),
    ('i128sh-m1/logs/matrix_m1.log', 'full_test_matrix_hosts.py --check (PATH)'),
    ('i128sh-m1/logs/matrix6808_m1.log', 'the same with TRUST_TARGO naming the 6808 targo'),
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
