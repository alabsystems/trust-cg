#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes and the SHA-256 of its manifest: one line
`<sha256>  <relative path>` per file under it, recursively, sorted by relative
path, newline-terminated."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
R = 'runs/requal-13556/'
FILES = [
    # The AY and the overlays.
    ('ay-cert/bin/ay-main-ebde49de3', 'the AY 13556 binary the overlays carry as `bin/ay`'),
    ('ay-cert/bin/ay-main-ebde49de3.banner', 'its `--version` banner'),
    (R + 'overlays/x86-stage1-ay13556.overlay.json', 'the root overlay\'s manifest'),
    (R + 'overlays/x86-stage0-bridge-ay13556.overlay.json', 'the bridge overlay\'s manifest'),
    (R + 'overlays/x86-stage0-bridge-ay13556.trustc-wrapper', 'its rewritten `bin/trustc`'),
    # Builds.
    (R + 'build_verify1.log', 'trust-cg-verify\'s lib tests on the overlay, `QUALIFIED_AY` moved'),
    (R + 'build_verify2.log', 'the same with the new tables'),
    (R + 'build_gates1.log', 'the codegen and trust-cg-lower test targets on the overlay'),
    (R + 'verify-measure1.bin', '`measure1`\'s test binary'),
    (R + 'verify-measure2.bin', '`measure2`\'s test binary'),
    (R + 'build_verify3.log', 'trust-cg-verify\'s lib tests on the tree merged with origin/main `f75a45cc1`'),
    (R + 'verify-measure3.bin', '`measure3`\'s test binary'),
    # Qualification.
    ('s18/qual/stage3/', 'the baseline: slice 18\'s final ledger on AY 12713 (logs, summary, dumped queries)'),
    (R + 'measure1/', '`measure1`: the 40 tool-gated tests, one per process, `QUALIFIED_AY` moved, old tables'),
    (R + 'measure2/', '`measure2`: the same with the new tables'),
    (R + 'measure3/', '`measure3`: the same on the tree merged with origin/main `f75a45cc1`'),
    (R + 'gaps300.tsv', 'every remaining gap and `SubU128` offline at 300 s on AY 13556 (`replay/gaps300.sh`)'),
    (R + 'both_ays.tsv', 'slice 9\'s `StoreJoin` and slice 11\'s `SubU128` on both routes and both AYs'),
    ('ay-fix/land2/storejoin/', 'the AY agent\'s export of the `StoreJoin` and `SlotU128` spellings before slice 18'),
    (R + 'storejoin_prev_spellings.tsv', 'those spellings on both routes and both AYs'),
    (R + 'matrix_capture.txt', 'the qualification matrix capture (`TCG_X86_BODY_QUALIFICATION_MATRIX=1`)'),
    (R + 'cex_check_measure1.tsv', '`replay/check_all_cex.py` on `measure1`'),
    (R + 'cex_check_measure2.tsv', '`replay/check_all_cex.py` on `measure2`'),
    (R + 'cex_check_measure3.tsv', '`replay/check_all_cex.py` on `measure3`'),
    # Codegen end to end and the gates.
    (R + 'e2e/e2e_serial.log', '`replay/gate_e2e.sh`: the codegen body and must-refuse tests, serial, time-stamped trace'),
    (R + 'gates/', '`replay/gates.sh` before the merge: each gate\'s complete output and the summary'),
    (R + 'gates-merged/', '`replay/gates.sh` on the merged tree'),
    ('runs/main-d0ecc85.dylib', 'the landing baseline bridge, main `d0ecc859f` (build 12713 lane)'),
    ('runs/census-main-d0ecc85/failed_roots.jsonl', 'the landing baseline census'),
    ('runs/census-main-d0ecc85/stderr.log', 'its body trace'),
    ('runs/census-main-d0ecc85.out', 'its summary'),
    ('runs/ay13556.dylib', 'this branch\'s bridge, `f0113c522` (build 13556 lane)'),
    ('runs/census-ay13556/failed_roots.jsonl', 'this branch\'s census'),
    ('runs/census-ay13556/stderr.log', 'its body trace'),
    ('runs/census-ay13556.out', 'its summary'),
    ('runs/dump-ay13556/', 'its uncertified bodies\' queries'),
    ('ay13556/compare/', '`census_compare.py` of the two rows'),
    ('ay13556/logs/census_chain_kept.log', 'the census chain log'),
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
        names = sorted(os.path.relpath(os.path.join(root, n), path)
                       for root, _, files in os.walk(path) for n in files)
        manifest = ''.join(f'{digest(os.path.join(path, n))}  {n}\n' for n in names)
        size = sum(os.path.getsize(os.path.join(path, n)) for n in names)
        sha = hashlib.sha256(manifest.encode()).hexdigest()
        print(f'| `{rel}` ({what}) ({len(names)} files) | {size} | `{sha}` (manifest) |')
    else:
        print(f'| `{rel}` ({what}) | {os.path.getsize(path)} | `{digest(path)}` |')
