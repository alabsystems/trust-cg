#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows of the 2026-11-07 LICM/rotation split record (path relative
to ~/tcg-scratch, bytes, sha256). A directory's row is its total bytes over its top-level files and
the SHA-256 of its manifest: one line `<sha256>  <name>` per file, sorted by name,
newline-terminated (as the 2026-11-06 knob-ceiling record's payloads_knobs.py)."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    ('s26-design/README-s25.md', 'the slice 26 design, revised onto slice 25'),
    ('s26-rebase/run_censuses.log', 'the run log (lane/run_censuses.sh)'),
    ('s26-rebase/per_root.tsv', 'the 111 roots, one row each'),
    ('s26-rebase/work/', 'the per-root attribution scripts and outputs'),
]
for tag in ['o2k-m301-l', 'o2k-m301-r']:
    FILES += [
        (f'runs/{tag}.dylib', f'census {tag}: the bridge copy'),
        (f'runs/census-{tag}.out', f'census {tag}: summary'),
        (f'runs/census-{tag}/failed_roots.jsonl', f'census {tag}: failed roots'),
        (f'runs/census-{tag}/refusals.jsonl', f'census {tag}: typed refusals'),
        (f'runs/census-{tag}/stderr.log', f'census {tag}: body trace'),
        (f'runs/census-{tag}/obj/', f'census {tag}: emitted objects'),
        (f'runs/dump-{tag}/', f'census {tag}: dumped queries'),
        (f's26-rebase/{tag}/root_classes.txt', f'census {tag}: first-refusal classes'),
        (f's26-rebase/{tag}/vs-o2-m301/', f'census_compare.py: {tag} against plain'),
        (f's26-rebase/{tag}/lr-vs-{tag}/', f'census_compare.py: lr against {tag}'),
        (f's26-rebase/{tag}/followup/', f'census_s25.py: {tag} against plain'),
    ]
FILES += [
    ('sefrt-diag/FILES.txt', 'the diagnosis tree, file by file'),
    ('sefrt-diag/ay/SUMMARY.txt', 'the census parts replayed on AY 13556'),
    ('sefrt-diag/ay/o2k-m301-lr/', 'replays of lr parts, with models'),
    ('sefrt-diag/ay/o2k-m301-all/', 'replays of all parts, with models'),
    ('sefrt-diag/ay/o2k-m301-allbm/', 'replays of allbm parts, with models'),
    ('sefrt-diag/ay/corerun-attempt1/', 'replays of the first attempt parts, with models'),
    ('sefrt-diag/corerun/run.log', 'the census-identical core re-run (lane/corerun.sh)'),
    ('sefrt-diag/corerun/attempt1/', 'the re-run: first attempt parts'),
    ('sefrt-diag/corerun/attempt2/', 'the re-run: second attempt parts'),
    ('sefrt-diag/corerun/rows-attempt1.txt', 'the function machine rows, first attempt'),
    ('sefrt-diag/corerun/rows-attempt2.txt', 'the function machine rows, second attempt'),
    ('sefrt-diag/coremir/sefrt.core.mir', 'the function runtime MIR under the census flags'),
    ('sefrt-diag/synth/', 'the defined queries, controls, AY outputs, certificates and Clean checks'),
    ('sefrt-diag/synth-recheck/', 'the fact check: the seven queries regenerated and re-run on AY'),
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
