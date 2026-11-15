#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes over its top-level files and the SHA-256
of its manifest: one line `<sha256>  <name>` per file, sorted by name,
newline-terminated (as the OD-233 record's payloads233.py defines it)."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
CENSUSES = [
    ('base', 'O2'), ('o0', 'O0'), ('o3', 'O3'), ('l', 'O2, no-x86-licm'),
    ('lr', 'O2, no-x86-licm no-x86-loop-rotate'), ('r', 'O2, no-x86-loop-rotate'),
    ('all', 'O2, LICM, rotation, if-conversion and cmov swap off'),
    ('tir', 'O2 with dump-trust-ir'),
]
FILES = [
    ('s24c-od233/payload/s26-design-2026-11-08.md', 'the slice-26 design as of this record (§1.4 bounds, §4.5 G-SEFRT, §5.1 replicas)'),
    ('build_bridge.t011.sh', 'the bridge build helper census-combined.sh runs'),
    ('census_t011_dylib.sh', 'the census driver census-combined.sh runs on the bridge dylib'),
    ('check_dylib_tools.sh', 'the dylib preflight census_t011_dylib.sh runs'),
    ('s24c-od233/census-combined.sh', 'the driver (also in tree as scripts/census-combined.sh)'),
    ('s24c-od233/logs/gates-71c5eb19e.log', 'gates 1-5 on 5a49bb594 (gate 1: 511 passed, the fold test and every golden re-render test among them)'),
    ('s24c-od233/logs/census-combined-5a49bb594-E0004.log', 'the first run on 5a49bb594: the bridge build failed with E0004 (DRIVER-EXIT 8)'),
    ('s24c-od233/logs/census-combined.log', 'the run on 49748f126: the build, eight censuses, the comparisons, the G-SEFRT trace lines'),
    ('runs/s26base.bridge-commit.txt', 'the commit the bridge was built from'),
    ('runs/s26base-base.dylib', 'the bridge dylib (the seven other s26base-*.dylib are hard links of it)'),
]
for tag, what in CENSUSES:
    FILES += [
        (f'runs/census-s26base-{tag}.out', f'the {what} census driver output'),
        (f'runs/census-s26base-{tag}', f'the {what} census outputs (failed roots, refusals, stderr trace)'),
        (f'runs/census-s26base-{tag}/obj', f'the {what} census\'s emitted objects'),
        (f'runs/dump-s26base-{tag}', f'the {what} census\'s dumped queries'),
    ]
FILES += [
    ('runs/tir-s26base', 'the TrustIR containers of the dump run (1,288 .trust_irbin with their .json)'),
    ('runs/compare-s26base-base-vs-l', 'census_compare.py: base against l'),
    ('runs/compare-s26base-base-vs-r', 'census_compare.py: base against r'),
    ('runs/compare-s26base-base-vs-lr', 'census_compare.py: base against lr'),
    ('runs/compare-s26base-base-vs-all', 'census_compare.py: base against all'),
    ('runs/cmp-combined', 'census_compare.py text outputs against the named censuses'),
]
for d in ['o2-s24c-vs-base', 'o2-od233-vs-base', 'o0-s24c-vs-o0', 'o3-s24c-vs-o3', 'o2k-od233-l-vs-l',
          'm301-l-vs-l', 'm301-r-vs-r', 'm301-lr-vs-lr', 'm301-all-vs-all', 's25-vs-s24c']:
    FILES.append((f'runs/cmp-combined/{d}', f'census_compare.py output directory {d}'))
FILES += [
    ('s24c-od233/payload/root_classes.py', 'slice 24c\'s root_classes.py (copied), which classed the 214'),
    ('g-sefrt/escape', 'OD-235\'s before: EscapeAscii::fmt\'s seven parts, AY replays and the part-2 variants (nodiv, shift, t600)'),
    ('g-sefrt/escape/replay.log', 'the parts\' AY replay times (part 2 unknown at 30 s)'),
]
for name, what in [('o2-s24c', 'slice 24c O2'), ('o0-s24c', 'slice 24c O0'), ('o3-s24c', 'slice 24c O3'),
                   ('o2-od233', 'OD-233 O2'), ('o0-od233', 'OD-233 O0'), ('o2k-od233-l', 'OD-233 no-x86-licm (OD-235\'s before)'),
                   ('o2k-m301-l', 'main b30110fcd no-x86-licm'), ('o2k-m301-r', 'main b30110fcd no-x86-loop-rotate'),
                   ('o2k-m301-lr', 'main b30110fcd no-x86-licm no-x86-loop-rotate'), ('o2k-m301-all', 'main b30110fcd, four knobs off')]:
    FILES.append((f'runs/census-{name}', f'the named census: {what}'))
    FILES.append((f'runs/census-{name}.out', f'the named census\'s driver output: {what}'))


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
