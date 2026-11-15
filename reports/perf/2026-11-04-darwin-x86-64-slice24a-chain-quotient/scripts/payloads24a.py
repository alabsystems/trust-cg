#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes over its top-level files and the SHA-256
of its manifest: one line `<sha256>  <name>` per file, sorted by name,
newline-terminated."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    # The design this slice implements.
    ('s24a-design/README.md', 'the slice-24a design (§1-§9)'),
    # Fails-before on 7ee0def54.
    ('s24a-run/fails-before/copy1_x86_source_bound_body_slice24_tests.rs',
     'the first fails-before copy `fails-before/make_fails_before.py` wrote into the 7ee0def54 worktree (never committed)'),
    ('s24a-run/logs/fails-before.log', 'its run: every fixture, control, wrong lowering and variant on 7ee0def54'),
    ('s24a-run/fails-before/copy4_x86_source_bound_body_slice24_tests.rs',
     'the review round\'s fails-before copy (the review\'s fixtures, variants and the O0 outcomes)'),
    ('s24a-run/logs/fails-before4.log',
     'its run on 7ee0def54: the first run\'s rows plus the review\'s pairs and the S24_O0 lines `slice24_o0_owners.txt` records'),
    # The final code.
    ('s24a-run/logs/jobC.log', 'the golden rewrite, the solver-free module, the fails-before run and the three slice-24a qualification lanes'),
    ('s24a-run/logs/print3.log', 'the printer on the final fixtures (LIR, merged machine, chains, theorem, every control)'),
    ('s24a-run/logs/jobD.log', 'gates 1, 3 and 4'),
    ('s24a-run/logs/gate5-fmt.log', 'gate 5, format'),
    ('s24a-run/logs/gate5-docs.log', 'gate 5, documentation'),
    # The review round.
    ('s24a-run/logs/fix1.log', 'the printer on the review\'s fixtures (the extra pairs\' outcomes)'),
    ('s24a-run/logs/jobR1.log', 'review round, first run: F12 multiplying the join value (its replay times out at 30 s; superseded)'),
    ('s24a-run/logs/jobR1b.log', 'review round, second run: F12 multiplying on its left arm (its replay times out at 30 s; superseded)'),
    ('s24a-run/logs/jobR1c.log', 'review round on the final fixtures: the golden rewrite, the solver-free module with --nocapture, the three slice-24a qualification lanes'),
    ('s24a-run/logs/chainR.log', 'review round: the fails-before rerun and the gates job at 4c54514eb, in order'),
    ('s24a-run/logs/jobR2.log', 'review head 4c54514eb: gate 1, gate 2\'s replay lane, gate 4'),
    ('s24a-run/logs/jobR4.log', 'the census fix (b342de091 before commit): the solver-free module with --nocapture and the three qualification lanes'),
    ('s24a-run/logs/chainF.log', 'final head: the fails-before rerun, the gates and the O2 census rerun, in order'),
    ('s24a-run/logs/jobR2f.log', 'final head: gate 1, gate 2\'s replay lane, gate 4'),
    ('s24a-run/logs/jobR3f.log', 'final head: gate 2\'s refutation and credit lanes'),
    ('s24a-run/logs/gate5-fmt-r.log', 'review head: gate 5, format'),
    ('s24a-run/logs/gate5-docs-r.log', 'review head: gate 5, documentation'),
    ('s24a-run/logs/gate5-matrix-r.log', 'review head: gate 5, the full-test-matrix hosts check (silent on success)'),
    # The census of the review head.
    ('build_bridge.t011.sh', 'the bridge build helper census.sh runs (release, the t011 overlay)'),
    ('census_t011_dylib.sh', 'the census driver census.sh runs on one bridge dylib'),
    ('s24a-run/logs/census.log', 'the bridge build at the review head and both censuses with their comparisons'),
    ('runs/o2-s24a.dylib', 'the bridge dylib both censuses ran'),
    ('runs/census-o2-s24a.out', 'the O2 census driver output'),
    ('runs/census-o2-s24a', 'the O2 census outputs (failed roots, refusals, stderr trace)'),
    ('runs/dump-o2-s24a', 'the O2 census\'s dumped queries'),
    ('s24a-run/census/o2', 'census_compare.py against census-o2-7ee0'),
    ('runs/census-o0-s24a.out', 'the O0 census driver output'),
    ('runs/census-o0-s24a', 'the O0 census outputs (failed roots, refusals, stderr trace)'),
    ('runs/dump-o0-s24a', 'the O0 census\'s dumped queries'),
    ('s24a-run/census/o0', 'census_compare.py against census-o0-7ee0'),
    ('s24a-run/census/merged.txt', 'the merged-chains attribution of both censuses at 4c54514eb (census_merged.py)'),
    ('s24a-run/census/merged-f.txt', 'the merged-chains attribution of the O2 census at b342de091 (census_merged.py)'),
    ('s24a-run/logs/census-f.log', 'the bridge rebuilt at the final head and its O2 census, comparison and attribution'),
    ('runs/o2-s24a-f.dylib', 'the final head\'s bridge dylib'),
    ('runs/census-o2-s24a-f.out', 'the final head\'s O2 census driver output'),
    ('runs/census-o2-s24a-f', 'the final head\'s O2 census outputs'),
    ('runs/dump-o2-s24a-f', 'the final head\'s O2 dumped queries'),
    ('s24a-run/census/o2-f', 'census_compare.py of the final head\'s O2 census against census-o2-7ee0'),
    ('s24a-run/logs/gate5-fmt-f.log', 'docs head: gate 5, format'),
    ('s24a-run/logs/gate5-docs-f.log', 'docs head: gate 5, documentation'),
    ('s24a-run/logs/gate5-matrix-f.log', 'docs head: gate 5, the full-test-matrix hosts check (silent on success)'),
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
