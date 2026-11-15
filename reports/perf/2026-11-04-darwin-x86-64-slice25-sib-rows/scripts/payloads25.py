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
    ('s25-design/README.md', 'the slice-25 design (§0-§9)'),
    # Slice 25.0 (6c036f1de): its gates and the diagnostic census.
    ('s25-run/s25.0-solverfree.log', 'slice 25.0: the solver-free x86 body suite'),
    ('s25-run/s25.0-fmt.log', 'slice 25.0: format'),
    ('s25-run/logs/census-diag.log', 'slice 25.0: the bridge build at 6c036f1de, the O2 census and its comparison (census_diag.sh)'),
    ('runs/o2-s25d.dylib', 'slice 25.0: the bridge dylib the diagnostic census ran'),
    ('runs/census-o2-s25d.out', 'slice 25.0: the O2 census driver output'),
    ('runs/census-o2-s25d', 'slice 25.0: the O2 census outputs (failed roots, refusals, stderr trace)'),
    ('runs/dump-o2-s25d', 'slice 25.0: the O2 census\'s dumped queries'),
    ('s25-run/census/diag/compare', 'slice 25.0: census_compare.py against census-o2-s24a-f'),
    ('s25-run/logs/diag-analysis.log', 'slice 25.0: the analysis run (diag_analysis.sh)'),
    ('s25-run/census/diag/trace_diff.txt', 'slice 25.0: the function-by-function no-verdict-change check'),
    ('s25-run/census/diag/trace_diff', 'slice 25.0: trace_diff.py\'s records'),
    ('s25-run/census/diag/histogram.md', 'slice 25.0: the histogram of the scan\'s named rows'),
    ('s25-run/census/diag/s_rows.tsv', 'slice 25.0: the named row of each S function'),
    ('s25-run/census/diag/s_roots.jsonl', 'slice 25.0: the S roots'),
    ('s25-run/census/diag/o0_sib_sites.json', 'slice 25.0: the O0 cross-reference'),
    ('s25-run/census/diag/merged.txt', 'slice 25.0: the merged-chains attribution (census_merged.py)'),
    # Slice 25.1 (6c8ea20c9).
    ('s25-run/logs/s251-solverfree.log', 'slice 25.1: the solver-free x86 body suite and the LeaSib control printer'),
    # Fails-before on 6c036f1de.
    ('s25-run/fails-before/copy1_x86_source_bound_body_slice25_tests.rs', 'fails-before, first copy (an earlier fixture section; superseded)'),
    ('s25-run/logs/fails-before1.log', 'its run on 6c036f1de (superseded)'),
    ('s25-run/fails-before/copy2_x86_source_bound_body_slice25_tests.rs', 'fails-before, second copy (an earlier fixture section; superseded)'),
    ('s25-run/logs/fails-before2.log', 'its run on 6c036f1de (superseded)'),
    ('s25-run/fails-before/copy3_x86_source_bound_body_slice25_tests.rs', 'fails-before, third copy (the final fixtures before their comments were corrected and formatted)'),
    ('s25-run/logs/fails-before3.log', 'its run on 6c036f1de: every fixture\'s rows and refusal'),
    ('s25-run/fails-before/copy4_x86_source_bound_body_slice25_tests.rs', 'fails-before, fourth copy (the committed fixture section)'),
    ('s25-run/logs/fails-before4.log', 'its run on 6c036f1de: every fixture\'s rows and refusal (the record)'),
    # Slice 25.2: the module, qualification and gates.
    ('s25-run/logs/s252d.log', 'the golden write (TCG_X86_BODY_SNAPSHOT_WRITE=1) and the module before the last control fixes'),
    ('s25-run/logs/s252e.log', 'the solver-free module on the final code (20 passed)'),
    ('s25-run/logs/jobQ.log', 'gate 2: the three slice-25 qualification lanes'),
    ('s25-run/qual-dump', 'gate 2: every replayed and refuted query'),
    ('s25-run/logs/jobG.log', 'gates 1, 3, 4 and 5'),
    ('s25-run/logs/jobF.log', 'the module with --nocapture (S25_MUTANT lines) and the printers on the final code'),
    ('s25-run/logs/gate6-fmt.log', 'gate 6, format'),
    ('s25-run/logs/gate6-docs.log', 'gate 6, documentation'),
    ('s25-run/logs/gate6-matrix.log', 'gate 6, the full-test-matrix hosts check (silent on success)'),
    # The review round (d92b944fe): its iterations on the pre-commit tree
    # (superseded by the merged head's gates.log), and its final job, stopped
    # in the bridge build.
    ('s25-run/fix/logs/m1.log', 'review round: the module and the golden write, first iteration'),
    ('s25-run/fix/logs/m2.log', 'review round: the module, the replay lane and the e2e target, second iteration'),
    ('s25-run/fix/logs/m3.log', 'review round: the module and the qualification lanes, third iteration'),
    ('s25-run/fix/logs/m4.log', 'review round: the module and gate 4 on the pre-commit tree'),
    ('s25-run/fix/logs/fin.log', 'review round: fin.sh, stopped in its bridge build (no result)'),
    # The extended fails-before record (base.sh, COPY=copy5) on 6c036f1de.
    ('s25-run/fails-before/copy5_x86_source_bound_body_slice25_tests.rs', 'fails-before, fifth copy (the review round\'s fixture section and the extended recorder)'),
    ('s25-run/logs/fails-before5-unused-import.log', 'its first attempt: the copy did not compile (an import only the controls use; the generator now allows unused imports)'),
    ('s25-run/logs/fails-before5.log', 'its run on 6c036f1de in the base tree\'s own target dir (the record)'),
    # The gates on the merged head a617488aa (gates.sh).
    ('s25-run/merged/gates.log', 'gates 1 to 4 on the merged head a617488aa'),
    ('s25-run/merged/qual-dump', 'the merged head\'s replayed and refuted queries'),
    # The refuted body's standalone reproducer.
    ('s25-run/diag-wtf8', 'the refuted body: the reproducer, its traces, rows and disassembly (FILES.txt indexes it)'),
    ('s25-run/diag-wtf8/ay', 'the refuted body: the census\'s three parts with (get-model) and AY 13556\'s answers'),
    ('s25-run/diag-wtf8/dump', 'the refuted body: the reproducer\'s dumped parts'),
    ('s25-run/diag-wtf8/tir', 'the refuted body: the reproducer\'s TrustIR container'),
    # The slice-25 census (d92b944fe): census.sh, then census_s25.py.
    ('build_bridge.t011.sh', 'the bridge build helper census.sh runs (release, the t011 overlay)'),
    ('census_t011_dylib.sh', 'the census driver census.sh runs on one bridge dylib'),
    ('check_dylib_tools.sh', 'the dylib preflight census_t011_dylib.sh runs'),
    ('s25-run/logs/census.log', 'the bridge build at d92b944fe and both censuses with their comparisons (census.sh)'),
    ('runs/o2-s25.dylib', 'the bridge dylib the O2 census ran'),
    ('runs/o0-s25.dylib', 'the bridge dylib the O0 census ran (the same build)'),
    ('runs/census-o2-s25.out', 'the O2 census driver output'),
    ('runs/census-o2-s25', 'the O2 census outputs (failed roots, refusals, stderr trace)'),
    ('runs/dump-o2-s25', 'the O2 census\'s dumped queries'),
    ('s25-run/census/o2', 'census_compare.py against census-o2-s24a-f, census_merged.py, root_classes.py and firsthit.py of both sides'),
    ('s25-run/logs/census-followup.log', 'the O2 follow-ups run (census_s25.py)'),
    ('s25-run/census/o2/followup', 'census_s25.py\'s records'),
    ('runs/census-o0-s25.out', 'the O0 census driver output'),
    ('runs/census-o0-s25', 'the O0 census outputs (failed roots, refusals, stderr trace)'),
    ('runs/dump-o0-s25', 'the O0 census\'s dumped queries: none, the directory is empty'),
    ('s25-run/census/o0', 'census_compare.py and census_merged.py against census-o0-s24a, and the trace check'),
    ('s25-run/census/o0/trace_diff', 'trace_diff.py\'s records of the O0 census'),
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
