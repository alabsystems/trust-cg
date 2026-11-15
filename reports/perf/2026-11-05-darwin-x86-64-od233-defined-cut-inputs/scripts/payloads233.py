#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes over its top-level files and the SHA-256
of its manifest: one line `<sha256>  <name>` per file, sorted by name,
newline-terminated."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    # The design this change implements.
    ('od233-design/README.md', 'the OD-233 design (§0-§9)'),
    # Slice 25's fails-before record the OD quotes.
    ('s25-run/logs/fails-before5.log', 'slice 25\'s fails-before record on 6c036f1de (its S25_FAILS_BEFORE decomposed lines 1790-1809)'),
    # The fails-before records and the copies they ran.
    ('od233-run/logs/a06-fb-base.log', 'fails-before at b30110fcd, first run (OD233_FAILS_BEFORE)'),
    ('od233-run/logs/a07-fb-pre.log', 'fails-before at 12ebba653, first run (OD233_FAILS_BEFORE)'),
    ('od233-run/fails-before/first', 'the fixture copies the first fails-before runs ran (before formatting)'),
    ('od233-run/logs/a11a-fb-base.log', 'fails-before at b30110fcd on the committed fixtures (lane a8d1d38c6)'),
    ('od233-run/logs/a11b-fb-pre.log', 'fails-before at 12ebba653 on the committed fixtures (lane a8d1d38c6)'),
    ('od233-run/fails-before', 'the fixture copies the review round\'s reruns ran (lane 5896ae541; they replaced the a8d1d38c6 copies)'),
    # The runs while the fixtures were settled.
    ('od233-run/logs/a01-print.log', 'the module with its printers while the fixtures were settled (9 of 10 failed)'),
    ('od233-run/logs/a03-print.log', 'the module and slice 16\'s every-point test while the fixtures were settled (both exit 101)'),
    ('od233-run/logs/a04-print.log', 'the module with its printers while the fixtures were settled (5 of 11 failed)'),
    # The overflow diagnosis.
    ('od233-run/logs/a02-suite.log', 'the first solver-free suite run (the stack overflow in slice 16\'s every-point test)'),
    ('od233-run/logs/a05-print.log', 'the module with its printers, and the per-phase overflow diagnosis with and without the rule'),
    ('od233-run/logs/a08-lldb.log', 'the overflow diagnosis with a 512 MiB stack, and under lldb'),
    ('od233-run/logs/a08-bt.txt', 'lldb\'s stop at the overflow (SmtExpr::try_eval)'),
    ('od233-run/logs/a09-depth.log', 'the statement depths with and without the rule (DEPTH233), and slice 16\'s every-point test on the verifier stack'),
    ('od233-run/logs/a10-module.log', 'slice 25\'s in-parts test, and the module with its printers and the parts texts (TCG_OD233_PRINT_TEXT=1), before the commit'),
    # The head's runs.
    ('od233-run/logs/a11-gates.log', 'gates 1-5 on a8d1d38c6, then the printers'),
    ('od233-run/qual-dump', 'the replayed queries of the qualification lanes'),
    ('od233-run/logs/a12-gate6.log', 'gate 6 (fmt, docs, the matrix check) on the records tree'),
    ('od233-run/logs/server-a12.log', 'the job server\'s start and exit lines for every job, through a12'),
    # The review round (2026-11-06).
    ('od233-run/logs/b01-iter1.log', 'review round: the sweep before the commit (V9 without its reload)'),
    ('od233-run/logs/b02-quick.log', 'review round: the module before the commit (V9 and Q1 failing)'),
    ('od233-run/logs/b03-diag.log', 'review round: V9\'s statement printed, and the positive test (Q1 failing)'),
    ('od233-run/logs/b04-quick.log', 'review round: the module passing before formatting and the commit'),
    ('od233-run/logs/b05-fb-base.log', 'review round: fails-before at b30110fcd on lane 5896ae541, with the base sweep digests (OD233_BASE_DIGEST)'),
    ('od233-run/logs/b06-fb-pre.log', 'review round: fails-before at 12ebba653 on lane 5896ae541'),
    ('od233-run/logs/b07-gates.log', 'review round: gates 1-5 on 5896ae541 (the sweep and digest lines digest-compare.txt reads)'),
    ('od233-run/logs/b08-recut-time.log', 'review round: the re-cut timing lane on 5896ae541, which panicked looking for s20 ManySlots in the wrong fixture list (fixed in 3ef06d6dd)'),
    ('od233-run/logs/b08b-printers.log', 'review round: the od233 printers on 5896ae541'),
    ('od233-run/logs/b10-recut-time.log', 'review round: the re-cut timing lane on AY on 3ef06d6dd (s20 ManySlots at every point)'),
    ('od233-run/logs/b11-gates.log', 'review round: gates 1-5 on 3ef06d6dd, the code head'),
    ('od233-run/logs/b12-gate6.log', 'review round: gate 6\'s first run on the records tree at 3ef06d6dd (the matrix check failed: the timing lane unlisted)'),
    ('od233-run/logs/b13-gate6.log', 'review round: gate 6 on the records tree at 454963b4c'),
    ('od233-run/logs/digest-compare.txt', 'review round: scripts/digest_compare.py on b05 and b07 (5896ae541)'),
    ('od233-run/logs/digest-compare-b11.txt', 'review round: scripts/digest_compare.py on b05 and b11 (3ef06d6dd)'),
    ('od233-run/census-parse', 'review round: the fixed parts_census.py on census-o2-s25 and on the reviewer\'s three-line attempt'),
    ('od233-run/logs/server-b13.log', 'review round: the job server\'s start and exit lines for every b job, through b13'),
    # The census (c76048fa3): scripts/census.sh, its helpers, and what it wrote.
    ('build_bridge.t011.sh', 'the bridge build helper census.sh runs (release, the t011 overlay)'),
    ('census_t011_dylib.sh', 'the census driver census.sh runs on one bridge dylib'),
    ('check_dylib_tools.sh', 'the dylib preflight census_t011_dylib.sh runs'),
    ('od233-run/logs/census.log', 'the bridge build at c76048fa3, the four censuses and their comparisons (census.sh)'),
    ('runs/o2-od233.dylib', 'the OD-233 bridge dylib the O2 census ran'),
    ('runs/o0-od233.dylib', 'the OD-233 bridge dylib the O0 census ran (the same build)'),
    ('runs/census-o2-od233.out', 'the OD-233 O2 census driver output'),
    ('runs/census-o2-od233', 'the OD-233 O2 census outputs (failed roots, refusals, stderr trace with solve-trace lines)'),
    ('runs/census-o2-od233/obj', 'the OD-233 O2 census\'s emitted objects'),
    ('runs/dump-o2-od233', 'the OD-233 O2 census\'s dumped queries (bodies that did not replay Valid)'),
    ('runs/census-o0-od233.out', 'the OD-233 O0 census driver output'),
    ('runs/census-o0-od233', 'the OD-233 O0 census outputs'),
    ('runs/census-o0-od233/obj', 'the OD-233 O0 census\'s emitted objects'),
    ('runs/dump-o0-od233', 'the OD-233 O0 census\'s dumped queries'),
    ('runs/o2-s25-st.dylib', 'the baseline dylib (a copy of o2-s25.dylib, d92b944fe) the O2 timing re-run ran'),
    ('runs/o0-s25-st.dylib', 'the baseline dylib (the same copy) the O0 timing re-run ran'),
    ('runs/census-o2-s25-st.out', 'the baseline O2 timing re-run\'s driver output'),
    ('runs/census-o2-s25-st', 'the baseline O2 timing re-run\'s outputs (solve-trace lines)'),
    ('runs/census-o0-s25-st.out', 'the baseline O0 timing re-run\'s driver output'),
    ('runs/census-o0-s25-st', 'the baseline O0 timing re-run\'s outputs (solve-trace lines)'),
    ('runs/census-o2-s25', 'the O2 baseline (slice 25\'s census, d92b944fe)'),
    ('runs/census-o0-s25', 'the O0 baseline (slice 25\'s census, d92b944fe)'),
    ('od233-run/census/o2', 'O2: root classes, parts (parts_census.py), objects, both sides'),
    ('od233-run/census/o2/compare', 'O2: census_compare.py against census-o2-s25'),
    ('od233-run/census/o2/followup', 'O2: census233.py (the stop rule\'s items, wtf8\'s trace, the cut_pairing texts)'),
    ('od233-run/census/o2/times', 'O2: part_times.py against the baseline re-run'),
    ('od233-run/census/o2/rerun-compare', 'O2: census_compare.py of the baseline re-run against census-o2-s25'),
    ('od233-run/census/o0', 'O0: root classes, parts, objects, trace_diff.txt'),
    ('od233-run/census/o0/compare', 'O0: census_compare.py against census-o0-s25'),
    ('od233-run/census/o0/followup', 'O0: census233.py'),
    ('od233-run/census/o0/trace_diff', 'O0: slice 25\'s trace_diff.py records'),
    ('od233-run/census/o0/times', 'O0: part_times.py against the baseline re-run'),
    ('od233-run/census/o0/rerun-compare', 'O0: census_compare.py of the baseline re-run against census-o0-s25'),
    ('od233-run/census/wtf8', 'O2: the certified-part store entries of core::wtf8::slice_error_fail\'s parts (copied from the shared store)'),
    # The O0 stop: census233.py reported 6 functions with more timeouts than census-o0-s25.
    ('od233-run/census/o0/stop-diagnosis', 'O0 stop: the six functions\' timed-out parts on the OD-233 census, the baseline re-run, census-o0-s24c and census-o0-s25 (six_parts.py)'),
    ('od233-run/census/o0/stop-diagnosis/base-vs-rerun', 'O0 stop: census233.py of census-o0-s25 against the baseline dylib\'s re-run'),
    ('od233-run/census/o0/stop-diagnosis/rerun-vs-od233', 'O0 stop: census233.py of the baseline dylib\'s re-run against the OD-233 census'),
    ('runs/census-o0-s24c', 'slice 24c\'s O0 census (2026-11-07), read for the six functions\' timeouts'),
    ('runs/census-o0-s24c.out', 'slice 24c\'s O0 census driver output (its dylib o0-s24c.dylib, another build)'),
    # The census record (2026-11-07): what it cites beyond census.sh's own outputs.
    ('runs/census-o2-s25.out', 'the O2 baseline\'s driver output (wall 909 s)'),
    ('runs/census-o0-s25.out', 'the O0 baseline\'s driver output (wall 2465 s)'),
    ('runs/census-o2-s25/obj', 'the O2 baseline\'s emitted objects (the object comparison\'s base side)'),
    ('runs/census-o0-s25/obj', 'the O0 baseline\'s emitted objects (the object comparison\'s base side)'),
    ('runs/dump-o2-s25', 'the O2 baseline\'s dumped queries (core::wtf8::slice_error_fail\'s three parts among them)'),
    ('runs/dump-o2-s25-st', 'the O2 baseline re-run\'s dumped queries'),
    ('runs/dump-o0-s25-st', 'the O0 baseline re-run\'s dumped queries: none, the directory is empty'),
    ('runs/census-o2-s25/obj/trust-witness', 'the O2 baseline\'s trust-witness directory'),
    ('runs/census-o2-s25-st/obj/trust-witness', 'the O2 baseline re-run\'s trust-witness directory'),
    ('runs/census-o2-od233/obj/trust-witness', 'the OD-233 O2 census\'s trust-witness directory'),
    ('runs/census-o0-s25/obj/trust-witness', 'the O0 baseline\'s trust-witness directory'),
    ('runs/census-o0-s25-st/obj/trust-witness', 'the O0 baseline re-run\'s trust-witness directory'),
    ('runs/census-o0-od233/obj/trust-witness', 'the OD-233 O0 census\'s trust-witness directory'),
    # The census record's review (2026-11-07): its fact checks and what they cite.
    ('od233-run/fact-checks', 'scripts/fact_checks233.py\'s output (fact_checks.txt, sections A-I) and the host\'s CPU counts (host.txt, sysctl)'),
    ('runs/o2-s25.dylib', 'the O2 baseline\'s bridge dylib (d92b944fe; also bound in slice 25\'s PAYLOADS.md)'),
    ('runs/o0-s25.dylib', 'the O0 baseline\'s bridge dylib (the same build; also bound in slice 25\'s PAYLOADS.md)'),
    ('od233-run/logs/b14-gate6-head.log', 'gate 6 on c76048fa3 with a clean tree'),
    ('od233-run/logs/server-b.log', 'the job server\'s start and exit lines for every b job, through b14'),
    ('od233-run/logs/c01-gate6.log', 'gate 6 on 78f602091 (the census record with its fact-check corrections) with a clean tree, run by hand'),
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
