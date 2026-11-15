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
    ('s24c-design/README.md', 'the slice-24c design (§0-§9 and the addendum)'),
    # The lane's runs, in order (one build-slot hold, scripts/server.sh).
    ('s24c-run/logs/job4.log', 'the first P6: a pure-test header rotated, nothing if-converted'),
    ('s24c-run/logs/job5.log', 'P6 from h(0, 0) refused at the loop entry edge; the cut-pairing and N7 probes'),
    ('s24c-run/fails-before/copy1_x86_source_bound_body_slice24c_tests.rs', 'fails-before, first copy (its recording test did not compile; superseded)'),
    ('s24c-run/logs/job6.log', 'its compile on a617488aa (the borrow error)'),
    ('s24c-run/logs/job7.log', 'the module before the golden digest and the O0 record, and the golden write'),
    ('s24c-run/fails-before/copy2_x86_source_bound_body_slice24c_tests.rs', 'fails-before, second copy (the record)'),
    ('s24c-run/logs/job8.log', 'its run on a617488aa: every outcome and the S24C_O0 lines'),
    ('s24c-run/logs/job9.log', 'the module with two surviving mutants (flags, check-off), and the slice-24a module'),
    ('s24c-run/logs/job10.log', 'the printer and the module on the final code (13 passed; the S24C_MUTANT lines)'),
    ('s24c-run/logs/job11.log', 'gates 1 to 5 at cdfda5a59 (gate 2: the LongDiamond Timeout, not yet recorded)'),
    ('s24c-run/logs/job12.log', 'the offline 300 s replay of the LongDiamond query'),
    ('s24c-run/offline', 'its query copy and outputs'),
    ('s24c-run/logs/job13.log', 'gate 2 on the lane head, the gap recorded'),
    ('s24c-run/qual-dump', 'gate 2 and 3: every replayed and refuted query'),
    ('s24c-run/queue', 'the job files the queue ran'),
    ('s24c-run/logs/server1.log', 'the queue run\'s own log'),
    ('s24c-run/logs/gate6-fmt.log', 'gate 6, format'),
    ('s24c-run/logs/gate6-docs.log', 'gate 6, documentation'),
    ('s24c-run/logs/gate6-matrix.log', 'gate 6, the full-test-matrix hosts check (silent on success)'),
    # The ceiling census (README, Census).
    ('runs/o2-s25.dylib', 'slice 25\'s release bridge dylib at d92b944fe, which census-o2-s25 ran (also bound in slice 25\'s PAYLOADS.md)'),
    ('runs/o0-s25.dylib', 'its byte copy, which census-o0-s25 ran'),
    ('runs/o2k-s25-nifc.dylib', 'its byte copy, which the ceiling census ran'),
    ('runs/census-o2k-s25-nifc', 'census-o2k-s25-nifc: slice 25\'s bridge at O2 without if-conversion or cmov swap (top-level files; obj/ not bound)'),
    ('s24c-run/logs/census-o2k-s25-nifc.log', 'its log'),
    ('s24c-run/census/nifc', 'its comparison with census-o2-s25 (compare, promoted, newly failing, transitions, both root-class tables, ceiling.log, SHA256SIZES.txt)'),
    ('s24c-run/census/nifc/ceiling', 'the ceiling attribution: ceiling.txt, candidates.tsv, roots.tsv'),
    ('s24c-run/census/nifc-s24a', 'the S24a-base nifc comparison (378 -> 339), moved here byte for byte'),
    ('s24c-run/logs/census-o2k-s24a-nifc.log', 'the S24a-base nifc census log'),
    # The review round.
    ('s24c-run/logs/server2.log', 'review round: the queue run of job14 and job15'),
    ('s24c-run/logs/job14.log', 'review round: the module on the working tree (P12 in one part, N8 refused by the loop admission)'),
    ('s24c-run/logs/job15.log', 'review round: the three qualification lanes on the working tree (two composition Timeouts and SlotJoin, not yet recorded)'),
    ('s24c-run/qual-dump-r1', 'their replayed and refuted queries'),
    ('s24c-run/offline/r1', 'offline AY replays of SlotJoin (30 s twice, 300 s), Diamonds5 and DiamondChain (300 s)'),
    ('s24c-run/offline/r2', 'SlotJoin at the 30 s budget, twice alone and three at once'),
    ('s24c-run/logs/server3.log', 'review round: the queue run of job16 to job19'),
    ('s24c-run/logs/job16.log', 'review round: the module on the working tree, P12 and N8 rebuilt'),
    ('s24c-run/logs/job17.log', 'review round: the three qualification lanes on the working tree, the gaps recorded'),
    ('s24c-run/qual-dump-r2', 'their replayed and refuted queries'),
    ('s24c-run/fails-before/copy3_x86_source_bound_body_slice24c_tests.rs', 'fails-before, third copy (the review round\'s fixtures)'),
    ('s24c-run/logs/job18.log', 'its run on a617488aa'),
    ('s24c-run/logs/job19.log', 'review round: gates 1 to 4 on the committed head 177d144b1'),
    ('s24c-run/qual-dump-g2', 'its gate 2 and 3 replayed and refuted queries'),
    ('s24c-run/logs/gate6-fmt-r2.log', 'review round: gate 6, format, on 177d144b1'),
    ('s24c-run/logs/gate6-docs-r2.log', 'review round: gate 6, documentation, on 177d144b1'),
    ('s24c-run/logs/gate6-matrix-r2.log', 'review round: gate 6, the full-test-matrix hosts check, on 177d144b1'),
    ('s24c-run/logs/gate6-fmt-r3.log', 'review round: gate 6, format, on the final tree'),
    ('s24c-run/logs/gate6-docs-r3.log', 'review round: gate 6, documentation, on the final tree'),
    ('s24c-run/logs/gate6-matrix-r3.log', 'review round: gate 6, the full-test-matrix hosts check, on the final tree'),
    # The head's census (README, Census: the slice-24c head).
    ('build_bridge.t011.sh', 'the bridge build helper census.sh runs (release, the t011 overlay)'),
    ('census_t011_dylib.sh', 'the census driver census.sh runs on one bridge dylib'),
    ('check_dylib_tools.sh', 'the dylib preflight census_t011_dylib.sh runs'),
    ('s24c-run/logs/census-s24c.log', 'census.sh: the bridge build at 38feaf386, the O2, O0 and O3 censuses and analyse.sh'),
    ('runs/o2-s24c.dylib', 'the slice-24c bridge dylib (o0-s24c.dylib and o3-s24c.dylib are byte-identical copies)'),
    ('runs/census-o2-s24c.out', 'O2: the census driver output'),
    ('runs/census-o2-s24c', 'O2: the census outputs (failed roots, refusals, stderr trace; obj/ not bound)'),
    ('runs/dump-o2-s24c', 'O2: the dumped queries'),
    ('runs/census-o0-s24c.out', 'O0: the census driver output'),
    ('runs/census-o0-s24c', 'O0: the census outputs (obj/ not bound)'),
    ('runs/dump-o0-s24c', 'O0: the dumped queries (none, the directory is empty)'),
    ('runs/census-o3-s24c.out', 'O3: the census driver output'),
    ('runs/census-o3-s24c', 'O3: the census outputs (obj/ not bound)'),
    ('runs/dump-o3-s24c', 'O3: the dumped queries'),
    ('runs/census-o2-s25.out', 'the O2 baseline (slice 25 at d92b944fe): its driver output'),
    ('runs/census-o2-s25', 'the O2 baseline: its census outputs (obj/ not bound)'),
    ('runs/dump-o2-s25', 'the O2 baseline: its dumped queries'),
    ('runs/census-o0-s25.out', 'the O0 baseline: its driver output'),
    ('runs/census-o0-s25', 'the O0 baseline: its census outputs (obj/ not bound)'),
    ('s24c-run/census/o2', 'O2 comparison: compare, merged, promoted, newly failing, transitions, both root-class tables'),
    ('s24c-run/census/o2/segments', 'O2 attribution (census_segments.py): segments.txt, roots.tsv, functions.tsv, segments.json'),
    ('s24c-run/census/o0', 'O0 comparison: compare, merged, transitions, trace_diff.txt, outcomes.txt'),
    ('s24c-run/census/o0/trace_diff', 'O0: trace_diff.py\'s records (anomalies, S records, summary)'),
    ('s24c-run/census/o3', 'O3: the three counts and the refuted lines (o3_counts.txt)'),
    ('s24c-run/census/stop_rule.txt', 'the stop rule over all three censuses (the O3 stop)'),
    # The O3 stop's diagnosis (README, The O3 stop).
    ('s24c-run/diag-o3', 'the diagnosis: FILES.txt, diag.sh, repro.sh, base_o3.sh and their logs'),
    ('runs/o3-s25.dylib', 'the O3 baseline\'s dylib (a byte copy of runs/o2-s25.dylib)'),
    ('runs/census-o3-s25.out', 'the O3 baseline (census-o3-s25): its driver output'),
    ('runs/census-o3-s25', 'the O3 baseline: its census outputs (obj/ not bound)'),
    ('runs/dump-o3-s25', 'the O3 baseline: its dumped queries'),
    ('s24c-run/diag-o3/compare', 'census-o3-s25 -> census-o3-s24c (census_compare.py) and segments.log'),
    ('s24c-run/diag-o3/compare/segments', 'its census_segments.py attribution'),
    ('s24c-run/diag-o3/ay', 'every dumped O3 part of the two functions with (get-model), and AY 13556\'s answers'),
    ('s24c-run/diag-o3/strsearcher', 'the StrSearcher::new reproducer (lib.rs)'),
    ('s24c-run/diag-o3/strsearcher/s24c-o3', 'its O3 trace through the slice-24c dylib'),
    ('s24c-run/diag-o3/strsearcher/s24c-o3/dump', 'its two dumped parts'),
    ('s24c-run/diag-o3/strsearcher/s24c-o3/obj', 'its emitted objects (StrSearcher::new\'s not among them)'),
    ('s24c-run/diag-o3/strsearcher/s24c-o3/obj/trust-witness', 'their witness'),
    ('s24c-run/diag-o3/strsearcher/s24c-o3/tir', 'the TrustIR containers it compiled (binary and JSON)'),
    ('s24c-run/diag-o3/strsearcher/s25-o3', 'its O3 trace through the slice-25 dylib'),
    ('s24c-run/diag-o3/strsearcher/s25-o3/dump', 'its two dumped parts'),
    ('s24c-run/diag-o3/strsearcher/s25-o3/obj', 'its emitted objects (StrSearcher::new\'s not among them)'),
    ('s24c-run/diag-o3/strsearcher/s25-o3/obj/trust-witness', 'their witness'),
    ('s24c-run/diag-o3/strsearcher/s25-o3/tir', 'the TrustIR containers it compiled (binary and JSON)'),
    ('s24c-run/diag-o3/strsearcher/s24c-o2', 'its O2 control through the slice-24c dylib'),
    ('s24c-run/diag-o3/strsearcher/s24c-o2/obj', 'its emitted objects (StrSearcher::new\'s among them; dump/ is empty)'),
    ('s24c-run/diag-o3/strsearcher/s24c-o2/obj/trust-witness', 'their witness'),
    ('s24c-run/diag-o3/strsearcher/s24c-o2/tir', 'the TrustIR containers it compiled (binary and JSON)'),
    ('s24c-run/diag-o3/strsearcher/s25-o2', 'its O2 control through the slice-25 dylib'),
    ('s24c-run/diag-o3/strsearcher/s25-o2/obj', 'its emitted objects (StrSearcher::new\'s among them; dump/ is empty)'),
    ('s24c-run/diag-o3/strsearcher/s25-o2/obj/trust-witness', 'their witness'),
    ('s24c-run/diag-o3/strsearcher/s25-o2/tir', 'the TrustIR containers it compiled (binary and JSON)'),
    ('s24c-run/diag-o3/strsearcher/s24c-o3-peephole', 'its pre-RA rows (peephole.log) and the two objects that compile emitted'),
    ('s24c-run/diag-o3/strsearcher/s24c-o3-peephole/trust-witness', 'their witness'),
    ('s24c-run/diag-o3/strsearcher/s24c-o3-np', 'its lowering-only object (no proof claim) and disassembly'),
    ('s24c-run/diag-o3/strsearcher/s24c-o3-np/trust-witness', 'its witness'),
    ('s24c-run/diag-o3/wtf8', 'the slice_error_fail reproducer (lib.rs, a byte copy of s25-run/diag-wtf8/lib.rs)'),
    ('s25-run/diag-wtf8/lib.rs', 'slice 25\'s reproducer it copies (also bound, in its directory\'s manifest, by slice 25\'s PAYLOADS.md)'),
    ('s24c-run/diag-o3/wtf8/s24c-o3', 'its O3 trace through the slice-24c dylib'),
    ('s24c-run/diag-o3/wtf8/s24c-o3/dump', 'its three dumped parts'),
    ('s24c-run/diag-o3/wtf8/s24c-o3/obj/trust-witness', 'its witness (obj/ holds no object: slice_error_fail\'s is not emitted)'),
    ('s24c-run/diag-o3/wtf8/s24c-o3/tir', 'the TrustIR container it compiled (binary and JSON)'),
    ('s24c-run/diag-o3/wtf8/s25-o3', 'its O3 trace through the slice-25 dylib'),
    ('s24c-run/diag-o3/wtf8/s25-o3/dump', 'its three dumped parts'),
    ('s24c-run/diag-o3/wtf8/s25-o3/obj/trust-witness', 'its witness (obj/ holds no object)'),
    ('s24c-run/diag-o3/wtf8/s25-o3/tir', 'the TrustIR container it compiled (binary and JSON)'),
    # Gate 6 on the census record's commit.
    ('s24c-run/logs/gate6-fmt-r5.log', 'census record: gate 6, format, on ad02a8f06'),
    ('s24c-run/logs/gate6-docs-r5.log', 'census record: gate 6, documentation, on ad02a8f06'),
    ('s24c-run/logs/gate6-matrix-r5.log', 'census record: gate 6, the full-test-matrix hosts check, on ad02a8f06'),
    # Gate 6 on the fact-check fixes' commit.
    ('s24c-run/logs/gate6-fmt-r6.log', 'fact-check fixes: gate 6, format, on 87d0107b6'),
    ('s24c-run/logs/gate6-docs-r6.log', 'fact-check fixes: gate 6, documentation, on 87d0107b6'),
    ('s24c-run/logs/gate6-matrix-r6.log', 'fact-check fixes: gate 6, the full-test-matrix hosts check, on 87d0107b6'),
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
