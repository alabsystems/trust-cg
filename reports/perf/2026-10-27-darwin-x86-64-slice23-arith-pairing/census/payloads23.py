#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows (path relative to ~/tcg-scratch, bytes, sha256).

A directory's row is its total bytes over its top-level files and the SHA-256
of its manifest: one line `<sha256>  <name>` per file, sorted by name,
newline-terminated."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    # The design this slice implements, and the census it reads.
    ('s23-design/README.md', 'the slice-23 design (§1-§7)'),
    ('s23-design/data/dump_sha256.txt', 'census-s22\'s three dumped root queries (sha256)'),
    ('runs/census-s22/failed_roots.jsonl', 'census-s22, the 23 failed roots'),
    ('runs/census-s22/stderr.log', 'its body trace (the census outcome of every function)'),
    # The fresh dump and the real bytes.
    ('runs/s23.dylib', 'the release bridge built from this branch at `addf2c93f`'),
    ('runs/core-ir-s23/', 'the fresh `core` trust-ir dump from it (byte for byte `core-ir-s22`)'),
    ('runs/core-ir-s22/', 'census-s22\'s dump'),
    ('s23-run/logs/dump.log', 'the dump\'s log'),
    ('s23-run/probe/x86_body_probe_p1', 'the probe at p1 (the row-level gate)'),
    ('s23-run/probe/x86_body_probe_p1t', 'p1 with the pairing trace (never committed)'),
    ('s23-run/probe/x86_body_probe_p1t2', 'p1 with the full-context trace (never committed)'),
    ('s23-run/stage_p1t2/roots.err', 'the traced run: each candidate row and the row-level gate\'s answer'),
    ('s23-run/probe/x86_body_probe_p2', 'the probe at p2 (the theorem-level gate)'),
    ('s23-run/probe/x86_body_probe_p3', 'the probe at p3 (merged with origin/main `4bf54e061`)'),
    ('s23-run/probe/x86_body_probe_p3m', 'p3 built with the rule mutants (TCG_S23_MUTANT)'),
    ('s23-run/probe/x86_body_probe_p4', 'the probe on the final code (merged with origin/main `c06393ad6`)'),
    ('s23-run/stage_p1/q/', 'the three roots\' queries, claim splits and generalizations at p1'),
    ('s23-run/stage_p2/q/', 'the same at p2 (= p3 = p4)'),
    ('s23-run/stage_p4/q/', 'the same on the final code'),
    ('s23-run/stage_p2/table.md', 'the per-root route at p2'),
    ('s23-run/stage_p2/align_all.tsv', 'every align_offset query replayed'),
    ('s23-run/stage_p2/pow_all.tsv', 'every overflowing_pow query replayed'),
    ('s23-run/stage_p2/smul_all.tsv', 'every scalar_mul query replayed'),
    ('s23-run/data/replays.jsonl', 'every one-shot replay (AY 13556 + Clean, 30 s), keyed by the bytes\' sha256'),
    # The whole core.
    ('s22-run/all/c/cf.tsv', 'the whole-core probe at slice 22 (22c; census-s22\'s bytes)'),
    ('s23-run/all/p2/cf.tsv', 'the whole-core probe at p2'),
    ('s23-run/all/p3/cf.tsv', 'at p3'),
    ('s23-run/all/p3m/cf.tsv', 'at p3 with the absorbed-pairing gate off (TCG_S23_MUTANT=pairing-never-absorbed)'),
    ('s23-run/all/p4/cf.tsv', 'on the final code'),
    ('s23-run/regress_p2/q/', 'the 15 changed census-certified functions\' queries'),
    ('s23-run/regress_p2/table.md', 'their replay'),
    ('s23-run/stage_grisu/table.md', '`format_shortest_opt`\'s route with claims and generalizations'),
    # Goldens.
    ('s23-run/goldens/pre23/', 'every golden before slice 23'),
    ('s23-run/goldens/new1/', 'every golden after'),
    ('s23-run/goldens/review1/out/review.jsonl', 'the review of the 5 moved theorems'),
    # Fails-before, qualification and gates.
    ('s23-run/mutants3/summary.txt', 'the mutant run on the final code (one log per mutant beside it)'),
    ('s23-run/gaps/offline300.jsonl', 'the four slice-23 exact gaps replayed offline at 300 s'),
    ('s23-run/qual_final2/summary.txt', 'the final qualification, one test per process (53 lanes and the deadline-bound lane)'),
    ('s23-run/logs/suite_final.log', 'the solver-free x86 body suite on the final code'),
    ('s23-run/logs/codegen_final2.log', 'the codegen body and must-refuse lanes'),
    ('s23-run/logs/lower_final.log', 'trust-cg-lower --lib'),
    # The hostile review of 9f7aa5b2b and its fixes (section 9).
    ('s23-review/stale_rdx.py', 'the review\'s z3 script for check (3)'),
    ('s23-review/shift_sem.py', 'the review\'s z3 script for the shift keys'),
    ('s23-fix/logs/s23_w2.log', 'the slice-23 and negative-memo controls on the fixes (2acc76c22)'),
    ('s23-fix/all/w2/cf.tsv', 'the whole-core probe on the fixes, before the merge'),
    ('s23-fix/logs/probe_diff_w2.txt', 'its diff against p4 (empty)'),
    ('s23-fix/mutants/summary.txt', 'the 20 mutants\' run (one log per mutant beside it)'),
    ('s23-fix/logs/suite_w3.log', 'the solver-free x86 body suite after the merge'),
    ('s23-fix/logs/codegen_w3.log', 'the codegen body and must-refuse lanes after the merge'),
    ('s23-fix/logs/lower_w3.log', 'trust-cg-lower --lib after the merge'),
    ('s23-fix/logs/cli_w3b.log', 'trust-cg-cli emit_proofs after the merge'),
    ('s23-fix/all/w3/cf.tsv', 'the whole-core probe after the merge'),
    ('s23-fix/all/w3/cf.err', 'its stderr, with each paired owner\'s pairing record re-derived'),
    ('s23-fix/logs/probe_diff_w3.txt', 'its diff against p4 (empty)'),
    ('s23-fix/qual_w3/summary.txt', 'the touched qualification lanes after the merge'),
    ('s23-fix/qual_tm/summary.txt', 'two lanes under the mutant pair-stamp-only'),
    ('s23-fix/logs/suite_w4.log', 'the solver-free x86 body suite after the second merge'),
    ('s23-fix/logs/codegen_w4.log', 'the codegen lanes after the second merge'),
    ('s23-fix/logs/cli_w4.log', 'trust-cg-cli emit_proofs after the second merge'),
    ('s23-fix/all/w4/cf.tsv', 'the whole-core probe after the second merge'),
    ('s23-fix/all/w4/cf.err', 'its stderr, each paired owner\'s pairing record re-derived'),
    ('s23-fix/logs/probe_diff_w4.txt', 'its diff against p4 (empty)'),
    ('s23-fix/qual_w4/summary.txt', 'the touched qualification lanes after the second merge'),
    ('s23-fix/logs/suite_w5.log', 'the solver-free x86 body suite on the final head'),
    ('s23-fix/logs/memo_unit_w5.log', 'the negative memo\'s unit tests on the final head'),
    ('s23-fix/logs/codegen_w5.log', 'the codegen lanes on the final head'),
    ('s23-fix/logs/cli_w5.log', 'trust-cg-cli emit_proofs on the final head'),
    ('s23-fix/all/w5/cf.tsv', 'the whole-core probe on the final head'),
    ('s23-fix/all/w5/cf.err', 'its stderr, each paired owner\'s pairing record re-derived'),
    ('s23-fix/logs/probe_diff_w5.txt', 'its diff against p4 (empty)'),
    ('s23-fix/qual_w5/summary.txt', 'the touched qualification lanes on the final head'),
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
