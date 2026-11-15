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
    ('s22-design/README.md', 'the slice-22 design (§1-§6)'),
    ('s22-design/data/names14.txt', 'the 14 roots'),
    ('runs/census-s21/failed_roots.jsonl', 'census-s21, the 36 failed roots the design read'),
    ('runs/census-s21/stderr.log', 'its body trace (the census outcome of every function)'),
    ('runs/s21.dylib', 'the census-s21 bridge the fresh dump ran'),
    # The fresh dump and the real bytes.
    ('runs/core-ir-s22/', 'the fresh `core` trust-ir dump (`census/dump_core_ir.sh`)'),
    ('s22-run/logs/dump.log', 'its log'),
    ('s22-run/probe/x86_body_probe_a2', 'the probe at 22a (OD-202)'),
    ('s22-run/probe/x86_body_probe_b', 'the probe at 22b without `guard`'),
    ('s22-run/probe/x86_body_probe_b2', 'the probe at 22b (OD-203)'),
    ('s22-run/probe/x86_body_probe_m', 'the probe on the merged tree without `catnf` (22b, trust-ir pin `73c5a310`)'),
    ('s22-run/probe/x86_body_probe_c', 'the probe at 22c (OD-204)'),
    ('s22-run/probe/trace_spelling.patch', 'the local spelling trace (never committed) that found the folded guard'),
    ('s22-run/probe/x86_body_probe_trace', 'the probe with that trace'),
    ('s22-run/trace/trace.err', 'its trace over the 14 roots'),
    ('s22-run/probe/trace2.patch', 'the second trace (22b without `guard`; theorems and parts)'),
    ('s22-run/probe/x86_body_probe_trace2', 'the probe with it'),
    ('s22-run/trace/trace32b.err', 'its trace over the 32 functions the step changes (each failed the check)'),
    ('s22-run/stage_a2/q/', 'the 14 roots\' queries and claim splits at 22a'),
    ('s22-run/stage_b/q/', 'the same at 22b without `guard`'),
    ('s22-run/stage_b2/q/', 'the same at 22b'),
    ('s22-run/stage_c/q/', 'the same at 22c'),
    ('s22-run/data/replays.jsonl', 'every one-shot replay (AY 13556 + Clean, 30 s), keyed by the bytes\' sha256'),
    ('s22-run/data/roots_a2.tsv', 'the per-root outcome at 22a'),
    ('s22-run/data/roots_b.tsv', 'at 22b without `guard`'),
    ('s22-run/data/roots_b2.tsv', 'at 22b'),
    ('s22-run/data/roots_c.tsv', 'at 22c'),
    ('s22-run/gaps/offline300.jsonl', 'the 300 s offline replays (U128MulConst, the cut fixture\'s first form, div_rem_1e16 at 22b)'),
    # The whole core.
    ('s22-run/all/main/cf.tsv', 'the whole-core probe, main (s21\'s probe)'),
    ('s22-run/all/a2/cf.tsv', 'at 22a'),
    ('s22-run/all/b/cf.tsv', 'at 22b without `guard`'),
    ('s22-run/all/b2/cf.tsv', 'at 22b'),
    ('s22-run/all/m/cf.tsv', 'the merged tree without `catnf`'),
    ('s22-run/all/c/cf.tsv', 'at 22c'),
    ('s22-run/logs/regress_ac.txt', 'every function whose theorem 22b and 22c change, with its census outcome'),
    ('s22-run/regress_ac/q/', 'the 142 census-certified ones\' 22c queries'),
    ('s22-run/data/roots_regress_ac.tsv', 'their replay (cached from the stage replays)'),
    ('s22-run/data/roots_regress_b2.tsv', 'the `guard` step\'s 32'),
    ('s22-run/data/roots_regress_c.tsv', '`catnf`\'s 112'),
    ('s22-run/data/roots_fmt_m.tsv', '`u128` `__fmt_inner` claim by claim without `catnf`'),
    ('s22-run/data/roots_fmt_c.tsv', 'and with it'),
    # OD-202's evidence and OD-203's exactness.
    ('s22-run/logs/native_diff.log', 'the native differential of both bindings (n = 20000)'),
    ('s22-run/logs/limb_exhaustive.txt', '`limb_exhaustive.c` at limbs of 1 to 8 bits'),
    ('s22-run/logs/limb_lemmas_z3.txt', 'z3 5.1.0 on `limb/*.smt2`'),
    ('s22-run/ayissue/a3.alethe', 'the AY issue note\'s proof (the rejected step at line 542)'),
    ('s22-run/ayissue/a3.clean.out', 'Clean\'s rejection'),
    # Goldens.
    ('s22-run/goldens/pre22b/', 'every golden before OD-203'),
    ('s22-run/goldens/pre22c/', 'every golden before OD-204'),
    ('s22-run/goldens/c1/', 'every golden at 22c'),
    ('s22-run/goldens/review_b4/review.jsonl', 'the review of OD-203\'s moves'),
    ('s22-run/goldens/review_c1/review.jsonl', 'the review of OD-204\'s moves'),
    # Fails-before.
    ('s22-run/mutants_all/', 'the mutant run (16 mutants; summary and each run\'s log)'),
    # Qualification and gates.
    ('s22-run/data/repeats_c.jsonl', 'three more replays of the four slowest certified class queries'),
    ('s22-run/qual_final/', 'the final qualification, one test per process (48 lanes and the deadline-bound lane)'),
    ('s22-run/logs/gate_a3.log', 'the solver-free x86 body suite at 22a'),
    ('s22-run/logs/gate_b5.log', 'at 22b'),
    ('s22-run/logs/gate_c5.log', 'on the final code'),
    ('s22-run/logs/codegen_final.body.log', 'the codegen body end-to-end lane'),
    ('s22-run/logs/codegen_final.identity.log', 'its replay identity (AY 13556), run with --nocapture'),
    ('s22-run/logs/codegen_final.mrc.log', 'the must-refuse corpus'),
    ('s22-run/logs/e2e_i128_div.log', 'the native i128 division end-to-end (lowering evidence)'),
    ('s22-run/logs/lower.log', 'trust-cg-lower --lib'),
    ('s22-run/logs/check_fmt.log', 'scripts/check_fmt.sh (the 6808 package\'s targo fmt)'),
    ('runs/main-20649af.dylib', 'the landing baseline bridge, main `20649afe9`'),
    ('runs/census-main-20649af/failed_roots.jsonl', 'the landing baseline census'),
    ('runs/census-main-20649af/stderr.log', 'its body trace'),
    ('runs/census-main-20649af.out', 'its summary'),
    ('runs/s22.dylib', 'the slice-22 bridge, `b596e62fe`'),
    ('runs/census-s22/failed_roots.jsonl', 'the slice-22 census'),
    ('runs/census-s22/stderr.log', 'its body trace'),
    ('runs/census-s22.out', 'its summary'),
    ('s22/compare/', '`census_compare.py` of the two rows'),
    ('s22/logs/census_chain_kept.log', 'the census chain log'),
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
