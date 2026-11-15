#!/usr/bin/env python3
"""Print the PAYLOADS.md table rows of the OD-224 report (path relative to ~/tcg-scratch, bytes,
sha256). A directory's row is its total bytes over its top-level files and the SHA-256 of its
manifest: one line `<sha256>  <name>` per file, sorted by name, newline-terminated (slice 23's
payloads23.py, OD-215's payloads_m1.py)."""
import hashlib
import os

H = os.path.expanduser('~/tcg-scratch')
FILES = [
    ('i128-mulo-design/README.md', 'the design this lane implements'),
    ('mulo-run/logs/main_f2a0_ti3_callers.txt', 'main\'s census objects that call a 128-bit division routine (census-s23-f2a0)'),
    # The whole-core probe (core-ir-s23), the lane's final code (p4).
    ('mulo-run/probe/x86_body_probe.rs', 'the probe source (OD-215\'s copy plus the MULO_DIVISION_FORM toggle; never committed)'),
    ('mulo-run/probe/x86_body_probe_p4', 'the probe built from the lane at c8a802a7c'),
    ('mulo-run/logs/probe_build_p4.log', 'its build'),
    ('mulo-run/logs/chain_probe_p4.txt', 'the probe chain\'s log'),
    ('mulo-run/all/p4_new/cf.tsv', 'the whole-core probe, division-free form'),
    ('mulo-run/all/p4_new/cf.err', 'its stderr (pairing records)'),
    ('mulo-run/all/p4_new/smt2/', 'its queries'),
    ('mulo-run/all/p4_old/cf.tsv', 'the whole-core probe, division form (MULO_DIVISION_FORM=1)'),
    ('mulo-run/all/p4_old/smt2/', 'its queries'),
    ('i128sh-m1/all/m1/cf.tsv', 'main\'s whole-core probe (6607d0f6b with the fold)'),
    ('mulo-run/logs/probe_diff_m1_p4_old.txt', 'diff -r of main\'s queries and the division form\'s (empty)'),
    ('mulo-run/all/cmp_old_new_p4.txt', 'the division form against the division-free one, function by function'),
    ('mulo-run/all/cmp_old_new_p4.changed.tsv', 'the 11 functions whose theorem bytes change'),
    # The census route.
    ('mulo-run/stage/names.txt', 'the 11 changed functions'),
    ('mulo-run/stage/new/q/', 'their units, claims, generalizations and arbiters, division-free'),
    ('mulo-run/stage/old/q/', 'the same in the division form (= main)'),
    ('mulo-run/replay/data/replays.jsonl', 'every one-shot replay (AY 13556, Clean 5f09e36c), keyed by the bytes\' sha256'),
    ('mulo-run/replay/chain_replay.txt', 'the every-route replay chain\'s log'),
    ('mulo-run/replay/route_new_p4.md', 'the production route, division-free'),
    ('mulo-run/replay/route_old_p4.md', 'the production route, division form'),
    ('mulo-run/replay/route_cost.txt', 'the AY and Clean seconds the route spent per function'),
    ('mulo-run/replay/table_mulo.md', 'the per-function route table'),
    ('mulo-run/replay/route_new.md', 'the first form\'s production route (9 of 11)'),
    ('mulo-run/replay/route_new3.md', 'the second form\'s (10 of 11)'),
    ('mulo-run/exp/exp1.out', 'div_rem_1e16\'s claim 3 offline at 120 s (the first form)'),
    # The fresh dump.
    ('mulo-run/logs/bridge_build.log', 'the release bridge build from the lane'),
    ('mulo-run/mulo.dylib', 'the bridge'),
    ('mulo-run/logs/dump.out', 'the fresh core dump'),
    ('mulo-run/core-ir-mulo/', 'its trust-ir modules'),
    ('mulo-run/logs/dump_diff_s23.txt', 'its diff against core-ir-s23 (the JSON sidecars\' new field only)'),
    ('mulo-run/logs/chain_bridge.txt', 'the bridge chain\'s log (the fresh probe equals core-ir-s23\'s)'),
    # Fixtures, qualification, tests.
    ('mulo-run/qual_4/summary.txt', 'the tool-gated lanes on the measured code (one test per process)'),
    ('mulo-run/logs/sweep16.log', 'the 2^32-pair sweeps at W = 16'),
    ('mulo-run/logs/e2e_mulo_nocapture.log', 'the native differential (O0-O3), with the fold'),
    ('mulo-run/logs/e2e_mulo_nofold.log', 'the same with TCG_NO_X86_I128_CONST_SHIFT=1'),
    ('mulo-run/icount/objs_fold/', 'the objects of the native module, with the fold'),
    ('mulo-run/icount/objs_nofold/', 'the same without it'),
    ('mulo-run/icount/counts.tsv', 'their per-function instruction counts'),
    ('mulo-run/icount/table.md', 'the count table'),
    # The gates on the final head.
    ('mulo-run/logs/chain_gates.txt', 'the gates chain\'s log'),
    ('mulo-run/logs/gate_lower.log', 'trust-cg-lower --lib'),
    ('mulo-run/testbin_final', 'the trust-cg-verify library test binary'),
    ('mulo-run/logs/gate_suite.log', 'the solver-free x86 body suite'),
    ('mulo-run/logs/gate_l04p10.log', 'L04-P10\'s solver-free tests'),
    ('mulo-run/qual_final/summary.txt', 'the tool-gated lanes, one test per process'),
    ('mulo-run/qual_final/', 'their logs'),
    ('mulo-run/logs/gate_verify_int.log', 'proof_gate_strict and coverage_gate_tests (the moved pins)'),
    ('mulo-run/logs/gate_pipeline.log', 'pipeline backend_expansion_nounwind_callees'),
    ('mulo-run/logs/gate_codegen.log', 'the codegen targets'),
    ('mulo-run/logs/gate_codegen_nocapture.log', 'the native differential and the body lane with --nocapture'),
    ('mulo-run/logs/gate_fmt.log', 'check_fmt.sh'),
    ('mulo-run/logs/gate_doc.log', 'check_documentation.py --check'),
    ('mulo-run/logs/gate_matrix.log', 'full_test_matrix_hosts.py --check'),
    # The z3 lemmas of section 4.7 (solver-backed only).
    ('mulo-run/z3/od224_z3.json', 'every lemma, control and cross-check of proofs/od224_z3.py, with its z3 CPU time'),
    ('mulo-run/z3/od224_z3.err', 'its stderr (empty)'),
    # The merged head's probe over the fresh dump.
    ('mulo-run/probe/x86_body_probe_p5', 'the probe built from the merged head 07c38c1a3'),
    ('mulo-run/logs/chain_probe_p5.txt', 'its chain\'s log (both forms as measured, byte for byte)'),
    ('mulo-run/all/p5_new/cf.tsv', 'its whole-core run, division-free'),
    ('mulo-run/all/p5_old/cf.tsv', 'its whole-core run, division form'),
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
