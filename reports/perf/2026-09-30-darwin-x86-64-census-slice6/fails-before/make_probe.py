"""Assemble the temporary fails-before probe from the slice-6 test module.

usage: make_probe.py install | uninstall
install: writes crates/trust-cg-verify/src/x86_source_bound_body_fb_probe.rs
(fixture builders, helpers, variants and refutation mutants copied verbatim
from the slice-6 tests, plus the probe) and registers it in the tests module.
"""
import os
import sys

ROOT = '~/trust-cg/.claude/worktrees/agent-a5088c5df59865bdd/'
SCRATCH = ('<scratch>
           '03d2cfdb-f305-414e-850d-d6c2ce00de82/scratchpad/slice6/')
SLICE6 = SCRATCH + 'slice6_tests_snapshot.rs'
PROBE = ROOT + 'crates/trust-cg-verify/src/x86_source_bound_body_fb_probe.rs'
TESTS = ROOT + 'crates/trust-cg-verify/src/x86_source_bound_body_tests.rs'
REG = '\n#[path = "x86_source_bound_body_fb_probe.rs"]\nmod fb_probe;\n'


def between(text, start, end):
    i = text.index(start)
    j = text.index(end, i)
    return text[i:j]


if sys.argv[1] == 'uninstall':
    if os.path.exists(PROBE):
        os.remove(PROBE)
    t = open(TESTS).read()
    if REG in t:
        open(TESTS, 'w').write(t.replace(REG, ''))
    print('uninstalled')
    sys.exit(0)

s = open(SLICE6).read()
parts = [
    between(s, '/// Slice-6 fixture shapes.', '/// The LIR of `source`, one line per instruction'),
    between(s, '/// The walk ordinal of the `n`-th row with `opcode`.',
            '#[test]\nfn every_slice_six_refutation_is_refuted_on_samples'),
    between(s, 'pub(crate) fn slice_six_variants()',
            "/// The real x86 optimizer's output at O1"),
]
head = ('#![allow(dead_code, unused_imports)]\n'
        '//! TEMPORARY fails-before probe; never committed.\n\n'
        'use super::slice5::describe;\nuse super::*;\n'
        'use trust_ir::{Constant, ICmpOp, SwitchCase};\n\n')
tail = open(SCRATCH + 'fb_probe_tail.rs').read()
open(PROBE, 'w').write(head + '\n'.join(parts) + tail)
t = open(TESTS).read()
if REG not in t:
    open(TESTS, 'w').write(t + REG)
print('installed')
