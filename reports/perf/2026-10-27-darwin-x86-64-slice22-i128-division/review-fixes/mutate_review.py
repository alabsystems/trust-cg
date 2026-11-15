#!/usr/bin/env python3
"""Mutants for the fixes of the hostile review of slice 22 (OD-210 and three controls): guard each
checked rule behind `TCG_S22R_MUTANT=<name>`, so one test build runs every mutant (the test runner
forwards TCG_* variables to the test binary). Restore the files with `git checkout` afterwards;
never commit them. `run_review_mutants.sh` runs the controls once per mutant.

usage: mutate_review.py <worktree root>

Mutants (each the code before the fix, or the mutant the review said would survive; a control
must fail):
  od210-routine-trusted      `check_trusted_routines` trusts every routine (slice 22 as landed:
                             no module definition is read)
  od210-circular-trusted     the function under proof may be the routine it calls
  catnf-merge-two-terms      the merge of adjacent extracts drops its same-term check
                             (`self.arg(c, 0) == self.arg(a, 0)`)
  catnf-extract-sext         an extract across a SIGN extension's boundary is read as a zero
                             extension's
  catnf-or-sext              the `bvor` of a SIGN extension and a chain ending in zeros merges
  guard128-zero-never-fires  a guard of any 128-bit constant never fires (the `lo | hi != 0` test
                             dropped)
"""
import sys

root = sys.argv[1]
M = 'std::env::var("TCG_S22R_MUTANT").is_ok_and(|mutant| mutant == "{}")'
OWNER = 'crates/trust-cg-verify/src/x86_source_bound_body.rs'
NORMAL = 'crates/trust-cg-verify/src/x86_source_bound_body/normal.rs'
EDITS = [
    ("od210-routine-trusted", OWNER,
     '    for routine in owner.trusted_routines() {\n',
     '    if ' + M.format("od210-routine-trusted") + ' {\n        return Ok(());\n    }\n'
     '    for routine in owner.trusted_routines() {\n'),
    ("od210-circular-trusted", OWNER,
     '        let definition = if owner.source().name == routine {\n',
     '        let definition = if owner.source().name == routine\n'
     '            && !' + M.format("od210-circular-trusted") + '\n        {\n'),
    ("catnf-merge-two-terms", NORMAL,
     '                        && self.arg(c, 0) == self.arg(a, 0)\n',
     '                        && (self.arg(c, 0) == self.arg(a, 0)\n'
     '                            || ' + M.format("catnf-merge-two-terms") + ')\n'),
    ("catnf-extract-sext", NORMAL,
     '                    Op::ZeroExtend(_) => {\n                        let y = self.arg(x, 0);\n',
     '                    Op::ZeroExtend(_) | Op::SignExtend(_)\n'
     '                        if matches!(self.op(x), Op::ZeroExtend(_))\n'
     '                            || ' + M.format("catnf-extract-sext") + ' =>\n'
     '                    {\n                        let y = self.arg(x, 0);\n'),
    ("catnf-or-sext", NORMAL,
     '                    if !matches!(self.op(p), Op::ZeroExtend(_)) || *self.op(q) != Op::Concat {\n',
     '                    if !(matches!(self.op(p), Op::ZeroExtend(_))\n'
     '                        || (' + M.format("catnf-or-sext") + '\n'
     '                            && matches!(self.op(p), Op::SignExtend(_))))\n'
     '                        || *self.op(q) != Op::Concat\n                    {\n'),
    ("guard128-zero-never-fires", OWNER,
     '                            && matches!(definition.op, SourceOp::Wide { lo, hi } if lo | hi != 0)\n',
     '                            && matches!(definition.op, SourceOp::Wide { lo, hi }\n'
     '                                if lo | hi != 0 || ' + M.format("guard128-zero-never-fires") + ')\n'),
]
for name, path, old, new in EDITS:
    full = f"{root}/{path}"
    text = open(full).read()
    if text.count(old) != 1:
        sys.exit(f"{name}: anchor found {text.count(old)} times in {path}")
    open(full, "w").write(text.replace(old, new))
    print(f"applied {name}")
