#!/usr/bin/env python3
"""Mutants for rulings OD-216 to OD-218: guard each new check behind `TCG_OD216_MUTANT=<name>`, so
one test build runs every mutant (the test runner forwards TCG_* variables to the test binary, and
a codegen test's child process inherits them). Restore the files with `git checkout` afterwards;
never commit them. `run_od216_mutants.sh` runs the controls once per mutant.

usage: mutate_od216.py <worktree root>

Mutants (each the code before the fix; a control must fail):
  od216-link-unit-unread         `X86ModuleDefinitions::with_link_unit` keeps nothing: the routines
                                 the crate's other codegen units define never reach the verifier
                                 (OD-210 as landed: the module alone)
  od217-memory-routine-untrusted the C memory routines' call arm records no routine: a theorem over
                                 a `Memcpy`/`Memmove`/`Memset` trusts its routine unguarded (slice
                                 13 as landed)
  od218-memset-route-recursive   the vectorizer's fill tier takes the `memset` route in `memset`
                                 itself
"""
import sys

root = sys.argv[1]
M = 'std::env::var("TCG_OD216_MUTANT").is_ok_and(|mutant| mutant == "{}")'
OWNER = 'crates/trust-cg-verify/src/x86_source_bound_body.rs'
VECTORIZE = 'crates/trust-cg-opt/src/x86_vectorize.rs'
EDITS = [
    ("od216-link-unit-unread", OWNER,
     '        for routine in symbols.into_iter().filter_map(Self::trusted_routine) {\n',
     '        if ' + M.format("od216-link-unit-unread") + ' {\n            return self;\n        }\n'
     '        for routine in symbols.into_iter().filter_map(Self::trusted_routine) {\n'),
    ("od217-memory-routine-untrusted", OWNER,
     '                        sites.routines.insert(symbol);\n',
     '                        if !' + M.format("od217-memory-routine-untrusted") + ' {\n'
     '                            sites.routines.insert(symbol);\n                        }\n'),
    ("od218-memset-route-recursive", VECTORIZE,
     '        || function == RuntimeSymbol::Memset.name()\n',
     '        || (function == RuntimeSymbol::Memset.name()\n'
     '            && !' + M.format("od218-memset-route-recursive") + ')\n'),
]
for name, path, old, new in EDITS:
    full = f"{root}/{path}"
    text = open(full).read()
    if text.count(old) != 1:
        sys.exit(f"{name}: anchor found {text.count(old)} times in {path}")
    open(full, "w").write(text.replace(old, new))
    print(f"applied {name}")
