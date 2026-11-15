#!/usr/bin/env python3
"""Slice-17 rule mutants: guard each slice-17 rule behind
`TCG_S17_MUTANT=<name>`, so one test build runs every mutant (the test runner
forwards TCG_* variables to the test binary). Restore the files with
`git checkout` afterwards; never commit them.

usage: mutate.py <worktree root>

Mutants (each disables one slice-17 rule; a control the rule exists for must
fail):
  no-source-ib             the source states no in-bounds claim
  no-machine-ib            the machine states no in-bounds claim
  ib-no-congruence         the in-bounds claim omits the congruence (the
                           candidates are still restricted)
  store-no-update          an indexed store leaves its bytes as they were
  store-first-candidate    an indexed store updates only the bytes the first
                           candidate covers
  candidates-one-short     the candidates stop one offset short (k <= n-w-1)
  arg-offset-unobserved    an indexed argument is observed as its slot's
                           address alone (no offset)
  arg-slot-unchecked       the machine's indexed argument may name another
                           slot
  indexed-taint-dropped    a value an indexed load reads is never tainted
  indexed-bool-unchecked   a bool read through an indexed address is admitted
                           whatever its candidates' bytes
  bound-finder-admits-all  every indexed use is admitted unbounded
  dead-byte-ignores-loads  the byte liveness counts no load as a read
  dead-byte-keeps-value    a machine byte dead at a loop header keeps its
                           entry edge's value instead of becoming unreadable
  agep-stride-one          an `ArrayGep` of a private slot at a variable index
                           is indexed with stride 1, not the element size
  bound-ignores-stride     the bound finder scales the index's range by the
                           index's own stride only, not the address's
"""
import sys

root = sys.argv[1]
M = 'std::env::var("TCG_S17_MUTANT").is_ok_and(|mutant| mutant == "{}")'
OWNER = 'crates/trust-cg-verify/src/x86_source_bound_body.rs'
INDEXED = 'crates/trust-cg-verify/src/x86_source_bound_body/indexed.rs'
SPLIT = 'crates/trust-cg-verify/src/x86_source_bound_body/split.rs'
EDITS = [
    ("no-source-ib", OWNER,
     '            program\n                .indexed\n                .iter()\n                .map(|site| {\n',
     '            program\n                .indexed\n                .iter()\n'
     f'                .filter(|_| !{M.format("no-source-ib")})\n'
     '                .map(|site| {\n'),
    ("no-machine-ib", OWNER,
     '        indexed: indexed_claims,\n    })\n}\n',
     f'        indexed: if {M.format("no-machine-ib")} {{\n'
     '            Vec::new()\n        } else {\n            indexed_claims\n        },\n    })\n}\n'),
    ("ib-no-congruence", INDEXED,
     '    if modulus == 1 {\n        within\n',
     f'    if modulus == 1 || {M.format("ib-no-congruence")} {{\n        within\n'),
    ("store-no-update", INDEXED,
     'pub(super) fn update(offset: &E, arms: Vec<(i64, E)>, old: E) -> E {\n',
     'pub(super) fn update(offset: &E, arms: Vec<(i64, E)>, old: E) -> E {\n'
     f'    if {M.format("store-no-update")} {{\n        return old;\n    }}\n'),
    ("store-first-candidate", INDEXED,
     '    candidates\n        .iter()\n        .filter(|k| **k <= position',
     '    candidates\n        .iter()\n'
     f'        .take(if {M.format("store-first-candidate")} {{ 1 }} else {{ usize::MAX }})\n'
     '        .filter(|k| **k <= position'),
    ("candidates-one-short", INDEXED,
     '    (0..=u64::from(last))\n',
     f'    (0..=u64::from(last).saturating_sub(u64::from({M.format("candidates-one-short")})))\n'),
    ("arg-offset-unobserved", INDEXED,
     'pub(super) fn argument_term(slot: u32, offset: E) -> E {\n',
     'pub(super) fn argument_term(slot: u32, offset: E) -> E {\n'
     f'    if {M.format("arg-offset-unobserved")} {{\n'
     '        return E::var(slot_address_name(slot), 64);\n    }\n'),
    ("arg-slot-unchecked", OWNER,
     '                            if slot != source.slot {\n',
     f'                            if slot != source.slot && !{M.format("arg-slot-unchecked")} {{\n'),
    ("indexed-taint-dropped", OWNER,
     '                        if derived {\n                            tainted.insert(inst.results[0]);\n                        }\n                        indexed_sites.push(IndexedSite {\n',
     f'                        if derived && !{M.format("indexed-taint-dropped")} {{\n'
     '                            tainted.insert(inst.results[0]);\n                        }\n                        indexed_sites.push(IndexedSite {\n'),
    ("indexed-bool-unchecked", OWNER,
     '                                _ if carrier == Carrier::B1 => {\n                                    if !matches!(\n                                        read.as_slice(),\n                                        [(_, Some(byte))] if byte.read_as_bool()\n                                    ) {\n                                        return Err(outside(\n                                            "loads a bool through an indexed address',
     '                                _ if carrier == Carrier::B1 => {\n'
     f'                                    if !{M.format("indexed-bool-unchecked")} && !matches!(\n'
     '                                        read.as_slice(),\n                                        [(_, Some(byte))] if byte.read_as_bool()\n                                    ) {\n                                        return Err(outside(\n                                            "loads a bool through an indexed address'),
    ("bound-finder-admits-all", OWNER,
     '    #[cfg(test)]\n    if WITHOUT_INDEXED_BOUNDS.with(std::cell::Cell::get) {\n',
     f'    #[cfg(test)]\n    if WITHOUT_INDEXED_BOUNDS.with(std::cell::Cell::get) || {M.format("bound-finder-admits-all")} {{\n'),
    ("dead-byte-ignores-loads", SPLIT,
     '            L::Load { ty, .. } | L::AtomicLoad { ty, .. } => match addresses.get(&inst.args[0]) {\n',
     f'            L::Load {{ ty, .. }} | L::AtomicLoad {{ ty, .. }} if !{M.format("dead-byte-ignores-loads")} => match addresses.get(&inst.args[0]) {{\n'),
    ("dead-byte-keeps-value", OWNER,
     '    // Slice 17: a byte dead at the header starts unreadable.\n    for &(slot, offset) in &header.dead {\n        state.stack[slot as usize][offset as usize] = Some(MachineByte::dead());\n',
     '    // Slice 17: a byte dead at the header starts unreadable.\n'
     f'    for &(slot, offset) in header.dead.iter().filter(|_| !{M.format("dead-byte-keeps-value")}) {{\n'
     '        state.stack[slot as usize][offset as usize] = Some(MachineByte::dead());\n'),
    ("agep-stride-one", OWNER,
     '                            delta: index,\n                            stride,\n',
     '                            delta: index,\n'
     f'                            stride: if {M.format("agep-stride-one")} {{ 1 }} else {{ stride }},\n'),
    ("bound-ignores-stride", INDEXED,
     '        let step = i128::from(chain.stride) * i128::from(address.stride);\n',
     '        let step = i128::from(chain.stride)\n'
     f'            * if {M.format("bound-ignores-stride")} {{ 1 }} else {{ i128::from(address.stride) }};\n'),
]
for name, path, old, new in EDITS:
    full = f"{root}/{path}"
    text = open(full).read()
    count = text.count(old)
    if count != 1:
        sys.exit(f"{name}: anchor found {count} times in {path}")
    open(full, "w").write(text.replace(old, new))
    print(f"applied {name}")
