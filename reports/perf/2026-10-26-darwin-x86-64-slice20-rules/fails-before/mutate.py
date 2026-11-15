#!/usr/bin/env python3
"""Slice-20 rule mutants: guard each slice-20 rule behind
`TCG_S20_MUTANT=<name>`, so one test build runs every mutant (the test runner
forwards TCG_* variables to the test binary). Restore the files with
`git checkout` afterwards; never commit them.

usage: mutate.py <worktree root>

Mutants (each breaks one slice-20 rule; a control the rule exists for must
fail):
 OD-191, a switch's binary-search blocks
  search-any-shape          any block of the switch's LIR block whose rows all
                            carry the switch's stamp is a search block,
                            whatever its rows
  search-any-predecessor    a search block may be reached from any block
  search-first-route-only   a route stops at its first way to the target (the
                            default keeps one of its routes)
  searched-switch-per-path  a source switch the selector may search is stated
                            per path, as before
 OD-192, a stored address dead at a DAG join
  join-dead-always          every byte holding a stored address at a join is
                            dead there, whatever reads it after the join
  join-dead-keeps-first     the source keeps the first edge's byte (the
                            address) instead of making it dead
  join-dead-machine-keeps   the machine's join ignores the bytes the source
                            made dead
 OD-193, I128 items as two halves
  i128-high-unrelated       no relation for the high register
  i128-high-pairing-from-low  the high register is the low one
  i128-pair-order-swapped   the higher virtual register holds the low half
  i128-start-halves-swapped the source's start value is low:high
  i128-machine-high-unset   the machine's region start leaves the high
                            register as the walk found it
  i128-pair-last-two-written  the pair is the last two 64-bit registers the
                            group writes, temporaries included (the WIP rule)
 OD-194, the singleton rules and the bounds
  shl128-no-bound           every variable I128 shift's amount is bounded
  boolread-any-byte         a byte no store wrote is bool-readable past a join
  boolread-bool-store-only  only a bool store's byte is (slice 19's rule)
  ufixed-in-loop            undefined bits a loop row introduces are fixed too
  ufixed-none               no undefined-bits input is fixed (slice 19's rule)
  slots-count-64            at most 64 slots again
  slots-total-unbounded     no bound on the slots' bytes in all
  candidates-256            at most 256 candidates per indexed access again
  candidates-unbounded      no candidate bound
"""
import sys

root = sys.argv[1]
M = 'std::env::var("TCG_S20_MUTANT").is_ok_and(|mutant| mutant == "{}")'
OWNER = 'crates/trust-cg-verify/src/x86_source_bound_body.rs'
INDEXED = 'crates/trust-cg-verify/src/x86_source_bound_body/indexed.rs'
SPLIT = 'crates/trust-cg-verify/src/x86_source_bound_body/split.rs'
EDITS = [
    ("search-any-shape", OWNER,
     '            let shaped = last.opcode == X86Opcode::Jmp\n',
     f'            let shaped = ({M.format("search-any-shape")} || last.opcode == X86Opcode::Jmp)\n'),
    ("search-any-shape", OWNER,
     '                    X86Opcode::Jcc => true,\n                    _ => false,\n                })\n',
     f'                    X86Opcode::Jcc => true,\n                    _ => {M.format("search-any-shape")},\n                }})\n'),
    ("search-any-predecessor", OWNER,
     '            let reached = predecessors.get(block).is_some_and(|from| {\n',
     f'            let reached = {M.format("search-any-predecessor")} || predecessors.get(block).is_some_and(|from| {{\n'),
    ("search-first-route-only", OWNER,
     '    if routes.is_empty() {\n        return Err(no_claim(format!(\n            "block {current:?} has no route to block {next_machine:?}, where the source \\\n',
     f'    if {M.format("search-first-route-only")} {{\n        routes.truncate(1);\n    }}\n'
     '    if routes.is_empty() {\n        return Err(no_claim(format!(\n            "block {current:?} has no route to block {next_machine:?}, where the source \\\n'),
    ("searched-switch-per-path", OWNER,
     '    cases.len() >= 5\n        && values.len() == cases.len()\n',
     f'    !{M.format("searched-switch-per-path")}\n        && cases.len() >= 5\n        && values.len() == cases.len()\n'),
    ("join-dead-always", OWNER,
     '    fn dead(&self, block: Block, address: FrameAddr) -> bool {\n',
     '    fn dead(&self, block: Block, address: FrameAddr) -> bool {\n'
     f'        if {M.format("join-dead-always")} {{\n            return true;\n        }}\n'),
    ("join-dead-keeps-first", OWNER,
     '                if liveness.dead(join, address) {\n                    *merged = Some(SlotByte::Dead);\n',
     '                if liveness.dead(join, address) {\n'
     f'                    if {M.format("join-dead-keeps-first")} {{\n                        continue;\n                    }}\n'
     '                    *merged = Some(SlotByte::Dead);\n'),
    ("join-dead-machine-keeps", OWNER,
     '            if dead.is_some_and(|dead| dead.contains(&(slot as u32, offset as i64))) {\n',
     f'            if !{M.format("join-dead-machine-keeps")} && dead.is_some_and(|dead| dead.contains(&(slot as u32, offset as i64))) {{\n'),
    ("i128-high-unrelated", OWNER,
     '            (Some(_), Some(high)) => vec![\n                (source.clone().extract(63, 0), low(register, 64)),\n                (source.extract(127, 64), low(high, 64)),\n            ],\n',
     f'            (Some(_), Some(_)) if {M.format("i128-high-unrelated")} => vec![\n                (source.extract(63, 0), low(register, 64)),\n            ],\n'
     '            (Some(_), Some(high)) => vec![\n                (source.clone().extract(63, 0), low(register, 64)),\n                (source.extract(127, 64), low(high, 64)),\n            ],\n'),
    ("i128-high-pairing-from-low", OWNER,
     '            (Root::Virtual(x), Root::Virtual(y)) => Some(if x < y { (*a, *b) } else { (*b, *a) }),\n',
     f'            (Root::Virtual(x), Root::Virtual(y)) if {M.format("i128-high-pairing-from-low")} => {{\n'
     '                let low = if x < y { *a } else { *b };\n                Some((low, low))\n            }\n'
     f'            (Root::Virtual(x), Root::Virtual(y)) if {M.format("i128-pair-order-swapped")} => {{\n'
     '                Some(if x < y { (*b, *a) } else { (*a, *b) })\n            }\n'
     '            (Root::Virtual(x), Root::Virtual(y)) => Some(if x < y { (*a, *b) } else { (*b, *a) }),\n'),
    ("i128-start-halves-swapped", OWNER,
     '    if carrier == Carrier::I128 {\n        E::var(header_half_name(header, i, true), 64)\n            .concat(E::var(header_half_name(header, i, false), 64))\n',
     f'    if carrier == Carrier::I128 && {M.format("i128-start-halves-swapped")} {{\n'
     '        E::var(header_half_name(header, i, false), 64)\n            .concat(E::var(header_half_name(header, i, true), 64))\n'
     '    } else if carrier == Carrier::I128 {\n        E::var(header_half_name(header, i, true), 64)\n            .concat(E::var(header_half_name(header, i, false), 64))\n'),
    ("i128-machine-high-unset", OWNER,
     '        if let Some((high, expr)) = root.high_template(header.block, i) {\n',
     f'        if let Some((high, expr)) = root.high_template(header.block, i).filter(|_| !{M.format("i128-machine-high-unset")}) {{\n'),
    ("i128-machine-high-unset", SPLIT,
     '        if let Some((high, expr)) = root.high_template(cut.block, i) {\n',
     f'        if let Some((high, expr)) = root.high_template(cut.block, i).filter(|_| !{M.format("i128-machine-high-unset")}) {{\n'),
    ("i128-pair-last-two-written", OWNER,
     '        if reg.bits != 64\n            || rows[k + 1..].iter().any(|later| {\n',
     f'        if reg.bits != 64\n            || !{M.format("i128-pair-last-two-written")} && rows[k + 1..].iter().any(|later| {{\n'),
    ("shl128-no-bound", INDEXED,
     '    let mut value = amount;\n    for _ in 0..64 {\n',
     f'    if {M.format("shl128-no-bound")} {{\n        return Some(0);\n    }}\n'
     '    let mut value = amount;\n    for _ in 0..64 {\n'),
    ("boolread-any-byte", OWNER,
     '        Some(SlotByte::Stored(_)) => true,\n        Some(byte) => byte.read_as_bool(),\n        None => false,\n',
     f'        Some(SlotByte::Stored(stored)) if {M.format("boolread-bool-store-only")} => stored.carrier == Carrier::B1,\n'
     '        Some(SlotByte::Stored(_)) => true,\n        Some(byte) => byte.read_as_bool(),\n'
     f'        None => {M.format("boolread-any-byte")},\n'),
    ("ufixed-in-loop", SPLIT,
     '        if in_loops.contains(lir) {\n            continue;\n        }\n',
     f'        if in_loops.contains(lir) && !{M.format("ufixed-in-loop")} {{\n            continue;\n        }}\n'
     f'        if {M.format("ufixed-none")} {{\n            continue;\n        }}\n'),
    ("slots-count-64", OWNER,
     '    if total > MAX_SLOT_TOTAL_BYTES {\n',
     f'    if (total > MAX_SLOT_TOTAL_BYTES && !{M.format("slots-total-unbounded")})\n'
     f'        || ({M.format("slots-count-64")} && slot_sizes.len() > 64)\n    {{\n'),
    ("candidates-256", INDEXED,
     'pub(super) const MAX_CANDIDATES: usize = 1024;\n',
     'pub(super) const MAX_CANDIDATES: usize = 1024;\n'
     'pub(super) fn max_candidates() -> usize {\n'
     f'    if {M.format("candidates-256")} {{\n        256\n'
     f'    }} else if {M.format("candidates-unbounded")} {{\n        usize::MAX / 2\n'
     '    } else {\n        MAX_CANDIDATES\n    }\n}\n'),
]
for name, path, old, new in EDITS:
    full = f"{root}/{path}"
    text = open(full).read()
    count = text.count(old)
    if count != 1:
        sys.exit(f"{name}: anchor found {count} times in {path}")
    open(full, "w").write(text.replace(old, new))
    print(f"applied {name}")
# The candidate bound's uses (the owner's three) read the mutable bound.
full = f"{root}/{OWNER}"
text = open(full).read()
uses = text.count("> indexed::MAX_CANDIDATES")
if uses != 3:
    sys.exit(f"candidates: {uses} uses of `> indexed::MAX_CANDIDATES`, not 3")
open(full, "w").write(text.replace("> indexed::MAX_CANDIDATES", "> indexed::max_candidates()"))
print(f"applied candidates bound to {uses} uses")
