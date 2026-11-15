#!/usr/bin/env python3
"""Slice-14 rule mutants: guard each slice-14 rule behind
`TCG_S14_MUTANT=<name>` in the owner, so one test build runs every mutant
(scripts/trust_cargo.sh forwards TCG_* variables to the test binary).
Restore the file with `git checkout` afterwards; never commit it.

usage: mutate.py <x86_source_bound_body.rs>

Mutants (each disables or weakens one slice-14 rule; a control that the rule
exists for must fail):
  no-undefined-stop     an undefined division adds no stop (the source runs on)
  no-constant-fold      a division by a nonzero constant adds a stop too
  path-insensitive-stop every unit is waived by every unit's undefined
                        division (the premise over the function, not the path)
  no-join-stop          a DAG join starts with no stop, whatever its incoming
                        edges stopped with
  no-guard-claim        a firing guard asks nothing of the machine
  fault-traps           a #DE counts as the trap a guard asks for
  no-liveness           the machine may stop where the source has not
  no-division-fault     `div`/`idiv` never raises #DE
  canonical-always      every dividend is taken as the extension of its low half
  cqo-zero              `cqo`/`cdq` define RDX as zero
  div-swapped           `div`/`idiv` write the remainder to RAX and the
                        quotient to RDX
  xor-reads             `xor r, r, r` reads `r` (no zeroing idiom)
  refuse-shared-targets a switch with two edges to one block is refused again
  first-case-only       a shared target's edge tests only its first case
  first-route-only      a shared target's machine literal is its first route's
  table-any-index       the dispatch reaches a target at any index of the table
  table-index-shift     the dispatch reads the index of a target one too high
  dispatch-unrecognized no dispatch block is recognized (jump tables refused)
  pair-always           a machine division is restated as the source's even where
                        their operands differ
  pow2-division-shift   a division by 2^k is spelled as a shift by k + 1
  pow2-product-shift    a `mul` by 2^j has the high half shifted by width - j - 1
"""
import sys

path = sys.argv[1]
text = open(path).read()
M = 'std::env::var("TCG_S14_MUTANT").is_ok_and(|mutant| mutant == "{}")'
EDITS = [
    ('                        kind: StopKind::Undefined { signed, lhs, rhs },\n'
     '                        block: block_id,\n'
     '                        index,\n'
     '                    });\n',
     '                        kind: StopKind::Undefined { signed, lhs, rhs },\n'
     '                        block: block_id,\n'
     '                        index,\n'
     '                    });\n'
     f'                    if {M.format("no-undefined-stop")} {{\n'
     '                        stops.pop();\n'
     '                    }\n'),
    ('                let defined = constants.get(&rhs).is_some_and(|k| {\n',
     f'                let defined = !{M.format("no-constant-fold")} && constants.get(&rhs).is_some_and(|k| {{\n'),
    ('    for names in std::iter::once(&walks.psabi).chain(walks.clean.as_ref()) {\n'
     '        // Slice 14: a canonical division\'s value restated through the\n',
     f'    if {M.format("path-insensitive-stop")} {{\n'
     '        let any = unit_stops\n'
     '            .iter()\n'
     '            .map(|unit| unit.before_event.last().unwrap().clone())\n'
     '            .fold(bit_zero(), bit_or);\n'
     '        for unit in &mut unit_stops {\n'
     '            for stop in &mut unit.before_event {\n'
     '                *stop = bit_or(stop.clone(), any.clone());\n'
     '            }\n'
     '        }\n'
     '    }\n'
     '    for names in std::iter::once(&walks.psabi).chain(walks.clean.as_ref()) {\n'
     '        // Slice 14: a canonical division\'s value restated through the\n'),
    ('                        if terms.iter().all(|term| *term == terms[0]) {\n'
     '                            terms[0].clone()\n',
     f'                        if {M.format("no-join-stop")} {{\n'
     '                            bit_zero()\n'
     '                        } else if terms.iter().all(|term| *term == terms[0]) {\n'
     '                            terms[0].clone()\n'),
    ('        for (before, fire, event) in &stops.guards {\n',
     f'        for (before, fire, event) in stops.guards.iter().filter(|_| !{M.format("no-guard-claim")}) {{\n'),
    ('                    let next = bit_or(stopped.clone(), bit_of(fault));\n',
     f'                    if {M.format("fault-traps")} {{\n'
     '                        *trapped = bit_or(trapped.clone(), bit_of(fault.clone()));\n'
     '                    }\n'
     f'                    let next = if {M.format("no-division-fault")} {{\n'
     '                        stopped.clone()\n'
     '                    } else {\n'
     '                        bit_or(stopped.clone(), bit_of(fault))\n'
     '                    };\n'),
    ('            if *stopped == bit_zero() {\n'
     '                continue;\n'
     '            }\n',
     f'            if *stopped == bit_zero() || {M.format("no-liveness")} {{\n'
     '                continue;\n'
     '            }\n'),
    ('    let canonical = high_definition.is_some_and(',
     f'    let canonical = {M.format("canonical-always")} || high_definition.is_some_and('),
    ('                    let name = names.define(row.ordinal, widen(sign_of(value), bits));\n',
     f'                    let value = if {M.format("cqo-zero")} {{\n'
     '                        E::bv_const(0, bits)\n'
     '                    } else {\n'
     '                        sign_of(value)\n'
     '                    };\n'
     '                    let name = names.define(row.ordinal, widen(value, bits));\n'),
    ('                    for (root, value) in [(RAX, quotient), (RDX, remainder)] {\n',
     f'                    let (quotient, remainder) = if {M.format("div-swapped")} {{\n'
     '                        (remainder, quotient)\n'
     '                    } else {\n'
     '                        (quotient, remainder)\n'
     '                    };\n'
     '                    for (root, value) in [(RAX, quotient), (RDX, remainder)] {\n'),
    ('                X86Opcode::XorRR\n'
     '                    if inst.operands.len() == 3\n',
     '                X86Opcode::XorRR\n'
     f'                    if !{M.format("xor-reads")}\n'
     '                        && inst.operands.len() == 3\n'),
    ('                let targets = switch_targets(cases, *default);\n',
     '                let targets = switch_targets(cases, *default);\n'
     f'                if {M.format("refuse-shared-targets")} && targets.len() != cases.len() + 1 {{\n'
     '                    return Err(shape(format!(\n'
     '                        "block {id:?} ends in a Switch with two edges to one block"\n'
     '                    )));\n'
     '                }\n'),
    ('                cases\n'
     '                    .iter()\n'
     '                    .map(|pattern| equals(*pattern))\n'
     '                    .chain(default)\n',
     '                cases\n'
     '                    .iter()\n'
     f'                    .take(if {M.format("first-case-only")} {{ 1 }} else {{ usize::MAX }})\n'
     '                    .map(|pattern| equals(*pattern))\n'
     f'                    .chain(default.filter(|_| !{M.format("first-case-only")}))\n'),
    ('    let taken = conditions\n'
     '        .iter()\n',
     '    let taken = conditions\n'
     '        .iter()\n'
     f'        .take(if {M.format("first-route-only")} {{ 1 }} else {{ usize::MAX }})\n'),
    ('                        .filter(|(_, block)| **block == to)\n'
     '                        .map(|(i, _)| index.clone().eq_expr(E::bv_const(i as u64, 64)))\n',
     f'                        .filter(|(_, block)| {M.format("table-any-index")} || **block == to)\n'
     '                        .map(|(i, _)| {\n'
     f'                            let shift = u64::from({M.format("table-index-shift")});\n'
     '                            index.clone().eq_expr(E::bv_const(i as u64 + shift, 64))\n'
     '                        })\n'),
    ('fn dispatch_blocks(machine: &X86ISelFunction) -> HashMap<Block, u32> {\n'
     '    let mut dispatch = HashMap::new();\n',
     'fn dispatch_blocks(machine: &X86ISelFunction) -> HashMap<Block, u32> {\n'
     '    let mut dispatch = HashMap::new();\n'
     f'    if {M.format("dispatch-unrecognized")} {{\n'
     '        return dispatch;\n'
     '    }\n'),
    ('            E::ite(condition, widen(value, division.bits), original.clone()),\n',
     f'            if {M.format("pair-always")} {{\n'
     '                widen(value, division.bits)\n'
     '            } else {\n'
     '                E::ite(condition, widen(value, division.bits), original.clone())\n'
     '            },\n'),
    ('        lhs.bvlshr(E::bv_const(u64::from(k.trailing_zeros()), bits))\n',
     '        lhs.bvlshr(E::bv_const(\n'
     f'            u64::from(k.trailing_zeros()) + u64::from({M.format("pow2-division-shift")}),\n'
     '            bits,\n'
     '        ))\n'),
    ('            value.bvlshr(E::bv_const(u64::from(bits) - j, bits)),\n',
     '            value.bvlshr(E::bv_const(\n'
     f'                u64::from(bits) - j - u64::from({M.format("pow2-product-shift")}),\n'
     '                bits,\n'
     '            )),\n'),
]
for old, new in EDITS:
    count = text.count(old)
    if count != 1:
        sys.exit(f"anchor found {count} times:\n{old}")
    text = text.replace(old, new)
open(path, "w").write(text)
print(f"applied {len(EDITS)} mutant guards")
