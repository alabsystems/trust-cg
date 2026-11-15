#!/usr/bin/env python3
"""Slice-12 rule mutants: apply a patch that guards each slice-12 rule behind
`TCG_S12_MUTANT=<name>`, so one test build runs every mutant (the test runner
forwards TCG_* variables to the test binary). Restore the file with
`git checkout` afterwards; never commit it.

usage: mutate.py <x86_source_bound_body.rs>

Mutants (each disables or weakens one slice-12 rule; a control that the rule
exists for must fail):
  no-back-edge-relation   the cut-point relation is stated only on a
                          header's entry edge, not on its other edges
  no-entry-relation       the cut-point relation is not stated on a header's
                          entry edge
  no-header-bytes         no private byte becomes a header byte (the region
                          assumes every byte is the entry edge's)
  no-machine-byte-check   a private byte the machine's loop changes and the
                          source's does not is not refused
  no-written-roots        a machine register some edge into a header changes
                          is still assumed to hold its entry value
  no-param-taint          a header parameter an edge gives a tainted value
                          (slice 7's retention rule) is not tainted
  no-header-escape-union  a slot that escaped on an edge into a header other
                          than the entry edge is not escaped at the header
  join-escape-refusal     a join of paths on which different slots escaped is
                          refused again (slice 9's rule)
  parallel-edge-copies    the copies into a header's parameters read the
                          state before all of them, not in order
  no-edge-copy-temps      a temporary only later edge copies read is not one
                          of the edge's copies
  psabi-bool-32           a `bool` parameter's register is stated at 32 bits
                          under the psABI walk too
  full-width-relation     every parameter's register is stated at 64 bits
  pairing-copy-source     a parameter is paired with the register its entry
                          copy READS, not the one it writes
  no-entry-header-check   a loop headed by the entry block is admitted
  no-irreducible-check    a retreating edge whose target does not dominate
                          its source is taken as a natural loop's back edge
  one-round               the header assumptions stop after one round
  header-address          a stored private address (slice 13) in a byte the
                          loop changes is not refused (the merged tree)
  no-clean-registers      no header assumes a register zero above its
                          parameter (each keeps a free input there)
  no-upper-bound          a register is clean only bit by bit, never by its
                          value's bound (`(byte + 255) >> 8`)
"""
import sys

path = sys.argv[1]
text = open(path).read()
M = 'std::env::var("TCG_S12_MUTANT").is_ok_and(|mutant| mutant == "{}")'
EDITS = [
    # The relation on a header's edges.
    ('                if let (Some(loops), Some(loop_walks)) = (&body.loops, &walks.loops)\n'
     '                    && let Some(edge) = loops.regions[*index].cuts.get(&(block, *target))\n'
     '                {\n',
     '                if let (Some(loops), Some(loop_walks)) = (&body.loops, &walks.loops)\n'
     '                    && let Some(edge) = loops.regions[*index].cuts.get(&(block, *target))\n'
     f'                    && !({M.format("no-back-edge-relation")} && loops.headers[target].entry != (*index, block))\n'
     f'                    && !({M.format("no-entry-relation")} && loops.headers[target].entry == (*index, block))\n'
     '                {\n'),
    # Header bytes.
    ('            if all != header.bytes {\n',
     f'            if all != header.bytes && !{M.format("no-header-bytes")} {{\n'),
    # The machine's byte check.
    ('                        if !same_byte(&start.stack[slot][offset], byte) {\n',
     f'                        if !same_byte(&start.stack[slot][offset], byte) && !{M.format("no-machine-byte-check")} {{\n'),
    # Registers the loop writes.
    ('                    if !same_reg(start.regs.get(&root), exit.regs.get(&root)) {\n',
     f'                    if !same_reg(start.regs.get(&root), exit.regs.get(&root)) && !{M.format("no-written-roots")} {{\n'),
    # Tainted parameters.
    ('                    if edge.state.tainted.contains(value) {\n',
     f'                    if edge.state.tainted.contains(value) && !{M.format("no-param-taint")} {{\n'),
    # Escapes at a header.
    ('                    grown |= header.escaped.insert(*slot);\n',
     f'                    grown |= !{M.format("no-header-escape-union")} && header.escaped.insert(*slot);\n'),
    # Escapes at a join (the merged tree: slice 13's closed union).
    ('    let states: Vec<&AdmitState> = incoming.iter().map(|block| &exits[block]).collect();\n'
     '    let first = states[0];\n',
     '    let states: Vec<&AdmitState> = incoming.iter().map(|block| &exits[block]).collect();\n'
     '    let first = states[0];\n'
     f'    if {M.format("join-escape-refusal")} && states.iter().any(|state| state.escaped != first.escaped) {{\n'
     '        return Err(unsupported(X86BodyUnsupported::SourceDomain(format!(\n'
     '            "block {join:?} joins paths on which different private stack slots escaped"\n'
     '        ))));\n'
     '    }\n'),
    # A stored private address in a header byte (the merged tree).
    ('                        if byte.and_then(SlotByte::address).is_some() {\n',
     f'                        if byte.and_then(SlotByte::address).is_some() && !{M.format("header-address")} {{\n'),
    # Clean loop-carried registers (the merged tree).
    ('        let expr = if wide.contains(&i) {\n',
     f'        let expr = if wide.contains(&i) || {M.format("no-clean-registers")} {{\n'),
    # The value bound behind a clean register (the merged tree).
    ('                || (bits < 128 && upper_bound(expr, defs, 0) < 1u128 << bits)\n',
     f'                || (!{M.format("no-upper-bound")} && bits < 128 && upper_bound(expr, defs, 0) < 1u128 << bits)\n'),
    # Sequential edge copies.
    ('                    .map_or(inst.args[0], |(value, _)| *value);\n',
     f'                    .map_or(inst.args[0], |(value, _)| *value);\n'
     f'                let read = if {M.format("parallel-edge-copies")} {{ inst.args[0] }} else {{ read }};\n'),
    # Edge-copy temporaries.
    ('        let temporary = run_reads.get(result).copied().unwrap_or(0) > 0\n',
     f'        let temporary = !{M.format("no-edge-copy-temps")} && run_reads.get(result).copied().unwrap_or(0) > 0\n'),
    # A psABI bool's byte.
    ('        if self.value_bits == 1 && convention == BoolArguments::PsAbi {\n',
     f'        if {M.format("full-width-relation")} {{\n'
     '            64\n'
     f'        }} else if self.value_bits == 1 && convention == BoolArguments::PsAbi && !{M.format("psabi-bool-32")} {{\n'),
    # The pairing.
    ('                .and_then(|row| destination_reg(row.row.inst))\n',
     f'                .and_then(|row| if {M.format("pairing-copy-source")} {{ row.row.inst.operands.get(1).and_then(|o| gpr(o).or_else(|| xmm(o))) }} else {{ destination_reg(row.row.inst) }})\n'),
    # The entry header and irreducible checks.
    ('        if !dominates(*header, *latch) {\n',
     f'        if !dominates(*header, *latch) && !{M.format("no-irreducible-check")} {{\n'),
    ('        if *header == entry {\n',
     f'        if *header == entry && !{M.format("no-entry-header-check")} {{\n'),
    # One round.
    ('        if !grown {\n'
     '            return Ok(LoopBody {\n',
     f'        if !grown || {M.format("one-round")} {{\n'
     '            return Ok(LoopBody {\n'),
]
for old, new in EDITS:
    count = text.count(old)
    if count != 1:
        sys.exit(f'edit anchor found {count} times:\n{old}')
    text = text.replace(old, new)
open(path, 'w').write(text)
print(f'applied {len(EDITS)} edits')
