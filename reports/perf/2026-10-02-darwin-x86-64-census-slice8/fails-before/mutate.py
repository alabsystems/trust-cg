#!/usr/bin/env python3
"""Slice-8 rule mutants: apply a patch that guards each slice-8 rule behind
`TCG_S8_MUTANT=<name>`, so one test build runs every mutant (the test runner
forwards TCG_* variables to the test binary). Restore the file with
`git checkout` afterwards; never commit it.

usage: mutate.py <x86_source_bound_body.rs>

Mutants (each disables or weakens one slice-8 rule; a control that the rule
exists for must fail):
  no-entry-bytes       an aggregate parameter's copy holds no register bytes
                       (its bytes are the slot's initial bytes)
  no-result-bytes      an aggregate call result's slot holds no result bytes
  reversed-lanes       a parameter's eightbytes come from its registers in
                       reverse order (a wrong classification)
  wide-result-lanes    a callee defines every bit of RAX/RDX above an
                       aggregate eightbyte's bytes as zero
  short-return-lanes   a returned eightbyte is observed one byte short
  no-lane-metadata     the call row's argument registers are not compared
                       with the classification when an aggregate is passed
  no-slot-table        the machine slot table is not compared with the
                       source's plus the aggregate copies
  alias-zero-extends   a byte/word load into a physical 8/16-bit alias
                       zero-extends
  tied-as-move         a tied `shl`/`shr`/`or` computes `d = x`
  aggregate-as-pointer an aggregate-typed argument is passed as its address
  raw-bool-bytes       a `bool` read of a parameter's or result's byte is its
                       bit 0
  no-result-taint      an aggregate call result after an escape is not
                       escape-derived
"""
import sys

path = sys.argv[1]
text = open(path).read()
M = 'std::env::var("TCG_S8_MUTANT").is_ok_and(|mutant| mutant == "{}")'
EDITS = [
    # Parameters: the copy's bytes.
    ('                slot_bytes[*slot as usize][(lane.offset + byte) as usize] =\n'
     '                    Some(SlotByte::Entry { root: *root, byte });\n',
     '                slot_bytes[*slot as usize][(lane.offset + byte) as usize] =\n'
     f'                    (!{M.format("no-entry-bytes")}).then_some(SlotByte::Entry {{ root: *root, byte }});\n'),
    # Parameters: the registers in classification order.
    ('        params.push(Param {\n'
     '            abi,\n'
     '            roots: roots.to_vec(),\n'
     '        });\n',
     '        let mut roots = roots.to_vec();\n'
     f'        if {M.format("reversed-lanes")} && matches!(abi, ParamAbi::Aggregate {{ .. }}) {{ roots.reverse(); }}\n'
     '        params.push(Param { abi, roots });\n'),
    # Call results: the slot's bytes.
    ('                            slot_bytes[slot as usize][(eightbyte.offset + byte) as usize] =\n'
     '                                Some(SlotByte::Result {\n',
     '                            slot_bytes[slot as usize][(eightbyte.offset + byte) as usize] =\n'
     f'                                (!{M.format("no-result-bytes")}).then_some(SlotByte::Result {{\n'),
    # Call results: the defined bits.
    ('            defined_bits: lane.bits(),\n',
     f'            defined_bits: if {M.format("wide-result-lanes")} {{ 64 }} else {{ lane.bits() }},\n'),
    # Results: the observed bits.
    ('            Self::Eightbyte(lane) => lane.bits(),\n',
     f'            Self::Eightbyte(lane) if {M.format("short-return-lanes")} && lane.bytes > 1 => lane.bits() - 8,\n'
     '            Self::Eightbyte(lane) => lane.bits(),\n'),
    ('                        let source = source_eightbyte(bytes, &value, body_walks);\n',
     '                        let source = source_eightbyte(bytes, &value, body_walks);\n'
     '                        let source = fit(source.clone(), source.bv_width(), *bits);\n'),
    # Call rows: the declared argument registers.
    ('    if inst.call_arg_regs != expected_args {\n',
     '    if inst.call_arg_regs != expected_args\n'
     f'        && !({M.format("no-lane-metadata")} && call.args.iter().any(|arg| matches!(arg, CallArg::Aggregate(_))))\n'
     '    {\n'),
    # The machine slot table.
    ('    if machine.stack_slots != slots {\n',
     f'    if machine.stack_slots != slots && !{M.format("no-slot-table")} {{\n'),
    # Narrow physical alias loads.
    ('                4 => (value.zero_ext(32), None),\n'
     '                _ => (\n',
     '                4 => (value.zero_ext(32), None),\n'
     f'                _ if {M.format("alias-zero-extends")} && gpr(&inst.operands[0]).is_none() => (value.zero_ext(64 - width), None),\n'
     '                _ => (\n'),
    # Tied two-operand rows.
    ('    match inst.operands.as_slice() {\n'
     '        [destination, source] if tied => {\n'
     '            let mut three = inst.clone();\n'
     '            three.operands = vec![destination.clone(), destination.clone(), source.clone()];\n',
     '    match inst.operands.as_slice() {\n'
     f'        [destination, source] if tied && {M.format("tied-as-move")} => {{\n'
     '            let mut three = inst.clone();\n'
     '            three.opcode = if matches!(source, O::Imm(_)) { X86Opcode::MovRI } else { X86Opcode::MovRR };\n'
     '            three.flags = three.opcode.default_flags();\n'
     '            three.operands = vec![destination.clone(), source.clone()];\n'
     '            Some(three)\n'
     '        }\n'
     '        [destination, source] if tied => {\n'
     '            let mut three = inst.clone();\n'
     '            three.operands = vec![destination.clone(), destination.clone(), source.clone()];\n'),
    # By-value aggregate arguments.
    ('                    let arg = match (frame.get(value), aggregates.get(value)) {\n',
     '                    let arg = match (frame.get(value), aggregates.get(value)'
     f'.filter(|_| !{M.format("aggregate-as-pointer")})) {{\n'),
    # Bool reads of register bytes.
    ('                SourceOp::StackBytes(bytes) => definition\n'
     '                    .ty\n'
     '                    .loaded_value(source_bytes(bytes, &value, walks)),\n',
     f'                SourceOp::StackBytes(bytes) if {M.format("raw-bool-bytes")} && definition.ty == Carrier::B1\n'
     '                    && matches!(bytes.as_slice(), [(_, Some(SlotByte::Entry { .. } | SlotByte::Result { .. }))]) =>\n'
     '                {\n'
     '                    source_bytes(bytes, &value, walks).extract(0, 0)\n'
     '                }\n'
     '                SourceOp::StackBytes(bytes) => definition\n'
     '                    .ty\n'
     '                    .loaded_value(source_bytes(bytes, &value, walks)),\n'),
    # Result taint after an escape.
    ('                            Some(SlotByte::Result { site, .. }) => tainted_sites.contains(site),\n',
     '                            Some(SlotByte::Result { site, .. }) => {\n'
     f'                                tainted_sites.contains(site) && !{M.format("no-result-taint")}\n'
     '                            }\n'),
]
for old, new in EDITS:
    count = text.count(old)
    assert count == 1, (count, old)
    text = text.replace(old, new)
open(path, 'w').write(text)
print(f'applied {len(EDITS)} edits')
