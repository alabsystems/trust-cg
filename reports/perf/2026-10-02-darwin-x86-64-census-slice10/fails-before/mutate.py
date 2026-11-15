#!/usr/bin/env python3
"""Slice-10 rule mutants: apply a patch that guards each slice-10 rule behind
`TCG_S10_MUTANT=<name>`, so one test build runs every mutant (the test runner
forwards TCG_* variables to the test binary). Restore the file with
`git checkout` afterwards; never commit it.

usage: mutate.py <x86_source_bound_body.rs> [<x86_64_eflags.rs>]

Mutants (each disables or weakens one slice-10 rule; a control that the rule
exists for must fail):
  add-flags-unmodelled  `add` writes no flags a reader may use
  add-carry-as-overflow `add` sets CF to the signed overflow
  sub-borrow-inverted   `sub` sets CF to "no borrow"
  imul-flags-defined    `imul` defines SF, ZF and PF (as its CF)
  mul-high-as-low       `mul` writes the low half to RDX too
  mul-no-overflow       `mul` sets CF = OF = 0
  overflow-unsigned     checked arithmetic's overflow is the unsigned one,
                        whatever the signedness
  overflow-narrow-mul   a product's exact width is the operand width + 1
  popcount-low-byte     population count counts the low byte only (both
                        sides: only the hardware-agreement control sees it)
  tied-and-as-move      a tied `and d, imm` computes `d = imm`
  callee-not-observed   an indirect call's function pointer is not observed
  call-kind-unpaired    a `call r64` pairs with a direct source call too
  narrow-checked        checked arithmetic of I8/I16/I32 is admitted
  shift-count-unmasked  a shift by CL uses all of RCX's low byte
  source-shift-unmasked a variable source shift does not reduce its amount
"""
import sys

path = sys.argv[1]
text = open(path).read()
M = 'std::env::var("TCG_S10_MUTANT").is_ok_and(|mutant| mutant == "{}")'
EDITS = [
    ('                        X86Opcode::AddRR => {\n'
     '                            flags = Flags::Alu(AluFlags::add(lhs.clone(), rhs.clone(), bits));\n'
     '                        }\n',
     f'                        X86Opcode::AddRR if {M.format("add-flags-unmodelled")} => {{}}\n'
     '                        X86Opcode::AddRR => {\n'
     '                            flags = Flags::Alu(AluFlags::add(lhs.clone(), rhs.clone(), bits));\n'
     f'                            if {M.format("add-carry-as-overflow")} && let Flags::Alu(alu) = &mut flags {{ alu.cf = alu.of.clone(); }}\n'
     '                        }\n'),
    ('                        X86Opcode::SubRR => {\n'
     '                            flags = Flags::Alu(AluFlags::sub(lhs.clone(), rhs.clone(), bits));\n'
     '                        }\n',
     '                        X86Opcode::SubRR => {\n'
     '                            flags = Flags::Alu(AluFlags::sub(lhs.clone(), rhs.clone(), bits));\n'
     f'                            if {M.format("sub-borrow-inverted")} && let Flags::Alu(alu) = &mut flags {{ alu.cf = alu.cf.clone().map(E::not_expr); }}\n'
     '                        }\n'),
    ('        let overflow = truncated.sign_ext(bits).eq_expr(full).not_expr();\n'
     '        Self::carry_and_overflow(overflow)\n',
     '        let overflow = truncated.sign_ext(bits).eq_expr(full).not_expr();\n'
     f'        if {M.format("imul-flags-defined")} {{\n'
     '            return Self { cf: Some(overflow.clone()), zf: Some(overflow.clone()), sf: Some(overflow.clone()), of: Some(overflow.clone()), pf: Some(overflow) };\n'
     '        }\n'
     '        Self::carry_and_overflow(overflow)\n'),
    ('                    for (root, value) in [(RAX, product), (RDX, high)] {\n',
     f'                    let high = if {M.format("mul-high-as-low")} {{ product.clone() }} else {{ high }};\n'
     '                    for (root, value) in [(RAX, product), (RDX, high)] {\n'),
    ('                    flags = Flags::Alu(AluFlags::carry_and_overflow(\n'
     '                        high.clone().eq_expr(E::bv_const(0, bits)).not_expr(),\n'
     '                    ));\n',
     '                    flags = Flags::Alu(AluFlags::carry_and_overflow(\n'
     f'                        if {M.format("mul-no-overflow")} {{ E::bool_const(false) }} else {{ high.clone().eq_expr(E::bv_const(0, bits)).not_expr() }},\n'
     '                    ));\n'),
    ('    fn signed(self) -> bool {\n'
     '        matches!(self, Self::Sadd | Self::Ssub | Self::Smul)\n',
     '    fn signed(self) -> bool {\n'
     f'        !{M.format("overflow-unsigned")} && matches!(self, Self::Sadd | Self::Ssub | Self::Smul)\n'),
    ('        let extra = match self.binary() {\n'
     '            BinaryOp::Mul => bits,\n',
     '        let extra = match self.binary() {\n'
     f'            BinaryOp::Mul if !{M.format("overflow-narrow-mul")} => bits,\n'),
    ('    let mut terms: Vec<E> = (0..bits)\n',
     f'    let mut terms: Vec<E> = (0..if {M.format("popcount-low-byte")} {{ 8 }} else {{ bits }})\n'),
    ('        [destination, source] if tied => {\n'
     '            let mut three = inst.clone();\n'
     '            three.operands = vec![destination.clone(), destination.clone(), source.clone()];\n',
     f'        [destination, source] if tied && inst.opcode == X86Opcode::AndRI && {M.format("tied-and-as-move")} => {{\n'
     '            let mut two = inst.clone();\n'
     '            two.opcode = X86Opcode::MovRI;\n'
     '            two.flags = two.opcode.default_flags();\n'
     '            two.operands = vec![destination.clone(), source.clone()];\n'
     '            Some(two)\n'
     '        }\n'
     '        [destination, source] if tied => {\n'
     '            let mut three = inst.clone();\n'
     '            three.operands = vec![destination.clone(), destination.clone(), source.clone()];\n'),
    ('                    let callee = call\n'
     '                        .callee\n'
     '                        .map(|callee| (source_values[&callee].clone(), false));\n',
     '                    let callee = call\n'
     '                        .callee\n'
     f'                        .filter(|_| !{M.format("callee-not-observed")})\n'
     '                        .map(|callee| (source_values[&callee].clone(), false));\n'),
    ('                        call.callee\n'
     '                            .iter()\n'
     '                            .chain(&call.args)\n',
     '                        call.callee\n'
     '                            .iter()\n'
     f'                            .filter(|_| !{M.format("callee-not-observed")})\n'
     '                            .chain(&call.args)\n'),
    ('        (_, None) => {\n'
     '            return Err(mismatch(X86BodyMismatch::CallTarget {\n'
     '                row,\n'
     '                expected: describe(&call.name, call.exact_module),\n'
     '                found: indirect,\n'
     '            }));\n'
     '        }\n',
     f'        (_, None) if {M.format("call-kind-unpaired")} => {{}}\n'
     '        (_, None) => {\n'
     '            return Err(mismatch(X86BodyMismatch::CallTarget {\n'
     '                row,\n'
     '                expected: describe(&call.name, call.exact_module),\n'
     '                found: indirect,\n'
     '            }));\n'
     '        }\n'),
    ('            if ty != Carrier::I64 {\n'
     '                return Err(outside("is checked arithmetic on a carrier other than I64"));\n',
     f'            if ty != Carrier::I64 && !{M.format("narrow-checked")} {{\n'
     '                return Err(outside("is checked arithmetic on a carrier other than I64"));\n'),
    ('                    (widen(shift_modulo_width(op, value, count), bits), None)\n',
     f'                    if {M.format("shift-count-unmasked")} {{ (widen(op.apply(value, count.zero_ext(bits - 8)), bits), None) }} else {{\n'
     '                    (widen(shift_modulo_width(op, value, count), bits), None)\n'
     '                    }\n'),
    ('                SourceOp::VariableShift(op, v, amount) => {\n'
     '                    shift_modulo_width(*op, value(v), value(amount))\n'
     '                }\n',
     f'                SourceOp::VariableShift(op, v, amount) if {M.format("source-shift-unmasked")} => op.apply(value(v), value(amount)),\n'
     '                SourceOp::VariableShift(op, v, amount) => {\n'
     '                    shift_modulo_width(*op, value(v), value(amount))\n'
     '                }\n'),
]
for old, new in EDITS:
    count = text.count(old)
    assert count == 1, (count, old)
    text = text.replace(old, new)
open(path, "w").write(text)
print(f"applied {len(EDITS)} edits to {path}")
