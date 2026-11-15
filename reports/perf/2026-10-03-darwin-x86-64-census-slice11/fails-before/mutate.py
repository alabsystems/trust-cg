#!/usr/bin/env python3
"""Slice-11 rule mutants: guard each slice-11 rule of the owner behind
`TCG_S11_MUTANT=<name>`, so one test build runs every mutant (the test runner
forwards TCG_* variables to the test binary). Restore the file with
`git checkout` afterwards; never commit it.

usage: mutate.py <x86_source_bound_body.rs>

Mutants (each disables or weakens one slice-11 rule; a control that the rule
exists for must fail):
  param-halves-swapped    an i128 parameter is (low register, high register)
                          read the other way round
  result-halves-swapped   an i128 result's high half is observed in RAX
  arg-halves-swapped      an i128 call argument's halves observed swapped
  call-result-swapped     an i128 call result is (RAX, RDX) the other way
  access-no-offset        an i128 access's high half at the address itself
  store-low-twice         an i128 store's high half writes the low half
  iconst-zero-extended    an I128 Iconst's high half is zero
  iconst128-swapped       Iconst128's halves swapped
  adc-no-carry            adc and sbb ignore CF
  sbb-adds-carry          sbb adds CF
  carry-from-anything     adc/sbb read CF as 0 where the flags are undefined
                          or unmodelled
  cl-shift-reads-zero     a one-operand shift by CL shifts 0, not its
                          destination
  cl-constant-unmasked    a known CL count is not masked to the width
  sse-one-class           floats take integer argument registers
  sse-result-in-rax       a float result lane is in RAX/RDX
  movss-keeps-upper       movss d, s keeps d's bits above 32 (as defined)
  xmm-survive-calls       a call leaves the SSE registers defined
  i128-variable-shift     a variable shift of an I128 is admitted
  ashr-as-logical         a constant arithmetic shift spelled as a logical one
  wide-names              a 128-bit source value is one name
  i128-field-refused      an aggregate's I128 field is refused
"""
import sys

path = sys.argv[1]
text = open(path).read()
M = 'std::env::var("TCG_S11_MUTANT").is_ok_and(|mutant| mutant == "{}")'


def on(name):
    return M.format(name)


EDITS = [
    # param-halves-swapped
    ('                E::var(entry_name(*high_root), 64).concat(E::var(entry_name(*low_root), 64))\n',
     f'                if {on("param-halves-swapped")} {{ E::var(entry_name(*low_root), 64).concat(E::var(entry_name(*high_root), 64)) }} else {{\n'
     '                E::var(entry_name(*high_root), 64).concat(E::var(entry_name(*low_root), 64))\n'
     '                }\n'),
    # result-halves-swapped
    ('        [Type::I128] => vec![ReturnLane::Half(0), ReturnLane::Half(1)],\n',
     f'        [Type::I128] if {on("result-halves-swapped")} => vec![ReturnLane::Half(1), ReturnLane::Half(0)],\n'
     '        [Type::I128] => vec![ReturnLane::Half(0), ReturnLane::Half(1)],\n'),
    ('                } else if let [ReturnLane::Half(0), ReturnLane::Half(1)] = return_tys.as_slice() {\n',
     '                } else if let [ReturnLane::Half(a), ReturnLane::Half(b)] = return_tys.as_slice() {\n'),
    ('                    returned = vec![Returned::Half(value, 0), Returned::Half(value, 1)];\n',
     '                    returned = vec![Returned::Half(value, *a), Returned::Half(value, *b)];\n'),
    # arg-halves-swapped
    ('                                (wide.clone().extract(63, 0), false),\n'
     '                                (wide.extract(127, 64), false),\n',
     f'                                (if {on("arg-halves-swapped")} {{ wide.clone().extract(127, 64) }} else {{ wide.clone().extract(63, 0) }}, false),\n'
     f'                                (if {on("arg-halves-swapped")} {{ wide.extract(63, 0) }} else {{ wide.extract(127, 64) }}, false),\n'),
    # call-result-swapped
    ('                    E::var(call_result_name(*call, 1), 64)\n'
     '                        .concat(E::var(call_result_name(*call, 0), 64))\n',
     f'                    if {on("call-result-swapped")} {{ E::var(call_result_name(*call, 0), 64).concat(E::var(call_result_name(*call, 1), 64)) }} else {{\n'
     '                    E::var(call_result_name(*call, 1), 64)\n'
     '                        .concat(E::var(call_result_name(*call, 0), 64))\n'
     '                    }\n'),
    # access-no-offset
    ('                        offset => address.bvadd(E::bv_const(offset, 64)),\n',
     f'                        _ if {on("access-no-offset")} => address,\n'
     '                        offset => address.bvadd(E::bv_const(offset, 64)),\n'),
    # store-low-twice
    ('                            Some(half) => stored.extract(64 * half + 63, 64 * half),\n',
     f'                            Some(_) if {on("store-low-twice")} => stored.extract(63, 0),\n'
     '                            Some(half) => stored.extract(64 * half + 63, 64 * half),\n'),
    # iconst-zero-extended, iconst128-swapped
    ('                    L::Iconst128 { lo, hi } => (*lo as u64, *hi as u64),\n'
     '                    _ => (*imm as u64, if *imm < 0 { u64::MAX } else { 0 }),\n',
     f'                    L::Iconst128 {{ lo, hi }} if {on("iconst128-swapped")} => (*hi as u64, *lo as u64),\n'
     '                    L::Iconst128 { lo, hi } => (*lo as u64, *hi as u64),\n'
     f'                    _ if {on("iconst-zero-extended")} => (*imm as u64, 0),\n'
     '                    _ => (*imm as u64, if *imm < 0 { u64::MAX } else { 0 }),\n'),
    # adc-no-carry, sbb-adds-carry, carry-from-anything
    ('                    let carry = E::ite(\n'
     '                        flags.condition(trust_cg_ir::X86CondCode::B, row.ordinal, inst.opcode)?,\n'
     '                        E::bv_const(1, bits),\n'
     '                        E::bv_const(0, bits),\n'
     '                    );\n'
     '                    let result = if inst.opcode == X86Opcode::AdcRR {\n'
     '                        lhs.bvadd(rhs).bvadd(carry)\n',
     '                    let cf = match flags.condition(trust_cg_ir::X86CondCode::B, row.ordinal, inst.opcode) {\n'
     f'                        Err(_) if {on("carry-from-anything")} => E::bool_const(false),\n'
     '                        other => other?,\n'
     '                    };\n'
     '                    let carry = E::ite(\n'
     '                        cf,\n'
     '                        E::bv_const(1, bits),\n'
     '                        E::bv_const(0, bits),\n'
     '                    );\n'
     f'                    let carry = if {on("adc-no-carry")} {{ E::bv_const(0, bits) }} else {{ carry }};\n'
     '                    let result = if inst.opcode == X86Opcode::AdcRR {\n'
     '                        lhs.bvadd(rhs).bvadd(carry)\n'),
    ('                        lhs.bvsub(rhs.bvadd(carry))\n',
     f'                        if {on("sbb-adds-carry")} {{ lhs.bvsub(rhs).bvadd(carry) }} else {{ lhs.bvsub(rhs.bvadd(carry)) }}\n'),
    # cl-shift-reads-zero
    ('        [destination] if tied_by_cl => {\n'
     '            let mut two = inst.clone();\n'
     '            two.operands = vec![destination.clone(), destination.clone()];\n',
     '        [destination] if tied_by_cl => {\n'
     '            let mut two = inst.clone();\n'
     '            two.operands = vec![destination.clone(), destination.clone()];\n'
     f'            if {on("cl-shift-reads-zero")} {{ two.opcode = X86Opcode::MovRI; two.flags = two.opcode.default_flags(); two.operands = vec![destination.clone(), O::Imm(0)]; }}\n'),
    # cl-constant-unmasked
    ('                            op.by_constant(value, (constant & u64::from(bits - 1)) as u32)\n',
     f'                            if {on("cl-constant-unmasked")} {{ op.apply(value, E::bv_const(constant & 0xff, bits)) }} else {{\n'
     '                            op.by_constant(value, (constant & u64::from(bits - 1)) as u32)\n'
     '                            }\n'),
    # sse-one-class
    ('            let (next, table): (&mut usize, &[u16]) = if is_sse {\n',
     f'            let (next, table): (&mut usize, &[u16]) = if is_sse && !{on("sse-one-class")} {{\n'),
    # sse-result-in-rax
    ('fn result_roots(lanes: impl IntoIterator<Item = bool>) -> Option<Vec<u16>> {\n',
     'fn result_roots(lanes: impl IntoIterator<Item = bool>) -> Option<Vec<u16>> {\n'
     f'    let mutant = {on("sse-result-in-rax")};\n'
     '    let lanes: Vec<bool> = lanes.into_iter().map(|sse| sse && !mutant).collect();\n'),
    # movss-keeps-upper
    ('                X86Opcode::MovssRR => {\n'
     '                    let value = read_low(&inst.operands[1], 32)?;\n',
     f'                X86Opcode::MovssRR if {on("movss-keeps-upper")} => {{\n'
     '                    let value = read_low(&inst.operands[1], 32)?;\n'
     '                    let kept = root_of(&inst.operands[0])\n'
     '                        .map(|(_, slot)| slot.expr.extract(63, 32))\n'
     '                        .unwrap_or(E::bv_const(0, 32));\n'
     '                    (kept.concat(value), None)\n'
     '                }\n'
     '                X86Opcode::MovssRR => {\n'
     '                    let value = read_low(&inst.operands[1], 32)?;\n'),
    # xmm-survive-calls
    ('                    for root in SYSV_CALLER_SAVED_ROOTS.into_iter().chain(XMM_ROOTS) {\n',
     f'                    for root in SYSV_CALLER_SAVED_ROOTS.into_iter().chain(XMM_ROOTS.filter(|_| !{on("xmm-survive-calls")})) {{\n'),
    # i128-variable-shift
    ('                        if ty == Carrier::I128 {\n'
     '                            return Err(outside(\n'
     '                                "shifts an i128 by a non-constant amount',
     f'                        if ty == Carrier::I128 && !{on("i128-variable-shift")} {{\n'
     '                            return Err(outside(\n'
     '                                "shifts an i128 by a non-constant amount'),
    # ashr-as-logical
    ('                value.extract(bits - 1, amount).sign_ext(amount)\n',
     f'                if {on("ashr-as-logical")} {{ value.extract(bits - 1, amount).zero_ext(amount) }} else {{\n'
     '                value.extract(bits - 1, amount).sign_ext(amount)\n'
     '                }\n'),
    # wide-names
    ('    match expr.bv_width() {\n'
     '        128 => {\n',
     '    match expr.bv_width() {\n'
     f'        128 if !{on("wide-names")} => {{\n'),
    # i128-field-refused
    ('            Type::I128 => {\n'
     '                if base != 0 {\n',
     '            Type::I128 => {\n'
     f'                if base != 0 || {on("i128-field-refused")} {{\n'),
]
for old, new in EDITS:
    count = text.count(old)
    if count != 1:
        sys.exit(f"{count} occurrences of {old[:90]!r}")
    text = text.replace(old, new)
open(path, "w").write(text)
print(f"applied {len(EDITS)} mutant guards")
