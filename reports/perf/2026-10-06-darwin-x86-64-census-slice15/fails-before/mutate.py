#!/usr/bin/env python3
"""Slice-15 rule mutants: guard each slice-15 rule of the owner behind
`TCG_S15_MUTANT=<name>`, so one test build runs every mutant (the test runner
forwards TCG_* variables to the test binary). Restore the file with
`git checkout` afterwards; never commit it.

usage: mutate.py <x86_source_bound_body.rs> [<x86_64_isel.rs>]

Mutants (each disables or weakens one slice-15 rule; a control the rule
exists for must fail):
  neg-as-abs              `Fneg` clears the sign bit (source)
  f32-nan-constant        an f32 NaN constant is admitted (its narrowed bits)
  const-pool-any-size     a constant-pool entry of another size is read
  const-pool-any-row      a constant-pool entry named by any row is admitted
  pxor-as-and             `pxor` is modelled as an AND (machine)
  mixed-copy-zero-extends a mixed-width copy zero-extends its low 32 bits
  mixed-alu-full-width    a mixed-width ALU row computes all 64 bits
  bool-arg-byte           a `bool` argument is observed at 8 bits
  derived-load-unobserved a load through a derived address observes no slot
  derived-store-keeps     a store through a derived address leaves the
                          escaped slots' bytes as they were
  derived-escape-unchecked the escaped slots at a derived access are not
                          compared with the source's
  i128-stack-unaligned    an I128 on the stack is not 16-byte aligned
  i128-stack-swapped      an I128 stack parameter's halves are swapped
  selector-bool-copy      (with the selector path) the selector copies a
                          System V `bool` register parameter's 32 bits at
                          entry, as before slice 15, instead of `movzx` of
                          its low byte
"""
import sys

path = sys.argv[1]
text = open(path).read()
M = 'std::env::var("TCG_S15_MUTANT").is_ok_and(|mutant| mutant == "{}")'


def on(name):
    return M.format(name)


EDITS = [
    # neg-as-abs
    ("""            Self::Neg => value.bvxor(E::bv_const(sign, bits)),""",
     f"""            Self::Neg if !{on("neg-as-abs")} => value.bvxor(E::bv_const(sign, bits)),
            Self::Neg => value.bvand(E::bv_const(crate::smt::mask(u64::MAX, bits) & !sign, bits)),"""),
    # f32-nan-constant
    ("""        Carrier::F32 if !imm.is_nan() => Some(u64::from((imm as f32).to_bits())),""",
     f"""        Carrier::F32 if !imm.is_nan() || {on("f32-nan-constant")} => {{
            Some(u64::from((imm as f32).to_bits()))
        }}"""),
    # const-pool-any-size
    ("""                .is_none_or(|entry| entry.data.len() != bytes)""",
     f"""                .is_none_or(|entry| entry.data.len() != bytes && !{on("const-pool-any-size")})"""),
    # const-pool-any-row
    ("""                X86Opcode::MovsdRipRel => 8,
                _ => {
                    return Err(function(""",
     f"""                X86Opcode::MovsdRipRel => 8,
                _ if {on("const-pool-any-row")} => continue,
                _ => {{
                    return Err(function("""),
    # pxor-as-and
    ("""                    let value = if inst.opcode == X86Opcode::Pxor {
                        source.expr.bvxor(mask.expr)""",
     f"""                    let value = if inst.opcode == X86Opcode::Pxor && !{on("pxor-as-and")} {{
                        source.expr.bvxor(mask.expr)"""),
    # mixed-copy-zero-extends
    ("""                    let value = read_low(&inst.operands[1], 32)?;
                    (
                        names
                            .undefined(UndefinedSite::Row(row.ordinal), 32)
                            .concat(value),
                        None,
                    )
                }
                X86Opcode::MovRR => {""",
     f"""                    let value = read_low(&inst.operands[1], 32)?;
                    if {on("mixed-copy-zero-extends")} {{
                        (widen(value, 32), None)
                    }} else {{
                    (
                        names
                            .undefined(UndefinedSite::Row(row.ordinal), 32)
                            .concat(value),
                        None,
                    )
                    }}
                }}
                X86Opcode::MovRR => {{"""),
    # mixed-alu-full-width
    ("""                    let lhs = read_low(&inst.operands[1], 32)?;
                    let rhs = read_low(&inst.operands[2], 32)?;
                    let low = machine_binary(inst.opcode, 32, lhs, rhs);""",
     f"""                    if {on("mixed-alu-full-width")} {{
                        let lhs = root_of(&inst.operands[1])?.1.expr;
                        let rhs = root_of(&inst.operands[2])?.1.expr;
                        *flags = Flags::Unmodelled;
                        (machine_binary(inst.opcode, 64, lhs, rhs), None)
                    }} else {{
                    let lhs = read_low(&inst.operands[1], 32)?;
                    let rhs = read_low(&inst.operands[2], 32)?;
                    let low = machine_binary(inst.opcode, 32, lhs, rhs);"""),
    ("""                    *flags = Flags::Unmodelled;
                    (
                        names
                            .undefined(UndefinedSite::Row(row.ordinal), 32)
                            .concat(low),
                        None,
                    )
                }""",
     """                    *flags = Flags::Unmodelled;
                    (
                        names
                            .undefined(UndefinedSite::Row(row.ordinal), 32)
                            .concat(low),
                        None,
                    )
                    }
                }"""),
    # bool-arg-byte (machine register bits, source item)
    ("""            Self::Scalar(_, Carrier::I128) => vec![64, 64],
            Self::Scalar(_, ty) => vec![ty.return_bits()],""",
     f"""            Self::Scalar(_, Carrier::I128) => vec![64, 64],
            Self::Scalar(_, Carrier::B1) if {on("bool-arg-byte")} => vec![8],
            Self::Scalar(_, ty) => vec![ty.return_bits()],"""),
    ("""                        CallArg::Scalar(value, ty) => {
                            vec![(ty.abi_value(source_values[value].clone()), false)]
                        }
                        CallArg::Frame(..) => Vec::new(),""",
     f"""                        CallArg::Scalar(value, Carrier::B1) if {on("bool-arg-byte")} => {{
                            vec![(fit(source_values[value].clone(), 1, 8), false)]
                        }}
                        CallArg::Scalar(value, ty) => {{
                            vec![(ty.abi_value(source_values[value].clone()), false)]
                        }}
                        CallArg::Frame(..) => Vec::new(),"""),
    # derived-load-unobserved
    ("""                        let derived = tainted.contains(&inst.args[0]);""",
     f"""                        let derived =
                            tainted.contains(&inst.args[0]) && !{on("derived-load-unobserved")};"""),
    # derived-store-keeps
    ("""                            let store_site = derived
                                .then(|| sites.access_store(block_id, index, part.unwrap_or(0)));""",
     f"""                            let store_site = (derived && !{on("derived-store-keeps")})
                                .then(|| sites.access_store(block_id, index, part.unwrap_or(0)));"""),
    # derived-escape-unchecked
    ("""                            if !escaped
                                .iter()
                                .copied()
                                .eq(reads.iter().map(|(slot, _)| *slot))
                            {
                                return Err(unsupported(X86BodyUnsupported::MachineRow {
                                    row: row.ordinal,
                                    detail: format!(
                                        "the private stack slots escaped at access {access} \\""",
     f"""                            if !escaped
                                .iter()
                                .copied()
                                .eq(reads.iter().map(|(slot, _)| *slot))
                                && !{on("derived-escape-unchecked")}
                            {{
                                return Err(unsupported(X86BodyUnsupported::MachineRow {{
                                    row: row.ordinal,
                                    detail: format!(
                                        "the private stack slots escaped at access {{access}} \\"""),
    # i128-stack-unaligned
    ("""                offset = (offset + 15) & !15;""",
     f"""                if !{on("i128-stack-unaligned")} {{
                    offset = (offset + 15) & !15;
                }}"""),
    ("""                    let disp = (stack + 15) & !15;""",
     f"""                    let disp = if {on("i128-stack-unaligned")} {{
                        stack
                    }} else {{
                        (stack + 15) & !15
                    }};"""),
    # i128-stack-swapped
    ("""                [low_disp, high_disp] => E::var(stack_parameter_name(*high_disp), 64)
                    .concat(E::var(stack_parameter_name(*low_disp), 64)),""",
     f"""                [low_disp, high_disp] if {on("i128-stack-swapped")} => {{
                    E::var(stack_parameter_name(*low_disp), 64)
                        .concat(E::var(stack_parameter_name(*high_disp), 64))
                }}
                [low_disp, high_disp] => E::var(stack_parameter_name(*high_disp), 64)
                    .concat(E::var(stack_parameter_name(*low_disp), 64)),"""),
]

for old, new in EDITS:
    count = text.count(old)
    if count != 1:
        sys.exit(f"anchor found {count} times:\n{old}")
    text = text.replace(old, new)
open(path, "w").write(text)
print(f"applied {len(EDITS)} edits")

if len(sys.argv) > 2:
    selector = sys.argv[2]
    text = open(selector).read()
    old = """                let opcode = if *ty == Type::B1 && self.abi == X86CallAbi::SystemV {"""
    new = f"""                let opcode = if *ty == Type::B1
                    && self.abi == X86CallAbi::SystemV
                    && !{on("selector-bool-copy")}
                {{"""
    if text.count(old) != 1:
        sys.exit(f"selector anchor found {text.count(old)} times")
    open(selector, "w").write(text.replace(old, new))
    print("applied the selector edit")
