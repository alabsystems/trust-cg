#!/usr/bin/env python3
"""OD-185 rule mutants: guard each `ArrayGep` rule of the x86-64 body theorem
behind `TCG_AGEP_MUTANT=<name>`, so one test build runs every mutant (the test
runner forwards TCG_* variables to the test binary). Restore the file with
`git checkout` afterwards; never commit it.

usage: mutate.py <worktree root>

Mutants (each disables or weakens one OD-185 rule; a control the rule exists
for must fail):
  source-refused        the source refuses `ArrayGep` over a non-private
                        address (the value rule disabled)
  source-unscaled       the source's element address is `base + index` (the
                        stride dropped)
  source-unindexed      the source's element address is `base` (the index
                        dropped)
  source-affine-off     the source states no affine value for an element
                        address
  any-index-width       the source admits an index of any type (the I64
                        index rule disabled)
  frame-refused         the source refuses a private base at a constant index
  frame-unscaled        a private base at a constant index is offset by the
                        index alone
  frame-wrapping        a private base's offset wraps instead of refusing an
                        overflow
  frame-variable-zero   a private base at a non-constant index is offset by
                        zero (the slice-17 refusal dropped)
  layout-unchecked      an element type outside the layout model or of size
                        zero has the selector's `Type::bytes` as its stride
  machine-frame-off     the machine refuses a scaled `lea` of a private
                        address (the frame rule disabled)
  machine-frame-unscaled the machine's scaled `lea` of a private address
                        ignores its scale
  machine-imul-fold-off a 64-bit `imul` of a constant is no constant
  machine-affine-off    a scaled `lea` at a constant index has no affine value
  stackaddr-hint-off    (OD-186) a slot's own address typed as an aggregate
                        is a pointer (the StackAddr arm disabled)
  gep-hint-aggregate    (OD-186) an element or field address typed as an
                        aggregate is that aggregate too
"""
import sys

root = sys.argv[1]
M = 'std::env::var("TCG_AGEP_MUTANT").is_ok_and(|mutant| mutant == "{}")'
OWNER = 'crates/trust-cg-verify/src/x86_source_bound_body.rs'
EDITS = [
    # source-refused
    (OWNER,
     '            L::ArrayGep { elem_ty } => {\n'
     '                let (base, index) = (inst.args[0], inst.args[1]);\n'
     '                if ty_of(&base)? != Carrier::I64 {\n',
     '            L::ArrayGep { elem_ty } => {\n'
     f'                if {M.format("source-refused")} {{\n'
     '                    return Err(outside("is ArrayGep (mutant)"));\n'
     '                }\n'
     '                let (base, index) = (inst.args[0], inst.args[1]);\n'
     '                if ty_of(&base)? != Carrier::I64 {\n'),
    # any-index-width
    (OWNER,
     '                if ty_of(&index)? != Carrier::I64 {\n'
     '                    return Err(outside(\n'
     '                        "indexes an array by a value other than an I64',
     f'                if ty_of(&index)? != Carrier::I64 && !{M.format("any-index-width")} {{\n'
     '                    return Err(outside(\n'
     '                        "indexes an array by a value other than an I64'),
    # source-affine-off
    (OWNER,
     '                let value_affine = match (affine_of(&base), constants.get(&index)) {\n'
     '                    (Some(base), Some(index)) => Some(base.combine(\n',
     '                let value_affine = match (affine_of(&base), constants.get(&index)) {\n'
     f'                    _ if {M.format("source-affine-off")} => None,\n'
     '                    (Some(base), Some(index)) => Some(base.combine(\n'),
    # source-unscaled / source-unindexed (the encoding)
    (OWNER,
     '                } => array_element_address(value(base), value(index), *stride),\n',
     f'                }} if {M.format("source-unscaled")} => value(base).bvadd(value(index)),\n'
     '                SourceOp::ArrayElement { base, .. }\n'
     f'                    if {M.format("source-unindexed")} =>\n'
     '                {\n'
     '                    value(base)\n'
     '                }\n'
     '                SourceOp::ArrayElement {\n'
     '                    base,\n'
     '                    index,\n'
     '                    stride,\n'
     '                } => array_element_address(value(base), value(index), *stride),\n'),
    # frame-refused / frame-unscaled / frame-wrapping / frame-variable-zero
    (OWNER,
     '                let index = constants\n'
     '                    .get(&index)\n'
     '                    .filter(|_| types.get(&index) == Some(&Carrier::I64))\n'
     '                    .ok_or_else(|| non_constant_offset(&index))?;\n'
     '                Some(\n'
     '                    i64::try_from(stride)\n'
     '                        .ok()\n'
     '                        .and_then(|stride| (*index as i64).checked_mul(stride))\n',
     f'                if {M.format("frame-refused")} {{\n'
     '                    return Err(outside("is ArrayGep of a frame (mutant)"));\n'
     '                }\n'
     f'                let stride = if {M.format("frame-unscaled")} {{ 1 }} else {{ stride }};\n'
     f'                let zero = 0u64;\n'
     '                let index = constants\n'
     '                    .get(&index)\n'
     '                    .filter(|_| types.get(&index) == Some(&Carrier::I64))\n'
     f'                    .or(Some(&zero).filter(|_| {M.format("frame-variable-zero")}))\n'
     '                    .ok_or_else(|| non_constant_offset(&index))?;\n'
     '                Some(\n'
     '                    i64::try_from(stride)\n'
     '                        .ok()\n'
     '                        .and_then(|stride| {\n'
     f'                            if {M.format("frame-wrapping")} {{\n'
     '                                Some((*index as i64).wrapping_mul(stride))\n'
     '                            } else {\n'
     '                                (*index as i64).checked_mul(stride)\n'
     '                            }\n'
     '                        })\n'),
    # layout-unchecked
    (OWNER,
     'fn array_element_stride(elem_ty: &Type) -> Option<u64> {\n',
     'fn array_element_stride(elem_ty: &Type) -> Option<u64> {\n'
     f'    if {M.format("layout-unchecked")} {{\n'
     '        return Some(u64::from(elem_ty.bytes()));\n'
     '    }\n'),
    # machine-frame-off / machine-frame-unscaled
    (OWNER,
     '                match (frame_of(base), constant(index)) {\n'
     '                    (Some(address), Some(k)) => Some(\n'
     '                        (k as i64)\n'
     '                            .checked_mul(i64::from(*scale))\n',
     '                match (frame_of(base), constant(index)) {\n'
     f'                    _ if {M.format("machine-frame-off")} => None,\n'
     '                    (Some(address), Some(k)) => Some(\n'
     '                        (k as i64)\n'
     f'                            .checked_mul(if {M.format("machine-frame-unscaled")} {{ 1 }} else {{ i64::from(*scale) }})\n'),
    # machine-imul-fold-off
    (OWNER,
     '                        BinaryOp::Mul if bits == 64 => lhs_affine\n',
     f'                        BinaryOp::Mul if bits == 64 && !{M.format("machine-imul-fold-off")} => lhs_affine\n'),
    # machine-affine-off
    (OWNER,
     '                        base_affine\n'
     '                            .zip(index_affine.and_then(Affine::as_constant))\n',
     '                        base_affine\n'
     f'                            .filter(|_| !{M.format("machine-affine-off")})\n'
     '                            .zip(index_affine.and_then(Affine::as_constant))\n'),
    # stackaddr-hint-off / gep-hint-aggregate
    (OWNER,
     '                L::StackAddr { .. } => Some(None),\n'
     '                _ => None,\n',
     f'                L::StackAddr {{ .. }} if !{M.format("stackaddr-hint-off")} => Some(None),\n'
     f'                L::StructGep {{ .. }} | L::ArrayGep {{ .. }}\n'
     f'                    if {M.format("gep-hint-aggregate")} =>\n'
     '                {\n'
     '                    Some(None)\n'
     '                }\n'
     '                _ => None,\n'),
]

for path, old, new in EDITS:
    full = f'{root}/{path}'
    text = open(full).read()
    count = text.count(old)
    if count != 1:
        sys.exit(f'{path}: expected one match, found {count}:\n{old}')
    open(full, 'w').write(text.replace(old, new))
print(f'applied {len(EDITS)} edits')
