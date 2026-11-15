//! A bounded scalar FP asm grammar (AArch64 Linux and Darwin). Unknown
//! instructions, extra clobbers and control flow retain the MIR refusal; no
//! function-name recognition is used.
use super::*;
use rustc_ast::{InlineAsmOptions, InlineAsmTemplatePiece};
use rustc_target::asm::{AArch64InlineAsmRegClass, InlineAsmRegClass, InlineAsmRegOrRegClass};
use trust_cg_lower::aarch64_fp_dialect::{self, Operation};

struct Plan {
    op: Operation,
    width: TrustIrTy,
    output: usize,
    inputs: Vec<usize>,
}

fn parse(template: &[InlineAsmTemplatePiece]) -> Result<Plan, String> {
    let mut text = String::new();
    let mut positions = Vec::new();
    let mut width = None;
    for piece in template {
        match piece {
            InlineAsmTemplatePiece::String(s) => {
                if s.contains('@') {
                    return Err("AArch64 FP asm contains literal operand syntax".into());
                }
                text.push_str(s);
            }
            InlineAsmTemplatePiece::Placeholder {
                operand_idx,
                modifier,
                ..
            } => {
                let ty = match modifier {
                    Some('s') => TrustIrTy::F32,
                    Some('d') => TrustIrTy::F64,
                    _ => return Err("AArch64 FP asm requires s/d register modifiers".into()),
                };
                if width.as_ref().is_some_and(|old| old != &ty) {
                    return Err("AArch64 FP asm mixes register widths".into());
                }
                width = Some(ty);
                positions.push(*operand_idx);
                text.push('@');
            }
        }
    }
    let (name, args) = text
        .trim_start()
        .split_once(char::is_whitespace)
        .ok_or("AArch64 FP asm requires an instruction and operands")?;
    let op = match name {
        "fmadd" => Operation::Fmadd,
        "fsqrt" => Operation::Fsqrt,
        "frintn" => Operation::Frintn,
        _ => return Err("unsupported AArch64 FP asm instruction".into()),
    };
    let args: String = args.chars().filter(|c| !c.is_ascii_whitespace()).collect();
    let expected = if op == Operation::Fmadd {
        "@,@,@,@"
    } else {
        "@,@"
    };
    if args != expected || positions.len() != op.inputs() + 1 {
        return Err("AArch64 FP asm requires one exact scalar instruction".into());
    }
    Ok(Plan {
        op,
        width: width.ok_or("AArch64 FP asm has no typed operands")?,
        output: positions[0],
        inputs: positions[1..].to_vec(),
    })
}

pub(super) fn lower<'tcx>(
    ctx: &mut MirLoweringCtx<'tcx>,
    body: &Body<'tcx>,
    block: &mut Block,
    kind: &TerminatorKind<'tcx>,
) -> Result<(), String> {
    let TerminatorKind::InlineAsm {
        asm_macro,
        template,
        operands,
        options,
        targets,
        unwind,
        ..
    } = kind
    else {
        return Err("expected InlineAsm terminator".into());
    };
    let required = InlineAsmOptions::PURE | InlineAsmOptions::NOMEM | InlineAsmOptions::NOSTACK;
    // AArch64 Linux, and since L06-P8 AArch64 Darwin: the dialect operation is
    // selected and encoded (and ENC-5 decode-checked) by the same AArch64
    // backend on both object formats.
    if ctx.tcx.sess.target.arch.desc() != "aarch64"
        || !(ctx.tcx.sess.target.os == rustc_target::spec::Os::Linux
            || ctx.tcx.sess.target.is_like_darwin)
        || !matches!(asm_macro, mir::InlineAsmMacro::Asm)
        || !options.contains(required)
        || !(*options - required - InlineAsmOptions::PRESERVES_FLAGS).is_empty()
        || targets.len() != 1
        || !matches!(unwind, mir::UnwindAction::Unreachable)
    {
        return Err(
            "AArch64 FP asm requires Linux or Darwin, pure/nomem/nostack and one non-unwinding \
             successor"
                .into(),
        );
    }
    let plan = parse(template)?;
    let mut output = None;
    for (index, operand) in operands.iter().enumerate() {
        let (reg, input, destination) = match operand {
            mir::InlineAsmOperand::In { reg, value } => (reg, Some(value), None),
            mir::InlineAsmOperand::Out {
                reg,
                place: Some(place),
                ..
            } => (reg, None, Some(place)),
            mir::InlineAsmOperand::InOut {
                reg,
                in_value,
                out_place: Some(place),
                ..
            } => (reg, Some(in_value), Some(place)),
            _ => return Err("AArch64 FP asm operand/clobber is unsupported".into()),
        };
        if !matches!(
            reg,
            InlineAsmRegOrRegClass::RegClass(InlineAsmRegClass::AArch64(
                AArch64InlineAsmRegClass::vreg
            ))
        ) {
            return Err("AArch64 FP asm requires vreg operands".into());
        }
        if let Some(input) = input {
            let ty = ctx.monomorphize_ty(operand_rust_ty(ctx, body, input)?);
            if rust_ty_to_trust_ir_ty(ctx.tcx, ty)? != plan.width || !plan.inputs.contains(&index) {
                return Err("AArch64 FP asm input type/use disagrees with its template".into());
            }
        } else if plan.inputs.contains(&index) {
            return Err("AArch64 FP asm reads an output-only operand".into());
        }
        if let Some(destination) = destination {
            if index != plan.output
                || output.is_some()
                || !destination.projection.is_empty()
                || place_trust_ir_ty(ctx, body, destination)? != plan.width
            {
                return Err("AArch64 FP asm requires one matching scalar-local output".into());
            }
            output = Some(destination);
        } else if index == plan.output {
            return Err("AArch64 FP asm writes an input-only operand".into());
        }
    }
    let destination = output.ok_or("AArch64 FP asm has no output")?;
    // Read every input before updating an inout destination. The SSA operation
    // preserves simultaneous register reads even when a source is repeated.
    let mut inputs = Vec::new();
    for &index in &plan.inputs {
        let input = match operands.get(index) {
            Some(mir::InlineAsmOperand::In { value, .. }) => value,
            Some(mir::InlineAsmOperand::InOut { in_value, .. }) => in_value,
            _ => return Err("AArch64 FP asm input index is invalid".into()),
        };
        inputs.push(lower_operand_to_value(ctx, body, block, input)?);
    }
    let target = prepare_assign_target(ctx, destination)?;
    block.body.push(
        InstrNode::new(Inst::DialectOp(Box::new(aarch64_fp_dialect::instruction(
            plan.op, plan.width, &inputs,
        ))))
        .with_result(target.value),
    );
    finish_assign_target(ctx, body, block, destination, target)?;
    emit_call_successor(block, Some(targets[0]));
    Ok(())
}
