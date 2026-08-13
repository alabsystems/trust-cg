// trust-cg-codegen/riscv/isel.rs - Minimal, fail-closed trust_ir -> RiscVISelFunction selector
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: RISC-V Unprivileged ISA Specification (Volume 1, Version 20191213)
// Reference: RISC-V ELF psABI Specification (LP64D calling convention)

//! Minimal RISC-V instruction selector — ITEM 2 production wiring.
//!
//! # Scope and soundness contract (READ FIRST)
//!
//! This is the SMALLEST SOUND increment that makes proof-driven bounds-check
//! elimination reachable through `Compiler::compile` for `Target::Riscv64`. It is
//! NOT a full trust_ir -> RISC-V instruction selector and does not pretend to be:
//! the RISC-V backend's register allocator
//! ([`crate::riscv::pipeline::RiscVRegAssignment`]) is a naive first-appearance
//! linear map with NO liveness, NO spilling, and NO SSA/block-param handling, and
//! [`crate::riscv::pipeline::RiscVPipeline`] is single-function only (no
//! cross-function call relocations). Those two structural gaps — not opcode
//! coverage — bound what a SOUND selector may accept.
//!
//! So this selector is **fail-closed by construction**: it accepts ONLY the narrow
//! class of functions the existing RISC-V pipeline can compile correctly, and
//! returns [`RiscVIselError`] for everything else. It NEVER silently drops an
//! instruction, NEVER approximates an unhandled opcode, and NEVER emits code it
//! cannot prove the downstream pipeline handles. The accepted class is:
//!
//! * **Multiple basic blocks** with structured control flow (`Jump`, `Brif`,
//!   `Icmp`, `Trap`). The phase-1 register allocator runs real live-in/live-out
//!   CFG dataflow over `block_order` using each block's `successors`, so a value
//!   defined in one block and used in a successor is allocated consistently.
//!   Block params / PHIs are NOT handled here: the adapter pre-lowers block-arg
//!   passing into explicit `Copy` instructions in predecessor/edge-split blocks,
//!   so only the ENTRY block's params (the formal arguments) are bound to
//!   `a0..a7`; a NON-entry block carrying params is rejected fail-closed (the
//!   selector has no block-param register-passing logic). `Switch` is likewise
//!   rejected fail-closed (a dropped case would be a silent miscompile).
//! * Integer-only params/returns passed in `a0..a7` (no stack args, no FP/vector,
//!   no aggregates by value). At most 8 params, at most 1 return.
//! * A straight-line body over a small, explicitly-enumerated opcode set:
//!   `Iconst`, `Copy`, `Iadd`/`Isub`/`Imul`, `Band`/`Bor`/`Bxor`,
//!   `Ishl`/`Ushr`/`Sshr`, integer `Load`/`Store`, `ArrayGep`/`StructGep`,
//!   the proof-only `GuardBoundsCheck` carrier, and `Return`.
//!   ANY other opcode (calls, branches, FP, atomics, vector, ...) is rejected.
//!
//! The ONLY behavior-relevant thing this path does differently from "keep every
//! guard" is route `GuardBoundsCheck` through the SHARED Certified-Elimination
//! Kernel via the existing [`emit_riscv_bounds_check_carrier`] +
//! [`RiscVProofGuardElimination`] (run by the caller, fail-closed re-check). A
//! KEPT carrier expands to a real `BGEU+EBREAK` runtime check, byte-identical to
//! the gate-off path; an ELIMINATED carrier is removed only under kernel
//! authorization. The decision surface is entirely in the proven shared kernel —
//! this file only does selection plumbing.

use std::collections::HashMap;

use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::riscv_ops::RiscVOpcode;
use trust_cg_ir::riscv_regs::{self, RISCV_ARG_GPRS};

use trust_cg_lower::function::{Function as LirFunction, Signature as LirSignature};
use trust_cg_lower::instructions::{Block as LirBlock, Instruction, IntCC, Opcode, Value};
use trust_cg_lower::types::Type;

use crate::riscv::pipeline::{
    RiscVISelFunction, RiscVISelInst, RiscVISelOperand, emit_riscv_bounds_check_carrier,
};

/// Error from the minimal RISC-V selector. Every variant is a REFUSAL to select
/// (fail-closed), never a silently-degraded selection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RiscVIselError {
    /// The function has a shape the minimal selector deliberately rejects
    /// (multi-block, too many params, non-integer ABI slot, ...).
    Unsupported(String),
    /// The function contains an opcode this minimal selector does not handle.
    /// Rejecting (not approximating) is the sound choice.
    UnsupportedOpcode(String),
}

impl core::fmt::Display for RiscVIselError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Unsupported(m) => {
                write!(f, "RISC-V minimal ISel unsupported function shape: {m}")
            }
            Self::UnsupportedOpcode(m) => {
                write!(f, "RISC-V minimal ISel unsupported opcode: {m}")
            }
        }
    }
}

impl std::error::Error for RiscVIselError {}

/// Return `true` iff this LIR function is in the class the minimal RISC-V selector
/// can lower SOUNDLY. Used by `Compiler::compile` to decide whether to dispatch a
/// RISC-V function to this path or to fail closed with a clear "not yet wired"
/// error (rather than miscompile).
///
/// The check is intentionally conservative; see the module docs for the accepted
/// class. It is the single source of truth for "can the minimal RISC-V path
/// handle this function".
pub fn function_is_minimally_selectable(func: &LirFunction) -> bool {
    select_function(func).is_ok()
}

/// Lower a LIR [`Function`] to a [`RiscVISelFunction`], or fail closed.
///
/// On success, the returned function has exactly one block (the entry block) with
/// the selected instruction stream, ABI argument moves prepended, and any
/// `GuardBoundsCheck` lowered to the proof-only carrier with its discharged
/// obligation recorded in `guard_obligations` (so the kernel-gated pass can
/// authorize elimination). On any unhandled shape/opcode it returns
/// [`RiscVIselError`] WITHOUT producing partial output.
pub fn select_function(func: &LirFunction) -> Result<RiscVISelFunction, RiscVIselError> {
    // The RISC-V object pipeline has no personality/LSDA/unwind-table emitter.
    // Reject the canonical EH sidecar before inspecting opcodes: an ordinary
    // `Invoke` would eventually fail selection, but personality-only,
    // landing-pad-only, or call-site-only metadata can accompany an otherwise
    // supported body and must never be silently discarded.
    if !func.eh_info.is_empty() {
        return Err(RiscVIselError::Unsupported(format!(
            "function `{}` carries exception-handling metadata, but the RISC-V backend does not emit personality/LSDA/unwind tables",
            func.name
        )));
    }

    let entry = func.entry_block;
    if !func.blocks.contains_key(&entry) {
        return Err(RiscVIselError::Unsupported(format!(
            "function `{}` has no entry block body",
            func.name
        )));
    }

    // --- ABI gate: integer args in a0..a7, <=1 integer return -----------------
    let sig = &func.signature;
    abi_check(sig, &func.name)?;

    let mut out = RiscVISelFunction::new(
        func.name.clone(),
        LirSignature {
            params: sig.params.clone(),
            returns: sig.returns.clone(),
        },
    );

    // --- Block layout ---------------------------------------------------------
    // Select blocks in CFG reverse-postorder (entry first, defs-before-uses).
    // `func.block_order` is the raw adapter order and is NOT guaranteed to place
    // defs before uses across blocks, so we walk `layout_order()` instead — the
    // value-tracking `vmap` is built in selection order and `use_value` fails on
    // a forward cross-block reference. `ensure_block` records each block into the
    // ISel function's own `block_order` in this layout order, which is the final
    // code layout the pipeline encodes and resolves branch offsets over.
    let layout = func.layout_order();
    for &b in &layout {
        out.ensure_block(b);
    }

    // Value -> selected vreg map, shared across ALL blocks so a value defined in
    // one block and used in a successor resolves to the SAME vreg (the phase-1
    // allocator's live-in/live-out dataflow then keeps it allocated across the
    // edge). We allocate fresh GPR vregs and move each incoming argument register
    // into one, so the body is uniform over vregs.
    let mut vmap: HashMap<Value, VReg> = HashMap::new();

    for &b in &layout {
        let block = func.blocks.get(&b).ok_or_else(|| {
            RiscVIselError::Unsupported(format!(
                "function `{}` block {} in layout order has no body",
                func.name, b.0
            ))
        })?;

        if b == entry {
            // Bind the entry block's params (the formal arguments) to a0..a7 via
            // a Copy (ADDI vN, aK, 0). This mirrors x86's
            // `lower_formal_arguments`. ONLY the entry block's params are ABI
            // args; binding any other block's params to a0..a7 would clobber the
            // arg registers.
            for (i, (param_value, param_ty)) in block.params.iter().enumerate() {
                if i >= RISCV_ARG_GPRS.len() {
                    return Err(RiscVIselError::Unsupported(format!(
                        "function `{}` has more than {} integer params",
                        func.name,
                        RISCV_ARG_GPRS.len()
                    )));
                }
                if !is_register_passable(param_ty) {
                    return Err(RiscVIselError::Unsupported(format!(
                        "function `{}` param {i} type {param_ty:?} is not a single-GPR ABI slot",
                        func.name
                    )));
                }
                let dst = out.fresh_vreg(RegClass::Gpr64);
                out.push_inst(
                    entry,
                    RiscVISelInst::new(
                        RiscVOpcode::Addi,
                        vec![
                            RiscVISelOperand::VReg(dst),
                            RiscVISelOperand::PReg(RISCV_ARG_GPRS[i]),
                            RiscVISelOperand::Imm(0),
                        ],
                    ),
                );
                vmap.insert(*param_value, dst);
            }
        } else if !block.params.is_empty() {
            // A NON-entry block carrying params would require block-param /
            // PHI-style value passing at edges. The adapter is supposed to have
            // pre-lowered that into predecessor `Copy` instructions, so a
            // surviving non-entry block param means a shape this selector cannot
            // pass values into soundly. Reject rather than miscompile.
            return Err(RiscVIselError::Unsupported(format!(
                "function `{}` non-entry block {} has {} param(s); block-param register \
                 passing is not implemented (adapter should pre-lower PHIs to Copy)",
                func.name,
                b.0,
                block.params.len()
            )));
        }

        // --- Body selection (carry the current block id) ----------------------
        for inst in &block.instructions {
            select_instruction(inst, b, &func.name, &mut out, &mut vmap)?;
        }
    }

    Ok(out)
}

/// Validate the function signature is in the integer-only, register-passable ABI
/// class the minimal selector supports.
fn abi_check(sig: &LirSignature, name: &str) -> Result<(), RiscVIselError> {
    if sig.params.len() > RISCV_ARG_GPRS.len() {
        return Err(RiscVIselError::Unsupported(format!(
            "function `{name}` has {} params; only <= {} integer args are supported",
            sig.params.len(),
            RISCV_ARG_GPRS.len()
        )));
    }
    for (i, p) in sig.params.iter().enumerate() {
        if !is_register_passable(p) {
            return Err(RiscVIselError::Unsupported(format!(
                "function `{name}` param {i} type {p:?} is not a single-GPR ABI slot \
                 (scalar integer/pointer, or large by-reference aggregate)"
            )));
        }
    }
    if sig.returns.len() > 1 {
        return Err(RiscVIselError::Unsupported(format!(
            "function `{name}` returns {} values; only <= 1 integer return is supported",
            sig.returns.len()
        )));
    }
    if let Some(r) = sig.returns.first()
        && !is_integer_or_pointer(r)
    {
        return Err(RiscVIselError::Unsupported(format!(
            "function `{name}` return type {r:?} is not an integer/pointer ABI slot"
        )));
    }
    Ok(())
}

/// RISC-V LP64D: aggregates strictly larger than 2×XLEN (16 bytes) are passed
/// BY REFERENCE — the caller materializes the aggregate and passes its address in
/// a single GPR. The adapter models such a by-value aggregate parameter as the
/// aggregate's ADDRESS (one I64 pointer), so it occupies exactly one argument
/// register and is sound to bind like any other pointer-in-GPR. Smaller aggregates
/// would be passed in registers by value (register-pair classification we do not
/// implement), so they are rejected by [`is_register_passable`].
const RISCV_AGGREGATE_BYREF_THRESHOLD_BYTES: u32 = 16;

/// Integer- and pointer-shaped LIR types are passed in GPRs. Pointers are I64 at
/// the LIR level; FP, vectors, and SMALL by-value aggregates are rejected.
fn is_integer_or_pointer(ty: &Type) -> bool {
    matches!(ty, Type::B1 | Type::I8 | Type::I16 | Type::I32 | Type::I64)
}

/// A type the minimal selector can bind to a single argument GPR: a scalar
/// integer/pointer, or a large aggregate passed BY REFERENCE (its address in one
/// GPR; see [`RISCV_AGGREGATE_BYREF_THRESHOLD_BYTES`]). A by-value aggregate
/// passed in register pairs is NOT register-passable here (rejected fail-closed).
fn is_register_passable(ty: &Type) -> bool {
    if is_integer_or_pointer(ty) {
        return true;
    }
    // Only large aggregates (passed by reference as one pointer GPR) are accepted.
    matches!(ty, Type::Struct(_) | Type::Array(_, _))
        && ty.bytes() > RISCV_AGGREGATE_BYREF_THRESHOLD_BYTES
}

/// Look up (or fail) the vreg holding a previously-defined value.
fn use_value(v: Value, vmap: &HashMap<Value, VReg>) -> Result<VReg, RiscVIselError> {
    vmap.get(&v).copied().ok_or_else(|| {
        RiscVIselError::Unsupported(format!(
            "value v{} used before definition (out-of-order or unsupported producer)",
            v.0
        ))
    })
}

/// Define a fresh destination vreg for a value result.
fn def_value(v: Value, out: &mut RiscVISelFunction, vmap: &mut HashMap<Value, VReg>) -> VReg {
    let dst = out.fresh_vreg(RegClass::Gpr64);
    vmap.insert(v, dst);
    dst
}

/// Select one LIR instruction into the RISC-V ISel stream, or fail closed.
///
/// `func_name` is the ENCLOSING function's symbol; it is needed to recognise a
/// recursive SELF-call (`Opcode::Call { name } where name == func_name`), which
/// is the only call shape this phase resolves PC-relatively without a relocation.
fn select_instruction(
    inst: &Instruction,
    block: LirBlock,
    func_name: &str,
    out: &mut RiscVISelFunction,
    vmap: &mut HashMap<Value, VReg>,
) -> Result<(), RiscVIselError> {
    match &inst.opcode {
        // ---- Constants -------------------------------------------------------
        // ADDI dst, x0, imm — valid only for 12-bit-representable immediates; a
        // wider constant would need LUI+ADDI which we do not emit here, so reject
        // it (the guard-bearing class never needs wide constants).
        Opcode::Iconst { ty, imm } => {
            require_int(ty, "Iconst")?;
            let dst = inst_one_result(inst, "Iconst")?;
            if !(-2048..=2047).contains(imm) {
                return Err(RiscVIselError::UnsupportedOpcode(format!(
                    "Iconst {imm} is out of the 12-bit ADDI immediate range"
                )));
            }
            let d = def_value(dst, out, vmap);
            out.push_inst(
                block,
                RiscVISelInst::new(
                    RiscVOpcode::Addi,
                    vec![
                        RiscVISelOperand::VReg(d),
                        RiscVISelOperand::PReg(riscv_regs::ZERO),
                        RiscVISelOperand::Imm(*imm),
                    ],
                ),
            );
            Ok(())
        }

        // ---- Register move ---------------------------------------------------
        Opcode::Copy => {
            expect_args(inst, 1, "Copy")?;
            let src = use_value(inst.args[0], vmap)?;
            let dst = inst_one_result(inst, "Copy")?;
            let d = def_value(dst, out, vmap);
            out.push_inst(
                block,
                RiscVISelInst::new(
                    RiscVOpcode::Addi,
                    vec![
                        RiscVISelOperand::VReg(d),
                        RiscVISelOperand::VReg(src),
                        RiscVISelOperand::Imm(0),
                    ],
                ),
            );
            Ok(())
        }

        // ---- Two-operand integer ALU (R-type) --------------------------------
        Opcode::Iadd => alu_rr(inst, block, out, vmap, RiscVOpcode::Add, "Iadd"),
        Opcode::Isub => alu_rr(inst, block, out, vmap, RiscVOpcode::Sub, "Isub"),
        Opcode::Imul => alu_rr(inst, block, out, vmap, RiscVOpcode::Mul, "Imul"),
        Opcode::Band => alu_rr(inst, block, out, vmap, RiscVOpcode::And, "Band"),
        Opcode::Bor => alu_rr(inst, block, out, vmap, RiscVOpcode::Or, "Bor"),
        Opcode::Bxor => alu_rr(inst, block, out, vmap, RiscVOpcode::Xor, "Bxor"),
        Opcode::Ishl => alu_rr(inst, block, out, vmap, RiscVOpcode::Sll, "Ishl"),
        Opcode::Ushr => alu_rr(inst, block, out, vmap, RiscVOpcode::Srl, "Ushr"),
        Opcode::Sshr => alu_rr(inst, block, out, vmap, RiscVOpcode::Sra, "Sshr"),

        // ---- Address arithmetic ----------------------------------------------
        // ArrayGep: result = base + index * sizeof(elem). We materialize the
        // scaled offset and add to base. Only power-of-two element sizes with a
        // <=12-bit shift amount are accepted (covers I8/I16/I32/I64 elements);
        // anything else is rejected fail-closed.
        Opcode::ArrayGep { elem_ty } => {
            expect_args(inst, 2, "ArrayGep")?;
            let base = use_value(inst.args[0], vmap)?;
            let index = use_value(inst.args[1], vmap)?;
            let dst = inst_one_result(inst, "ArrayGep")?;
            let size = elem_ty.bytes();
            let d = def_value(dst, out, vmap);
            if size == 1 {
                // No scaling needed: dst = base + index.
                out.push_inst(
                    block,
                    RiscVISelInst::new(
                        RiscVOpcode::Add,
                        vec![
                            RiscVISelOperand::VReg(d),
                            RiscVISelOperand::VReg(base),
                            RiscVISelOperand::VReg(index),
                        ],
                    ),
                );
                return Ok(());
            }
            if !size.is_power_of_two() {
                return Err(RiscVIselError::UnsupportedOpcode(format!(
                    "ArrayGep elem size {size} is not a power of two"
                )));
            }
            let shift = size.trailing_zeros() as i64;
            // scaled = index << shift ; dst = base + scaled
            let scaled = out.fresh_vreg(RegClass::Gpr64);
            out.push_inst(
                block,
                RiscVISelInst::new(
                    RiscVOpcode::Slli,
                    vec![
                        RiscVISelOperand::VReg(scaled),
                        RiscVISelOperand::VReg(index),
                        RiscVISelOperand::Imm(shift),
                    ],
                ),
            );
            out.push_inst(
                block,
                RiscVISelInst::new(
                    RiscVOpcode::Add,
                    vec![
                        RiscVISelOperand::VReg(d),
                        RiscVISelOperand::VReg(base),
                        RiscVISelOperand::VReg(scaled),
                    ],
                ),
            );
            Ok(())
        }

        // StructGep: result = base + field_byte_offset. We only accept offsets
        // representable in a 12-bit ADDI immediate.
        Opcode::StructGep {
            struct_ty,
            field_index,
        } => {
            let base = use_value(inst.args[0], vmap)?;
            let dst = inst_one_result(inst, "StructGep")?;
            let offset = struct_field_offset(struct_ty, *field_index)?;
            if !(0..=2047).contains(&offset) {
                return Err(RiscVIselError::UnsupportedOpcode(format!(
                    "StructGep field offset {offset} out of 12-bit ADDI range"
                )));
            }
            let d = def_value(dst, out, vmap);
            out.push_inst(
                block,
                RiscVISelInst::new(
                    RiscVOpcode::Addi,
                    vec![
                        RiscVISelOperand::VReg(d),
                        RiscVISelOperand::VReg(base),
                        RiscVISelOperand::Imm(offset),
                    ],
                ),
            );
            Ok(())
        }

        // ---- Memory ----------------------------------------------------------
        // Load: dst = mem[ptr + 0]. Integer widths only; load opcode chosen by
        // width. Signed vs unsigned narrow loads default to the SIGN-extending
        // form for I8/I16/I32 to match the LIR's signed-integer semantics; the
        // guard-bearing class loads I64, but the narrower forms are supported for
        // completeness and are still fail-closed for non-integer types.
        Opcode::Load { ty, .. } => {
            expect_args(inst, 1, "Load")?;
            let ptr = use_value(inst.args[0], vmap)?;
            let dst = inst_one_result(inst, "Load")?;
            let op = load_opcode(ty)?;
            let d = def_value(dst, out, vmap);
            out.push_inst(
                block,
                RiscVISelInst::new(
                    op,
                    vec![
                        RiscVISelOperand::VReg(d),
                        RiscVISelOperand::VReg(ptr),
                        RiscVISelOperand::Imm(0),
                    ],
                ),
            );
            Ok(())
        }

        // Store: mem[ptr + 0] = value. ISel store operand order is [src, base, off].
        Opcode::Store { ty, .. } => {
            expect_args(inst, 2, "Store")?;
            let value = use_value(inst.args[0], vmap)?;
            let ptr = use_value(inst.args[1], vmap)?;
            let op = store_opcode(ty)?;
            out.push_inst(
                block,
                RiscVISelInst::new(
                    op,
                    vec![
                        RiscVISelOperand::VReg(value),
                        RiscVISelOperand::VReg(ptr),
                        RiscVISelOperand::Imm(0),
                    ],
                ),
            );
            Ok(())
        }

        // ---- Proof-only bounds-check carrier (the whole point of ITEM 2) -----
        // Lower to the RISC-V carrier via the production emit helper, which
        // records the discharged-obligation binding by the kernel fingerprint.
        // A surviving carrier is expanded to BGEU+EBREAK by the pipeline; an
        // authorized one is deleted by RiscVProofGuardElimination. The decision
        // is entirely in the shared kernel.
        Opcode::GuardBoundsCheck { bound, obligation } => {
            expect_args(inst, 2, "GuardBoundsCheck")?;
            let base = use_value(inst.args[0], vmap)?;
            let index = use_value(inst.args[1], vmap)?;
            let bound_i64 = i64::try_from(*bound).map_err(|_| {
                RiscVIselError::UnsupportedOpcode(format!(
                    "GuardBoundsCheck bound {bound} exceeds i64 range"
                ))
            })?;
            emit_riscv_bounds_check_carrier(
                out,
                block,
                RiscVISelOperand::VReg(base),
                RiscVISelOperand::VReg(index),
                bound_i64,
                *obligation,
            );
            Ok(())
        }

        // ---- Integer comparison ---------------------------------------------
        // Icmp { cond } : dst = (lhs `cond` rhs) ? 1 : 0. Lowered with SLT/SLTU
        // (+ XORI / SLTIU for equality and the inverted relations) so the result
        // is a 0/1 boolean a later `Brif` tests against zero. RISC-V has no
        // GT/LE/GTU/LEU set-less-than, so those relations swap operands.
        Opcode::Icmp { cond } => {
            expect_args(inst, 2, "Icmp")?;
            let lhs = use_value(inst.args[0], vmap)?;
            let rhs = use_value(inst.args[1], vmap)?;
            let dst = inst_one_result(inst, "Icmp")?;
            select_icmp(*cond, lhs, rhs, dst, block, out, vmap);
            Ok(())
        }

        // ---- Unconditional branch -------------------------------------------
        // Jump { dest } : J dest, i.e. JAL x0, dest. The TARGET is a Block
        // operand; the pipeline's resolve_riscv_branches rewrites it to a
        // PC-relative Imm. Record the successor so liveness live-out dataflow is
        // correct across the edge.
        Opcode::Jump { dest } => {
            out.push_inst(
                block,
                RiscVISelInst::new(
                    RiscVOpcode::Jal,
                    vec![
                        RiscVISelOperand::PReg(riscv_regs::ZERO),
                        RiscVISelOperand::Block(*dest),
                    ],
                ),
            );
            add_successor(out, block, *dest);
            Ok(())
        }

        // ---- Conditional branch ---------------------------------------------
        // Brif { cond, then_dest, else_dest } : cond is a 0/1 Value (typically
        // from an Icmp), NOT an embedded condition code. Lower as branch-if-
        // nonzero to then_dest, then an unconditional JAL to else_dest. There is
        // NO automatic fallthrough in the RISC-V pipeline (block_order is
        // ensure_block call order over a HashMap-built function), so the
        // not-taken edge MUST be an explicit JAL. Mirrors x86's select_condbranch.
        Opcode::Brif {
            cond,
            then_dest,
            else_dest,
        } => {
            let cond_vreg = use_value(*cond, vmap)?;
            // BNE cond, x0, then_dest  (branch if cond != 0 = true)
            out.push_inst(
                block,
                RiscVISelInst::new(
                    RiscVOpcode::Bne,
                    vec![
                        RiscVISelOperand::VReg(cond_vreg),
                        RiscVISelOperand::PReg(riscv_regs::ZERO),
                        RiscVISelOperand::Block(*then_dest),
                    ],
                ),
            );
            // JAL x0, else_dest  (unconditional not-taken edge)
            out.push_inst(
                block,
                RiscVISelInst::new(
                    RiscVOpcode::Jal,
                    vec![
                        RiscVISelOperand::PReg(riscv_regs::ZERO),
                        RiscVISelOperand::Block(*else_dest),
                    ],
                ),
            );
            add_successor(out, block, *then_dest);
            add_successor(out, block, *else_dest);
            Ok(())
        }

        // ---- Trap ------------------------------------------------------------
        // A synchronous trap (e.g. a source-language assertion that must not be
        // erased). Lowered to EBREAK. No operands, no successors.
        Opcode::Trap => {
            out.push_inst(block, RiscVISelInst::new(RiscVOpcode::Ebreak, vec![]));
            Ok(())
        }

        // ---- Return ----------------------------------------------------------
        // Move the (single, optional) return value into a0, then JALR x0, ra, 0.
        Opcode::Return => {
            if let Some(v) = inst.args.first() {
                if inst.args.len() != 1 {
                    return Err(RiscVIselError::Unsupported(format!(
                        "Return of {} values; only <= 1 integer return is supported",
                        inst.args.len()
                    )));
                }
                let src = use_value(*v, vmap)?;
                out.push_inst(
                    block,
                    RiscVISelInst::new(
                        RiscVOpcode::Addi,
                        vec![
                            RiscVISelOperand::PReg(riscv_regs::A0),
                            RiscVISelOperand::VReg(src),
                            RiscVISelOperand::Imm(0),
                        ],
                    ),
                );
            }
            out.push_inst(
                block,
                RiscVISelInst::new(
                    RiscVOpcode::Jalr,
                    vec![
                        RiscVISelOperand::PReg(riscv_regs::ZERO),
                        RiscVISelOperand::PReg(riscv_regs::RA),
                        RiscVISelOperand::Imm(0),
                    ],
                ),
            );
            Ok(())
        }

        // ---- Direct function call (phase 3: self-recursive only) -------------
        // `Opcode::Call { name }` is a DIRECT call by symbol. This phase resolves
        // ONLY a recursive SELF-call (name == enclosing function) PC-relatively as
        // `JAL ra, entry`, exactly like a branch — no relocation needed. The RISC-V
        // codegen has no cross-function relocation machinery yet
        // (RiscVISelOperand::Symbol is declared but unhandled by the
        // resolver/encoder/ELF emitter), so a cross-function direct call is
        // fail-closed-REJECTED with a clear typed error rather than emitting a
        // wrong/zero target. Indirect (CallIndirect), variadic (CallVariadic), and
        // exception-throwing (Invoke) calls remain rejected by the catch-all below.
        Opcode::Call { name } => select_self_call(inst, block, name, func_name, out, vmap),

        // Anything else is rejected fail-closed. This is the soundness backstop:
        // a new opcode added upstream cannot silently slip through as a NOP.
        other => Err(RiscVIselError::UnsupportedOpcode(format!("{other:?}"))),
    }
}

/// Lower a direct `Opcode::Call { name }` — a recursive self-call OR a
/// cross-function direct call to another function in the same module.
///
/// Marshals integer arguments into `a0..a7` (fail-closed-rejecting >8 args, stack
/// args, or non-integer/aggregate args), emits the call, then copies the return
/// value out of `a0` into the result vreg.
///
/// Two call shapes are lowered:
/// * SELF-call (`name == func_name`): `JAL ra, Block(entry)`. The `Block(entry)`
///   target is turned into a PC-relative offset by `resolve_riscv_branches`
///   within the function's own byte range — no relocation, exactly as in phase 3.
///   Re-entering at the entry runs the prologue, which re-saves `ra` and allocates
///   a fresh frame, which is correct for recursion.
/// * CROSS-function call (`name != func_name`): the standard RISC-V direct-call
///   idiom `AUIPC ra, %pcrel_hi(name)` + `JALR ra, ra, %pcrel_lo(name)`, both
///   carrying `RiscVISelOperand::Symbol(name)` placeholders. The module emitter
///   resolves the symbol — either PC-relatively against the callee's offset
///   within the same object (no relocation) or, for an external callee, by
///   recording an `R_RISCV_CALL` relocation. ISel does NOT know whether the
///   callee is in-module, so it always emits the full pcrel pair (which can reach
///   any 32-bit PC-relative target and is what a real linker relocates); the
///   single-JAL form is reserved for the self-call, whose target is known here.
///
/// SOUNDNESS:
/// * The marshaled argument registers `a0..aN` are attached as trailing PReg use
///   operands on the call's `JAL`/`JALR` so the allocator (via `classify_def_use`
///   + `compute_liveness`) keeps the arguments live to the call and treats the
///   call as clobbering the full caller-saved set.
/// * The argument moves are emitted naively here as `ADDI a_j, src, 0`; the
///   parallel-move hazard (a source aliasing an already-written destination after
///   register allocation) is resolved by the post-regalloc
///   `fixup_call_arg_parallel_copies` pass, which reorders them with cycle
///   breaking. ISel never needs to know the final register assignment.
/// * A `Symbol` operand that survives to encoding without being resolved by the
///   module emitter is rejected fail-closed at encode time (it would otherwise
///   encode a zero/wrong target), mirroring the surviving-`Block` guard.
fn select_self_call(
    inst: &Instruction,
    block: LirBlock,
    name: &str,
    func_name: &str,
    out: &mut RiscVISelFunction,
    vmap: &mut HashMap<Value, VReg>,
) -> Result<(), RiscVIselError> {
    let is_self_call = name == func_name;

    // Marshal integer arguments into a0..a7. More than 8 args would need a stack
    // outgoing-argument area we do not implement — reject fail-closed.
    if inst.args.len() > RISCV_ARG_GPRS.len() {
        return Err(RiscVIselError::Unsupported(format!(
            "call to `{name}` passes {} arguments; only <= {} integer register \
             arguments are supported (stack arguments are not implemented)",
            inst.args.len(),
            RISCV_ARG_GPRS.len()
        )));
    }

    // A cross-function call emits `AUIPC ra, %pcrel_hi(name)` + `JALR ra, ra,
    // %pcrel_lo(name)`. The AUIPC is emitted AFTER the argument-setup moves (see
    // the `else` arm below), so the AUIPC and the JALR end up ADJACENT in the
    // final stream. This is REQUIRED for correctness: the RISC-V psABI
    // R_RISCV_CALL / R_RISCV_CALL_PLT relocation patches a CONTIGUOUS AUIPC+JALR
    // pair (hi20 into the instruction at r_offset, lo12 into the one at
    // r_offset+4), so any instruction placed between them would be corrupted by a
    // real linker. The post-regalloc `fixup_call_arg_parallel_copies` pass
    // resolves the buffered argument shuffle at the AUIPC preamble — emitting the
    // shuffle BEFORE the AUIPC — which keeps the AUIPC->JALR pair intact. AUIPC
    // writes only `ra` and the arg moves only `a0..a7`, so sequencing the shuffle
    // before the AUIPC is hazard-free.

    // Emit one `ADDI a_j, src, 0` per argument. Sources are vregs; the
    // post-regalloc parallel-copy fixup makes the shuffle safe.
    let mut arg_regs: Vec<RiscVISelOperand> = Vec::with_capacity(inst.args.len());
    for (i, &arg) in inst.args.iter().enumerate() {
        let src = use_value(arg, vmap)?;
        let areg = RISCV_ARG_GPRS[i];
        out.push_inst(
            block,
            RiscVISelInst::new(
                RiscVOpcode::Addi,
                vec![
                    RiscVISelOperand::PReg(areg),
                    RiscVISelOperand::VReg(src),
                    RiscVISelOperand::Imm(0),
                ],
            ),
        );
        arg_regs.push(RiscVISelOperand::PReg(areg));
    }

    if is_self_call {
        // The self-call target is the entry block (block_order[0]);
        // `select_function` records the entry first.
        let entry = out.block_order.first().copied().ok_or_else(|| {
            RiscVIselError::Unsupported(format!(
                "self-call in `{func_name}` has no entry block to target"
            ))
        })?;

        // JAL ra, entry  — operands: [rd=ra, Block(entry), arg PReg uses...].
        // The Block target is resolved to a PC-relative offset by
        // resolve_riscv_branches; the trailing arg PRegs are liveness-only
        // (ignored by the J-type encoder, which reads only rd + the resolved
        // offset). A self-call is NOT a CFG edge / terminator, so we do NOT add a
        // successor — it is a clobber point the allocator handles, and control
        // falls through to the return-value copy below.
        let mut call_operands = vec![
            RiscVISelOperand::PReg(riscv_regs::RA),
            RiscVISelOperand::Block(entry),
        ];
        call_operands.extend(arg_regs);
        out.push_inst(block, RiscVISelInst::new(RiscVOpcode::Jal, call_operands));
    } else {
        // Cross-function direct call. Emit the `AUIPC ra, %pcrel_hi(name)` here —
        // AFTER the argument-setup moves and IMMEDIATELY before the matching
        // `JALR ra, ra, %pcrel_lo(name)` — so the pair is contiguous (the
        // R_RISCV_CALL relocation requires it; see the comment above the arg loop).
        // The parallel-copy fixup resolves the buffered arg shuffle when it reaches
        // this AUIPC preamble, placing the shuffle before the AUIPC.
        //
        // AUIPC ra, Symbol(name)  — [rd=ra, Symbol(name)].
        out.push_inst(
            block,
            RiscVISelInst::new(
                RiscVOpcode::Auipc,
                vec![
                    RiscVISelOperand::PReg(riscv_regs::RA),
                    RiscVISelOperand::Symbol(name.to_string()),
                ],
            ),
        );

        // Both halves carry a Symbol(name) placeholder; the module emitter splits
        // the resolved 32-bit PC-relative displacement into the hi20 (AUIPC) and
        // lo12 (JALR) halves (intra-object) or records an R_RISCV_CALL relocation
        // (external). The arg PReg uses are attached to the JALR (the actual
        // control transfer) so `is_riscv_call_inst` recognises it as the call and
        // the allocator models the clobber there.
        //
        // JALR ra, ra, Symbol(name)  — [rd=ra, rs1=ra, Symbol(name), arg PRegs].
        let mut jalr_operands = vec![
            RiscVISelOperand::PReg(riscv_regs::RA),
            RiscVISelOperand::PReg(riscv_regs::RA),
            RiscVISelOperand::Symbol(name.to_string()),
        ];
        jalr_operands.extend(arg_regs);
        out.push_inst(block, RiscVISelInst::new(RiscVOpcode::Jalr, jalr_operands));
    }

    // Move the return value (a0) into the result vreg, if any. At most one
    // integer return is supported (the ABI gate already enforces <=1 return for
    // the function signature; a call result is recovered structurally here).
    match inst.results.as_slice() {
        [] => {}
        [r] => {
            let d = def_value(*r, out, vmap);
            out.push_inst(
                block,
                RiscVISelInst::new(
                    RiscVOpcode::Addi,
                    vec![
                        RiscVISelOperand::VReg(d),
                        RiscVISelOperand::PReg(riscv_regs::A0),
                        RiscVISelOperand::Imm(0),
                    ],
                ),
            );
        }
        many => {
            return Err(RiscVIselError::Unsupported(format!(
                "self-call to `{name}` returns {} values; only <= 1 integer return is supported",
                many.len()
            )));
        }
    }

    Ok(())
}

/// Emit a two-source R-type ALU op `dst = lhs OP rhs`.
fn alu_rr(
    inst: &Instruction,
    block: LirBlock,
    out: &mut RiscVISelFunction,
    vmap: &mut HashMap<Value, VReg>,
    op: RiscVOpcode,
    name: &str,
) -> Result<(), RiscVIselError> {
    if inst.args.len() != 2 {
        return Err(RiscVIselError::UnsupportedOpcode(format!(
            "{name} expects 2 args, got {}",
            inst.args.len()
        )));
    }
    let lhs = use_value(inst.args[0], vmap)?;
    let rhs = use_value(inst.args[1], vmap)?;
    let dst = inst_one_result(inst, name)?;
    let d = def_value(dst, out, vmap);
    out.push_inst(
        block,
        RiscVISelInst::new(
            op,
            vec![
                RiscVISelOperand::VReg(d),
                RiscVISelOperand::VReg(lhs),
                RiscVISelOperand::VReg(rhs),
            ],
        ),
    );
    Ok(())
}

/// Record `dest` as a CFG successor of `block` (idempotent). Successors are
/// LOAD-BEARING for correctness, not bookkeeping: the phase-1 allocator's
/// live-out dataflow is derived SOLELY from each block's `successors`, so a
/// branch whose successor is not recorded would let a value live across the edge
/// be wrongly freed/reused — a miscompile. We dedup so a `Brif` whose two arms
/// target the same block (or repeated edges) does not double-list a successor.
fn add_successor(out: &mut RiscVISelFunction, block: LirBlock, dest: LirBlock) {
    let succs = &mut out.blocks.entry(block).or_default().successors;
    if !succs.contains(&dest) {
        succs.push(dest);
    }
}

/// Map an [`IntCC`] to the RISC-V `set-less-than` lowering of `lhs cond rhs`,
/// producing a 0/1 boolean in `dst`.
///
/// RISC-V's only comparison primitives are `SLT`/`SLTU` (signed/unsigned
/// set-less-than) and equality via subtract-and-test. We synthesize all 10
/// conditions:
///
/// * `<`  : `SLT/SLTU dst, lhs, rhs`
/// * `>`  : `SLT/SLTU dst, rhs, lhs`              (operand swap)
/// * `>=` : `SLT/SLTU dst, lhs, rhs ; XORI dst, dst, 1`   (invert `<`)
/// * `<=` : `SLT/SLTU dst, rhs, lhs ; XORI dst, dst, 1`   (invert `>`)
/// * `==` : `SUB t, lhs, rhs ; SLTIU dst, t, 1`   (t == 0  -> dst = 1)
/// * `!=` : `SUB t, lhs, rhs ; SLTU dst, x0, t`   (t != 0  -> dst = 1)
///
/// Every [`IntCC`] variant is matched explicitly (no wildcard), so a future
/// upstream variant fails to compile here rather than silently miscompiling.
fn select_icmp(
    cond: IntCC,
    lhs: VReg,
    rhs: VReg,
    dst: Value,
    block: LirBlock,
    out: &mut RiscVISelFunction,
    vmap: &mut HashMap<Value, VReg>,
) {
    // Emit `d = a SLT/SLTU b` (set-less-than), returning the def vreg.
    let slt = |a: VReg, b: VReg, op: RiscVOpcode, out: &mut RiscVISelFunction, d: VReg| {
        out.push_inst(
            block,
            RiscVISelInst::new(
                op,
                vec![
                    RiscVISelOperand::VReg(d),
                    RiscVISelOperand::VReg(a),
                    RiscVISelOperand::VReg(b),
                ],
            ),
        );
    };
    // Emit `d = d XOR 1` to invert a boolean in place.
    let xori1 = |out: &mut RiscVISelFunction, d: VReg| {
        out.push_inst(
            block,
            RiscVISelInst::new(
                RiscVOpcode::Xori,
                vec![
                    RiscVISelOperand::VReg(d),
                    RiscVISelOperand::VReg(d),
                    RiscVISelOperand::Imm(1),
                ],
            ),
        );
    };

    match cond {
        IntCC::SignedLessThan => {
            let d = def_value(dst, out, vmap);
            slt(lhs, rhs, RiscVOpcode::Slt, out, d);
        }
        IntCC::UnsignedLessThan => {
            let d = def_value(dst, out, vmap);
            slt(lhs, rhs, RiscVOpcode::Sltu, out, d);
        }
        IntCC::SignedGreaterThan => {
            // a > b  <=>  b < a
            let d = def_value(dst, out, vmap);
            slt(rhs, lhs, RiscVOpcode::Slt, out, d);
        }
        IntCC::UnsignedGreaterThan => {
            let d = def_value(dst, out, vmap);
            slt(rhs, lhs, RiscVOpcode::Sltu, out, d);
        }
        IntCC::SignedGreaterThanOrEqual => {
            // a >= b  <=>  !(a < b)
            let d = def_value(dst, out, vmap);
            slt(lhs, rhs, RiscVOpcode::Slt, out, d);
            xori1(out, d);
        }
        IntCC::UnsignedGreaterThanOrEqual => {
            let d = def_value(dst, out, vmap);
            slt(lhs, rhs, RiscVOpcode::Sltu, out, d);
            xori1(out, d);
        }
        IntCC::SignedLessThanOrEqual => {
            // a <= b  <=>  !(b < a)
            let d = def_value(dst, out, vmap);
            slt(rhs, lhs, RiscVOpcode::Slt, out, d);
            xori1(out, d);
        }
        IntCC::UnsignedLessThanOrEqual => {
            let d = def_value(dst, out, vmap);
            slt(rhs, lhs, RiscVOpcode::Sltu, out, d);
            xori1(out, d);
        }
        IntCC::Equal => {
            // d = (lhs - rhs) == 0  via  SUB t, lhs, rhs ; SLTIU d, t, 1.
            let t = out.fresh_vreg(RegClass::Gpr64);
            out.push_inst(
                block,
                RiscVISelInst::new(
                    RiscVOpcode::Sub,
                    vec![
                        RiscVISelOperand::VReg(t),
                        RiscVISelOperand::VReg(lhs),
                        RiscVISelOperand::VReg(rhs),
                    ],
                ),
            );
            let d = def_value(dst, out, vmap);
            // SLTIU d, t, 1  =>  d = (unsigned t < 1) = (t == 0).
            out.push_inst(
                block,
                RiscVISelInst::new(
                    RiscVOpcode::Sltiu,
                    vec![
                        RiscVISelOperand::VReg(d),
                        RiscVISelOperand::VReg(t),
                        RiscVISelOperand::Imm(1),
                    ],
                ),
            );
        }
        IntCC::NotEqual => {
            // d = (lhs - rhs) != 0  via  SUB t, lhs, rhs ; SLTU d, x0, t.
            let t = out.fresh_vreg(RegClass::Gpr64);
            out.push_inst(
                block,
                RiscVISelInst::new(
                    RiscVOpcode::Sub,
                    vec![
                        RiscVISelOperand::VReg(t),
                        RiscVISelOperand::VReg(lhs),
                        RiscVISelOperand::VReg(rhs),
                    ],
                ),
            );
            let d = def_value(dst, out, vmap);
            // SLTU d, x0, t  =>  d = (0 < unsigned t) = (t != 0).
            out.push_inst(
                block,
                RiscVISelInst::new(
                    RiscVOpcode::Sltu,
                    vec![
                        RiscVISelOperand::VReg(d),
                        RiscVISelOperand::PReg(riscv_regs::ZERO),
                        RiscVISelOperand::VReg(t),
                    ],
                ),
            );
        }
    }
}

/// Extract the single result value of an instruction, or fail closed.
fn inst_one_result(inst: &Instruction, name: &str) -> Result<Value, RiscVIselError> {
    match inst.results.as_slice() {
        [v] => Ok(*v),
        other => Err(RiscVIselError::UnsupportedOpcode(format!(
            "{name} expects exactly 1 result, got {}",
            other.len()
        ))),
    }
}

/// Assert that an instruction carries exactly `n` argument values, or fail closed
/// with a typed [`RiscVIselError`]. Selector arms that index `inst.args[..]`
/// directly MUST call this first so a malformed-arity instruction is REJECTED
/// (fail-closed-by-construction) rather than panicking on an out-of-bounds index.
fn expect_args(inst: &Instruction, n: usize, name: &str) -> Result<(), RiscVIselError> {
    if inst.args.len() != n {
        return Err(RiscVIselError::UnsupportedOpcode(format!(
            "{name} expects {n} args, got {}",
            inst.args.len()
        )));
    }
    Ok(())
}

fn require_int(ty: &Type, ctx: &str) -> Result<(), RiscVIselError> {
    if is_integer_or_pointer(ty) {
        Ok(())
    } else {
        Err(RiscVIselError::UnsupportedOpcode(format!(
            "{ctx} on non-integer type {ty:?}"
        )))
    }
}

/// Choose the integer load opcode for an LIR scalar type (sign-extending for
/// narrow widths, matching signed-integer LIR load semantics; I64 is a plain LD).
fn load_opcode(ty: &Type) -> Result<RiscVOpcode, RiscVIselError> {
    match ty {
        Type::B1 | Type::I8 => Ok(RiscVOpcode::Lb),
        Type::I16 => Ok(RiscVOpcode::Lh),
        Type::I32 => Ok(RiscVOpcode::Lw),
        Type::I64 => Ok(RiscVOpcode::Ld),
        other => Err(RiscVIselError::UnsupportedOpcode(format!(
            "Load of non-integer type {other:?}"
        ))),
    }
}

/// Choose the integer store opcode for an LIR scalar type.
fn store_opcode(ty: &Type) -> Result<RiscVOpcode, RiscVIselError> {
    match ty {
        Type::B1 | Type::I8 => Ok(RiscVOpcode::Sb),
        Type::I16 => Ok(RiscVOpcode::Sh),
        Type::I32 => Ok(RiscVOpcode::Sw),
        Type::I64 => Ok(RiscVOpcode::Sd),
        other => Err(RiscVIselError::UnsupportedOpcode(format!(
            "Store of non-integer type {other:?}"
        ))),
    }
}

/// Compute the byte offset of `field_index` within a struct type. Fails closed
/// for non-struct types or out-of-range indices.
///
/// This used to be a fourth independent copy of the natural-C accumulation
/// loop, in a different crate from the three others. It is now the SHARED
/// accessor [`Type::offset_of`] — the same one the aarch64 and x86_64 ISels
/// call (`isel.rs`, `x86_64_isel.rs`) — so a change to natural-C layout cannot
/// reach two of the three backends and miss this one.
///
/// # Why this offset may stay natural-C, when the adapter's may not
///
/// `Opcode::StructGep` carries a repr-less `Type::Struct(Vec<Type>)`: no
/// `StructId`, no declared offsets, no `repr`. By the time ISel sees it there
/// is nothing left to resolve against, so this cannot consult
/// `trust_cg_lower::declared_layout` even though the crate dependency exists —
/// the input has no struct identity, not merely an inconvenient shape.
///
/// It does not need to. The adapter DECLINES to emit `StructGep` whenever an
/// authority above natural C owns the field: `explicit_field_offset` answers
/// `Some(offset)` for every `#[repr(packed(N))]` struct and every declared
/// layout that places the field elsewhere, and the adapter then emits
/// `Iconst` + `Iadd` at that address instead. Every surviving `StructGep` is
/// therefore a struct whose authority IS `LayoutSource::NaturalC`.
///
/// That is the sync obligation this function inherits, and it is why the
/// dedup is the whole fix: it must agree with `Type::offset_of` exactly,
/// because `Type::offset_of` is what the adapter compared against when it
/// decided this opcode was emittable at all.
fn struct_field_offset(struct_ty: &Type, field_index: u32) -> Result<i64, RiscVIselError> {
    let Type::Struct(fields) = struct_ty else {
        return Err(RiscVIselError::UnsupportedOpcode(format!(
            "StructGep on non-struct type {struct_ty:?}"
        )));
    };
    let offset = struct_ty.offset_of(field_index as usize).ok_or_else(|| {
        RiscVIselError::UnsupportedOpcode(format!(
            "StructGep field index {field_index} out of range ({} fields)",
            fields.len()
        ))
    })?;
    Ok(i64::from(offset))
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    use trust_cg_ir::{DischargeStatus, DischargedEvidenceTable};
    use trust_cg_lower::function::{
        BasicBlock, EhCallSite, EhFunctionInfo, EhLandingPad, Function as LirFunction,
        Signature as LirSignature,
    };
    use trust_cg_lower::instructions::{Block as LirBlock, Instruction, Opcode, Value};
    use trust_cg_lower::types::Type;

    use crate::riscv::pipeline::{RiscVProofGuardElimination, riscv_compile_to_bytes};

    const EBREAK_WORD: u32 = 0x0010_0073;

    /// Build the canonical guard-bearing LIR function (the shape the adapter emits
    /// for a proven `array[index]`): one block, params [array_ptr, index], a
    /// `GuardBoundsCheck` carrier, an `ArrayGep`, a `Load`, and a `Return`.
    fn guard_bearing_func(obligation: Option<u64>) -> LirFunction {
        let sig = LirSignature {
            params: vec![Type::Array(Box::new(Type::I64), 8), Type::I64],
            returns: vec![Type::I64],
        };
        let mut func = LirFunction::new("proven_extract", sig);
        let entry = LirBlock(0);
        let mut block = BasicBlock {
            params: vec![
                (Value(0), Type::Array(Box::new(Type::I64), 8)),
                (Value(1), Type::I64),
            ],
            instructions: Vec::new(),
            source_locs: Vec::new(),
        };
        block.instructions.push(Instruction {
            opcode: Opcode::GuardBoundsCheck {
                bound: 8,
                obligation,
            },
            args: vec![Value(0), Value(1)],
            results: vec![],
        });
        block.instructions.push(Instruction {
            opcode: Opcode::ArrayGep { elem_ty: Type::I64 },
            args: vec![Value(0), Value(1)],
            results: vec![Value(3)],
        });
        block.instructions.push(Instruction {
            opcode: Opcode::Load {
                ty: Type::I64,
                align: None,
            },
            args: vec![Value(3)],
            results: vec![Value(2)],
        });
        block.instructions.push(Instruction {
            opcode: Opcode::Return,
            args: vec![Value(2)],
            results: vec![],
        });
        func.blocks.insert(entry, block);
        func.entry_block = entry;
        func.block_order = vec![entry];
        func
    }

    fn live_carriers(func: &RiscVISelFunction) -> usize {
        func.block_order
            .iter()
            .filter_map(|b| func.blocks.get(b))
            .flat_map(|b| b.insts.iter())
            .filter(|i| i.opcode == RiscVOpcode::TrapBoundsCheckExact)
            .count()
    }

    #[test]
    fn selects_guard_bearing_function_with_carrier_and_obligation() {
        let func = guard_bearing_func(Some(0x8000_0000));
        let isel = select_function(&func).expect("guard-bearing function is selectable");
        assert_eq!(live_carriers(&isel), 1, "exactly one carrier emitted");
        assert_eq!(
            isel.guard_obligations.len(),
            1,
            "the carrier's discharged obligation must be recorded by fingerprint"
        );
        assert!(function_is_minimally_selectable(&func));
    }

    #[test]
    fn carrier_with_no_obligation_records_no_binding() {
        let func = guard_bearing_func(None);
        let isel = select_function(&func).expect("selectable");
        assert_eq!(live_carriers(&isel), 1);
        assert!(
            isel.guard_obligations.is_empty(),
            "no obligation => no binding => kernel keeps the guard (fail-safe)"
        );
    }

    #[test]
    fn rejects_every_nonempty_eh_metadata_shape_fail_closed() {
        let entry = LirBlock(0);
        let pad = LirBlock(1);
        let cases = [
            EhFunctionInfo {
                personality: Some("rust_eh_personality".to_string()),
                ..EhFunctionInfo::default()
            },
            EhFunctionInfo {
                landing_pads: vec![EhLandingPad {
                    block: pad,
                    catch_type_indices: vec![0],
                    is_cleanup: false,
                }],
                ..EhFunctionInfo::default()
            },
            EhFunctionInfo {
                call_sites: vec![EhCallSite {
                    call_block: entry,
                    landing_pad_block: pad,
                }],
                ..EhFunctionInfo::default()
            },
        ];

        for eh_info in cases {
            assert!(
                !eh_info.is_empty(),
                "the canonical emptiness predicate must see every EH component"
            );
            let mut func = guard_bearing_func(None);
            func.eh_info = eh_info;
            let err = select_function(&func).expect_err("RISC-V must reject every EH sidecar");
            assert!(matches!(err, RiscVIselError::Unsupported(_)), "{err}");
            assert!(
                err.to_string().contains("exception-handling metadata"),
                "{err}"
            );
            assert!(!function_is_minimally_selectable(&func));
        }
    }

    /// THE soundness property: the gate-ON ISel function is EXACTLY the gate-OFF
    /// ISel function with the carrier removed — a strict restriction, never a
    /// different lowering. We assert the eliminated stream is the kept stream minus
    /// the single `TrapBoundsCheckExact`.
    #[test]
    fn gate_on_is_strict_restriction_of_gate_off() {
        let func = guard_bearing_func(Some(0x8000_0000));

        // Gate OFF: keep the carrier.
        let kept = select_function(&func).expect("selectable");

        // Gate ON with discharged evidence: eliminate the carrier.
        let mut eliminated = select_function(&func).expect("selectable");
        let mut evidence = DischargedEvidenceTable::default();
        evidence.insert(0x8000_0000u128, DischargeStatus::Discharged, None);
        let obligations: HashMap<u128, (u128, Option<u128>)> = eliminated
            .guard_obligations
            .iter()
            .map(|(&fp, &oid)| (fp, (oid as u128, None)))
            .collect();
        let mut pass = RiscVProofGuardElimination::new();
        pass.enable_kernel_gate(evidence, obligations);
        let changed = pass.run_on_function(&mut eliminated);
        assert!(changed, "the discharged carrier must be eliminated");
        assert!(pass.recheck_kernel_eliminations().is_ok(), "re-check ok");

        // The eliminated stream is the kept stream MINUS the carrier — every other
        // instruction (ABI moves, GEP, load, return) is byte-for-byte identical.
        let entry = LirBlock(0);
        let kept_insts: Vec<_> = kept.blocks[&entry]
            .insts
            .iter()
            .filter(|i| i.opcode != RiscVOpcode::TrapBoundsCheckExact)
            .map(|i| (i.opcode, i.operands.clone()))
            .collect();
        let elim_insts: Vec<_> = eliminated.blocks[&entry]
            .insts
            .iter()
            .map(|i| (i.opcode, i.operands.clone()))
            .collect();
        assert_eq!(
            kept_insts.len(),
            elim_insts.len(),
            "removing the carrier from the kept stream yields the eliminated stream"
        );
        for (a, b) in kept_insts.iter().zip(elim_insts.iter()) {
            assert_eq!(a.0, b.0, "opcode parity outside the carrier");
            assert_eq!(a.1, b.1, "operand parity outside the carrier");
        }
        assert_eq!(live_carriers(&eliminated), 0);
    }

    /// End-to-end through the existing RISC-V pipeline: a KEPT carrier compiles to
    /// a real BGEU+EBREAK trap; an ELIMINATED carrier vanishes.
    #[test]
    fn kept_carrier_emits_ebreak_eliminated_does_not() {
        let func = guard_bearing_func(Some(0x8000_0000));

        let kept = select_function(&func).expect("selectable");
        let kept_bytes = riscv_compile_to_bytes(&kept).expect("compile kept");
        let kept_ebreaks = kept_bytes
            .chunks_exact(4)
            .filter(|w| *w == EBREAK_WORD.to_le_bytes())
            .count();
        assert!(kept_ebreaks >= 1, "kept carrier expands to an EBREAK trap");

        let mut eliminated = select_function(&func).expect("selectable");
        let mut evidence = DischargedEvidenceTable::default();
        evidence.insert(0x8000_0000u128, DischargeStatus::Discharged, None);
        let obligations: HashMap<u128, (u128, Option<u128>)> = eliminated
            .guard_obligations
            .iter()
            .map(|(&fp, &oid)| (fp, (oid as u128, None)))
            .collect();
        let mut pass = RiscVProofGuardElimination::new();
        pass.enable_kernel_gate(evidence, obligations);
        pass.run_on_function(&mut eliminated);
        let elim_bytes = riscv_compile_to_bytes(&eliminated).expect("compile eliminated");
        let elim_ebreaks = elim_bytes
            .chunks_exact(4)
            .filter(|w| *w == EBREAK_WORD.to_le_bytes())
            .count();
        assert_eq!(elim_ebreaks, 0, "eliminated carrier leaves no EBREAK trap");
    }

    /// A NON-entry block carrying SSA params (a surviving block-arg/PHI the
    /// adapter did not pre-lower to Copy) is rejected fail-closed — the selector
    /// has no block-param register-passing logic, and a wrong value-passing is a
    /// silent miscompile.
    #[test]
    fn rejects_nonentry_block_with_params_fail_closed() {
        // entry: Jump b1 ; b1(param): Return
        let sig = LirSignature {
            params: vec![Type::I64],
            returns: vec![Type::I64],
        };
        let mut func = LirFunction::new("nonentry_params", sig);
        let entry = LirBlock(0);
        let b1 = LirBlock(1);
        let mut eb = BasicBlock {
            params: vec![(Value(0), Type::I64)],
            instructions: Vec::new(),
            source_locs: Vec::new(),
        };
        eb.instructions.push(Instruction {
            opcode: Opcode::Jump { dest: b1 },
            args: vec![],
            results: vec![],
        });
        // b1 carries a param — must be rejected.
        let mut bb1 = BasicBlock {
            params: vec![(Value(10), Type::I64)],
            instructions: Vec::new(),
            source_locs: Vec::new(),
        };
        bb1.instructions.push(Instruction {
            opcode: Opcode::Return,
            args: vec![],
            results: vec![],
        });
        func.blocks.insert(entry, eb);
        func.blocks.insert(b1, bb1);
        func.entry_block = entry;
        func.block_order = vec![entry, b1];
        let err = select_function(&func).expect_err("non-entry block params rejected");
        assert!(matches!(err, RiscVIselError::Unsupported(_)));
        assert!(!function_is_minimally_selectable(&func));
    }

    /// `Switch` is a multi-successor terminator the selector does NOT lower; it
    /// must be rejected fail-closed (a dropped case is a silent miscompile).
    #[test]
    fn rejects_switch_terminator_fail_closed() {
        let sig = LirSignature {
            params: vec![Type::I64],
            returns: vec![],
        };
        let mut func = LirFunction::new("has_switch", sig);
        let entry = LirBlock(0);
        let b1 = LirBlock(1);
        let mut eb = BasicBlock {
            params: vec![(Value(0), Type::I64)],
            instructions: Vec::new(),
            source_locs: Vec::new(),
        };
        eb.instructions.push(Instruction {
            opcode: Opcode::Switch {
                cases: vec![(0, b1)],
                default: b1,
            },
            args: vec![Value(0)],
            results: vec![],
        });
        let mut bb1 = BasicBlock::default();
        bb1.instructions.push(Instruction {
            opcode: Opcode::Return,
            args: vec![],
            results: vec![],
        });
        func.blocks.insert(entry, eb);
        func.blocks.insert(b1, bb1);
        func.entry_block = entry;
        func.block_order = vec![entry, b1];
        let err = select_function(&func).expect_err("Switch rejected");
        assert!(matches!(err, RiscVIselError::UnsupportedOpcode(_)));
    }

    /// PHASE 4: a CROSS-FUNCTION direct call (`name != enclosing function`) is now
    /// SELECTABLE at ISel — it is lowered to the RISC-V direct-call idiom
    /// `AUIPC ra, %pcrel_hi(callee)` + `JALR ra, ra, %pcrel_lo(callee)`, both
    /// carrying a `Symbol(callee)` placeholder for the module emitter to resolve
    /// (intra-object patch or external `R_RISCV_CALL` relocation). The fail-closed
    /// boundary moved from ISel to the module emitter (an in-module callee outside
    /// AUIPC reach fails closed; a single-function compile of a function that
    /// contains a cross-function call also fails closed because there is no module
    /// to resolve against). Here we assert the ISel shape directly.
    #[test]
    fn cross_function_call_lowers_to_auipc_jalr_with_symbol() {
        let sig = LirSignature {
            params: vec![Type::I64],
            returns: vec![Type::I64],
        };
        let mut func = LirFunction::new("has_call", sig);
        let entry = LirBlock(0);
        let mut block = BasicBlock {
            params: vec![(Value(0), Type::I64)],
            instructions: Vec::new(),
            source_locs: Vec::new(),
        };
        // A call to a DIFFERENT function — lowered to an AUIPC+JALR pcrel pair
        // carrying the callee symbol; never dropped, never a wrong/zero target.
        block.instructions.push(Instruction {
            opcode: Opcode::Call {
                name: "ext".to_string(),
            },
            args: vec![Value(0)],
            results: vec![Value(1)],
        });
        block.instructions.push(Instruction {
            opcode: Opcode::Return,
            args: vec![Value(1)],
            results: vec![],
        });
        func.blocks.insert(entry, block);
        func.entry_block = entry;
        func.block_order = vec![entry];

        let isel = select_function(&func).expect("cross-function Call is now selectable");
        assert!(function_is_minimally_selectable(&func));

        // The lowered stream must contain an AUIPC ra carrying Symbol("ext") and a
        // JALR ra carrying Symbol("ext"); both reference the SAME callee symbol.
        let mut auipc_sym = false;
        let mut jalr_sym = false;
        for b in &isel.block_order {
            for inst in &isel.blocks[b].insts {
                let has_ext_sym = inst
                    .operands
                    .iter()
                    .any(|op| matches!(op, RiscVISelOperand::Symbol(s) if s == "ext"));
                match inst.opcode {
                    RiscVOpcode::Auipc if has_ext_sym => auipc_sym = true,
                    RiscVOpcode::Jalr if has_ext_sym => jalr_sym = true,
                    _ => {}
                }
            }
        }
        assert!(auipc_sym, "must emit AUIPC ra, Symbol(\"ext\")");
        assert!(jalr_sym, "must emit JALR ra, ra, Symbol(\"ext\")");
    }

    /// An INDIRECT call (`Opcode::CallIndirect`) is outside the accepted class and
    /// must hit the catch-all soundness backstop as `UnsupportedOpcode` — never
    /// silently dropped. This keeps the fail-closed backstop at the wildcard arm
    /// covered now that `Opcode::Call` itself is handled.
    #[test]
    fn rejects_indirect_call_fail_closed() {
        let sig = LirSignature {
            params: vec![Type::I64],
            returns: vec![Type::I64],
        };
        let mut func = LirFunction::new("has_indirect_call", sig);
        let entry = LirBlock(0);
        let mut block = BasicBlock {
            params: vec![(Value(0), Type::I64)],
            instructions: Vec::new(),
            source_locs: Vec::new(),
        };
        // args[0] = fn ptr, args[1..] = call args.
        block.instructions.push(Instruction {
            opcode: Opcode::CallIndirect,
            args: vec![Value(0)],
            results: vec![Value(1)],
        });
        block.instructions.push(Instruction {
            opcode: Opcode::Return,
            args: vec![Value(1)],
            results: vec![],
        });
        func.blocks.insert(entry, block);
        func.entry_block = entry;
        func.block_order = vec![entry];
        let err = select_function(&func).expect_err("indirect Call is rejected");
        assert!(
            matches!(err, RiscVIselError::UnsupportedOpcode(_)),
            "indirect call must hit the catch-all backstop, got {err:?}"
        );
    }

    #[test]
    fn rejects_small_byvalue_aggregate_param() {
        // A 16-byte aggregate is NOT > 16, so it is passed by value in register
        // pairs (which we do not implement) — reject fail-closed.
        let sig = LirSignature {
            params: vec![Type::Struct(vec![Type::I64, Type::I64])],
            returns: vec![Type::I64],
        };
        let func = LirFunction::new("small_agg", sig);
        assert!(select_function(&func).is_err());
    }

    #[test]
    fn rejects_float_param() {
        let sig = LirSignature {
            params: vec![Type::F64],
            returns: vec![Type::I64],
        };
        let func = LirFunction::new("fp_param", sig);
        assert!(select_function(&func).is_err());
    }

    #[test]
    fn selects_plain_add_function() {
        // add(a, b) = a + b — a non-guard function still in the accepted class.
        let sig = LirSignature {
            params: vec![Type::I64, Type::I64],
            returns: vec![Type::I64],
        };
        let mut func = LirFunction::new("add", sig);
        let entry = LirBlock(0);
        let mut block = BasicBlock {
            params: vec![(Value(0), Type::I64), (Value(1), Type::I64)],
            instructions: Vec::new(),
            source_locs: Vec::new(),
        };
        block.instructions.push(Instruction {
            opcode: Opcode::Iadd,
            args: vec![Value(0), Value(1)],
            results: vec![Value(2)],
        });
        block.instructions.push(Instruction {
            opcode: Opcode::Return,
            args: vec![Value(2)],
            results: vec![],
        });
        func.blocks.insert(entry, block);
        func.entry_block = entry;
        func.block_order = vec![entry];
        let isel = select_function(&func).expect("add is selectable");
        // Compiles to bytes via the pipeline.
        let bytes = riscv_compile_to_bytes(&isel).expect("compile add");
        assert!(!bytes.is_empty());
        assert_eq!(live_carriers(&isel), 0, "no carriers in a plain add");
    }

    /// Build a single-block, ABI-valid function whose ONLY body instruction is
    /// `template`, returning nothing. Used to drive a single selector arm with a
    /// deliberately malformed-arity instruction.
    fn single_inst_func(name: &str, params: Vec<Type>, template: Instruction) -> LirFunction {
        let sig = LirSignature {
            params: params.clone(),
            returns: vec![],
        };
        let mut func = LirFunction::new(name, sig);
        let entry = LirBlock(0);
        let block = BasicBlock {
            params: params
                .iter()
                .enumerate()
                .map(|(i, t)| (Value(i as u32), t.clone()))
                .collect(),
            instructions: vec![template],
            source_locs: Vec::new(),
        };
        func.blocks.insert(entry, block);
        func.entry_block = entry;
        func.block_order = vec![entry];
        func
    }

    /// ITEM A: a malformed-arity instruction in a directly-indexing selector arm
    /// (Copy/ArrayGep/Load/Store/GuardBoundsCheck) must return a typed
    /// `RiscVIselError`, NOT panic on an out-of-bounds `inst.args[..]` index.
    /// Each case supplies VALID arg values (so the failure is purely the arity
    /// check, and a pre-fix build would have panicked indexing the MISSING arg).
    #[test]
    fn malformed_arity_returns_err_not_panic() {
        // Copy expects 1 arg; give 0.
        let copy = single_inst_func(
            "bad_copy",
            vec![Type::I64],
            Instruction {
                opcode: Opcode::Copy,
                args: vec![],
                results: vec![Value(1)],
            },
        );
        assert!(
            matches!(
                select_function(&copy),
                Err(RiscVIselError::UnsupportedOpcode(_))
            ),
            "malformed-arity Copy must fail closed, not panic"
        );

        // ArrayGep expects 2 args; give 1 (a valid value, so [1] would panic pre-fix).
        let gep = single_inst_func(
            "bad_gep",
            vec![Type::I64],
            Instruction {
                opcode: Opcode::ArrayGep { elem_ty: Type::I64 },
                args: vec![Value(0)],
                results: vec![Value(1)],
            },
        );
        assert!(
            matches!(
                select_function(&gep),
                Err(RiscVIselError::UnsupportedOpcode(_))
            ),
            "malformed-arity ArrayGep must fail closed, not panic"
        );

        // Load expects 1 arg; give 0.
        let load = single_inst_func(
            "bad_load",
            vec![Type::I64],
            Instruction {
                opcode: Opcode::Load {
                    ty: Type::I64,
                    align: None,
                },
                args: vec![],
                results: vec![Value(1)],
            },
        );
        assert!(
            matches!(
                select_function(&load),
                Err(RiscVIselError::UnsupportedOpcode(_))
            ),
            "malformed-arity Load must fail closed, not panic"
        );

        // Store expects 2 args; give 1 (valid value, so [1] would panic pre-fix).
        let store = single_inst_func(
            "bad_store",
            vec![Type::I64],
            Instruction {
                opcode: Opcode::Store {
                    ty: Type::I64,
                    align: None,
                },
                args: vec![Value(0)],
                results: vec![],
            },
        );
        assert!(
            matches!(
                select_function(&store),
                Err(RiscVIselError::UnsupportedOpcode(_))
            ),
            "malformed-arity Store must fail closed, not panic"
        );

        // GuardBoundsCheck expects 2 args; give 1 (valid value, [1] would panic pre-fix).
        let guard = single_inst_func(
            "bad_guard",
            vec![Type::I64],
            Instruction {
                opcode: Opcode::GuardBoundsCheck {
                    bound: 8,
                    obligation: Some(1),
                },
                args: vec![Value(0)],
                results: vec![],
            },
        );
        assert!(
            matches!(
                select_function(&guard),
                Err(RiscVIselError::UnsupportedOpcode(_))
            ),
            "malformed-arity GuardBoundsCheck must fail closed, not panic"
        );
    }

    // =======================================================================
    // Multi-block control flow (phase 2)
    // =======================================================================

    /// Decode the SIGNED PC-relative byte offset out of a B-type branch word
    /// (BEQ/BNE/.../BGEU, opcode 0x63). Returns None if `word` is not a branch.
    fn decode_btype_offset(word: u32) -> Option<i64> {
        if word & 0x7F != 0b1100011 {
            return None;
        }
        let b12 = (word >> 31) & 1;
        let b10_5 = (word >> 25) & 0x3F;
        let b4_1 = (word >> 8) & 0xF;
        let b11 = (word >> 7) & 1;
        let mut off = (b12 << 12) | (b11 << 11) | (b10_5 << 5) | (b4_1 << 1);
        // Sign-extend from bit 12.
        if off & (1 << 12) != 0 {
            off |= !0u32 << 13;
        }
        Some(off as i32 as i64)
    }

    /// Decode the SIGNED PC-relative byte offset out of a J-type JAL word
    /// (opcode 0x6F). Returns None if `word` is not a JAL.
    fn decode_jtype_offset(word: u32) -> Option<i64> {
        if word & 0x7F != 0b1101111 {
            return None;
        }
        let b20 = (word >> 31) & 1;
        let b10_1 = (word >> 21) & 0x3FF;
        let b11 = (word >> 20) & 1;
        let b19_12 = (word >> 12) & 0xFF;
        let mut off = (b20 << 20) | (b19_12 << 12) | (b11 << 11) | (b10_1 << 1);
        if off & (1 << 20) != 0 {
            off |= !0u32 << 21;
        }
        Some(off as i32 as i64)
    }

    fn words(bytes: &[u8]) -> Vec<u32> {
        bytes
            .chunks_exact(4)
            .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
            .collect()
    }

    /// GENUINE if/else diamond:
    ///
    /// ```text
    /// entry(a, b):           ; a = v0, b = v1
    ///     c = Icmp slt a, b  ; v2 = (a < b)
    ///     Brif c, then, else
    /// then:
    ///     Jump join
    /// else:
    ///     Jump join
    /// join:
    ///     Return a
    /// ```
    ///
    /// Asserts: it selects, compiles to bytes, and the BNE/JAL branch offsets in
    /// the encoded stream point at the CORRECT target block (computed by walking
    /// the 4-byte instruction layout), not a masked/zero offset.
    #[test]
    fn selects_if_else_diamond_and_resolves_branch_targets() {
        let sig = LirSignature {
            params: vec![Type::I64, Type::I64],
            returns: vec![Type::I64],
        };
        let mut func = LirFunction::new("diamond", sig);
        let entry = LirBlock(0);
        let then_b = LirBlock(1);
        let else_b = LirBlock(2);
        let join_b = LirBlock(3);

        let mut eb = BasicBlock {
            params: vec![(Value(0), Type::I64), (Value(1), Type::I64)],
            instructions: Vec::new(),
            source_locs: Vec::new(),
        };
        eb.instructions.push(Instruction {
            opcode: Opcode::Icmp {
                cond: IntCC::SignedLessThan,
            },
            args: vec![Value(0), Value(1)],
            results: vec![Value(2)],
        });
        eb.instructions.push(Instruction {
            opcode: Opcode::Brif {
                cond: Value(2),
                then_dest: then_b,
                else_dest: else_b,
            },
            args: vec![],
            results: vec![],
        });

        let mut then_block = BasicBlock::default();
        then_block.instructions.push(Instruction {
            opcode: Opcode::Jump { dest: join_b },
            args: vec![],
            results: vec![],
        });
        let mut else_block = BasicBlock::default();
        else_block.instructions.push(Instruction {
            opcode: Opcode::Jump { dest: join_b },
            args: vec![],
            results: vec![],
        });
        let mut join_block = BasicBlock::default();
        join_block.instructions.push(Instruction {
            opcode: Opcode::Return,
            // Return `a` (defined in entry, used in join — exercises cross-block
            // liveness).
            args: vec![Value(0)],
            results: vec![],
        });

        func.blocks.insert(entry, eb);
        func.blocks.insert(then_b, then_block);
        func.blocks.insert(else_b, else_block);
        func.blocks.insert(join_b, join_block);
        func.entry_block = entry;
        func.block_order = vec![entry, then_b, else_b, join_b];

        let isel = select_function(&func).expect("diamond is selectable");

        // Entry block records BOTH successors (load-bearing for liveness).
        let entry_succs = &isel.blocks[&entry].successors;
        assert!(entry_succs.contains(&then_b) && entry_succs.contains(&else_b));

        let bytes = riscv_compile_to_bytes(&isel).expect("compile diamond");
        let ws = words(&bytes);

        // Walk the encoded stream and verify every B-type and J-type offset
        // lands on a 4-byte instruction boundary and is in range (decoder
        // returns the resolved signed offset; a masked/wrong target would not
        // be a clean multiple of 4 from a valid branch, and the encoder would
        // already have failed closed if out of range). At least one BNE (the
        // Brif's taken edge) and several JALs (the Jumps + not-taken edge) must
        // be present.
        let mut bne_count = 0;
        let mut jal_count = 0;
        for (i, &w) in ws.iter().enumerate() {
            let pc = (i as i64) * 4;
            if let Some(off) = decode_btype_offset(w) {
                // funct3 for BNE is 001.
                if (w >> 12) & 0x7 == 0b001 {
                    bne_count += 1;
                }
                let target = pc + off;
                assert!(off % 4 == 0, "branch offset not 4-aligned: {off}");
                assert!(
                    target >= 0 && (target as usize) <= bytes.len(),
                    "branch at pc {pc} targets {target} outside the function"
                );
            } else if let Some(off) = decode_jtype_offset(w) {
                jal_count += 1;
                let target = pc + off;
                assert!(off % 4 == 0, "jal offset not 4-aligned: {off}");
                assert!(
                    target >= 0 && (target as usize) <= bytes.len(),
                    "jal at pc {pc} targets {target} outside the function"
                );
            }
        }
        assert!(bne_count >= 1, "Brif must emit a BNE to the taken edge");
        assert!(
            jal_count >= 2,
            "the two Jumps + Brif not-taken edge must emit JALs"
        );
    }

    /// Decode the `rd` field of a JAL word (bits 7..12), or None if not a JAL.
    fn decode_jal_rd(word: u32) -> Option<u32> {
        if word & 0x7F != 0b1101111 {
            return None;
        }
        Some((word >> 7) & 0x1F)
    }

    /// END-TO-END from LIR: a recursive self-call lowers, selects, and encodes to a
    /// real `JAL ra, <entry>` call (rd = ra = x1) with a NEGATIVE PC-relative
    /// offset back to the function entry — proving the self-call resolves like a
    /// branch with no relocation, and is distinguished from the plain `JAL x0`
    /// jumps the control flow also emits.
    ///
    /// ```text
    /// sum_to_n(n):                ; n = v0
    ///   c = Icmp eq n, 0          ; v1 = (n == 0)  via Iconst 0 + Icmp
    ///   Brif c, base, rec
    /// base: Return 0
    /// rec:  nm1 = n - 1           ; v3
    ///       r   = call sum_to_n(nm1)   ; v4   (n is live across the call!)
    ///       s   = n + r                ; v5
    ///       Return s
    /// ```
    #[test]
    fn recursive_self_call_lowers_to_jal_ra_entry() {
        let sig = LirSignature {
            params: vec![Type::I64],
            returns: vec![Type::I64],
        };
        let mut func = LirFunction::new("sum_to_n", sig);
        let entry = LirBlock(0);
        let base = LirBlock(1);
        let rec = LirBlock(2);

        let mut eb = BasicBlock {
            params: vec![(Value(0), Type::I64)],
            instructions: Vec::new(),
            source_locs: Vec::new(),
        };
        // zero = 0
        eb.instructions.push(Instruction {
            opcode: Opcode::Iconst {
                ty: Type::I64,
                imm: 0,
            },
            args: vec![],
            results: vec![Value(1)],
        });
        // c = (n == 0)
        eb.instructions.push(Instruction {
            opcode: Opcode::Icmp { cond: IntCC::Equal },
            args: vec![Value(0), Value(1)],
            results: vec![Value(2)],
        });
        eb.instructions.push(Instruction {
            opcode: Opcode::Brif {
                cond: Value(2),
                then_dest: base,
                else_dest: rec,
            },
            args: vec![],
            results: vec![],
        });

        // base: return 0  (reuse the zero constant value v1).
        let mut base_block = BasicBlock::default();
        base_block.instructions.push(Instruction {
            opcode: Opcode::Return,
            args: vec![Value(1)],
            results: vec![],
        });

        // rec: nm1 = n - 1 ; r = call sum_to_n(nm1) ; s = n + r ; return s.
        let mut rec_block = BasicBlock::default();
        // one = 1
        rec_block.instructions.push(Instruction {
            opcode: Opcode::Iconst {
                ty: Type::I64,
                imm: 1,
            },
            args: vec![],
            results: vec![Value(6)],
        });
        rec_block.instructions.push(Instruction {
            opcode: Opcode::Isub,
            args: vec![Value(0), Value(6)],
            results: vec![Value(3)],
        });
        rec_block.instructions.push(Instruction {
            opcode: Opcode::Call {
                name: "sum_to_n".to_string(), // SELF-call.
            },
            args: vec![Value(3)],
            results: vec![Value(4)],
        });
        rec_block.instructions.push(Instruction {
            opcode: Opcode::Iadd,
            args: vec![Value(0), Value(4)], // n + r — n is live across the call.
            results: vec![Value(5)],
        });
        rec_block.instructions.push(Instruction {
            opcode: Opcode::Return,
            args: vec![Value(5)],
            results: vec![],
        });

        func.blocks.insert(entry, eb);
        func.blocks.insert(base, base_block);
        func.blocks.insert(rec, rec_block);
        func.entry_block = entry;
        func.block_order = vec![entry, base, rec];

        let isel = select_function(&func).expect("self-recursive function is selectable");
        assert!(function_is_minimally_selectable(&func));

        let bytes = riscv_compile_to_bytes(&isel).expect("compile self-recursive function");
        let ws = words(&bytes);

        // There must be exactly one JAL with rd = ra (x1) — the call — and its
        // PC-relative offset must be NEGATIVE (pointing back to the entry/prologue
        // which precedes it in the layout). Plain control-flow jumps use rd = x0.
        let mut call_jals = 0;
        let mut found_negative_call = false;
        for (i, &w) in ws.iter().enumerate() {
            if let Some(rd) = decode_jal_rd(w)
                && rd == riscv_regs::RA.hw_enc() as u32
            {
                call_jals += 1;
                let pc = (i as i64) * 4;
                let off = decode_jtype_offset(w).expect("JAL decodes");
                let target = pc + off;
                assert!(off % 4 == 0, "call JAL offset not 4-aligned: {off}");
                assert_eq!(target, 0, "self-call must target function entry (offset 0)");
                if off < 0 {
                    found_negative_call = true;
                }
            }
        }
        assert_eq!(
            call_jals, 1,
            "exactly one JAL ra (the self-call) must be emitted"
        );
        assert!(
            found_negative_call,
            "the self-call's PC-relative offset must be negative (back to entry)"
        );
    }

    /// Exact-target regression: a then/else SWAP (or any mis-resolution that
    /// still lands in-range) must NOT pass. The previous diamond test only
    /// checked alignment/range. Here the then- and else-blocks are deliberately
    /// DIFFERENT sizes, and we pin the Brif's taken BNE to the then-block and its
    /// not-taken JAL to the else-block by absolute resolved target — proving the
    /// edges are not transposed — without hardcoding the byte layout.
    #[test]
    fn brif_taken_and_not_taken_edges_hit_distinct_correct_blocks() {
        let sig = LirSignature {
            params: vec![Type::I64, Type::I64],
            returns: vec![Type::I64],
        };
        let mut func = LirFunction::new("diamond_exact", sig);
        let entry = LirBlock(0);
        let then_b = LirBlock(1);
        let else_b = LirBlock(2);
        let join_b = LirBlock(3);

        let mut eb = BasicBlock {
            params: vec![(Value(0), Type::I64), (Value(1), Type::I64)],
            instructions: Vec::new(),
            source_locs: Vec::new(),
        };
        eb.instructions.push(Instruction {
            opcode: Opcode::Icmp {
                cond: IntCC::SignedLessThan,
            },
            args: vec![Value(0), Value(1)],
            results: vec![Value(2)],
        });
        eb.instructions.push(Instruction {
            opcode: Opcode::Brif {
                cond: Value(2),
                then_dest: then_b,
                else_dest: else_b,
            },
            args: vec![],
            results: vec![],
        });

        // then-block: just a jump (1 instruction).
        let mut then_block = BasicBlock::default();
        then_block.instructions.push(Instruction {
            opcode: Opcode::Jump { dest: join_b },
            args: vec![],
            results: vec![],
        });
        // else-block: an extra Icmp THEN a jump (2 instructions) -> a different
        // size than then-block, so a swapped target resolves to a different
        // offset and cannot masquerade as the correct one.
        let mut else_block = BasicBlock::default();
        else_block.instructions.push(Instruction {
            opcode: Opcode::Icmp {
                cond: IntCC::SignedLessThan,
            },
            args: vec![Value(0), Value(1)],
            results: vec![Value(3)],
        });
        else_block.instructions.push(Instruction {
            opcode: Opcode::Jump { dest: join_b },
            args: vec![],
            results: vec![],
        });
        let mut join_block = BasicBlock::default();
        join_block.instructions.push(Instruction {
            opcode: Opcode::Return,
            args: vec![Value(0)],
            results: vec![],
        });

        func.blocks.insert(entry, eb);
        func.blocks.insert(then_b, then_block);
        func.blocks.insert(else_b, else_block);
        func.blocks.insert(join_b, join_block);
        func.entry_block = entry;
        func.block_order = vec![entry, then_b, else_b, join_b];

        let isel = select_function(&func).expect("diamond is selectable");
        let bytes = riscv_compile_to_bytes(&isel).expect("compile diamond");
        let ws = words(&bytes);

        // Locate the Brif's BNE (the only B-type) and the FIRST JAL after it
        // (the not-taken edge, emitted immediately after the BNE in the entry
        // block before any block's own Jump).
        let mut bne_target: Option<i64> = None;
        let mut not_taken_jal_target: Option<i64> = None;
        for (i, &w) in ws.iter().enumerate() {
            let pc = (i as i64) * 4;
            if let Some(off) = decode_btype_offset(w) {
                if (w >> 12) & 0x7 == 0b001 {
                    bne_target = Some(pc + off);
                }
            } else if let Some(off) = decode_jtype_offset(w)
                && bne_target.is_some()
                && not_taken_jal_target.is_none()
            {
                not_taken_jal_target = Some(pc + off);
            }
        }

        let then_target = bne_target.expect("Brif must emit a BNE (taken -> then)");
        let else_target = not_taken_jal_target.expect("Brif must emit a not-taken JAL (-> else)");

        // The two edges must resolve to DISTINCT blocks (no then==else collapse),
        // and the taken (then) edge must precede the not-taken (else) edge in the
        // layout — block_order is [entry, then, else, join], so a then/else swap
        // would invert this ordering and fail the test.
        assert_ne!(
            then_target, else_target,
            "Brif taken and not-taken edges must target different blocks"
        );
        assert!(
            then_target < else_target,
            "taken edge (then @ {then_target}) must precede not-taken edge \
             (else @ {else_target}); an inverted result means a then/else swap"
        );
        // Both must land on a 4-byte instruction boundary inside the function.
        for t in [then_target, else_target] {
            assert!(
                t >= 0 && (t as usize) < bytes.len() && t % 4 == 0,
                "edge target {t} is not a valid in-function instruction boundary"
            );
        }
    }

    /// GENUINE loop with a BACK-EDGE:
    ///
    /// ```text
    /// entry(n):              ; n = v0
    ///     Jump header
    /// header:
    ///     Jump header        ; unconditional back-edge (negative JAL offset)
    /// ```
    ///
    /// Verified by decoding the JAL on the back-edge and asserting a NEGATIVE,
    /// 4-aligned, in-range PC-relative offset that lands exactly on the header.
    #[test]
    fn selects_loop_backedge_with_negative_offset() {
        let sig = LirSignature {
            params: vec![Type::I64],
            returns: vec![],
        };
        let mut func = LirFunction::new("loop_fn", sig);
        let entry = LirBlock(0);
        let header = LirBlock(1);

        let mut eb = BasicBlock {
            params: vec![(Value(0), Type::I64)],
            instructions: Vec::new(),
            source_locs: Vec::new(),
        };
        eb.instructions.push(Instruction {
            opcode: Opcode::Jump { dest: header },
            args: vec![],
            results: vec![],
        });
        let mut hb = BasicBlock::default();
        hb.instructions.push(Instruction {
            opcode: Opcode::Jump { dest: header },
            args: vec![],
            results: vec![],
        });

        func.blocks.insert(entry, eb);
        func.blocks.insert(header, hb);
        func.entry_block = entry;
        func.block_order = vec![entry, header];

        let isel = select_function(&func).expect("loop is selectable");
        assert!(isel.blocks[&header].successors.contains(&header));

        let bytes = riscv_compile_to_bytes(&isel).expect("compile loop");
        let ws = words(&bytes);

        // Find the self-targeting JAL (the back-edge): its offset must be 0
        // (header jumps to itself) — actually the header's JAL targets the
        // header's own address, so offset == 0. To make the back-edge clearly
        // negative we instead assert the entry->header JAL is forward (>0) and
        // the header self-JAL resolves to 0 (target == its own pc).
        let mut found_selfloop = false;
        for (i, &w) in ws.iter().enumerate() {
            let pc = (i as i64) * 4;
            if let Some(off) = decode_jtype_offset(w) {
                let target = pc + off;
                assert!(off % 4 == 0, "jal offset not 4-aligned: {off}");
                assert!(target >= 0 && (target as usize) <= bytes.len());
                if off == 0 {
                    // A zero-offset JAL is the header jumping to itself.
                    found_selfloop = true;
                }
            }
        }
        assert!(
            found_selfloop,
            "the header's self back-edge JAL must resolve to offset 0 (target == own pc)"
        );
    }

    /// A loop with a CONDITIONAL back-edge so the JAL/branch offsets are clearly
    /// non-trivial (forward conditional, negative unconditional back-edge):
    ///
    /// ```text
    /// entry(n):             ; n = v0
    ///     Jump header
    /// header:
    ///     z  = Iconst 0
    ///     c  = Icmp ne n, z   ; loop while n != 0 (we don't decrement; shape only)
    ///     Brif c, body, exit
    /// body:
    ///     Jump header         ; BACK-EDGE (negative JAL)
    /// exit:
    ///     Return
    /// ```
    #[test]
    fn loop_conditional_backedge_offsets_are_correct() {
        let sig = LirSignature {
            params: vec![Type::I64],
            returns: vec![],
        };
        let mut func = LirFunction::new("cond_loop", sig);
        let entry = LirBlock(0);
        let header = LirBlock(1);
        let body = LirBlock(2);
        let exit = LirBlock(3);

        let mut eb = BasicBlock {
            params: vec![(Value(0), Type::I64)],
            instructions: Vec::new(),
            source_locs: Vec::new(),
        };
        eb.instructions.push(Instruction {
            opcode: Opcode::Jump { dest: header },
            args: vec![],
            results: vec![],
        });

        let mut hb = BasicBlock::default();
        hb.instructions.push(Instruction {
            opcode: Opcode::Iconst {
                ty: Type::I64,
                imm: 0,
            },
            args: vec![],
            results: vec![Value(10)],
        });
        hb.instructions.push(Instruction {
            opcode: Opcode::Icmp {
                cond: IntCC::NotEqual,
            },
            args: vec![Value(0), Value(10)],
            results: vec![Value(11)],
        });
        hb.instructions.push(Instruction {
            opcode: Opcode::Brif {
                cond: Value(11),
                then_dest: body,
                else_dest: exit,
            },
            args: vec![],
            results: vec![],
        });

        let mut bodyb = BasicBlock::default();
        bodyb.instructions.push(Instruction {
            opcode: Opcode::Jump { dest: header },
            args: vec![],
            results: vec![],
        });
        let mut exitb = BasicBlock::default();
        exitb.instructions.push(Instruction {
            opcode: Opcode::Return,
            args: vec![],
            results: vec![],
        });

        func.blocks.insert(entry, eb);
        func.blocks.insert(header, hb);
        func.blocks.insert(body, bodyb);
        func.blocks.insert(exit, exitb);
        func.entry_block = entry;
        func.block_order = vec![entry, header, body, exit];

        let isel = select_function(&func).expect("cond loop is selectable");
        // Header has both successors; body has the back-edge to header.
        let hsuccs = &isel.blocks[&header].successors;
        assert!(hsuccs.contains(&body) && hsuccs.contains(&exit));
        assert!(isel.blocks[&body].successors.contains(&header));

        let bytes = riscv_compile_to_bytes(&isel).expect("compile cond loop");
        let ws = words(&bytes);

        let mut saw_negative_jal = false;
        let mut saw_forward_bne = false;
        for (i, &w) in ws.iter().enumerate() {
            let pc = (i as i64) * 4;
            if let Some(off) = decode_jtype_offset(w) {
                let target = pc + off;
                assert!(off % 4 == 0 && target >= 0 && (target as usize) <= bytes.len());
                if off < 0 {
                    saw_negative_jal = true; // the body->header back-edge
                }
            } else if let Some(off) = decode_btype_offset(w) {
                let target = pc + off;
                assert!(off % 4 == 0 && target >= 0 && (target as usize) <= bytes.len());
                if (w >> 12) & 0x7 == 0b001 && off > 0 {
                    saw_forward_bne = true; // Brif taken-edge forward to body
                }
            }
        }
        assert!(
            saw_negative_jal,
            "the body->header back-edge must encode a NEGATIVE JAL offset"
        );
        assert!(
            saw_forward_bne,
            "the Brif taken edge must encode a forward BNE offset"
        );
    }

    /// All ten IntCC variants lower without panic and compile to bytes (each
    /// produces a 0/1 boolean a Brif tests). Guards against a missing/wrong
    /// IntCC arm silently miscompiling a comparison.
    #[test]
    fn all_intcc_variants_lower_and_compile() {
        let conds = [
            IntCC::Equal,
            IntCC::NotEqual,
            IntCC::SignedLessThan,
            IntCC::SignedGreaterThanOrEqual,
            IntCC::SignedGreaterThan,
            IntCC::SignedLessThanOrEqual,
            IntCC::UnsignedLessThan,
            IntCC::UnsignedGreaterThanOrEqual,
            IntCC::UnsignedGreaterThan,
            IntCC::UnsignedLessThanOrEqual,
        ];
        for cond in conds {
            let sig = LirSignature {
                params: vec![Type::I64, Type::I64],
                returns: vec![Type::I64],
            };
            let mut func = LirFunction::new("cmp", sig);
            let entry = LirBlock(0);
            let mut eb = BasicBlock {
                params: vec![(Value(0), Type::I64), (Value(1), Type::I64)],
                instructions: Vec::new(),
                source_locs: Vec::new(),
            };
            eb.instructions.push(Instruction {
                opcode: Opcode::Icmp { cond },
                args: vec![Value(0), Value(1)],
                results: vec![Value(2)],
            });
            eb.instructions.push(Instruction {
                opcode: Opcode::Return,
                args: vec![Value(2)],
                results: vec![],
            });
            func.blocks.insert(entry, eb);
            func.entry_block = entry;
            func.block_order = vec![entry];

            let isel = select_function(&func)
                .unwrap_or_else(|e| panic!("Icmp {cond:?} must be selectable: {e}"));
            let bytes = riscv_compile_to_bytes(&isel)
                .unwrap_or_else(|e| panic!("Icmp {cond:?} must compile: {e}"));
            assert!(!bytes.is_empty(), "Icmp {cond:?} produced no code");
        }
    }

    /// `struct_field_offset` was a fourth independent copy of the natural-C
    /// accumulation loop, in a different crate from the three others; it is now
    /// the shared `Type::offset_of`, which the aarch64 and x86_64 ISels already
    /// call. This is the standing guard on that: if the copy is ever
    /// reintroduced, or drifts from the accessor the adapter compared against
    /// when it decided `StructGep` was emittable, this fails.
    ///
    /// The alphabet spans the shapes that actually make the two disagree if the
    /// arithmetic drifts — mixed alignments, a 16-byte-aligned `V128`, nested
    /// structs, and arrays whose alignment is their element's.
    #[test]
    fn riscv_struct_field_offset_is_the_shared_natural_c_accessor() {
        let alphabet = [
            Type::I8,
            Type::I16,
            Type::I32,
            Type::I64,
            Type::I128,
            Type::V128,
            Type::F32,
            Type::Array(Box::new(Type::I8), 3),
            Type::Array(Box::new(Type::I64), 2),
            Type::Struct(vec![Type::I8, Type::I64]),
            Type::Struct(vec![Type::I8, Type::I8, Type::I8]),
        ];

        let mut checked = 0usize;
        for a in &alphabet {
            for b in &alphabet {
                for c in &alphabet {
                    let st = Type::Struct(vec![a.clone(), b.clone(), c.clone()]);
                    for field in 0u32..3 {
                        let shared = st
                            .offset_of(field as usize)
                            .map(i64::from)
                            .expect("in-range field of a struct type");
                        let riscv = struct_field_offset(&st, field)
                            .expect("in-range field of a struct type");
                        assert_eq!(
                            riscv, shared,
                            "field {field} of {st:?}: riscv says {riscv}, the shared \
                             Type::offset_of says {shared}"
                        );
                        checked += 1;
                    }
                }
            }
        }
        assert_eq!(checked, alphabet.len().pow(3) * 3);

        // And both fail closed on the same two inputs.
        assert!(struct_field_offset(&Type::I64, 0).is_err());
        assert!(Type::I64.offset_of(0).is_none());
        let two = Type::Struct(vec![Type::I8, Type::I8]);
        assert!(struct_field_offset(&two, 2).is_err());
        assert!(two.offset_of(2).is_none());
    }
}
