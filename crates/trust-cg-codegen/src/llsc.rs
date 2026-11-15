// trust-cg-codegen/llsc.rs - Post-RA expansion of AArch64 LL/SC atomics
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Post-register-allocation expansion of the opaque LL/SC atomic pseudos.
//!
//! Baseline armv8.0 (no FEAT_LSE) implements atomic read-modify-write and
//! compare-and-swap with load-exclusive / store-exclusive retry loops. The
//! architecture only guarantees forward progress for such a loop when no
//! other explicit memory access sits between the load-exclusive and the
//! store-exclusive, so the loop must never contain a spill or reload. The
//! backend therefore mirrors LLVM's `CMP_SWAP_*` / `ATOMIC_*` pseudo design:
//!
//! 1. ISel selects one opaque `LlscRmw{8,16,32,64}` / `LlscCmpSwap{8,16,32,64}`
//!    instruction (operand layout in [`trust_cg_ir::llsc`]). Every register the
//!    loop writes is an explicit definition, and every definition interferes
//!    with every use at the same instruction, so the allocator assigns
//!    pairwise-distinct registers.
//! 2. Register allocation, spill materialization and frame lowering see only
//!    that single instruction; any spill or reload lands before or after it.
//!    This is the whole-window spill strategy: spill materialization gives
//!    every spilled operand its own register for the whole loop (X16/X17 for
//!    uses first, then an allocatable register that is not an operand, saved
//!    to an emergency slot before and restored after the pseudo when it is
//!    live), so each value live across the loop is in a register or in
//!    memory outside the window.
//! 3. [`expand_llsc_atomics`] then rewrites the pseudo in place into the fixed
//!    loop below, re-validating every register-distinctness precondition and
//!    failing closed with `[TCG-LLSC-EXPAND]` instead of emitting a loop that
//!    could clobber a value it re-reads.
//! 4. [`check_exclusive_windows`] refuses, after expansion and again on the
//!    final stream at encoding, any spill access (`[TCG-LLSC-SPILL-WINDOW]`)
//!    or other memory access or call (`[TCG-LLSC-WINDOW]`) between a
//!    load-exclusive and the next store-exclusive or `CLREX` on any path.
//!
//! Read-modify-write (`op` is one ALU step, or none for exchange):
//!
//! ```text
//! loop: LD{A}XR{B,H} old, [addr]
//!       <op>         new, old, value
//!       ST{L}XR{B,H} status, new, [addr]
//!       CBNZ         status, loop
//! ```
//!
//! Compare-and-swap:
//!
//! ```text
//! loop: LD{A}XR{B,H} old, [addr]
//!       UXT{B,H}     status, expected      ; byte/halfword only
//!       CMP          old, expected|status
//!       B.NE         fail
//!       ST{L}XR{B,H} status, desired, [addr]
//!       CBNZ         status, loop
//!       B.EQ         done                  ; NZCV is still EQ from the CMP
//! fail: CLREX
//! done:
//! ```
//!
//! The success exit uses `B.EQ` rather than `B` so the block keeps no
//! unconditional terminator in its middle: neither the store-exclusive nor
//! `CBNZ` writes NZCV, so the branch is always taken on the success path.
//! [`llsc_internal_branches`] recognizes exactly these templates in a
//! resolved stream so final CFG reconstruction accepts their intra-block
//! branches and rejects every other intra-block branch target.
//!
//! Evidence boundary: this is an implementation with encoder/decoder, decode
//! check and native differential tests. It is not an exclusive-monitor,
//! ordering, linearizability or progress proof; the pseudos and exclusives are
//! RED rows in the opcode coverage gate.

use std::collections::{BTreeMap, BTreeSet};

use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_ir::llsc::{
    LLSC_CAS_ADDR_OPERAND, LLSC_CAS_DESIRED_OPERAND, LLSC_CAS_EXPECTED_OPERAND,
    LLSC_CAS_OLD_OPERAND, LLSC_CAS_ORDERING_OPERAND, LLSC_CAS_STATUS_OPERAND,
    LLSC_RMW_ADDR_OPERAND, LLSC_RMW_NEW_OPERAND, LLSC_RMW_OLD_OPERAND, LLSC_RMW_OP_OPERAND,
    LLSC_RMW_ORDERING_OPERAND, LLSC_RMW_STATUS_OPERAND, LLSC_RMW_VALUE_OPERAND, LlscOrdering,
    LlscPseudo, LlscRmwOp, LlscWidth, exclusive_load_opcode, exclusive_store_opcode,
    is_exclusive_load, is_exclusive_pair, is_exclusive_store,
};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::{PReg, RegClass, SpecialReg, preg_class};
use trust_cg_ir::{CondCode, InstId, MachFunction};

/// Greppable diagnostic tag for every LL/SC expansion refusal.
pub const LLSC_EXPANSION_TAG: &str = "[TCG-LLSC-EXPAND]";

/// A fail-closed refusal to expand an LL/SC pseudo.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum LlscExpansionError {
    /// The pseudo does not carry its exact operand layout.
    #[error(
        "[TCG-LLSC-EXPAND] fn `{function}`: {opcode:?} has {actual} operands, expected {expected}"
    )]
    OperandCount {
        function: String,
        opcode: AArch64Opcode,
        actual: usize,
        expected: usize,
    },
    /// An operand has the wrong kind, bank, width or immediate value.
    #[error("[TCG-LLSC-EXPAND] fn `{function}`: {opcode:?} operand {index}: {detail}")]
    Operand {
        function: String,
        opcode: AArch64Opcode,
        index: usize,
        detail: String,
    },
    /// A loop-written register shares storage with another operand, so the
    /// retry loop would clobber a value it must re-read (or the
    /// store-exclusive would be constrained unpredictable).
    #[error(
        "[TCG-LLSC-EXPAND] fn `{function}`: {opcode:?} definition operand {def_index} shares \
         a register with operand {other_index}; allocation must keep every LL/SC definition \
         distinct from every use and from every other definition"
    )]
    Alias {
        function: String,
        opcode: AArch64Opcode,
        def_index: usize,
        other_index: usize,
    },
    /// The pseudo is linked from more than one block position, or the new
    /// loop instructions would not all receive a `u32` instruction ID.
    #[error("[TCG-LLSC-EXPAND] fn `{function}`: {detail}")]
    Layout { function: String, detail: String },
}

/// One general-purpose register operand after allocation, width-independent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Gpr {
    /// X0-X30 / W0-W30 by hardware number.
    Num(u8),
    /// XZR / WZR.
    Zero,
    /// SP (only legal as an exclusive base register).
    Sp,
}

impl Gpr {
    fn x(self) -> PReg {
        match self {
            Self::Num(n) => PReg::new(u16::from(n)),
            Self::Zero => trust_cg_ir::regs::XZR,
            Self::Sp => trust_cg_ir::regs::SP,
        }
    }

    fn w(self) -> PReg {
        match self {
            Self::Num(n) => PReg::new(u16::from(n) + 32),
            Self::Zero => trust_cg_ir::regs::WZR,
            Self::Sp => trust_cg_ir::aarch64_regs::WSP,
        }
    }

    fn at(self, wide: bool) -> MachOperand {
        MachOperand::PReg(if wide { self.x() } else { self.w() })
    }
}

/// Register operand classification: `(register, is_64_bit)`.
fn gpr_operand(operand: &MachOperand) -> Option<(Gpr, bool)> {
    match operand {
        MachOperand::PReg(reg) => {
            let encoding = reg.encoding();
            match encoding {
                0..=30 => Some((Gpr::Num(encoding as u8), true)),
                31 => Some((Gpr::Sp, true)),
                32..=62 => Some((Gpr::Num((encoding - 32) as u8), false)),
                63 => Some((Gpr::Sp, false)),
                _ if *reg == trust_cg_ir::regs::XZR => Some((Gpr::Zero, true)),
                _ if *reg == trust_cg_ir::regs::WZR => Some((Gpr::Zero, false)),
                _ => None,
            }
            .filter(|_| matches!(preg_class(*reg), RegClass::Gpr32 | RegClass::Gpr64))
        }
        MachOperand::Special(SpecialReg::XZR) => Some((Gpr::Zero, true)),
        MachOperand::Special(SpecialReg::WZR) => Some((Gpr::Zero, false)),
        MachOperand::Special(SpecialReg::SP) => Some((Gpr::Sp, true)),
        _ => None,
    }
}

/// Role of a pseudo operand in validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Role {
    /// A register the loop writes: a real GPR, never ZR/SP.
    Def,
    /// A data value the loop reads: GPR or ZR, never SP.
    Data,
    /// The address: an X GPR or SP, never ZR.
    Address,
}

struct Checked<'a> {
    function: &'a str,
    opcode: AArch64Opcode,
    operands: &'a [MachOperand],
}

impl Checked<'_> {
    fn err(&self, index: usize, detail: impl Into<String>) -> LlscExpansionError {
        LlscExpansionError::Operand {
            function: self.function.to_owned(),
            opcode: self.opcode,
            index,
            detail: detail.into(),
        }
    }

    /// Validate one register operand. `wide` is the width the access needs
    /// (`true` = 64-bit X data). Narrow data may arrive in an X carrier (the
    /// Gpr64 `B1` value class); it is used through its W alias. A 64-bit
    /// access never accepts a W operand, which would silently narrow it.
    fn gpr(&self, index: usize, role: Role, wide: bool) -> Result<Gpr, LlscExpansionError> {
        let (reg, is_x) = gpr_operand(&self.operands[index]).ok_or_else(|| {
            self.err(
                index,
                format!("expected a GPR, got {:?}", self.operands[index]),
            )
        })?;
        match (role, reg) {
            (Role::Def, Gpr::Zero | Gpr::Sp) => {
                return Err(self.err(index, "loop-written register must be X0-X30/W0-W30"));
            }
            (Role::Data, Gpr::Sp) => return Err(self.err(index, "data cannot be SP")),
            (Role::Address, Gpr::Zero) => return Err(self.err(index, "address cannot be ZR")),
            (Role::Address, _) if !is_x => {
                return Err(self.err(index, "address must be a 64-bit X register or SP"));
            }
            _ => {}
        }
        if role != Role::Address && wide && !is_x {
            return Err(self.err(index, "64-bit LL/SC access requires an X register"));
        }
        Ok(reg)
    }

    fn imm(&self, index: usize) -> Result<i64, LlscExpansionError> {
        match self.operands[index] {
            MachOperand::Imm(value) => Ok(value),
            ref other => Err(self.err(index, format!("expected an immediate, got {other:?}"))),
        }
    }
}

/// Reject any definition that shares storage with another operand.
fn require_distinct(
    function: &str,
    opcode: AArch64Opcode,
    defs: &[(usize, Gpr)],
    uses: &[(usize, Gpr)],
) -> Result<(), LlscExpansionError> {
    for (position, &(def_index, def)) in defs.iter().enumerate() {
        let others = defs[position + 1..].iter().chain(uses.iter());
        for &(other_index, other) in others {
            if matches!((def, other), (Gpr::Num(a), Gpr::Num(b)) if a == b) {
                return Err(LlscExpansionError::Alias {
                    function: function.to_owned(),
                    opcode,
                    def_index,
                    other_index,
                });
            }
        }
    }
    Ok(())
}

fn inst(opcode: AArch64Opcode, operands: Vec<MachOperand>, source: &MachInst) -> MachInst {
    let mut inst = MachInst::new(opcode, operands);
    inst.source_loc = source.source_loc;
    inst
}

fn cond(code: CondCode) -> MachOperand {
    MachOperand::Imm(i64::from(code.encoding()))
}

/// Expand one `LlscRmw*` pseudo into its retry loop (first instruction is
/// the load-exclusive loop head).
fn expand_rmw(
    function: &str,
    pseudo: &MachInst,
    width: LlscWidth,
) -> Result<Vec<MachInst>, LlscExpansionError> {
    let checked = Checked {
        function,
        opcode: pseudo.opcode,
        operands: &pseudo.operands,
    };
    let op = LlscRmwOp::from_imm(checked.imm(LLSC_RMW_OP_OPERAND)?)
        .ok_or_else(|| checked.err(LLSC_RMW_OP_OPERAND, "unknown LL/SC RMW operation"))?;
    let ordering = LlscOrdering::from_imm(checked.imm(LLSC_RMW_ORDERING_OPERAND)?)
        .ok_or_else(|| checked.err(LLSC_RMW_ORDERING_OPERAND, "unknown LL/SC ordering"))?;
    let wide = width == LlscWidth::B64;
    let old = checked.gpr(LLSC_RMW_OLD_OPERAND, Role::Def, wide)?;
    let new = checked.gpr(LLSC_RMW_NEW_OPERAND, Role::Def, wide)?;
    let status = checked.gpr(LLSC_RMW_STATUS_OPERAND, Role::Def, false)?;
    let value = checked.gpr(LLSC_RMW_VALUE_OPERAND, Role::Data, wide)?;
    let addr = checked.gpr(LLSC_RMW_ADDR_OPERAND, Role::Address, true)?;
    require_distinct(
        function,
        pseudo.opcode,
        &[
            (LLSC_RMW_OLD_OPERAND, old),
            (LLSC_RMW_NEW_OPERAND, new),
            (LLSC_RMW_STATUS_OPERAND, status),
        ],
        &[
            (LLSC_RMW_VALUE_OPERAND, value),
            (LLSC_RMW_ADDR_OPERAND, addr),
        ],
    )?;

    let r = |reg: Gpr| reg.at(wide);
    let mut body = vec![inst(
        exclusive_load_opcode(width, ordering.acquire),
        vec![r(old), addr.at(true)],
        pseudo,
    )];
    let three = |opcode, lhs: Gpr, rhs: Gpr| inst(opcode, vec![r(new), r(lhs), r(rhs)], pseudo);
    let stored = match op {
        LlscRmwOp::Xchg => value,
        LlscRmwOp::Add => {
            body.push(three(AArch64Opcode::AddRR, old, value));
            new
        }
        LlscRmwOp::Sub => {
            body.push(three(AArch64Opcode::SubRR, old, value));
            new
        }
        LlscRmwOp::And => {
            body.push(three(AArch64Opcode::AndRR, old, value));
            new
        }
        LlscRmwOp::Or => {
            body.push(three(AArch64Opcode::OrrRR, old, value));
            new
        }
        LlscRmwOp::Xor => {
            body.push(three(AArch64Opcode::EorRR, old, value));
            new
        }
        LlscRmwOp::Smax | LlscRmwOp::Smin | LlscRmwOp::Umax | LlscRmwOp::Umin => {
            let signed = matches!(op, LlscRmwOp::Smax | LlscRmwOp::Smin);
            let select = match op {
                LlscRmwOp::Smax => CondCode::GT,
                LlscRmwOp::Smin => CondCode::LT,
                LlscRmwOp::Umax => CondCode::HI,
                _ => CondCode::LO,
            };
            if width.is_sub_word() {
                // LDXR{B,H} zero-extends `old`; `value` may carry arbitrary
                // bits above the access width. Compare both operands extended
                // to 32 bits exactly as the access width's signedness says,
                // using `new` and `status` as scratch before either is live.
                let (lhs, rhs) = if signed {
                    let extend = if width == LlscWidth::B8 {
                        AArch64Opcode::Sxtb
                    } else {
                        AArch64Opcode::Sxth
                    };
                    body.push(inst(extend, vec![new.at(false), old.at(false)], pseudo));
                    body.push(inst(
                        extend,
                        vec![status.at(false), value.at(false)],
                        pseudo,
                    ));
                    (new, status)
                } else {
                    let extend = if width == LlscWidth::B8 {
                        AArch64Opcode::Uxtb
                    } else {
                        AArch64Opcode::Uxth
                    };
                    body.push(inst(
                        extend,
                        vec![status.at(false), value.at(false)],
                        pseudo,
                    ));
                    (old, status)
                };
                body.push(inst(
                    AArch64Opcode::CmpRR,
                    vec![lhs.at(false), rhs.at(false)],
                    pseudo,
                ));
            } else {
                body.push(inst(AArch64Opcode::CmpRR, vec![r(old), r(value)], pseudo));
            }
            body.push(inst(
                AArch64Opcode::Csel,
                vec![r(new), r(old), r(value), cond(select)],
                pseudo,
            ));
            new
        }
    };
    body.push(inst(
        exclusive_store_opcode(width, ordering.release),
        vec![status.at(false), r(stored), addr.at(true)],
        pseudo,
    ));
    let back = -(body.len() as i64);
    body.push(inst(
        AArch64Opcode::Cbnz,
        vec![status.at(false), MachOperand::Imm(back)],
        pseudo,
    ));
    Ok(body)
}

/// Expand one `LlscCmpSwap*` pseudo into its retry loop.
fn expand_cmp_swap(
    function: &str,
    pseudo: &MachInst,
    width: LlscWidth,
) -> Result<Vec<MachInst>, LlscExpansionError> {
    let checked = Checked {
        function,
        opcode: pseudo.opcode,
        operands: &pseudo.operands,
    };
    let ordering = LlscOrdering::from_imm(checked.imm(LLSC_CAS_ORDERING_OPERAND)?)
        .ok_or_else(|| checked.err(LLSC_CAS_ORDERING_OPERAND, "unknown LL/SC ordering"))?;
    let wide = width == LlscWidth::B64;
    let old = checked.gpr(LLSC_CAS_OLD_OPERAND, Role::Def, wide)?;
    let status = checked.gpr(LLSC_CAS_STATUS_OPERAND, Role::Def, false)?;
    let expected = checked.gpr(LLSC_CAS_EXPECTED_OPERAND, Role::Data, wide)?;
    let desired = checked.gpr(LLSC_CAS_DESIRED_OPERAND, Role::Data, wide)?;
    let addr = checked.gpr(LLSC_CAS_ADDR_OPERAND, Role::Address, true)?;
    require_distinct(
        function,
        pseudo.opcode,
        &[
            (LLSC_CAS_OLD_OPERAND, old),
            (LLSC_CAS_STATUS_OPERAND, status),
        ],
        &[
            (LLSC_CAS_EXPECTED_OPERAND, expected),
            (LLSC_CAS_DESIRED_OPERAND, desired),
            (LLSC_CAS_ADDR_OPERAND, addr),
        ],
    )?;

    let r = |reg: Gpr| reg.at(wide);
    let mut body = vec![inst(
        exclusive_load_opcode(width, ordering.acquire),
        vec![r(old), addr.at(true)],
        pseudo,
    )];
    let compared = if width.is_sub_word() {
        let extend = if width == LlscWidth::B8 {
            AArch64Opcode::Uxtb
        } else {
            AArch64Opcode::Uxth
        };
        body.push(inst(
            extend,
            vec![status.at(false), expected.at(false)],
            pseudo,
        ));
        status
    } else {
        expected
    };
    body.push(inst(
        AArch64Opcode::CmpRR,
        vec![r(old), r(compared)],
        pseudo,
    ));
    // B.NE skips STXR, CBNZ and B.EQ to land on CLREX.
    body.push(inst(
        AArch64Opcode::BCond,
        vec![cond(CondCode::NE), MachOperand::Imm(4)],
        pseudo,
    ));
    body.push(inst(
        exclusive_store_opcode(width, ordering.release),
        vec![status.at(false), r(desired), addr.at(true)],
        pseudo,
    ));
    let back = -(body.len() as i64);
    body.push(inst(
        AArch64Opcode::Cbnz,
        vec![status.at(false), MachOperand::Imm(back)],
        pseudo,
    ));
    body.push(inst(
        AArch64Opcode::BCond,
        vec![cond(CondCode::EQ), MachOperand::Imm(2)],
        pseudo,
    ));
    body.push(inst(AArch64Opcode::Clrex, vec![], pseudo));
    Ok(body)
}

/// The pair-register operands of a 128-bit pseudo, checked as X registers.
fn pair(
    checked: &Checked<'_>,
    lo: usize,
    hi: usize,
    role: Role,
) -> Result<(Gpr, Gpr), LlscExpansionError> {
    Ok((checked.gpr(lo, role, true)?, checked.gpr(hi, role, true)?))
}

fn load_pair(
    ordering: LlscOrdering,
    (lo, hi): (Gpr, Gpr),
    addr: Gpr,
    source: &MachInst,
) -> MachInst {
    inst(
        exclusive_load_opcode(LlscWidth::B128, ordering.acquire),
        vec![lo.at(true), hi.at(true), addr.at(true)],
        source,
    )
}

fn store_pair(
    ordering: LlscOrdering,
    status: Gpr,
    (lo, hi): (Gpr, Gpr),
    addr: Gpr,
    source: &MachInst,
) -> MachInst {
    inst(
        exclusive_store_opcode(LlscWidth::B128, ordering.release),
        vec![status.at(false), lo.at(true), hi.at(true), addr.at(true)],
        source,
    )
}

fn retry(status: Gpr, body_len: usize, source: &MachInst) -> MachInst {
    inst(
        AArch64Opcode::Cbnz,
        vec![status.at(false), MachOperand::Imm(-(body_len as i64))],
        source,
    )
}

/// `LlscLoad128`: an LDXP alone is not single-copy atomic on armv8.0, so
/// the loaded pair is stored back and the loop retries until that store
/// succeeds (the LLVM armv8.0 mapping; it writes, so read-only memory
/// faults).
fn expand_load128(function: &str, pseudo: &MachInst) -> Result<Vec<MachInst>, LlscExpansionError> {
    use trust_cg_ir::llsc::{
        LLSC_LOAD128_ADDR_OPERAND, LLSC_LOAD128_HI_OPERAND, LLSC_LOAD128_LO_OPERAND,
        LLSC_LOAD128_ORDERING_OPERAND, LLSC_LOAD128_STATUS_OPERAND,
    };
    let checked = Checked {
        function,
        opcode: pseudo.opcode,
        operands: &pseudo.operands,
    };
    let ordering = LlscOrdering::from_imm(checked.imm(LLSC_LOAD128_ORDERING_OPERAND)?)
        .ok_or_else(|| checked.err(LLSC_LOAD128_ORDERING_OPERAND, "unknown LL/SC ordering"))?;
    let value = pair(
        &checked,
        LLSC_LOAD128_LO_OPERAND,
        LLSC_LOAD128_HI_OPERAND,
        Role::Def,
    )?;
    let status = checked.gpr(LLSC_LOAD128_STATUS_OPERAND, Role::Def, false)?;
    let addr = checked.gpr(LLSC_LOAD128_ADDR_OPERAND, Role::Address, true)?;
    require_distinct(
        function,
        pseudo.opcode,
        &[
            (LLSC_LOAD128_LO_OPERAND, value.0),
            (LLSC_LOAD128_HI_OPERAND, value.1),
            (LLSC_LOAD128_STATUS_OPERAND, status),
        ],
        &[(LLSC_LOAD128_ADDR_OPERAND, addr)],
    )?;
    Ok(vec![
        load_pair(ordering, value, addr, pseudo),
        store_pair(ordering, status, value, addr, pseudo),
        retry(status, 2, pseudo),
    ])
}

/// `LlscStore128`: load-exclusive the pair into scratch registers, then
/// store-exclusive the new value.
fn expand_store128(function: &str, pseudo: &MachInst) -> Result<Vec<MachInst>, LlscExpansionError> {
    use trust_cg_ir::llsc::{
        LLSC_STORE128_ADDR_OPERAND, LLSC_STORE128_ORDERING_OPERAND,
        LLSC_STORE128_SCRATCH_HI_OPERAND, LLSC_STORE128_SCRATCH_LO_OPERAND,
        LLSC_STORE128_STATUS_OPERAND, LLSC_STORE128_VALUE_HI_OPERAND,
        LLSC_STORE128_VALUE_LO_OPERAND,
    };
    let checked = Checked {
        function,
        opcode: pseudo.opcode,
        operands: &pseudo.operands,
    };
    let ordering = LlscOrdering::from_imm(checked.imm(LLSC_STORE128_ORDERING_OPERAND)?)
        .ok_or_else(|| checked.err(LLSC_STORE128_ORDERING_OPERAND, "unknown LL/SC ordering"))?;
    let scratch = pair(
        &checked,
        LLSC_STORE128_SCRATCH_LO_OPERAND,
        LLSC_STORE128_SCRATCH_HI_OPERAND,
        Role::Def,
    )?;
    let status = checked.gpr(LLSC_STORE128_STATUS_OPERAND, Role::Def, false)?;
    let value = pair(
        &checked,
        LLSC_STORE128_VALUE_LO_OPERAND,
        LLSC_STORE128_VALUE_HI_OPERAND,
        Role::Data,
    )?;
    let addr = checked.gpr(LLSC_STORE128_ADDR_OPERAND, Role::Address, true)?;
    require_distinct(
        function,
        pseudo.opcode,
        &[
            (LLSC_STORE128_SCRATCH_LO_OPERAND, scratch.0),
            (LLSC_STORE128_SCRATCH_HI_OPERAND, scratch.1),
            (LLSC_STORE128_STATUS_OPERAND, status),
        ],
        &[
            (LLSC_STORE128_VALUE_LO_OPERAND, value.0),
            (LLSC_STORE128_VALUE_HI_OPERAND, value.1),
            (LLSC_STORE128_ADDR_OPERAND, addr),
        ],
    )?;
    Ok(vec![
        load_pair(ordering, scratch, addr, pseudo),
        store_pair(ordering, status, value, addr, pseudo),
        retry(status, 2, pseudo),
    ])
}

/// `LlscRmw128`: pair load-exclusive, a two-limb ALU step (carry chains for
/// add/sub, a 128-bit `CMP`/`SBCS` comparison for min/max), pair
/// store-exclusive and retry.
fn expand_rmw128(function: &str, pseudo: &MachInst) -> Result<Vec<MachInst>, LlscExpansionError> {
    use trust_cg_ir::llsc::{
        LLSC_RMW128_ADDR_OPERAND, LLSC_RMW128_NEW_HI_OPERAND, LLSC_RMW128_NEW_LO_OPERAND,
        LLSC_RMW128_OLD_HI_OPERAND, LLSC_RMW128_OLD_LO_OPERAND, LLSC_RMW128_OP_OPERAND,
        LLSC_RMW128_ORDERING_OPERAND, LLSC_RMW128_STATUS_OPERAND, LLSC_RMW128_VALUE_HI_OPERAND,
        LLSC_RMW128_VALUE_LO_OPERAND,
    };
    let checked = Checked {
        function,
        opcode: pseudo.opcode,
        operands: &pseudo.operands,
    };
    let op = LlscRmwOp::from_imm(checked.imm(LLSC_RMW128_OP_OPERAND)?)
        .ok_or_else(|| checked.err(LLSC_RMW128_OP_OPERAND, "unknown LL/SC RMW operation"))?;
    let ordering = LlscOrdering::from_imm(checked.imm(LLSC_RMW128_ORDERING_OPERAND)?)
        .ok_or_else(|| checked.err(LLSC_RMW128_ORDERING_OPERAND, "unknown LL/SC ordering"))?;
    let old = pair(
        &checked,
        LLSC_RMW128_OLD_LO_OPERAND,
        LLSC_RMW128_OLD_HI_OPERAND,
        Role::Def,
    )?;
    let new = pair(
        &checked,
        LLSC_RMW128_NEW_LO_OPERAND,
        LLSC_RMW128_NEW_HI_OPERAND,
        Role::Def,
    )?;
    let status = checked.gpr(LLSC_RMW128_STATUS_OPERAND, Role::Def, false)?;
    let value = pair(
        &checked,
        LLSC_RMW128_VALUE_LO_OPERAND,
        LLSC_RMW128_VALUE_HI_OPERAND,
        Role::Data,
    )?;
    let addr = checked.gpr(LLSC_RMW128_ADDR_OPERAND, Role::Address, true)?;
    require_distinct(
        function,
        pseudo.opcode,
        &[
            (LLSC_RMW128_OLD_LO_OPERAND, old.0),
            (LLSC_RMW128_OLD_HI_OPERAND, old.1),
            (LLSC_RMW128_NEW_LO_OPERAND, new.0),
            (LLSC_RMW128_NEW_HI_OPERAND, new.1),
            (LLSC_RMW128_STATUS_OPERAND, status),
        ],
        &[
            (LLSC_RMW128_VALUE_LO_OPERAND, value.0),
            (LLSC_RMW128_VALUE_HI_OPERAND, value.1),
            (LLSC_RMW128_ADDR_OPERAND, addr),
        ],
    )?;
    let x = |reg: Gpr| reg.at(true);
    let mut body = vec![load_pair(ordering, old, addr, pseudo)];
    let limb =
        |opcode, dst: Gpr, lhs: Gpr, rhs: Gpr| inst(opcode, vec![x(dst), x(lhs), x(rhs)], pseudo);
    let stored = match op {
        LlscRmwOp::Xchg => value,
        LlscRmwOp::Add | LlscRmwOp::Sub | LlscRmwOp::And | LlscRmwOp::Or | LlscRmwOp::Xor => {
            let (low, high) = match op {
                LlscRmwOp::Add => (AArch64Opcode::AddsRR, AArch64Opcode::Adc),
                LlscRmwOp::Sub => (AArch64Opcode::SubsRR, AArch64Opcode::Sbc),
                LlscRmwOp::And => (AArch64Opcode::AndRR, AArch64Opcode::AndRR),
                LlscRmwOp::Or => (AArch64Opcode::OrrRR, AArch64Opcode::OrrRR),
                _ => (AArch64Opcode::EorRR, AArch64Opcode::EorRR),
            };
            body.push(limb(low, new.0, old.0, value.0));
            body.push(limb(high, new.1, old.1, value.1));
            new
        }
        LlscRmwOp::Smax | LlscRmwOp::Smin | LlscRmwOp::Umax | LlscRmwOp::Umin => {
            // CMP lo ; SBCS XZR, hi computes old - value over 128 bits: C and
            // N^V are exact, Z is not, so select with HS/LO or GE/LT only.
            let select = match op {
                LlscRmwOp::Smax => CondCode::GE,
                LlscRmwOp::Smin => CondCode::LT,
                LlscRmwOp::Umax => CondCode::HS,
                _ => CondCode::LO,
            };
            body.push(inst(
                AArch64Opcode::CmpRR,
                vec![x(old.0), x(value.0)],
                pseudo,
            ));
            body.push(inst(
                AArch64Opcode::Sbcs,
                vec![Gpr::Zero.at(true), x(old.1), x(value.1)],
                pseudo,
            ));
            for (dst, lhs, rhs) in [(new.0, old.0, value.0), (new.1, old.1, value.1)] {
                body.push(inst(
                    AArch64Opcode::Csel,
                    vec![x(dst), x(lhs), x(rhs), cond(select)],
                    pseudo,
                ));
            }
            new
        }
    };
    body.push(store_pair(ordering, status, stored, addr, pseudo));
    let len = body.len();
    body.push(retry(status, len, pseudo));
    Ok(body)
}

/// `LlscCmpSwap128`: both halves must match; on failure the loaded pair is
/// stored back so the returned value was read single-copy atomically.
///
/// ```text
/// loop: LD{A}XP      old_lo, old_hi, [addr]
///       CMP          old_lo, expected_lo
///       B.NE         fail
///       CMP          old_hi, expected_hi
///       B.NE         fail
///       ST{L}XP      status, desired_lo, desired_hi, [addr]
///       CBNZ         status, loop
///       B.EQ         done              ; NZCV is still EQ from the CMP
/// fail: ST{L}XP      status, old_lo, old_hi, [addr]
///       CBNZ         status, loop
/// done:
/// ```
fn expand_cas128(function: &str, pseudo: &MachInst) -> Result<Vec<MachInst>, LlscExpansionError> {
    use trust_cg_ir::llsc::{
        LLSC_CAS128_ADDR_OPERAND, LLSC_CAS128_DESIRED_HI_OPERAND, LLSC_CAS128_DESIRED_LO_OPERAND,
        LLSC_CAS128_EXPECTED_HI_OPERAND, LLSC_CAS128_EXPECTED_LO_OPERAND,
        LLSC_CAS128_OLD_HI_OPERAND, LLSC_CAS128_OLD_LO_OPERAND, LLSC_CAS128_ORDERING_OPERAND,
        LLSC_CAS128_STATUS_OPERAND,
    };
    let checked = Checked {
        function,
        opcode: pseudo.opcode,
        operands: &pseudo.operands,
    };
    let ordering = LlscOrdering::from_imm(checked.imm(LLSC_CAS128_ORDERING_OPERAND)?)
        .ok_or_else(|| checked.err(LLSC_CAS128_ORDERING_OPERAND, "unknown LL/SC ordering"))?;
    let old = pair(
        &checked,
        LLSC_CAS128_OLD_LO_OPERAND,
        LLSC_CAS128_OLD_HI_OPERAND,
        Role::Def,
    )?;
    let status = checked.gpr(LLSC_CAS128_STATUS_OPERAND, Role::Def, false)?;
    let expected = pair(
        &checked,
        LLSC_CAS128_EXPECTED_LO_OPERAND,
        LLSC_CAS128_EXPECTED_HI_OPERAND,
        Role::Data,
    )?;
    let desired = pair(
        &checked,
        LLSC_CAS128_DESIRED_LO_OPERAND,
        LLSC_CAS128_DESIRED_HI_OPERAND,
        Role::Data,
    )?;
    let addr = checked.gpr(LLSC_CAS128_ADDR_OPERAND, Role::Address, true)?;
    require_distinct(
        function,
        pseudo.opcode,
        &[
            (LLSC_CAS128_OLD_LO_OPERAND, old.0),
            (LLSC_CAS128_OLD_HI_OPERAND, old.1),
            (LLSC_CAS128_STATUS_OPERAND, status),
        ],
        &[
            (LLSC_CAS128_EXPECTED_LO_OPERAND, expected.0),
            (LLSC_CAS128_EXPECTED_HI_OPERAND, expected.1),
            (LLSC_CAS128_DESIRED_LO_OPERAND, desired.0),
            (LLSC_CAS128_DESIRED_HI_OPERAND, desired.1),
            (LLSC_CAS128_ADDR_OPERAND, addr),
        ],
    )?;
    let x = |reg: Gpr| reg.at(true);
    let bne = |displacement| {
        inst(
            AArch64Opcode::BCond,
            vec![cond(CondCode::NE), MachOperand::Imm(displacement)],
            pseudo,
        )
    };
    Ok(vec![
        load_pair(ordering, old, addr, pseudo),
        inst(AArch64Opcode::CmpRR, vec![x(old.0), x(expected.0)], pseudo),
        bne(6),
        inst(AArch64Opcode::CmpRR, vec![x(old.1), x(expected.1)], pseudo),
        bne(4),
        store_pair(ordering, status, desired, addr, pseudo),
        retry(status, 6, pseudo),
        inst(
            AArch64Opcode::BCond,
            vec![cond(CondCode::EQ), MachOperand::Imm(3)],
            pseudo,
        ),
        store_pair(ordering, status, old, addr, pseudo),
        retry(status, 9, pseudo),
    ])
}

/// Expand one pseudo, returning the replacement sequence.
pub fn expand_llsc_pseudo(
    function: &str,
    pseudo: &MachInst,
) -> Result<Option<Vec<MachInst>>, LlscExpansionError> {
    let Some(kind) = LlscPseudo::of(pseudo.opcode) else {
        return Ok(None);
    };
    if pseudo.operands.len() != kind.operand_count() {
        return Err(LlscExpansionError::OperandCount {
            function: function.to_owned(),
            opcode: pseudo.opcode,
            actual: pseudo.operands.len(),
            expected: kind.operand_count(),
        });
    }
    match kind {
        LlscPseudo::Rmw(LlscWidth::B128) => expand_rmw128(function, pseudo),
        LlscPseudo::CmpSwap(LlscWidth::B128) => expand_cas128(function, pseudo),
        LlscPseudo::Rmw(width) => expand_rmw(function, pseudo, width),
        LlscPseudo::CmpSwap(width) => expand_cmp_swap(function, pseudo, width),
        LlscPseudo::Load128 => expand_load128(function, pseudo),
        LlscPseudo::Store128 => expand_store128(function, pseudo),
    }
    .map(Some)
}

/// Expand every LL/SC pseudo in `func` in place.
///
/// Must run after register allocation, spill materialization and frame
/// lowering (every operand is physical) and before branch layout and branch
/// resolution. The pseudo's instruction id is reused for the loop-head
/// load-exclusive, which defines the same `old` register, so register-debug
/// provenance keyed by the defining instruction stays exact. Returns the
/// number of pseudos expanded; on error the function is left unchanged.
pub fn expand_llsc_atomics(func: &mut MachFunction) -> Result<usize, LlscExpansionError> {
    let mut planned: Vec<(usize, Vec<LlscExpansion>)> = Vec::new();
    let mut placed = BTreeSet::new();
    let mut new_insts_needed = 0usize;
    for (block_index, block) in func.blocks.iter().enumerate() {
        let mut expansions = Vec::new();
        for &inst_id in &block.insts {
            let pseudo = func.inst(inst_id);
            if let Some(sequence) = expand_llsc_pseudo(&func.name, pseudo)? {
                // The head reuses the pseudo's id; a second placement would
                // then name a lone load-exclusive with no store or retry.
                if !placed.insert(inst_id) {
                    return Err(LlscExpansionError::Layout {
                        function: func.name.clone(),
                        detail: format!(
                            "{:?} {inst_id:?} is linked from more than one block position",
                            pseudo.opcode
                        ),
                    });
                }
                let mut sequence = sequence.into_iter();
                let Some(head) = sequence.next() else {
                    return Err(LlscExpansionError::Layout {
                        function: func.name.clone(),
                        detail: format!(
                            "{:?} {inst_id:?} expanded to no instructions",
                            pseudo.opcode
                        ),
                    });
                };
                let tail: Vec<MachInst> = sequence.collect();
                new_insts_needed = new_insts_needed.saturating_add(tail.len());
                expansions.push((inst_id, head, tail));
            }
        }
        if !expansions.is_empty() {
            planned.push((block_index, expansions));
        }
    }
    if !new_inst_ids_fit(func.insts.len(), new_insts_needed) {
        return Err(LlscExpansionError::Layout {
            function: func.name.clone(),
            detail: format!(
                "{new_insts_needed} expanded loop instructions after {} existing ones exceed \
                 the u32 instruction-ID domain",
                func.insts.len()
            ),
        });
    }

    if planned.is_empty() {
        return Ok(0);
    }
    // `new_inst_ids_fit` admitted every new id, so the commit cannot fail on
    // the id domain; should it fail anyway, the snapshot keeps the documented
    // unchanged-on-error contract.
    let snapshot = func.clone();
    match commit_llsc_expansions(func, planned) {
        Ok(expanded) => Ok(expanded),
        Err(error) => {
            *func = snapshot;
            Err(error)
        }
    }
}

/// One planned expansion: the pseudo's id, the load-exclusive head that reuses
/// it, and the loop's remaining instructions.
type LlscExpansion = (InstId, MachInst, Vec<MachInst>);

fn commit_llsc_expansions(
    func: &mut MachFunction,
    planned: Vec<(usize, Vec<LlscExpansion>)>,
) -> Result<usize, LlscExpansionError> {
    let mut expanded = 0;
    for (block_index, expansions) in planned {
        let mut by_id: BTreeMap<InstId, (MachInst, Vec<MachInst>)> = expansions
            .into_iter()
            .map(|(id, head, tail)| (id, (head, tail)))
            .collect();
        let old_insts = std::mem::take(&mut func.blocks[block_index].insts);
        let mut new_insts = Vec::with_capacity(old_insts.len() + by_id.len() * 8);
        for inst_id in old_insts {
            let Some((head, tail)) = by_id.remove(&inst_id) else {
                new_insts.push(inst_id);
                continue;
            };
            *func.inst_mut(inst_id) = head;
            new_insts.push(inst_id);
            for inst in tail {
                let id = func
                    .try_push_inst(inst)
                    .ok_or_else(|| LlscExpansionError::Layout {
                        function: func.name.clone(),
                        detail:
                            "an expanded loop instruction exceeds the u32 instruction-ID domain"
                                .to_string(),
                    })?;
                new_insts.push(id);
            }
            expanded += 1;
        }
        func.blocks[block_index].insts = new_insts;
    }
    Ok(expanded)
}

/// True when `needed` new arena entries appended after `existing` ones all
/// receive a `u32` instruction ID.
fn new_inst_ids_fit(existing: usize, needed: usize) -> bool {
    needed == 0
        || existing
            .checked_add(needed - 1)
            .is_some_and(|last| u32::try_from(last).is_ok())
}

fn imm_at(inst: &MachInst, index: usize) -> Option<i64> {
    match inst.operands.get(index) {
        Some(MachOperand::Imm(value)) => Some(*value),
        _ => None,
    }
}

fn reg_num(operand: Option<&MachOperand>) -> Option<Gpr> {
    operand.and_then(gpr_operand).map(|(reg, _)| reg)
}

/// ALU opcodes an expanded LL/SC loop body may contain between its exclusive
/// pair. None of them accesses memory.
fn is_llsc_body_alu(opcode: AArch64Opcode) -> bool {
    matches!(
        opcode,
        AArch64Opcode::AddRR
            | AArch64Opcode::SubRR
            | AArch64Opcode::AndRR
            | AArch64Opcode::OrrRR
            | AArch64Opcode::EorRR
            | AArch64Opcode::CmpRR
            | AArch64Opcode::Csel
            | AArch64Opcode::Sxtb
            | AArch64Opcode::Sxth
            | AArch64Opcode::Uxtb
            | AArch64Opcode::Uxth
            | AArch64Opcode::AddsRR
            | AArch64Opcode::Adc
            | AArch64Opcode::SubsRR
            | AArch64Opcode::Sbc
            | AArch64Opcode::Sbcs
    )
}

fn is_cond(inst: &MachInst, code: CondCode, displacement: i64) -> bool {
    inst.opcode == AArch64Opcode::BCond
        && inst.operands.len() == 2
        && imm_at(inst, 0) == Some(i64::from(code.encoding()))
        && imm_at(inst, 1) == Some(displacement)
}

fn is_bne(inst: &MachInst) -> Option<i64> {
    (inst.opcode == AArch64Opcode::BCond
        && inst.operands.len() == 2
        && imm_at(inst, 0) == Some(i64::from(CondCode::NE.encoding())))
    .then(|| imm_at(inst, 1))
    .flatten()
}

/// `(base operand index, data operand indices)` of an exclusive load or
/// store with its exact operand count, or `None` for any other shape.
fn exclusive_shape(inst: &MachInst) -> Option<(usize, &'static [usize])> {
    let pair = is_exclusive_pair(inst.opcode);
    match (
        is_exclusive_load(inst.opcode),
        is_exclusive_store(inst.opcode),
        pair,
    ) {
        (true, _, false) if inst.operands.len() == 2 => Some((1, &[0])),
        (true, _, true) if inst.operands.len() == 3 => Some((2, &[0, 1])),
        (_, true, false) if inst.operands.len() == 3 => Some((2, &[1])),
        (_, true, true) if inst.operands.len() == 4 => Some((3, &[1, 2])),
        _ => None,
    }
}

/// True when `cbnz` retries `store`'s status to exactly `target`.
fn closes_loop(cbnz: &MachInst, store: &MachInst, at: usize, target: usize) -> bool {
    cbnz.opcode == AArch64Opcode::Cbnz
        && cbnz.operands.len() == 2
        && reg_num(cbnz.operands.first()) == reg_num(store.operands.first())
        && imm_at(cbnz, 1) == Some(target as i64 - at as i64)
}

/// Branches internal to an expanded LL/SC loop, found by exact template
/// match over one block's real instructions (`insts` in layout order, pseudo
/// instructions already removed). Returns the ids of the internal branches.
///
/// A branch qualifies only inside a complete template: a load-exclusive, at
/// most six register-only ALU instructions (plus the compare-failure `B.NE`s
/// of a compare-and-swap), a store-exclusive of the same kind on the same
/// base register whose status feeds the `CBNZ` that returns exactly to the
/// load-exclusive, and for compare-and-swap its exact exit tail: `B.EQ +2 ;
/// CLREX` for a single register, or `B.EQ +3 ; ST{L}XP status, old ; CBNZ`
/// back to the head for a pair. Anything else keeps the ordinary
/// intra-block refusal.
pub fn llsc_internal_branches(insts: &[(InstId, &MachInst)]) -> BTreeSet<InstId> {
    let mut internal = BTreeSet::new();
    let mut head = 0;
    while head < insts.len() {
        let load = insts[head].1;
        let Some((load_base, load_data)) =
            exclusive_shape(load).filter(|_| is_exclusive_load(load.opcode))
        else {
            head += 1;
            continue;
        };
        let Some(base) = reg_num(load.operands.get(load_base)) else {
            head += 1;
            continue;
        };
        let pair = is_exclusive_pair(load.opcode);
        let mut cursor = head + 1;
        let mut exits = Vec::new();
        while cursor < insts.len() && cursor - head <= 6 {
            let inst = insts[cursor].1;
            if is_llsc_body_alu(inst.opcode) {
                cursor += 1;
            } else if let Some(displacement) = is_bne(inst).filter(|_| exits.len() < 2) {
                exits.push((cursor, displacement));
                cursor += 1;
            } else {
                break;
            }
        }
        let Some(&(_, store)) = insts.get(cursor) else {
            break;
        };
        let store_matches = is_exclusive_store(store.opcode)
            && is_exclusive_pair(store.opcode) == pair
            && exclusive_shape(store).is_some_and(|(store_base, _)| {
                reg_num(store.operands.get(store_base)) == Some(base)
            });
        let Some(&(cbnz_id, cbnz)) = insts.get(cursor + 1) else {
            break;
        };
        if !store_matches || !closes_loop(cbnz, store, cursor + 1, head) {
            head += 1;
            continue;
        }
        let at = |offset: usize| insts.get(cursor + offset).map(|(_, inst)| *inst);
        match exits.as_slice() {
            [] => {
                internal.insert(cbnz_id);
                head = cursor + 2;
            }
            // Single-register CAS: B.NE +4 just before the store, then
            // B.EQ +2 and CLREX after the CBNZ.
            [(bne, 4)] if !pair && *bne + 1 == cursor => {
                let complete = at(2).is_some_and(|beq| is_cond(beq, CondCode::EQ, 2))
                    && at(3).is_some_and(|clrex| {
                        clrex.opcode == AArch64Opcode::Clrex && clrex.operands.is_empty()
                    });
                if complete {
                    internal.extend([insts[*bne].0, cbnz_id, insts[cursor + 2].0]);
                    head = cursor + 4;
                } else {
                    head += 1;
                }
            }
            // Pair CAS: CMP/B.NE +6/CMP/B.NE +4 before the store; after the
            // CBNZ, B.EQ +3 then the write-back store of the loaded pair and
            // its own CBNZ back to the head.
            [(first, 6), (second, 4)]
                if pair && *first == head + 2 && *second == head + 4 && cursor == head + 5 =>
            {
                let write_back = at(3).filter(|fail| {
                    fail.opcode == store.opcode
                        && fail.operands.len() == 4
                        && reg_num(fail.operands.first()) == reg_num(store.operands.first())
                        && reg_num(fail.operands.get(3)) == Some(base)
                        && load_data.iter().zip([1, 2]).all(|(&loaded, stored)| {
                            reg_num(load.operands.get(loaded)) == reg_num(fail.operands.get(stored))
                        })
                });
                let complete = at(2).is_some_and(|beq| is_cond(beq, CondCode::EQ, 3))
                    && write_back.is_some_and(|fail| {
                        at(4).is_some_and(|retry| closes_loop(retry, fail, cursor + 4, head))
                    });
                if complete {
                    internal.extend([
                        insts[*first].0,
                        insts[*second].0,
                        cbnz_id,
                        insts[cursor + 2].0,
                        insts[cursor + 4].0,
                    ]);
                    head = cursor + 5;
                } else {
                    head += 1;
                }
            }
            _ => head += 1,
        }
    }
    internal
}

/// Greppable tag for a spill access inside an exclusive window.
pub const LLSC_SPILL_WINDOW_TAG: &str = "[TCG-LLSC-SPILL-WINDOW]";
/// Greppable tag for any other memory access or call inside an exclusive
/// window.
pub const LLSC_WINDOW_TAG: &str = "[TCG-LLSC-WINDOW]";

/// A fail-closed refusal of an instruction placed inside an open
/// load-exclusive/store-exclusive window.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ExclusiveWindowError {
    /// A flagged register-allocation spill store or reload (or an emergency
    /// register save/restore) sits between a load-exclusive and its
    /// store-exclusive on some path.
    #[error(
        "[TCG-LLSC-SPILL-WINDOW] fn `{function}`: block {block} instruction #{position} \
         ({opcode:?}) is a spill access inside an open load-exclusive/store-exclusive \
         window; a value live across an LL/SC loop must stay in a register or be \
         spilled and reloaded outside the window"
    )]
    SpillAccess {
        function: String,
        block: u32,
        position: usize,
        opcode: AArch64Opcode,
    },
    /// Any other explicit memory access, stack-slot reference or call sits
    /// inside an open window on some path.
    #[error(
        "[TCG-LLSC-WINDOW] fn `{function}`: block {block} instruction #{position} \
         ({opcode:?}) {what} inside an open load-exclusive/store-exclusive window, \
         where an explicit memory access may clear the exclusive monitor"
    )]
    MemoryAccess {
        function: String,
        block: u32,
        position: usize,
        opcode: AArch64Opcode,
        what: &'static str,
    },
}

/// What an instruction inside an open exclusive window may not be.
fn window_intrusion(inst: &MachInst) -> Option<&'static str> {
    use trust_cg_ir::inst::InstFlags;
    let default = inst.opcode.default_flags();
    let flags = inst.flags.union(default);
    if flags.contains(InstFlags::IS_CALL)
        || matches!(
            inst.opcode,
            AArch64Opcode::Bl
                | AArch64Opcode::BL
                | AArch64Opcode::Blr
                | AArch64Opcode::BLR
                | AArch64Opcode::TlsDescCall
                | AArch64Opcode::BlrTlsdesc
        )
    {
        return Some("is a call");
    }
    if flags.contains(InstFlags::READS_MEMORY) || flags.contains(InstFlags::WRITES_MEMORY) {
        return Some("accesses memory");
    }
    if inst.operands.iter().any(|operand| {
        matches!(
            operand,
            MachOperand::StackSlot(_)
                | MachOperand::FrameIndex(_)
                | MachOperand::IncomingArg(_)
                | MachOperand::MemOp { .. }
        )
    }) {
        return Some("references a memory operand");
    }
    None
}

/// Refuse every spill access, memory access and call placed inside an open
/// exclusive window of `func`, on any path.
///
/// A window opens at a load-exclusive (`LD{A}X{R,P}{B,H}`) and closes at the
/// next store-exclusive or `CLREX` on the same path. The check is a forward
/// "may be open" dataflow over `func`'s successor lists (each block is also
/// scanned from a closed state, so in-block windows are checked even in a
/// block the CFG does not reach). Inside an open window it refuses a
/// [`InstFlags::SPILL_SLOT_ACCESS`](trust_cg_ir::inst::InstFlags::SPILL_SLOT_ACCESS)
/// access by name ([`LLSC_SPILL_WINDOW_TAG`]) and every other memory access,
/// stack-slot or memory operand and call ([`LLSC_WINDOW_TAG`]). Branches,
/// register-only ALU instructions, returns and barriers are permitted.
///
/// This is the post-expansion enforcement of the whole-window spill strategy:
/// LL/SC pseudos keep every spill, reload and emergency register save outside
/// their loops by construction ([`expand_llsc_atomics`] runs after spill
/// materialization and frame lowering), and this check turns any later pass,
/// hand-built stream or public-encoder input that breaks it into a named
/// compile error. It is a structural check, not an exclusive-monitor or
/// forward-progress proof. Returns the number of load-exclusives examined.
pub fn check_exclusive_windows(func: &MachFunction) -> Result<usize, ExclusiveWindowError> {
    let has_exclusive = func.blocks.iter().any(|block| {
        block
            .insts
            .iter()
            .filter_map(|id| func.insts.get(id.0 as usize))
            .any(|inst| is_exclusive_load(inst.opcode))
    });
    if !has_exclusive {
        return Ok(0);
    }
    let blocks = func.blocks.len();
    let mut open_in = vec![false; blocks];
    let mut queued = vec![true; blocks];
    let mut worklist: std::collections::VecDeque<usize> = (0..blocks).collect();
    let mut examined = vec![0usize; blocks];
    while let Some(block) = worklist.pop_front() {
        queued[block] = false;
        let mut open = open_in[block];
        let mut loads = 0usize;
        for (position, &inst_id) in func.blocks[block].insts.iter().enumerate() {
            // An out-of-range id is the CFG validator's refusal, not ours.
            let Some(inst) = func.insts.get(inst_id.0 as usize) else {
                continue;
            };
            if inst.is_pseudo() {
                continue;
            }
            if is_exclusive_load(inst.opcode) {
                open = true;
                loads += 1;
                continue;
            }
            if is_exclusive_store(inst.opcode) || inst.opcode == AArch64Opcode::Clrex {
                open = false;
                continue;
            }
            if !open {
                continue;
            }
            let block_id = block as u32;
            if inst.flags.is_spill_slot_access() {
                return Err(ExclusiveWindowError::SpillAccess {
                    function: func.name.clone(),
                    block: block_id,
                    position,
                    opcode: inst.opcode,
                });
            }
            if let Some(what) = window_intrusion(inst) {
                return Err(ExclusiveWindowError::MemoryAccess {
                    function: func.name.clone(),
                    block: block_id,
                    position,
                    opcode: inst.opcode,
                    what,
                });
            }
        }
        examined[block] = loads;
        if !open {
            continue;
        }
        for succ in &func.blocks[block].succs {
            let s = succ.0 as usize;
            if s < blocks && !open_in[s] {
                open_in[s] = true;
                if !queued[s] {
                    queued[s] = true;
                    worklist.push_back(s);
                }
            }
        }
    }
    Ok(examined.iter().sum())
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::function::Signature;
    use trust_cg_ir::regs::{W0, W1, W2, W3, X0, X1, X2, X3, X4, XZR};

    fn func_with(inst: MachInst) -> MachFunction {
        let mut func = MachFunction::new("llsc".into(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let id = func.push_inst(inst);
        func.append_inst(entry, id);
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(entry, ret);
        func
    }

    fn rmw(
        opcode: AArch64Opcode,
        regs: [PReg; 5],
        op: LlscRmwOp,
        ordering: LlscOrdering,
    ) -> MachInst {
        let mut operands: Vec<MachOperand> = regs.iter().map(|&r| MachOperand::PReg(r)).collect();
        operands.push(MachOperand::Imm(op.to_imm()));
        operands.push(MachOperand::Imm(ordering.to_imm()));
        MachInst::new(opcode, operands)
    }

    fn opcodes(func: &MachFunction) -> Vec<AArch64Opcode> {
        func.blocks[0]
            .insts
            .iter()
            .map(|&id| func.inst(id).opcode)
            .collect()
    }

    #[test]
    fn rmw_add_expands_to_exact_exclusive_loop_and_keeps_head_id() {
        let pseudo = rmw(
            AArch64Opcode::LlscRmw64,
            [X0, X1, W2, X3, X4],
            LlscRmwOp::Add,
            LlscOrdering::ACQ_REL,
        );
        let mut func = func_with(pseudo);
        let head_id = func.blocks[0].insts[0];
        assert_eq!(expand_llsc_atomics(&mut func), Ok(1));
        assert_eq!(
            opcodes(&func),
            [
                AArch64Opcode::Ldaxr,
                AArch64Opcode::AddRR,
                AArch64Opcode::Stlxr,
                AArch64Opcode::Cbnz,
                AArch64Opcode::Ret
            ]
        );
        assert_eq!(func.blocks[0].insts[0], head_id);
        let cbnz = func.inst(func.blocks[0].insts[3]);
        assert_eq!(
            cbnz.operands,
            vec![MachOperand::PReg(W2), MachOperand::Imm(-3)]
        );
        let store = func.inst(func.blocks[0].insts[2]);
        assert_eq!(
            store.operands,
            vec![
                MachOperand::PReg(W2),
                MachOperand::PReg(X1),
                MachOperand::PReg(X4)
            ]
        );
        let block: Vec<_> = func.blocks[0]
            .insts
            .iter()
            .map(|&id| (id, func.inst(id)))
            .collect();
        assert_eq!(
            llsc_internal_branches(&block),
            BTreeSet::from([func.blocks[0].insts[3]])
        );
    }

    #[test]
    fn every_rmw_op_width_and_ordering_selects_exact_exclusives() {
        let mut checked = 0;
        for width in LlscWidth::SINGLE_REGISTER {
            let wide = width == LlscWidth::B64;
            let regs = if wide {
                [X0, X1, W2, X3, X4]
            } else {
                [W0, W1, W2, W3, X4]
            };
            for op in LlscRmwOp::ALL {
                for ordering in [
                    LlscOrdering::RELAXED,
                    LlscOrdering::ACQUIRE,
                    LlscOrdering::RELEASE,
                    LlscOrdering::ACQ_REL,
                ] {
                    let pseudo = rmw(LlscPseudo::Rmw(width).opcode(), regs, op, ordering);
                    let mut func = func_with(pseudo);
                    expand_llsc_atomics(&mut func).unwrap();
                    let ops = opcodes(&func);
                    assert_eq!(ops[0], exclusive_load_opcode(width, ordering.acquire));
                    let store = ops.len() - 3;
                    assert_eq!(ops[store], exclusive_store_opcode(width, ordering.release));
                    assert_eq!(ops[store + 1], AArch64Opcode::Cbnz);
                    for body in &ops[1..store] {
                        assert!(is_llsc_body_alu(*body), "{op:?} {width:?}: {body:?}");
                    }
                    let block: Vec<_> = func.blocks[0]
                        .insts
                        .iter()
                        .map(|&id| (id, func.inst(id)))
                        .collect();
                    assert_eq!(llsc_internal_branches(&block).len(), 1);
                    for &id in &func.blocks[0].insts {
                        crate::aarch64::encode::encode_instruction(func.inst(id))
                            .unwrap_or_else(|e| panic!("{op:?} {width:?}: {e}"));
                    }
                    checked += 1;
                }
            }
        }
        assert_eq!(checked, 4 * 10 * 4);
    }

    #[test]
    fn cmp_swap_expands_with_failure_clrex_and_recognized_exits() {
        for width in LlscWidth::SINGLE_REGISTER {
            let wide = width == LlscWidth::B64;
            let data = |n: PReg| {
                if wide {
                    n
                } else {
                    trust_cg_ir::aarch64_regs::gpr64_to_gpr32(n).unwrap()
                }
            };
            let pseudo = MachInst::new(
                LlscPseudo::CmpSwap(width).opcode(),
                vec![
                    MachOperand::PReg(data(X0)),
                    MachOperand::PReg(W1),
                    MachOperand::PReg(data(X2)),
                    MachOperand::PReg(data(X3)),
                    MachOperand::PReg(X4),
                    MachOperand::Imm(LlscOrdering::ACQUIRE.to_imm()),
                ],
            );
            let mut func = func_with(pseudo);
            expand_llsc_atomics(&mut func).unwrap();
            let ops = opcodes(&func);
            let mut expected = vec![exclusive_load_opcode(width, true)];
            if width.is_sub_word() {
                expected.push(if width == LlscWidth::B8 {
                    AArch64Opcode::Uxtb
                } else {
                    AArch64Opcode::Uxth
                });
            }
            expected.extend([
                AArch64Opcode::CmpRR,
                AArch64Opcode::BCond,
                exclusive_store_opcode(width, false),
                AArch64Opcode::Cbnz,
                AArch64Opcode::BCond,
                AArch64Opcode::Clrex,
                AArch64Opcode::Ret,
            ]);
            assert_eq!(ops, expected, "{width:?}");
            let block: Vec<_> = func.blocks[0]
                .insts
                .iter()
                .map(|&id| (id, func.inst(id)))
                .collect();
            assert_eq!(llsc_internal_branches(&block).len(), 3, "{width:?}");
        }
    }

    #[test]
    fn aliased_or_zero_definitions_and_bad_immediates_fail_closed() {
        // `new` aliases the address.
        let aliased = rmw(
            AArch64Opcode::LlscRmw64,
            [X0, X4, W2, X3, X4],
            LlscRmwOp::Add,
            LlscOrdering::RELAXED,
        );
        let error = expand_llsc_atomics(&mut func_with(aliased)).unwrap_err();
        assert!(matches!(
            error,
            LlscExpansionError::Alias {
                def_index: 1,
                other_index: 4,
                ..
            }
        ));
        assert!(error.to_string().starts_with(LLSC_EXPANSION_TAG), "{error}");
        // Status aliases `old` through the W/X view.
        let aliased = rmw(
            AArch64Opcode::LlscRmw64,
            [X0, X1, W0, X3, X4],
            LlscRmwOp::Xchg,
            LlscOrdering::RELAXED,
        );
        assert!(matches!(
            expand_llsc_atomics(&mut func_with(aliased)),
            Err(LlscExpansionError::Alias { .. })
        ));
        // A discarded (ZR) status would make CBNZ never retry.
        let zero = rmw(
            AArch64Opcode::LlscRmw32,
            [W0, W1, trust_cg_ir::regs::WZR, W3, X4],
            LlscRmwOp::Add,
            LlscOrdering::RELAXED,
        );
        assert!(matches!(
            expand_llsc_atomics(&mut func_with(zero)),
            Err(LlscExpansionError::Operand { index: 2, .. })
        ));
        // A 64-bit access must not accept a W value.
        let narrow = rmw(
            AArch64Opcode::LlscRmw64,
            [X0, X1, W2, W3, X4],
            LlscRmwOp::Add,
            LlscOrdering::RELAXED,
        );
        assert!(matches!(
            expand_llsc_atomics(&mut func_with(narrow)),
            Err(LlscExpansionError::Operand { index: 3, .. })
        ));
        let mut bad_op = rmw(
            AArch64Opcode::LlscRmw32,
            [W0, W1, W2, W3, X4],
            LlscRmwOp::Add,
            LlscOrdering::RELAXED,
        );
        bad_op.operands[5] = MachOperand::Imm(99);
        assert!(matches!(
            expand_llsc_atomics(&mut func_with(bad_op)),
            Err(LlscExpansionError::Operand { index: 5, .. })
        ));
        let mut short = rmw(
            AArch64Opcode::LlscRmw32,
            [W0, W1, W2, W3, X4],
            LlscRmwOp::Add,
            LlscOrdering::RELAXED,
        );
        short.operands.pop();
        let mut func = func_with(short);
        let before = func.clone();
        assert!(matches!(
            expand_llsc_atomics(&mut func),
            Err(LlscExpansionError::OperandCount { .. })
        ));
        assert_eq!(
            opcodes(&func),
            opcodes(&before),
            "failure leaves the stream unchanged"
        );
        // XZR is a legal data value (exchange/store of zero).
        let zero_value = rmw(
            AArch64Opcode::LlscRmw64,
            [X0, X1, W2, XZR, X4],
            LlscRmwOp::Xchg,
            LlscOrdering::RELAXED,
        );
        expand_llsc_atomics(&mut func_with(zero_value)).unwrap();
    }

    #[test]
    fn duplicate_pseudo_placement_and_exhausted_id_domain_fail_closed() {
        let pseudo = rmw(
            AArch64Opcode::LlscRmw64,
            [X0, X1, W2, X3, X4],
            LlscRmwOp::Add,
            LlscOrdering::RELAXED,
        );
        let mut func = func_with(pseudo);
        let head = func.blocks[0].insts[0];
        func.blocks[0].insts.insert(1, head);
        let before = func.clone();
        let error = expand_llsc_atomics(&mut func).unwrap_err();
        assert!(
            matches!(error, LlscExpansionError::Layout { .. }),
            "{error:?}"
        );
        assert!(error.to_string().starts_with(LLSC_EXPANSION_TAG), "{error}");
        assert_eq!(func.insts.len(), before.insts.len());
        assert_eq!(func.blocks[0].insts, before.blocks[0].insts);
        assert_eq!(opcodes(&func), opcodes(&before));

        let last = u32::MAX as usize;
        assert!(new_inst_ids_fit(0, 0));
        assert!(new_inst_ids_fit(usize::MAX, 0));
        assert!(new_inst_ids_fit(last, 1));
        assert!(new_inst_ids_fit(last - 8, 9));
        assert!(!new_inst_ids_fit(last - 7, 9));
        assert!(!new_inst_ids_fit(last + 1, 1));
        assert!(!new_inst_ids_fit(usize::MAX, 2));
    }

    #[test]
    fn template_recognizer_rejects_near_misses() {
        let loop_body = |back: i64, base: PReg| {
            vec![
                MachInst::new(
                    AArch64Opcode::Ldxr,
                    vec![MachOperand::PReg(X0), MachOperand::PReg(X4)],
                ),
                MachInst::new(
                    AArch64Opcode::Stxr,
                    vec![
                        MachOperand::PReg(W2),
                        MachOperand::PReg(X1),
                        MachOperand::PReg(base),
                    ],
                ),
                MachInst::new(
                    AArch64Opcode::Cbnz,
                    vec![MachOperand::PReg(W2), MachOperand::Imm(back)],
                ),
            ]
        };
        let ids = |insts: &[MachInst]| -> Vec<(InstId, MachInst)> {
            insts
                .iter()
                .cloned()
                .enumerate()
                .map(|(i, inst)| (InstId(i as u32), inst))
                .collect()
        };
        let good = ids(&loop_body(-2, X4));
        let view: Vec<_> = good.iter().map(|(id, inst)| (*id, inst)).collect();
        assert_eq!(llsc_internal_branches(&view).len(), 1);
        for bad in [loop_body(-1, X4), loop_body(-2, X3)] {
            let bad = ids(&bad);
            let view: Vec<_> = bad.iter().map(|(id, inst)| (*id, inst)).collect();
            assert!(llsc_internal_branches(&view).is_empty());
        }
        // A memory access inside the window breaks the template.
        let mut with_load = loop_body(-3, X4);
        with_load.insert(
            1,
            MachInst::new(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::PReg(X5_FOR_TEST),
                    MachOperand::PReg(X4),
                    MachOperand::Imm(0),
                ],
            ),
        );
        let with_load = ids(&with_load);
        let view: Vec<_> = with_load.iter().map(|(id, inst)| (*id, inst)).collect();
        assert!(llsc_internal_branches(&view).is_empty());
    }

    const X5_FOR_TEST: PReg = trust_cg_ir::regs::X5;

    fn x(n: u16) -> MachOperand {
        MachOperand::PReg(PReg::new(n))
    }

    fn w(n: u16) -> MachOperand {
        MachOperand::PReg(PReg::new(n + 32))
    }

    fn block_view(func: &MachFunction) -> Vec<(InstId, &MachInst)> {
        func.blocks[0]
            .insts
            .iter()
            .map(|&id| (id, func.inst(id)))
            .collect()
    }

    #[test]
    fn pair_pseudos_expand_to_exact_ldxp_stxp_loops() {
        use AArch64Opcode as O;
        let ordering = MachOperand::Imm(LlscOrdering::ACQ_REL.to_imm());
        let load = MachInst::new(
            O::LlscLoad128,
            vec![x(0), x(1), w(2), x(3), ordering.clone()],
        );
        let store = MachInst::new(
            O::LlscStore128,
            vec![x(0), x(1), w(2), x(4), x(5), x(3), ordering.clone()],
        );
        for (pseudo, expected) in [
            (load, vec![O::Ldaxp, O::Stlxp, O::Cbnz, O::Ret]),
            (store, vec![O::Ldaxp, O::Stlxp, O::Cbnz, O::Ret]),
        ] {
            let mut func = func_with(pseudo);
            expand_llsc_atomics(&mut func).unwrap();
            assert_eq!(opcodes(&func), expected);
            assert_eq!(llsc_internal_branches(&block_view(&func)).len(), 1);
            for &id in &func.blocks[0].insts {
                crate::aarch64::encode::encode_instruction(func.inst(id)).unwrap();
            }
        }
        for op in LlscRmwOp::ALL {
            let mut func = func_with(MachInst::new(
                O::LlscRmw128,
                vec![
                    x(0),
                    x(1),
                    x(2),
                    x(3),
                    w(4),
                    x(5),
                    x(6),
                    x(7),
                    MachOperand::Imm(op.to_imm()),
                    MachOperand::Imm(LlscOrdering::RELAXED.to_imm()),
                ],
            ));
            expand_llsc_atomics(&mut func).unwrap();
            let ops = opcodes(&func);
            assert_eq!(ops[0], O::Ldxp, "{op:?}");
            assert_eq!(ops[ops.len() - 3], O::Stxp, "{op:?}");
            assert_eq!(ops[ops.len() - 2], O::Cbnz, "{op:?}");
            let body = &ops[1..ops.len() - 3];
            let want: &[O] = match op {
                LlscRmwOp::Xchg => &[],
                LlscRmwOp::Add => &[O::AddsRR, O::Adc],
                LlscRmwOp::Sub => &[O::SubsRR, O::Sbc],
                LlscRmwOp::And => &[O::AndRR, O::AndRR],
                LlscRmwOp::Or => &[O::OrrRR, O::OrrRR],
                LlscRmwOp::Xor => &[O::EorRR, O::EorRR],
                _ => &[O::CmpRR, O::Sbcs, O::Csel, O::Csel],
            };
            assert_eq!(body, want, "{op:?}");
            assert_eq!(
                llsc_internal_branches(&block_view(&func)).len(),
                1,
                "{op:?}"
            );
            for &id in &func.blocks[0].insts {
                crate::aarch64::encode::encode_instruction(func.inst(id))
                    .unwrap_or_else(|error| panic!("{op:?}: {error}"));
            }
        }
    }

    #[test]
    fn pair_cmp_swap_writes_back_on_failure_and_is_recognized() {
        use AArch64Opcode as O;
        let mut func = func_with(MachInst::new(
            O::LlscCmpSwap128,
            vec![
                x(0),
                x(1),
                w(2),
                x(3),
                x(4),
                x(5),
                x(6),
                x(7),
                MachOperand::Imm(LlscOrdering::RELEASE.to_imm()),
            ],
        ));
        expand_llsc_atomics(&mut func).unwrap();
        assert_eq!(
            opcodes(&func),
            [
                O::Ldxp,
                O::CmpRR,
                O::BCond,
                O::CmpRR,
                O::BCond,
                O::Stlxp,
                O::Cbnz,
                O::BCond,
                O::Stlxp,
                O::Cbnz,
                O::Ret
            ]
        );
        let insts = func.blocks[0].insts.clone();
        let write_back = func.inst(insts[8]);
        assert_eq!(write_back.operands, vec![w(2), x(0), x(1), x(7)]);
        assert_eq!(llsc_internal_branches(&block_view(&func)).len(), 5);
        for &id in &insts {
            crate::aarch64::encode::encode_instruction(func.inst(id)).unwrap();
        }
        // A write-back that stores anything but the loaded pair is not the
        // template: the intra-block branches are then refused.
        func.inst_mut(insts[8]).operands[1] = x(5);
        assert!(llsc_internal_branches(&block_view(&func)).is_empty());
    }

    #[test]
    fn pair_pseudo_aliases_and_narrow_halves_fail_closed() {
        use AArch64Opcode as O;
        // new_lo aliases the address.
        let aliased = MachInst::new(
            O::LlscRmw128,
            vec![
                x(0),
                x(1),
                x(7),
                x(3),
                w(4),
                x(5),
                x(6),
                x(7),
                MachOperand::Imm(0),
                MachOperand::Imm(0),
            ],
        );
        assert!(matches!(
            expand_llsc_atomics(&mut func_with(aliased)),
            Err(LlscExpansionError::Alias { .. })
        ));
        // A W half of a 128-bit value would silently narrow it.
        let narrow = MachInst::new(
            O::LlscStore128,
            vec![x(0), x(1), w(2), w(4), x(5), x(3), MachOperand::Imm(0)],
        );
        assert!(matches!(
            expand_llsc_atomics(&mut func_with(narrow)),
            Err(LlscExpansionError::Operand { index: 3, .. })
        ));
        // Loaded halves must be distinct registers (LDXP Rt == Rt2 is
        // constrained unpredictable).
        let same = MachInst::new(
            O::LlscLoad128,
            vec![x(0), x(0), w(2), x(3), MachOperand::Imm(0)],
        );
        assert!(matches!(
            expand_llsc_atomics(&mut func_with(same)),
            Err(LlscExpansionError::Alias { .. })
        ));
    }

    fn flagged(mut inst: MachInst) -> MachInst {
        inst.flags
            .insert(trust_cg_ir::inst::InstFlags::SPILL_SLOT_ACCESS);
        inst
    }

    fn fp_access(opcode: AArch64Opcode, data: PReg, offset: i64) -> MachInst {
        MachInst::new(
            opcode,
            vec![
                MachOperand::PReg(data),
                MachOperand::MemOp {
                    base: trust_cg_ir::aarch64_regs::X29,
                    offset,
                },
            ],
        )
    }

    /// An expanded 64-bit fetch-add loop with `extra` inserted at `at`.
    fn expanded_rmw_with(at: usize, extra: MachInst) -> MachFunction {
        let mut func = func_with(rmw(
            AArch64Opcode::LlscRmw64,
            [X0, X1, W2, X3, X4],
            LlscRmwOp::Add,
            LlscOrdering::ACQ_REL,
        ));
        expand_llsc_atomics(&mut func).unwrap();
        let id = func.push_inst(extra);
        func.blocks[0].insts.insert(at, id);
        func
    }

    #[test]
    fn exclusive_windows_of_every_expanded_pseudo_are_clean() {
        use AArch64Opcode as O;
        let ordering = LlscOrdering::ACQ_REL.to_imm();
        let pseudos = [
            rmw(
                O::LlscRmw32,
                [W0, W1, W2, W3, X4],
                LlscRmwOp::Xchg,
                LlscOrdering::RELAXED,
            ),
            MachInst::new(
                O::LlscCmpSwap64,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(W2),
                    MachOperand::PReg(X1),
                    MachOperand::PReg(X3),
                    MachOperand::PReg(X4),
                    MachOperand::Imm(ordering),
                ],
            ),
            MachInst::new(
                O::LlscCmpSwap128,
                vec![
                    x(0),
                    x(1),
                    w(2),
                    x(3),
                    x(4),
                    x(5),
                    x(6),
                    x(7),
                    MachOperand::Imm(ordering),
                ],
            ),
            MachInst::new(
                O::LlscLoad128,
                vec![x(0), x(1), w(2), x(3), MachOperand::Imm(ordering)],
            ),
        ];
        for pseudo in pseudos {
            let opcode = pseudo.opcode;
            let mut func = func_with(pseudo);
            // Spill traffic around the pseudo is outside the window.
            let before = func.push_inst(flagged(fp_access(O::LdrRI, X4, -16)));
            func.blocks[0].insts.insert(0, before);
            let after = func.push_inst(flagged(fp_access(O::StrRI, X0, -24)));
            let last = func.blocks[0].insts.len() - 1;
            func.blocks[0].insts.insert(last + 1, after);
            expand_llsc_atomics(&mut func).unwrap();
            assert_eq!(check_exclusive_windows(&func), Ok(1), "{opcode:?}");
        }
        // No exclusive at all: nothing examined.
        let plain = func_with(fp_access(O::LdrRI, X4, -16));
        assert_eq!(check_exclusive_windows(&plain), Ok(0));
    }

    #[test]
    fn spill_access_inside_an_exclusive_window_is_refused_by_name() {
        // [LDAXR, ADD, STLXR, CBNZ, RET]: a reload between the load-exclusive
        // and the store-exclusive, at either position inside the window.
        for at in [1, 2] {
            let func = expanded_rmw_with(at, flagged(fp_access(AArch64Opcode::LdrRI, X3, -16)));
            let error = check_exclusive_windows(&func).unwrap_err();
            assert!(
                matches!(error, ExclusiveWindowError::SpillAccess { position, .. } if position == at),
                "{error:?}"
            );
            assert!(error.to_string().contains(LLSC_SPILL_WINDOW_TAG), "{error}");
        }
        // A spill store after the store-exclusive is outside the window.
        let after = expanded_rmw_with(3, flagged(fp_access(AArch64Opcode::StrRI, X0, -24)));
        assert_eq!(check_exclusive_windows(&after), Ok(1));
    }

    #[test]
    fn memory_access_or_call_inside_an_exclusive_window_is_refused() {
        let load = expanded_rmw_with(1, fp_access(AArch64Opcode::LdrRI, X3, -16));
        let error = check_exclusive_windows(&load).unwrap_err();
        assert!(
            matches!(error, ExclusiveWindowError::MemoryAccess { .. }),
            "{error:?}"
        );
        assert!(error.to_string().contains(LLSC_WINDOW_TAG), "{error}");
        let call = expanded_rmw_with(
            2,
            MachInst::new(
                AArch64Opcode::Bl,
                vec![MachOperand::Symbol("callee".to_string())],
            ),
        );
        assert!(matches!(
            check_exclusive_windows(&call),
            Err(ExclusiveWindowError::MemoryAccess { .. })
        ));
    }

    #[test]
    fn exclusive_window_open_across_a_block_boundary_is_followed() {
        // entry: LDAXR (no store-exclusive) -> next: reload, STLXR. The reload
        // runs with the monitor still open on the only path into `next`.
        let mut func = MachFunction::new("open_window".into(), Signature::new(vec![], vec![]));
        let entry = func.entry;
        let next = func.create_block();
        let load = func.push_inst(MachInst::new(
            AArch64Opcode::Ldaxr,
            vec![MachOperand::PReg(X0), MachOperand::PReg(X4)],
        ));
        func.append_inst(entry, load);
        let reload = func.push_inst(flagged(fp_access(AArch64Opcode::LdrRI, X1, -16)));
        func.append_inst(next, reload);
        let store = func.push_inst(MachInst::new(
            AArch64Opcode::Stlxr,
            vec![
                MachOperand::PReg(W2),
                MachOperand::PReg(X1),
                MachOperand::PReg(X4),
            ],
        ));
        func.append_inst(next, store);
        func.add_edge(entry, next);
        assert!(matches!(
            check_exclusive_windows(&func),
            Err(ExclusiveWindowError::SpillAccess { block: 1, .. })
        ));
        // CLREX closes the window before the block ends.
        let clrex = func.push_inst(MachInst::new(AArch64Opcode::Clrex, vec![]));
        func.append_inst(entry, clrex);
        assert_eq!(check_exclusive_windows(&func), Ok(1));
    }
}
