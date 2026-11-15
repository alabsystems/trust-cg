// trust-cg-opt - x86-64 pure-trap block predicate shared by the machine passes
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The ONE predicate that decides whether an [`X86ISelFunction`] block is a
//! **pure trap**: a dead-end sink a correct program never enters, which does
//! no observable work before the process dies. Every x86 machine pass that
//! elides, re-targets, re-lays-out or deletes a guard's failure edge
//! (`x86_vectorize`, `x86_bounds_check_elim`, `x86_branch_layout`,
//! `x86_cmov_swap`) keys on this definition, so the bridge's trap shapes are
//! admitted or refused identically everywhere.
//!
//! # Accepted shapes
//!
//! The block must exist, have NO successor edges, and — ignoring pseudo
//! padding (`Nop`, `NopMulti`, `Phi`, `StackAlloc`: none encodes an
//! observable operation) — consist of exactly one of:
//!
//! 1. `[Ud2]`: the ISel synthetic trap (`emit_synthetic_trap_block`, the fail
//!    edge of an unfused MIR `Assert`) and every expanded proof carrier's fail
//!    target.
//! 2. `[Call Symbol("abort"), Ud2]`: the bridge's shared panic=abort assert
//!    block (`emit_panic_abort_trap`: libc `abort()` for the exit-134 panic
//!    contract, then `Unreachable`, which selects to `Ud2`). The call must
//!    carry no argument registers, no result registers and no operand other
//!    than the symbol — `abort` takes nothing, returns nothing and never
//!    returns.
//!
//! Both shapes diverge unconditionally. A pass that has separately proven a
//! guard can never fail may therefore drop or re-target the edge into such a
//! block without changing what any passing program computes; the only thing
//! the failure path could ever have decided is HOW the process dies, and that
//! path is exactly the one the proof shows is never taken. Anything else — a
//! second real instruction, a call to any other symbol, a call with argument
//! or result registers, a successor edge — is refused, and the caller must
//! treat the edge as a live exit.

use trust_cg_ir::InstFlags;
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

/// The libc symbol the bridge's panic=abort trap block calls before its `Ud2`
/// (`emit_panic_abort_trap`). Matched exactly, as a plain `Symbol`.
pub const PANIC_ABORT_SYMBOL: &str = "abort";

/// True iff `block` is a pure trap sink in the sense of the module doc:
/// no successors and, modulo pseudo padding, exactly `[Ud2]` or
/// `[Call Symbol("abort") (no arg/result registers), Ud2]`.
pub fn is_pure_trap_block(func: &X86ISelFunction, block: Block) -> bool {
    let Some(b) = func.blocks.get(&block) else {
        return false;
    };
    if !b.successors.is_empty() {
        return false;
    }
    let mut real = b
        .insts
        .iter()
        .filter(|inst| !is_pseudo_padding(inst.opcode));
    match (real.next(), real.next(), real.next()) {
        (Some(only), None, None) => only.opcode == X86Opcode::Ud2,
        (Some(call), Some(trap), None) => {
            is_panic_abort_call(call) && trap.opcode == X86Opcode::Ud2
        }
        _ => false,
    }
}

/// True iff `block` is a **divergent sink**: a no-successor block that can
/// never return control to its predecessor, but — unlike a pure trap — may do
/// observable work before the process dies.
///
/// This is the shape of the bridge's faithful Rust panic raise
/// (`assert_panic::emit`, the unconditional native route since upstream
/// `c876e3bd0`): argument marshalling for the lang item's operands — `index`,
/// `len` and the caller `&Location` for `panic_bounds_check` — emitted INTO
/// this block by `lower_direct_call_args`, then the diverging `Call`, then
/// `Ud2` for the `!` return.
///
/// # Accepted shape
///
/// No successor edges and, ignoring pseudo padding, a straight-line run that
///
/// * ends in `Ud2`,
/// * contains EXACTLY ONE call (`Call`/`CallR`/`CallM`), and
/// * writes no memory and holds no other branch or terminator.
///
/// Control therefore cannot leave the block: either the call diverges, or it
/// returns and the `Ud2` traps.
///
/// # This is NOT a weaker [`is_pure_trap_block`], and must not be used as one
///
/// A pure trap does no observable work, so a pass may drop, re-target **or
/// conditionalize** an edge into one freely. A divergent sink DOES observable
/// work — it runs the panic hook with the real payload and caller location —
/// so an edge into one may be discarded ONLY by a caller that has separately
/// **proven the edge is never taken**, and the sink's content is then
/// irrelevant because no execution reaches it. A pass that instead needs
/// "nothing happens down here" because it makes both sides of a branch
/// execute (`x86_cmov_swap`) must keep using [`is_pure_trap_block`]; this
/// predicate would be unsound there.
///
/// # What this predicate does NOT certify
///
/// The marshalling instructions **read vregs defined outside this block** (the
/// guard's `index` and `len`). A caller that discards those definitions must
/// also remove this block, or it leaves dangling operand reads behind.
pub fn is_divergent_sink(func: &X86ISelFunction, block: Block) -> bool {
    let Some(b) = func.blocks.get(&block) else {
        return false;
    };
    if !b.successors.is_empty() {
        return false;
    }
    let real: Vec<&X86ISelInst> = b
        .insts
        .iter()
        .filter(|inst| !is_pseudo_padding(inst.opcode))
        .collect();
    let Some((last, head)) = real.split_last() else {
        return false;
    };
    if last.opcode != X86Opcode::Ud2 {
        return false;
    }
    let mut calls = 0usize;
    for inst in head {
        let flags = inst.opcode.default_flags();
        if flags.contains(InstFlags::IS_CALL) {
            calls += 1;
            continue;
        }
        let forbidden = InstFlags::WRITES_MEMORY
            .union(InstFlags::IS_TERMINATOR)
            .union(InstFlags::IS_BRANCH)
            .union(InstFlags::IS_RETURN);
        if !flags.intersection(forbidden).is_empty() {
            return false;
        }
    }
    calls == 1
}

/// Pseudo opcodes that may pad a trap block without making it "do work": the
/// encoded no-ops and the frame/SSA pseudos that emit no bytes of their own.
fn is_pseudo_padding(op: X86Opcode) -> bool {
    matches!(
        op,
        X86Opcode::Nop | X86Opcode::NopMulti | X86Opcode::Phi | X86Opcode::StackAlloc
    )
}

/// True iff `inst` is exactly the bridge's `abort()` call: a direct `Call`
/// whose only operand is `Symbol("abort")`, consuming no argument registers
/// and defining no result registers.
fn is_panic_abort_call(inst: &X86ISelInst) -> bool {
    inst.opcode == X86Opcode::Call
        && matches!(
            inst.operands.as_slice(),
            [X86ISelOperand::Symbol(symbol)] if symbol == PANIC_ABORT_SYMBOL
        )
        && inst.call_arg_regs.is_empty()
        && inst
            .call_result_regs
            .as_ref()
            .is_none_or(|results| results.is_empty())
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::x86_64_regs::{RAX, RDI};
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::x86_64_isel::{X86CallArgReg, X86CallResultReg};

    fn func_with_block(insts: Vec<X86ISelInst>, succs: Vec<Block>) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![],
        };
        let mut f = X86ISelFunction::new("trap_test".to_string(), sig);
        f.ensure_block(Block(0));
        let b = f.blocks.get_mut(&Block(0)).unwrap();
        b.insts = insts;
        b.successors = succs;
        f
    }

    fn ud2() -> X86ISelInst {
        X86ISelInst::new(X86Opcode::Ud2, vec![])
    }

    fn call(symbol: &str) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::Call,
            vec![X86ISelOperand::Symbol(symbol.to_string())],
        )
    }

    #[test]
    fn accepts_bare_ud2() {
        let f = func_with_block(vec![ud2()], vec![]);
        assert!(is_pure_trap_block(&f, Block(0)));
    }

    #[test]
    fn accepts_abort_call_then_ud2() {
        let f = func_with_block(vec![call("abort"), ud2()], vec![]);
        assert!(is_pure_trap_block(&f, Block(0)));
    }

    #[test]
    fn accepts_pseudo_padding_around_the_trap() {
        let f = func_with_block(
            vec![
                X86ISelInst::new(X86Opcode::Nop, vec![]),
                call("abort"),
                X86ISelInst::new(X86Opcode::Nop, vec![]),
                ud2(),
            ],
            vec![],
        );
        assert!(is_pure_trap_block(&f, Block(0)));
    }

    #[test]
    fn rejects_absent_block() {
        let f = func_with_block(vec![ud2()], vec![]);
        assert!(!is_pure_trap_block(&f, Block(7)));
    }

    #[test]
    fn rejects_call_to_other_symbol() {
        let f = func_with_block(vec![call("exit"), ud2()], vec![]);
        assert!(!is_pure_trap_block(&f, Block(0)));
    }

    #[test]
    fn rejects_abort_call_without_ud2() {
        let f = func_with_block(vec![call("abort")], vec![]);
        assert!(!is_pure_trap_block(&f, Block(0)));
    }

    #[test]
    fn rejects_trap_block_with_a_successor() {
        let f = func_with_block(vec![call("abort"), ud2()], vec![Block(0)]);
        assert!(!is_pure_trap_block(&f, Block(0)));
        let g = func_with_block(vec![ud2()], vec![Block(0)]);
        assert!(!is_pure_trap_block(&g, Block(0)));
    }

    #[test]
    fn rejects_abort_call_with_registers_or_extra_operands() {
        let with_args = call("abort").with_call_arg_regs(vec![X86CallArgReg::new(RDI, 64)]);
        let f = func_with_block(vec![with_args, ud2()], vec![]);
        assert!(!is_pure_trap_block(&f, Block(0)));
        let with_result = call("abort").with_call_result_regs(vec![X86CallResultReg::new(RAX, 64)]);
        let g = func_with_block(vec![with_result, ud2()], vec![]);
        assert!(!is_pure_trap_block(&g, Block(0)));
        let h = func_with_block(
            vec![
                X86ISelInst::new(
                    X86Opcode::Call,
                    vec![
                        X86ISelOperand::Symbol("abort".to_string()),
                        X86ISelOperand::Imm(0),
                    ],
                ),
                ud2(),
            ],
            vec![],
        );
        assert!(!is_pure_trap_block(&h, Block(0)));
    }

    #[test]
    fn rejects_real_work_before_the_trap() {
        let f = func_with_block(
            vec![
                X86ISelInst::new(
                    X86Opcode::MovRI,
                    vec![
                        X86ISelOperand::VReg(trust_cg_ir::regs::VReg::new(
                            0,
                            trust_cg_ir::regs::RegClass::Gpr64,
                        )),
                        X86ISelOperand::Imm(9),
                    ],
                ),
                ud2(),
            ],
            vec![],
        );
        assert!(!is_pure_trap_block(&f, Block(0)));
        let two_ud2 = func_with_block(vec![ud2(), ud2()], vec![]);
        assert!(!is_pure_trap_block(&two_ud2, Block(0)));
    }
    // ---- is_divergent_sink: the faithful panic raise shape --------------
    //
    // Upstream `c876e3bd0` routes every MIR assertion through
    // `assert_panic::emit`, whose `lower_direct_call_args` marshals the lang
    // item's operands INTO the raise block. These pin the accepted shape and,
    // deliberately first, everything adjacent to it that is REFUSED.

    fn mov_rr(dst: u32, src: u32) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![
                X86ISelOperand::VReg(trust_cg_ir::regs::VReg::new(
                    dst,
                    trust_cg_ir::regs::RegClass::Gpr64,
                )),
                X86ISelOperand::VReg(trust_cg_ir::regs::VReg::new(
                    src,
                    trust_cg_ir::regs::RegClass::Gpr64,
                )),
            ],
        )
    }

    /// The marshalled diverging call: three argument registers (index, len,
    /// &Location), no result registers, a Rust mangled symbol — NOT `abort`.
    fn panic_bounds_check_call() -> X86ISelInst {
        call("_ZN4core9panicking18panic_bounds_check17h0000000000000000E")
            .with_call_arg_regs(vec![X86CallArgReg::new(RDI, 64)])
    }

    #[test]
    fn accepts_the_bridge_panic_raise_shape() {
        // marshalling, the diverging call, then Ud2 for the `!` return.
        let f = func_with_block(
            vec![mov_rr(1, 2), mov_rr(3, 4), panic_bounds_check_call(), ud2()],
            vec![],
        );
        assert!(is_divergent_sink(&f, Block(0)));
        // And it is NOT a pure trap — the two predicates stay disjoint, so no
        // caller can get the weaker guarantee by accident.
        assert!(!is_pure_trap_block(&f, Block(0)));
    }

    #[test]
    fn rejects_divergent_sink_without_a_trailing_ud2() {
        // A call that is merely the last instruction does not prove control
        // cannot fall out of the block.
        let f = func_with_block(vec![mov_rr(1, 2), panic_bounds_check_call()], vec![]);
        assert!(!is_divergent_sink(&f, Block(0)));
    }

    #[test]
    fn rejects_divergent_sink_with_a_successor() {
        let f = func_with_block(vec![panic_bounds_check_call(), ud2()], vec![Block(1)]);
        assert!(!is_divergent_sink(&f, Block(0)));
    }

    #[test]
    fn rejects_divergent_sink_with_two_calls() {
        // Two calls is not the raise shape; the second could return.
        let f = func_with_block(
            vec![panic_bounds_check_call(), panic_bounds_check_call(), ud2()],
            vec![],
        );
        assert!(!is_divergent_sink(&f, Block(0)));
    }

    #[test]
    fn rejects_divergent_sink_with_no_call_at_all() {
        // `[Ud2]` and `[Call abort, Ud2]` are `is_pure_trap_block`'s business.
        // This predicate requires exactly one call, so a bare trap is refused
        // here and the two predicates cannot be confused.
        let bare = func_with_block(vec![ud2()], vec![]);
        assert!(!is_divergent_sink(&bare, Block(0)));
        assert!(is_pure_trap_block(&bare, Block(0)));

        let marshal_only = func_with_block(vec![mov_rr(1, 2), ud2()], vec![]);
        assert!(!is_divergent_sink(&marshal_only, Block(0)));
    }

    #[test]
    fn rejects_divergent_sink_that_writes_memory() {
        // A store is not argument marshalling. Refused even though the block
        // is unreachable under the caller's dead-guard proof: the predicate
        // asserts a SHAPE, and a caller may rely on that shape for more than
        // reachability.
        let store = X86ISelInst::new(
            X86Opcode::MovMR,
            vec![
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::VReg(trust_cg_ir::regs::VReg::new(
                        1,
                        trust_cg_ir::regs::RegClass::Gpr64,
                    ))),
                    disp: 0,
                },
                X86ISelOperand::VReg(trust_cg_ir::regs::VReg::new(
                    2,
                    trust_cg_ir::regs::RegClass::Gpr64,
                )),
            ],
        );
        let f = func_with_block(vec![store, panic_bounds_check_call(), ud2()], vec![]);
        assert!(!is_divergent_sink(&f, Block(0)));
    }

    #[test]
    fn rejects_divergent_sink_with_an_interior_branch() {
        let jcc = X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(1))]);
        let f = func_with_block(vec![jcc, panic_bounds_check_call(), ud2()], vec![]);
        assert!(!is_divergent_sink(&f, Block(0)));
    }

    #[test]
    fn rejects_absent_block_for_divergent_sink() {
        let f = func_with_block(vec![panic_bounds_check_call(), ud2()], vec![]);
        assert!(!is_divergent_sink(&f, Block(7)));
    }

    #[test]
    fn divergent_sink_accepts_pseudo_padding_around_the_raise() {
        let f = func_with_block(
            vec![
                X86ISelInst::new(X86Opcode::Nop, vec![]),
                panic_bounds_check_call(),
                X86ISelInst::new(X86Opcode::Nop, vec![]),
                ud2(),
            ],
            vec![],
        );
        assert!(is_divergent_sink(&f, Block(0)));
    }
}
