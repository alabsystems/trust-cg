// x86_pass_opt_out_installers.rs - tracked opt-outs for x86 O2 machine passes
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The tracked opt-out installers for `X86BlockMerge`, `X86LoopRotate` and
//! the x86 LICM pure-call tier (`-Ztrust-ir-cg-args=no-x86-block-merge`,
//! `no-x86-loop-rotate`, `no-x86-pure-call-hoist`).
//!
//! Each installer writes a process-global `OnceLock`, so these checks live in
//! their own test binary (one process) and in ONE test function, which fixes
//! their order: the default-on arm must run before the installer decides the
//! default for the rest of the process. In a pass's unit-test binary the
//! installer would decide the default for every other test there.
//!
//! Each pass is checked in both directions on the same input: with nothing
//! installed it changes the function, so the opt-out arm cannot pass
//! vacuously on a function the pass would not have touched anyway.

use trust_cg_ir::regs::RegClass;
use trust_cg_ir::x86_64_regs::{RAX, RDI};
use trust_cg_ir::{InstFlags, VReg, X86CondCode, X86Opcode};
use trust_cg_lower::X86ISelBlock;
use trust_cg_lower::function::Signature;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::types::Type;
use trust_cg_lower::x86_64_isel::{X86CallArgReg, X86CallResultReg};
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};
use trust_cg_opt::{X86BlockMerge, X86LoopInvariantCodeMotion, X86LoopRotate, X86MachinePass};

fn jmp(target: u32) -> X86ISelInst {
    X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(target))])
}

fn vr(id: u32) -> X86ISelOperand {
    X86ISelOperand::VReg(VReg {
        id,
        class: RegClass::Gpr64,
    })
}

fn function(name: &str, blocks: u32, returns: Vec<Type>) -> X86ISelFunction {
    let mut func = X86ISelFunction::new(
        name.to_string(),
        Signature {
            params: vec![],
            returns,
        },
    );
    for b in 0..blocks {
        func.blocks.insert(
            Block(b),
            X86ISelBlock {
                insts: vec![],
                successors: vec![],
            },
        );
    }
    func.block_order = (0..blocks).map(Block).collect();
    func
}

/// `b0 -> b1 -> b2`: each block's only predecessor ends in exactly `Jmp` to
/// it, so the pass merges the whole chain (it runs to a fixpoint) into one
/// block.
fn mergeable_chain() -> X86ISelFunction {
    let mut func = function("merge", 3, vec![Type::I64]);
    func.push_inst(Block(0), jmp(1));
    func.blocks.get_mut(&Block(0)).unwrap().successors = vec![Block(1)];
    func.push_inst(Block(1), X86ISelInst::new(X86Opcode::Nop, vec![]));
    func.push_inst(Block(1), jmp(2));
    func.blocks.get_mut(&Block(1)).unwrap().successors = vec![Block(2)];
    func.push_inst(Block(2), X86ISelInst::new(X86Opcode::Ret, vec![]));
    func
}

/// A top-tested loop the pass rotates: preheader(0) -> header(1){cmp; jcc NE
/// body; jmp exit}; body(2) is the latch, with enough work to clear the pass's
/// size floor, ending `Jmp header`; exit(3) returns.
fn rotatable_loop() -> X86ISelFunction {
    let mut func = function("rotate", 4, vec![]);
    func.push_inst(Block(0), jmp(1));
    func.blocks.get_mut(&Block(0)).unwrap().successors = vec![Block(1)];
    func.push_inst(
        Block(1),
        X86ISelInst::new(X86Opcode::CmpRI, vec![vr(0), X86ISelOperand::Imm(7)]),
    );
    func.push_inst(
        Block(1),
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::NE),
                X86ISelOperand::Block(Block(2)),
            ],
        ),
    );
    func.push_inst(Block(1), jmp(3));
    func.blocks.get_mut(&Block(1)).unwrap().successors = vec![Block(2), Block(3)];
    for _ in 0..16 {
        func.push_inst(
            Block(2),
            X86ISelInst::new(X86Opcode::AddRR, vec![vr(0), vr(0), vr(1)]),
        );
    }
    func.push_inst(Block(2), jmp(1));
    func.blocks.get_mut(&Block(2)).unwrap().successors = vec![Block(1)];
    func.push_inst(Block(3), X86ISelInst::new(X86Opcode::Ret, vec![]));
    func
}

/// A loop that certainly runs (`v20 = 0; cmp v20, 10; jb body`) whose body
/// opens with the pure-call cluster `mov rdi, v30; call pure_fn; mov v60, rax`
/// on an invariant argument: preheader(0) -> header(1){jb 2; jmp 4};
/// body(2) -> latch(3){v20 += 1; jmp 1}; exit(4) returns. LICM's pure-call
/// tier moves the cluster into the preheader.
fn pure_call_loop() -> X86ISelFunction {
    let mut func = function("pure_call", 5, vec![Type::I64]);
    func.next_vreg = 64;
    func.push_inst(
        Block(0),
        X86ISelInst::new(X86Opcode::MovRI, vec![vr(20), X86ISelOperand::Imm(0)]),
    );
    func.push_inst(
        Block(0),
        X86ISelInst::new(X86Opcode::MovRI, vec![vr(30), X86ISelOperand::Imm(1)]),
    );
    func.push_inst(Block(0), jmp(1));
    func.blocks.get_mut(&Block(0)).unwrap().successors = vec![Block(1)];
    func.push_inst(
        Block(1),
        X86ISelInst::new(X86Opcode::MovRI, vec![vr(22), X86ISelOperand::Imm(10)]),
    );
    func.push_inst(
        Block(1),
        X86ISelInst::new(X86Opcode::CmpRR, vec![vr(20), vr(22)]),
    );
    func.push_inst(
        Block(1),
        X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(Block(2)),
            ],
        ),
    );
    func.push_inst(Block(1), jmp(4));
    func.blocks.get_mut(&Block(1)).unwrap().successors = vec![Block(2), Block(4)];
    func.push_inst(
        Block(2),
        X86ISelInst::new(X86Opcode::MovRR, vec![X86ISelOperand::PReg(RDI), vr(30)]),
    );
    let call = X86ISelInst::new(
        X86Opcode::Call,
        vec![X86ISelOperand::Symbol("pure_fn".to_string())],
    );
    let mut flags = call.flags;
    flags.insert(InstFlags::PURE_CALL_HOISTABLE);
    func.push_inst(
        Block(2),
        X86ISelInst::with_flags(call.opcode, call.operands, flags)
            .with_call_arg_regs(vec![X86CallArgReg::full(RDI)])
            .with_call_result_regs(vec![X86CallResultReg::new(RAX, 64)]),
    );
    func.push_inst(
        Block(2),
        X86ISelInst::new(X86Opcode::MovRR, vec![vr(60), X86ISelOperand::PReg(RAX)]),
    );
    func.push_inst(Block(2), jmp(3));
    func.blocks.get_mut(&Block(2)).unwrap().successors = vec![Block(3)];
    func.push_inst(
        Block(3),
        X86ISelInst::new(
            X86Opcode::AddRI,
            vec![vr(20), vr(20), X86ISelOperand::Imm(1)],
        ),
    );
    func.push_inst(Block(3), jmp(1));
    func.blocks.get_mut(&Block(3)).unwrap().successors = vec![Block(1)];
    func.push_inst(Block(4), X86ISelInst::new(X86Opcode::Ret, vec![]));
    func
}

fn calls_in(func: &X86ISelFunction, b: u32) -> usize {
    func.blocks[&Block(b)]
        .insts
        .iter()
        .filter(|i| i.opcode == X86Opcode::Call)
        .count()
}

#[test]
fn opt_out_installers_disable_their_pass_and_refuse_a_conflicting_reinstall() {
    for var in ["TCG_NO_X86_BLOCK_MERGE", "TCG_NO_X86_ROTATE"] {
        assert!(
            std::env::var_os(var).is_none(),
            "{var} is set in this test's environment; the default-on arm cannot be measured"
        );
    }

    // Default on: nothing installed, both passes change their input.
    let mut merged = mergeable_chain();
    assert!(
        X86BlockMerge::new().run(&mut merged),
        "block merge must be on by default"
    );
    assert_eq!(merged.block_order.len(), 1, "the chain merged into b0");
    let mut rotated = rotatable_loop();
    assert!(
        X86LoopRotate.run(&mut rotated),
        "loop rotation must be on by default"
    );
    // Both LICM policies run the pure-call tier by default.
    for mut licm in [
        X86LoopInvariantCodeMotion::pure_only(),
        X86LoopInvariantCodeMotion::with_invariant_load_hoisting(),
    ] {
        let mut hoisted = pure_call_loop();
        assert!(
            licm.run(&mut hoisted),
            "the pure-call tier must be on by default"
        );
        assert_eq!(
            (calls_in(&hoisted, 0), calls_in(&hoisted, 2)),
            (1, 0),
            "the call moved into the preheader"
        );
    }

    // Installed opt-out: the same inputs are left untouched.
    assert!(trust_cg_opt::x86_block_merge::set_block_merge_disabled(
        true
    ));
    assert!(trust_cg_opt::x86_rotate::set_loop_rotate_disabled(true));
    assert!(trust_cg_opt::x86_licm::set_pure_call_hoist_disabled(true));
    let mut kept = mergeable_chain();
    assert!(
        !X86BlockMerge::new().run(&mut kept),
        "the opt-out must disable block merge"
    );
    assert_eq!(kept.block_order.len(), 3);
    let mut unrotated = rotatable_loop();
    assert!(
        !X86LoopRotate.run(&mut unrotated),
        "the opt-out must disable loop rotation"
    );
    let latch = &unrotated.blocks[&Block(2)];
    assert_eq!(
        latch.successors,
        vec![Block(1)],
        "the latch keeps its back edge"
    );
    for mut licm in [
        X86LoopInvariantCodeMotion::pure_only(),
        X86LoopInvariantCodeMotion::with_invariant_load_hoisting(),
    ] {
        let mut kept_call = pure_call_loop();
        let _ = licm.run(&mut kept_call);
        assert_eq!(
            (calls_in(&kept_call, 0), calls_in(&kept_call, 2)),
            (0, 1),
            "the opt-out must keep the call in its loop"
        );
    }

    // One policy per process: an equal reinstall is accepted, a different one refused.
    assert!(trust_cg_opt::x86_block_merge::set_block_merge_disabled(
        true
    ));
    assert!(!trust_cg_opt::x86_block_merge::set_block_merge_disabled(
        false
    ));
    assert!(trust_cg_opt::x86_rotate::set_loop_rotate_disabled(true));
    assert!(!trust_cg_opt::x86_rotate::set_loop_rotate_disabled(false));
    assert!(trust_cg_opt::x86_licm::set_pure_call_hoist_disabled(true));
    assert!(!trust_cg_opt::x86_licm::set_pure_call_hoist_disabled(false));
}
