// x86_loop_pass_opt_out_installers.rs - tracked whole-pass opt-outs for x86 LICM and unrolling
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The tracked opt-out installers for the whole of x86 LICM and for
//! `X86LoopUnroll` (`-Ztrust-ir-cg-args=no-x86-licm`, `no-x86-loop-unroll`).
//!
//! Each installer writes a process-global `OnceLock`, so these checks live in
//! their own test binary (one process) and in ONE test function, which fixes
//! their order: the default-on arm must run before the installer decides the
//! default for the rest of the process. They are not in
//! `x86_pass_opt_out_installers.rs`: disabling the whole of LICM there would
//! make that binary's pure-call opt-out check pass vacuously.
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
use trust_cg_opt::{X86LoopInvariantCodeMotion, X86LoopUnroll, X86MachinePass};

fn jmp(target: u32) -> X86ISelInst {
    X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(target))])
}

fn jcc(cc: X86CondCode, target: u32) -> X86ISelInst {
    X86ISelInst::new(
        X86Opcode::Jcc,
        vec![
            X86ISelOperand::CondCode(cc),
            X86ISelOperand::Block(Block(target)),
        ],
    )
}

fn vr(id: u32) -> X86ISelOperand {
    X86ISelOperand::VReg(VReg {
        id,
        class: RegClass::Gpr64,
    })
}

fn imm(v: i64) -> X86ISelOperand {
    X86ISelOperand::Imm(v)
}

fn inst(op: X86Opcode, ops: Vec<X86ISelOperand>) -> X86ISelInst {
    X86ISelInst::new(op, ops)
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
    func.next_vreg = 100;
    func
}

fn fill(func: &mut X86ISelFunction, b: u32, insts: Vec<X86ISelInst>, successors: Vec<u32>) {
    let block = func.blocks.get_mut(&Block(b)).unwrap();
    block.insts = insts;
    block.successors = successors.into_iter().map(Block).collect();
}

/// A loop that certainly runs (`v20 = 0; cmp v20, 10; jb body`) whose body
/// opens with the pure-call cluster `mov rdi, v30; call pure_fn; mov v60, rax`
/// on an invariant argument: preheader(0) -> header(1){jb 2; jmp 4};
/// body(2) -> latch(3){v20 += 1; jmp 1}; exit(4) returns. LICM moves the
/// cluster into the preheader.
fn hoistable_loop() -> X86ISelFunction {
    let mut func = function("licm", 5, vec![Type::I64]);
    fill(
        &mut func,
        0,
        vec![
            inst(X86Opcode::MovRI, vec![vr(20), imm(0)]),
            inst(X86Opcode::MovRI, vec![vr(30), imm(1)]),
            jmp(1),
        ],
        vec![1],
    );
    fill(
        &mut func,
        1,
        vec![
            inst(X86Opcode::MovRI, vec![vr(22), imm(10)]),
            inst(X86Opcode::CmpRR, vec![vr(20), vr(22)]),
            jcc(X86CondCode::B, 2),
            jmp(4),
        ],
        vec![2, 4],
    );
    let call = inst(
        X86Opcode::Call,
        vec![X86ISelOperand::Symbol("pure_fn".to_string())],
    );
    let mut flags = call.flags;
    flags.insert(InstFlags::PURE_CALL_HOISTABLE);
    let call = X86ISelInst::with_flags(call.opcode, call.operands, flags)
        .with_call_arg_regs(vec![X86CallArgReg::full(RDI)])
        .with_call_result_regs(vec![X86CallResultReg::new(RAX, 64)]);
    fill(
        &mut func,
        2,
        vec![
            inst(X86Opcode::MovRR, vec![X86ISelOperand::PReg(RDI), vr(30)]),
            call,
            inst(X86Opcode::MovRR, vec![vr(60), X86ISelOperand::PReg(RAX)]),
            jmp(3),
        ],
        vec![3],
    );
    fill(
        &mut func,
        3,
        vec![inst(X86Opcode::AddRI, vec![vr(20), vr(20), imm(1)]), jmp(1)],
        vec![1],
    );
    fill(&mut func, 4, vec![inst(X86Opcode::Ret, vec![])], vec![]);
    func
}

fn calls_in(func: &X86ISelFunction, b: u32) -> usize {
    func.blocks[&Block(b)]
        .insts
        .iter()
        .filter(|i| i.opcode == X86Opcode::Call)
        .count()
}

/// The direct-compare counted loop the unroller fully unrolls (trip 4):
/// pre(0){v0 = 0; v1 = 0; jmp 1} -> hdr(1){cmp v0, 4; jae 3; jmp 2} ->
/// latch(2){v1 += 5; guard v0; v0 += 1; jmp 1}; exit(3){v1 += 0; ret}. The
/// IV-indexed guard clears the pass's profitability gate.
fn unrollable_loop() -> X86ISelFunction {
    let mut func = function("unroll", 4, vec![]);
    fill(
        &mut func,
        0,
        vec![
            inst(X86Opcode::MovRI, vec![vr(0), imm(0)]),
            inst(X86Opcode::MovRI, vec![vr(1), imm(0)]),
            jmp(1),
        ],
        vec![1],
    );
    fill(
        &mut func,
        1,
        vec![
            inst(X86Opcode::CmpRI, vec![vr(0), imm(4)]),
            jcc(X86CondCode::AE, 3),
            jmp(2),
        ],
        vec![3, 2],
    );
    fill(
        &mut func,
        2,
        vec![
            inst(X86Opcode::AddRI, vec![vr(1), imm(5)]),
            inst(
                X86Opcode::TrapBoundsCheckExact,
                vec![vr(20), vr(0), imm(999)],
            ),
            inst(X86Opcode::AddRI, vec![vr(0), imm(1)]),
            jmp(1),
        ],
        vec![1],
    );
    fill(
        &mut func,
        3,
        vec![
            inst(X86Opcode::AddRI, vec![vr(1), imm(0)]),
            inst(X86Opcode::Ret, vec![]),
        ],
        vec![],
    );
    func
}

#[test]
fn loop_pass_opt_outs_disable_their_pass_and_refuse_a_conflicting_reinstall() {
    // Default on: nothing installed, both passes change their input.
    for mut licm in [
        X86LoopInvariantCodeMotion::pure_only(),
        X86LoopInvariantCodeMotion::with_invariant_load_hoisting(),
    ] {
        let mut hoisted = hoistable_loop();
        assert!(licm.run(&mut hoisted), "LICM must be on by default");
        assert_eq!(
            (calls_in(&hoisted, 0), calls_in(&hoisted, 2)),
            (1, 0),
            "the call moved into the preheader"
        );
    }
    let mut unrolled = unrollable_loop();
    assert!(
        X86LoopUnroll.run(&mut unrolled),
        "the unroller must be on by default"
    );
    assert_eq!(
        unrolled.blocks[&Block(2)].successors,
        vec![Block(3)],
        "the unrolled body falls out to the exit"
    );

    // Installed opt-outs: the same inputs are left untouched.
    assert!(trust_cg_opt::x86_licm::set_licm_disabled(true));
    assert!(trust_cg_opt::x86_loop_unroll::set_loop_unroll_disabled(
        true
    ));
    for mut licm in [
        X86LoopInvariantCodeMotion::pure_only(),
        X86LoopInvariantCodeMotion::with_invariant_load_hoisting(),
    ] {
        let mut kept = hoistable_loop();
        assert!(!licm.run(&mut kept), "the opt-out must disable LICM");
        assert_eq!(
            (calls_in(&kept, 0), calls_in(&kept, 2)),
            (0, 1),
            "the call stays in its loop"
        );
        // The direct entry point ignores the knob (tests run the pass with it).
        let mut direct = hoistable_loop();
        assert!(licm.run_on_function(&mut direct));
    }
    let mut kept = unrollable_loop();
    assert!(
        !X86LoopUnroll.run(&mut kept),
        "the opt-out must disable the unroller"
    );
    assert_eq!(
        kept.blocks[&Block(2)].successors,
        vec![Block(1)],
        "the latch keeps its back edge"
    );
    assert!(X86LoopUnroll.run_on_function(&mut unrollable_loop()));

    // One policy per process: an equal reinstall is accepted, a different one refused.
    assert!(trust_cg_opt::x86_licm::set_licm_disabled(true));
    assert!(!trust_cg_opt::x86_licm::set_licm_disabled(false));
    assert!(trust_cg_opt::x86_loop_unroll::set_loop_unroll_disabled(
        true
    ));
    assert!(!trust_cg_opt::x86_loop_unroll::set_loop_unroll_disabled(
        false
    ));
}
