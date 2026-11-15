// trust-cg-codegen/tests/x86_64_opt_tied_operands.rs - x86 machine passes respect tied and written operand 0
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The production x86 pass order (`X86Pipeline::run_x86_optimization_passes`
//! at O1, O2 and O3) must respect what an instruction does with its operand 0.
//!
//! * A tied operand 0 is read AND written. x86 copy propagation rewrote the
//!   tied operand 0 of `Not [v]` as if it were a pure use, so `v := v0; NOT v`
//!   became `NOT v0` and the function returned the un-inverted copy. x86 CSE
//!   keyed the tied two-operand `AddRR [d, s]` by `s` alone, so
//!   `d1 += s; d2 += s` became `d1 += s; d2 := d1`.
//! * `StackAlloc [dst, ..]` WRITES operand 0. The shared classifier answered
//!   "no def", so x86 LICM did not see the loop redefine `dst` and hoisted a
//!   `Lea` of the fresh allocation out of the loop.
//!
//! The straight-line shapes are evaluated on concrete inputs after
//! optimization by a small interpreter below (it refuses any opcode it does
//! not model), so the checks do not depend on the def/use model under test.
//! Host-neutral: nothing here executes x86 code.

use std::collections::HashMap;

use trust_cg_codegen::x86_64::{X86Pipeline, X86PipelineConfig};
use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::x86_64_ops::{X86CondCode, X86Opcode};
use trust_cg_ir::x86_64_regs::{RAX, RDI, RDX, RSI, X86PReg};
use trust_cg_lower::function::Signature;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::types::Type;
use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst, X86ISelOperand};
use trust_cg_opt::OptLevel;

const OPT_LEVELS: [OptLevel; 3] = [OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn v(id: u32) -> X86ISelOperand {
    X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64))
}

fn p(reg: X86PReg) -> X86ISelOperand {
    X86ISelOperand::PReg(reg)
}

fn imm(value: i64) -> X86ISelOperand {
    X86ISelOperand::Imm(value)
}

fn inst(opcode: X86Opcode, operands: Vec<X86ISelOperand>) -> X86ISelInst {
    X86ISelInst::new(opcode, operands)
}

fn straight_line(name: &str, params: usize, insts: Vec<X86ISelInst>) -> X86ISelFunction {
    let mut func = X86ISelFunction::new(
        name.to_string(),
        Signature {
            params: vec![Type::I64; params],
            returns: vec![Type::I64],
        },
    );
    func.ensure_block(Block(0));
    func.next_vreg = 32;
    for inst in insts {
        func.push_inst(Block(0), inst);
    }
    func
}

fn optimize(mut func: X86ISelFunction, opt_level: OptLevel) -> X86ISelFunction {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level,
        ..X86PipelineConfig::default()
    });
    let _ = pipeline.run_x86_optimization_passes(&mut func);
    func
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Loc {
    V(u32),
    P(X86PReg),
}

fn loc(operand: &X86ISelOperand) -> Loc {
    match operand {
        X86ISelOperand::VReg(v) => Loc::V(v.id),
        X86ISelOperand::PReg(p) => Loc::P(*p),
        other => panic!("not a register operand: {other:?}"),
    }
}

/// Evaluate a single-block, 64-bit, straight-line function and return RAX at
/// its `Ret`. Panics on any opcode or form it does not model.
fn eval(func: &X86ISelFunction, args: &[(X86PReg, i64)]) -> i64 {
    assert_eq!(func.block_order.len(), 1, "straight-line only: {func:#?}");
    let insts = &func.blocks[&func.block_order[0]].insts;
    let mut regs: HashMap<Loc, i64> = args.iter().map(|(r, x)| (Loc::P(*r), *x)).collect();
    let read = |regs: &HashMap<Loc, i64>, operand: &X86ISelOperand| -> i64 {
        match operand {
            X86ISelOperand::Imm(value) => *value,
            register => *regs
                .get(&loc(register))
                .unwrap_or_else(|| panic!("read of unwritten {register:?}: {insts:#?}")),
        }
    };
    for inst in insts {
        use X86Opcode::*;
        let ops = inst.operands.as_slice();
        // (destination, value) for the value-producing forms.
        let write = match (inst.opcode, ops) {
            (MovRR | MovRI, [d, s]) => Some((d, read(&regs, s))),
            (Not, [d]) => Some((d, !read(&regs, d))),
            (Not, [d, s]) => Some((d, !read(&regs, s))),
            (Neg, [d]) => Some((d, read(&regs, d).wrapping_neg())),
            (Neg, [d, s]) => Some((d, read(&regs, s).wrapping_neg())),
            (Inc, [d]) => Some((d, read(&regs, d).wrapping_add(1))),
            (Dec, [d]) => Some((d, read(&regs, d).wrapping_sub(1))),
            (AddRR | AddRI, [d, s]) => Some((d, read(&regs, d).wrapping_add(read(&regs, s)))),
            (AddRR | AddRI, [d, a, b]) => Some((d, read(&regs, a).wrapping_add(read(&regs, b)))),
            (SubRR | SubRI, [d, s]) => Some((d, read(&regs, d).wrapping_sub(read(&regs, s)))),
            (SubRR | SubRI, [d, a, b]) => Some((d, read(&regs, a).wrapping_sub(read(&regs, b)))),
            (XorRR | XorRI, [d, s]) => Some((d, read(&regs, d) ^ read(&regs, s))),
            (XorRR | XorRI, [d, a, b]) => Some((d, read(&regs, a) ^ read(&regs, b))),
            (Lea, [d, X86ISelOperand::MemAddr { base, disp }]) => {
                Some((d, read(&regs, base.as_ref()).wrapping_add(i64::from(*disp))))
            }
            (
                LeaSib,
                [
                    d,
                    X86ISelOperand::SibMemAddr {
                        base,
                        index,
                        scale,
                        disp,
                    },
                ],
            ) => Some((
                d,
                read(&regs, base.as_ref())
                    .wrapping_add(read(&regs, index.as_ref()).wrapping_mul(i64::from(*scale)))
                    .wrapping_add(i64::from(*disp)),
            )),
            (CmpRR | CmpRI | TestRR | TestRI | Nop, _) => None,
            (Ret, _) => return read(&regs, &p(RAX)),
            _ => panic!("the evaluator does not model {inst:?}: {insts:#?}"),
        };
        if let Some((d, value)) = write {
            regs.insert(loc(d), value);
        }
    }
    panic!("no Ret: {insts:#?}")
}

/// `f(x) = !x`, written as `v1 := x; NOT v1; return v1` — the tied
/// one-operand `NOT` the x86 peephole produces from `XOR v, -1`.
#[test]
fn a_tied_not_after_a_copy_still_inverts_the_copy() {
    let func = || {
        straight_line(
            "not_after_copy",
            1,
            vec![
                inst(X86Opcode::MovRR, vec![v(0), p(RDI)]),
                inst(X86Opcode::MovRR, vec![v(1), v(0)]),
                inst(X86Opcode::Not, vec![v(1)]),
                inst(X86Opcode::MovRR, vec![p(RAX), v(1)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        )
    };
    for x in [0i64, 5, -1, 0x1234_5678] {
        assert_eq!(eval(&func(), &[(RDI, x)]), !x, "unoptimized fixture");
        for opt_level in OPT_LEVELS {
            let optimized = optimize(func(), opt_level);
            assert_eq!(
                eval(&optimized, &[(RDI, x)]),
                !x,
                "f({x}) at {opt_level:?}: {optimized:#?}"
            );
        }
    }
}

/// `f(x, y, z) = (x + z) - (y + z)` with both adds in the tied two-operand
/// form `AddRR [d, z]`.
#[test]
fn tied_adds_into_different_destinations_stay_distinct() {
    let func = || {
        straight_line(
            "tied_adds",
            3,
            vec![
                inst(X86Opcode::MovRR, vec![v(1), p(RDI)]),
                inst(X86Opcode::MovRR, vec![v(2), p(RSI)]),
                inst(X86Opcode::MovRR, vec![v(3), p(RDX)]),
                inst(X86Opcode::AddRR, vec![v(1), v(3)]),
                inst(X86Opcode::AddRR, vec![v(2), v(3)]),
                inst(X86Opcode::SubRR, vec![v(4), v(1), v(2)]),
                inst(X86Opcode::MovRR, vec![p(RAX), v(4)]),
                inst(X86Opcode::Ret, vec![]),
            ],
        )
    };
    for (x, y, z) in [(10i64, 20, 3), (7, 7, 1), (-4, 9, 100)] {
        let args = [(RDI, x), (RSI, y), (RDX, z)];
        assert_eq!(eval(&func(), &args), x - y, "unoptimized fixture");
        for opt_level in OPT_LEVELS {
            let optimized = optimize(func(), opt_level);
            assert_eq!(
                eval(&optimized, &args),
                x - y,
                "f({x}, {y}, {z}) at {opt_level:?}: {optimized:#?}"
            );
        }
    }
}

/// A loop that takes a fresh runtime stack allocation every iteration and
/// forms an address into it:
///
/// ```text
///   bb0: v5 := 0; v7 := 7; v9 := n; jmp bb1
///   bb1: v5 := StackAlloc(v9, 8, 16); v6 := lea [v5 + 8]; [v6] := v7;
///        cmp v9, 0; jne bb1
///   bb2: rax := 0; ret
/// ```
///
/// The `Lea` reads the allocation of the current iteration, so it must stay
/// in the loop after the `StackAlloc`.
#[test]
fn a_lea_of_a_per_iteration_stack_allocation_stays_in_the_loop() {
    let mem = |base: u32, disp: i32| X86ISelOperand::MemAddr {
        base: Box::new(v(base)),
        disp,
    };
    for opt_level in OPT_LEVELS {
        let mut func = X86ISelFunction::new(
            "alloc_in_loop".to_string(),
            Signature {
                params: vec![Type::I64],
                returns: vec![Type::I64],
            },
        );
        let (entry, body, exit) = (Block(0), Block(1), Block(2));
        for block in [entry, body, exit] {
            func.ensure_block(block);
        }
        func.next_vreg = 32;
        func.blocks.get_mut(&entry).unwrap().successors = vec![body];
        func.blocks.get_mut(&body).unwrap().successors = vec![body, exit];
        for inst in [
            inst(X86Opcode::MovRR, vec![v(9), p(RDI)]),
            inst(X86Opcode::MovRI, vec![v(5), imm(0)]),
            inst(X86Opcode::MovRI, vec![v(7), imm(7)]),
            inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(body)]),
        ] {
            func.push_inst(entry, inst);
        }
        for inst in [
            inst(X86Opcode::StackAlloc, vec![v(5), v(9), imm(8), imm(16)]),
            inst(X86Opcode::Lea, vec![v(6), mem(5, 8)]),
            inst(X86Opcode::MovMR, vec![mem(6, 0), v(7)]),
            inst(X86Opcode::CmpRI, vec![v(9), imm(0)]),
            inst(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(body),
                ],
            ),
            inst(X86Opcode::Jmp, vec![X86ISelOperand::Block(exit)]),
        ] {
            func.push_inst(body, inst);
        }
        for inst in [
            inst(X86Opcode::MovRI, vec![v(10), imm(0)]),
            inst(X86Opcode::MovRR, vec![p(RAX), v(10)]),
            inst(X86Opcode::Ret, vec![]),
        ] {
            func.push_inst(exit, inst);
        }

        let optimized = optimize(func, opt_level);

        // Every `Lea` whose base is a StackAlloc destination must follow that
        // StackAlloc in the same block.
        let mut checked = 0;
        for block in &optimized.block_order {
            let insts = &optimized.blocks[block].insts;
            for (at, lea) in insts.iter().enumerate() {
                let (X86Opcode::Lea, [_, X86ISelOperand::MemAddr { base, .. }]) =
                    (lea.opcode, lea.operands.as_slice())
                else {
                    continue;
                };
                let allocated_here = |i: &X86ISelInst| {
                    i.opcode == X86Opcode::StackAlloc && i.operands.first() == Some(base.as_ref())
                };
                if optimized
                    .blocks
                    .values()
                    .flat_map(|b| b.insts.iter())
                    .any(allocated_here)
                {
                    checked += 1;
                    assert!(
                        insts[..at].iter().any(allocated_here),
                        "at {opt_level:?} the Lea of {base:?} in {block:?} no longer follows its \
                         StackAlloc: {optimized:#?}"
                    );
                }
            }
        }
        assert_eq!(checked, 1, "at {opt_level:?}: {optimized:#?}");
    }
}
