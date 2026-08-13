// trust-cg-codegen integration test: MOVZ/MOVK emitted by neon-bytesum
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_ir::aarch64_regs::{W0, X0};
use trust_cg_ir::{
    AArch64Opcode, BlockId, MachFunction, MachInst, MachOperand, RegClass, Signature, VReg,
};
use trust_cg_opt::neon_bytesum::NeonBytesumPass;
use trust_cg_opt::pass_manager::MachinePass;

fn x(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}

fn w(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}

fn imm(value: i64) -> MachOperand {
    MachOperand::Imm(value)
}

fn block(block: BlockId) -> MachOperand {
    MachOperand::Block(block)
}

/// Build the scalar `u64 += u8` reduction shape consumed by neon-bytesum.
fn bytesum_loop(n: i64) -> MachFunction {
    let mut func = MachFunction::new(
        "movz_movk_bytesum".to_string(),
        Signature::new(vec![], vec![]),
    );
    let preheader = func.entry;
    let header = func.create_block();
    let guard = func.create_block();
    let latch = func.create_block();
    let exit = func.create_block();

    let push = |func: &mut MachFunction, block_id: BlockId, opcode, operands| {
        let id = func.push_inst(MachInst::new(opcode, operands));
        func.append_inst(block_id, id);
    };
    use AArch64Opcode::*;

    push(&mut func, preheader, Copy, vec![x(0), x(0)]);
    push(&mut func, preheader, Movz, vec![x(4), imm(n & 0xFFFF)]);
    if n > 0xFFFF {
        push(
            &mut func,
            preheader,
            Movk,
            vec![x(4), imm((n >> 16) & 0xFFFF), imm(16)],
        );
    }
    push(&mut func, preheader, Movz, vec![x(47), imm(0)]);
    push(&mut func, preheader, Movz, vec![x(49), imm(0)]);
    push(&mut func, preheader, B, vec![block(header)]);

    push(&mut func, header, MovR, vec![x(50), x(47)]);
    push(&mut func, header, CmpRR, vec![x(50), x(4)]);
    push(&mut func, header, BCond, vec![imm(3), block(guard)]); // CC_LO
    push(&mut func, header, B, vec![block(exit)]);

    push(&mut func, guard, MovR, vec![x(53), x(47)]);
    push(
        &mut func,
        guard,
        TrapBoundsCheckExact,
        vec![x(53), x(53), imm(n)],
    );
    push(&mut func, guard, B, vec![block(latch)]);

    push(&mut func, latch, LdrbRO, vec![x(63), x(0), x(53), imm(0)]);
    push(&mut func, latch, Uxtw, vec![x(85), w(63)]);
    push(&mut func, latch, AddRR, vec![x(86), x(49), x(85)]);
    push(&mut func, latch, Movz, vec![x(88), imm(1)]);
    push(&mut func, latch, AddRR, vec![x(89), x(47), x(88)]);
    push(&mut func, latch, MovR, vec![x(49), x(86)]);
    push(&mut func, latch, MovR, vec![x(47), x(89)]);
    push(&mut func, latch, B, vec![block(header)]);

    push(&mut func, exit, B, vec![block(exit)]);

    func.add_edge(preheader, header);
    func.add_edge(header, guard);
    func.add_edge(header, exit);
    func.add_edge(guard, latch);
    func.add_edge(latch, header);
    func
}

#[test]
fn neon_bytesum_hw0_movz_movk_chain_reaches_real_encoder() {
    // ByteSum unroll width is 128, so N-(width-1) is exactly 65_536. The
    // Canonical optimizer materialization is an hw0 MOVZ seed followed by a
    // MOVK halfword repair: MOVZ #0; MOVK #1, LSL #16.
    let mut func = bytesum_loop(65_536 + 127);
    let mut pass = NeonBytesumPass::new();
    assert!(pass.run(&mut func));
    assert_eq!(pass.fired(), 1);

    let mut saw_bound_chain = false;
    let mut encoded_move_wides = 0usize;
    for inst in func
        .blocks
        .iter()
        .flat_map(|block| block.insts.iter().map(|&id| func.inst(id)))
        .filter(|inst| matches!(inst.opcode, AArch64Opcode::Movz | AArch64Opcode::Movk))
    {
        let mut physical = inst.clone();
        let dst = inst.operands[0]
            .as_vreg()
            .expect("optimizer fixture uses virtual GPR destinations");
        physical.operands[0] = MachOperand::PReg(match dst.class {
            RegClass::Gpr64 => X0,
            RegClass::Gpr32 => W0,
            other => panic!("unexpected move-wide destination class {other:?}"),
        });

        let word = encode_instruction(&physical)
            .unwrap_or_else(|error| panic!("optimizer emitted unencodable {physical:?}: {error}"));
        encoded_move_wides += 1;
        if physical.opcode == AArch64Opcode::Movz {
            assert_eq!((word >> 21) & 0b11, 0, "every MOVZ must encode at hw0");
        }
    }

    for block in &func.blocks {
        for pair in block.insts.windows(2) {
            let movz = func.inst(pair[0]);
            let movk = func.inst(pair[1]);
            if movz.opcode == AArch64Opcode::Movz
                && movz.operands.get(1) == Some(&MachOperand::Imm(0))
                && matches!(movz.operands.get(2), None | Some(MachOperand::Imm(0)))
                && movk.opcode == AArch64Opcode::Movk
                && movk.operands.first() == movz.operands.first()
                && movk.operands.get(1) == Some(&MachOperand::Imm(1))
                && movk.operands.get(2) == Some(&MachOperand::Imm(16))
            {
                let mut physical_movk = movk.clone();
                physical_movk.operands[0] = MachOperand::PReg(X0);
                let word = encode_instruction(&physical_movk)
                    .expect("optimizer MOVK repair must reach the real encoder");
                assert_eq!((word >> 21) & 0b11, 1, "MOVK must repair hw1");
                saw_bound_chain = true;
            }
        }
    }

    assert!(encoded_move_wides > 0);
    assert!(
        saw_bound_chain,
        "expected the optimizer's 65_536 bound to reach the real encoder as MOVZ#0 + MOVK#1"
    );
}
