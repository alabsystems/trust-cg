// fuzz/fuzz_targets/fuzz_compile_x86_64.rs
//
// libFuzzer target shadowing panic_fuzz_compile_x86_64.rs. Builds small
// x86-64 ISel functions directly and compiles them through X86Pipeline.

#![no_main]

use libfuzzer_sys::fuzz_target;

use trust_cg_codegen::x86_64::{X86OutputFormat, X86Pipeline, X86PipelineConfig};
use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_ir::x86_64_regs;
use trust_cg_lower::function::Signature;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::types::Type;
use trust_cg_lower::x86_64_isel::{
    X86ISelConstPoolEntry, X86ISelFunction, X86ISelInst, X86ISelOperand,
};
use trust_cg_opt::OptLevel;

fn pick_opt_level(byte: u8) -> OptLevel {
    match byte % 4 {
        0 => OptLevel::O0,
        1 => OptLevel::O1,
        2 => OptLevel::O2,
        _ => OptLevel::O3,
    }
}

fn pick_int_opcode(byte: u8) -> X86Opcode {
    match byte % 5 {
        0 => X86Opcode::AddRR,
        1 => X86Opcode::SubRR,
        2 => X86Opcode::XorRR,
        3 => X86Opcode::AndRR,
        _ => X86Opcode::OrRR,
    }
}

fn minimal_func(name: &str, returns: Vec<Type>) -> X86ISelFunction {
    let sig = Signature {
        params: vec![],
        returns,
    };
    let mut func = X86ISelFunction::new(name.to_string(), sig);
    func.ensure_block(Block(0));
    func
}

fn push_vreg_imm(func: &mut X86ISelFunction, next_vreg: &mut u32, value: i64) -> VReg {
    let vreg = VReg::new(*next_vreg, RegClass::Gpr64);
    *next_vreg += 1;
    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![X86ISelOperand::VReg(vreg), X86ISelOperand::Imm(value)],
        ),
    );
    vreg
}

fn build_int_chain(data: &[u8]) -> X86ISelFunction {
    let mut func = minimal_func("fuzz_x86_int_chain", vec![Type::I64]);
    let mut next_vreg = 0;
    let mut acc = push_vreg_imm(&mut func, &mut next_vreg, 0);

    for (idx, byte) in data.iter().copied().take(16).enumerate() {
        let rhs = push_vreg_imm(&mut func, &mut next_vreg, i64::from(byte) - 128);
        let dst = VReg::new(next_vreg, RegClass::Gpr64);
        next_vreg += 1;
        func.push_inst(
            Block(0),
            X86ISelInst::new(
                pick_int_opcode(byte.wrapping_add(idx as u8)),
                vec![
                    X86ISelOperand::VReg(dst),
                    X86ISelOperand::VReg(acc),
                    X86ISelOperand::VReg(rhs),
                ],
            ),
        );
        acc = dst;
    }

    func.next_vreg = next_vreg;
    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![
                X86ISelOperand::PReg(x86_64_regs::RAX),
                X86ISelOperand::VReg(acc),
            ],
        ),
    );
    func.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));
    func
}

fn build_spill_pressure(data: &[u8]) -> X86ISelFunction {
    let live_values = data.first().map_or(20, |b| u32::from((b % 32).max(1)));
    let mut func = minimal_func("fuzz_x86_spill_pressure", vec![Type::I64]);

    for id in 0..live_values {
        func.push_inst(
            Block(0),
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![
                    X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64)),
                    X86ISelOperand::Imm(i64::from(id) * 19 - 83),
                ],
            ),
        );
    }
    for id in 1..live_values {
        func.push_inst(
            Block(0),
            X86ISelInst::new(
                X86Opcode::AddRR,
                vec![
                    X86ISelOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                    X86ISelOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                    X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64)),
                ],
            ),
        );
    }

    func.next_vreg = live_values;
    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![
                X86ISelOperand::PReg(x86_64_regs::RAX),
                X86ISelOperand::VReg(VReg::new(0, RegClass::Gpr64)),
            ],
        ),
    );
    func.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));
    func
}

fn build_fp_const_pool(data: &[u8]) -> X86ISelFunction {
    let mut func = minimal_func("fuzz_x86_fp_const_pool", vec![Type::F64]);
    let mut padded = [0u8; 12];
    for (idx, byte) in data.iter().copied().take(padded.len()).enumerate() {
        padded[idx] = byte;
    }

    func.const_pool_entries.push(X86ISelConstPoolEntry {
        data: padded[0..4].to_vec(),
        align: 4,
    });
    if data.first().is_some_and(|b| b & 1 != 0) {
        func.const_pool_entries.push(X86ISelConstPoolEntry {
            data: padded[0..4].to_vec(),
            align: 4,
        });
    }
    let f64_index = func.const_pool_entries.len();
    func.const_pool_entries.push(X86ISelConstPoolEntry {
        data: padded[4..12].to_vec(),
        align: 8,
    });

    let f32_tmp = VReg::new(0, RegClass::Fpr32);
    let f64_ret = VReg::new(1, RegClass::Fpr64);
    func.next_vreg = 2;
    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::MovssRipRel,
            vec![
                X86ISelOperand::VReg(f32_tmp),
                X86ISelOperand::ConstPoolEntry(0),
            ],
        ),
    );
    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::MovsdRipRel,
            vec![
                X86ISelOperand::VReg(f64_ret),
                X86ISelOperand::ConstPoolEntry(f64_index),
            ],
        ),
    );
    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::MovsdRR,
            vec![
                X86ISelOperand::PReg(x86_64_regs::XMM0),
                X86ISelOperand::VReg(f64_ret),
            ],
        ),
    );
    func.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));
    func
}

fuzz_target!(|data: &[u8]| {
    if data.len() < 2 {
        return;
    }

    let func = match data[0] % 3 {
        0 => build_int_chain(&data[2..]),
        1 => build_spill_pressure(&data[2..]),
        _ => build_fp_const_pool(&data[2..]),
    };
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: pick_opt_level(data[1]),
        output_format: X86OutputFormat::RawBytes,
        emit_frame: true,
        ..X86PipelineConfig::default()
    });
    let _ = pipeline.compile_function(&func);
});
