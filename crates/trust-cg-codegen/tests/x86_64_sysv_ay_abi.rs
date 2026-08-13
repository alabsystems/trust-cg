// trust-cg-codegen/tests/x86_64_sysv_ay_abi.rs
//
// Focused x86-64 SysV ABI canaries for ay-shaped helper signatures.

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_ir::x86_64_regs::{
    EAX, ECX, EDI, EDX, ESI, R8D, R9D, RSP, X86PReg, XMM0, XMM1, XMM2, XMM3,
};
use trust_cg_lower::function::{BasicBlock, Function as LirFunction, Signature};
use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
use trust_cg_lower::types::Type;
use trust_cg_lower::x86_64_isel::{
    X86CallAbi, X86ISelFunction, X86ISelInst, X86ISelOperand, X86InstructionSelector,
};
use trust_ir::{CastOp, FuncId, Ty};
use trust_ir_build::ModuleBuilder;

fn i32_const(value: u32, imm: i64) -> Instruction {
    Instruction {
        opcode: Opcode::Iconst { ty: Type::I32, imm },
        args: vec![],
        results: vec![Value(value)],
    }
}

fn f64_const(value: u32, imm: f64) -> Instruction {
    Instruction {
        opcode: Opcode::Fconst { ty: Type::F64, imm },
        args: vec![],
        results: vec![Value(value)],
    }
}

fn call_i32(name: &str, args: Vec<Value>, result: u32) -> Instruction {
    Instruction {
        opcode: Opcode::Call {
            name: name.to_owned(),
        },
        args,
        results: vec![Value(result)],
    }
}

fn ret(values: Vec<Value>) -> Instruction {
    Instruction {
        opcode: Opcode::Return,
        args: values,
        results: vec![],
    }
}

fn lir_function(name: &str, returns: Vec<Type>, instructions: Vec<Instruction>) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![],
            returns,
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions,
            source_locs: vec![],
        },
    );
    func
}

fn select_sysv_lir(func: &LirFunction, type_hints: &[(Value, Type)]) -> X86ISelFunction {
    let mut selector = X86InstructionSelector::with_abi(
        func.name.clone(),
        func.signature.clone(),
        X86CallAbi::SystemV,
    );
    selector.seed_value_types(&type_hints.iter().cloned().collect());
    selector.seed_function_value_use_counts(func);
    selector
        .lower_formal_arguments(&func.signature, func.entry_block)
        .expect("x86 SysV formal argument lowering should succeed");
    let block = &func.blocks[&func.entry_block];
    selector
        .select_block(func.entry_block, &block.instructions)
        .expect("x86 SysV call canary should select");
    selector.finalize()
}

fn entry_insts(func: &X86ISelFunction) -> &[X86ISelInst] {
    &func.blocks[&Block(0)].insts
}

fn call_index(insts: &[X86ISelInst]) -> usize {
    insts
        .iter()
        .position(|inst| inst.opcode == X86Opcode::Call)
        .expect("selected function should contain a direct call")
}

fn preg_dest_sequence(insts: &[X86ISelInst], opcode: X86Opcode) -> Vec<X86PReg> {
    insts
        .iter()
        .filter(|inst| inst.opcode == opcode)
        .filter_map(|inst| match inst.operands.first() {
            Some(X86ISelOperand::PReg(reg)) => Some(*reg),
            _ => None,
        })
        .collect()
}

fn stack_store_disps(insts: &[X86ISelInst], opcode: X86Opcode) -> Vec<i32> {
    insts
        .iter()
        .filter(|inst| inst.opcode == opcode)
        .filter_map(|inst| match inst.operands.first() {
            Some(X86ISelOperand::MemAddr { base, disp })
                if matches!(base.as_ref(), X86ISelOperand::PReg(reg) if *reg == RSP) =>
            {
                Some(*disp)
            }
            _ => None,
        })
        .collect()
}

fn has_rsp_adjust(insts: &[X86ISelInst], opcode: X86Opcode, imm: i64) -> bool {
    insts.iter().any(|inst| {
        inst.opcode == opcode
            && inst.operands == vec![X86ISelOperand::PReg(RSP), X86ISelOperand::Imm(imm)]
    })
}

#[test]
fn sysv_six_i32_call_uses_register_args_and_eax_return() {
    let mut instructions = Vec::new();
    for idx in 0..6 {
        instructions.push(i32_const(idx, (idx as i64 + 1) * 11));
    }
    instructions.push(call_i32(
        "ay_six_i32_helper",
        (0..6).map(Value).collect(),
        6,
    ));
    instructions.push(ret(vec![Value(6)]));

    let func = lir_function("ay_six_i32_caller", vec![Type::I32], instructions);
    let selected = select_sysv_lir(&func, &[(Value(6), Type::I32)]);
    let insts = entry_insts(&selected);
    let call = call_index(insts);
    let before_call = &insts[..call];
    let after_call = &insts[call + 1..];

    assert_eq!(
        preg_dest_sequence(before_call, X86Opcode::MovRR32),
        vec![EDI, ESI, EDX, ECX, R8D, R9D],
        "six i32 SysV args must stay in the integer register sequence"
    );
    assert!(
        !has_rsp_adjust(before_call, X86Opcode::SubRI, 16),
        "six register-only i32 args must not allocate an outgoing stack area"
    );
    assert!(
        stack_store_disps(before_call, X86Opcode::MovMR32).is_empty(),
        "six register-only i32 args must not spill outgoing stack args"
    );
    assert!(
        after_call.iter().any(|inst| {
            inst.opcode == X86Opcode::MovRR32
                && matches!(inst.operands.get(1), Some(X86ISelOperand::PReg(reg)) if *reg == EAX)
        }),
        "i32 call result must be read from EAX"
    );
}

#[test]
fn sysv_seven_and_eight_i32_calls_preserve_stack_order_and_alignment() {
    for (arity, expected_disps) in [(7, vec![0]), (8, vec![0, 8])] {
        let mut instructions = Vec::new();
        for idx in 0..arity {
            instructions.push(i32_const(idx, idx as i64 + 1));
        }
        let result = arity;
        instructions.push(call_i32(
            &format!("ay_{arity}_i32_helper"),
            (0..arity).map(Value).collect(),
            result,
        ));
        instructions.push(ret(vec![Value(result)]));

        let func = lir_function(
            &format!("ay_{arity}_i32_caller"),
            vec![Type::I32],
            instructions,
        );
        let selected = select_sysv_lir(&func, &[(Value(result), Type::I32)]);
        let insts = entry_insts(&selected);
        let call = call_index(insts);
        let before_call = &insts[..call];
        let after_call = &insts[call + 1..];

        assert!(
            has_rsp_adjust(before_call, X86Opcode::SubRI, 16),
            "{arity} i32 args should reserve a 16-byte-aligned outgoing stack area"
        );
        assert_eq!(
            stack_store_disps(before_call, X86Opcode::MovMR32),
            expected_disps,
            "{arity} i32 args should store stack overflow args left-to-right"
        );
        assert!(
            has_rsp_adjust(after_call, X86Opcode::AddRI, 16),
            "{arity} i32 args should restore the aligned outgoing stack area after CALL"
        );
        assert_eq!(
            preg_dest_sequence(before_call, X86Opcode::MovRR32),
            vec![EDI, ESI, EDX, ECX, R8D, R9D],
            "{arity} i32 args should keep the first six args in SysV GPRs"
        );
    }
}

#[test]
fn sysv_mixed_i32_f64_call_uses_independent_gpr_and_xmm_sequences() {
    let instructions = vec![
        i32_const(0, 1),
        f64_const(1, 2.0),
        i32_const(2, 3),
        f64_const(3, 4.0),
        i32_const(4, 5),
        f64_const(5, 6.0),
        i32_const(6, 7),
        f64_const(7, 8.0),
        call_i32("ay_mixed_i32_f64_helper", (0..8).map(Value).collect(), 8),
        ret(vec![Value(8)]),
    ];

    let func = lir_function("ay_mixed_i32_f64_caller", vec![Type::I32], instructions);
    let selected = select_sysv_lir(&func, &[(Value(8), Type::I32)]);
    let insts = entry_insts(&selected);
    let call = call_index(insts);
    let before_call = &insts[..call];

    assert_eq!(
        preg_dest_sequence(before_call, X86Opcode::MovRR32),
        vec![EDI, ESI, EDX, ECX],
        "interleaved i32 args must consume only the SysV GPR sequence"
    );
    assert_eq!(
        preg_dest_sequence(before_call, X86Opcode::MovsdRR),
        vec![XMM0, XMM1, XMM2, XMM3],
        "interleaved f64 args must consume only the SysV XMM sequence"
    );
    assert!(
        !has_rsp_adjust(before_call, X86Opcode::SubRI, 16),
        "four i32 plus four f64 SysV args should fit in independent register banks"
    );
}

fn host_jit_o0_compiler() -> Compiler {
    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = OptLevel::O0;
    Compiler::new(config)
}

fn weighted_i32_sum(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    args: &[trust_ir::ValueId],
) -> trust_ir::ValueId {
    let mut acc = fb.iconst(Ty::I32, 0);
    for (idx, arg) in args.iter().enumerate() {
        let weight = fb.iconst(Ty::I32, idx as i128 + 1);
        let weighted = fb.mul(Ty::I32, *arg, weight);
        acc = fb.add(Ty::I32, acc, weighted);
    }
    acc
}

fn add_i32_direct_and_call_pair(
    mb: &mut ModuleBuilder,
    direct_id: FuncId,
    direct_name: &str,
    call_name: &str,
    arity: usize,
) {
    let ty = mb.add_func_type(vec![Ty::I32; arity], vec![Ty::I32]);

    {
        let mut fb = mb.function(direct_name, ty);
        let entry = fb.create_block();
        let args: Vec<_> = (0..arity)
            .map(|_| fb.add_block_param(entry, Ty::I32))
            .collect();
        fb.switch_to_block(entry);
        let result = weighted_i32_sum(&mut fb, &args);
        fb.ret(vec![result]);
        fb.build();
    }

    {
        let mut fb = mb.function(call_name, ty);
        let entry = fb.create_block();
        let args: Vec<_> = (0..arity)
            .map(|_| fb.add_block_param(entry, Ty::I32))
            .collect();
        fb.switch_to_block(entry);
        let called = fb.call(direct_id, args);
        let bias = fb.iconst(Ty::I32, 17);
        let result = fb.add(Ty::I32, called, bias);
        fb.ret(vec![result]);
        fb.build();
    }
}

fn build_ay_sysv_host_jit_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_sysv_ay_abi");

    add_i32_direct_and_call_pair(
        &mut mb,
        FuncId::new(0),
        "ay_sysv_six_i32_direct",
        "ay_sysv_six_i32_call",
        6,
    );
    add_i32_direct_and_call_pair(
        &mut mb,
        FuncId::new(2),
        "ay_sysv_eight_i32_direct",
        "ay_sysv_eight_i32_call",
        8,
    );

    let mixed_ty = mb.add_func_type(
        vec![
            Ty::I32,
            Ty::F64,
            Ty::I32,
            Ty::F64,
            Ty::I32,
            Ty::F64,
            Ty::I32,
            Ty::F64,
        ],
        vec![Ty::F64],
    );
    let mixed_direct_id = FuncId::new(4);

    {
        let mut fb = mb.function("ay_sysv_mixed_i32_f64_direct", mixed_ty);
        let entry = fb.create_block();
        let i0 = fb.add_block_param(entry, Ty::I32);
        let f0 = fb.add_block_param(entry, Ty::F64);
        let i1 = fb.add_block_param(entry, Ty::I32);
        let f1 = fb.add_block_param(entry, Ty::F64);
        let i2 = fb.add_block_param(entry, Ty::I32);
        let f2 = fb.add_block_param(entry, Ty::F64);
        let i3 = fb.add_block_param(entry, Ty::I32);
        let f3 = fb.add_block_param(entry, Ty::F64);
        fb.switch_to_block(entry);

        let ints = [i0, i1, i2, i3].map(|arg| fb.cast(CastOp::SIToFP, Ty::I32, Ty::F64, arg));
        let w10 = fb.fconst(Ty::F64, 10.0);
        let w100 = fb.fconst(Ty::F64, 100.0);
        let w1000 = fb.fconst(Ty::F64, 1000.0);
        let w10_000 = fb.fconst(Ty::F64, 10_000.0);
        let w100_000 = fb.fconst(Ty::F64, 100_000.0);
        let w1_000_000 = fb.fconst(Ty::F64, 1_000_000.0);
        let w10_000_000 = fb.fconst(Ty::F64, 10_000_000.0);
        let terms = [
            ints[0],
            fb.fmul(Ty::F64, f0, w10),
            fb.fmul(Ty::F64, ints[1], w100),
            fb.fmul(Ty::F64, f1, w1000),
            fb.fmul(Ty::F64, ints[2], w10_000),
            fb.fmul(Ty::F64, f2, w100_000),
            fb.fmul(Ty::F64, ints[3], w1_000_000),
            fb.fmul(Ty::F64, f3, w10_000_000),
        ];
        let mut acc = fb.fconst(Ty::F64, 0.0);
        for term in terms {
            acc = fb.fadd(Ty::F64, acc, term);
        }
        fb.ret(vec![acc]);
        fb.build();
    }

    {
        let mut fb = mb.function("ay_sysv_mixed_i32_f64_call", mixed_ty);
        let entry = fb.create_block();
        let args: Vec<_> = (0..8)
            .map(|idx| fb.add_block_param(entry, if idx % 2 == 0 { Ty::I32 } else { Ty::F64 }))
            .collect();
        fb.switch_to_block(entry);
        let called = fb.call(mixed_direct_id, args);
        let half = fb.fconst(Ty::F64, 0.5);
        let result = fb.fadd(Ty::F64, called, half);
        fb.ret(vec![result]);
        fb.build();
    }

    mb.build()
}

#[test]
fn x86_64_sysv_host_jit_executes_ay_abi_canaries() {
    if !cfg!(all(target_arch = "x86_64", unix)) {
        eprintln!(
            "skipping x86_64_sysv_host_jit_executes_ay_abi_canaries: requires x86_64 Unix host"
        );
        return;
    }

    let module = build_ay_sysv_host_jit_module();
    let result = host_jit_o0_compiler()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("x86-64 SysV host JIT should compile ay ABI canaries");

    let six_direct: extern "C" fn(i32, i32, i32, i32, i32, i32) -> i32 = unsafe {
        result
            .buffer
            .get_fn_bound("ay_sysv_six_i32_direct")
            .expect("ay_sysv_six_i32_direct symbol")
            .into_inner()
    };
    let six_call: extern "C" fn(i32, i32, i32, i32, i32, i32) -> i32 = unsafe {
        result
            .buffer
            .get_fn_bound("ay_sysv_six_i32_call")
            .expect("ay_sysv_six_i32_call symbol")
            .into_inner()
    };
    let eight_direct: extern "C" fn(i32, i32, i32, i32, i32, i32, i32, i32) -> i32 = unsafe {
        result
            .buffer
            .get_fn_bound("ay_sysv_eight_i32_direct")
            .expect("ay_sysv_eight_i32_direct symbol")
            .into_inner()
    };
    let eight_call: extern "C" fn(i32, i32, i32, i32, i32, i32, i32, i32) -> i32 = unsafe {
        result
            .buffer
            .get_fn_bound("ay_sysv_eight_i32_call")
            .expect("ay_sysv_eight_i32_call symbol")
            .into_inner()
    };
    let mixed_direct: extern "C" fn(i32, f64, i32, f64, i32, f64, i32, f64) -> f64 = unsafe {
        result
            .buffer
            .get_fn_bound("ay_sysv_mixed_i32_f64_direct")
            .expect("ay_sysv_mixed_i32_f64_direct symbol")
            .into_inner()
    };
    let mixed_call: extern "C" fn(i32, f64, i32, f64, i32, f64, i32, f64) -> f64 = unsafe {
        result
            .buffer
            .get_fn_bound("ay_sysv_mixed_i32_f64_call")
            .expect("ay_sysv_mixed_i32_f64_call symbol")
            .into_inner()
    };

    assert_eq!(six_direct(1, 2, 3, 4, 5, 6), 91);
    assert_eq!(six_call(1, 2, 3, 4, 5, 6), 108);
    assert_eq!(six_direct(-1, 2, -3, 4, -5, 6), 21);
    assert_eq!(six_call(-1, 2, -3, 4, -5, 6), 38);

    assert_eq!(eight_direct(1, 2, 3, 4, 5, 6, 7, 8), 204);
    assert_eq!(eight_call(1, 2, 3, 4, 5, 6, 7, 8), 221);
    assert_eq!(eight_direct(-1, 2, -3, 4, -5, 6, -7, 8), 36);
    assert_eq!(eight_call(-1, 2, -3, 4, -5, 6, -7, 8), 53);

    assert_eq!(mixed_direct(1, 2.0, 3, 4.0, 5, 6.0, 7, 8.0), 87_654_321.0);
    assert_eq!(mixed_call(1, 2.0, 3, 4.0, 5, 6.0, 7, 8.0), 87_654_321.5);
}
