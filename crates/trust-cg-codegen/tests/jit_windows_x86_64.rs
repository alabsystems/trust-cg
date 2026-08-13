// x86-64 host-JIT integration tests.

#![cfg(target_arch = "x86_64")]

use std::collections::HashMap;

#[cfg(target_os = "windows")]
use trust_cg_codegen::CompileError;
use trust_cg_codegen::Compiler;
#[cfg(target_os = "windows")]
use trust_cg_codegen::compiler::CompilerConfig;
use trust_cg_codegen::jit::ProfileHookMode;
#[cfg(target_os = "windows")]
use trust_cg_codegen::pipeline::OptLevel;
#[cfg(target_os = "windows")]
use trust_cg_codegen::target::TargetSpec;
#[cfg(target_os = "windows")]
use trust_cg_codegen::trust_ir_bitfield_builder::TrustCgBitfieldBuilderExt;
#[cfg(target_os = "windows")]
use trust_ir::{AtomicRMWOp, BinOp, FCmpOp, ICmpOp, Ordering};
use trust_ir::{CastOp, FuncId, Ty};
use trust_ir_build::ModuleBuilder;

#[cfg(target_os = "windows")]
use core::arch::{asm, global_asm};
#[cfg(target_os = "windows")]
use core::ffi::c_void;
#[cfg(target_os = "windows")]
use trust_ir::{
    Block as TrustIrBlock, BlockId, CallingConv, Constant, FuncTy, FuncTyId,
    Function as TrustIrFunction, Inst, InstrNode, Linkage, Module as TrustIrModule,
    ProofAnnotation, SwitchCase, ValueId,
};

#[cfg(target_os = "windows")]
const WIN64_STACK_PROBE_A0: i64 = 0x101;
#[cfg(target_os = "windows")]
const WIN64_STACK_PROBE_A1: i64 = 0x202;
#[cfg(target_os = "windows")]
const WIN64_STACK_PROBE_A2: i64 = 0x303;
#[cfg(target_os = "windows")]
const WIN64_STACK_PROBE_A3: i64 = 0x404;
#[cfg(target_os = "windows")]
const WIN64_STACK_PROBE_A4: i64 = 0x505;
#[cfg(target_os = "windows")]
const WIN64_STACK_PROBE_A5: i64 = 0x606;
#[cfg(target_os = "windows")]
const WIN64_STACK_PROBE_OK: i64 = 0x1f;

#[cfg(target_os = "windows")]
#[repr(C)]
#[derive(Debug, Default)]
struct Win64StackProbeObservation {
    entry_rsp: u64,
    entry_rsp_mod16: u64,
    rcx: i64,
    rdx: i64,
    r8: i64,
    r9: i64,
    stack_a4_before: i64,
    stack_a5_before: i64,
    stack_out_before: usize,
    shadow0_after_write: u64,
    shadow1_after_write: u64,
    shadow2_after_write: u64,
    shadow3_after_write: u64,
    stack_a4_after_shadow_write: i64,
    stack_a5_after_shadow_write: i64,
    stack_out_after_shadow_write: usize,
}

#[cfg(target_os = "windows")]
global_asm!(
    ".text",
    ".globl trust_cg_win64_call_dirty_rcx2",
    ".def trust_cg_win64_call_dirty_rcx2; .scl 2; .type 32; .endef",
    "trust_cg_win64_call_dirty_rcx2:",
    "mov r11, rcx",
    "mov rcx, rdx",
    "mov rdx, r8",
    "sub rsp, 40",
    "call r11",
    "add rsp, 40",
    "ret",
    ".globl trust_cg_win64_dirty_i8_return",
    ".def trust_cg_win64_dirty_i8_return; .scl 2; .type 32; .endef",
    "trust_cg_win64_dirty_i8_return:",
    "mov eax, 0x12345680",
    "ret",
    ".globl trust_cg_win64_dirty_i16_return",
    ".def trust_cg_win64_dirty_i16_return; .scl 2; .type 32; .endef",
    "trust_cg_win64_dirty_i16_return:",
    "mov eax, 0x12348000",
    "ret",
    ".globl trust_cg_win64_stack_probe_helper",
    ".def trust_cg_win64_stack_probe_helper; .scl 2; .type 32; .endef",
    "trust_cg_win64_stack_probe_helper:",
    "mov r10, qword ptr [rsp + 56]",
    "mov qword ptr [r10 + 0], rsp",
    "mov rax, rsp",
    "and rax, 15",
    "mov qword ptr [r10 + 8], rax",
    "mov qword ptr [r10 + 16], rcx",
    "mov qword ptr [r10 + 24], rdx",
    "mov qword ptr [r10 + 32], r8",
    "mov qword ptr [r10 + 40], r9",
    "mov rax, qword ptr [rsp + 40]",
    "mov qword ptr [r10 + 48], rax",
    "mov rax, qword ptr [rsp + 48]",
    "mov qword ptr [r10 + 56], rax",
    "mov rax, qword ptr [rsp + 56]",
    "mov qword ptr [r10 + 64], rax",
    "xor r11d, r11d",
    "cmp qword ptr [r10 + 8], 8",
    "jne 1f",
    "or r11d, 1",
    "1:",
    "cmp rcx, 0x101",
    "jne 2f",
    "cmp rdx, 0x202",
    "jne 2f",
    "cmp r8, 0x303",
    "jne 2f",
    "cmp r9, 0x404",
    "jne 2f",
    "or r11d, 2",
    "2:",
    "cmp qword ptr [rsp + 40], 0x505",
    "jne 3f",
    "cmp qword ptr [rsp + 48], 0x606",
    "jne 3f",
    "or r11d, 4",
    "3:",
    "cmp qword ptr [rsp + 56], r10",
    "jne 4f",
    "or r11d, 8",
    "4:",
    "movabs rax, 0x1111222233334444",
    "mov qword ptr [rsp + 8], rax",
    "mov qword ptr [r10 + 72], rax",
    "movabs rax, 0x5555666677778888",
    "mov qword ptr [rsp + 16], rax",
    "mov qword ptr [r10 + 80], rax",
    "movabs rax, 0x9999aaaabbbbcccc",
    "mov qword ptr [rsp + 24], rax",
    "mov qword ptr [r10 + 88], rax",
    "movabs rax, 0xddddeeeeffff0000",
    "mov qword ptr [rsp + 32], rax",
    "mov qword ptr [r10 + 96], rax",
    "mov rax, qword ptr [rsp + 40]",
    "mov qword ptr [r10 + 104], rax",
    "mov rax, qword ptr [rsp + 48]",
    "mov qword ptr [r10 + 112], rax",
    "mov rax, qword ptr [rsp + 56]",
    "mov qword ptr [r10 + 120], rax",
    "cmp qword ptr [rsp + 40], 0x505",
    "jne 5f",
    "cmp qword ptr [rsp + 48], 0x606",
    "jne 5f",
    "cmp qword ptr [rsp + 56], r10",
    "jne 5f",
    "or r11d, 16",
    "5:",
    "mov rax, r11",
    "ret",
);

#[cfg(target_os = "windows")]
unsafe extern "C" {
    fn trust_cg_win64_call_dirty_rcx2(target: *const c_void, lhs: i64, rhs: i64) -> i64;
    fn trust_cg_win64_dirty_i8_return() -> i8;
    fn trust_cg_win64_dirty_i16_return() -> i16;
    fn trust_cg_win64_stack_probe_helper(
        a0: i64,
        a1: i64,
        a2: i64,
        a3: i64,
        a4: i64,
        a5: i64,
        out: *mut Win64StackProbeObservation,
    ) -> i64;
}

#[cfg(target_os = "windows")]
fn windows_jit_symbol_bytes(
    buffer: &trust_cg_codegen::jit::ExecutableBuffer,
    name: &str,
) -> (Vec<u8>, u64, *const u8) {
    let ptr = buffer
        .get_fn_ptr_bound(name)
        .unwrap_or_else(|| panic!("{name} symbol"));
    let code_offset = buffer
        .code_offset_for_host_pc(ptr.as_ptr() as u64)
        .unwrap_or_else(|| panic!("{name} should belong to the JIT buffer"));
    let replay = buffer.replay_report_metadata();
    let symbol = replay
        .symbols
        .iter()
        .find(|symbol| symbol.name == name)
        .unwrap_or_else(|| panic!("replay metadata should include {name}"));
    assert_eq!(
        symbol.range.start_offset, code_offset,
        "{name} function pointer should target the symbol start"
    );
    let start = usize::try_from(symbol.range.start_offset).expect("symbol start should fit usize");
    let len = usize::try_from(symbol.range.byte_len()).expect("symbol length should fit usize");
    let code_base = unsafe {
        ptr.as_ptr()
            .sub(usize::try_from(code_offset).expect("code offset should fit usize"))
    };
    let bytes = unsafe { std::slice::from_raw_parts(code_base.add(start), len) }.to_vec();
    (bytes, symbol.range.start_offset, code_base)
}

#[cfg(target_os = "windows")]
fn decode_first_rel32_call_target(function_bytes: &[u8], function_start: u64) -> u64 {
    let call_offset = function_bytes
        .windows(5)
        .position(|window| window[0] == 0xE8)
        .expect("function should contain a direct CALL rel32");
    let disp = i32::from_le_bytes(
        function_bytes[call_offset + 1..call_offset + 5]
            .try_into()
            .expect("CALL displacement should be 4 bytes"),
    ) as i64;
    let next_pc = function_start as i64 + call_offset as i64 + 5;
    u64::try_from(next_pc + disp).expect("CALL target should be inside JIT code")
}

#[cfg(target_os = "windows")]
fn symbol_ranges_contain(
    replay: &trust_cg_codegen::jit_diagnostics::JitReplayReportMetadata,
    offset: u64,
) -> bool {
    replay
        .symbols
        .iter()
        .any(|symbol| symbol.range.contains(offset))
}

#[test]
fn x86_64_jit_calls_host_abi_entrypoints() {
    let mut mb = ModuleBuilder::new("x86_64_host_jit");

    {
        let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("add_fn", ty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I64);
        let b = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let result = fb.add(Ty::I64, a, b);
        fb.ret(vec![result]);
        fb.build();
    }

    {
        let ty = mb.add_func_type(
            vec![
                Ty::I64,
                Ty::I64,
                Ty::I64,
                Ty::I64,
                Ty::I64,
                Ty::I64,
                Ty::I64,
            ],
            vec![Ty::I64],
        );
        let mut fb = mb.function("sum7_fn", ty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I64);
        let b = fb.add_block_param(entry, Ty::I64);
        let c = fb.add_block_param(entry, Ty::I64);
        let d = fb.add_block_param(entry, Ty::I64);
        let e = fb.add_block_param(entry, Ty::I64);
        let f = fb.add_block_param(entry, Ty::I64);
        let g = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let ab = fb.add(Ty::I64, a, b);
        let abc = fb.add(Ty::I64, ab, c);
        let abcd = fb.add(Ty::I64, abc, d);
        let abcde = fb.add(Ty::I64, abcd, e);
        let abcdef = fb.add(Ty::I64, abcde, f);
        let result = fb.add(Ty::I64, abcdef, g);
        fb.ret(vec![result]);
        fb.build();
    }

    {
        let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("call_add_plus_one", ty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I64);
        let b = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let called = fb.call(FuncId::new(0), vec![a, b]);
        let one = fb.iconst(Ty::I64, 1);
        let result = fb.add(Ty::I64, called, one);
        fb.ret(vec![result]);
        fb.build();
    }

    let module = mb.build();
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("x86-64 host JIT should compile");

    assert_eq!(result.buffer.symbol_count(), 3);

    let add: extern "C" fn(i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("add_fn")
            .expect("add_fn symbol")
            .into_inner()
    };
    let sum7: extern "C" fn(i64, i64, i64, i64, i64, i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("sum7_fn")
            .expect("sum7_fn symbol")
            .into_inner()
    };
    let call_add_plus_one: extern "C" fn(i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("call_add_plus_one")
            .expect("call_add_plus_one symbol")
            .into_inner()
    };

    assert_eq!(add(3, 4), 7);
    assert_eq!(sum7(1, 2, 3, 4, 5, 6, 7), 28);
    assert_eq!(call_add_plus_one(40, 1), 42);
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_accepts_requested_windows_target_spec() {
    let mut mb = ModuleBuilder::new("x86_64_windows_requested_jit_target_spec");
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("answer", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let answer = fb.iconst(Ty::I64, 42);
    fb.ret(vec![answer]);
    fb.build();
    let module = mb.build();

    let target_spec = TargetSpec::parse("x86_64-pc-windows-msvc").unwrap();
    let compiler = Compiler::new_for_target_spec(CompilerConfig::for_host_jit(), target_spec);
    assert_eq!(compiler.target_spec(), target_spec);

    let result = compiler
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 host JIT should accept the requested Windows ABI");
    let answer_fn: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("answer")
            .expect("answer symbol")
            .into_inner()
    };
    assert_eq!(answer_fn(), 42);
}

#[cfg(target_os = "windows")]
fn add_dirty_arg_icmp_fn(mb: &mut ModuleBuilder, name: &'static str, ty: Ty, op: ICmpOp) {
    let func_ty = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![Ty::I64]);
    let mut fb = mb.function(name, func_ty);
    let entry = fb.create_block();
    let lhs = fb.add_block_param(entry, ty.clone());
    let rhs = fb.add_block_param(entry, ty.clone());
    fb.switch_to_block(entry);
    let cmp = fb.icmp(op, ty, lhs, rhs);
    let result = fb.zext(Ty::Bool, Ty::I64, cmp);
    fb.ret(vec![result]);
    fb.build();
}

#[cfg(target_os = "windows")]
fn windows_dirty_narrow_icmp_args_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("x86_64_windows_dirty_narrow_icmp_args");

    add_dirty_arg_icmp_fn(&mut mb, "dirty_b1_eq", Ty::Bool, ICmpOp::Eq);
    add_dirty_arg_icmp_fn(&mut mb, "dirty_i8_eq", Ty::I8, ICmpOp::Eq);
    add_dirty_arg_icmp_fn(&mut mb, "dirty_i8_ult", Ty::I8, ICmpOp::Ult);
    add_dirty_arg_icmp_fn(&mut mb, "dirty_i8_slt", Ty::I8, ICmpOp::Slt);
    add_dirty_arg_icmp_fn(&mut mb, "dirty_i16_eq", Ty::I16, ICmpOp::Eq);
    add_dirty_arg_icmp_fn(&mut mb, "dirty_i16_ult", Ty::I16, ICmpOp::Ult);
    add_dirty_arg_icmp_fn(&mut mb, "dirty_i16_slt", Ty::I16, ICmpOp::Slt);

    mb.build()
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_canonicalizes_dirty_narrow_icmp_args() {
    let module = windows_dirty_narrow_icmp_args_module();
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile dirty narrow comparison probes");

    let symbol = |name: &str| {
        result
            .buffer
            .get_fn_ptr_bound(name)
            .unwrap_or_else(|| panic!("{name} symbol"))
            .as_ptr() as *const c_void
    };
    let dirty = |low: u16| (0x1234_5678_9ABC_0000_u64 | u64::from(low)) as i64;
    let call = |name: &str, lhs: i64, rhs: i64| unsafe {
        trust_cg_win64_call_dirty_rcx2(symbol(name), lhs, rhs)
    };

    assert_eq!(call("dirty_b1_eq", dirty(0x0002), 0), 1);
    assert_eq!(call("dirty_b1_eq", dirty(0x0003), 1), 1);
    assert_eq!(call("dirty_i8_eq", dirty(0x00AA), 0xAA), 1);
    assert_eq!(call("dirty_i8_ult", dirty(0x0100), 1), 1);
    assert_eq!(call("dirty_i8_slt", dirty(0x0080), 0), 1);
    assert_eq!(call("dirty_i16_eq", dirty(0xBEEF), 0xBEEF), 1);
    assert_eq!(call("dirty_i16_ult", dirty(0x0000), 1), 1);
    assert_eq!(call("dirty_i16_slt", dirty(0x8000), 0), 1);
}

#[cfg(target_os = "windows")]
fn windows_dirty_narrow_extern_return_module() -> TrustIrModule {
    let i8_extern_ty = FuncTyId::new(0);
    let i16_extern_ty = FuncTyId::new(1);
    let i8_caller_ty = FuncTyId::new(2);
    let i16_caller_ty = FuncTyId::new(3);

    fn extern_decl(id: u32, name: &str, ty: FuncTyId) -> TrustIrFunction {
        TrustIrFunction {
            attrs: Default::default(),
            id: FuncId::new(id),
            name: name.to_owned(),
            ty,
            entry: BlockId::new(0),
            blocks: vec![],
            proofs: vec![],
            calling_conv: CallingConv::default(),
            linkage: Linkage::External,
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
        }
    }

    fn caller(id: u32, name: &str, ty: FuncTyId, callee: FuncId, narrow_ty: Ty) -> TrustIrFunction {
        TrustIrFunction {
            attrs: Default::default(),
            id: FuncId::new(id),
            name: name.to_owned(),
            ty,
            entry: BlockId::new(0),
            blocks: vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Call {
                        callee,
                        args: vec![],
                    })
                    .with_result(ValueId::new(0)),
                    InstrNode::new(Inst::Const {
                        ty: narrow_ty.clone(),
                        value: Constant::Int(0),
                    })
                    .with_result(ValueId::new(1)),
                    InstrNode::new(Inst::ICmp {
                        op: ICmpOp::Slt,
                        ty: narrow_ty,
                        lhs: ValueId::new(0),
                        rhs: ValueId::new(1),
                    })
                    .with_result(ValueId::new(2)),
                    InstrNode::new(Inst::Cast {
                        op: CastOp::ZExt,
                        src_ty: Ty::Bool,
                        dst_ty: Ty::I64,
                        operand: ValueId::new(2),
                    })
                    .with_result(ValueId::new(3)),
                    InstrNode::new(Inst::Return {
                        values: vec![ValueId::new(3)],
                    }),
                ],
            }],
            proofs: vec![],
            calling_conv: CallingConv::default(),
            linkage: Linkage::default(),
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
        }
    }

    TrustIrModule {
        name: "x86_64_windows_dirty_narrow_extern_return".to_owned(),
        functions: vec![
            extern_decl(0, "trust_cg_win64_dirty_i8_return", i8_extern_ty),
            extern_decl(1, "trust_cg_win64_dirty_i16_return", i16_extern_ty),
            caller(
                2,
                "dirty_i8_return_slt_zero",
                i8_caller_ty,
                FuncId::new(0),
                Ty::I8,
            ),
            caller(
                3,
                "dirty_i16_return_slt_zero",
                i16_caller_ty,
                FuncId::new(1),
                Ty::I16,
            ),
        ],
        structs: vec![],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![],
                returns: vec![Ty::I8],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::I16],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_canonicalizes_dirty_narrow_extern_returns() {
    let extern_symbols = HashMap::from([
        (
            "trust_cg_win64_dirty_i8_return".to_owned(),
            trust_cg_win64_dirty_i8_return as *const () as *const u8,
        ),
        (
            "trust_cg_win64_dirty_i16_return".to_owned(),
            trust_cg_win64_dirty_i16_return as *const () as *const u8,
        ),
    ]);
    let result = Compiler::for_host()
        .compile_module_to_jit(
            &windows_dirty_narrow_extern_return_module(),
            &extern_symbols,
        )
        .expect("Windows x86-64 JIT should compile dirty narrow extern-return probes");

    let dirty_i8_return_slt_zero: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("dirty_i8_return_slt_zero")
            .expect("dirty_i8_return_slt_zero symbol")
            .into_inner()
    };
    let dirty_i16_return_slt_zero: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("dirty_i16_return_slt_zero")
            .expect("dirty_i16_return_slt_zero symbol")
            .into_inner()
    };

    assert_eq!(dirty_i8_return_slt_zero(), 1);
    assert_eq!(dirty_i16_return_slt_zero(), 1);
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_executes_atomic_xchg_i64() {
    let mut mb = ModuleBuilder::new("x86_64_windows_atomic_xchg_i64");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("atomic_swap_i64", ty);
    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let desired = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let old = fb.atomic_rmw(AtomicRMWOp::Xchg, Ty::I64, ptr, desired, Ordering::SeqCst);
    fb.ret(vec![old]);
    fb.build();
    let module = mb.build();

    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile i64 atomic exchange");
    let atomic_swap_i64: extern "C" fn(*mut i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("atomic_swap_i64")
            .expect("atomic_swap_i64 symbol")
            .into_inner()
    };

    let mut cell = 11_i64;
    assert_eq!(atomic_swap_i64(&mut cell, 29), 11);
    assert_eq!(cell, 29);
    assert_eq!(atomic_swap_i64(&mut cell, -7), 29);
    assert_eq!(cell, -7);
}

#[cfg(target_os = "windows")]
fn add_atomic_store_load_zext_fn(mb: &mut ModuleBuilder, name: &'static str, narrow_ty: Ty) {
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function(name, ty);
    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let value = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let narrowed = fb.trunc(Ty::I64, narrow_ty.clone(), value);
    fb.atomic_store(narrow_ty.clone(), ptr, narrowed, Ordering::SeqCst);
    let loaded = fb.atomic_load(narrow_ty.clone(), ptr, Ordering::SeqCst);
    let widened = fb.zext(narrow_ty, Ty::I64, loaded);
    fb.ret(vec![widened]);
    fb.build();
}

#[cfg(target_os = "windows")]
fn add_atomic_fence_load_fn(mb: &mut ModuleBuilder, name: &'static str, ordering: Ordering) {
    let ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
    let mut fb = mb.function(name, ty);
    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    fb.fence(ordering);
    let loaded = fb.atomic_load(Ty::I64, ptr, Ordering::Acquire);
    fb.ret(vec![loaded]);
    fb.build();
}

#[cfg(target_os = "windows")]
fn windows_atomic_load_store_fence_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("x86_64_windows_atomic_load_store_fence");

    {
        let ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
        let mut fb = mb.function("atomic_load_i64", ty);
        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        let loaded = fb.atomic_load(Ty::I64, ptr, Ordering::SeqCst);
        fb.ret(vec![loaded]);
        fb.build();
    }

    {
        let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("atomic_store_load_i64", ty);
        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        let value = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        fb.atomic_store(Ty::I64, ptr, value, Ordering::SeqCst);
        let loaded = fb.atomic_load(Ty::I64, ptr, Ordering::SeqCst);
        fb.ret(vec![loaded]);
        fb.build();
    }

    add_atomic_store_load_zext_fn(&mut mb, "atomic_store_load_i8_zext", Ty::I8);
    add_atomic_store_load_zext_fn(&mut mb, "atomic_store_load_i16_zext", Ty::I16);
    add_atomic_store_load_zext_fn(&mut mb, "atomic_store_load_i32_zext", Ty::I32);

    {
        let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("atomic_fence_store_load_i64", ty);
        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        let value = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        fb.atomic_store(Ty::I64, ptr, value, Ordering::Release);
        fb.fence(Ordering::SeqCst);
        let loaded = fb.atomic_load(Ty::I64, ptr, Ordering::Acquire);
        fb.ret(vec![loaded]);
        fb.build();
    }

    add_atomic_fence_load_fn(&mut mb, "atomic_fence_acquire_load_i64", Ordering::Acquire);
    add_atomic_fence_load_fn(&mut mb, "atomic_fence_release_load_i64", Ordering::Release);
    add_atomic_fence_load_fn(&mut mb, "atomic_fence_acqrel_load_i64", Ordering::AcqRel);

    mb.build()
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_executes_atomic_load_store_fence_widths() {
    let module = windows_atomic_load_store_fence_module();
    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = OptLevel::O0;
    let result = Compiler::new(config)
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile atomic load/store/fence widths");

    let atomic_load_i64: extern "C" fn(*mut i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("atomic_load_i64")
            .expect("atomic_load_i64 symbol")
            .into_inner()
    };
    let atomic_store_load_i64: extern "C" fn(*mut i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("atomic_store_load_i64")
            .expect("atomic_store_load_i64 symbol")
            .into_inner()
    };
    let atomic_store_load_i8: extern "C" fn(*mut u8, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("atomic_store_load_i8_zext")
            .expect("atomic_store_load_i8_zext symbol")
            .into_inner()
    };
    let atomic_store_load_i16: extern "C" fn(*mut u16, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("atomic_store_load_i16_zext")
            .expect("atomic_store_load_i16_zext symbol")
            .into_inner()
    };
    let atomic_store_load_i32: extern "C" fn(*mut u32, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("atomic_store_load_i32_zext")
            .expect("atomic_store_load_i32_zext symbol")
            .into_inner()
    };
    let atomic_fence_store_load_i64: extern "C" fn(*mut i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("atomic_fence_store_load_i64")
            .expect("atomic_fence_store_load_i64 symbol")
            .into_inner()
    };

    let mut cell = 11_i64;
    assert_eq!(atomic_load_i64(&mut cell), 11);
    assert_eq!(atomic_store_load_i64(&mut cell, -12345), -12345);
    assert_eq!(cell, -12345);

    let mut bytes = [0xAA_u8, 0x11, 0xBB];
    let byte_ptr = unsafe { bytes.as_mut_ptr().add(1) };
    assert_eq!(atomic_store_load_i8(byte_ptr, 0x1ff), 0xff);
    assert_eq!(bytes, [0xAA, 0xFF, 0xBB]);

    let mut words = [0xAAAA_u16, 0x1111, 0xBBBB];
    assert_eq!(atomic_store_load_i16(&mut words[1], 0x1_2345), 0x2345);
    assert_eq!(words, [0xAAAA, 0x2345, 0xBBBB]);

    let mut dwords = [0xAAAA_AAAA_u32, 0x1111_1111, 0xBBBB_BBBB];
    assert_eq!(
        atomic_store_load_i32(&mut dwords[1], 0x1_2345_6789),
        0x2345_6789
    );
    assert_eq!(dwords, [0xAAAA_AAAA, 0x2345_6789, 0xBBBB_BBBB]);

    let mut fence_cell = 5_i64;
    assert_eq!(atomic_fence_store_load_i64(&mut fence_cell, 41), 41);
    assert_eq!(fence_cell, 41);

    let (fence_bytes, _, _) =
        windows_jit_symbol_bytes(&result.buffer, "atomic_fence_store_load_i64");
    assert!(
        fence_bytes
            .windows(3)
            .any(|window| window == [0x0F, 0xAE, 0xF0]),
        "atomic_fence_store_load_i64 should contain MFENCE (0f ae f0), bytes: {fence_bytes:02x?}"
    );
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_executes_non_exchange_atomic_rmw_i64() {
    let mut mb = ModuleBuilder::new("x86_64_windows_non_exchange_atomic_rmw_i64");
    macro_rules! add_atomic_rmw_fn {
        ($name:literal, $op:expr) => {{
            let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
            let mut fb = mb.function($name, ty);
            let entry = fb.create_block();
            let ptr = fb.add_block_param(entry, Ty::Ptr);
            let value = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            let old = fb.atomic_rmw($op, Ty::I64, ptr, value, Ordering::SeqCst);
            fb.ret(vec![old]);
            fb.build();
        }};
    }

    add_atomic_rmw_fn!("atomic_add_i64", AtomicRMWOp::Add);
    add_atomic_rmw_fn!("atomic_sub_i64", AtomicRMWOp::Sub);
    add_atomic_rmw_fn!("atomic_and_i64", AtomicRMWOp::And);
    add_atomic_rmw_fn!("atomic_or_i64", AtomicRMWOp::Or);
    add_atomic_rmw_fn!("atomic_xor_i64", AtomicRMWOp::Xor);
    let module = mb.build();

    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile i64 non-exchange atomic RMWs");
    let atomic_add_i64: extern "C" fn(*mut i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("atomic_add_i64")
            .expect("atomic_add_i64 symbol")
            .into_inner()
    };
    let atomic_sub_i64: extern "C" fn(*mut i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("atomic_sub_i64")
            .expect("atomic_sub_i64 symbol")
            .into_inner()
    };
    let atomic_and_i64: extern "C" fn(*mut i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("atomic_and_i64")
            .expect("atomic_and_i64 symbol")
            .into_inner()
    };
    let atomic_or_i64: extern "C" fn(*mut i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("atomic_or_i64")
            .expect("atomic_or_i64 symbol")
            .into_inner()
    };
    let atomic_xor_i64: extern "C" fn(*mut i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("atomic_xor_i64")
            .expect("atomic_xor_i64 symbol")
            .into_inner()
    };

    let mut cell = 11_i64;
    assert_eq!(atomic_add_i64(&mut cell, 5), 11);
    assert_eq!(cell, 16);
    assert_eq!(atomic_add_i64(&mut cell, -7), 16);
    assert_eq!(cell, 9);

    cell = 20;
    assert_eq!(atomic_sub_i64(&mut cell, 5), 20);
    assert_eq!(cell, 15);
    assert_eq!(atomic_sub_i64(&mut cell, -7), 15);
    assert_eq!(cell, 22);

    cell = 0b1111_0000;
    assert_eq!(atomic_and_i64(&mut cell, 0b1010_1010), 0b1111_0000);
    assert_eq!(cell, 0b1010_0000);

    cell = 0b0001_0000;
    assert_eq!(atomic_or_i64(&mut cell, 0b0000_0101), 0b0001_0000);
    assert_eq!(cell, 0b0001_0101);

    cell = 0b1010;
    assert_eq!(atomic_xor_i64(&mut cell, 0b1100), 0b1010);
    assert_eq!(cell, 0b0110);
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_executes_non_exchange_atomic_rmw_i8_i16() {
    let mut mb = ModuleBuilder::new("x86_64_windows_non_exchange_atomic_rmw_i8_i16");

    {
        let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("atomic_add_i8_zext_old", ty);
        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        let value = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let narrowed = fb.trunc(Ty::I64, Ty::I8, value);
        let old = fb.atomic_rmw(AtomicRMWOp::Add, Ty::I8, ptr, narrowed, Ordering::SeqCst);
        let old_i64 = fb.zext(Ty::I8, Ty::I64, old);
        fb.ret(vec![old_i64]);
        fb.build();
    }

    {
        let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("atomic_xor_i16_zext_old", ty);
        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        let value = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let narrowed = fb.trunc(Ty::I64, Ty::I16, value);
        let old = fb.atomic_rmw(AtomicRMWOp::Xor, Ty::I16, ptr, narrowed, Ordering::SeqCst);
        let old_i64 = fb.zext(Ty::I16, Ty::I64, old);
        fb.ret(vec![old_i64]);
        fb.build();
    }

    let module = mb.build();
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile i8/i16 non-exchange atomic RMWs");
    let atomic_add_i8: extern "C" fn(*mut u8, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("atomic_add_i8_zext_old")
            .expect("atomic_add_i8_zext_old symbol")
            .into_inner()
    };
    let atomic_xor_i16: extern "C" fn(*mut u16, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("atomic_xor_i16_zext_old")
            .expect("atomic_xor_i16_zext_old symbol")
            .into_inner()
    };

    let mut bytes = [250_u8, 0xAA];
    assert_eq!(atomic_add_i8(&mut bytes[0], 10), 250);
    assert_eq!(bytes, [4, 0xAA]);

    let mut words = [0xFFF0_u16, 0xBEEF];
    assert_eq!(atomic_xor_i16(&mut words[0], 0x00FF), 0xFFF0);
    assert_eq!(words, [0xFF0F, 0xBEEF]);
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_executes_cmpxchg_i64_success_and_failure() {
    let mut mb = ModuleBuilder::new("x86_64_windows_cmpxchg_i64");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("atomic_cas_i64", ty);
    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let expected = fb.add_block_param(entry, Ty::I64);
    let desired = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let (old, _success) = fb.cmpxchg(
        Ty::I64,
        ptr,
        expected,
        desired,
        Ordering::SeqCst,
        Ordering::SeqCst,
    );
    fb.ret(vec![old]);
    fb.build();
    let module = mb.build();

    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile i64 compare-exchange");
    let atomic_cas_i64: extern "C" fn(*mut i64, i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("atomic_cas_i64")
            .expect("atomic_cas_i64 symbol")
            .into_inner()
    };

    let mut cell = 11_i64;
    assert_eq!(atomic_cas_i64(&mut cell, 11, 29), 11);
    assert_eq!(cell, 29);
    assert_eq!(atomic_cas_i64(&mut cell, 11, 41), 29);
    assert_eq!(cell, 29);
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_executes_branch_diamond_with_block_args() {
    let mut mb = ModuleBuilder::new("x86_64_windows_branch_diamond_block_args");
    let ty = mb.add_func_type(vec![Ty::I64, Ty::I64, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("branch_diamond_block_arg", ty);
    let entry = fb.create_block();
    let selector = fb.add_block_param(entry, Ty::I64);
    let lhs = fb.add_block_param(entry, Ty::I64);
    let rhs = fb.add_block_param(entry, Ty::I64);
    let then_block = fb.create_block();
    let else_block = fb.create_block();
    let join_block = fb.create_block();
    let joined = fb.add_block_param(join_block, Ty::I64);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::I64, 0);
    let choose_lhs = fb.icmp(ICmpOp::Sgt, Ty::I64, selector, zero);
    fb.condbr(choose_lhs, then_block, vec![], else_block, vec![]);

    fb.switch_to_block(then_block);
    let lhs_adjusted = fb.add(Ty::I64, lhs, selector);
    fb.br(join_block, vec![lhs_adjusted]);

    fb.switch_to_block(else_block);
    let neg_selector = fb.sub(Ty::I64, zero, selector);
    let rhs_adjusted = fb.add(Ty::I64, rhs, neg_selector);
    fb.br(join_block, vec![rhs_adjusted]);

    fb.switch_to_block(join_block);
    let bias = fb.iconst(Ty::I64, 5);
    let result = fb.add(Ty::I64, joined, bias);
    fb.ret(vec![result]);
    fb.build();
    let module = mb.build();

    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile a branch diamond with block args");
    let branch_diamond_block_arg: extern "C" fn(i64, i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("branch_diamond_block_arg")
            .expect("branch_diamond_block_arg symbol")
            .into_inner()
    };

    assert_eq!(branch_diamond_block_arg(7, 10, 100), 22);
    assert_eq!(branch_diamond_block_arg(-3, 10, 100), 108);
    assert_eq!(branch_diamond_block_arg(0, 2, 9), 14);
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_executes_scalar_fp_select() {
    let mut mb = ModuleBuilder::new("x86_64_windows_scalar_fp_select");

    {
        let ty = mb.add_func_type(vec![Ty::I64, Ty::F64, Ty::F64], vec![Ty::F64]);
        let mut fb = mb.function("select_f64_from_i64_cmp", ty);
        let entry = fb.create_block();
        let selector = fb.add_block_param(entry, Ty::I64);
        let true_val = fb.add_block_param(entry, Ty::F64);
        let false_val = fb.add_block_param(entry, Ty::F64);
        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::I64, 0);
        let cond = fb.icmp(ICmpOp::Sgt, Ty::I64, selector, zero);
        let selected = fb.select(Ty::F64, cond, true_val, false_val);
        fb.ret(vec![selected]);
        fb.build();
    }

    {
        let ty = mb.add_func_type(vec![Ty::I64, Ty::F32, Ty::F32], vec![Ty::F32]);
        let mut fb = mb.function("select_f32_from_i64_cmp", ty);
        let entry = fb.create_block();
        let selector = fb.add_block_param(entry, Ty::I64);
        let true_val = fb.add_block_param(entry, Ty::F32);
        let false_val = fb.add_block_param(entry, Ty::F32);
        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::I64, 0);
        let cond = fb.icmp(ICmpOp::Sgt, Ty::I64, selector, zero);
        let selected = fb.select(Ty::F32, cond, true_val, false_val);
        fb.ret(vec![selected]);
        fb.build();
    }

    let module = mb.build();
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile scalar FP selects");
    let select_f64_from_i64_cmp: extern "C" fn(i64, f64, f64) -> f64 = unsafe {
        result
            .buffer
            .get_fn_bound("select_f64_from_i64_cmp")
            .expect("select_f64_from_i64_cmp symbol")
            .into_inner()
    };
    let select_f32_from_i64_cmp: extern "C" fn(i64, f32, f32) -> f32 = unsafe {
        result
            .buffer
            .get_fn_bound("select_f32_from_i64_cmp")
            .expect("select_f32_from_i64_cmp symbol")
            .into_inner()
    };

    assert_eq!(select_f64_from_i64_cmp(7, 1.5, -2.25), 1.5);
    assert_eq!(select_f64_from_i64_cmp(0, 1.5, -2.25), -2.25);
    assert_eq!(select_f64_from_i64_cmp(-3, 1.5, -2.25), -2.25);
    assert_eq!(select_f32_from_i64_cmp(4, 3.25, -4.5), 3.25);
    assert_eq!(select_f32_from_i64_cmp(0, 3.25, -4.5), -4.5);
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_executes_fcmp_nan_predicates() {
    fn add_fcmp_i64_result(mb: &mut ModuleBuilder, name: &str, ty: Ty, op: FCmpOp) {
        let sig = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![Ty::I64]);
        let mut fb = mb.function(name, sig);
        let entry = fb.create_block();
        let lhs = fb.add_block_param(entry, ty.clone());
        let rhs = fb.add_block_param(entry, ty.clone());
        fb.switch_to_block(entry);
        let cond = fb.fcmp(op, ty, lhs, rhs);
        let one = fb.iconst(Ty::I64, 1);
        let zero = fb.iconst(Ty::I64, 0);
        let result = fb.select(Ty::I64, cond, one, zero);
        fb.ret(vec![result]);
        fb.build();
    }

    let mut mb = ModuleBuilder::new("x86_64_windows_fcmp_nan_predicates");
    add_fcmp_i64_result(&mut mb, "fcmp_f64_oeq", Ty::F64, FCmpOp::OEq);
    add_fcmp_i64_result(&mut mb, "fcmp_f64_olt", Ty::F64, FCmpOp::OLt);
    add_fcmp_i64_result(&mut mb, "fcmp_f64_one", Ty::F64, FCmpOp::ONe);
    add_fcmp_i64_result(&mut mb, "fcmp_f64_oge", Ty::F64, FCmpOp::OGe);
    add_fcmp_i64_result(&mut mb, "fcmp_f64_ueq", Ty::F64, FCmpOp::UEq);
    add_fcmp_i64_result(&mut mb, "fcmp_f64_une", Ty::F64, FCmpOp::UNe);
    add_fcmp_i64_result(&mut mb, "fcmp_f64_ult", Ty::F64, FCmpOp::ULt);
    add_fcmp_i64_result(&mut mb, "fcmp_f64_ugt", Ty::F64, FCmpOp::UGt);
    add_fcmp_i64_result(&mut mb, "fcmp_f64_uge", Ty::F64, FCmpOp::UGe);
    add_fcmp_i64_result(&mut mb, "fcmp_f32_ole", Ty::F32, FCmpOp::OLe);
    add_fcmp_i64_result(&mut mb, "fcmp_f32_oge", Ty::F32, FCmpOp::OGe);
    add_fcmp_i64_result(&mut mb, "fcmp_f32_ult", Ty::F32, FCmpOp::ULt);
    add_fcmp_i64_result(&mut mb, "fcmp_f32_ugt", Ty::F32, FCmpOp::UGt);
    add_fcmp_i64_result(&mut mb, "fcmp_f32_uge", Ty::F32, FCmpOp::UGe);

    let module = mb.build();
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile FCmp NaN predicates");
    type F64Cmp = extern "C" fn(f64, f64) -> i64;
    type F32Cmp = extern "C" fn(f32, f32) -> i64;
    let fcmp_f64_oeq: F64Cmp = unsafe {
        result
            .buffer
            .get_fn_bound("fcmp_f64_oeq")
            .expect("fcmp_f64_oeq symbol")
            .into_inner()
    };
    let fcmp_f64_olt: F64Cmp = unsafe {
        result
            .buffer
            .get_fn_bound("fcmp_f64_olt")
            .expect("fcmp_f64_olt symbol")
            .into_inner()
    };
    let fcmp_f64_one: F64Cmp = unsafe {
        result
            .buffer
            .get_fn_bound("fcmp_f64_one")
            .expect("fcmp_f64_one symbol")
            .into_inner()
    };
    let fcmp_f64_oge: F64Cmp = unsafe {
        result
            .buffer
            .get_fn_bound("fcmp_f64_oge")
            .expect("fcmp_f64_oge symbol")
            .into_inner()
    };
    let fcmp_f64_ueq: F64Cmp = unsafe {
        result
            .buffer
            .get_fn_bound("fcmp_f64_ueq")
            .expect("fcmp_f64_ueq symbol")
            .into_inner()
    };
    let fcmp_f64_une: F64Cmp = unsafe {
        result
            .buffer
            .get_fn_bound("fcmp_f64_une")
            .expect("fcmp_f64_une symbol")
            .into_inner()
    };
    let fcmp_f64_ult: F64Cmp = unsafe {
        result
            .buffer
            .get_fn_bound("fcmp_f64_ult")
            .expect("fcmp_f64_ult symbol")
            .into_inner()
    };
    let fcmp_f64_ugt: F64Cmp = unsafe {
        result
            .buffer
            .get_fn_bound("fcmp_f64_ugt")
            .expect("fcmp_f64_ugt symbol")
            .into_inner()
    };
    let fcmp_f64_uge: F64Cmp = unsafe {
        result
            .buffer
            .get_fn_bound("fcmp_f64_uge")
            .expect("fcmp_f64_uge symbol")
            .into_inner()
    };
    let fcmp_f32_ole: F32Cmp = unsafe {
        result
            .buffer
            .get_fn_bound("fcmp_f32_ole")
            .expect("fcmp_f32_ole symbol")
            .into_inner()
    };
    let fcmp_f32_oge: F32Cmp = unsafe {
        result
            .buffer
            .get_fn_bound("fcmp_f32_oge")
            .expect("fcmp_f32_oge symbol")
            .into_inner()
    };
    let fcmp_f32_ult: F32Cmp = unsafe {
        result
            .buffer
            .get_fn_bound("fcmp_f32_ult")
            .expect("fcmp_f32_ult symbol")
            .into_inner()
    };
    let fcmp_f32_ugt: F32Cmp = unsafe {
        result
            .buffer
            .get_fn_bound("fcmp_f32_ugt")
            .expect("fcmp_f32_ugt symbol")
            .into_inner()
    };
    let fcmp_f32_uge: F32Cmp = unsafe {
        result
            .buffer
            .get_fn_bound("fcmp_f32_uge")
            .expect("fcmp_f32_uge symbol")
            .into_inner()
    };

    let nan64 = f64::NAN;
    assert_eq!(fcmp_f64_oeq(2.0, 2.0), 1);
    assert_eq!(fcmp_f64_oeq(2.0, 3.0), 0);
    assert_eq!(fcmp_f64_oeq(3.0, 2.0), 0);
    assert_eq!(fcmp_f64_oeq(nan64, 2.0), 0);
    assert_eq!(fcmp_f64_oeq(2.0, nan64), 0);

    assert_eq!(fcmp_f64_olt(1.0, 2.0), 1);
    assert_eq!(fcmp_f64_olt(2.0, 2.0), 0);
    assert_eq!(fcmp_f64_olt(3.0, 2.0), 0);
    assert_eq!(fcmp_f64_olt(nan64, 2.0), 0);
    assert_eq!(fcmp_f64_olt(2.0, nan64), 0);

    assert_eq!(fcmp_f64_one(2.0, 2.0), 0);
    assert_eq!(fcmp_f64_one(1.0, 2.0), 1);
    assert_eq!(fcmp_f64_one(3.0, 2.0), 1);
    assert_eq!(fcmp_f64_one(nan64, 2.0), 0);
    assert_eq!(fcmp_f64_one(2.0, nan64), 0);

    assert_eq!(fcmp_f64_oge(1.0, 2.0), 0);
    assert_eq!(fcmp_f64_oge(2.0, 2.0), 1);
    assert_eq!(fcmp_f64_oge(3.0, 2.0), 1);
    assert_eq!(fcmp_f64_oge(nan64, 2.0), 0);
    assert_eq!(fcmp_f64_oge(2.0, nan64), 0);

    assert_eq!(fcmp_f64_ueq(2.0, 2.0), 1);
    assert_eq!(fcmp_f64_ueq(1.0, 2.0), 0);
    assert_eq!(fcmp_f64_ueq(3.0, 2.0), 0);
    assert_eq!(fcmp_f64_ueq(nan64, 2.0), 1);
    assert_eq!(fcmp_f64_ueq(2.0, nan64), 1);

    assert_eq!(fcmp_f64_une(2.0, 2.0), 0);
    assert_eq!(fcmp_f64_une(1.0, 2.0), 1);
    assert_eq!(fcmp_f64_une(3.0, 2.0), 1);
    assert_eq!(fcmp_f64_une(nan64, 2.0), 1);
    assert_eq!(fcmp_f64_une(2.0, nan64), 1);

    assert_eq!(fcmp_f64_ult(1.0, 2.0), 1);
    assert_eq!(fcmp_f64_ult(2.0, 2.0), 0);
    assert_eq!(fcmp_f64_ult(3.0, 2.0), 0);
    assert_eq!(fcmp_f64_ult(nan64, 2.0), 1);
    assert_eq!(fcmp_f64_ult(2.0, nan64), 1);

    assert_eq!(fcmp_f64_ugt(1.0, 2.0), 0);
    assert_eq!(fcmp_f64_ugt(2.0, 2.0), 0);
    assert_eq!(fcmp_f64_ugt(3.0, 2.0), 1);
    assert_eq!(fcmp_f64_ugt(nan64, 2.0), 1);
    assert_eq!(fcmp_f64_ugt(2.0, nan64), 1);

    assert_eq!(fcmp_f64_uge(1.0, 2.0), 0);
    assert_eq!(fcmp_f64_uge(2.0, 2.0), 1);
    assert_eq!(fcmp_f64_uge(3.0, 2.0), 1);
    assert_eq!(fcmp_f64_uge(nan64, 2.0), 1);
    assert_eq!(fcmp_f64_uge(2.0, nan64), 1);

    let nan32 = f32::NAN;
    assert_eq!(fcmp_f32_ole(1.0, 2.0), 1);
    assert_eq!(fcmp_f32_ole(2.0, 2.0), 1);
    assert_eq!(fcmp_f32_ole(3.0, 2.0), 0);
    assert_eq!(fcmp_f32_ole(nan32, 2.0), 0);
    assert_eq!(fcmp_f32_ole(2.0, nan32), 0);

    assert_eq!(fcmp_f32_oge(1.0, 2.0), 0);
    assert_eq!(fcmp_f32_oge(2.0, 2.0), 1);
    assert_eq!(fcmp_f32_oge(3.0, 2.0), 1);
    assert_eq!(fcmp_f32_oge(nan32, 2.0), 0);
    assert_eq!(fcmp_f32_oge(2.0, nan32), 0);

    assert_eq!(fcmp_f32_ult(1.0, 2.0), 1);
    assert_eq!(fcmp_f32_ult(2.0, 2.0), 0);
    assert_eq!(fcmp_f32_ult(3.0, 2.0), 0);
    assert_eq!(fcmp_f32_ult(nan32, 2.0), 1);
    assert_eq!(fcmp_f32_ult(2.0, nan32), 1);

    assert_eq!(fcmp_f32_ugt(1.0, 2.0), 0);
    assert_eq!(fcmp_f32_ugt(2.0, 2.0), 0);
    assert_eq!(fcmp_f32_ugt(3.0, 2.0), 1);
    assert_eq!(fcmp_f32_ugt(nan32, 2.0), 1);
    assert_eq!(fcmp_f32_ugt(2.0, nan32), 1);

    assert_eq!(fcmp_f32_uge(1.0, 2.0), 0);
    assert_eq!(fcmp_f32_uge(2.0, 2.0), 1);
    assert_eq!(fcmp_f32_uge(3.0, 2.0), 1);
    assert_eq!(fcmp_f32_uge(nan32, 2.0), 1);
    assert_eq!(fcmp_f32_uge(2.0, nan32), 1);
}

#[cfg(all(target_os = "windows", feature = "verify"))]
fn windows_scalar_fp_select_proof_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_windows_scalar_fp_select_proofs");

    {
        let ty = mb.add_func_type(vec![Ty::I64, Ty::F64, Ty::F64], vec![Ty::F64]);
        let mut fb = mb.function("proof_select_f64_from_i64_cmp", ty);
        let entry = fb.create_block();
        let selector = fb.add_block_param(entry, Ty::I64);
        let true_val = fb.add_block_param(entry, Ty::F64);
        let false_val = fb.add_block_param(entry, Ty::F64);
        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::I64, 0);
        let cond = fb.icmp(ICmpOp::Sgt, Ty::I64, selector, zero);
        let selected = fb.select(Ty::F64, cond, true_val, false_val);
        fb.ret(vec![selected]);
        fb.build();
    }

    {
        let ty = mb.add_func_type(vec![Ty::I64, Ty::F32, Ty::F32], vec![Ty::F32]);
        let mut fb = mb.function("proof_select_f32_from_i64_cmp", ty);
        let entry = fb.create_block();
        let selector = fb.add_block_param(entry, Ty::I64);
        let true_val = fb.add_block_param(entry, Ty::F32);
        let false_val = fb.add_block_param(entry, Ty::F32);
        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::I64, 0);
        let cond = fb.icmp(ICmpOp::Sgt, Ty::I64, selector, zero);
        let selected = fb.select(Ty::F32, cond, true_val, false_val);
        fb.ret(vec![selected]);
        fb.build();
    }

    mb.build()
}

#[cfg(all(target_os = "windows", feature = "verify"))]
fn windows_fcmp_remainder_proof_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_windows_fcmp_remainder_proofs");

    {
        let ty = mb.add_func_type(vec![Ty::F64, Ty::F64], vec![Ty::I64]);
        let mut fb = mb.function("proof_fcmp_f64_oge", ty);
        let entry = fb.create_block();
        let lhs = fb.add_block_param(entry, Ty::F64);
        let rhs = fb.add_block_param(entry, Ty::F64);
        fb.switch_to_block(entry);
        let cmp = fb.fcmp(FCmpOp::OGe, Ty::F64, lhs, rhs);
        let as_i64 = fb.zext(Ty::Bool, Ty::I64, cmp);
        fb.ret(vec![as_i64]);
        fb.build();
    }

    {
        let ty = mb.add_func_type(vec![Ty::F32, Ty::F32], vec![Ty::I64]);
        let mut fb = mb.function("proof_fcmp_f32_uge", ty);
        let entry = fb.create_block();
        let lhs = fb.add_block_param(entry, Ty::F32);
        let rhs = fb.add_block_param(entry, Ty::F32);
        fb.switch_to_block(entry);
        let cmp = fb.fcmp(FCmpOp::UGe, Ty::F32, lhs, rhs);
        let as_i64 = fb.zext(Ty::Bool, Ty::I64, cmp);
        fb.ret(vec![as_i64]);
        fb.build();
    }

    {
        let ty = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![Ty::U32]);
        let mut fb = mb.function("proof_urem_u32", ty);
        let entry = fb.create_block();
        let lhs = fb.add_block_param(entry, Ty::U32);
        let rhs = fb.add_block_param(entry, Ty::U32);
        fb.switch_to_block(entry);
        let rem = fb.binop(BinOp::URem, Ty::U32, lhs, rhs);
        fb.ret(vec![rem]);
        fb.build();
    }

    {
        let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("proof_srem_i64", ty);
        let entry = fb.create_block();
        let lhs = fb.add_block_param(entry, Ty::I64);
        let rhs = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let rem = fb.binop(BinOp::SRem, Ty::I64, lhs, rhs);
        fb.ret(vec![rem]);
        fb.build();
    }

    mb.build()
}

#[cfg(all(target_os = "windows", feature = "verify"))]
fn windows_atomic_rmw_proof_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_windows_atomic_rmw_proofs");

    {
        let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("proof_atomic_add_i64", ty);
        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        let value = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let old = fb.atomic_rmw(AtomicRMWOp::Add, Ty::I64, ptr, value, Ordering::SeqCst);
        fb.ret(vec![old]);
        fb.build();
    }

    {
        let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("proof_atomic_xchg_i8", ty);
        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        let value = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let narrowed = fb.trunc(Ty::I64, Ty::I8, value);
        let old = fb.atomic_rmw(AtomicRMWOp::Xchg, Ty::I8, ptr, narrowed, Ordering::SeqCst);
        let old_i64 = fb.zext(Ty::I8, Ty::I64, old);
        fb.ret(vec![old_i64]);
        fb.build();
    }

    {
        let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("proof_atomic_xor_i16", ty);
        let entry = fb.create_block();
        let ptr = fb.add_block_param(entry, Ty::Ptr);
        let value = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let narrowed = fb.trunc(Ty::I64, Ty::I16, value);
        let old = fb.atomic_rmw(AtomicRMWOp::Xor, Ty::I16, ptr, narrowed, Ordering::SeqCst);
        let old_i64 = fb.zext(Ty::I16, Ty::I64, old);
        fb.ret(vec![old_i64]);
        fb.build();
    }

    mb.build()
}

#[cfg(all(target_os = "windows", feature = "verify"))]
fn windows_call_branch_proof_gap_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_windows_call_branch_proof_gaps");

    {
        let ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("proof_gap_callee", ty);
        let entry = fb.create_block();
        let value = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let one = fb.iconst(Ty::I64, 1);
        let result = fb.add(Ty::I64, value, one);
        fb.ret(vec![result]);
        fb.build();
    }

    {
        let ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("proof_gap_entry", ty);
        let entry = fb.create_block();
        let input = fb.add_block_param(entry, Ty::I64);
        let then_block = fb.create_block();
        let else_block = fb.create_block();
        let join_block = fb.create_block();
        let joined = fb.add_block_param(join_block, Ty::I64);

        fb.switch_to_block(entry);
        let called = fb.call(FuncId::new(0), vec![input]);
        let zero = fb.iconst(Ty::I64, 0);
        let is_positive = fb.icmp(ICmpOp::Sgt, Ty::I64, called, zero);
        fb.condbr(is_positive, then_block, vec![], else_block, vec![]);

        fb.switch_to_block(then_block);
        let one = fb.iconst(Ty::I64, 1);
        fb.br(join_block, vec![one]);

        fb.switch_to_block(else_block);
        let minus_one = fb.iconst(Ty::I64, -1);
        fb.br(join_block, vec![minus_one]);

        fb.switch_to_block(join_block);
        fb.ret(vec![joined]);
        fb.build();
    }

    mb.build()
}

#[cfg(all(target_os = "windows", feature = "verify"))]
fn has_unverified_mapping_gap(
    proofs: &[trust_cg_codegen::compiler::ProofCertificate],
    opcode: trust_cg_ir::x86_64_ops::X86Opcode,
) -> bool {
    let needle = format!("no proof mapping for x86-64 opcode {opcode:?}");
    proofs.iter().any(|proof| {
        !proof.verified && proof.category == "unverified" && proof.strength.contains(&needle)
    })
}

#[cfg(all(target_os = "windows", feature = "verify"))]
fn has_unverified_query_gap(
    proofs: &[trust_cg_codegen::compiler::ProofCertificate],
    query: &str,
) -> bool {
    let needle = format!("no x86-64 proof matching '{query}'");
    proofs.iter().any(|proof| {
        !proof.verified && proof.category == "unverified" && proof.strength.contains(&needle)
    })
}

#[cfg(all(target_os = "windows", feature = "verify"))]
fn has_verified_query(
    proofs: &[trust_cg_codegen::compiler::ProofCertificate],
    query: &str,
) -> bool {
    proofs.iter().any(|proof| {
        proof.verified && proof.category == "x86-64 Lowering" && proof.rule_name.contains(query)
    })
}

#[cfg(all(target_os = "windows", feature = "verify"))]
fn has_verified_query_for_function(
    proofs: &[trust_cg_codegen::compiler::ProofCertificate],
    function: &str,
    query: &str,
) -> bool {
    proofs.iter().any(|proof| {
        proof.function_name == function
            && proof.verified
            && proof.category == "x86-64 Lowering"
            && proof.rule_name.contains(query)
    })
}

#[cfg(all(target_os = "windows", feature = "verify"))]
fn assert_no_rule_for_function(
    proofs: &[trust_cg_codegen::compiler::ProofCertificate],
    function: &str,
    needle: &str,
) {
    assert!(
        !proofs
            .iter()
            .any(|proof| proof.function_name == function && proof.rule_name.contains(needle)),
        "{function} should not emit proof rule containing {needle:?}; proofs: {proofs:#?}"
    );
}

#[cfg(all(target_os = "windows", feature = "verify"))]
fn assert_fp_select_opcode_verified(
    proofs: &[trust_cg_codegen::compiler::ProofCertificate],
    opcode: trust_cg_ir::x86_64_ops::X86Opcode,
) {
    let mapping_gap = has_unverified_mapping_gap(proofs, opcode);
    let query = trust_cg_verify::X86FunctionVerifier::opcode_to_proof_query(opcode)
        .unwrap_or_else(|| panic!("{opcode:?} must map to an x86-64 proof query"));

    assert!(
        !mapping_gap,
        "{opcode:?} has a verifier query ({query}) but still emitted the old no-mapping gap; proofs: {proofs:#?}"
    );

    assert!(
        has_verified_query(proofs, query),
        "{opcode:?} must emit a verified scalar FP-select transfer proof for query {query}; proofs: {proofs:#?}"
    );
}

#[cfg(all(target_os = "windows", feature = "verify"))]
fn assert_atomic_rmw_query_verified(
    proofs: &[trust_cg_codegen::compiler::ProofCertificate],
    opcode: trust_cg_ir::x86_64_ops::X86Opcode,
    query: &str,
) {
    assert!(
        !has_unverified_mapping_gap(proofs, opcode),
        "{opcode:?} should have an x86-64 verifier query; proofs: {proofs:#?}"
    );
    assert!(
        !has_unverified_query_gap(proofs, query),
        "{opcode:?} should have a registered proof for query {query}; proofs: {proofs:#?}"
    );
    assert!(
        has_verified_query(proofs, query),
        "{opcode:?} must emit a verified atomic RMW proof for query {query}; proofs: {proofs:#?}"
    );
}

#[cfg(all(target_os = "windows", feature = "verify"))]
fn assert_atomic_memory_query_verified(
    proofs: &[trust_cg_codegen::compiler::ProofCertificate],
    opcode: trust_cg_ir::x86_64_ops::X86Opcode,
    query: &str,
) {
    assert!(
        !has_unverified_mapping_gap(proofs, opcode),
        "{opcode:?} should have an x86-64 verifier query for {query}; proofs: {proofs:#?}"
    );
    assert!(
        !has_unverified_query_gap(proofs, query),
        "{opcode:?} should have a registered proof for query {query}; proofs: {proofs:#?}"
    );
    assert!(
        has_verified_query(proofs, query),
        "{opcode:?} must emit a verified atomic memory/fence proof for query {query}; proofs: {proofs:#?}"
    );
}

#[cfg(all(target_os = "windows", feature = "verify"))]
fn assert_verified_rule_for_function(
    proofs: &[trust_cg_codegen::compiler::ProofCertificate],
    function: &str,
    rule_name: &str,
) {
    assert!(
        proofs.iter().any(|proof| {
            proof.function_name == function
                && proof.verified
                && proof.category == "x86-64 Lowering"
                && proof.rule_name == rule_name
        }),
        "{function} must emit exact verified proof rule {rule_name:?}; proofs: {proofs:#?}"
    );
}

#[cfg(all(target_os = "windows", feature = "verify"))]
fn assert_stale_transfer_gaps_absent(proofs: &[trust_cg_codegen::compiler::ProofCertificate]) {
    use trust_cg_ir::x86_64_ops::X86Opcode;

    for opcode in [
        X86Opcode::Cmovcc,
        X86Opcode::Cmovcc32,
        X86Opcode::MovqFromXmm,
        X86Opcode::MovqToXmm,
        X86Opcode::MovdFromXmm,
        X86Opcode::MovdToXmm,
    ] {
        assert!(
            !has_unverified_mapping_gap(proofs, opcode),
            "{opcode:?} is no longer a current verifier mapping gap; proofs: {proofs:#?}"
        );
    }
}

#[cfg(all(target_os = "windows", feature = "verify"))]
#[test]
fn x86_64_windows_jit_emit_proofs_records_call_branch_verifier_gaps() {
    let child = std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            use trust_cg_ir::x86_64_ops::X86Opcode;

            let module = windows_call_branch_proof_gap_module();
            let mut config = CompilerConfig::for_host_jit();
            config.emit_proofs = true;
            config.opt_level = OptLevel::O0;
            config.parallel = false;

            let result = Compiler::new(config)
                .compile_module_to_jit(&module, &HashMap::new())
                .expect("Windows x86-64 JIT should compile call/branch proof-gap module");

            let proof_gap_entry: extern "C" fn(i64) -> i64 = unsafe {
                result
                    .buffer
                    .get_fn_bound("proof_gap_entry")
                    .expect("proof_gap_entry symbol")
                    .into_inner()
            };
            assert_eq!(proof_gap_entry(3), 1);
            assert_eq!(proof_gap_entry(-4), -1);

            let proofs = result
                .proofs
                .as_ref()
                .expect("emit_proofs=true should attach x86 proof reports");
            assert!(
                proofs.iter().any(|proof| proof.verified),
                "call/branch proof-gap module should still emit verified reports for covered opcodes"
            );

            for opcode in [X86Opcode::Call, X86Opcode::Jcc, X86Opcode::Jmp] {
                assert!(
                    has_unverified_mapping_gap(proofs, opcode),
                    "{opcode:?} should remain visible as a current verifier mapping gap; proofs: {proofs:#?}"
                );
            }

            assert_stale_transfer_gaps_absent(proofs);
        })
        .expect("failed to spawn x86 call/branch proof-gap test thread");
    child
        .join()
        .expect("x86 call/branch proof-gap test thread panicked");
}

#[cfg(all(target_os = "windows", feature = "verify"))]
fn assert_no_failed_fp_select_transfer_proofs(
    proofs: &[trust_cg_codegen::compiler::ProofCertificate],
) {
    use trust_cg_ir::x86_64_ops::X86Opcode;

    let transfer_queries: Vec<_> = [
        X86Opcode::Cmovcc,
        X86Opcode::Cmovcc32,
        X86Opcode::MovqFromXmm,
        X86Opcode::MovqToXmm,
        X86Opcode::MovdFromXmm,
        X86Opcode::MovdToXmm,
    ]
    .into_iter()
    .filter_map(trust_cg_verify::X86FunctionVerifier::opcode_to_proof_query)
    .collect();

    let failed: Vec<_> = proofs
        .iter()
        .filter(|proof| {
            !proof.verified
                && proof.category != "unverified"
                && transfer_queries
                    .iter()
                    .any(|query| proof.rule_name.contains(query))
        })
        .collect();
    assert!(
        failed.is_empty(),
        "scalar FP-select transfer proofs must not fail once mapped; failed reports: {failed:#?}"
    );
}

#[cfg(all(target_os = "windows", feature = "verify"))]
fn assert_scalar_fp_select_transfer_proof_status(
    proofs: &[trust_cg_codegen::compiler::ProofCertificate],
) {
    use trust_cg_ir::x86_64_ops::X86Opcode;

    for opcode in [
        X86Opcode::Cmovcc,
        X86Opcode::Cmovcc32,
        X86Opcode::MovqFromXmm,
        X86Opcode::MovqToXmm,
        X86Opcode::MovdFromXmm,
        X86Opcode::MovdToXmm,
    ] {
        assert_fp_select_opcode_verified(proofs, opcode);
    }

    assert_no_failed_fp_select_transfer_proofs(proofs);
}

#[cfg(all(target_os = "windows", feature = "verify"))]
#[test]
fn x86_64_windows_jit_emit_proofs_tracks_scalar_fp_select_transfer_proofs() {
    let child = std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let module = windows_scalar_fp_select_proof_module();
            let mut config = CompilerConfig::for_host_jit();
            config.emit_proofs = true;
            config.opt_level = OptLevel::O0;
            config.parallel = false;

            let result = Compiler::new(config)
                .compile_module_to_jit(&module, &HashMap::new())
                .expect("Windows x86-64 JIT should compile with emit_proofs=true");

            let proof_select_f64_from_i64_cmp: extern "C" fn(i64, f64, f64) -> f64 = unsafe {
                result
                    .buffer
                    .get_fn_bound("proof_select_f64_from_i64_cmp")
                    .expect("proof_select_f64_from_i64_cmp symbol")
                    .into_inner()
            };
            let proof_select_f32_from_i64_cmp: extern "C" fn(i64, f32, f32) -> f32 = unsafe {
                result
                    .buffer
                    .get_fn_bound("proof_select_f32_from_i64_cmp")
                    .expect("proof_select_f32_from_i64_cmp symbol")
                    .into_inner()
            };
            assert_eq!(proof_select_f64_from_i64_cmp(3, 1.5, -2.5), 1.5);
            assert_eq!(proof_select_f64_from_i64_cmp(-4, 1.5, -2.5), -2.5);
            assert_eq!(proof_select_f32_from_i64_cmp(3, 4.25, -8.5), 4.25);
            assert_eq!(proof_select_f32_from_i64_cmp(-4, 4.25, -8.5), -8.5);

            let proofs = result
                .proofs
                .as_ref()
                .expect("emit_proofs=true should attach x86 proof reports");
            assert!(
                proofs.iter().any(|proof| proof.verified),
                "proof-gap module should still emit verified reports for covered opcodes"
            );

            assert_scalar_fp_select_transfer_proof_status(proofs);
        })
        .expect("failed to spawn x86 scalar FP-select proof test thread");
    child
        .join()
        .expect("x86 scalar FP-select proof test thread panicked");
}

#[cfg(all(target_os = "windows", feature = "verify"))]
#[test]
fn x86_64_windows_jit_emit_proofs_binds_fcmp_and_remainder_sequences_to_exact_proofs() {
    let child = std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            use trust_cg_ir::x86_64_ops::X86Opcode;

            let module = windows_fcmp_remainder_proof_module();
            let mut config = CompilerConfig::for_host_jit();
            config.emit_proofs = true;
            config.opt_level = OptLevel::O0;
            config.parallel = false;

            let result = Compiler::new(config)
                .compile_module_to_jit(&module, &HashMap::new())
                .expect("Windows x86-64 JIT should compile fcmp/rem with emit_proofs=true");

            let proof_fcmp_f64_oge: extern "C" fn(f64, f64) -> i64 = unsafe {
                result
                    .buffer
                    .get_fn_bound("proof_fcmp_f64_oge")
                    .expect("proof_fcmp_f64_oge symbol")
                    .into_inner()
            };
            let proof_fcmp_f32_uge: extern "C" fn(f32, f32) -> i64 = unsafe {
                result
                    .buffer
                    .get_fn_bound("proof_fcmp_f32_uge")
                    .expect("proof_fcmp_f32_uge symbol")
                    .into_inner()
            };
            let proof_urem_u32: extern "C" fn(u32, u32) -> u32 = unsafe {
                result
                    .buffer
                    .get_fn_bound("proof_urem_u32")
                    .expect("proof_urem_u32 symbol")
                    .into_inner()
            };
            let proof_srem_i64: extern "C" fn(i64, i64) -> i64 = unsafe {
                result
                    .buffer
                    .get_fn_bound("proof_srem_i64")
                    .expect("proof_srem_i64 symbol")
                    .into_inner()
            };

            assert_eq!(proof_fcmp_f64_oge(3.0, 2.0), 1);
            assert_eq!(proof_fcmp_f64_oge(1.0, 2.0), 0);
            assert_eq!(proof_fcmp_f32_uge(f32::NAN, 2.0), 1);
            assert_eq!(proof_fcmp_f32_uge(1.0, 2.0), 0);
            assert_eq!(proof_urem_u32(u32::MAX, 17), u32::MAX % 17);
            assert_eq!(proof_srem_i64(-987, 31), -987 % 31);

            let proofs = result
                .proofs
                .as_ref()
                .expect("emit_proofs=true should attach x86 proof reports");
            assert!(
                proofs.iter().any(|proof| proof.verified),
                "fcmp/rem proof module should emit verified x86-64 proof reports"
            );

            assert!(
                has_verified_query_for_function(proofs, "proof_fcmp_f64_oge", "Fcmp_GE_F64"),
                "proof_fcmp_f64_oge should bind to Fcmp_GE_F64; proofs: {proofs:#?}"
            );
            assert!(
                has_verified_query_for_function(proofs, "proof_fcmp_f32_uge", "Fcmp_UGE_F32"),
                "proof_fcmp_f32_uge should bind to Fcmp_UGE_F32; proofs: {proofs:#?}"
            );
            assert!(
                has_verified_query_for_function(proofs, "proof_urem_u32", "Urem_I32"),
                "proof_urem_u32 should bind to Urem_I32; proofs: {proofs:#?}"
            );
            assert!(
                has_verified_query_for_function(proofs, "proof_srem_i64", "Srem_I64"),
                "proof_srem_i64 should bind to Srem_I64; proofs: {proofs:#?}"
            );

            assert_no_rule_for_function(proofs, "proof_fcmp_f64_oge", "Icmp_");
            assert_no_rule_for_function(proofs, "proof_fcmp_f32_uge", "Icmp_");
            assert_no_rule_for_function(proofs, "proof_urem_u32", "Udiv_I");
            assert_no_rule_for_function(proofs, "proof_srem_i64", "Sdiv_I");

            for opcode in [
                X86Opcode::Ucomisd,
                X86Opcode::Ucomiss,
                X86Opcode::Div,
                X86Opcode::Idiv,
            ] {
                assert!(
                    !has_unverified_mapping_gap(proofs, opcode),
                    "{opcode:?} should not emit a stale verifier mapping gap; proofs: {proofs:#?}"
                );
            }

            for query in ["Fcmp_GE_F64", "Fcmp_UGE_F32", "Urem_I32", "Srem_I64"] {
                assert!(
                    !has_unverified_query_gap(proofs, query),
                    "{query} should have a verified x86-64 proof binding; proofs: {proofs:#?}"
                );
            }
        })
        .expect("failed to spawn x86 fcmp/remainder proof test thread");
    child
        .join()
        .expect("x86 fcmp/remainder proof test thread panicked");
}

#[cfg(all(target_os = "windows", feature = "verify"))]
#[test]
fn x86_64_windows_jit_emit_proofs_tracks_atomic_rmw_cas_loop_proofs() {
    let child = std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            use trust_cg_ir::x86_64_ops::X86Opcode;

            let module = windows_atomic_rmw_proof_module();
            let mut config = CompilerConfig::for_host_jit();
            config.emit_proofs = true;
            config.opt_level = OptLevel::O0;
            config.parallel = false;

            let result = Compiler::new(config)
                .compile_module_to_jit(&module, &HashMap::new())
                .expect("Windows x86-64 JIT should compile atomic RMWs with emit_proofs=true");

            let proof_atomic_add_i64: extern "C" fn(*mut i64, i64) -> i64 = unsafe {
                result
                    .buffer
                    .get_fn_bound("proof_atomic_add_i64")
                    .expect("proof_atomic_add_i64 symbol")
                    .into_inner()
            };
            let proof_atomic_xchg_i8: extern "C" fn(*mut u8, i64) -> i64 = unsafe {
                result
                    .buffer
                    .get_fn_bound("proof_atomic_xchg_i8")
                    .expect("proof_atomic_xchg_i8 symbol")
                    .into_inner()
            };
            let proof_atomic_xor_i16: extern "C" fn(*mut u16, i64) -> i64 = unsafe {
                result
                    .buffer
                    .get_fn_bound("proof_atomic_xor_i16")
                    .expect("proof_atomic_xor_i16 symbol")
                    .into_inner()
            };

            let mut cell64 = 11_i64;
            assert_eq!(proof_atomic_add_i64(&mut cell64, 5), 11);
            assert_eq!(cell64, 16);

            let mut bytes = [7_u8, 0xAA];
            assert_eq!(proof_atomic_xchg_i8(&mut bytes[0], 9), 7);
            assert_eq!(bytes, [9, 0xAA]);

            let mut words = [0xFFF0_u16, 0xBEEF];
            assert_eq!(proof_atomic_xor_i16(&mut words[0], 0x00FF), 0xFFF0);
            assert_eq!(words, [0xFF0F, 0xBEEF]);

            let proofs = result
                .proofs
                .as_ref()
                .expect("emit_proofs=true should attach x86 proof reports");
            assert!(
                proofs.iter().any(|proof| proof.verified),
                "atomic RMW proof module should emit verified x86-64 proof reports"
            );

            assert_atomic_rmw_query_verified(
                proofs,
                X86Opcode::AtomicRmwCasLoop,
                "AtomicRmwCasLoop_Add_I64",
            );
            assert_atomic_rmw_query_verified(
                proofs,
                X86Opcode::AtomicRmwCasLoop8,
                "AtomicRmwCasLoop8_Xchg_I8",
            );
            assert_atomic_rmw_query_verified(
                proofs,
                X86Opcode::AtomicRmwCasLoop16,
                "AtomicRmwCasLoop16_Xor_I16",
            );
        })
        .expect("failed to spawn x86 atomic RMW proof test thread");
    child
        .join()
        .expect("x86 atomic RMW proof test thread panicked");
}

#[cfg(all(target_os = "windows", feature = "verify"))]
#[test]
fn x86_64_windows_jit_emit_proofs_tracks_atomic_load_store_fence_proofs() {
    let child = std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            use trust_cg_ir::x86_64_ops::X86Opcode;

            let module = windows_atomic_load_store_fence_module();
            let mut config = CompilerConfig::for_host_jit();
            config.emit_proofs = true;
            config.opt_level = OptLevel::O0;
            config.parallel = false;

            let result = Compiler::new(config)
                .compile_module_to_jit(&module, &HashMap::new())
                .expect("Windows x86-64 JIT should compile atomic load/store/fence with emit_proofs=true");

            let atomic_load_i64: extern "C" fn(*mut i64) -> i64 = unsafe {
                result
                    .buffer
                    .get_fn_bound("atomic_load_i64")
                    .expect("atomic_load_i64 symbol")
                    .into_inner()
            };
            let atomic_store_load_i64: extern "C" fn(*mut i64, i64) -> i64 = unsafe {
                result
                    .buffer
                    .get_fn_bound("atomic_store_load_i64")
                    .expect("atomic_store_load_i64 symbol")
                    .into_inner()
            };
            let atomic_store_load_i8: extern "C" fn(*mut u8, i64) -> i64 = unsafe {
                result
                    .buffer
                    .get_fn_bound("atomic_store_load_i8_zext")
                    .expect("atomic_store_load_i8_zext symbol")
                    .into_inner()
            };
            let atomic_store_load_i16: extern "C" fn(*mut u16, i64) -> i64 = unsafe {
                result
                    .buffer
                    .get_fn_bound("atomic_store_load_i16_zext")
                    .expect("atomic_store_load_i16_zext symbol")
                    .into_inner()
            };
            let atomic_store_load_i32: extern "C" fn(*mut u32, i64) -> i64 = unsafe {
                result
                    .buffer
                    .get_fn_bound("atomic_store_load_i32_zext")
                    .expect("atomic_store_load_i32_zext symbol")
                    .into_inner()
            };
            let atomic_fence_store_load_i64: extern "C" fn(*mut i64, i64) -> i64 = unsafe {
                result
                    .buffer
                    .get_fn_bound("atomic_fence_store_load_i64")
                    .expect("atomic_fence_store_load_i64 symbol")
                    .into_inner()
            };
            let atomic_fence_acquire_load_i64: extern "C" fn(*mut i64) -> i64 = unsafe {
                result
                    .buffer
                    .get_fn_bound("atomic_fence_acquire_load_i64")
                    .expect("atomic_fence_acquire_load_i64 symbol")
                    .into_inner()
            };
            let atomic_fence_release_load_i64: extern "C" fn(*mut i64) -> i64 = unsafe {
                result
                    .buffer
                    .get_fn_bound("atomic_fence_release_load_i64")
                    .expect("atomic_fence_release_load_i64 symbol")
                    .into_inner()
            };
            let atomic_fence_acqrel_load_i64: extern "C" fn(*mut i64) -> i64 = unsafe {
                result
                    .buffer
                    .get_fn_bound("atomic_fence_acqrel_load_i64")
                    .expect("atomic_fence_acqrel_load_i64 symbol")
                    .into_inner()
            };

            let mut cell = 11_i64;
            assert_eq!(atomic_load_i64(&mut cell), 11);
            assert_eq!(atomic_store_load_i64(&mut cell, -12345), -12345);
            assert_eq!(cell, -12345);

            let mut bytes = [0xAA_u8, 0x11, 0xBB];
            let byte_ptr = unsafe { bytes.as_mut_ptr().add(1) };
            assert_eq!(atomic_store_load_i8(byte_ptr, 0x1ff), 0xff);
            assert_eq!(bytes, [0xAA, 0xFF, 0xBB]);

            let mut words = [0xAAAA_u16, 0x1111, 0xBBBB];
            assert_eq!(atomic_store_load_i16(&mut words[1], 0x1_2345), 0x2345);
            assert_eq!(words, [0xAAAA, 0x2345, 0xBBBB]);

            let mut dwords = [0xAAAA_AAAA_u32, 0x1111_1111, 0xBBBB_BBBB];
            assert_eq!(
                atomic_store_load_i32(&mut dwords[1], 0x1_2345_6789),
                0x2345_6789
            );
            assert_eq!(dwords, [0xAAAA_AAAA, 0x2345_6789, 0xBBBB_BBBB]);

            let mut fence_cell = 5_i64;
            assert_eq!(atomic_fence_store_load_i64(&mut fence_cell, 41), 41);
            assert_eq!(fence_cell, 41);
            assert_eq!(atomic_fence_acquire_load_i64(&mut fence_cell), 41);
            assert_eq!(atomic_fence_release_load_i64(&mut fence_cell), 41);
            assert_eq!(atomic_fence_acqrel_load_i64(&mut fence_cell), 41);

            let proofs = result
                .proofs
                .as_ref()
                .expect("emit_proofs=true should attach x86 proof reports");
            assert!(
                proofs.iter().any(|proof| proof.verified),
                "atomic load/store/fence module should emit verified x86-64 proof reports"
            );

            for (opcode, query) in [
                (X86Opcode::MovRM8, "AtomicLoad_I8"),
                (X86Opcode::MovRM16, "AtomicLoad_I16"),
                (X86Opcode::MovRM32, "AtomicLoad_I32"),
                (X86Opcode::MovRM, "AtomicLoad_I64"),
                (X86Opcode::MovMR8, "AtomicStore_I8"),
                (X86Opcode::MovMR16, "AtomicStore_I16"),
                (X86Opcode::MovMR32, "AtomicStore_I32"),
                (X86Opcode::MovMR, "AtomicStore_I64"),
                (X86Opcode::Mfence, "Fence_Acquire"),
                (X86Opcode::Mfence, "Fence_Release"),
                (X86Opcode::Mfence, "Fence_AcqRel"),
                (X86Opcode::Mfence, "Fence_SeqCst"),
            ] {
                assert_atomic_memory_query_verified(proofs, opcode, query);
            }

            for (function, rule_name) in [
                ("atomic_load_i64", "x86_64: AtomicLoad_I64 -> MOV r,[mem]"),
                (
                    "atomic_store_load_i64",
                    "x86_64: AtomicStore_I64 -> MOV [mem],r",
                ),
                (
                    "atomic_store_load_i64",
                    "x86_64: AtomicLoad_I64 -> MOV r,[mem]",
                ),
                (
                    "atomic_store_load_i8_zext",
                    "x86_64: AtomicStore_I8 -> MOV [mem],r",
                ),
                (
                    "atomic_store_load_i8_zext",
                    "x86_64: AtomicLoad_I8 -> MOV r,[mem]",
                ),
                (
                    "atomic_store_load_i16_zext",
                    "x86_64: AtomicStore_I16 -> MOV [mem],r",
                ),
                (
                    "atomic_store_load_i16_zext",
                    "x86_64: AtomicLoad_I16 -> MOV r,[mem]",
                ),
                (
                    "atomic_store_load_i32_zext",
                    "x86_64: AtomicStore_I32 -> MOV [mem],r",
                ),
                (
                    "atomic_store_load_i32_zext",
                    "x86_64: AtomicLoad_I32 -> MOV r,[mem]",
                ),
                (
                    "atomic_fence_store_load_i64",
                    "x86_64: AtomicStore_I64 -> MOV [mem],r",
                ),
                (
                    "atomic_fence_store_load_i64",
                    "x86_64: Fence_SeqCst -> MFENCE",
                ),
                (
                    "atomic_fence_acquire_load_i64",
                    "x86_64: Fence_Acquire -> MFENCE",
                ),
                (
                    "atomic_fence_release_load_i64",
                    "x86_64: Fence_Release -> MFENCE",
                ),
                (
                    "atomic_fence_acqrel_load_i64",
                    "x86_64: Fence_AcqRel -> MFENCE",
                ),
                (
                    "atomic_fence_store_load_i64",
                    "x86_64: AtomicLoad_I64 -> MOV r,[mem]",
                ),
            ] {
                assert_verified_rule_for_function(proofs, function, rule_name);
            }
        })
        .expect("failed to spawn x86 atomic load/store/fence proof test thread");
    child
        .join()
        .expect("x86 atomic load/store/fence proof test thread panicked");
}

#[cfg(target_os = "windows")]
fn windows_typed_trust_ir_bitfield_i64_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("x86_64_windows_typed_trust_ir_bitfield_i64");

    {
        let ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("trust_ir_extract_mid16_i64", ty);
        let entry = fb.create_block();
        let value = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let result = fb.trust_cg_extract_bits(Ty::I64, value, 8, 16);
        fb.ret(vec![result]);
        fb.build();
    }

    {
        let ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("trust_ir_sextract_mid12_i64", ty);
        let entry = fb.create_block();
        let value = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let result = fb.trust_cg_sextract_bits(Ty::I64, value, 4, 12);
        fb.ret(vec![result]);
        fb.build();
    }

    {
        let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("trust_ir_insert_mid12_i64", ty);
        let entry = fb.create_block();
        let dst = fb.add_block_param(entry, Ty::I64);
        let src = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let result = fb.trust_cg_insert_bits(Ty::I64, dst, src, 16, 12);
        fb.ret(vec![result]);
        fb.build();
    }

    {
        let ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("trust_ir_insert_mid12_i64_alias", ty);
        let entry = fb.create_block();
        let value = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let result = fb.trust_cg_insert_bits(Ty::I64, value, value, 16, 12);
        fb.ret(vec![result]);
        fb.build();
    }

    mb.build()
}

#[cfg(all(target_os = "windows", feature = "verify"))]
fn assert_scalar_bitfield_component_proof_status(
    proofs: &[trust_cg_codegen::compiler::ProofCertificate],
) {
    use trust_cg_ir::x86_64_ops::X86Opcode;

    for (opcode, label) in [
        (X86Opcode::ShrRI, "unsigned extract shift"),
        (X86Opcode::SarRI, "signed extract shift"),
        (X86Opcode::ShlRI, "insert/sign-position shift"),
        (X86Opcode::AndRR, "bitfield mask"),
        (X86Opcode::OrRR, "bitfield merge"),
    ] {
        let query = trust_cg_verify::X86FunctionVerifier::opcode_to_proof_query(opcode)
            .unwrap_or_else(|| panic!("{opcode:?} must map to an x86-64 proof query"));
        assert!(
            !has_unverified_mapping_gap(proofs, opcode),
            "{label} ({opcode:?}) should have an x86-64 verifier query; proofs: {proofs:#?}"
        );
        assert!(
            !has_unverified_query_gap(proofs, query),
            "{label} ({opcode:?}) should have a registered proof for query {query}; proofs: {proofs:#?}"
        );
        assert!(
            has_verified_query(proofs, query),
            "{label} ({opcode:?}) must emit a verified scalar bitfield component proof for query {query}; proofs: {proofs:#?}"
        );
    }
}

#[cfg(all(target_os = "windows", feature = "verify"))]
#[test]
fn x86_64_windows_jit_emit_proofs_tracks_scalar_bitfield_lowering_components() {
    let child = std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let module = windows_typed_trust_ir_bitfield_i64_module();
            let mut config = CompilerConfig::for_host_jit();
            config.emit_proofs = true;
            config.opt_level = OptLevel::O0;
            config.parallel = false;

            let result = Compiler::new(config)
                .compile_module_to_jit(&module, &HashMap::new())
                .expect("Windows x86-64 JIT should compile bitfield ops with emit_proofs=true");
            let proofs = result
                .proofs
                .as_ref()
                .expect("emit_proofs=true should attach x86 bitfield proof reports");
            assert!(
                proofs.iter().any(|proof| proof.verified),
                "bitfield proof module should emit verified x86-64 proof reports"
            );

            assert_scalar_bitfield_component_proof_status(proofs);
        })
        .expect("failed to spawn x86 bitfield proof test thread");
    child
        .join()
        .expect("x86 bitfield proof test thread panicked");
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_executes_typed_trust_ir_bitfield_i64_ops() {
    let module = windows_typed_trust_ir_bitfield_i64_module();
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 typed trust_ir JIT should compile i64 bitfield ops");
    let extract: extern "C" fn(i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("trust_ir_extract_mid16_i64")
            .expect("trust_ir_extract_mid16_i64 symbol")
            .into_inner()
    };
    let sextract: extern "C" fn(i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("trust_ir_sextract_mid12_i64")
            .expect("trust_ir_sextract_mid12_i64 symbol")
            .into_inner()
    };
    let insert: extern "C" fn(i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("trust_ir_insert_mid12_i64")
            .expect("trust_ir_insert_mid12_i64 symbol")
            .into_inner()
    };
    let insert_alias: extern "C" fn(i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("trust_ir_insert_mid12_i64_alias")
            .expect("trust_ir_insert_mid12_i64_alias symbol")
            .into_inner()
    };

    assert_eq!(extract(0x1234_5678_9abc_def0), 0xbcde);
    assert_eq!(extract(-1), 0xffff);
    assert_eq!(extract(0xff), 0);
    assert_eq!(sextract(0x8000), -2048);
    assert_eq!(sextract(0x7ff0), 2047);
    assert_eq!(sextract(0xfab0), -85);
    assert_eq!(insert(0x1234_5678_9abc_def0, 0xfed), 0x1234_5678_9fed_def0);
    assert_eq!(insert(-1, 0), 0xffff_ffff_f000_ffff_u64 as i64);
    assert_eq!(insert(0, -1), 0x0000_0000_0fff_0000);
    assert_eq!(insert_alias(0x1234_5678_9abc_def0), 0x1234_5678_9ef0_def0);
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_rejects_typed_trust_ir_bitfield_bad_range() {
    let mut mb = ModuleBuilder::new("x86_64_windows_typed_trust_ir_bad_bitfield");
    let ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("bad_extract", ty);
    let entry = fb.create_block();
    let value = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let result = fb.trust_cg_extract_bits(Ty::I64, value, 63, 2);
    fb.ret(vec![result]);
    fb.build();

    let module = mb.build();
    let err = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect_err("bad bitfield range should fail before JIT publication");
    assert!(
        matches!(err, CompileError::DialectPipeline(_))
            && err.to_string().contains("invalid bitfield range"),
        "unexpected bad range diagnostic: {err:?}"
    );
}

#[cfg(target_os = "windows")]
fn windows_i64_switch_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("x86_64_windows_i64_switch");
    let ty = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "switch_i64_cases", ty, BlockId::new(0));
    let mut blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![InstrNode::new(Inst::Switch {
            value: ValueId::new(0),
            default: BlockId::new(4),
            default_args: vec![],
            cases: vec![
                SwitchCase {
                    value: Constant::Int(-3),
                    target: BlockId::new(1),
                    args: vec![],
                    exhaustive_enum_unreachable: false,
                },
                SwitchCase {
                    value: Constant::Int(0),
                    target: BlockId::new(2),
                    args: vec![],
                },
                SwitchCase {
                    value: Constant::Int(7),
                    target: BlockId::new(3),
                    args: vec![],
                },
            ],
        })],
    }];

    for (block, result, value) in [
        (1_u32, 10_u32, -30_i128),
        (2_u32, 20_u32, 11_i128),
        (3_u32, 30_u32, 70_i128),
        (4_u32, 40_u32, 99_i128),
    ] {
        blocks.push(TrustIrBlock {
            id: BlockId::new(block),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(value),
                })
                .with_result(ValueId::new(result)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(result)],
                }),
            ],
        });
    }

    func.blocks = blocks;
    module.add_function(func);
    module
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_executes_i64_switch_cases() {
    let module = windows_i64_switch_module();
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile i64 switch cases");

    let switch_i64_cases: extern "C" fn(i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("switch_i64_cases")
            .expect("switch_i64_cases symbol")
            .into_inner()
    };

    for (selector, expected) in [
        (-3_i64, -30_i64),
        (0_i64, 11_i64),
        (7_i64, 70_i64),
        (-4_i64, 99_i64),
        (1_i64, 99_i64),
        (i64::MAX, 99_i64),
    ] {
        assert_eq!(
            switch_i64_cases(selector),
            expected,
            "switch result mismatch for selector {selector}"
        );
    }
}

#[cfg(target_os = "windows")]
fn windows_global_ref_indirect_call_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("x86_64_windows_global_ref_indirect_call");
    let callee_ty = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let entry_ty = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let mut target = TrustIrFunction::new(
        FuncId::new(0),
        "global_ref_target",
        callee_ty,
        BlockId::new(0),
    );
    target.blocks.push(TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(77),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ],
    });

    let mut entry = TrustIrFunction::new(
        FuncId::new(1),
        "global_ref_entry",
        entry_ty,
        BlockId::new(0),
    );
    entry.blocks.push(TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Func(callee_ty),
                value: Constant::Closure {
                    func: FuncId::new(0),
                    captures: vec![],
                },
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(0),
                sig: callee_ty,
                args: vec![],
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    });

    module.add_function(target);
    module.add_function(entry);
    module
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_materializes_in_module_global_ref_for_indirect_call() {
    let module = windows_global_ref_indirect_call_module();
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should patch in-module GlobalRef LEA fixups");

    let global_ref_entry: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("global_ref_entry")
            .expect("global_ref_entry symbol")
            .into_inner()
    };
    assert_eq!(global_ref_entry(), 77);
}

#[cfg(target_os = "windows")]
extern "C" fn host_extern_ref_add7(value: i64) -> i64 {
    value + 7
}

#[cfg(target_os = "windows")]
fn windows_extern_ref_indirect_call_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("x86_64_windows_extern_ref_indirect_call");
    let callback_ty = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let entry_ty = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    module.add_function(TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "host_extern_ref_add7".to_string(),
        ty: callback_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    });

    let mut entry = TrustIrFunction::new(
        FuncId::new(1),
        "extern_ref_entry",
        entry_ty,
        BlockId::new(0),
    );
    entry.blocks.push(TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::Func(callback_ty),
                value: Constant::FnDef(FuncId::new(0)),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(35),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::CallIndirect {
                callee: ValueId::new(0),
                sig: callback_ty,
                args: vec![ValueId::new(1)],
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    });

    module.add_function(entry);
    module
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_materializes_extern_ref_for_indirect_call() {
    let module = windows_extern_ref_indirect_call_module();
    let extern_symbols = HashMap::from([(
        "host_extern_ref_add7".to_string(),
        host_extern_ref_add7 as *const () as *const u8,
    )]);
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &extern_symbols)
        .expect("Windows x86-64 JIT should patch ExternRef pointer slots");

    let extern_ref_entry: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("extern_ref_entry")
            .expect("extern_ref_entry symbol")
            .into_inner()
    };
    assert_eq!(extern_ref_entry(), 42);
}

#[cfg(target_os = "windows")]
extern "C" fn host_windows_indirect_weighted_sum6(
    a: i64,
    b: i64,
    c: i64,
    d: i64,
    e: i64,
    f: i64,
) -> i64 {
    a + 10 * b + 100 * c + 1_000 * d + 10_000 * e + 100_000 * f
}

#[cfg(target_os = "windows")]
fn windows_indirect_six_i64_call_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_windows_indirect_call_six_i64");
    let callback_ty = mb.add_func_type(vec![Ty::I64; 6], vec![Ty::I64]);
    let mut entry_params = vec![Ty::Func(callback_ty)];
    entry_params.extend(vec![Ty::I64; 6]);
    let entry_ty = mb.add_func_type(entry_params, vec![Ty::I64]);

    let mut fb = mb.function("indirect_sum6_entry", entry_ty);
    let entry = fb.create_block();
    let callee = fb.add_block_param(entry, Ty::Func(callback_ty));
    let args: Vec<_> = (0..6).map(|_| fb.add_block_param(entry, Ty::I64)).collect();
    fb.switch_to_block(entry);
    let result = fb.call_indirect(callee, callback_ty, args);
    fb.ret(vec![result]);
    fb.build();
    mb.build()
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_executes_indirect_call_with_overflow_integer_args() {
    let module = windows_indirect_six_i64_call_module();
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile indirect six-i64 call");

    let indirect_sum6_entry: extern "C" fn(*const c_void, i64, i64, i64, i64, i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("indirect_sum6_entry")
            .expect("indirect_sum6_entry symbol")
            .into_inner()
    };
    let callback = host_windows_indirect_weighted_sum6 as *const () as *const c_void;

    assert_eq!(indirect_sum6_entry(callback, 1, 2, 3, 4, 5, 6), 654_321);
    assert_eq!(indirect_sum6_entry(callback, -3, 4, -5, 6, -7, 8), 735_537);
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_rejects_requested_foreign_target_specs() {
    let module = ModuleBuilder::new("x86_64_windows_foreign_jit_target_spec").build();
    let host_spec = TargetSpec::parse("x86_64-pc-windows-msvc").unwrap();

    for triple in ["x86_64-unknown-linux-gnu", "x86_64-apple-darwin"] {
        let requested = TargetSpec::parse(triple).unwrap();
        let compiler = Compiler::new_for_target_spec(CompilerConfig::for_host_jit(), requested);
        let err = compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_err();

        match err {
            CompileError::JitTargetSpecMismatch {
                requested: actual,
                host,
            } => {
                assert_eq!(actual, requested);
                assert_eq!(host, host_spec);
            }
            other => panic!("expected JitTargetSpecMismatch for {triple}, got {other:?}"),
        }
    }
}

#[test]
fn x86_64_jit_call_counts_profile_hook_counts_entries() {
    let mut mb = ModuleBuilder::new("x86_64_host_jit_profile");
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("profiled_answer", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let answer = fb.iconst(Ty::I64, 42);
    fb.ret(vec![answer]);
    fb.build();

    let module = mb.build();
    let result = Compiler::for_host()
        .compile_module_to_jit_with_profile_hooks(
            &module,
            &HashMap::new(),
            ProfileHookMode::CallCounts,
        )
        .expect("x86-64 host JIT should support function-entry counters");

    let profiled_answer: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("profiled_answer")
            .expect("profiled_answer symbol")
            .into_inner()
    };

    assert_eq!(profiled_answer(), 42);
    assert_eq!(profiled_answer(), 42);
    assert_eq!(profiled_answer(), 42);
    assert_eq!(result.buffer.entry_count("profiled_answer"), Some(3));
    assert_eq!(
        result
            .buffer
            .get_profile("profiled_answer")
            .expect("profile should exist")
            .call_count,
        3
    );
}

#[test]
fn x86_64_jit_mixed_int_float_host_abi_direct_and_internal_call() {
    let mut mb = ModuleBuilder::new("x86_64_host_jit_mixed_abi");
    let mixed_ty = mb.add_func_type(vec![Ty::I64, Ty::F64, Ty::I64, Ty::F64], vec![Ty::F64]);

    {
        let mut fb = mb.function("mixed_direct", mixed_ty);
        let entry = fb.create_block();
        let i0 = fb.add_block_param(entry, Ty::I64);
        let f0 = fb.add_block_param(entry, Ty::F64);
        let i1 = fb.add_block_param(entry, Ty::I64);
        let f1 = fb.add_block_param(entry, Ty::F64);
        fb.switch_to_block(entry);

        let i0f = fb.cast(CastOp::SIToFP, Ty::I64, Ty::F64, i0);
        let i1f = fb.cast(CastOp::SIToFP, Ty::I64, Ty::F64, i1);
        let ten = fb.fconst(Ty::F64, 10.0);
        let hundred = fb.fconst(Ty::F64, 100.0);
        let thousand = fb.fconst(Ty::F64, 1000.0);
        let weighted_f0 = fb.fmul(Ty::F64, f0, ten);
        let weighted_i1 = fb.fmul(Ty::F64, i1f, hundred);
        let weighted_f1 = fb.fmul(Ty::F64, f1, thousand);
        let lhs = fb.fadd(Ty::F64, i0f, weighted_f0);
        let rhs = fb.fadd(Ty::F64, weighted_i1, weighted_f1);
        let result = fb.fadd(Ty::F64, lhs, rhs);
        fb.ret(vec![result]);
        fb.build();
    }

    {
        let mut fb = mb.function("mixed_call", mixed_ty);
        let entry = fb.create_block();
        let i0 = fb.add_block_param(entry, Ty::I64);
        let f0 = fb.add_block_param(entry, Ty::F64);
        let i1 = fb.add_block_param(entry, Ty::I64);
        let f1 = fb.add_block_param(entry, Ty::F64);
        fb.switch_to_block(entry);

        let called = fb.call(FuncId::new(0), vec![i0, f0, i1, f1]);
        let half = fb.fconst(Ty::F64, 0.5);
        let result = fb.fadd(Ty::F64, called, half);
        fb.ret(vec![result]);
        fb.build();
    }

    let module = mb.build();
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("x86-64 host JIT should compile mixed integer/float ABI module");

    assert_eq!(result.buffer.symbol_count(), 2);

    let mixed_direct: extern "C" fn(i64, f64, i64, f64) -> f64 = unsafe {
        result
            .buffer
            .get_fn_bound("mixed_direct")
            .expect("mixed_direct symbol")
            .into_inner()
    };
    let mixed_call: extern "C" fn(i64, f64, i64, f64) -> f64 = unsafe {
        result
            .buffer
            .get_fn_bound("mixed_call")
            .expect("mixed_call symbol")
            .into_inner()
    };

    assert_eq!(mixed_direct(1, 2.0, 3, 4.0), 4321.0);
    assert_eq!(mixed_direct(-7, 1.25, 9, -0.5), 405.5);
    assert_eq!(mixed_call(1, 2.0, 3, 4.0), 4321.5);
    assert_eq!(mixed_call(-7, 1.25, 9, -0.5), 406.0);
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_mixed_int_float_stack_args_direct_and_internal_call() {
    let mut mb = ModuleBuilder::new("x86_64_windows_mixed_stack_abi");
    let mixed_ty = mb.add_func_type(
        vec![
            Ty::I64,
            Ty::F64,
            Ty::I64,
            Ty::F64,
            Ty::I64,
            Ty::F64,
            Ty::I64,
            Ty::F64,
        ],
        vec![Ty::I64],
    );

    {
        let mut fb = mb.function("mixed_stack_direct", mixed_ty);
        let entry = fb.create_block();
        let i0 = fb.add_block_param(entry, Ty::I64);
        let f0 = fb.add_block_param(entry, Ty::F64);
        let i1 = fb.add_block_param(entry, Ty::I64);
        let f1 = fb.add_block_param(entry, Ty::F64);
        let i2 = fb.add_block_param(entry, Ty::I64);
        let f2 = fb.add_block_param(entry, Ty::F64);
        let i3 = fb.add_block_param(entry, Ty::I64);
        let f3 = fb.add_block_param(entry, Ty::F64);
        fb.switch_to_block(entry);

        let f0i = fb.cast(CastOp::FPToSI, Ty::F64, Ty::I64, f0);
        let f1i = fb.cast(CastOp::FPToSI, Ty::F64, Ty::I64, f1);
        let f2i = fb.cast(CastOp::FPToSI, Ty::F64, Ty::I64, f2);
        let f3i = fb.cast(CastOp::FPToSI, Ty::F64, Ty::I64, f3);
        let w10 = fb.iconst(Ty::I64, 10);
        let w100 = fb.iconst(Ty::I64, 100);
        let w1000 = fb.iconst(Ty::I64, 1000);
        let w10000 = fb.iconst(Ty::I64, 10_000);
        let w100000 = fb.iconst(Ty::I64, 100_000);
        let w1000000 = fb.iconst(Ty::I64, 1_000_000);
        let w10000000 = fb.iconst(Ty::I64, 10_000_000);
        let f0w = fb.mul(Ty::I64, f0i, w10);
        let i1w = fb.mul(Ty::I64, i1, w100);
        let f1w = fb.mul(Ty::I64, f1i, w1000);
        let i2w = fb.mul(Ty::I64, i2, w10000);
        let f2w = fb.mul(Ty::I64, f2i, w100000);
        let i3w = fb.mul(Ty::I64, i3, w1000000);
        let f3w = fb.mul(Ty::I64, f3i, w10000000);
        let mut sum = fb.add(Ty::I64, i0, f0w);
        sum = fb.add(Ty::I64, sum, i1w);
        sum = fb.add(Ty::I64, sum, f1w);
        sum = fb.add(Ty::I64, sum, i2w);
        sum = fb.add(Ty::I64, sum, f2w);
        sum = fb.add(Ty::I64, sum, i3w);
        sum = fb.add(Ty::I64, sum, f3w);
        fb.ret(vec![sum]);
        fb.build();
    }

    {
        let mut fb = mb.function("mixed_stack_call", mixed_ty);
        let entry = fb.create_block();
        let args: Vec<_> = (0..8)
            .map(|idx| fb.add_block_param(entry, if idx % 2 == 0 { Ty::I64 } else { Ty::F64 }))
            .collect();
        fb.switch_to_block(entry);
        let called = fb.call(FuncId::new(0), args);
        let bias = fb.iconst(Ty::I64, 11);
        let result = fb.add(Ty::I64, called, bias);
        fb.ret(vec![result]);
        fb.build();
    }

    let module = mb.build();
    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = OptLevel::O0;
    let result = Compiler::new(config)
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile mixed integer/FP stack-arg ABI module");

    let mixed_stack_direct: extern "C" fn(i64, f64, i64, f64, i64, f64, i64, f64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("mixed_stack_direct")
            .expect("mixed_stack_direct symbol")
            .into_inner()
    };
    let mixed_stack_call: extern "C" fn(i64, f64, i64, f64, i64, f64, i64, f64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("mixed_stack_call")
            .expect("mixed_stack_call symbol")
            .into_inner()
    };

    assert_eq!(
        mixed_stack_direct(1, 2.0, 3, 4.0, 5, 6.0, 7, 8.0),
        87_654_321
    );
    assert_eq!(mixed_stack_call(1, 2.0, 3, 4.0, 5, 6.0, 7, 8.0), 87_654_332);
    assert_eq!(
        mixed_stack_direct(-1, -2.0, 3, -4.0, 5, -6.0, 7, -8.0),
        -73_553_721
    );
    assert_eq!(
        mixed_stack_call(-1, -2.0, 3, -4.0, 5, -6.0, 7, -8.0),
        -73_553_710
    );
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_unsigned_float_conversion_edges() {
    let mut mb = ModuleBuilder::new("x86_64_windows_unsigned_float_conversions");
    let u32_to_f64_ty = mb.add_func_type(vec![Ty::U32], vec![Ty::F64]);
    let u64_to_f64_ty = mb.add_func_type(vec![Ty::U64], vec![Ty::F64]);
    let u64_to_f32_ty = mb.add_func_type(vec![Ty::U64], vec![Ty::F32]);
    let f64_to_u32_ty = mb.add_func_type(vec![Ty::F64], vec![Ty::U32]);
    let f32_to_u32_ty = mb.add_func_type(vec![Ty::F32], vec![Ty::U32]);
    let f64_to_u64_ty = mb.add_func_type(vec![Ty::F64], vec![Ty::U64]);

    {
        let mut fb = mb.function("u32_to_f64", u32_to_f64_ty);
        let entry = fb.create_block();
        let value = fb.add_block_param(entry, Ty::U32);
        fb.switch_to_block(entry);
        let result = fb.cast(CastOp::UIToFP, Ty::U32, Ty::F64, value);
        fb.ret(vec![result]);
        fb.build();
    }
    {
        let mut fb = mb.function("u64_to_f64", u64_to_f64_ty);
        let entry = fb.create_block();
        let value = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let result = fb.cast(CastOp::UIToFP, Ty::U64, Ty::F64, value);
        fb.ret(vec![result]);
        fb.build();
    }
    {
        let mut fb = mb.function("u64_to_f32", u64_to_f32_ty);
        let entry = fb.create_block();
        let value = fb.add_block_param(entry, Ty::U64);
        fb.switch_to_block(entry);
        let result = fb.cast(CastOp::UIToFP, Ty::U64, Ty::F32, value);
        fb.ret(vec![result]);
        fb.build();
    }
    {
        let mut fb = mb.function("f64_to_u32", f64_to_u32_ty);
        let entry = fb.create_block();
        let value = fb.add_block_param(entry, Ty::F64);
        fb.switch_to_block(entry);
        let result = fb.cast(CastOp::FPToUI, Ty::F64, Ty::U32, value);
        fb.ret(vec![result]);
        fb.build();
    }
    {
        let mut fb = mb.function("f32_to_u32", f32_to_u32_ty);
        let entry = fb.create_block();
        let value = fb.add_block_param(entry, Ty::F32);
        fb.switch_to_block(entry);
        let result = fb.cast(CastOp::FPToUI, Ty::F32, Ty::U32, value);
        fb.ret(vec![result]);
        fb.build();
    }
    {
        let mut fb = mb.function("f64_to_u64", f64_to_u64_ty);
        let entry = fb.create_block();
        let value = fb.add_block_param(entry, Ty::F64);
        fb.switch_to_block(entry);
        let result = fb.cast(CastOp::FPToUI, Ty::F64, Ty::U64, value);
        fb.ret(vec![result]);
        fb.build();
    }

    let module = mb.build();
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile unsigned FP conversion edges");

    let u32_to_f64: extern "C" fn(u32) -> f64 = unsafe {
        result
            .buffer
            .get_fn_bound("u32_to_f64")
            .expect("u32_to_f64 symbol")
            .into_inner()
    };
    let u64_to_f64: extern "C" fn(u64) -> f64 = unsafe {
        result
            .buffer
            .get_fn_bound("u64_to_f64")
            .expect("u64_to_f64 symbol")
            .into_inner()
    };
    let u64_to_f32: extern "C" fn(u64) -> f32 = unsafe {
        result
            .buffer
            .get_fn_bound("u64_to_f32")
            .expect("u64_to_f32 symbol")
            .into_inner()
    };
    let f64_to_u32: extern "C" fn(f64) -> u32 = unsafe {
        result
            .buffer
            .get_fn_bound("f64_to_u32")
            .expect("f64_to_u32 symbol")
            .into_inner()
    };
    let f32_to_u32: extern "C" fn(f32) -> u32 = unsafe {
        result
            .buffer
            .get_fn_bound("f32_to_u32")
            .expect("f32_to_u32 symbol")
            .into_inner()
    };
    let f64_to_u64: extern "C" fn(f64) -> u64 = unsafe {
        result
            .buffer
            .get_fn_bound("f64_to_u64")
            .expect("f64_to_u64 symbol")
            .into_inner()
    };

    for symbol in ["f64_to_u32", "f32_to_u32", "f64_to_u64"] {
        let (bytes, _, _) = windows_jit_symbol_bytes(&result.buffer, symbol);
        assert!(
            bytes.windows(2).any(|window| window == [0x0F, 0x0B]),
            "{symbol} should contain a UD2 trap route for invalid FPToUI inputs; bytes: {bytes:02x?}"
        );
    }

    assert_eq!(u32_to_f64(2_147_483_647).to_bits(), 0x41dfffffffc00000);
    assert_eq!(u32_to_f64(2_147_483_648).to_bits(), 0x41e0000000000000);
    assert_eq!(u32_to_f64(2_147_483_649).to_bits(), 0x41e0000000200000);
    assert_eq!(u32_to_f64(u32::MAX).to_bits(), 0x41efffffffe00000);

    assert_eq!(u64_to_f64(u64::MAX / 2).to_bits(), 0x43e0000000000000);
    assert_eq!(u64_to_f64(1_u64 << 63).to_bits(), 0x43e0000000000000);
    assert_eq!(
        u64_to_f64((1_u64 << 63) + 2048).to_bits(),
        0x43e0000000000001
    );
    assert_eq!(u64_to_f64(u64::MAX).to_bits(), 0x43f0000000000000);

    assert_eq!(u64_to_f32(1_u64 << 63).to_bits(), 0x5f000000);
    assert_eq!(u64_to_f32(u64::MAX).to_bits(), 0x5f800000);

    assert_eq!(f64_to_u32(2_147_483_647.0), 2_147_483_647);
    assert_eq!(f64_to_u32(2_147_483_647.75), 2_147_483_647);
    assert_eq!(f64_to_u32(2_147_483_648.0), 2_147_483_648);
    assert_eq!(f64_to_u32(2_147_483_649.0), 2_147_483_649);
    assert_eq!(f64_to_u32(u32::MAX as f64), u32::MAX);

    assert_eq!(f32_to_u32(1.75), 1);
    assert_eq!(f32_to_u32(f32::from_bits(0x4effffff)), 2_147_483_520);
    assert_eq!(f32_to_u32(f32::from_bits(0x4f000000)), 2_147_483_648);
    assert_eq!(f32_to_u32(f32::from_bits(0x4f7fffff)), 4_294_967_040);

    assert_eq!(f64_to_u64(42.75), 42);
    assert_eq!(
        f64_to_u64(f64::from_bits(0x43dfffffffffffff)),
        9_223_372_036_854_774_784
    );
    assert_eq!(f64_to_u64(f64::from_bits(0x43e0000000000000)), 1_u64 << 63);
    assert_eq!(
        f64_to_u64(f64::from_bits(0x43e0000000000001)),
        9_223_372_036_854_777_856
    );
    assert_eq!(
        f64_to_u64(f64::from_bits(0x43efffffffffffff)),
        18_446_744_073_709_549_568
    );
}

#[test]
fn x86_64_jit_store_then_reload_through_host_pointer() {
    let mut mb = ModuleBuilder::new("x86_64_host_jit_memory");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::I64, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("store_sum_and_return_delta", ty);
    let entry = fb.create_block();
    let ptr = fb.add_block_param(entry, Ty::Ptr);
    let lhs = fb.add_block_param(entry, Ty::I64);
    let rhs = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);

    let old = fb.load(Ty::I64, ptr);
    let sum = fb.add(Ty::I64, lhs, rhs);
    fb.store(Ty::I64, ptr, sum);
    let reloaded = fb.load(Ty::I64, ptr);
    let result = fb.sub(Ty::I64, reloaded, old);
    fb.ret(vec![result]);
    fb.build();

    let module = mb.build();
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("x86-64 host JIT should compile pointer load/store module");

    let store_sum_and_return_delta: extern "C" fn(*mut i64, i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("store_sum_and_return_delta")
            .expect("store_sum_and_return_delta symbol")
            .into_inner()
    };

    let mut slot = 5_i64;
    assert_eq!(store_sum_and_return_delta(&mut slot, 20, 22), 37);
    assert_eq!(slot, 42);
    assert_eq!(store_sum_and_return_delta(&mut slot, -7, 10), -39);
    assert_eq!(slot, 3);
}

#[cfg(target_os = "windows")]
extern "C" fn jit_windows_host_memcpy(dst: *mut u8, src: *const u8, len: i64) {
    unsafe {
        std::ptr::copy_nonoverlapping(src, dst, len as usize);
    }
}

#[cfg(target_os = "windows")]
extern "C" fn jit_windows_host_memmove(dst: *mut u8, src: *const u8, len: i64) {
    unsafe {
        std::ptr::copy(src, dst, len as usize);
    }
}

#[cfg(target_os = "windows")]
extern "C" fn jit_windows_host_memset(dst: *mut u8, byte: i32, len: i64) {
    unsafe {
        std::ptr::write_bytes(dst, byte as u8, len as usize);
    }
}

#[cfg(target_os = "windows")]
fn windows_memory_intrinsic_module() -> TrustIrModule {
    let memcpy_ty = FuncTyId::new(0);
    let memmove_ty = FuncTyId::new(1);
    let memset_ty = FuncTyId::new(2);
    let pointer_copy_params = vec![Ty::Ptr, Ty::Ptr, Ty::I64];
    let memset_params = vec![Ty::Ptr, Ty::I32, Ty::I64];

    fn extern_decl(id: u32, name: &str, ty: FuncTyId) -> TrustIrFunction {
        TrustIrFunction {
            attrs: Default::default(),
            id: FuncId::new(id),
            name: name.to_owned(),
            ty,
            entry: BlockId::new(0),
            blocks: vec![],
            proofs: vec![],
            calling_conv: CallingConv::default(),
            linkage: Linkage::External,
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
        }
    }

    fn wrapper(
        id: u32,
        name: &str,
        ty: FuncTyId,
        callee: FuncId,
        params: Vec<Ty>,
    ) -> TrustIrFunction {
        let args: Vec<_> = (0..params.len() as u32).map(ValueId::new).collect();
        TrustIrFunction {
            attrs: Default::default(),
            id: FuncId::new(id),
            name: name.to_owned(),
            ty,
            entry: BlockId::new(0),
            blocks: vec![TrustIrBlock {
                id: BlockId::new(0),
                params: args.iter().copied().zip(params).collect(),
                body: vec![
                    InstrNode {
                        inst: Inst::Call {
                            callee,
                            args: args.clone(),
                        },
                        results: vec![],
                        proofs: vec![],
                        span: None,
                        proof_context: None,
                        scope: None,
                    },
                    InstrNode {
                        inst: Inst::Return { values: vec![] },
                        results: vec![],
                        proofs: vec![],
                        span: None,
                        proof_context: None,
                        scope: None,
                    },
                ],
            }],
            proofs: vec![],
            calling_conv: CallingConv::default(),
            linkage: Linkage::default(),
            summary: None,
            producer: None,
            value_names: None,
            scopes: None,
            source_provenance: None,
        }
    }

    TrustIrModule {
        name: "x86_64_windows_memory_intrinsics".to_owned(),
        functions: vec![
            extern_decl(0, "memcpy", memcpy_ty),
            extern_decl(1, "memmove", memmove_ty),
            extern_decl(2, "memset", memset_ty),
            wrapper(
                3,
                "call_intrinsic_memcpy",
                memcpy_ty,
                FuncId::new(0),
                pointer_copy_params.clone(),
            ),
            wrapper(
                4,
                "call_intrinsic_memmove",
                memmove_ty,
                FuncId::new(1),
                pointer_copy_params,
            ),
            wrapper(
                5,
                "call_intrinsic_memset",
                memset_ty,
                FuncId::new(2),
                memset_params.clone(),
            ),
        ],
        structs: vec![],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![Ty::Ptr, Ty::Ptr, Ty::I64],
                returns: vec![],
                is_vararg: false,
            },
            FuncTy {
                params: vec![Ty::Ptr, Ty::Ptr, Ty::I64],
                returns: vec![],
                is_vararg: false,
            },
            FuncTy {
                params: memset_params,
                returns: vec![],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_executes_memory_intrinsics() {
    let extern_symbols = HashMap::from([
        (
            "memcpy".to_owned(),
            jit_windows_host_memcpy as *const () as *const u8,
        ),
        (
            "memmove".to_owned(),
            jit_windows_host_memmove as *const () as *const u8,
        ),
        (
            "memset".to_owned(),
            jit_windows_host_memset as *const () as *const u8,
        ),
    ]);
    let result = Compiler::for_host()
        .compile_module_to_jit(&windows_memory_intrinsic_module(), &extern_symbols)
        .expect("Windows x86-64 JIT should compile memory intrinsics");

    let call_memcpy: extern "C" fn(*mut u8, *const u8, i64) = unsafe {
        result
            .buffer
            .get_fn_bound("call_intrinsic_memcpy")
            .expect("call_intrinsic_memcpy symbol")
            .into_inner()
    };
    let call_memmove: extern "C" fn(*mut u8, *const u8, i64) = unsafe {
        result
            .buffer
            .get_fn_bound("call_intrinsic_memmove")
            .expect("call_intrinsic_memmove symbol")
            .into_inner()
    };
    let call_memset: extern "C" fn(*mut u8, i32, i64) = unsafe {
        result
            .buffer
            .get_fn_bound("call_intrinsic_memset")
            .expect("call_intrinsic_memset symbol")
            .into_inner()
    };

    let mut small_dst = [0xCC_u8; 12];
    let small_src = [0xE0, 1, 2, 3, 4, 5, 6, 7, 0xE1];
    call_memcpy(
        unsafe { small_dst.as_mut_ptr().add(2) },
        unsafe { small_src.as_ptr().add(1) },
        7,
    );
    assert_eq!(&small_dst[..2], &[0xCC, 0xCC]);
    assert_eq!(&small_dst[2..9], &small_src[1..8]);
    assert_eq!(&small_dst[9..], &[0xCC, 0xCC, 0xCC]);

    let medium_src: Vec<u8> = (0..257).map(|i| (i as u8).wrapping_mul(37)).collect();
    let mut medium_dst = vec![0xD5_u8; 261];
    call_memcpy(
        unsafe { medium_dst.as_mut_ptr().add(2) },
        medium_src.as_ptr(),
        medium_src.len() as i64,
    );
    assert_eq!(&medium_dst[..2], &[0xD5, 0xD5]);
    assert_eq!(&medium_dst[2..259], medium_src.as_slice());
    assert_eq!(&medium_dst[259..], &[0xD5, 0xD5]);

    let mut zero_copy_dst = [0x91_u8, 0x92, 0x93, 0x94, 0x95];
    let zero_copy_src = [0xA0_u8, 0xA1, 0xA2, 0xA3];
    let before_zero_copy_dst = zero_copy_dst;
    call_memcpy(
        unsafe { zero_copy_dst.as_mut_ptr().add(2) },
        unsafe { zero_copy_src.as_ptr().add(1) },
        0,
    );
    assert_eq!(zero_copy_dst, before_zero_copy_dst);

    let mut zero_fill = [3_u8, 4, 5, 6, 7];
    let before_zero_fill = zero_fill;
    call_memset(unsafe { zero_fill.as_mut_ptr().add(1) }, 0xA5, 0);
    assert_eq!(zero_fill, before_zero_fill);

    let mut medium_fill = vec![0x11_u8; 197];
    call_memset(unsafe { medium_fill.as_mut_ptr().add(2) }, 0xA5, 193);
    assert_eq!(&medium_fill[..2], &[0x11, 0x11]);
    assert!(medium_fill[2..195].iter().all(|byte| *byte == 0xA5));
    assert_eq!(&medium_fill[195..], &[0x11, 0x11]);

    let original: Vec<u8> = (0..16).collect();
    let mut dst_above_src = original.clone();
    call_memmove(
        unsafe { dst_above_src.as_mut_ptr().add(4) },
        dst_above_src.as_ptr(),
        8,
    );
    let mut expected_above = original.clone();
    for i in 0..8 {
        expected_above[4 + i] = original[i];
    }
    assert_eq!(dst_above_src, expected_above);

    let mut dst_below_src = original.clone();
    call_memmove(
        dst_below_src.as_mut_ptr(),
        unsafe { dst_below_src.as_ptr().add(4) },
        8,
    );
    let mut expected_below = original.clone();
    expected_below[..8].copy_from_slice(&original[4..12]);
    assert_eq!(dst_below_src, expected_below);

    let mut zero_move = [0x31_u8, 0x32, 0x33, 0x34, 0x35, 0x36];
    let before_zero_move = zero_move;
    call_memmove(
        unsafe { zero_move.as_mut_ptr().add(3) },
        zero_move.as_ptr(),
        0,
    );
    assert_eq!(zero_move, before_zero_move);
}

#[cfg(target_os = "windows")]
const GPR_SPILL_REPLAY_LANES: usize = 32;

#[cfg(target_os = "windows")]
fn build_high_gpr_pressure_spill_replay_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_windows_gpr_spill_replay");
    let ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
    let mut fb = mb.function("high_gpr_pressure_reduce", ty);
    let entry = fb.create_block();
    let input = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);

    let mut live_values = Vec::with_capacity(GPR_SPILL_REPLAY_LANES);
    for lane in 0..GPR_SPILL_REPLAY_LANES {
        let index = fb.iconst(Ty::I64, lane as i128);
        let addr = fb.gep(Ty::I64, input, vec![index]);
        let loaded = fb.load(Ty::I64, addr);
        let multiplier = fb.iconst(Ty::I64, ((lane as i64) % 5 + 2) as i128);
        let product = fb.mul(Ty::I64, loaded, multiplier);
        let bias = fb.iconst(Ty::I64, (lane as i64 * 11 - 23) as i128);
        live_values.push(fb.add(Ty::I64, product, bias));
    }

    let mut acc = fb.iconst(Ty::I64, 0);
    for value in live_values {
        acc = fb.add(Ty::I64, acc, value);
    }
    fb.ret(vec![acc]);
    fb.build();
    mb.build()
}

#[cfg(target_os = "windows")]
fn reference_high_gpr_pressure(input: &[i64]) -> i64 {
    input
        .iter()
        .take(GPR_SPILL_REPLAY_LANES)
        .enumerate()
        .map(|(lane, value)| value * ((lane as i64) % 5 + 2) + lane as i64 * 11 - 23)
        .sum()
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_high_gpr_pressure_spill_replay_executes() {
    let module = build_high_gpr_pressure_spill_replay_module();
    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = OptLevel::O0;
    let result = Compiler::new(config)
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile high-pressure GPR spill replay");

    let high_gpr_pressure_reduce: extern "C" fn(*const i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("high_gpr_pressure_reduce")
            .expect("high_gpr_pressure_reduce symbol")
            .into_inner()
    };

    let input: Vec<i64> = (0..GPR_SPILL_REPLAY_LANES)
        .map(|lane| (lane as i64 * 17) - 41)
        .collect();
    assert_eq!(
        high_gpr_pressure_reduce(input.as_ptr()),
        reference_high_gpr_pressure(&input)
    );
}

#[cfg(target_os = "windows")]
fn build_fixed_reg_div_shift_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_windows_fixed_reg_div_shift");
    let ty = mb.add_func_type(
        vec![Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        vec![Ty::I64],
    );
    let mut fb = mb.function("fixed_reg_div_shift", ty);
    let entry = fb.create_block();
    let dividend = fb.add_block_param(entry, Ty::I64);
    let divisor = fb.add_block_param(entry, Ty::I64);
    let shift = fb.add_block_param(entry, Ty::I64);
    let salt = fb.add_block_param(entry, Ty::I64);
    let tail = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);

    let quotient = fb.sdiv(Ty::I64, dividend, divisor);
    let remainder = fb.binop(BinOp::SRem, Ty::I64, dividend, divisor);
    let shifted = fb.binop(BinOp::Shl, Ty::I64, quotient, shift);
    let signed_shift = fb.binop(BinOp::AShr, Ty::I64, salt, shift);
    let tail_mix = fb.mul(Ty::I64, salt, tail);
    let div_mix = fb.add(Ty::I64, shifted, remainder);
    let shifted_mix = fb.add(Ty::I64, div_mix, signed_shift);
    let result = fb.add(Ty::I64, shifted_mix, tail_mix);
    fb.ret(vec![result]);
    fb.build();
    mb.build()
}

#[cfg(target_os = "windows")]
fn reference_fixed_reg_div_shift(
    dividend: i64,
    divisor: i64,
    shift: u32,
    salt: i64,
    tail: i64,
) -> i64 {
    ((dividend / divisor) << shift) + (dividend % divisor) + (salt >> shift) + (salt * tail)
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_executes_idiv_cqo_and_shift_cl_fixed_regs() {
    let module = build_fixed_reg_div_shift_module();
    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = OptLevel::O0;
    let result = Compiler::new(config)
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile IDIV/CQO and shift-CL fixed-register path");

    let fixed_reg_div_shift: extern "C" fn(i64, i64, i64, i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("fixed_reg_div_shift")
            .expect("fixed_reg_div_shift symbol")
            .into_inner()
    };

    for (dividend, divisor, shift, salt, tail) in [
        (1234, 17, 3, -512, 9),
        (-987, 13, 2, 255, -4),
        (4095, -31, 1, -99, 7),
    ] {
        assert_eq!(
            fixed_reg_div_shift(dividend, divisor, shift, salt, tail),
            reference_fixed_reg_div_shift(dividend, divisor, shift as u32, salt, tail),
            "fixed-register divide/shift result mismatch for {dividend}/{divisor}, shift {shift}"
        );
    }
}

#[cfg(target_os = "windows")]
fn build_unsigned_fixed_reg_div_shift_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_windows_unsigned_fixed_reg_div_shift");
    let ty = mb.add_func_type(
        vec![Ty::U64, Ty::U64, Ty::U64, Ty::U64, Ty::U64],
        vec![Ty::U64],
    );
    let mut fb = mb.function("unsigned_fixed_reg_div_shift", ty);
    let entry = fb.create_block();
    let dividend = fb.add_block_param(entry, Ty::U64);
    let divisor = fb.add_block_param(entry, Ty::U64);
    let shift = fb.add_block_param(entry, Ty::U64);
    let high_bits = fb.add_block_param(entry, Ty::U64);
    let tail = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);

    let quotient = fb.binop(BinOp::UDiv, Ty::U64, dividend, divisor);
    let remainder = fb.binop(BinOp::URem, Ty::U64, dividend, divisor);
    let shifted = fb.binop(BinOp::LShr, Ty::U64, high_bits, shift);
    let quotient_prime = fb.iconst(Ty::U64, 0x9E37_79B9_7F4A_7C15u64 as i128);
    let remainder_prime = fb.iconst(Ty::U64, 0xBF58_476D_1CE4_E5B9u64 as i128);
    let quotient_mix = fb.mul(Ty::U64, quotient, quotient_prime);
    let remainder_mix = fb.mul(Ty::U64, remainder, remainder_prime);
    let shifted_tail = fb.binop(BinOp::Xor, Ty::U64, shifted, tail);
    let div_mix = fb.add(Ty::U64, quotient_mix, remainder_mix);
    let shifted_mix = fb.add(Ty::U64, div_mix, shifted_tail);
    let result = fb.add(Ty::U64, shifted_mix, shift);
    fb.ret(vec![result]);
    fb.build();
    mb.build()
}

#[cfg(target_os = "windows")]
fn reference_unsigned_fixed_reg_div_shift(
    dividend: u64,
    divisor: u64,
    shift: u32,
    high_bits: u64,
    tail: u64,
) -> u64 {
    let quotient = dividend / divisor;
    let remainder = dividend % divisor;
    let shifted = high_bits >> shift;
    quotient
        .wrapping_mul(0x9E37_79B9_7F4A_7C15)
        .wrapping_add(remainder.wrapping_mul(0xBF58_476D_1CE4_E5B9))
        .wrapping_add(shifted ^ tail)
        .wrapping_add(u64::from(shift))
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_executes_udiv_urem_lshr_u64_fixed_regs() {
    let module = build_unsigned_fixed_reg_div_shift_module();
    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = OptLevel::O0;
    let result = Compiler::new(config)
        .compile_module_to_jit(&module, &HashMap::new())
        .expect(
            "Windows x86-64 JIT should compile unsigned DIV and logical shift fixed-register path",
        );

    let unsigned_fixed_reg_div_shift: extern "C" fn(u64, u64, u64, u64, u64) -> u64 = unsafe {
        result
            .buffer
            .get_fn_bound("unsigned_fixed_reg_div_shift")
            .expect("unsigned_fixed_reg_div_shift symbol")
            .into_inner()
    };

    for (dividend, divisor, shift, high_bits, tail) in [
        (u64::MAX, 3, 1, 1u64 << 63, 0x0123_4567_89AB_CDEF),
        (1u64 << 63, 7, 17, u64::MAX, 0xDEAD_BEEF_CAFE_BABE),
        (
            0xFEDC_BA98_7654_3210,
            0x1_0000_0001,
            63,
            0x8000_0000_0000_0001,
            0,
        ),
        (
            0x8000_0000_0000_0005,
            5,
            4,
            0xF000_0000_0000_0000,
            0xA5A5_5A5A_F0F0_0F0F,
        ),
    ] {
        assert_eq!(
            unsigned_fixed_reg_div_shift(dividend, divisor, shift, high_bits, tail),
            reference_unsigned_fixed_reg_div_shift(
                dividend,
                divisor,
                shift as u32,
                high_bits,
                tail
            ),
            "unsigned divide/remainder/logical-shift result mismatch for {dividend}/{divisor}, shift {shift}"
        );
    }
}

#[cfg(target_os = "windows")]
fn build_unsigned_u32_fixed_reg_div_shift_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_windows_unsigned_u32_fixed_reg_div_shift");
    let ty = mb.add_func_type(
        vec![Ty::U32, Ty::U32, Ty::U32, Ty::U32, Ty::U32],
        vec![Ty::U32],
    );
    let mut fb = mb.function("unsigned_u32_fixed_reg_div_shift", ty);
    let entry = fb.create_block();
    let dividend = fb.add_block_param(entry, Ty::U32);
    let divisor = fb.add_block_param(entry, Ty::U32);
    let shift = fb.add_block_param(entry, Ty::U32);
    let high_bits = fb.add_block_param(entry, Ty::U32);
    let tail = fb.add_block_param(entry, Ty::U32);
    fb.switch_to_block(entry);

    let quotient = fb.binop(BinOp::UDiv, Ty::U32, dividend, divisor);
    let remainder = fb.binop(BinOp::URem, Ty::U32, dividend, divisor);
    let shifted = fb.binop(BinOp::LShr, Ty::U32, high_bits, shift);
    let quotient_prime = fb.iconst(Ty::U32, 0x9E37_79B9u32 as i128);
    let remainder_prime = fb.iconst(Ty::U32, 0x85EB_CA6Bu32 as i128);
    let quotient_mix = fb.mul(Ty::U32, quotient, quotient_prime);
    let remainder_mix = fb.mul(Ty::U32, remainder, remainder_prime);
    let shifted_tail = fb.binop(BinOp::Xor, Ty::U32, shifted, tail);
    let div_mix = fb.add(Ty::U32, quotient_mix, remainder_mix);
    let shifted_mix = fb.add(Ty::U32, div_mix, shifted_tail);
    let result = fb.add(Ty::U32, shifted_mix, shift);
    fb.ret(vec![result]);
    fb.build();
    mb.build()
}

#[cfg(target_os = "windows")]
fn reference_unsigned_u32_fixed_reg_div_shift(
    dividend: u32,
    divisor: u32,
    shift: u32,
    high_bits: u32,
    tail: u32,
) -> u32 {
    let quotient = dividend / divisor;
    let remainder = dividend % divisor;
    let shifted = high_bits >> shift;
    quotient
        .wrapping_mul(0x9E37_79B9)
        .wrapping_add(remainder.wrapping_mul(0x85EB_CA6B))
        .wrapping_add(shifted ^ tail)
        .wrapping_add(shift)
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_executes_u32_udiv_urem_lshr_fixed_regs() {
    let module = build_unsigned_u32_fixed_reg_div_shift_module();
    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = OptLevel::O0;
    let result = Compiler::new(config)
        .compile_module_to_jit(&module, &HashMap::new())
        .expect(
            "Windows x86-64 JIT should compile U32 unsigned DIV and CL logical shift fixed-register path",
        );

    let unsigned_u32_fixed_reg_div_shift: extern "C" fn(u32, u32, u32, u32, u32) -> u32 = unsafe {
        result
            .buffer
            .get_fn_bound("unsigned_u32_fixed_reg_div_shift")
            .expect("unsigned_u32_fixed_reg_div_shift symbol")
            .into_inner()
    };

    for (dividend, divisor, shift, high_bits, tail) in [
        (u32::MAX, 3, 1, 1u32 << 31, 0x0123_4567),
        (1u32 << 31, 7, 17, u32::MAX, 0xDEAD_BEEF),
        (0xFEDC_BA98, 0x0001_0001, 31, 0x8000_0001, 0),
        (0x8000_0005, 5, 4, 0xF000_0000, 0xA5A5_5A5A),
    ] {
        assert_eq!(
            unsigned_u32_fixed_reg_div_shift(dividend, divisor, shift, high_bits, tail),
            reference_unsigned_u32_fixed_reg_div_shift(dividend, divisor, shift, high_bits, tail),
            "U32 unsigned divide/remainder/logical-shift result mismatch for {dividend}/{divisor}, shift {shift}"
        );
    }
}

#[cfg(target_os = "windows")]
fn windows_guarded_sdiv_trap_route_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("x86_64_windows_guarded_sdiv_trap_route");
    let ty = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func =
        TrustIrFunction::new(FuncId::new(0), "guarded_sdiv_nonzero", ty, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode {
                inst: Inst::BinOp {
                    op: BinOp::SDiv,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                },
                results: vec![ValueId::new(2)],
                proofs: vec![ProofAnnotation::DivNonZero],
                span: None,
                proof_context: None,
                scope: None,
            },
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_guarded_div_nonzero_contains_ud2_trap_route() {
    let module = windows_guarded_sdiv_trap_route_module();
    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = OptLevel::O0;
    let result = Compiler::new(config)
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile guarded division with a trap route");

    let guarded_sdiv_nonzero: extern "C" fn(i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("guarded_sdiv_nonzero")
            .expect("guarded_sdiv_nonzero symbol")
            .into_inner()
    };
    assert_eq!(guarded_sdiv_nonzero(84, 2), 42);
    assert_eq!(guarded_sdiv_nonzero(-81, 3), -27);

    let fn_ptr = result
        .buffer
        .get_fn_ptr_bound("guarded_sdiv_nonzero")
        .expect("guarded_sdiv_nonzero pointer");
    let code_offset = result
        .buffer
        .code_offset_for_host_pc(fn_ptr.as_ptr() as u64)
        .expect("function pointer should belong to the JIT buffer");
    let replay = result.buffer.replay_report_metadata();
    let symbol = replay
        .symbols
        .iter()
        .find(|symbol| symbol.name == "guarded_sdiv_nonzero")
        .expect("replay metadata should include guarded_sdiv_nonzero");
    assert!(symbol.range.contains(code_offset));

    let code_len =
        usize::try_from(replay.code_size).expect("JIT code size should fit usize for inspection");
    assert!(
        (1..=4096).contains(&code_len),
        "guarded_sdiv_nonzero test should compile to a small JIT artifact, got {code_len} bytes"
    );
    let code_base = fn_ptr
        .as_ptr()
        .wrapping_sub(usize::try_from(code_offset).expect("code offset should fit usize"));
    let bytes = unsafe { std::slice::from_raw_parts(code_base, code_len) };
    let preview_len = bytes.len().min(128);
    assert!(
        bytes.windows(2).any(|window| window == [0x0F, 0x0B]),
        "guarded_sdiv_nonzero should contain a UD2 trap route, code_size: {}, symbol range: {:?}, bytes prefix: {:02x?}",
        replay.code_size,
        symbol.range,
        &bytes[..preview_len]
    );
}

#[cfg(target_os = "windows")]
fn windows_stack_alignment_probe_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("x86_64_windows_stack_alignment_probe");
    let probe_ty = module.add_func_type(FuncTy {
        params: vec![
            Ty::I64,
            Ty::I64,
            Ty::I64,
            Ty::I64,
            Ty::I64,
            Ty::I64,
            Ty::Ptr,
        ],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let entry_ty = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    module.add_function(TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "trust_cg_win64_stack_probe_helper".to_owned(),
        ty: probe_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    });

    let mut body = Vec::new();
    for (idx, value) in [
        WIN64_STACK_PROBE_A0,
        WIN64_STACK_PROBE_A1,
        WIN64_STACK_PROBE_A2,
        WIN64_STACK_PROBE_A3,
        WIN64_STACK_PROBE_A4,
        WIN64_STACK_PROBE_A5,
    ]
    .into_iter()
    .enumerate()
    {
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(value as i128),
            })
            .with_result(ValueId::new((idx + 1) as u32)),
        );
    }
    body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![
                ValueId::new(1),
                ValueId::new(2),
                ValueId::new(3),
                ValueId::new(4),
                ValueId::new(5),
                ValueId::new(6),
                ValueId::new(0),
            ],
        })
        .with_result(ValueId::new(7)),
    );
    body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(7)],
    }));

    let mut entry = TrustIrFunction::new(
        FuncId::new(1),
        "run_win64_stack_probe",
        entry_ty,
        BlockId::new(0),
    );
    entry.blocks.push(TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr)],
        body,
    });
    module.add_function(entry);
    module
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_validates_shadow_space_and_stack_alignment_with_overflow_args() {
    let module = windows_stack_alignment_probe_module();
    let extern_symbols = HashMap::from([(
        "trust_cg_win64_stack_probe_helper".to_owned(),
        trust_cg_win64_stack_probe_helper as *const () as *const u8,
    )]);
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &extern_symbols)
        .expect("Windows x86-64 JIT should compile stack-alignment probe");

    assert_eq!(result.buffer.symbol_count(), 1);
    assert!(
        result
            .buffer
            .get_fn_ptr_bound("trust_cg_win64_stack_probe_helper")
            .is_none()
    );

    let run_win64_stack_probe: extern "C" fn(*mut Win64StackProbeObservation) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("run_win64_stack_probe")
            .expect("run_win64_stack_probe symbol")
            .into_inner()
    };

    let mut observed = Win64StackProbeObservation::default();
    let status = run_win64_stack_probe(&mut observed);
    let observed_ptr = &mut observed as *mut Win64StackProbeObservation as usize;

    assert_eq!(status, WIN64_STACK_PROBE_OK, "{observed:#?}");
    assert_eq!(observed.entry_rsp_mod16, 8);
    assert_eq!((observed.entry_rsp + 8) % 16, 0);
    assert_eq!(observed.rcx, WIN64_STACK_PROBE_A0);
    assert_eq!(observed.rdx, WIN64_STACK_PROBE_A1);
    assert_eq!(observed.r8, WIN64_STACK_PROBE_A2);
    assert_eq!(observed.r9, WIN64_STACK_PROBE_A3);
    assert_eq!(observed.stack_a4_before, WIN64_STACK_PROBE_A4);
    assert_eq!(observed.stack_a5_before, WIN64_STACK_PROBE_A5);
    assert_eq!(observed.stack_out_before, observed_ptr);
    assert_eq!(observed.shadow0_after_write, 0x1111_2222_3333_4444);
    assert_eq!(observed.shadow1_after_write, 0x5555_6666_7777_8888);
    assert_eq!(observed.shadow2_after_write, 0x9999_aaaa_bbbb_cccc);
    assert_eq!(observed.shadow3_after_write, 0xdddd_eeee_ffff_0000);
    assert_eq!(observed.stack_a4_after_shadow_write, WIN64_STACK_PROBE_A4);
    assert_eq!(observed.stack_a5_after_shadow_write, WIN64_STACK_PROBE_A5);
    assert_eq!(observed.stack_out_after_shadow_write, observed_ptr);
}

#[cfg(target_os = "windows")]
fn windows_stack_local_survives_stack_arg_call_module() -> TrustIrModule {
    const FIXED_SENTINEL: i64 = 0x1234_5678_0102_0304;
    const RUNTIME_SENTINEL: i64 = 0x2345_6789_0A0B_0C0D;

    fn const_i64(result: u32, value: i64) -> InstrNode {
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(value as i128),
        })
        .with_result(ValueId::new(result))
    }

    fn add_i64(result: u32, lhs: u32, rhs: u32) -> InstrNode {
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(lhs),
            rhs: ValueId::new(rhs),
        })
        .with_result(ValueId::new(result))
    }

    fn push_sum8_args(body: &mut Vec<InstrNode>, first_result: u32) -> Vec<ValueId> {
        let mut args = Vec::with_capacity(8);
        for idx in 0..8 {
            let result = first_result + idx;
            body.push(const_i64(result, i64::from(idx + 1)));
            args.push(ValueId::new(result));
        }
        args
    }

    let mut module = TrustIrModule::new("x86_64_windows_stack_local_survives_call");
    let sum_ty = module.add_func_type(FuncTy {
        params: vec![Ty::I64; 8],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let fixed_ty = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let runtime_ty = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let mut sum8 = TrustIrFunction::new(
        FuncId::new(0),
        "sum8_stack_local_probe",
        sum_ty,
        BlockId::new(0),
    );
    let mut sum_body = Vec::new();
    let mut acc = 0;
    for (rhs, result) in (1..8).zip(8..15) {
        sum_body.push(add_i64(result, acc, rhs));
        acc = result;
    }
    sum8.blocks.push(TrustIrBlock {
        id: BlockId::new(0),
        params: (0..8).map(|value| (ValueId::new(value), Ty::I64)).collect(),
        body: {
            sum_body.push(InstrNode::new(Inst::Return {
                values: vec![ValueId::new(acc)],
            }));
            sum_body
        },
    });
    module.add_function(sum8);

    let mut fixed_body = vec![
        InstrNode::new(Inst::Alloca {
            ty: Ty::I64,
            count: None,
            align: None,
        })
        .with_result(ValueId::new(0)),
        const_i64(1, FIXED_SENTINEL),
        InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: ValueId::new(0),
            value: ValueId::new(1),
            align: None,
            volatile: false,
        }),
    ];
    let fixed_args = push_sum8_args(&mut fixed_body, 2);
    fixed_body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: fixed_args,
        })
        .with_result(ValueId::new(10)),
    );
    fixed_body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::I64,
            ptr: ValueId::new(0),
            align: None,
            volatile: false,
        })
        .with_result(ValueId::new(11)),
    );
    fixed_body.push(add_i64(12, 11, 10));
    fixed_body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(12)],
    }));
    let mut fixed = TrustIrFunction::new(
        FuncId::new(1),
        "fixed_stack_local_survives_stack_arg_call",
        fixed_ty,
        BlockId::new(0),
    );
    fixed.blocks.push(TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: fixed_body,
    });
    module.add_function(fixed);

    let mut runtime_body = vec![
        InstrNode::new(Inst::Alloca {
            ty: Ty::I64,
            count: Some(ValueId::new(0)),
            align: None,
        })
        .with_result(ValueId::new(2)),
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::I64,
            base: ValueId::new(2),
            indices: vec![ValueId::new(1)],
            inbounds: false,
        })
        .with_result(ValueId::new(3)),
        const_i64(4, RUNTIME_SENTINEL),
        InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: ValueId::new(3),
            value: ValueId::new(4),
            align: None,
            volatile: false,
        }),
    ];
    let runtime_args = push_sum8_args(&mut runtime_body, 5);
    runtime_body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: runtime_args,
        })
        .with_result(ValueId::new(13)),
    );
    runtime_body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::I64,
            ptr: ValueId::new(3),
            align: None,
            volatile: false,
        })
        .with_result(ValueId::new(14)),
    );
    runtime_body.push(add_i64(15, 14, 13));
    runtime_body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(15)],
    }));
    let mut runtime = TrustIrFunction::new(
        FuncId::new(2),
        "runtime_stack_local_survives_stack_arg_call",
        runtime_ty,
        BlockId::new(0),
    );
    runtime.blocks.push(TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: runtime_body,
    });
    module.add_function(runtime);

    module
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_preserves_stack_locals_across_stack_arg_calls() {
    const FIXED_SENTINEL: i64 = 0x1234_5678_0102_0304;
    const RUNTIME_SENTINEL: i64 = 0x2345_6789_0A0B_0C0D;
    const CALL_SUM: i64 = 36;

    let module = windows_stack_local_survives_stack_arg_call_module();
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile stack-local call overlap probes");
    let fixed_stack_local_survives_stack_arg_call: extern "C" fn() -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("fixed_stack_local_survives_stack_arg_call")
            .expect("fixed_stack_local_survives_stack_arg_call symbol")
            .into_inner()
    };
    let runtime_stack_local_survives_stack_arg_call: extern "C" fn(i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("runtime_stack_local_survives_stack_arg_call")
            .expect("runtime_stack_local_survives_stack_arg_call symbol")
            .into_inner()
    };

    assert_eq!(
        fixed_stack_local_survives_stack_arg_call(),
        FIXED_SENTINEL + CALL_SUM
    );
    assert_eq!(
        runtime_stack_local_survives_stack_arg_call(8, 5),
        RUNTIME_SENTINEL + CALL_SUM
    );
}

#[cfg(target_os = "windows")]
unsafe extern "system" {
    fn GetCurrentProcess() -> *mut c_void;
}

#[cfg(target_os = "windows")]
#[repr(C)]
#[derive(Debug)]
struct RuntimeFunction {
    begin_address: u32,
    end_address: u32,
    unwind_info_address: u32,
}

#[cfg(target_os = "windows")]
unsafe extern "system" {
    fn RtlLookupFunctionEntry(
        control_pc: u64,
        image_base: *mut u64,
        history_table: *mut c_void,
    ) -> *mut RuntimeFunction;
}

#[cfg(target_os = "windows")]
fn windows_get_current_process_module() -> TrustIrModule {
    let extern_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);

    let extern_decl = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "GetCurrentProcess".to_owned(),
        ty: extern_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "call_get_current_process".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: vec![],
                    },
                    results: vec![ValueId::new(0)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                InstrNode {
                    inst: Inst::Return {
                        values: vec![ValueId::new(0)],
                    },
                    results: vec![],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_windows_process_symbol_fallback".to_owned(),
        functions: vec![extern_decl, caller],
        structs: vec![],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: vec![],
                returns: vec![Ty::Ptr],
                is_vararg: false,
            },
            FuncTy {
                params: vec![],
                returns: vec![Ty::Ptr],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_resolves_kernel32_helper_without_extern_symbols() {
    let module = windows_get_current_process_module();
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should resolve GetCurrentProcess from loaded modules");

    let call_get_current_process: extern "C" fn() -> *mut c_void = unsafe {
        result
            .buffer
            .get_fn_bound("call_get_current_process")
            .expect("call_get_current_process symbol")
            .into_inner()
    };

    let expected = unsafe { GetCurrentProcess() };
    assert_eq!(call_get_current_process(), expected);
    assert!(!call_get_current_process().is_null());
}

#[cfg(target_os = "windows")]
fn windows_jit_non_leaf_unwind_lookup_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_windows_jit_unwind_lookup");

    {
        let ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("unwind_lookup_callee", ty);
        let entry = fb.create_block();
        let value = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let one = fb.iconst(Ty::I64, 1);
        let result = fb.add(Ty::I64, value, one);
        fb.ret(vec![result]);
        fb.build();
    }

    {
        let ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("unwind_lookup_caller", ty);
        let entry = fb.create_block();
        let value = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let called = fb.call(FuncId::new(0), vec![value]);
        let two = fb.iconst(Ty::I64, 2);
        let result = fb.add(Ty::I64, called, two);
        fb.ret(vec![result]);
        fb.build();
    }

    mb.build()
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_rtl_lookup_function_entry_finds_non_leaf_function() {
    let module = windows_jit_non_leaf_unwind_lookup_module();
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile non-leaf unwind lookup module");

    let caller = result
        .buffer
        .get_fn_ptr_bound("unwind_lookup_caller")
        .expect("unwind_lookup_caller symbol");
    let control_pc = caller.as_ptr() as u64;
    let code_offset = result
        .buffer
        .code_offset_for_host_pc(control_pc)
        .expect("function pointer should belong to the JIT buffer");
    let replay = result.buffer.replay_report_metadata();
    let caller_symbol = replay
        .symbols
        .iter()
        .find(|symbol| symbol.name == "unwind_lookup_caller")
        .expect("replay metadata should include caller range");
    assert!(
        caller_symbol.range.contains(code_offset),
        "JIT PC offset {code_offset:#x} should fall in caller range {:?}",
        caller_symbol.range
    );

    let mut image_base = 0u64;
    let runtime_function =
        unsafe { RtlLookupFunctionEntry(control_pc, &mut image_base, std::ptr::null_mut()) };

    assert!(
        !runtime_function.is_null(),
        "RtlLookupFunctionEntry should resolve a registered Windows x64 JIT function table entry"
    );

    let runtime_function = unsafe { &*runtime_function };
    let relative_pc = control_pc
        .checked_sub(image_base)
        .expect("control PC should be within the returned image base");
    assert!(
        u64::from(runtime_function.begin_address) <= relative_pc
            && relative_pc < u64::from(runtime_function.end_address),
        "RtlLookupFunctionEntry range {:?} with image base {image_base:#x} should contain PC {control_pc:#x}",
        runtime_function
    );
    assert_ne!(
        runtime_function.unwind_info_address, 0,
        "registered runtime function should point at UNWIND_INFO"
    );
}

#[cfg(target_os = "windows")]
extern "C" fn jit_windows_explicit_host_weighted_sum(
    a: i64,
    b: i64,
    c: i64,
    d: i64,
    e: i64,
    f: i64,
) -> i64 {
    a * 3 - b * 5 + c * 7 - d * 11 + e * 13 - f * 17 + 19
}

#[cfg(target_os = "windows")]
fn windows_explicit_extern_weighted_sum_module() -> TrustIrModule {
    let extern_ty = FuncTyId::new(0);
    let caller_ty = FuncTyId::new(1);
    let params = vec![Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64];

    let extern_decl = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "jit_windows_explicit_host_weighted_sum".to_owned(),
        ty: extern_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };
    let caller = TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "call_explicit_host_weighted_sum".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: (0..6).map(|value| (ValueId::new(value), Ty::I64)).collect(),
            body: vec![
                InstrNode {
                    inst: Inst::Call {
                        callee: FuncId::new(0),
                        args: (0..6).map(ValueId::new).collect(),
                    },
                    results: vec![ValueId::new(6)],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
                InstrNode {
                    inst: Inst::Return {
                        values: vec![ValueId::new(6)],
                    },
                    results: vec![],
                    proofs: vec![],
                    span: None,
                    proof_context: None,
                    scope: None,
                },
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    };

    TrustIrModule {
        name: "x86_64_windows_explicit_extern_binding".to_owned(),
        functions: vec![extern_decl, caller],
        structs: vec![],
        records: vec![],
        closure_types: vec![],
        globals: vec![],
        func_types: vec![
            FuncTy {
                params: params.clone(),
                returns: vec![Ty::I64],
                is_vararg: false,
            },
            FuncTy {
                params,
                returns: vec![Ty::I64],
                is_vararg: false,
            },
        ],
        types: vec![],
        proof_obligations: vec![],
        proof_certificates: vec![],
        enums: vec![],
        target_info: None,
        files: vec![],
        obligation_diagnostics: vec![],
        spec_modules: vec![],
        universes: vec![],
        predicates: vec![],
    }
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_uses_explicit_extern_symbol_veneer() {
    let module = windows_explicit_extern_weighted_sum_module();
    Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect_err("unique host helper should require an explicit extern binding");

    let mut extern_symbols = HashMap::new();
    extern_symbols.insert(
        "jit_windows_explicit_host_weighted_sum".to_owned(),
        jit_windows_explicit_host_weighted_sum as *const () as *const u8,
    );
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &extern_symbols)
        .expect("Windows x86-64 JIT should bind explicit extern through a veneer");

    assert_eq!(result.buffer.symbol_count(), 1);

    let call_explicit_host_weighted_sum: extern "C" fn(i64, i64, i64, i64, i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("call_explicit_host_weighted_sum")
            .expect("call_explicit_host_weighted_sum symbol")
            .into_inner()
    };

    assert_eq!(
        call_explicit_host_weighted_sum(2, -3, 5, 7, -11, 13),
        jit_windows_explicit_host_weighted_sum(2, -3, 5, 7, -11, 13)
    );
    assert_eq!(
        call_explicit_host_weighted_sum(1, 2, 3, 4, 5, 6),
        jit_windows_explicit_host_weighted_sum(1, 2, 3, 4, 5, 6)
    );
}

#[cfg(target_os = "windows")]
extern "C" fn jit_windows_shared_explicit_host_affine(a: i64, b: i64) -> i64 {
    a * 17 - b * 29 + 43
}

#[cfg(target_os = "windows")]
fn windows_shared_explicit_extern_veneer_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("x86_64_windows_shared_explicit_extern_veneer");
    let extern_ty = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let caller_ty = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    module.add_function(TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(0),
        name: "jit_windows_shared_explicit_host_affine".to_owned(),
        ty: extern_ty,
        entry: BlockId::new(0),
        blocks: vec![],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::External,
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    });

    module.add_function(TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(1),
        name: "call_shared_explicit_a".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(0),
                    args: vec![ValueId::new(0), ValueId::new(1)],
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(2)],
                }),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    });

    module.add_function(TrustIrFunction {
        attrs: Default::default(),
        id: FuncId::new(2),
        name: "call_shared_explicit_b".to_owned(),
        ty: caller_ty,
        entry: BlockId::new(0),
        blocks: vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(0),
                    args: vec![ValueId::new(1), ValueId::new(0)],
                })
                .with_result(ValueId::new(2)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(7),
                })
                .with_result(ValueId::new(3)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(2),
                    rhs: ValueId::new(3),
                })
                .with_result(ValueId::new(4)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(4)],
                }),
            ],
        }],
        proofs: vec![],
        calling_conv: CallingConv::default(),
        linkage: Linkage::default(),
        summary: None,
        producer: None,
        value_names: None,
        scopes: None,
        source_provenance: None,
    });

    module
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_reuses_shared_explicit_extern_veneer_across_call_sites() {
    let module = windows_shared_explicit_extern_veneer_module();
    Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect_err("shared host helper should require an explicit extern binding");

    let extern_symbols = HashMap::from([(
        "jit_windows_shared_explicit_host_affine".to_owned(),
        jit_windows_shared_explicit_host_affine as *const () as *const u8,
    )]);
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &extern_symbols)
        .expect("Windows x86-64 JIT should bind shared explicit extern through one veneer");

    assert_eq!(result.buffer.symbol_count(), 2);
    let call_shared_explicit_a: extern "C" fn(i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("call_shared_explicit_a")
            .expect("call_shared_explicit_a symbol")
            .into_inner()
    };
    let call_shared_explicit_b: extern "C" fn(i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("call_shared_explicit_b")
            .expect("call_shared_explicit_b symbol")
            .into_inner()
    };
    assert_eq!(
        call_shared_explicit_a(11, -3),
        jit_windows_shared_explicit_host_affine(11, -3)
    );
    assert_eq!(
        call_shared_explicit_b(11, -3),
        jit_windows_shared_explicit_host_affine(-3, 11) + 7
    );

    let replay = result.buffer.replay_report_metadata();
    let (bytes_a, start_a, code_base_a) =
        windows_jit_symbol_bytes(&result.buffer, "call_shared_explicit_a");
    let (bytes_b, start_b, code_base_b) =
        windows_jit_symbol_bytes(&result.buffer, "call_shared_explicit_b");
    assert_eq!(code_base_a, code_base_b);
    let target_a = decode_first_rel32_call_target(&bytes_a, start_a);
    let target_b = decode_first_rel32_call_target(&bytes_b, start_b);

    assert_eq!(
        target_a, target_b,
        "both generated call sites should patch to the same extern veneer"
    );
    assert!(
        !symbol_ranges_contain(&replay, target_a),
        "shared extern veneer should live outside generated function ranges"
    );
    assert!(
        target_a + 14 <= replay.code_size,
        "shared extern veneer should be fully inside the JIT artifact"
    );

    let veneer = unsafe { std::slice::from_raw_parts(code_base_a.add(target_a as usize), 14) };
    assert_eq!(&veneer[..6], &[0xff, 0x25, 0x00, 0x00, 0x00, 0x00]);
    let embedded = u64::from_le_bytes(
        veneer[6..14]
            .try_into()
            .expect("veneer target pointer should be 8 bytes"),
    );
    assert_eq!(
        embedded,
        jit_windows_shared_explicit_host_affine as *const () as usize as u64
    );
}

fn build_fp_constant_pool_boundary_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_fp_constant_pool_boundary");
    let ty = mb.add_func_type(vec![], vec![Ty::F64]);
    let mut fb = mb.function("fp_pressure_leaf", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);

    let mut acc = fb.fconst(Ty::F64, 0.25);
    for i in 1..=12 {
        let value = fb.fconst(Ty::F64, f64::from(i) + 0.5);
        let scale = fb.fconst(Ty::F64, f64::from((i % 7) + 1));
        let product = fb.fmul(Ty::F64, value, scale);
        acc = fb.fadd(Ty::F64, acc, product);
    }

    fb.ret(vec![acc]);
    fb.build();
    mb.build()
}

#[test]
fn x86_64_jit_fp_constant_pool_duplicate_boundary_compiles() {
    let module = build_fp_constant_pool_boundary_module();
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("x86-64 JIT should compile FP constant-pool boundary module");

    assert_eq!(result.buffer.symbol_count(), 1);
}

#[cfg(target_os = "windows")]
unsafe fn call_and_capture_xmm6(func: extern "C" fn() -> f64) -> (f64, [u64; 2]) {
    let sentinel = [0x0123_4567_89ab_cdef_u64, 0xfedc_ba98_7654_3210_u64];
    let mut original = [0_u64; 2];
    let mut observed = [0_u64; 2];
    let result: f64;

    unsafe {
        asm!(
            "movupd xmmword ptr [{original}], xmm6",
            "movupd xmm6, xmmword ptr [{sentinel}]",
            "sub rsp, 32",
            "call {target}",
            "add rsp, 32",
            "movupd xmmword ptr [{observed}], xmm6",
            "movupd xmm6, xmmword ptr [{original}]",
            original = in(reg) original.as_mut_ptr(),
            sentinel = in(reg) sentinel.as_ptr(),
            observed = in(reg) observed.as_mut_ptr(),
            target = in(reg) func,
            lateout("xmm0") result,
            clobber_abi("C"),
        );
    }

    (result, observed)
}

#[cfg(target_os = "windows")]
unsafe fn call_and_capture_nonvolatile_gprs(
    func: extern "C" fn(*const i64) -> i64,
    input: *const i64,
) -> (i64, [u64; 6]) {
    let sentinel = [
        0x0102_0304_0506_0708_u64,
        0x1112_1314_1516_1718_u64,
        0x2122_2324_2526_2728_u64,
        0x3132_3334_3536_3738_u64,
        0x4142_4344_4546_4748_u64,
        0x5152_5354_5556_5758_u64,
    ];
    let mut original = [0_u64; 6];
    let mut observed = [0_u64; 6];
    let result: i64;

    unsafe {
        asm!(
            "sub rsp, 80",
            "mov qword ptr [rsp + 32], r10",
            "mov qword ptr [rsp + 40], r8",
            "mov qword ptr [r8 + 0], rbx",
            "mov qword ptr [r8 + 8], rsi",
            "mov qword ptr [r8 + 16], rdi",
            "mov qword ptr [r8 + 24], r12",
            "mov qword ptr [r8 + 32], r13",
            "mov qword ptr [r8 + 40], r14",
            "mov rbx, qword ptr [r9 + 0]",
            "mov rsi, qword ptr [r9 + 8]",
            "mov rdi, qword ptr [r9 + 16]",
            "mov r12, qword ptr [r9 + 24]",
            "mov r13, qword ptr [r9 + 32]",
            "mov r14, qword ptr [r9 + 40]",
            "call r11",
            "mov r10, qword ptr [rsp + 32]",
            "mov r8, qword ptr [rsp + 40]",
            "mov qword ptr [r10 + 0], rbx",
            "mov qword ptr [r10 + 8], rsi",
            "mov qword ptr [r10 + 16], rdi",
            "mov qword ptr [r10 + 24], r12",
            "mov qword ptr [r10 + 32], r13",
            "mov qword ptr [r10 + 40], r14",
            "mov rbx, qword ptr [r8 + 0]",
            "mov rsi, qword ptr [r8 + 8]",
            "mov rdi, qword ptr [r8 + 16]",
            "mov r12, qword ptr [r8 + 24]",
            "mov r13, qword ptr [r8 + 32]",
            "mov r14, qword ptr [r8 + 40]",
            "add rsp, 80",
            in("rcx") input,
            in("r8") original.as_mut_ptr(),
            in("r9") sentinel.as_ptr(),
            in("r10") observed.as_mut_ptr(),
            in("r11") func,
            lateout("rax") result,
            clobber_abi("C"),
        );
    }

    (result, observed)
}

#[cfg(target_os = "windows")]
fn has_nonvolatile_gpr_save(bytes: &[u8]) -> bool {
    bytes.iter().any(|byte| matches!(byte, 0x53 | 0x56 | 0x57))
        || bytes
            .windows(2)
            .any(|window| window[0] == 0x41 && (0x54..=0x57).contains(&window[1]))
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_preserves_nonvolatile_xmm6() {
    let module = build_fp_constant_pool_boundary_module();
    let result = Compiler::for_host()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile FP pressure module");

    let fp_pressure_leaf: extern "C" fn() -> f64 = unsafe {
        result
            .buffer
            .get_fn_bound("fp_pressure_leaf")
            .expect("fp_pressure_leaf symbol")
            .into_inner()
    };

    let (returned, observed_xmm6) = unsafe { call_and_capture_xmm6(fp_pressure_leaf) };

    assert_eq!(returned, 353.25);
    assert_eq!(
        observed_xmm6,
        [0x0123_4567_89ab_cdef_u64, 0xfedc_ba98_7654_3210_u64],
        "Windows x64 callees must preserve XMM6"
    );
}

#[cfg(target_os = "windows")]
#[test]
fn x86_64_windows_jit_preserves_nonvolatile_gprs_under_pressure() {
    let module = build_high_gpr_pressure_spill_replay_module();
    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = OptLevel::O0;
    let result = Compiler::new(config)
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("Windows x86-64 JIT should compile high-pressure GPR module");

    let high_gpr_pressure_reduce: extern "C" fn(*const i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("high_gpr_pressure_reduce")
            .expect("high_gpr_pressure_reduce symbol")
            .into_inner()
    };
    let input: Vec<i64> = (0..GPR_SPILL_REPLAY_LANES)
        .map(|lane| (lane as i64 * 19) - 37)
        .collect();

    let (returned, observed_gprs) =
        unsafe { call_and_capture_nonvolatile_gprs(high_gpr_pressure_reduce, input.as_ptr()) };
    assert_eq!(returned, reference_high_gpr_pressure(&input));
    assert_eq!(
        observed_gprs,
        [
            0x0102_0304_0506_0708_u64,
            0x1112_1314_1516_1718_u64,
            0x2122_2324_2526_2728_u64,
            0x3132_3334_3536_3738_u64,
            0x4142_4344_4546_4748_u64,
            0x5152_5354_5556_5758_u64,
        ],
        "Windows x64 callees must preserve nonvolatile GPRs"
    );

    let (bytes, _, _) = windows_jit_symbol_bytes(&result.buffer, "high_gpr_pressure_reduce");
    assert!(
        has_nonvolatile_gpr_save(&bytes),
        "high-pressure function should force at least one non-RBP nonvolatile GPR save; bytes: {bytes:02x?}"
    );
}
