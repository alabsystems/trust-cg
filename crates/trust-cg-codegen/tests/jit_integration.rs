// trust-cg-codegen/tests/jit_integration.rs - JIT end-to-end integration tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Tests that compile IR functions through the full JIT pipeline and execute
// them in-process via JitCompiler::compile_raw(). Exercises:
// - Simple arithmetic functions (add, multiply, subtract)
// - Multi-function compilation with cross-function BL calls
// - External symbol resolution via veneer trampolines
// - Edge cases: branch patching limits, large function buffers
//
// Part of #342 — JIT integration tests: end-to-end compile + execute

#![cfg(target_arch = "aarch64")]
// Existing tests use `ExecutableBuffer::get_fn` and `get_fn_ptr`, which are
// deprecated in favour of the lifetime-bound `get_fn_bound` /
// `get_fn_ptr_bound` APIs (issue #355). These tests continue to exercise
// the legacy paths intentionally as regression coverage; silence the
// per-call deprecation warnings at the file level.
#![allow(deprecated)]

use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};
use std::sync::{Mutex, MutexGuard};

use trust_cg_codegen::compiler::Compiler;
use trust_cg_codegen::jit::{JitCompiler, JitConfig, JitError};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_cg_codegen::{JIT_REPLAY_SCHEMA, JIT_REPLAY_SCHEMA_VERSION};
use trust_cg_ir::function::{MachFunction, Signature, Type};
use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::operand::MachOperand::Special;
use trust_cg_ir::regs::{FP, LR, SpecialReg, X0, X1, X8, X9};

// ---------------------------------------------------------------------------
// Test helpers: function builders
// ---------------------------------------------------------------------------

/// Build `fn add(a: i64, b: i64) -> i64 { a + b }`
///
/// ADD X0, X0, X1 ; RET
fn build_add() -> MachFunction {
    let sig = Signature::new(vec![Type::I64, Type::I64], vec![Type::I64]);
    let mut func = MachFunction::new("add".to_string(), sig);
    let entry = func.entry;

    let add = MachInst::new(
        AArch64Opcode::AddRR,
        vec![
            MachOperand::PReg(X0),
            MachOperand::PReg(X0),
            MachOperand::PReg(X1),
        ],
    );
    let add_id = func.push_inst(add);
    func.append_inst(entry, add_id);

    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    let ret_id = func.push_inst(ret);
    func.append_inst(entry, ret_id);

    func
}

/// Build `fn sub(a: i64, b: i64) -> i64 { a - b }`
///
/// SUB X0, X0, X1 ; RET
fn build_sub() -> MachFunction {
    let sig = Signature::new(vec![Type::I64, Type::I64], vec![Type::I64]);
    let mut func = MachFunction::new("sub".to_string(), sig);
    let entry = func.entry;

    let sub = MachInst::new(
        AArch64Opcode::SubRR,
        vec![
            MachOperand::PReg(X0),
            MachOperand::PReg(X0),
            MachOperand::PReg(X1),
        ],
    );
    let sub_id = func.push_inst(sub);
    func.append_inst(entry, sub_id);

    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    let ret_id = func.push_inst(ret);
    func.append_inst(entry, ret_id);

    func
}

/// Build `fn mul(a: i64, b: i64) -> i64 { a * b }`
///
/// MUL X0, X0, X1 (encoded as MADD X0, X0, X1, XZR) ; RET
fn build_mul() -> MachFunction {
    let sig = Signature::new(vec![Type::I64, Type::I64], vec![Type::I64]);
    let mut func = MachFunction::new("mul".to_string(), sig);
    let entry = func.entry;

    let mul = MachInst::new(
        AArch64Opcode::MulRR,
        vec![
            MachOperand::PReg(X0),
            MachOperand::PReg(X0),
            MachOperand::PReg(X1),
        ],
    );
    let mul_id = func.push_inst(mul);
    func.append_inst(entry, mul_id);

    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    let ret_id = func.push_inst(ret);
    func.append_inst(entry, ret_id);

    func
}

/// Build `fn return_const() -> i64 { 42 }`
///
/// MOVZ X0, #42 ; RET
fn build_return_const() -> MachFunction {
    let sig = Signature::new(vec![], vec![Type::I64]);
    let mut func = MachFunction::new("return_const".to_string(), sig);
    let entry = func.entry;

    let mov = MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(X0), MachOperand::Imm(42)],
    );
    let mov_id = func.push_inst(mov);
    func.append_inst(entry, mov_id);

    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    let ret_id = func.push_inst(ret);
    func.append_inst(entry, ret_id);

    func
}

/// Build `fn negate(a: i64) -> i64 { 0 - a }`
///
/// NEG X0, X0 (encoded as SUB X0, XZR, X0) ; RET
fn build_negate() -> MachFunction {
    let sig = Signature::new(vec![Type::I64], vec![Type::I64]);
    let mut func = MachFunction::new("negate".to_string(), sig);
    let entry = func.entry;

    let neg = MachInst::new(
        AArch64Opcode::Neg,
        vec![MachOperand::PReg(X0), MachOperand::PReg(X0)],
    );
    let neg_id = func.push_inst(neg);
    func.append_inst(entry, neg_id);

    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    let ret_id = func.push_inst(ret);
    func.append_inst(entry, ret_id);

    func
}

/// Build `fn identity(a: i64) -> i64 { a }`
///
/// RET (X0 passthrough)
fn build_identity() -> MachFunction {
    let sig = Signature::new(vec![Type::I64], vec![Type::I64]);
    let mut func = MachFunction::new("identity".to_string(), sig);
    let entry = func.entry;

    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    let ret_id = func.push_inst(ret);
    func.append_inst(entry, ret_id);

    func
}

fn build_zero_instruction_function() -> MachFunction {
    MachFunction::new(
        "zero_instruction".to_string(),
        Signature::new(vec![], vec![]),
    )
}

/// Build iterative factorial:
///   fn factorial(n: i64) -> i64 {
///       result = 1, i = n
///       loop: if i <= 1 goto done; result *= i; i -= 1; goto loop
///       done: return result
///   }
fn build_factorial() -> MachFunction {
    let sig = Signature::new(vec![Type::I64], vec![Type::I64]);
    let mut func = MachFunction::new("factorial".to_string(), sig);

    let bb_entry = func.entry;
    let bb_loop = func.create_block();
    let bb_done = func.create_block();

    // MOV X8, X0 (i = n)
    let mov_n = MachInst::new(
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(X8), MachOperand::PReg(X0)],
    );
    let mov_n_id = func.push_inst(mov_n);
    func.append_inst(bb_entry, mov_n_id);

    // MOVZ X9, #1 (result = 1)
    let mov_one = MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::PReg(X9), MachOperand::Imm(1)],
    );
    let mov_one_id = func.push_inst(mov_one);
    func.append_inst(bb_entry, mov_one_id);

    // (fall through to bb_loop)

    // bb_loop: CMP X8, #1
    let cmp = MachInst::new(
        AArch64Opcode::CmpRI,
        vec![MachOperand::PReg(X8), MachOperand::Imm(1)],
    );
    let cmp_id = func.push_inst(cmp);
    func.append_inst(bb_loop, cmp_id);

    // B.LE bb_done (+4 instructions forward)
    let ble = MachInst::new(
        AArch64Opcode::BCond,
        vec![
            MachOperand::Imm(0xD), // LE
            MachOperand::Imm(4),   // +4 insts to bb_done
        ],
    );
    let ble_id = func.push_inst(ble);
    func.append_inst(bb_loop, ble_id);

    // MUL X9, X9, X8 (result *= i)
    let mul = MachInst::new(
        AArch64Opcode::MulRR,
        vec![
            MachOperand::PReg(X9),
            MachOperand::PReg(X9),
            MachOperand::PReg(X8),
        ],
    );
    let mul_id = func.push_inst(mul);
    func.append_inst(bb_loop, mul_id);

    // SUB X8, X8, #1 (i -= 1)
    let sub = MachInst::new(
        AArch64Opcode::SubRI,
        vec![
            MachOperand::PReg(X8),
            MachOperand::PReg(X8),
            MachOperand::Imm(1),
        ],
    );
    let sub_id = func.push_inst(sub);
    func.append_inst(bb_loop, sub_id);

    // B bb_loop (-4 instructions)
    let b_loop = MachInst::new(AArch64Opcode::B, vec![MachOperand::Imm(-4i64)]);
    let b_loop_id = func.push_inst(b_loop);
    func.append_inst(bb_loop, b_loop_id);

    // bb_done: MOV X0, X9
    let mov_result = MachInst::new(
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(X0), MachOperand::PReg(X9)],
    );
    let mov_result_id = func.push_inst(mov_result);
    func.append_inst(bb_done, mov_result_id);

    // RET
    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    let ret_id = func.push_inst(ret);
    func.append_inst(bb_done, ret_id);

    func
}

/// Build a function that calls another function via BL symbol reference.
///
/// `fn caller(a: i64, b: i64) -> i64 { callee(a, b) }`
///
/// Since BL clobbers LR, the caller must save/restore LR (X30) around the
/// call. We emit a minimal prologue/epilogue:
///   STP FP, LR, [SP, #-16]!   (save FP and LR, pre-index)
///   BL <callee>                (call — args already in X0, X1)
///   LDP FP, LR, [SP], #16     (restore FP and LR, post-index)
///   RET                        (return callee's result in X0)
fn build_caller(caller_name: &str, callee_name: &str) -> MachFunction {
    let sig = Signature::new(vec![Type::I64, Type::I64], vec![Type::I64]);
    let mut func = MachFunction::new(caller_name.to_string(), sig);
    let entry = func.entry;

    // STP FP, LR, [SP, #-16]! (pre-index: save frame pointer and link register)
    let stp = MachInst::new(
        AArch64Opcode::StpPreIndex,
        vec![
            MachOperand::PReg(FP),
            MachOperand::PReg(LR),
            Special(SpecialReg::SP),
            MachOperand::Imm(-16),
        ],
    );
    let stp_id = func.push_inst(stp);
    func.append_inst(entry, stp_id);

    // BL <callee> (symbol reference — resolved by JIT linker)
    let bl = MachInst::new(
        AArch64Opcode::Bl,
        vec![MachOperand::Symbol(callee_name.to_string())],
    );
    let bl_id = func.push_inst(bl);
    func.append_inst(entry, bl_id);

    // LDP FP, LR, [SP], #16 (post-index: restore frame pointer and link register)
    let ldp = MachInst::new(
        AArch64Opcode::LdpPostIndex,
        vec![
            MachOperand::PReg(FP),
            MachOperand::PReg(LR),
            Special(SpecialReg::SP),
            MachOperand::Imm(16),
        ],
    );
    let ldp_id = func.push_inst(ldp);
    func.append_inst(entry, ldp_id);

    // RET
    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    let ret_id = func.push_inst(ret);
    func.append_inst(entry, ret_id);

    func
}

fn decode_aarch64_bl_target(call_site: *const u8) -> usize {
    let word = unsafe { std::ptr::read_unaligned(call_site.cast::<u32>()) };
    assert_eq!(
        word & 0xFC00_0000,
        0x9400_0000,
        "expected BL at {call_site:p}, got word 0x{word:08x}"
    );
    let imm26 = word & 0x03FF_FFFF;
    let signed_imm26 = if imm26 & 0x0200_0000 != 0 {
        (imm26 as i64) | !0x03FF_FFFFi64
    } else {
        imm26 as i64
    };
    (call_site as isize + (signed_imm26 as isize * 4)) as usize
}

fn find_first_aarch64_bl_site(func_ptr: *const u8, max_bytes: usize) -> Option<*const u8> {
    for offset in (0..max_bytes).step_by(4) {
        let site = unsafe { func_ptr.add(offset) };
        let word = unsafe { std::ptr::read_unaligned(site.cast::<u32>()) };
        if word & 0xFC00_0000 == 0x9400_0000 {
            return Some(site);
        }
    }
    None
}

/// Build a "large" function that contains many ADD-immediate-zero instructions
/// to test code buffers approaching meaningful sizes.
///
/// Uses `ADD X8, X8, #0` as a no-op filler (real encoded instruction, unlike
/// the pseudo Nop which is skipped during encoding).
///
/// `fn large_fn(a: i64) -> i64 { /* filler_count ADDs */ return a }`
fn build_large_filler_function(name: &str, filler_count: usize) -> MachFunction {
    let sig = Signature::new(vec![Type::I64], vec![Type::I64]);
    let mut func = MachFunction::new(name.to_string(), sig);
    let entry = func.entry;

    for _ in 0..filler_count {
        // ADD X8, X8, #0 — real instruction, no effect on X0 (the return value).
        let filler = MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                MachOperand::PReg(X8),
                MachOperand::PReg(X8),
                MachOperand::Imm(0),
            ],
        );
        let filler_id = func.push_inst(filler);
        func.append_inst(entry, filler_id);
    }

    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    let ret_id = func.push_inst(ret);
    func.append_inst(entry, ret_id);

    func
}

// ---------------------------------------------------------------------------
// Test: simple add — compile and call via JIT
// ---------------------------------------------------------------------------

#[test]
fn test_jit_add() {
    let jit = JitCompiler::new(JitConfig::default());
    let add_fn = build_add();
    let ext: HashMap<String, *const u8> = HashMap::new();

    let buf = jit
        .compile_raw(&[add_fn], &ext)
        .expect("compile_raw should succeed");

    assert!(buf.allocated_size() > 0, "buffer should have nonzero size");
    assert!(buf.symbol_count() >= 1, "should have at least 1 symbol");

    let f: extern "C" fn(i64, i64) -> i64 =
        unsafe { buf.get_fn("add").expect("should find 'add' symbol") };

    assert_eq!(f(3, 4), 7);
    assert_eq!(f(0, 0), 0);
    assert_eq!(f(-1, 1), 0);
    assert_eq!(f(100, 200), 300);
    assert_eq!(f(i64::MAX, 0), i64::MAX);
    assert_eq!(f(-100, -200), -300);
}

// ---------------------------------------------------------------------------
// Test: subtract
// ---------------------------------------------------------------------------

#[test]
fn test_jit_sub() {
    let jit = JitCompiler::new(JitConfig::default());
    let sub_fn = build_sub();
    let ext: HashMap<String, *const u8> = HashMap::new();

    let buf = jit
        .compile_raw(&[sub_fn], &ext)
        .expect("compile_raw should succeed");

    let f: extern "C" fn(i64, i64) -> i64 =
        unsafe { buf.get_fn("sub").expect("should find 'sub' symbol") };

    assert_eq!(f(10, 3), 7);
    assert_eq!(f(0, 0), 0);
    assert_eq!(f(5, 5), 0);
    assert_eq!(f(-10, -3), -7);
    assert_eq!(f(1, -1), 2);
}

// ---------------------------------------------------------------------------
// Test: multiply
// ---------------------------------------------------------------------------

#[test]
fn test_jit_mul() {
    let jit = JitCompiler::new(JitConfig::default());
    let mul_fn = build_mul();
    let ext: HashMap<String, *const u8> = HashMap::new();

    let buf = jit
        .compile_raw(&[mul_fn], &ext)
        .expect("compile_raw should succeed");

    let f: extern "C" fn(i64, i64) -> i64 =
        unsafe { buf.get_fn("mul").expect("should find 'mul' symbol") };

    assert_eq!(f(3, 4), 12);
    assert_eq!(f(0, 999), 0);
    assert_eq!(f(7, 1), 7);
    assert_eq!(f(-3, 4), -12);
    assert_eq!(f(-3, -4), 12);
    assert_eq!(f(1000, 1000), 1_000_000);
}

// ---------------------------------------------------------------------------
// Test: return constant
// ---------------------------------------------------------------------------

#[test]
fn test_jit_return_const() {
    let jit = JitCompiler::new(JitConfig::default());
    let func = build_return_const();
    let ext: HashMap<String, *const u8> = HashMap::new();

    let buf = jit
        .compile_raw(&[func], &ext)
        .expect("compile_raw should succeed");

    let f: extern "C" fn() -> i64 = unsafe {
        buf.get_fn("return_const")
            .expect("should find 'return_const' symbol")
    };

    assert_eq!(f(), 42);
}

// ---------------------------------------------------------------------------
// Test: negate
// ---------------------------------------------------------------------------

#[test]
fn test_jit_negate() {
    let jit = JitCompiler::new(JitConfig::default());
    let func = build_negate();
    let ext: HashMap<String, *const u8> = HashMap::new();

    let buf = jit
        .compile_raw(&[func], &ext)
        .expect("compile_raw should succeed");

    let f: extern "C" fn(i64) -> i64 =
        unsafe { buf.get_fn("negate").expect("should find 'negate' symbol") };

    assert_eq!(f(5), -5);
    assert_eq!(f(-5), 5);
    assert_eq!(f(0), 0);
    assert_eq!(f(1), -1);
}

// ---------------------------------------------------------------------------
// Test: identity (passthrough)
// ---------------------------------------------------------------------------

#[test]
fn test_jit_identity() {
    let jit = JitCompiler::new(JitConfig::default());
    let func = build_identity();
    let ext: HashMap<String, *const u8> = HashMap::new();

    let buf = jit
        .compile_raw(&[func], &ext)
        .expect("compile_raw should succeed");

    let f: extern "C" fn(i64) -> i64 = unsafe {
        buf.get_fn("identity")
            .expect("should find 'identity' symbol")
    };

    assert_eq!(f(0), 0);
    assert_eq!(f(42), 42);
    assert_eq!(f(-1), -1);
    assert_eq!(f(i64::MAX), i64::MAX);
    assert_eq!(f(i64::MIN), i64::MIN);
}

// ---------------------------------------------------------------------------
// Test: factorial (loop)
// ---------------------------------------------------------------------------

#[test]
fn test_jit_factorial() {
    let jit = JitCompiler::new(JitConfig::default());
    let func = build_factorial();
    let ext: HashMap<String, *const u8> = HashMap::new();

    let buf = jit
        .compile_raw(&[func], &ext)
        .expect("compile_raw should succeed");

    let f: extern "C" fn(i64) -> i64 = unsafe {
        buf.get_fn("factorial")
            .expect("should find 'factorial' symbol")
    };

    assert_eq!(f(0), 1);
    assert_eq!(f(1), 1);
    assert_eq!(f(5), 120);
    assert_eq!(f(10), 3_628_800);
    assert_eq!(f(20), 2_432_902_008_176_640_000);
}

// ---------------------------------------------------------------------------
// Test: multiple functions in one compilation unit
// ---------------------------------------------------------------------------

#[test]
fn test_jit_multiple_functions() {
    let jit = JitCompiler::new(JitConfig::default());
    let funcs = vec![build_add(), build_sub(), build_mul(), build_return_const()];
    let ext: HashMap<String, *const u8> = HashMap::new();

    let buf = jit
        .compile_raw(&funcs, &ext)
        .expect("compile_raw should succeed");

    assert!(
        buf.symbol_count() >= 4,
        "should have at least 4 symbols, got {}",
        buf.symbol_count()
    );

    let add: extern "C" fn(i64, i64) -> i64 = unsafe { buf.get_fn("add").expect("add") };
    let sub: extern "C" fn(i64, i64) -> i64 = unsafe { buf.get_fn("sub").expect("sub") };
    let mul: extern "C" fn(i64, i64) -> i64 = unsafe { buf.get_fn("mul").expect("mul") };
    let rc: extern "C" fn() -> i64 = unsafe { buf.get_fn("return_const").expect("return_const") };

    assert_eq!(add(10, 20), 30);
    assert_eq!(sub(10, 3), 7);
    assert_eq!(mul(6, 7), 42);
    assert_eq!(rc(), 42);
}

// ---------------------------------------------------------------------------
// Test: cross-function BL call (caller -> callee within same compilation)
// ---------------------------------------------------------------------------

#[test]
fn test_jit_cross_function_bl() {
    let jit = JitCompiler::new(JitConfig::default());

    // callee: add(a, b) -> a + b
    let callee = build_add();
    // caller: calls "add" via BL symbol, forwarding args
    let caller = build_caller("call_add", "add");

    let ext: HashMap<String, *const u8> = HashMap::new();
    let buf = jit
        .compile_raw(&[callee, caller], &ext)
        .expect("compile_raw should succeed with cross-function BL");

    let f: extern "C" fn(i64, i64) -> i64 = unsafe {
        buf.get_fn("call_add")
            .expect("should find 'call_add' symbol")
    };

    assert_eq!(f(10, 20), 30);
    assert_eq!(f(0, 0), 0);
    assert_eq!(f(-5, 5), 0);
}

#[test]
fn test_jit_forward_named_bl_patches_to_callee_not_self() {
    let jit = JitCompiler::new(JitConfig::default());

    let caller = build_caller("call_forward_add", "add");
    let callee = build_add();

    let ext: HashMap<String, *const u8> = HashMap::new();
    let buf = jit
        .compile_raw(&[caller, callee], &ext)
        .expect("compile_raw should patch forward named BL to callee");

    let caller_ptr = buf
        .get_fn_ptr_bound("call_forward_add")
        .expect("call_forward_add")
        .as_ptr();
    let callee_ptr = buf.get_fn_ptr_bound("add").expect("add").as_ptr();

    let bl_site = unsafe { caller_ptr.add(4) };
    let bl_target = decode_aarch64_bl_target(bl_site);
    assert_ne!(
        bl_target, bl_site as usize,
        "forward named BL kept imm26=0 and would self-call at {bl_site:p}"
    );
    assert_eq!(
        bl_target, callee_ptr as usize,
        "forward named BL should target callee"
    );

    let f: extern "C" fn(i64, i64) -> i64 = unsafe {
        buf.get_fn_bound("call_forward_add")
            .expect("call_forward_add")
            .into_inner()
    };
    assert_eq!(f(13, 29), 42);
    assert_eq!(f(-7, 7), 0);
}

fn build_trust_ir_forward_direct_call_module() -> trust_ir::Module {
    use trust_ir::{
        BinOp, Block as TrustIrBlock, BlockId, FuncId, FuncTy, Function as TrustIrFunction, Inst,
        InstrNode, Module as TrustIrModule, Ty, ValueId,
    };

    let mut module = TrustIrModule::new("jit_trust_ir_forward_direct_call");
    let sig = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let mut caller = TrustIrFunction::new(
        FuncId::new(0),
        "trust_ir_forward_direct_call",
        sig,
        BlockId::new(0),
    );
    caller.blocks.push(TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![ValueId::new(0), ValueId::new(1)],
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    });

    let mut callee =
        TrustIrFunction::new(FuncId::new(1), "trust_ir_forward_add", sig, BlockId::new(0));
    callee.blocks.push(TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    });

    module.add_function(caller);
    module.add_function(callee);
    module
}

#[test]
fn test_jit_trust_ir_forward_direct_call_patches_regalloc_preserved_symbol() {
    let module = build_trust_ir_forward_direct_call_module();
    let ext: HashMap<String, *const u8> = HashMap::new();
    let buf = compile_trust_ir_module_with_ty_o1_pipeline(&module, &ext)
        .expect("TY-like O1 pipeline should preserve direct-call relocation symbols");

    let caller_ptr = buf
        .get_fn_ptr_bound("trust_ir_forward_direct_call")
        .expect("trust_ir_forward_direct_call")
        .as_ptr();
    let callee_ptr = buf
        .get_fn_ptr_bound("trust_ir_forward_add")
        .expect("trust_ir_forward_add")
        .as_ptr();

    let bl_site = find_first_aarch64_bl_site(caller_ptr, 256)
        .expect("trust_ir_forward_direct_call should contain a direct BL");
    let bl_target = decode_aarch64_bl_target(bl_site);
    assert_ne!(
        bl_target, bl_site as usize,
        "pipeline direct BL kept imm26=0 after regalloc and would self-call at {bl_site:p}"
    );
    assert_eq!(
        bl_target, callee_ptr as usize,
        "pipeline direct BL should target the callee symbol"
    );

    let f: extern "C" fn(i64, i64) -> i64 = unsafe {
        buf.get_fn_bound("trust_ir_forward_direct_call")
            .expect("trust_ir_forward_direct_call")
            .into_inner()
    };
    assert_eq!(f(13, 29), 42);
    assert_eq!(f(-7, 7), 0);
}

fn build_internal_helper_call_abi_retbuf_module() -> trust_ir::Module {
    use trust_ir::{
        BinOp, Block as TrustIrBlock, BlockId, CastOp, Constant, FuncId, FuncTy,
        Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, Ty, ValueId,
    };

    let mut module = TrustIrModule::new("jit_internal_helper_call_abi_retbuf");
    let helper_ty = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::U32, Ty::Ptr, Ty::I64],
        returns: vec![],
        is_vararg: false,
    });
    let caller_ty = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::U32],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let mut helper = TrustIrFunction::new(
        FuncId::new(0),
        "internal_helper_write_retbuf",
        helper_ty,
        BlockId::new(0),
    );
    helper.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::Ptr),
            (ValueId::new(1), Ty::Ptr),
            (ValueId::new(2), Ty::Ptr),
            (ValueId::new(3), Ty::U32),
            (ValueId::new(4), Ty::Ptr),
            (ValueId::new(5), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: ValueId::new(4),
                value: ValueId::new(5),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: ValueId::new(4),
                indices: vec![ValueId::new(6)],
                inbounds: false,
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::U32,
                dst_ty: Ty::I64,
                operand: ValueId::new(3),
            })
            .with_result(ValueId::new(8)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: ValueId::new(7),
                value: ValueId::new(8),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];

    let mut caller = TrustIrFunction::new(
        FuncId::new(1),
        "call_internal_helper_retbuf",
        caller_ty,
        BlockId::new(0),
    );
    caller.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::Ptr),
            (ValueId::new(1), Ty::Ptr),
            (ValueId::new(2), Ty::Ptr),
            (ValueId::new(3), Ty::U32),
        ],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(2),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: Some(ValueId::new(4)),
                align: None,
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(11),
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![
                    ValueId::new(0),
                    ValueId::new(1),
                    ValueId::new(2),
                    ValueId::new(3),
                    ValueId::new(5),
                    ValueId::new(6),
                ],
            }),
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(5),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(8)),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: ValueId::new(5),
                indices: vec![ValueId::new(8)],
                inbounds: false,
            })
            .with_result(ValueId::new(9)),
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(9),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(10)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1000),
            })
            .with_result(ValueId::new(11)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: ValueId::new(7),
                rhs: ValueId::new(11),
            })
            .with_result(ValueId::new(12)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(12),
                rhs: ValueId::new(10),
            })
            .with_result(ValueId::new(13)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(13)],
            }),
        ],
    }];

    module.add_function(helper);
    module.add_function(caller);
    module
}

#[test]
fn test_jit_internal_helper_call_abi_retbuf_after_u32() {
    let module = build_internal_helper_call_abi_retbuf_module();
    let ext: HashMap<String, *const u8> = HashMap::new();
    let buf = compile_trust_ir_module_with_ty_o1_pipeline(&module, &ext)
        .expect("TY-like O1 pipeline should compile internal helper call ABI case");

    let f: extern "C" fn(*mut i64, *mut i64, *mut i64, u32) -> i64 = unsafe {
        buf.get_fn_bound("call_internal_helper_retbuf")
            .expect("call_internal_helper_retbuf symbol")
            .into_inner()
    };

    let mut a = 0_i64;
    let mut b = 0_i64;
    let mut c = 0_i64;

    assert_eq!(f(&mut a, &mut b, &mut c, 0), 11_000);
    assert_eq!(f(&mut a, &mut b, &mut c, 7), 11_007);
    assert_eq!(f(&mut a, &mut b, &mut c, 123), 11_123);
}

#[test]
fn test_jit_internal_helper_call_abi_retbuf_after_u32_o2() {
    let module = build_internal_helper_call_abi_retbuf_module();
    let ext: HashMap<String, *const u8> = HashMap::new();
    let buf = compile_trust_ir_module_with_ty_pipeline(&module, &ext, OptLevel::O2)
        .expect("TY-like O2 pipeline should compile internal helper call ABI case");

    let f: extern "C" fn(*mut i64, *mut i64, *mut i64, u32) -> i64 = unsafe {
        buf.get_fn_bound("call_internal_helper_retbuf")
            .expect("call_internal_helper_retbuf symbol")
            .into_inner()
    };

    let mut a = 0_i64;
    let mut b = 0_i64;
    let mut c = 0_i64;

    assert_eq!(f(&mut a, &mut b, &mut c, 0), 11_000);
    assert_eq!(f(&mut a, &mut b, &mut c, 7), 11_007);
    assert_eq!(f(&mut a, &mut b, &mut c, 123), 11_123);
}

// ---------------------------------------------------------------------------
// Test: cross-function BL with underscore-prefixed symbol resolution
// ---------------------------------------------------------------------------

#[test]
fn test_jit_cross_function_bl_underscore_prefix() {
    let jit = JitCompiler::new(JitConfig::default());

    // callee: add(a, b) -> a + b  (registered as both "add" and "_add")
    let callee = build_add();
    // caller: calls "_add" via BL symbol (Mach-O mangling prefix)
    let caller = build_caller("call_add_mangled", "_add");

    let ext: HashMap<String, *const u8> = HashMap::new();
    let buf = jit
        .compile_raw(&[callee, caller], &ext)
        .expect("compile_raw should succeed with _-prefixed symbol");

    let f: extern "C" fn(i64, i64) -> i64 = unsafe {
        buf.get_fn("call_add_mangled")
            .expect("should find 'call_add_mangled' symbol")
    };

    assert_eq!(f(7, 8), 15);
}

// ---------------------------------------------------------------------------
// Test: external symbol resolution via veneer trampolines
// ---------------------------------------------------------------------------

/// A native helper function used as an external symbol for JIT tests.
/// add_ten(x) -> x + 10
extern "C" fn host_add_ten(x: i64) -> i64 {
    x + 10
}

extern "C" fn host_direct_named_alias_shadow(x: i64) -> i64 {
    x + 9999
}

/// Build a function that calls an external symbol.
///
/// `fn call_extern(a: i64) -> i64 { callee_symbol(a) }`
///
/// Includes STP/LDP prologue/epilogue to save/restore LR around the BL.
fn build_extern_caller(callee_symbol: &str) -> MachFunction {
    let sig = Signature::new(vec![Type::I64], vec![Type::I64]);
    let mut func = MachFunction::new("call_extern".to_string(), sig);
    let entry = func.entry;

    // STP FP, LR, [SP, #-16]!
    let stp = MachInst::new(
        AArch64Opcode::StpPreIndex,
        vec![
            MachOperand::PReg(FP),
            MachOperand::PReg(LR),
            Special(SpecialReg::SP),
            MachOperand::Imm(-16),
        ],
    );
    let stp_id = func.push_inst(stp);
    func.append_inst(entry, stp_id);

    // BL <external symbol>
    let bl = MachInst::new(
        AArch64Opcode::Bl,
        vec![MachOperand::Symbol(callee_symbol.to_string())],
    );
    let bl_id = func.push_inst(bl);
    func.append_inst(entry, bl_id);

    // LDP FP, LR, [SP], #16
    let ldp = MachInst::new(
        AArch64Opcode::LdpPostIndex,
        vec![
            MachOperand::PReg(FP),
            MachOperand::PReg(LR),
            Special(SpecialReg::SP),
            MachOperand::Imm(16),
        ],
    );
    let ldp_id = func.push_inst(ldp);
    func.append_inst(entry, ldp_id);

    // RET
    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    let ret_id = func.push_inst(ret);
    func.append_inst(entry, ret_id);

    func
}

#[test]
fn test_jit_external_symbol_veneer() {
    let jit = JitCompiler::new(JitConfig::default());
    let caller = build_extern_caller("_host_add_ten");

    let mut ext: HashMap<String, *const u8> = HashMap::new();
    ext.insert("_host_add_ten".to_string(), host_add_ten as *const u8);

    let buf = jit
        .compile_raw(&[caller], &ext)
        .expect("compile_raw should succeed with external symbol");

    let f: extern "C" fn(i64) -> i64 = unsafe {
        buf.get_fn("call_extern")
            .expect("should find 'call_extern' symbol")
    };

    assert_eq!(f(0), 10);
    assert_eq!(f(32), 42);
    assert_eq!(f(-10), 0);
    assert_eq!(f(100), 110);
}

#[test]
fn test_jit_named_external_symbol_preferred_over_generated_internal_alias() {
    let jit = JitCompiler::new(JitConfig::default());

    let mut internal = build_identity();
    internal.name = "trust_cg_jit_alias_shadow_target".to_string();
    let external_symbol = "_trust_cg_jit_alias_shadow_target";
    let caller = build_extern_caller(external_symbol);

    let mut ext: HashMap<String, *const u8> = HashMap::new();
    ext.insert(
        external_symbol.to_string(),
        host_direct_named_alias_shadow as *const u8,
    );

    let buf = jit
        .compile_raw(&[internal, caller], &ext)
        .expect("external symbol should not be shadowed by generated alias");

    let internal_alias: extern "C" fn(i64) -> i64 = unsafe {
        buf.get_fn(external_symbol)
            .expect("generated internal alias should remain lookup-compatible")
    };
    assert_eq!(internal_alias(7), 7);

    let f: extern "C" fn(i64) -> i64 = unsafe {
        buf.get_fn("call_extern")
            .expect("should find 'call_extern' symbol")
    };
    assert_eq!(f(0), 9999);
    assert_eq!(f(1), 10000);
}

// ---------------------------------------------------------------------------
// Test: trust_ir CallIndirect through a raw Rust callback pointer
// ---------------------------------------------------------------------------

const HOST_WRITE_MAGIC: u64 = 0xC0DE_CAFE_1234_5678;
const HOST_WRITE_RET: u64 = 0xABCD_EF01_2345_6789;

extern "C" fn host_write_magic(out: *mut u64) -> u64 {
    unsafe {
        *out = HOST_WRITE_MAGIC;
    }
    HOST_WRITE_RET
}

fn build_call_raw_callback_module() -> trust_ir::Module {
    use trust_ir::Ty;
    use trust_ir_build::ModuleBuilder;

    let mut mb = ModuleBuilder::new("jit_call_indirect_raw_callback");
    let callback_ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
    let entry_ty = mb.add_func_type(vec![Ty::Func(callback_ty), Ty::Ptr], vec![Ty::I64]);

    {
        let mut fb = mb.function("call_raw_callback", entry_ty);
        let entry = fb.create_block();
        let raw_callback = fb.add_block_param(entry, Ty::Func(callback_ty));
        let out = fb.add_block_param(entry, Ty::Ptr);

        fb.switch_to_block(entry);
        let returned = fb.call_indirect(raw_callback, callback_ty, vec![out]);
        fb.ret(vec![returned]);
        fb.build();
    }

    mb.build()
}

#[test]
fn test_jit_call_indirect_raw_callback_writes_through_pointer() {
    let module = build_call_raw_callback_module();
    let compiler = Compiler::jit_fast(Target::Aarch64);
    let ext: HashMap<String, *const u8> = HashMap::new();
    let result = compiler
        .compile_module_to_jit(&module, &ext)
        .expect("compile_module_to_jit should succeed for raw callback");

    let call_raw_callback: extern "C" fn(u64, *mut u64) -> u64 = unsafe {
        result
            .buffer
            .get_fn_bound("call_raw_callback")
            .expect("call_raw_callback symbol")
            .into_inner()
    };

    let raw_callback = host_write_magic as *const () as usize as u64;
    let mut observed = 0_u64;
    let returned = call_raw_callback(raw_callback, &mut observed);

    assert_eq!(returned, HOST_WRITE_RET);
    assert_eq!(observed, HOST_WRITE_MAGIC);
}

// ---------------------------------------------------------------------------
// Test: trust_ir CallIndirect through a TY-like callout callback
// ---------------------------------------------------------------------------

const CALLOUT_STATUS_RUNTIME_ERROR: i64 = 1;
const CALLOUT_STATUS_OK: u8 = 0;
const CALLOUT_VALUE_ENABLED: i64 = 1;

#[repr(C)]
#[derive(Default)]
struct TestCallout {
    status: u8,
    _pad: [u8; 7],
    value: i64,
}

static CALLOUT_ACTION_CALLS: AtomicUsize = AtomicUsize::new(0);
static CALLOUT_ACTION_STATE_IN_VALUE: AtomicUsize = AtomicUsize::new(0);
static CALLOUT_ACTION_STATE_OUT: AtomicUsize = AtomicUsize::new(0);
static CALLOUT_ACTION_LEN: AtomicU32 = AtomicU32::new(0);
static STACK_CALLOUT_ACTION_CALLS: AtomicUsize = AtomicUsize::new(0);
static STACK_CALLOUT_ACTION_STATE_IN_VALUE: AtomicUsize = AtomicUsize::new(0);
static STACK_CALLOUT_ACTION_STATE_OUT: AtomicUsize = AtomicUsize::new(0);
static STACK_CALLOUT_ACTION_LEN: AtomicU32 = AtomicU32::new(0);
static MINI_BFS_CALLOUT_ACTION_CALLS: AtomicUsize = AtomicUsize::new(0);
static MINI_BFS_CALLOUT_ACTION_STATE_IN_VALUE: AtomicUsize = AtomicUsize::new(0);
static MINI_BFS_CALLOUT_ACTION_STATE_OUT: AtomicUsize = AtomicUsize::new(0);
static MINI_BFS_CALLOUT_ACTION_LEN: AtomicU32 = AtomicU32::new(0);
static MINI_BFS_CALLOUT_ACTION_LOCK: Mutex<()> = Mutex::new(());

fn lock_mini_bfs_callout_action() -> MutexGuard<'static, ()> {
    MINI_BFS_CALLOUT_ACTION_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}
static LOOP_LIVEIN_CALLOUT_ACTION_CALLS: AtomicUsize = AtomicUsize::new(0);
static LOOP_LIVEIN_CALLOUT_LAST_IDX: AtomicUsize = AtomicUsize::new(0);
static LOOP_LIVEIN_CALLOUT_LAST_COUNT: AtomicUsize = AtomicUsize::new(0);
static LOOP_LIVEIN_CALLOUT_LAST_SENTINEL: AtomicUsize = AtomicUsize::new(0);
static LOOP_LIVEIN_CALLOUT_STATE_OUT: AtomicUsize = AtomicUsize::new(0);

extern "C" fn host_trust_ir_like_callout_action(
    out: *mut TestCallout,
    state_in: *const i64,
    state_out: *mut i64,
    len: u32,
) {
    CALLOUT_ACTION_CALLS.fetch_add(1, Ordering::SeqCst);
    CALLOUT_ACTION_STATE_OUT.store(state_out as usize, Ordering::SeqCst);
    CALLOUT_ACTION_LEN.store(len, Ordering::SeqCst);

    unsafe {
        if !state_in.is_null() {
            CALLOUT_ACTION_STATE_IN_VALUE.store(*state_in as usize, Ordering::SeqCst);
        }
        if !state_out.is_null() && !state_in.is_null() && len != 0 {
            *state_out = *state_in + 32;
        }
        if !out.is_null() {
            (*out).status = CALLOUT_STATUS_OK;
            (*out).value = CALLOUT_VALUE_ENABLED;
        }
    }
}

extern "C" fn host_trust_ir_like_stack_callout_action(
    out: *mut TestCallout,
    state_in: *const i64,
    state_out: *mut i64,
    len: u32,
) {
    STACK_CALLOUT_ACTION_CALLS.fetch_add(1, Ordering::SeqCst);
    STACK_CALLOUT_ACTION_STATE_OUT.store(state_out as usize, Ordering::SeqCst);
    STACK_CALLOUT_ACTION_LEN.store(len, Ordering::SeqCst);

    unsafe {
        if !state_in.is_null() {
            STACK_CALLOUT_ACTION_STATE_IN_VALUE.store(*state_in as usize, Ordering::SeqCst);
        }
        if !state_out.is_null() && !state_in.is_null() && len != 0 {
            *state_out = *state_in + 32;
        }
        if !out.is_null() {
            (*out).status = CALLOUT_STATUS_OK;
            (*out).value = CALLOUT_VALUE_ENABLED;
        }
    }
}

extern "C" fn host_trust_ir_like_mini_bfs_callout_action(
    out: *mut TestCallout,
    state_in: *const i64,
    state_out: *mut i64,
    len: u32,
) {
    MINI_BFS_CALLOUT_ACTION_CALLS.fetch_add(1, Ordering::SeqCst);
    MINI_BFS_CALLOUT_ACTION_STATE_OUT.store(state_out as usize, Ordering::SeqCst);
    MINI_BFS_CALLOUT_ACTION_LEN.store(len, Ordering::SeqCst);

    unsafe {
        if !state_in.is_null() {
            MINI_BFS_CALLOUT_ACTION_STATE_IN_VALUE.store(*state_in as usize, Ordering::SeqCst);
        }
        if !state_out.is_null() {
            *state_out = 42;
        }
        if !out.is_null() {
            (*out).status = CALLOUT_STATUS_OK;
            (*out).value = CALLOUT_VALUE_ENABLED;
        }
    }
}

extern "C" fn host_loop_livein_callout_action(
    state_out: *mut i64,
    state_in: *const i64,
    idx: u64,
    count: u64,
    a: u64,
    b: u64,
    c: u64,
    d: u64,
) {
    LOOP_LIVEIN_CALLOUT_ACTION_CALLS.fetch_add(1, Ordering::SeqCst);
    LOOP_LIVEIN_CALLOUT_LAST_IDX.store(idx as usize, Ordering::SeqCst);
    LOOP_LIVEIN_CALLOUT_LAST_COUNT.store(count as usize, Ordering::SeqCst);
    LOOP_LIVEIN_CALLOUT_LAST_SENTINEL.store((a + b + c + d) as usize, Ordering::SeqCst);
    LOOP_LIVEIN_CALLOUT_STATE_OUT.store(state_out as usize, Ordering::SeqCst);

    unsafe {
        if !state_out.is_null() && !state_in.is_null() {
            *state_out = *state_in + idx as i64 + count as i64 + (a + b + c + d) as i64;
        }
    }
}

#[inline(never)]
extern "C" fn host_clobber_call_volatile_registers() {
    unsafe {
        core::arch::asm!(
            "mov x0, #1",
            "mov x1, #2",
            "mov x2, #3",
            "mov x3, #4",
            "mov x4, #5",
            "mov x5, #6",
            "mov x6, #7",
            "mov x7, #8",
            "mov x8, #9",
            "mov x9, #10",
            "mov x10, #11",
            "mov x11, #12",
            "mov x12, #13",
            "mov x13, #14",
            "mov x14, #15",
            "mov x15, #16",
            "mov x16, #17",
            "mov x17, #18",
            out("x0") _,
            out("x1") _,
            out("x2") _,
            out("x3") _,
            out("x4") _,
            out("x5") _,
            out("x6") _,
            out("x7") _,
            out("x8") _,
            out("x9") _,
            out("x10") _,
            out("x11") _,
            out("x12") _,
            out("x13") _,
            out("x14") _,
            out("x15") _,
            out("x16") _,
            out("x17") _,
            options(nostack)
        );
    }
}

fn volatile_clobber_checksum(seed: u64) -> u64 {
    (0..24_u64)
        .map(|lane| {
            let value = seed.wrapping_add(0x1f1f_0101_u64.wrapping_mul(lane + 1));
            value.wrapping_mul(lane + 3)
        })
        .fold(0_u64, u64::wrapping_add)
}

fn build_indirect_call_live_values_survive_volatile_clobber_module() -> trust_ir::Module {
    use trust_ir::{BinOp, CastOp, Ty};
    use trust_ir_build::ModuleBuilder;

    let mut mb = ModuleBuilder::new("jit_indirect_call_live_values_survive_volatile_clobber");
    let callback_ty = mb.add_func_type(vec![], vec![]);
    let entry_ty = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);

    {
        let mut fb = mb.function("live_values_survive_volatile_clobber", entry_ty);
        let entry = fb.create_block();
        let seed = fb.add_block_param(entry, Ty::U64);

        fb.switch_to_block(entry);

        let mut live_values = Vec::new();
        for lane in 0..24_u64 {
            let offset = fb.iconst(Ty::U64, i128::from(0x1f1f_0101_u64.wrapping_mul(lane + 1)));
            let biased = fb.binop(BinOp::Add, Ty::U64, seed, offset);
            let multiplier = fb.iconst(Ty::U64, i128::from(lane + 3));
            live_values.push(fb.binop(BinOp::Mul, Ty::U64, biased, multiplier));
        }

        let callback_addr = fb.iconst(
            Ty::U64,
            host_clobber_call_volatile_registers as *const () as usize as i128,
        );
        let callback_ptr = fb.cast(
            CastOp::IntToPtr,
            Ty::U64,
            Ty::Func(callback_ty),
            callback_addr,
        );
        fb.call_indirect_void(callback_ptr, callback_ty, vec![]);

        let mut acc = fb.iconst(Ty::U64, 0);
        for value in live_values {
            acc = fb.binop(BinOp::Add, Ty::U64, acc, value);
        }
        fb.ret(vec![acc]);
        fb.build();
    }

    mb.build()
}

fn build_trust_ir_like_callout_indirect_module() -> trust_ir::Module {
    use trust_ir::{BinOp, CastOp, Ty};
    use trust_ir_build::ModuleBuilder;

    let mut mb = ModuleBuilder::new("jit_call_indirect_trust_ir_like_callout");
    let callback_ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::U32], vec![]);
    let entry_ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::U32], vec![Ty::I64]);

    {
        let mut fb = mb.function("call_trust_ir_like_callout", entry_ty);
        let entry = fb.create_block();
        let out = fb.add_block_param(entry, Ty::Ptr);
        let state_in = fb.add_block_param(entry, Ty::Ptr);
        let state_out = fb.add_block_param(entry, Ty::Ptr);
        let len = fb.add_block_param(entry, Ty::U32);

        fb.switch_to_block(entry);

        let callback_addr = fb.iconst(
            Ty::U64,
            host_trust_ir_like_callout_action as *const () as usize as i128,
        );
        let callback_ptr = fb.cast(
            CastOp::IntToPtr,
            Ty::U64,
            Ty::Func(callback_ty),
            callback_addr,
        );

        let runtime_error = fb.iconst(Ty::I64, CALLOUT_STATUS_RUNTIME_ERROR as i128);
        fb.store(Ty::I64, out, runtime_error);

        let zero_idx = fb.iconst(Ty::U64, 0);
        let one_idx = fb.iconst(Ty::U64, 1);
        let value_ptr = fb.gep(Ty::I64, out, vec![one_idx]);
        fb.store(Ty::I64, value_ptr, zero_idx);

        fb.call_indirect_void(
            callback_ptr,
            callback_ty,
            vec![out, state_in, state_out, len],
        );

        let status = fb.load(Ty::U8, out);
        let status_i64 = fb.cast(CastOp::ZExt, Ty::U8, Ty::I64, status);
        let value = fb.load(Ty::I64, value_ptr);
        let status_scaled_by_reset = fb.binop(BinOp::Mul, Ty::I64, status_i64, runtime_error);
        let result = fb.binop(BinOp::Add, Ty::I64, value, status_scaled_by_reset);
        fb.ret(vec![result]);
        fb.build();
    }

    mb.build()
}

fn build_direct_call_retbuf_live_across_call_module() -> trust_ir::Module {
    use trust_ir::{
        Block as TrustIrBlock, BlockId, CastOp, Constant, FuncId, FuncTy,
        Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, Ty, ValueId,
    };

    let mut module = TrustIrModule::new("jit_direct_call_retbuf_live_across_call");
    let entry_ty = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let helper_ty = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr, Ty::I32, Ty::Ptr],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let mut entry = TrustIrFunction::new(
        FuncId::new(0),
        "direct_call_retbuf_live_across_call",
        entry_ty,
        BlockId::new(0),
    );
    entry.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(5),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: Some(ValueId::new(1)),
                align: None,
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![
                    ValueId::new(0),
                    ValueId::new(0),
                    ValueId::new(3),
                    ValueId::new(2),
                ],
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::I64,
                operand: ValueId::new(2),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: Ty::I64,
                dst_ty: Ty::Ptr,
                operand: ValueId::new(5),
            })
            .with_result(ValueId::new(6)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: ValueId::new(6),
                indices: vec![ValueId::new(7)],
                inbounds: false,
            })
            .with_result(ValueId::new(8)),
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(8),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(9)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(9)],
            }),
        ],
    }];
    module.add_function(entry);

    let mut helper = TrustIrFunction::new(
        FuncId::new(1),
        "direct_call_retbuf_helper",
        helper_ty,
        BlockId::new(1),
    );
    helper.blocks = vec![TrustIrBlock {
        id: BlockId::new(1),
        params: vec![
            (ValueId::new(10), Ty::Ptr),
            (ValueId::new(11), Ty::Ptr),
            (ValueId::new(12), Ty::I32),
            (ValueId::new(13), Ty::Ptr),
        ],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(ValueId::new(14)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(15)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(4),
            })
            .with_result(ValueId::new(16)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(31),
            })
            .with_result(ValueId::new(17)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(20)),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: ValueId::new(13),
                indices: vec![ValueId::new(14)],
                inbounds: false,
            })
            .with_result(ValueId::new(18)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: ValueId::new(18),
                value: ValueId::new(16),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I64,
                base: ValueId::new(13),
                indices: vec![ValueId::new(15)],
                inbounds: false,
            })
            .with_result(ValueId::new(19)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: ValueId::new(19),
                value: ValueId::new(17),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(20)],
            }),
        ],
    }];
    module.add_function(helper);

    module
}

#[test]
fn test_jit_call_indirect_trust_ir_like_void_callout_updates_memory() {
    CALLOUT_ACTION_CALLS.store(0, Ordering::SeqCst);
    CALLOUT_ACTION_STATE_IN_VALUE.store(0, Ordering::SeqCst);
    CALLOUT_ACTION_STATE_OUT.store(0, Ordering::SeqCst);
    CALLOUT_ACTION_LEN.store(0, Ordering::SeqCst);

    let ext: HashMap<String, *const u8> = HashMap::new();
    let module = build_trust_ir_like_callout_indirect_module();
    let buffer = compile_trust_ir_module_with_ty_o1_pipeline(&module, &ext)
        .expect("TY-like O1 pipeline should compile trust_ir-like callout");

    let call_trust_ir_like_callout: extern "C" fn(
        *mut TestCallout,
        *const i64,
        *mut i64,
        u32,
    ) -> i64 = unsafe {
        buffer
            .get_fn_bound("call_trust_ir_like_callout")
            .expect("call_trust_ir_like_callout symbol")
            .into_inner()
    };

    let mut callout = TestCallout {
        status: 77,
        _pad: [0xAA; 7],
        value: 99,
    };
    let state_in = [10_i64];
    let mut state_out = [0_i64];

    let returned = call_trust_ir_like_callout(
        &mut callout,
        state_in.as_ptr(),
        state_out.as_mut_ptr(),
        state_in.len() as u32,
    );

    assert_eq!(returned, CALLOUT_VALUE_ENABLED);
    assert_eq!(callout.status, CALLOUT_STATUS_OK);
    assert_eq!(callout.value, CALLOUT_VALUE_ENABLED);
    assert_eq!(state_out, [42]);
    assert_eq!(CALLOUT_ACTION_CALLS.load(Ordering::SeqCst), 1);
    assert_eq!(CALLOUT_ACTION_STATE_IN_VALUE.load(Ordering::SeqCst), 10);
    assert_eq!(
        CALLOUT_ACTION_STATE_OUT.load(Ordering::SeqCst),
        state_out.as_ptr() as usize
    );
    assert_eq!(CALLOUT_ACTION_LEN.load(Ordering::SeqCst), 1);
}

fn build_trust_ir_like_stack_callout_indirect_module() -> trust_ir::Module {
    use trust_ir::{
        BinOp, Block as TrustIrBlock, BlockId, CastOp, Constant, FuncId, FuncTy,
        Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, Ty, ValueId,
    };

    let mut module = TrustIrModule::new("jit_call_indirect_trust_ir_like_stack_callout");
    let callback_ty = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::U32],
        returns: vec![],
        is_vararg: false,
    });
    let entry_ty = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr, Ty::U32],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let entry = BlockId::new(0);
    let state_in = ValueId::new(0);
    let state_out = ValueId::new(1);
    let len = ValueId::new(2);
    let mut block = TrustIrBlock::new(entry)
        .with_param(state_in, Ty::Ptr)
        .with_param(state_out, Ty::Ptr)
        .with_param(len, Ty::U32);

    let callout_words = ValueId::new(3);
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(5),
        })
        .with_result(callout_words),
    );

    let callout = ValueId::new(4);
    block.body.push(
        InstrNode::new(Inst::Alloca {
            ty: Ty::I64,
            count: Some(callout_words),
            align: None,
        })
        .with_result(callout),
    );

    let callback_addr = ValueId::new(5);
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(
                host_trust_ir_like_stack_callout_action as *const () as usize as i128,
            ),
        })
        .with_result(callback_addr),
    );

    let callback_ptr = ValueId::new(6);
    block.body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::IntToPtr,
            src_ty: Ty::U64,
            dst_ty: Ty::Func(callback_ty),
            operand: callback_addr,
        })
        .with_result(callback_ptr),
    );

    let runtime_error = ValueId::new(7);
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(CALLOUT_STATUS_RUNTIME_ERROR as i128),
        })
        .with_result(runtime_error),
    );
    block.body.push(InstrNode::new(Inst::Store {
        ty: Ty::I64,
        ptr: callout,
        value: runtime_error,
        volatile: false,
        align: None,
    }));

    let zero = ValueId::new(8);
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(0),
        })
        .with_result(zero),
    );
    let one = ValueId::new(9);
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(1),
        })
        .with_result(one),
    );
    let value_ptr = ValueId::new(10);
    block.body.push(
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::I64,
            base: callout,
            indices: vec![one],
            inbounds: false,
        })
        .with_result(value_ptr),
    );
    block.body.push(InstrNode::new(Inst::Store {
        ty: Ty::I64,
        ptr: value_ptr,
        value: zero,
        volatile: false,
        align: None,
    }));

    block.body.push(InstrNode::new(Inst::CallIndirect {
        callee: callback_ptr,
        sig: callback_ty,
        args: vec![callout, state_in, state_out, len],
        calling_conv: trust_ir::CallingConv::C,
    }));

    let status = ValueId::new(11);
    block.body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::U8,
            ptr: callout,
            volatile: false,
            align: None,
        })
        .with_result(status),
    );
    let status_i64 = ValueId::new(12);
    block.body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::U8,
            dst_ty: Ty::I64,
            operand: status,
        })
        .with_result(status_i64),
    );
    let value = ValueId::new(13);
    block.body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::I64,
            ptr: value_ptr,
            volatile: false,
            align: None,
        })
        .with_result(value),
    );
    let result = ValueId::new(14);
    block.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: value,
            rhs: status_i64,
        })
        .with_result(result),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![result],
    }));

    let mut function = TrustIrFunction::new(
        FuncId::new(0),
        "call_trust_ir_like_stack_callout",
        entry_ty,
        entry,
    );
    function.blocks = vec![block];
    module.add_function(function);
    module
}

fn build_trust_ir_like_mini_bfs_callout_indirect_module() -> trust_ir::Module {
    use trust_ir::{
        BinOp, Block as TrustIrBlock, BlockId, CastOp, Constant, FuncId, FuncTy,
        Function as TrustIrFunction, ICmpOp, Inst, InstrNode, Module as TrustIrModule, Ty, ValueId,
    };

    fn value(next_value: &mut u32) -> ValueId {
        let value = ValueId::new(*next_value);
        *next_value += 1;
        value
    }

    fn push_result(block: &mut TrustIrBlock, next_value: &mut u32, inst: Inst) -> ValueId {
        let result = value(next_value);
        block.body.push(InstrNode::new(inst).with_result(result));
        result
    }

    fn push_void(block: &mut TrustIrBlock, inst: Inst) {
        block.body.push(InstrNode::new(inst));
    }

    fn iconst(block: &mut TrustIrBlock, next_value: &mut u32, ty: Ty, int: i128) -> ValueId {
        push_result(
            block,
            next_value,
            Inst::Const {
                ty,
                value: Constant::Int(int),
            },
        )
    }

    fn gep(
        block: &mut TrustIrBlock,
        next_value: &mut u32,
        pointee_ty: Ty,
        base: ValueId,
        index: ValueId,
    ) -> ValueId {
        push_result(
            block,
            next_value,
            Inst::GEP {
                pointee_ty,
                base,
                indices: vec![index],
                inbounds: false,
            },
        )
    }

    fn byte_gep(
        block: &mut TrustIrBlock,
        next_value: &mut u32,
        base: ValueId,
        offset: i128,
    ) -> ValueId {
        let offset = iconst(block, next_value, Ty::U64, offset);
        gep(block, next_value, Ty::U8, base, offset)
    }

    fn load(block: &mut TrustIrBlock, next_value: &mut u32, ty: Ty, ptr: ValueId) -> ValueId {
        push_result(
            block,
            next_value,
            Inst::Load {
                ty,
                ptr,
                volatile: false,
                align: None,
            },
        )
    }

    fn load_volatile(
        block: &mut TrustIrBlock,
        next_value: &mut u32,
        ty: Ty,
        ptr: ValueId,
    ) -> ValueId {
        push_result(
            block,
            next_value,
            Inst::Load {
                ty,
                ptr,
                volatile: false,
                align: None,
            },
        )
    }

    fn store(block: &mut TrustIrBlock, ty: Ty, ptr: ValueId, value: ValueId) {
        push_void(
            block,
            Inst::Store {
                ty,
                ptr,
                value,
                volatile: false,
                align: None,
            },
        );
    }

    fn store_volatile(block: &mut TrustIrBlock, ty: Ty, ptr: ValueId, value: ValueId) {
        push_void(
            block,
            Inst::Store {
                ty,
                ptr,
                value,
                volatile: false,
                align: None,
            },
        );
    }

    fn binop(
        block: &mut TrustIrBlock,
        next_value: &mut u32,
        op: BinOp,
        ty: Ty,
        lhs: ValueId,
        rhs: ValueId,
    ) -> ValueId {
        push_result(block, next_value, Inst::BinOp { op, ty, lhs, rhs })
    }

    fn icmp(
        block: &mut TrustIrBlock,
        next_value: &mut u32,
        op: ICmpOp,
        ty: Ty,
        lhs: ValueId,
        rhs: ValueId,
    ) -> ValueId {
        push_result(block, next_value, Inst::ICmp { op, ty, lhs, rhs })
    }

    let mut module = TrustIrModule::new("jit_call_indirect_trust_ir_like_mini_bfs");
    let callback_ty = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::U32],
        returns: vec![],
        is_vararg: false,
    });
    let entry_ty = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr, Ty::U64],
        returns: vec![Ty::U64],
        is_vararg: false,
    });

    let entry_id = BlockId::new(0);
    let header_id = BlockId::new(1);
    let copy_id = BlockId::new(2);
    let after_call_id = BlockId::new(3);
    let value_check_id = BlockId::new(4);
    let enabled_id = BlockId::new(5);
    let advance_id = BlockId::new(6);
    let done_id = BlockId::new(7);
    let error_id = BlockId::new(8);

    let mut next_value = 0;
    let parents = value(&mut next_value);
    let states = value(&mut next_value);
    let parent_count = value(&mut next_value);

    let mut entry = TrustIrBlock::new(entry_id)
        .with_param(parents, Ty::Ptr)
        .with_param(states, Ty::Ptr)
        .with_param(parent_count, Ty::U64);
    let callout_words = iconst(&mut entry, &mut next_value, Ty::U64, 5);
    let callout = push_result(
        &mut entry,
        &mut next_value,
        Inst::Alloca {
            ty: Ty::I64,
            count: Some(callout_words),
            align: None,
        },
    );
    let idx_ptr = push_result(
        &mut entry,
        &mut next_value,
        Inst::Alloca {
            ty: Ty::U64,
            count: None,
            align: None,
        },
    );
    let generated_ptr = push_result(
        &mut entry,
        &mut next_value,
        Inst::Alloca {
            ty: Ty::U64,
            count: None,
            align: None,
        },
    );
    let zero_u64 = iconst(&mut entry, &mut next_value, Ty::U64, 0);
    store(&mut entry, Ty::U64, idx_ptr, zero_u64);
    store(&mut entry, Ty::U64, generated_ptr, zero_u64);
    push_void(
        &mut entry,
        Inst::Br {
            target: header_id,
            args: vec![],
        },
    );

    let mut header = TrustIrBlock::new(header_id);
    let idx = load(&mut header, &mut next_value, Ty::U64, idx_ptr);
    let has_parent = icmp(
        &mut header,
        &mut next_value,
        ICmpOp::Ult,
        Ty::U64,
        idx,
        parent_count,
    );
    push_void(
        &mut header,
        Inst::CondBr {
            cond: has_parent,
            then_target: copy_id,
            then_args: vec![],
            else_target: done_id,
            else_args: vec![],
        },
    );

    let mut copy = TrustIrBlock::new(copy_id);
    let idx = load(&mut copy, &mut next_value, Ty::U64, idx_ptr);
    let parent_slot = gep(&mut copy, &mut next_value, Ty::I64, parents, idx);
    let parent_value = load(&mut copy, &mut next_value, Ty::I64, parent_slot);
    let state_slot = gep(&mut copy, &mut next_value, Ty::I64, states, idx);
    store(&mut copy, Ty::I64, state_slot, parent_value);
    push_void(
        &mut copy,
        Inst::Br {
            target: after_call_id,
            args: vec![],
        },
    );

    let mut after_call = TrustIrBlock::new(after_call_id);
    let idx = load(&mut after_call, &mut next_value, Ty::U64, idx_ptr);
    let parent_slot = gep(&mut after_call, &mut next_value, Ty::I64, parents, idx);
    let state_slot = gep(&mut after_call, &mut next_value, Ty::I64, states, idx);
    let callback_addr = iconst(
        &mut after_call,
        &mut next_value,
        Ty::U64,
        host_trust_ir_like_mini_bfs_callout_action as *const () as usize as i128,
    );
    let callback_ptr = push_result(
        &mut after_call,
        &mut next_value,
        Inst::Cast {
            op: CastOp::IntToPtr,
            src_ty: Ty::U64,
            dst_ty: Ty::Func(callback_ty),
            operand: callback_addr,
        },
    );
    let runtime_error = iconst(
        &mut after_call,
        &mut next_value,
        Ty::I64,
        CALLOUT_STATUS_RUNTIME_ERROR as i128,
    );
    store_volatile(&mut after_call, Ty::I64, callout, runtime_error);
    let value_ptr = byte_gep(&mut after_call, &mut next_value, callout, 8);
    let zero_i64 = iconst(&mut after_call, &mut next_value, Ty::I64, 0);
    store_volatile(&mut after_call, Ty::I64, value_ptr, zero_i64);
    let one_u32 = iconst(&mut after_call, &mut next_value, Ty::U32, 1);
    push_void(
        &mut after_call,
        Inst::CallIndirect {
            callee: callback_ptr,
            sig: callback_ty,
            args: vec![callout, parent_slot, state_slot, one_u32],
            calling_conv: trust_ir::CallingConv::C,
        },
    );
    let status = load_volatile(&mut after_call, &mut next_value, Ty::U8, callout);
    let status_u64 = push_result(
        &mut after_call,
        &mut next_value,
        Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::U8,
            dst_ty: Ty::U64,
            operand: status,
        },
    );
    let callout_value = load_volatile(&mut after_call, &mut next_value, Ty::I64, value_ptr);
    let zero_i64 = iconst(&mut after_call, &mut next_value, Ty::I64, 0);
    let value_is_zero = icmp(
        &mut after_call,
        &mut next_value,
        ICmpOp::Eq,
        Ty::I64,
        callout_value,
        zero_i64,
    );
    let ok_status = iconst(&mut after_call, &mut next_value, Ty::U64, 0);
    let status_ok = icmp(
        &mut after_call,
        &mut next_value,
        ICmpOp::Eq,
        Ty::U64,
        status_u64,
        ok_status,
    );
    push_void(
        &mut after_call,
        Inst::CondBr {
            cond: status_ok,
            then_target: value_check_id,
            then_args: vec![value_is_zero],
            else_target: error_id,
            else_args: vec![status_u64],
        },
    );

    let value_is_zero_param = value(&mut next_value);
    let mut value_check =
        TrustIrBlock::new(value_check_id).with_param(value_is_zero_param, Ty::Bool);
    push_void(
        &mut value_check,
        Inst::CondBr {
            cond: value_is_zero_param,
            then_target: advance_id,
            then_args: vec![],
            else_target: enabled_id,
            else_args: vec![],
        },
    );

    let mut enabled = TrustIrBlock::new(enabled_id);
    let generated = load(&mut enabled, &mut next_value, Ty::U64, generated_ptr);
    let one_u64 = iconst(&mut enabled, &mut next_value, Ty::U64, 1);
    let generated_next = binop(
        &mut enabled,
        &mut next_value,
        BinOp::Add,
        Ty::U64,
        generated,
        one_u64,
    );
    store(&mut enabled, Ty::U64, generated_ptr, generated_next);
    push_void(
        &mut enabled,
        Inst::Br {
            target: advance_id,
            args: vec![],
        },
    );

    let mut advance = TrustIrBlock::new(advance_id);
    let idx = load(&mut advance, &mut next_value, Ty::U64, idx_ptr);
    let one_u64 = iconst(&mut advance, &mut next_value, Ty::U64, 1);
    let idx_next = binop(
        &mut advance,
        &mut next_value,
        BinOp::Add,
        Ty::U64,
        idx,
        one_u64,
    );
    store(&mut advance, Ty::U64, idx_ptr, idx_next);
    push_void(
        &mut advance,
        Inst::Br {
            target: header_id,
            args: vec![],
        },
    );

    let mut done = TrustIrBlock::new(done_id);
    let generated = load(&mut done, &mut next_value, Ty::U64, generated_ptr);
    push_void(
        &mut done,
        Inst::Return {
            values: vec![generated],
        },
    );

    let error_status = value(&mut next_value);
    let mut error = TrustIrBlock::new(error_id).with_param(error_status, Ty::U64);
    let base = iconst(&mut error, &mut next_value, Ty::U64, 9_000);
    let result = binop(
        &mut error,
        &mut next_value,
        BinOp::Add,
        Ty::U64,
        base,
        error_status,
    );
    push_void(
        &mut error,
        Inst::Return {
            values: vec![result],
        },
    );

    let mut function = TrustIrFunction::new(
        FuncId::new(0),
        "call_trust_ir_like_mini_bfs",
        entry_ty,
        entry_id,
    );
    function.blocks = vec![
        entry,
        header,
        copy,
        after_call,
        value_check,
        enabled,
        advance,
        done,
        error,
    ];
    module.add_function(function);
    module
}

fn build_loop_livein_callout_indirect_module() -> trust_ir::Module {
    use trust_ir::{
        BinOp, Block as TrustIrBlock, BlockId, CastOp, Constant, FuncId, FuncTy,
        Function as TrustIrFunction, ICmpOp, Inst, InstrNode, Module as TrustIrModule, Ty, ValueId,
    };

    fn value(next_value: &mut u32) -> ValueId {
        let value = ValueId::new(*next_value);
        *next_value += 1;
        value
    }

    fn push_result(block: &mut TrustIrBlock, next_value: &mut u32, inst: Inst) -> ValueId {
        let result = value(next_value);
        block.body.push(InstrNode::new(inst).with_result(result));
        result
    }

    fn push_void(block: &mut TrustIrBlock, inst: Inst) {
        block.body.push(InstrNode::new(inst));
    }

    fn iconst(block: &mut TrustIrBlock, next_value: &mut u32, ty: Ty, int: i128) -> ValueId {
        push_result(
            block,
            next_value,
            Inst::Const {
                ty,
                value: Constant::Int(int),
            },
        )
    }

    fn load(block: &mut TrustIrBlock, next_value: &mut u32, ty: Ty, ptr: ValueId) -> ValueId {
        push_result(
            block,
            next_value,
            Inst::Load {
                ty,
                ptr,
                volatile: false,
                align: None,
            },
        )
    }

    fn store(block: &mut TrustIrBlock, ty: Ty, ptr: ValueId, stored: ValueId) {
        push_void(
            block,
            Inst::Store {
                ty,
                ptr,
                value: stored,
                volatile: false,
                align: None,
            },
        );
    }

    fn gep(
        block: &mut TrustIrBlock,
        next_value: &mut u32,
        pointee_ty: Ty,
        base: ValueId,
        index: ValueId,
    ) -> ValueId {
        push_result(
            block,
            next_value,
            Inst::GEP {
                pointee_ty,
                base,
                indices: vec![index],
                inbounds: false,
            },
        )
    }

    fn binop(
        block: &mut TrustIrBlock,
        next_value: &mut u32,
        op: BinOp,
        ty: Ty,
        lhs: ValueId,
        rhs: ValueId,
    ) -> ValueId {
        push_result(block, next_value, Inst::BinOp { op, ty, lhs, rhs })
    }

    fn icmp(
        block: &mut TrustIrBlock,
        next_value: &mut u32,
        op: ICmpOp,
        ty: Ty,
        lhs: ValueId,
        rhs: ValueId,
    ) -> ValueId {
        push_result(block, next_value, Inst::ICmp { op, ty, lhs, rhs })
    }

    let mut module = TrustIrModule::new("jit_loop_livein_callout");
    let callback_ty = module.add_func_type(FuncTy {
        params: vec![
            Ty::Ptr,
            Ty::Ptr,
            Ty::U64,
            Ty::U64,
            Ty::U64,
            Ty::U64,
            Ty::U64,
            Ty::U64,
        ],
        returns: vec![],
        is_vararg: false,
    });
    let entry_ty = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr, Ty::U64],
        returns: vec![Ty::U64],
        is_vararg: false,
    });

    let entry_id = BlockId::new(0);
    let header_id = BlockId::new(1);
    let body_id = BlockId::new(2);
    let done_id = BlockId::new(3);

    let mut next_value = 0;
    let input = value(&mut next_value);
    let output = value(&mut next_value);
    let count = value(&mut next_value);

    let mut entry = TrustIrBlock::new(entry_id)
        .with_param(input, Ty::Ptr)
        .with_param(output, Ty::Ptr)
        .with_param(count, Ty::U64);
    let idx_ptr = push_result(
        &mut entry,
        &mut next_value,
        Inst::Alloca {
            ty: Ty::U64,
            count: None,
            align: None,
        },
    );
    let zero = iconst(&mut entry, &mut next_value, Ty::U64, 0);
    store(&mut entry, Ty::U64, idx_ptr, zero);
    push_void(
        &mut entry,
        Inst::Br {
            target: header_id,
            args: vec![],
        },
    );

    let mut header = TrustIrBlock::new(header_id);
    let idx = load(&mut header, &mut next_value, Ty::U64, idx_ptr);
    let has_item = icmp(
        &mut header,
        &mut next_value,
        ICmpOp::Ult,
        Ty::U64,
        idx,
        count,
    );
    push_void(
        &mut header,
        Inst::CondBr {
            cond: has_item,
            then_target: body_id,
            then_args: vec![],
            else_target: done_id,
            else_args: vec![],
        },
    );

    let mut body = TrustIrBlock::new(body_id);
    let idx = load(&mut body, &mut next_value, Ty::U64, idx_ptr);
    let state_in = gep(&mut body, &mut next_value, Ty::I64, input, idx);
    let state_out = gep(&mut body, &mut next_value, Ty::I64, output, idx);
    let callback_addr = iconst(
        &mut body,
        &mut next_value,
        Ty::U64,
        host_loop_livein_callout_action as *const () as usize as i128,
    );
    let callback_ptr = push_result(
        &mut body,
        &mut next_value,
        Inst::Cast {
            op: CastOp::IntToPtr,
            src_ty: Ty::U64,
            dst_ty: Ty::Func(callback_ty),
            operand: callback_addr,
        },
    );
    let a = iconst(&mut body, &mut next_value, Ty::U64, 11);
    let b = iconst(&mut body, &mut next_value, Ty::U64, 13);
    let c = iconst(&mut body, &mut next_value, Ty::U64, 17);
    let d = iconst(&mut body, &mut next_value, Ty::U64, 19);
    push_void(
        &mut body,
        Inst::CallIndirect {
            callee: callback_ptr,
            sig: callback_ty,
            args: vec![state_out, state_in, idx, count, a, b, c, d],
            calling_conv: trust_ir::CallingConv::C,
        },
    );
    let idx_after_call = load(&mut body, &mut next_value, Ty::U64, idx_ptr);
    let one = iconst(&mut body, &mut next_value, Ty::U64, 1);
    let idx_next = binop(
        &mut body,
        &mut next_value,
        BinOp::Add,
        Ty::U64,
        idx_after_call,
        one,
    );
    store(&mut body, Ty::U64, idx_ptr, idx_next);
    push_void(
        &mut body,
        Inst::Br {
            target: header_id,
            args: vec![],
        },
    );

    let mut done = TrustIrBlock::new(done_id);
    let processed = load(&mut done, &mut next_value, Ty::U64, idx_ptr);
    push_void(
        &mut done,
        Inst::Return {
            values: vec![processed],
        },
    );

    let mut function =
        TrustIrFunction::new(FuncId::new(0), "loop_livein_callout", entry_ty, entry_id);
    function.blocks = vec![entry, header, body, done];
    module.add_function(function);
    module
}

fn compile_trust_ir_module_with_ty_pipeline(
    module: &trust_ir::Module,
    ext: &HashMap<String, *const u8>,
    opt_level: OptLevel,
) -> Result<trust_cg_codegen::ExecutableBuffer, String> {
    compile_trust_ir_module_with_ty_pipeline_backend(module, ext, opt_level)
}

fn compile_trust_ir_module_with_ty_pipeline_backend(
    module: &trust_ir::Module,
    ext: &HashMap<String, *const u8>,
    opt_level: OptLevel,
) -> Result<trust_cg_codegen::ExecutableBuffer, String> {
    let functions_with_proofs =
        trust_cg_lower::adapter::translate_module(module).map_err(|err| err.to_string())?;
    let pipeline = trust_cg_codegen::Pipeline::new(trust_cg_codegen::PipelineConfig {
        opt_level,
        emit_debug: false,
        verify_dispatch: trust_cg_codegen::DispatchVerifyMode::Off,
        verify: false,
        target_triple: "aarch64-apple-darwin".to_owned(),
        cegis_superopt_budget_sec: None,
        ..Default::default()
    });

    let mut ir_functions = Vec::new();
    for (func, proof_ctx) in &functions_with_proofs {
        let ir_func = pipeline
            .prepare_function_with_proofs(func, Some(proof_ctx))
            .map_err(|err| err.to_string())?;
        ir_functions.push(ir_func);
    }

    let jit = JitCompiler::new(JitConfig {
        opt_level,
        verify: false,
        verify_dispatch: trust_cg_codegen::DispatchVerifyMode::Off,
        ..JitConfig::default()
    });
    jit.compile_raw(&ir_functions, ext)
        .map_err(|err| err.to_string())
}

fn compile_trust_ir_module_with_ty_o1_pipeline(
    module: &trust_ir::Module,
    ext: &HashMap<String, *const u8>,
) -> Result<trust_cg_codegen::ExecutableBuffer, String> {
    compile_trust_ir_module_with_ty_pipeline(module, ext, OptLevel::O1)
}

fn compile_trust_ir_module_with_ty_o3_full_backend_pipeline(
    module: &trust_ir::Module,
    ext: &HashMap<String, *const u8>,
) -> Result<trust_cg_codegen::ExecutableBuffer, String> {
    compile_trust_ir_module_with_ty_pipeline_backend(module, ext, OptLevel::O3)
}

fn build_bool_block_param_live_pointer_alias_module() -> trust_ir::Module {
    use trust_ir::{
        BinOp, Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy,
        Function as TrustIrFunction, ICmpOp, Inst, InstrNode, Module as TrustIrModule, Ty, ValueId,
    };

    fn value(next_value: &mut u32) -> ValueId {
        let value = ValueId::new(*next_value);
        *next_value += 1;
        value
    }

    fn push_result(block: &mut TrustIrBlock, next_value: &mut u32, inst: Inst) -> ValueId {
        let result = value(next_value);
        block.body.push(InstrNode::new(inst).with_result(result));
        result
    }

    fn push_void(block: &mut TrustIrBlock, inst: Inst) {
        block.body.push(InstrNode::new(inst));
    }

    fn iconst(block: &mut TrustIrBlock, next_value: &mut u32, ty: Ty, int: i128) -> ValueId {
        push_result(
            block,
            next_value,
            Inst::Const {
                ty,
                value: Constant::Int(int),
            },
        )
    }

    fn gep(
        block: &mut TrustIrBlock,
        next_value: &mut u32,
        pointee_ty: Ty,
        base: ValueId,
        index: ValueId,
    ) -> ValueId {
        push_result(
            block,
            next_value,
            Inst::GEP {
                pointee_ty,
                base,
                indices: vec![index],
                inbounds: false,
            },
        )
    }

    fn load(block: &mut TrustIrBlock, next_value: &mut u32, ty: Ty, ptr: ValueId) -> ValueId {
        push_result(
            block,
            next_value,
            Inst::Load {
                ty,
                ptr,
                volatile: false,
                align: None,
            },
        )
    }

    fn binop(
        block: &mut TrustIrBlock,
        next_value: &mut u32,
        op: BinOp,
        ty: Ty,
        lhs: ValueId,
        rhs: ValueId,
    ) -> ValueId {
        push_result(block, next_value, Inst::BinOp { op, ty, lhs, rhs })
    }

    fn icmp(
        block: &mut TrustIrBlock,
        next_value: &mut u32,
        op: ICmpOp,
        ty: Ty,
        lhs: ValueId,
        rhs: ValueId,
    ) -> ValueId {
        push_result(block, next_value, Inst::ICmp { op, ty, lhs, rhs })
    }

    let mut module = TrustIrModule::new("jit_bool_block_param_live_pointer_alias");
    let entry_ty = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::U64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let entry_id = BlockId::new(0);
    let value_check_id = BlockId::new(1);
    let use_ptr_id = BlockId::new(2);

    let mut next_value = 0;
    let base = value(&mut next_value);
    let selector = value(&mut next_value);

    let mut entry = TrustIrBlock::new(entry_id)
        .with_param(base, Ty::Ptr)
        .with_param(selector, Ty::U64);

    let zero = iconst(&mut entry, &mut next_value, Ty::U64, 0);
    let status_ok = icmp(
        &mut entry,
        &mut next_value,
        ICmpOp::Eq,
        Ty::U64,
        selector,
        zero,
    );
    let value_is_zero = icmp(
        &mut entry,
        &mut next_value,
        ICmpOp::Eq,
        Ty::U64,
        selector,
        zero,
    );

    let mut live_slots = Vec::new();
    for slot in 0..26 {
        let idx = iconst(&mut entry, &mut next_value, Ty::U64, slot);
        live_slots.push(gep(&mut entry, &mut next_value, Ty::I64, base, idx));
    }

    push_void(
        &mut entry,
        Inst::CondBr {
            cond: status_ok,
            then_target: value_check_id,
            then_args: vec![value_is_zero],
            else_target: use_ptr_id,
            else_args: vec![],
        },
    );

    let flag = value(&mut next_value);
    let mut value_check = TrustIrBlock::new(value_check_id).with_param(flag, Ty::Bool);
    push_void(
        &mut value_check,
        Inst::CondBr {
            cond: flag,
            then_target: use_ptr_id,
            then_args: vec![],
            else_target: use_ptr_id,
            else_args: vec![],
        },
    );

    let mut use_ptr = TrustIrBlock::new(use_ptr_id);
    let mut acc = load(&mut use_ptr, &mut next_value, Ty::I64, live_slots[0]);
    for ptr in live_slots.iter().copied().skip(1) {
        let slot = load(&mut use_ptr, &mut next_value, Ty::I64, ptr);
        acc = binop(
            &mut use_ptr,
            &mut next_value,
            BinOp::Add,
            Ty::I64,
            acc,
            slot,
        );
    }
    push_void(&mut use_ptr, Inst::Return { values: vec![acc] });

    let mut function = TrustIrFunction::new(
        FuncId::new(0),
        "bool_block_param_live_pointer_alias",
        entry_ty,
        entry_id,
    );
    function.blocks = vec![entry, value_check, use_ptr];
    module.add_function(function);
    module
}

#[test]
fn test_jit_bool_block_param_does_not_clobber_live_pointer_alias() {
    let ext: HashMap<String, *const u8> = HashMap::new();
    let module = build_bool_block_param_live_pointer_alias_module();

    let data: Vec<i64> = (0..26).map(|idx| 1000 + (idx as i64 * 17)).collect();
    let expected: i64 = data.iter().sum();

    for full_backend in [false, true] {
        let buffer = if full_backend {
            compile_trust_ir_module_with_ty_o3_full_backend_pipeline(&module, &ext)
                .expect("TY-like O3 full backend should compile bool/pointer alias probe")
        } else {
            compile_trust_ir_module_with_ty_o1_pipeline(&module, &ext)
                .expect("TY-like O1 pipeline should compile bool/pointer alias probe")
        };
        let label = if full_backend {
            "O3 full backend"
        } else {
            "O1"
        };

        let bool_block_param_live_pointer_alias: extern "C" fn(*const i64, u64) -> i64 = unsafe {
            buffer
                .get_fn_bound("bool_block_param_live_pointer_alias")
                .expect("bool_block_param_live_pointer_alias symbol")
                .into_inner()
        };

        assert_eq!(
            bool_block_param_live_pointer_alias(data.as_ptr(), 0),
            expected,
            "{label} should preserve live pointer values across the Bool block-param edge"
        );
        assert_eq!(
            bool_block_param_live_pointer_alias(data.as_ptr(), 1),
            expected,
            "{label} should preserve live pointer values on the no-arg edge"
        );
    }
}

fn build_trust_ir_icmp_eq_select_old_vs_appended_module() -> trust_ir::Module {
    use trust_ir::{ICmpOp, Ty};
    use trust_ir_build::ModuleBuilder;

    let mut mb = ModuleBuilder::new("jit_ty_icmp_eq_select_old_vs_appended");
    let entry_ty = mb.add_func_type(vec![Ty::I64, Ty::I64, Ty::I64, Ty::I64], vec![Ty::I64]);

    {
        let mut fb = mb.function("select_old_vs_appended", entry_ty);
        let entry = fb.create_block();
        let sender = fb.add_block_param(entry, Ty::I64);
        let receiver = fb.add_block_param(entry, Ty::I64);
        let old = fb.add_block_param(entry, Ty::I64);
        let appended = fb.add_block_param(entry, Ty::I64);

        fb.switch_to_block(entry);
        let is_self_channel = fb.icmp(ICmpOp::Eq, Ty::I64, sender, receiver);
        let selected = fb.select(Ty::I64, is_self_channel, old, appended);
        fb.ret(vec![selected]);
        fb.build();
    }

    mb.build()
}

#[test]
fn test_jit_ty_icmp_eq_select_returns_old_vs_appended() {
    let ext: HashMap<String, *const u8> = HashMap::new();
    let module = build_trust_ir_icmp_eq_select_old_vs_appended_module();

    for opt_level in [OptLevel::O1, OptLevel::O3] {
        let buffer = compile_trust_ir_module_with_ty_pipeline(&module, &ext, opt_level)
            .unwrap_or_else(|err| {
                panic!("TY-like {opt_level:?} pipeline should compile icmp-eq select: {err}")
            });

        let select_old_vs_appended: extern "C" fn(i64, i64, i64, i64) -> i64 = unsafe {
            buffer
                .get_fn_bound("select_old_vs_appended")
                .expect("select_old_vs_appended symbol")
                .into_inner()
        };

        assert_eq!(
            select_old_vs_appended(1, 1, 7, 42),
            7,
            "{opt_level:?} should select the old channel when sender == receiver"
        );
        assert_eq!(
            select_old_vs_appended(1, 2, 7, 42),
            42,
            "{opt_level:?} should select the appended channel when sender != receiver"
        );
        assert_eq!(
            select_old_vs_appended(-4, -4, -11, 55),
            -11,
            "{opt_level:?} should preserve signed payloads on the true arm"
        );
        assert_eq!(
            select_old_vs_appended(-4, 4, -11, 55),
            55,
            "{opt_level:?} should preserve signed payloads on the false arm"
        );
    }
}

fn build_trust_ir_broadcast_channel_shape_select_module() -> trust_ir::Module {
    use trust_ir::{ICmpOp, Ty};
    use trust_ir_build::ModuleBuilder;

    let mut mb = ModuleBuilder::new("jit_ty_broadcast_channel_shape_select");
    let entry_ty = mb.add_func_type(vec![Ty::I64, Ty::I64, Ty::Ptr, Ty::Ptr, Ty::Ptr], vec![]);

    {
        let mut fb = mb.function("broadcast_channel_shape_select", entry_ty);
        let entry = fb.create_block();
        let sender = fb.add_block_param(entry, Ty::I64);
        let receiver = fb.add_block_param(entry, Ty::I64);
        let old = fb.add_block_param(entry, Ty::Ptr);
        let appended = fb.add_block_param(entry, Ty::Ptr);
        let out = fb.add_block_param(entry, Ty::Ptr);

        fb.switch_to_block(entry);

        let is_self_channel = fb.icmp(ICmpOp::Eq, Ty::I64, sender, receiver);

        for slot in 0..7 {
            let idx = fb.iconst(Ty::I64, slot);

            let old_slot_ptr = fb.gep(Ty::I64, old, vec![idx]);
            let appended_slot_ptr = fb.gep(Ty::I64, appended, vec![idx]);
            let out_slot_ptr = fb.gep(Ty::I64, out, vec![idx]);

            let old_slot = fb.load(Ty::I64, old_slot_ptr);
            let appended_slot = fb.load(Ty::I64, appended_slot_ptr);
            let selected = fb.select(Ty::I64, is_self_channel, old_slot, appended_slot);

            fb.store(Ty::I64, out_slot_ptr, selected);
        }

        fb.ret(vec![]);
        fb.build();
    }

    mb.build()
}

fn build_ty_bytecode_register_false_path_module() -> trust_ir::Module {
    use trust_ir::{
        Block as TrustIrBlock, BlockId, CastOp, Constant, FuncId, FuncTy,
        Function as TrustIrFunction, ICmpOp, Inst, InstrNode, Module as TrustIrModule, Ty, ValueId,
    };

    fn value(next_value: &mut u32) -> ValueId {
        let value = ValueId::new(*next_value);
        *next_value += 1;
        value
    }

    fn push_result(block: &mut TrustIrBlock, next_value: &mut u32, inst: Inst) -> ValueId {
        let result = value(next_value);
        block.body.push(InstrNode::new(inst).with_result(result));
        result
    }

    fn push_void(block: &mut TrustIrBlock, inst: Inst) {
        block.body.push(InstrNode::new(inst));
    }

    fn iconst(block: &mut TrustIrBlock, next_value: &mut u32, ty: Ty, int: i128) -> ValueId {
        push_result(
            block,
            next_value,
            Inst::Const {
                ty,
                value: Constant::Int(int),
            },
        )
    }

    fn alloca_i64(block: &mut TrustIrBlock, next_value: &mut u32) -> ValueId {
        push_result(
            block,
            next_value,
            Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            },
        )
    }

    fn gep_i64(
        block: &mut TrustIrBlock,
        next_value: &mut u32,
        base: ValueId,
        index: ValueId,
    ) -> ValueId {
        push_result(
            block,
            next_value,
            Inst::GEP {
                pointee_ty: Ty::I64,
                base,
                indices: vec![index],
                inbounds: false,
            },
        )
    }

    fn load_i64(block: &mut TrustIrBlock, next_value: &mut u32, ptr: ValueId) -> ValueId {
        push_result(
            block,
            next_value,
            Inst::Load {
                ty: Ty::I64,
                ptr,
                volatile: false,
                align: None,
            },
        )
    }

    fn store_i64(block: &mut TrustIrBlock, ptr: ValueId, value: ValueId) {
        push_void(
            block,
            Inst::Store {
                ty: Ty::I64,
                ptr,
                value,
                volatile: false,
                align: None,
            },
        );
    }

    fn eq_i64(
        block: &mut TrustIrBlock,
        next_value: &mut u32,
        lhs: ValueId,
        rhs: ValueId,
    ) -> ValueId {
        push_result(
            block,
            next_value,
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I64,
                lhs,
                rhs,
            },
        )
    }

    fn ne_i64_zero(block: &mut TrustIrBlock, next_value: &mut u32, value: ValueId) -> ValueId {
        let zero = iconst(block, next_value, Ty::I64, 0);
        push_result(
            block,
            next_value,
            Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I64,
                lhs: value,
                rhs: zero,
            },
        )
    }

    fn zext_bool_to_i64(block: &mut TrustIrBlock, next_value: &mut u32, value: ValueId) -> ValueId {
        push_result(
            block,
            next_value,
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I64,
                operand: value,
            },
        )
    }

    let mut module = TrustIrModule::new("jit_ty_bytecode_register_false_path");
    let entry_ty = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    let entry_id = BlockId::new(0);
    let self_30_id = BlockId::new(1);
    let self_31_id = BlockId::new(2);
    let self_32_id = BlockId::new(3);
    let self_33_id = BlockId::new(4);
    let domain_error_id = BlockId::new(5);
    let guard_id = BlockId::new(6);
    let after_first_false_id = BlockId::new(7);
    let after_second_false_id = BlockId::new(8);
    let ret_id = BlockId::new(9);
    let true_id = BlockId::new(10);

    let mut next_value = 0;
    let state = value(&mut next_value);
    let mut entry = TrustIrBlock::new(entry_id).with_param(state, Ty::Ptr);
    let mut regs = Vec::new();
    for _ in 0..21 {
        regs.push(alloca_i64(&mut entry, &mut next_value));
    }

    let self_id = iconst(&mut entry, &mut next_value, Ty::I64, 30);
    store_i64(&mut entry, regs[0], self_id);

    let r0 = load_i64(&mut entry, &mut next_value, regs[0]);
    let domain_30 = iconst(&mut entry, &mut next_value, Ty::I64, 30);
    let is_30 = eq_i64(&mut entry, &mut next_value, r0, domain_30);
    push_void(
        &mut entry,
        Inst::CondBr {
            cond: is_30,
            then_target: self_30_id,
            then_args: vec![],
            else_target: self_31_id,
            else_args: vec![],
        },
    );

    let mut self_30 = TrustIrBlock::new(self_30_id);
    let idx_9 = iconst(&mut self_30, &mut next_value, Ty::I32, 9);
    let pc_ptr = gep_i64(&mut self_30, &mut next_value, state, idx_9);
    let pc_value = load_i64(&mut self_30, &mut next_value, pc_ptr);
    store_i64(&mut self_30, regs[2], pc_value);
    push_void(
        &mut self_30,
        Inst::Br {
            target: guard_id,
            args: vec![],
        },
    );

    let mut self_31 = TrustIrBlock::new(self_31_id);
    let r0 = load_i64(&mut self_31, &mut next_value, regs[0]);
    let domain_31 = iconst(&mut self_31, &mut next_value, Ty::I64, 31);
    let is_31 = eq_i64(&mut self_31, &mut next_value, r0, domain_31);
    push_void(
        &mut self_31,
        Inst::CondBr {
            cond: is_31,
            then_target: self_32_id,
            then_args: vec![],
            else_target: self_32_id,
            else_args: vec![],
        },
    );

    let mut self_32 = TrustIrBlock::new(self_32_id);
    let r0 = load_i64(&mut self_32, &mut next_value, regs[0]);
    let domain_32 = iconst(&mut self_32, &mut next_value, Ty::I64, 32);
    let is_32 = eq_i64(&mut self_32, &mut next_value, r0, domain_32);
    push_void(
        &mut self_32,
        Inst::CondBr {
            cond: is_32,
            then_target: self_33_id,
            then_args: vec![],
            else_target: self_33_id,
            else_args: vec![],
        },
    );

    let mut self_33 = TrustIrBlock::new(self_33_id);
    let r0 = load_i64(&mut self_33, &mut next_value, regs[0]);
    let domain_33 = iconst(&mut self_33, &mut next_value, Ty::I64, 33);
    let is_33 = eq_i64(&mut self_33, &mut next_value, r0, domain_33);
    push_void(
        &mut self_33,
        Inst::CondBr {
            cond: is_33,
            then_target: domain_error_id,
            then_args: vec![],
            else_target: domain_error_id,
            else_args: vec![],
        },
    );

    let mut domain_error = TrustIrBlock::new(domain_error_id);
    let domain_error_value = iconst(&mut domain_error, &mut next_value, Ty::I64, -1);
    push_void(
        &mut domain_error,
        Inst::Return {
            values: vec![domain_error_value],
        },
    );

    let mut guard = TrustIrBlock::new(guard_id);
    let li2 = iconst(&mut guard, &mut next_value, Ty::I64, 1);
    store_i64(&mut guard, regs[3], li2);
    let pc = load_i64(&mut guard, &mut next_value, regs[2]);
    let expected = load_i64(&mut guard, &mut next_value, regs[3]);
    let pc_is_li2 = eq_i64(&mut guard, &mut next_value, pc, expected);
    let pc_is_li2_i64 = zext_bool_to_i64(&mut guard, &mut next_value, pc_is_li2);
    store_i64(&mut guard, regs[4], pc_is_li2_i64);
    let first_guard = load_i64(&mut guard, &mut next_value, regs[4]);
    store_i64(&mut guard, regs[5], first_guard);
    let branch_value = load_i64(&mut guard, &mut next_value, regs[5]);
    let branch_cond = ne_i64_zero(&mut guard, &mut next_value, branch_value);
    push_void(
        &mut guard,
        Inst::CondBr {
            cond: branch_cond,
            then_target: true_id,
            then_args: vec![],
            else_target: after_first_false_id,
            else_args: vec![],
        },
    );

    let mut after_first_false = TrustIrBlock::new(after_first_false_id);
    let carried = load_i64(&mut after_first_false, &mut next_value, regs[5]);
    store_i64(&mut after_first_false, regs[12], carried);
    let second_guard = load_i64(&mut after_first_false, &mut next_value, regs[12]);
    let second_cond = ne_i64_zero(&mut after_first_false, &mut next_value, second_guard);
    push_void(
        &mut after_first_false,
        Inst::CondBr {
            cond: second_cond,
            then_target: true_id,
            then_args: vec![],
            else_target: after_second_false_id,
            else_args: vec![],
        },
    );

    let mut after_second_false = TrustIrBlock::new(after_second_false_id);
    let carried = load_i64(&mut after_second_false, &mut next_value, regs[12]);
    store_i64(&mut after_second_false, regs[19], carried);
    let final_guard = load_i64(&mut after_second_false, &mut next_value, regs[19]);
    let final_cond = ne_i64_zero(&mut after_second_false, &mut next_value, final_guard);
    push_void(
        &mut after_second_false,
        Inst::CondBr {
            cond: final_cond,
            then_target: true_id,
            then_args: vec![],
            else_target: ret_id,
            else_args: vec![],
        },
    );

    let mut ret = TrustIrBlock::new(ret_id);
    let result = load_i64(&mut ret, &mut next_value, regs[19]);
    store_i64(&mut ret, regs[0], result);
    let result = load_i64(&mut ret, &mut next_value, regs[0]);
    let result_bool = ne_i64_zero(&mut ret, &mut next_value, result);
    let result_i64 = zext_bool_to_i64(&mut ret, &mut next_value, result_bool);
    push_void(
        &mut ret,
        Inst::Return {
            values: vec![result_i64],
        },
    );

    let mut true_block = TrustIrBlock::new(true_id);
    let true_value = iconst(&mut true_block, &mut next_value, Ty::I64, 1);
    push_void(
        &mut true_block,
        Inst::Return {
            values: vec![true_value],
        },
    );

    let mut function = TrustIrFunction::new(
        FuncId::new(0),
        "ty_bytecode_register_false_path",
        entry_ty,
        entry_id,
    );
    function.blocks = vec![
        entry,
        self_30,
        self_31,
        self_32,
        self_33,
        domain_error,
        guard,
        after_first_false,
        after_second_false,
        ret,
        true_block,
    ];
    module.add_function(function);
    module
}

#[test]
fn test_jit_direct_call_preserves_retbuf_pointer_live_across_call() {
    let ext: HashMap<String, *const u8> = HashMap::new();
    let module = build_direct_call_retbuf_live_across_call_module();

    for opt_level in [OptLevel::O1, OptLevel::O3] {
        let buffer = compile_trust_ir_module_with_ty_pipeline(&module, &ext, opt_level)
            .unwrap_or_else(|err| {
                panic!("TY-like {opt_level:?} pipeline should compile retbuf caller: {err}")
            });

        let entry: extern "C" fn(*mut u64) -> i64 = unsafe {
            buffer
                .get_fn_bound("direct_call_retbuf_live_across_call")
                .expect("direct_call_retbuf_live_across_call symbol")
                .into_inner()
        };

        let mut scratch = [0_u64; 2];
        assert_eq!(
            entry(scratch.as_mut_ptr()),
            31,
            "{opt_level:?} must keep the caller-owned return buffer pointer live after BL"
        );
    }
}

#[test]
fn test_jit_ty_bytecode_register_false_path_returns_zero() {
    let ext: HashMap<String, *const u8> = HashMap::new();
    let module = build_ty_bytecode_register_false_path_module();

    for opt_level in [OptLevel::O1, OptLevel::O3] {
        let buffer = compile_trust_ir_module_with_ty_pipeline(&module, &ext, opt_level)
            .unwrap_or_else(|err| {
                panic!(
                    "TY-like {opt_level:?} pipeline should compile bytecode register flow: {err}"
                )
            });

        let entry: extern "C" fn(*const i64) -> i64 = unsafe {
            buffer
                .get_fn_bound("ty_bytecode_register_false_path")
                .expect("ty_bytecode_register_false_path symbol")
                .into_inner()
        };

        let mut state = [0_i64; 21];
        state[9] = 0;
        assert_eq!(
            entry(state.as_ptr()),
            0,
            "{opt_level:?} must preserve the widened false guard through bytecode-register stack slots"
        );

        state[9] = 1;
        assert_eq!(
            entry(state.as_ptr()),
            1,
            "{opt_level:?} must still take the true guard when the pc matches"
        );
    }
}

#[test]
fn test_jit_ty_broadcast_channel_shape_selects_each_slot_o1_o3() {
    let ext: HashMap<String, *const u8> = HashMap::new();
    let module = build_trust_ir_broadcast_channel_shape_select_module();

    for opt_level in [OptLevel::O1, OptLevel::O3] {
        let buffer = compile_trust_ir_module_with_ty_pipeline(&module, &ext, opt_level)
            .unwrap_or_else(|err| {
                panic!("TY-like {opt_level:?} pipeline should compile broadcast shape: {err}")
            });

        let broadcast_channel_shape_select: extern "C" fn(
            i64,
            i64,
            *const i64,
            *const i64,
            *mut i64,
        ) = unsafe {
            buffer
                .get_fn_bound("broadcast_channel_shape_select")
                .expect("broadcast_channel_shape_select symbol")
                .into_inner()
        };

        let old = [10, 11, 12, 13, 14, 15, 16];
        let appended = [20, 21, 22, 23, 24, 25, 26];

        let mut out = [0; 7];
        broadcast_channel_shape_select(3, 3, old.as_ptr(), appended.as_ptr(), out.as_mut_ptr());
        assert_eq!(
            out, old,
            "{opt_level:?} should select old channel slots when sender == receiver"
        );

        out = [0; 7];
        broadcast_channel_shape_select(3, 4, old.as_ptr(), appended.as_ptr(), out.as_mut_ptr());
        assert_eq!(
            out, appended,
            "{opt_level:?} should select appended channel slots when sender != receiver"
        );
    }
}

#[test]
fn test_jit_call_indirect_trust_ir_like_mini_bfs_loop_enters_callout() {
    let _guard = lock_mini_bfs_callout_action();
    MINI_BFS_CALLOUT_ACTION_CALLS.store(0, Ordering::SeqCst);
    MINI_BFS_CALLOUT_ACTION_STATE_IN_VALUE.store(0, Ordering::SeqCst);
    MINI_BFS_CALLOUT_ACTION_STATE_OUT.store(0, Ordering::SeqCst);
    MINI_BFS_CALLOUT_ACTION_LEN.store(0, Ordering::SeqCst);

    let ext: HashMap<String, *const u8> = HashMap::new();
    let module = build_trust_ir_like_mini_bfs_callout_indirect_module();
    // Runs with post-RA optimization ON at O1. The post-RA copy coalescer
    // (trust_cg_regalloc::post_ra_coalesce) no longer treats a narrow-alias
    // write (e.g. `mov w0,#imm`) as a full kill of the wide register, so the
    // `x0` call-argument copy (the callout out-buffer pointer) survives across
    // the call instead of being deleted.
    let buffer = compile_trust_ir_module_with_ty_o1_pipeline(&module, &ext)
        .expect("TY-like O1 pipeline should compile mini BFS callout");

    let call_trust_ir_like_mini_bfs: extern "C" fn(*const i64, *mut i64, u64) -> u64 = unsafe {
        buffer
            .get_fn_bound("call_trust_ir_like_mini_bfs")
            .expect("call_trust_ir_like_mini_bfs symbol")
            .into_inner()
    };

    let parents = [10_i64, 20_i64];
    let mut states = [0_i64, 0_i64];
    let returned =
        call_trust_ir_like_mini_bfs(parents.as_ptr(), states.as_mut_ptr(), parents.len() as u64);

    assert_eq!(
        returned,
        2,
        "states={states:?} calls={} last_in={} last_out=0x{:x} len={}",
        MINI_BFS_CALLOUT_ACTION_CALLS.load(Ordering::SeqCst),
        MINI_BFS_CALLOUT_ACTION_STATE_IN_VALUE.load(Ordering::SeqCst),
        MINI_BFS_CALLOUT_ACTION_STATE_OUT.load(Ordering::SeqCst),
        MINI_BFS_CALLOUT_ACTION_LEN.load(Ordering::SeqCst)
    );
    assert_eq!(states, [42, 42]);
    assert_eq!(MINI_BFS_CALLOUT_ACTION_CALLS.load(Ordering::SeqCst), 2);
    assert_eq!(
        MINI_BFS_CALLOUT_ACTION_STATE_IN_VALUE.load(Ordering::SeqCst),
        20
    );
    assert_eq!(
        MINI_BFS_CALLOUT_ACTION_STATE_OUT.load(Ordering::SeqCst),
        states[1..].as_ptr() as usize
    );
    assert_eq!(MINI_BFS_CALLOUT_ACTION_LEN.load(Ordering::SeqCst), 1);
}

#[test]
fn test_jit_call_indirect_trust_ir_like_mini_bfs_loop_enters_callout_o3_full_backend() {
    let _guard = lock_mini_bfs_callout_action();
    MINI_BFS_CALLOUT_ACTION_CALLS.store(0, Ordering::SeqCst);
    MINI_BFS_CALLOUT_ACTION_STATE_IN_VALUE.store(0, Ordering::SeqCst);
    MINI_BFS_CALLOUT_ACTION_STATE_OUT.store(0, Ordering::SeqCst);
    MINI_BFS_CALLOUT_ACTION_LEN.store(0, Ordering::SeqCst);

    let ext: HashMap<String, *const u8> = HashMap::new();
    let module = build_trust_ir_like_mini_bfs_callout_indirect_module();
    let buffer = compile_trust_ir_module_with_ty_o3_full_backend_pipeline(&module, &ext)
        .expect("TY-like O3 full backend should compile mini BFS indirect callout");

    let call_trust_ir_like_mini_bfs: extern "C" fn(*const i64, *mut i64, u64) -> u64 = unsafe {
        buffer
            .get_fn_bound("call_trust_ir_like_mini_bfs")
            .expect("call_trust_ir_like_mini_bfs symbol")
            .into_inner()
    };

    let parents = [10_i64, 20_i64];
    let mut states = [0_i64, 0_i64];
    let returned =
        call_trust_ir_like_mini_bfs(parents.as_ptr(), states.as_mut_ptr(), parents.len() as u64);

    assert_eq!(returned, 2);
    assert_eq!(states, [42, 42]);
    assert_eq!(MINI_BFS_CALLOUT_ACTION_CALLS.load(Ordering::SeqCst), 2);
    assert_eq!(
        MINI_BFS_CALLOUT_ACTION_STATE_IN_VALUE.load(Ordering::SeqCst),
        20
    );
    assert_eq!(
        MINI_BFS_CALLOUT_ACTION_STATE_OUT.load(Ordering::SeqCst),
        states[1..].as_ptr() as usize
    );
    assert_eq!(MINI_BFS_CALLOUT_ACTION_LEN.load(Ordering::SeqCst), 1);
}

#[test]
fn test_jit_loop_callback_preserves_call_liveins_and_loop_state() {
    let ext: HashMap<String, *const u8> = HashMap::new();

    for full_backend in [false, true] {
        LOOP_LIVEIN_CALLOUT_ACTION_CALLS.store(0, Ordering::SeqCst);
        LOOP_LIVEIN_CALLOUT_LAST_IDX.store(0, Ordering::SeqCst);
        LOOP_LIVEIN_CALLOUT_LAST_COUNT.store(0, Ordering::SeqCst);
        LOOP_LIVEIN_CALLOUT_LAST_SENTINEL.store(0, Ordering::SeqCst);
        LOOP_LIVEIN_CALLOUT_STATE_OUT.store(0, Ordering::SeqCst);

        let module = build_loop_livein_callout_indirect_module();
        // Runs with post-RA optimization ON (O1 and O3). The copy coalescer
        // (trust_cg_regalloc::post_ra_coalesce) no longer deletes a copy that
        // delivers a call argument when a full-width scratch redef of the arg
        // register sits between the copy and a call that reads it via
        // implicit_uses, so the loop-carried live-ins survive across the
        // indirect call.
        let buffer = if full_backend {
            compile_trust_ir_module_with_ty_o3_full_backend_pipeline(&module, &ext)
                .expect("TY-like O3 full backend should compile live-in loop callout")
        } else {
            compile_trust_ir_module_with_ty_o1_pipeline(&module, &ext)
                .expect("TY-like O1 pipeline should compile live-in loop callout")
        };
        let label = if full_backend {
            "O3 full backend"
        } else {
            "O1"
        };

        let loop_livein_callout: extern "C" fn(*const i64, *mut i64, u64) -> u64 = unsafe {
            buffer
                .get_fn_bound("loop_livein_callout")
                .expect("loop_livein_callout symbol")
                .into_inner()
        };

        let input = [3_i64, 5_i64];
        let mut output = [0_i64, 0_i64];
        let returned = loop_livein_callout(input.as_ptr(), output.as_mut_ptr(), input.len() as u64);

        assert_eq!(returned, 2, "{label} should process both parents");
        assert_eq!(output, [65, 68], "{label} should preserve loop state");
        assert_eq!(
            LOOP_LIVEIN_CALLOUT_ACTION_CALLS.load(Ordering::SeqCst),
            2,
            "{label} should enter the indirect callout once per parent"
        );
        assert_eq!(LOOP_LIVEIN_CALLOUT_LAST_IDX.load(Ordering::SeqCst), 1);
        assert_eq!(LOOP_LIVEIN_CALLOUT_LAST_COUNT.load(Ordering::SeqCst), 2);
        assert_eq!(LOOP_LIVEIN_CALLOUT_LAST_SENTINEL.load(Ordering::SeqCst), 60);
        assert_eq!(
            LOOP_LIVEIN_CALLOUT_STATE_OUT.load(Ordering::SeqCst),
            output[1..].as_ptr() as usize
        );
    }
}

#[test]
fn test_jit_indirect_call_live_values_survive_volatile_clobber() {
    let ext: HashMap<String, *const u8> = HashMap::new();
    let module = build_indirect_call_live_values_survive_volatile_clobber_module();
    let buffer = compile_trust_ir_module_with_ty_o1_pipeline(&module, &ext)
        .expect("TY-like O1 pipeline should compile volatile-clobber live-in test");

    let live_values_survive_volatile_clobber: extern "C" fn(u64) -> u64 = unsafe {
        buffer
            .get_fn_bound("live_values_survive_volatile_clobber")
            .expect("live_values_survive_volatile_clobber symbol")
            .into_inner()
    };

    for seed in [0_u64, 1, 0x100, 0xfeed_face_cafe_babe] {
        assert_eq!(
            live_values_survive_volatile_clobber(seed),
            volatile_clobber_checksum(seed),
            "live values must survive an indirect BLR target that clobbers call-volatile registers"
        );
    }
}

#[test]
fn test_jit_call_indirect_trust_ir_like_stack_callout_updates_memory() {
    STACK_CALLOUT_ACTION_CALLS.store(0, Ordering::SeqCst);
    STACK_CALLOUT_ACTION_STATE_IN_VALUE.store(0, Ordering::SeqCst);
    STACK_CALLOUT_ACTION_STATE_OUT.store(0, Ordering::SeqCst);
    STACK_CALLOUT_ACTION_LEN.store(0, Ordering::SeqCst);

    let ext: HashMap<String, *const u8> = HashMap::new();
    let module = build_trust_ir_like_stack_callout_indirect_module();
    let buffer = compile_trust_ir_module_with_ty_o1_pipeline(&module, &ext)
        .expect("TY-like O1 pipeline should compile stack callout");

    let call_trust_ir_like_stack_callout: extern "C" fn(*const i64, *mut i64, u32) -> i64 = unsafe {
        buffer
            .get_fn_bound("call_trust_ir_like_stack_callout")
            .expect("call_trust_ir_like_stack_callout symbol")
            .into_inner()
    };

    let state_in = [10_i64];
    let mut state_out = [0_i64];
    let returned = call_trust_ir_like_stack_callout(
        state_in.as_ptr(),
        state_out.as_mut_ptr(),
        state_in.len() as u32,
    );

    assert_eq!(returned, CALLOUT_VALUE_ENABLED);
    assert_eq!(state_out, [42]);
    assert_eq!(STACK_CALLOUT_ACTION_CALLS.load(Ordering::SeqCst), 1);
    assert_eq!(
        STACK_CALLOUT_ACTION_STATE_IN_VALUE.load(Ordering::SeqCst),
        10
    );
    assert_eq!(
        STACK_CALLOUT_ACTION_STATE_OUT.load(Ordering::SeqCst),
        state_out.as_ptr() as usize
    );
    assert_eq!(STACK_CALLOUT_ACTION_LEN.load(Ordering::SeqCst), 1);
}

// ---------------------------------------------------------------------------
// Test: external symbol with multiple callers sharing one veneer
// ---------------------------------------------------------------------------

extern "C" fn host_double(x: i64) -> i64 {
    x * 2
}

#[test]
fn test_jit_shared_veneer() {
    let jit = JitCompiler::new(JitConfig::default());

    // Two different callers both referencing the same external symbol.
    // Each saves/restores LR around the BL (non-leaf function pattern).
    let caller_a = {
        let sig = Signature::new(vec![Type::I64], vec![Type::I64]);
        let mut func = MachFunction::new("caller_a".to_string(), sig);
        let entry = func.entry;
        // STP FP, LR, [SP, #-16]!
        let stp = MachInst::new(
            AArch64Opcode::StpPreIndex,
            vec![
                MachOperand::PReg(FP),
                MachOperand::PReg(LR),
                Special(SpecialReg::SP),
                MachOperand::Imm(-16),
            ],
        );
        let stp_id = func.push_inst(stp);
        func.append_inst(entry, stp_id);
        let bl = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("_host_double".to_string())],
        );
        let bl_id = func.push_inst(bl);
        func.append_inst(entry, bl_id);
        // LDP FP, LR, [SP], #16
        let ldp = MachInst::new(
            AArch64Opcode::LdpPostIndex,
            vec![
                MachOperand::PReg(FP),
                MachOperand::PReg(LR),
                Special(SpecialReg::SP),
                MachOperand::Imm(16),
            ],
        );
        let ldp_id = func.push_inst(ldp);
        func.append_inst(entry, ldp_id);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let ret_id = func.push_inst(ret);
        func.append_inst(entry, ret_id);
        func
    };

    let caller_b = {
        let sig = Signature::new(vec![Type::I64], vec![Type::I64]);
        let mut func = MachFunction::new("caller_b".to_string(), sig);
        let entry = func.entry;
        // STP FP, LR, [SP, #-16]!
        let stp = MachInst::new(
            AArch64Opcode::StpPreIndex,
            vec![
                MachOperand::PReg(FP),
                MachOperand::PReg(LR),
                Special(SpecialReg::SP),
                MachOperand::Imm(-16),
            ],
        );
        let stp_id = func.push_inst(stp);
        func.append_inst(entry, stp_id);
        let bl = MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("_host_double".to_string())],
        );
        let bl_id = func.push_inst(bl);
        func.append_inst(entry, bl_id);
        // LDP FP, LR, [SP], #16
        let ldp = MachInst::new(
            AArch64Opcode::LdpPostIndex,
            vec![
                MachOperand::PReg(FP),
                MachOperand::PReg(LR),
                Special(SpecialReg::SP),
                MachOperand::Imm(16),
            ],
        );
        let ldp_id = func.push_inst(ldp);
        func.append_inst(entry, ldp_id);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let ret_id = func.push_inst(ret);
        func.append_inst(entry, ret_id);
        func
    };

    let mut ext: HashMap<String, *const u8> = HashMap::new();
    ext.insert("_host_double".to_string(), host_double as *const u8);

    let buf = jit
        .compile_raw(&[caller_a, caller_b], &ext)
        .expect("compile_raw should succeed with shared veneer");

    let fa: extern "C" fn(i64) -> i64 = unsafe { buf.get_fn("caller_a").expect("caller_a") };
    let fb: extern "C" fn(i64) -> i64 = unsafe { buf.get_fn("caller_b").expect("caller_b") };

    assert_eq!(fa(5), 10);
    assert_eq!(fb(21), 42);
    // Both callers should produce the same result for the same input.
    assert_eq!(fa(100), fb(100));
}

// ---------------------------------------------------------------------------
// Test: unresolved symbol produces an error
// ---------------------------------------------------------------------------

#[test]
fn test_jit_unresolved_symbol_error() {
    let jit = JitCompiler::new(JitConfig::default());
    let caller = build_extern_caller("_nonexistent_function");
    let ext: HashMap<String, *const u8> = HashMap::new();

    let result = jit.compile_raw(&[caller], &ext);
    assert!(
        result.is_err(),
        "compile_raw should fail for unresolved symbol"
    );
    match result {
        Err(JitError::UnresolvedSymbol(name)) => {
            assert_eq!(name, "_nonexistent_function");
        }
        Err(other) => panic!("Expected UnresolvedSymbol error, got: {}", other),
        Ok(_) => unreachable!("already checked result.is_err()"),
    }
}

// ---------------------------------------------------------------------------
// Test: duplicate symbol names produce JitError::DuplicateSymbol (#374)
// ---------------------------------------------------------------------------

#[test]
fn test_jit_duplicate_primary_symbol_error() {
    // Two functions with identical primary names — direct collision on the
    // primary-name slot.
    let jit = JitCompiler::new(JitConfig::default());
    let mut a = build_add();
    let mut b = build_add();
    a.name = "dup".to_string();
    b.name = "dup".to_string();
    let ext: HashMap<String, *const u8> = HashMap::new();

    let result = jit.compile_raw(&[a, b], &ext);
    match result {
        Err(JitError::DuplicateSymbol(name)) => {
            assert_eq!(name, "dup", "collision should report primary name");
        }
        Err(other) => panic!("Expected DuplicateSymbol, got: {}", other),
        Ok(_) => panic!("Expected DuplicateSymbol error, got success"),
    }
}

#[test]
fn test_jit_duplicate_alias_vs_primary_symbol_error() {
    // Order `[foo, _foo]`: the second function's PRIMARY name `_foo`
    // collides with the first function's already-inserted alias `_foo`.
    // This fires the primary-name check on iteration 2.
    let jit = JitCompiler::new(JitConfig::default());
    let mut a = build_add();
    let mut b = build_add();
    a.name = "foo".to_string();
    b.name = "_foo".to_string();
    let ext: HashMap<String, *const u8> = HashMap::new();

    let result = jit.compile_raw(&[a, b], &ext);
    match result {
        Err(JitError::DuplicateSymbol(name)) => {
            assert_eq!(
                name, "_foo",
                "collision should report the colliding key (`_foo`)"
            );
        }
        Err(other) => panic!("Expected DuplicateSymbol, got: {}", other),
        Ok(_) => panic!("Expected DuplicateSymbol error, got success"),
    }
}

#[test]
fn test_jit_duplicate_alias_check_path() {
    // Order `[_foo, foo]`: exercises the ALIAS check branch specifically.
    //
    // Iter 1 (`_foo`): primary `_foo` and alias `__foo` inserted. No collision.
    // Iter 2 (`foo`): primary `foo` not present → inserted. Alias `_foo` is
    //                 already present → alias check fires.
    //
    // Without this ordering, no test would exercise the alias-check branch
    // (the `if func_offsets.contains_key(alias.as_str())` block).
    let jit = JitCompiler::new(JitConfig::default());
    let mut a = build_add();
    let mut b = build_add();
    a.name = "_foo".to_string();
    b.name = "foo".to_string();
    let ext: HashMap<String, *const u8> = HashMap::new();

    let result = jit.compile_raw(&[a, b], &ext);
    match result {
        Err(JitError::DuplicateSymbol(name)) => {
            assert_eq!(
                name, "_foo",
                "alias collision should report the generated alias key (`_foo`)"
            );
        }
        Err(other) => panic!("Expected DuplicateSymbol, got: {}", other),
        Ok(_) => panic!("Expected DuplicateSymbol error, got success"),
    }
}

// ---------------------------------------------------------------------------
// Test: ExecutableBuffer API — symbol enumeration and lookup
// ---------------------------------------------------------------------------

#[test]
fn test_jit_buffer_api() {
    let jit = JitCompiler::new(JitConfig::default());
    let funcs = vec![build_add(), build_sub()];
    let ext: HashMap<String, *const u8> = HashMap::new();

    let buf = jit
        .compile_raw(&funcs, &ext)
        .expect("compile_raw should succeed");

    // Fix #360: symbol_count reflects the canonical symbol list (one entry
    // per compiled function), not the /2-ed size of the lookup map.
    assert_eq!(
        buf.symbol_count(),
        2,
        "expected exactly 2 canonical symbols (add, sub)"
    );

    // get_fn_ptr returns valid pointers.
    assert!(buf.get_fn_ptr("add").is_some(), "should find 'add'");
    assert!(buf.get_fn_ptr("sub").is_some(), "should find 'sub'");
    assert!(buf.get_fn_ptr("_add").is_some(), "should find '_add' alias");
    assert!(buf.get_fn_ptr("_sub").is_some(), "should find '_sub' alias");
    assert!(
        buf.get_fn_ptr("nonexistent").is_none(),
        "shouldn't find fake symbol"
    );

    // Fix #360: symbols() enumerates canonical names (no alias duplicates,
    // no hiding of `_`-prefixed user names).
    let names: Vec<&str> = buf.symbols().map(|(name, _)| name).collect();
    assert_eq!(names.len(), 2, "symbols() must yield canonical names only");
    assert!(names.contains(&"add"), "symbols() should contain 'add'");
    assert!(names.contains(&"sub"), "symbols() should contain 'sub'");

    // Allocated size should be at least a page.
    assert!(
        buf.allocated_size() >= 4096,
        "buffer should be at least one page"
    );
}

#[test]
fn test_jit_buffer_replay_report_metadata_uses_compiled_layout() {
    let jit = JitCompiler::new(JitConfig::default());
    let funcs = vec![build_add(), build_sub()];
    let ext: HashMap<String, *const u8> = HashMap::new();

    let buf = jit
        .compile_raw(&funcs, &ext)
        .expect("compile_raw should succeed");

    let report = buf.replay_report_metadata();
    let json = report.to_json_value();

    assert_eq!(json["schema"], JIT_REPLAY_SCHEMA);
    assert_eq!(json["schema_version"], JIT_REPLAY_SCHEMA_VERSION);
    assert_eq!(json["producer"], "trust-cg-codegen");
    assert_eq!(
        json["code_size"], 16,
        "add/sub should preserve the raw 16-byte code layout, not page size"
    );

    assert_eq!(
        json["symbols"],
        serde_json::json!([
            {
                "aliases": ["_add"],
                "name": "add",
                "range": {
                    "byte_len": 8,
                    "end_offset": 8,
                    "start_offset": 0,
                    "valid": true,
                },
            },
            {
                "aliases": ["_sub"],
                "name": "sub",
                "range": {
                    "byte_len": 8,
                    "end_offset": 16,
                    "start_offset": 8,
                    "valid": true,
                },
            },
        ])
    );
    assert_eq!(
        json["pc_map"],
        serde_json::json!([
            {
                "machine_inst_index": null,
                "pc_offset": 0,
                "source_label": null,
                "symbol": "add",
                "symbol_offset": 0,
                "trust_ir_op": null,
            },
            {
                "machine_inst_index": null,
                "pc_offset": 8,
                "source_label": null,
                "symbol": "sub",
                "symbol_offset": 0,
                "trust_ir_op": null,
            },
        ])
    );
    assert_eq!(json["statuses"], serde_json::json!([]));
}

// ---------------------------------------------------------------------------
// Test: ExecutableBuffer is Send + Sync
// ---------------------------------------------------------------------------

#[test]
fn test_jit_buffer_send_sync() {
    let jit = JitCompiler::new(JitConfig::default());
    let func = build_add();
    let ext: HashMap<String, *const u8> = HashMap::new();

    let buf = jit
        .compile_raw(&[func], &ext)
        .expect("compile_raw should succeed");

    // Verify the buffer can be sent to another thread and used there.
    let handle = std::thread::spawn(move || {
        let f: extern "C" fn(i64, i64) -> i64 = unsafe { buf.get_fn("add").expect("add") };
        f(10, 20)
    });

    assert_eq!(handle.join().unwrap(), 30);
}

// ---------------------------------------------------------------------------
// Test: empty function list
// ---------------------------------------------------------------------------

#[test]
fn test_jit_empty_functions() {
    let jit = JitCompiler::new(JitConfig::default());
    let ext: HashMap<String, *const u8> = HashMap::new();

    match jit.compile_raw(&[], &ext) {
        Err(JitError::EmptyExecutableBuffer { function_count }) => {
            assert_eq!(function_count, 0);
        }
        Err(other) => panic!("expected EmptyExecutableBuffer, got {other:?}"),
        Ok(buf) => panic!(
            "empty compile_raw input must not publish executable buffer: allocated_size={}",
            buf.allocated_size()
        ),
    }
}

#[test]
fn test_jit_zero_instruction_function_rejected() {
    let jit = JitCompiler::new(JitConfig::default());
    let ext: HashMap<String, *const u8> = HashMap::new();

    match jit.compile_raw(&[build_zero_instruction_function()], &ext) {
        Err(JitError::EmptyExecutableBuffer { function_count }) => {
            assert_eq!(function_count, 1);
        }
        Err(other) => panic!("expected EmptyExecutableBuffer, got {other:?}"),
        Ok(buf) => panic!(
            "zero-instruction function must not publish executable buffer: allocated_size={}",
            buf.allocated_size()
        ),
    }
}

// ---------------------------------------------------------------------------
// Test: large function buffer (many filler instructions, multi-page mmap)
// ---------------------------------------------------------------------------

#[test]
fn test_jit_large_function() {
    let jit = JitCompiler::new(JitConfig::default());
    // 4096 instructions = 16384 bytes = exactly one Apple Silicon page.
    // Add the RET instruction, and we spill into a second page.
    let func = build_large_filler_function("big_fn", 4096);
    let ext: HashMap<String, *const u8> = HashMap::new();

    let buf = jit
        .compile_raw(&[func], &ext)
        .expect("compile_raw should succeed with large function");

    // The function should still work — filler ADD X8,X8,#0 doesn't affect X0.
    let f: extern "C" fn(i64) -> i64 =
        unsafe { buf.get_fn("big_fn").expect("should find 'big_fn'") };

    assert_eq!(f(42), 42);
    assert_eq!(f(0), 0);

    // Buffer should be at least 2 pages (filler + RET > 1 page on Apple Silicon).
    assert!(
        buf.allocated_size() >= 2 * 16384,
        "buffer should span multiple pages, got {} bytes",
        buf.allocated_size()
    );
}

// ---------------------------------------------------------------------------
// Test: JitConfig with O0 optimization
// ---------------------------------------------------------------------------

#[test]
fn test_jit_config_o0() {
    let jit = JitCompiler::new(JitConfig {
        opt_level: OptLevel::O0,
        verify: false,
        ..JitConfig::default()
    });

    let func = build_add();
    let ext: HashMap<String, *const u8> = HashMap::new();

    let buf = jit
        .compile_raw(&[func], &ext)
        .expect("O0 compile should succeed");

    let f: extern "C" fn(i64, i64) -> i64 = unsafe { buf.get_fn("add").expect("add") };

    assert_eq!(f(1, 2), 3);
}

// ---------------------------------------------------------------------------
// Test: mixed internal + external calls
// ---------------------------------------------------------------------------

extern "C" fn host_square(x: i64) -> i64 {
    x * x
}

#[test]
fn test_jit_mixed_internal_external() {
    let jit = JitCompiler::new(JitConfig::default());

    // Internal function: add
    let add_fn = build_add();

    // Caller that calls internal "add" via BL
    let call_add = build_caller("call_add", "add");

    // Caller that calls external "_host_square" via BL
    let call_square = build_extern_caller("_host_square");

    let mut ext: HashMap<String, *const u8> = HashMap::new();
    ext.insert("_host_square".to_string(), host_square as *const u8);

    let buf = jit
        .compile_raw(&[add_fn, call_add, call_square], &ext)
        .expect("mixed internal/external compile should succeed");

    // Test internal call
    let fa: extern "C" fn(i64, i64) -> i64 = unsafe { buf.get_fn("call_add").expect("call_add") };
    assert_eq!(fa(10, 20), 30);

    // Test external call (call_extern calls _host_square)
    let fs: extern "C" fn(i64) -> i64 = unsafe { buf.get_fn("call_extern").expect("call_extern") };
    assert_eq!(fs(5), 25);
    assert_eq!(fs(0), 0);
    assert_eq!(fs(-3), 9);
}

// ---------------------------------------------------------------------------
// Test: branch patching out of range error
// ---------------------------------------------------------------------------

#[test]
fn test_jit_branch_out_of_range() {
    // BL has a +/-128MB range (26-bit signed offset * 4 bytes).
    // We can't easily allocate 128MB of code in a test, but we can verify
    // the error path exists by checking the JitError::BranchOutOfRange variant.
    // The patch_branch26 function validates the range and returns this error.
    //
    // This test verifies the error type is constructible and the compile_raw
    // path would propagate it. A true out-of-range test would require
    // generating ~32M instructions which is impractical for a unit test.

    let err = JitError::BranchOutOfRange {
        offset: 0,
        target: 256 * 1024 * 1024, // 256MB — beyond +-128MB
        distance: 256 * 1024 * 1024,
    };
    let msg = format!("{}", err);
    assert!(
        msg.contains("branch out of range"),
        "error message: {}",
        msg
    );
}

// ---------------------------------------------------------------------------
// Test: multiple large functions (stress test for layout)
// ---------------------------------------------------------------------------

#[test]
fn test_jit_multiple_large_functions() {
    let jit = JitCompiler::new(JitConfig::default());

    // 3 functions, each 1024 NOPs = 4KB code each, plus identity semantics.
    let f1 = build_large_filler_function("big_a", 1024);
    let f2 = build_large_filler_function("big_b", 1024);
    let f3 = build_large_filler_function("big_c", 1024);

    let ext: HashMap<String, *const u8> = HashMap::new();
    let buf = jit
        .compile_raw(&[f1, f2, f3], &ext)
        .expect("compile_raw should succeed with multiple large functions");

    // All three functions should be independently callable.
    let fa: extern "C" fn(i64) -> i64 = unsafe { buf.get_fn("big_a").expect("big_a") };
    let fb: extern "C" fn(i64) -> i64 = unsafe { buf.get_fn("big_b").expect("big_b") };
    let fc: extern "C" fn(i64) -> i64 = unsafe { buf.get_fn("big_c").expect("big_c") };

    assert_eq!(fa(1), 1);
    assert_eq!(fb(2), 2);
    assert_eq!(fc(3), 3);

    // Verify they are at different offsets.
    let ptr_a = buf.get_fn_ptr("big_a").unwrap();
    let ptr_b = buf.get_fn_ptr("big_b").unwrap();
    let ptr_c = buf.get_fn_ptr("big_c").unwrap();
    assert_ne!(
        ptr_a, ptr_b,
        "big_a and big_b should be at different addresses"
    );
    assert_ne!(
        ptr_b, ptr_c,
        "big_b and big_c should be at different addresses"
    );
}

// ---------------------------------------------------------------------------
// Test: function symbols are at expected offsets
// ---------------------------------------------------------------------------

#[test]
fn test_jit_symbol_offsets() {
    let jit = JitCompiler::new(JitConfig::default());

    // add: 2 instructions (ADD + RET) = 8 bytes
    // sub: 2 instructions (SUB + RET) = 8 bytes
    let funcs = vec![build_add(), build_sub()];
    let ext: HashMap<String, *const u8> = HashMap::new();

    let buf = jit
        .compile_raw(&funcs, &ext)
        .expect("compile_raw should succeed");

    // Verify symbol offsets through the iterator.
    let offsets: HashMap<&str, u64> = buf.symbols().collect();
    assert_eq!(offsets["add"], 0, "first function should be at offset 0");
    assert_eq!(
        offsets["sub"], 8,
        "second function should start at offset 8 (after 2 x 4-byte instructions)"
    );
}

// ---------------------------------------------------------------------------
// Test: drop safety — ExecutableBuffer cleans up on drop
// ---------------------------------------------------------------------------

#[test]
fn test_jit_buffer_drop() {
    // Compile, use, then drop the buffer.
    // If munmap is broken, this would cause a memory leak or crash.
    for _ in 0..10 {
        let jit = JitCompiler::new(JitConfig::default());
        let func = build_add();
        let ext: HashMap<String, *const u8> = HashMap::new();

        let buf = jit.compile_raw(&[func], &ext).expect("compile");
        let f: extern "C" fn(i64, i64) -> i64 = unsafe { buf.get_fn("add").expect("add") };
        assert_eq!(f(1, 1), 2);
        // buf drops here, calling munmap
    }
}

// ===========================================================================
// Issue #363 — JIT re-entrant compilation support
// ---------------------------------------------------------------------------
// Verifies that Trust Codegen's JIT supports the three re-entrancy scenarios ty
// needs for interpreter fallback + re-entrant compilation:
//
//   1. Multiple `ExecutableBuffer`s active simultaneously
//   2. Cross-buffer function calls (buffer A calls into buffer B via an extern
//      symbol resolved to a pointer into buffer B's mmap)
//   3. JIT compilation on the main thread while JIT code executes on another
//      thread
//
// All three are expected to work out of the box: each `ExecutableBuffer` owns
// an independent mmap region, the veneer trampoline embeds a full 64-bit
// absolute address (reachable to any target), and `JitCompiler::compile_raw`
// takes `&self` and carries no globally shared mutable state.
// ===========================================================================

// ---------------------------------------------------------------------------
// Helper: external two-arg caller via BL symbol reference
// ---------------------------------------------------------------------------

/// Build a function that calls an external symbol via BL, forwarding X0 and X1.
///
/// `fn caller(a: i64, b: i64) -> i64 { callee_symbol(a, b) }`
fn build_two_arg_extern_caller(caller_name: &str, callee_symbol: &str) -> MachFunction {
    let sig = Signature::new(vec![Type::I64, Type::I64], vec![Type::I64]);
    let mut func = MachFunction::new(caller_name.to_string(), sig);
    let entry = func.entry;

    // STP FP, LR, [SP, #-16]!
    let stp = MachInst::new(
        AArch64Opcode::StpPreIndex,
        vec![
            MachOperand::PReg(FP),
            MachOperand::PReg(LR),
            Special(SpecialReg::SP),
            MachOperand::Imm(-16),
        ],
    );
    let stp_id = func.push_inst(stp);
    func.append_inst(entry, stp_id);

    // BL <external symbol> (args already in X0, X1)
    let bl = MachInst::new(
        AArch64Opcode::Bl,
        vec![MachOperand::Symbol(callee_symbol.to_string())],
    );
    let bl_id = func.push_inst(bl);
    func.append_inst(entry, bl_id);

    // LDP FP, LR, [SP], #16
    let ldp = MachInst::new(
        AArch64Opcode::LdpPostIndex,
        vec![
            MachOperand::PReg(FP),
            MachOperand::PReg(LR),
            Special(SpecialReg::SP),
            MachOperand::Imm(16),
        ],
    );
    let ldp_id = func.push_inst(ldp);
    func.append_inst(entry, ldp_id);

    // RET
    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    let ret_id = func.push_inst(ret);
    func.append_inst(entry, ret_id);

    func
}

/// Build a function that calls an external symbol via BL, forwarding X0 and X1.
///
/// `fn caller(base: Ptr, delta: i64) -> Ptr { callee_symbol(base, delta) }`
fn build_ptr_i64_extern_caller(caller_name: &str, callee_symbol: &str) -> MachFunction {
    let sig = Signature::new(vec![Type::Ptr, Type::I64], vec![Type::Ptr]);
    let mut func = MachFunction::new(caller_name.to_string(), sig);
    let entry = func.entry;

    // STP FP, LR, [SP, #-16]!
    let stp = MachInst::new(
        AArch64Opcode::StpPreIndex,
        vec![
            MachOperand::PReg(FP),
            MachOperand::PReg(LR),
            Special(SpecialReg::SP),
            MachOperand::Imm(-16),
        ],
    );
    let stp_id = func.push_inst(stp);
    func.append_inst(entry, stp_id);

    // BL <external symbol> (Ptr in X0, i64 in X1, Ptr result in X0)
    let bl = MachInst::new(
        AArch64Opcode::Bl,
        vec![MachOperand::Symbol(callee_symbol.to_string())],
    );
    let bl_id = func.push_inst(bl);
    func.append_inst(entry, bl_id);

    // LDP FP, LR, [SP], #16
    let ldp = MachInst::new(
        AArch64Opcode::LdpPostIndex,
        vec![
            MachOperand::PReg(FP),
            MachOperand::PReg(LR),
            Special(SpecialReg::SP),
            MachOperand::Imm(16),
        ],
    );
    let ldp_id = func.push_inst(ldp);
    func.append_inst(entry, ldp_id);

    // RET
    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    let ret_id = func.push_inst(ret);
    func.append_inst(entry, ret_id);

    func
}

/// Build `fn call_writer_then_reload(slot: Ptr) -> i64`.
///
/// The external call receives the pointer argument and writes `7` through it.
/// The JIT code then reloads the saved pointer after the call and returns the
/// pointee value. Returning the pre-call value would mean the call was not
/// respected as a memory barrier for the pointer argument.
fn build_call_writer_then_reload(callee_symbol: &str) -> MachFunction {
    let sig = Signature::new(vec![Type::Ptr], vec![Type::I64]);
    let mut func = MachFunction::new("call_writer_then_reload".to_string(), sig);
    let entry = func.entry;

    // STP FP, LR, [SP, #-32]!
    let stp = MachInst::new(
        AArch64Opcode::StpPreIndex,
        vec![
            MachOperand::PReg(FP),
            MachOperand::PReg(LR),
            Special(SpecialReg::SP),
            MachOperand::Imm(-32),
        ],
    );
    let stp_id = func.push_inst(stp);
    func.append_inst(entry, stp_id);

    // Save the incoming pointer. X0 is caller-saved across the external call.
    let save_ptr = MachInst::new(
        AArch64Opcode::StrRI,
        vec![
            MachOperand::PReg(X0),
            Special(SpecialReg::SP),
            MachOperand::Imm(16),
        ],
    );
    let save_ptr_id = func.push_inst(save_ptr);
    func.append_inst(entry, save_ptr_id);

    // BL <external writer> (slot pointer is still in X0)
    let bl = MachInst::new(
        AArch64Opcode::Bl,
        vec![MachOperand::Symbol(callee_symbol.to_string())],
    );
    let bl_id = func.push_inst(bl);
    func.append_inst(entry, bl_id);

    // Reload the saved pointer after the call, then load the pointee value.
    let reload_ptr = MachInst::new(
        AArch64Opcode::LdrRI,
        vec![
            MachOperand::PReg(X8),
            Special(SpecialReg::SP),
            MachOperand::Imm(16),
        ],
    );
    let reload_ptr_id = func.push_inst(reload_ptr);
    func.append_inst(entry, reload_ptr_id);

    let reload_value = MachInst::new(
        AArch64Opcode::LdrRI,
        vec![
            MachOperand::PReg(X0),
            MachOperand::PReg(X8),
            MachOperand::Imm(0),
        ],
    );
    let reload_value_id = func.push_inst(reload_value);
    func.append_inst(entry, reload_value_id);

    // LDP FP, LR, [SP], #32
    let ldp = MachInst::new(
        AArch64Opcode::LdpPostIndex,
        vec![
            MachOperand::PReg(FP),
            MachOperand::PReg(LR),
            Special(SpecialReg::SP),
            MachOperand::Imm(32),
        ],
    );
    let ldp_id = func.push_inst(ldp);
    func.append_inst(entry, ldp_id);

    // Keep the following external-call veneer literal slot 8-byte aligned.
    let align_pad = MachInst::new(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(X8),
            MachOperand::PReg(X8),
            MachOperand::Imm(0),
        ],
    );
    let align_pad_id = func.push_inst(align_pad);
    func.append_inst(entry, align_pad_id);

    let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
    let ret_id = func.push_inst(ret);
    func.append_inst(entry, ret_id);

    func
}

// ---------------------------------------------------------------------------
// Test: multiple independent JIT buffers can be live simultaneously
// ---------------------------------------------------------------------------

#[test]
fn test_jit_multiple_buffers_simultaneously() {
    let jit_a = JitCompiler::new(JitConfig::default());
    let jit_b = JitCompiler::new(JitConfig::default());
    let ext: HashMap<String, *const u8> = HashMap::new();

    let buf_a = jit_a
        .compile_raw(&[build_add()], &ext)
        .expect("compile_raw should succeed for add");
    let buf_b = jit_b
        .compile_raw(&[build_sub()], &ext)
        .expect("compile_raw should succeed for sub");

    let add: extern "C" fn(i64, i64) -> i64 = unsafe { buf_a.get_fn("add").expect("add") };
    let sub: extern "C" fn(i64, i64) -> i64 = unsafe { buf_b.get_fn("sub").expect("sub") };

    assert_eq!(add(3, 4), 7);
    assert_eq!(sub(10, 3), 7);
    assert_eq!(add(-5, 2), -3);
    assert_eq!(sub(1, 9), -8);

    let buf_c = jit_a
        .compile_raw(&[build_mul()], &ext)
        .expect("reused compiler should produce another independent buffer");
    let mul: extern "C" fn(i64, i64) -> i64 = unsafe { buf_c.get_fn("mul").expect("mul") };

    assert_eq!(add(20, 22), 42);
    assert_eq!(sub(100, 58), 42);
    assert_eq!(mul(6, 7), 42);
}

// ---------------------------------------------------------------------------
// Test: cross-buffer call via extern symbol trampoline
// ---------------------------------------------------------------------------

#[test]
fn test_jit_cross_buffer_call_via_extern_symbol() {
    let jit_b = JitCompiler::new(JitConfig::default());
    let ext_b: HashMap<String, *const u8> = HashMap::new();

    let buf_b = jit_b
        .compile_raw(&[build_sub()], &ext_b)
        .expect("compile_raw should succeed for sub");
    let ptr_b = buf_b.get_fn_ptr("sub").expect("should find 'sub' symbol");

    let jit_a = JitCompiler::new(JitConfig::default());
    let mut ext_a: HashMap<String, *const u8> = HashMap::new();
    ext_a.insert("_bridge_sub".to_string(), ptr_b);

    let buf_a = jit_a
        .compile_raw(
            &[build_two_arg_extern_caller("call_sub_cross", "_bridge_sub")],
            &ext_a,
        )
        .expect("compile_raw should succeed for cross-buffer extern call");

    // This proves the veneer trampoline mechanism can resolve extern symbols to
    // addresses in any memory region, including other JIT buffers.
    let call_sub_cross: extern "C" fn(i64, i64) -> i64 =
        unsafe { buf_a.get_fn("call_sub_cross").expect("call_sub_cross") };

    assert_eq!(call_sub_cross(10, 3), 7);
    assert_eq!(call_sub_cross(0, 0), 0);
    assert_eq!(call_sub_cross(100, 50), 50);
    assert_eq!(call_sub_cross(-5, 5), -10);

    // Sanity-check: both buffers are still reachable after the cross call.
    let sub_direct: extern "C" fn(i64, i64) -> i64 =
        unsafe { buf_b.get_fn("sub").expect("sub direct") };
    assert_eq!(sub_direct(42, 1), 41);
}

extern "C" fn trust_cg_jit_test_ptr_stride(base: *mut u64, delta: i64) -> *mut u64 {
    assert!(delta >= 0, "test helper expects non-negative delta");
    unsafe { base.add(delta as usize) }
}

extern "C" fn trust_cg_jit_test_write_seven(slot: *mut u64) {
    unsafe {
        *slot = 7;
    }
}

#[test]
fn test_jit_external_symbol_ptr_i64_to_ptr_abi() {
    let jit = JitCompiler::new(JitConfig::default());
    let mut ext: HashMap<String, *const u8> = HashMap::new();
    ext.insert(
        "_host_ptr_stride".to_string(),
        trust_cg_jit_test_ptr_stride as *const u8,
    );

    let buf = jit
        .compile_raw(
            &[build_ptr_i64_extern_caller(
                "call_ptr_stride",
                "_host_ptr_stride",
            )],
            &ext,
        )
        .expect("compile_raw should succeed for ptr+i64->ptr extern call");

    let call_ptr_stride: extern "C" fn(*mut u64, i64) -> *mut u64 =
        unsafe { buf.get_fn("call_ptr_stride").expect("call_ptr_stride") };

    let mut words = [11u64, 22, 33, 44, 55];
    let stepped = call_ptr_stride(words.as_mut_ptr(), 3);

    assert_eq!(stepped, unsafe { words.as_mut_ptr().add(3) });
    assert_eq!(unsafe { *stepped }, 44);
}

#[test]
fn test_jit_external_call_is_memory_barrier_for_pointer_argument() {
    let jit = JitCompiler::new(JitConfig::default());
    let mut ext: HashMap<String, *const u8> = HashMap::new();
    ext.insert(
        "_trust_cg_jit_test_write_seven".to_string(),
        trust_cg_jit_test_write_seven as *const u8,
    );

    let buf = jit
        .compile_raw(
            &[build_call_writer_then_reload(
                "_trust_cg_jit_test_write_seven",
            )],
            &ext,
        )
        .expect("compile_raw should succeed for external writer call");

    let f: extern "C" fn(*mut u64) -> u64 = unsafe {
        buf.get_fn("call_writer_then_reload")
            .expect("call_writer_then_reload symbol")
    };

    let mut slot = 3u64;
    assert_eq!(f(&mut slot), 7);
    assert_eq!(slot, 7);
}

// ---------------------------------------------------------------------------
// Test: compile on one thread while JIT code executes on another
// ---------------------------------------------------------------------------

#[test]
fn test_jit_concurrent_compile_while_executing() {
    let jit = JitCompiler::new(JitConfig::default());
    let ext: HashMap<String, *const u8> = HashMap::new();

    let factorial_buf = jit
        .compile_raw(&[build_factorial()], &ext)
        .expect("compile_raw should succeed for factorial");
    let factorial_buf = std::sync::Arc::new(factorial_buf);

    let worker_buf = std::sync::Arc::clone(&factorial_buf);
    let worker = std::thread::spawn(move || {
        let factorial: extern "C" fn(i64) -> i64 =
            unsafe { worker_buf.get_fn("factorial").expect("factorial") };

        let mut sum = 0i64;
        for _ in 0..10_000 {
            sum += factorial(10);
        }
        sum
    });

    // This proves `JitCompiler::compile_raw` has no shared mutable state that
    // would make concurrent compile-while-execute unsafe. It does not prove
    // concurrent COMPILATION on multiple threads (see the next test).
    let mut verified_compilations = 0usize;
    for i in 0..32 {
        match i % 3 {
            0 => {
                let buf = jit.compile_raw(&[build_add()], &ext).expect("compile add");
                let f: extern "C" fn(i64, i64) -> i64 = unsafe { buf.get_fn("add").expect("add") };
                assert_eq!(f(i as i64, 2), i as i64 + 2);
            }
            1 => {
                let buf = jit.compile_raw(&[build_sub()], &ext).expect("compile sub");
                let f: extern "C" fn(i64, i64) -> i64 = unsafe { buf.get_fn("sub").expect("sub") };
                assert_eq!(f(i as i64, 2), i as i64 - 2);
            }
            _ => {
                let buf = jit.compile_raw(&[build_mul()], &ext).expect("compile mul");
                let f: extern "C" fn(i64, i64) -> i64 = unsafe { buf.get_fn("mul").expect("mul") };
                assert_eq!(f(i as i64, 2), i as i64 * 2);
            }
        }
        verified_compilations += 1;
    }

    let worker_sum = worker.join().expect("worker thread should succeed");
    // factorial(10) = 3_628_800, summed 10_000 times = 36_288_000_000.
    assert_eq!(worker_sum, 36_288_000_000);
    assert_eq!(verified_compilations, 32);
}

// ---------------------------------------------------------------------------
// Test: multiple threads can compile independently with separate JIT instances
// ---------------------------------------------------------------------------

#[test]
fn test_jit_concurrent_compilation_multiple_threads() {
    let handles: Vec<_> = (0..4)
        .map(|i| {
            std::thread::spawn(move || {
                let jit = JitCompiler::new(JitConfig::default());
                let ext: HashMap<String, *const u8> = HashMap::new();

                match i % 4 {
                    0 => {
                        let buf = jit.compile_raw(&[build_add()], &ext).expect("compile add");
                        let f: extern "C" fn(i64, i64) -> i64 =
                            unsafe { buf.get_fn("add").expect("add") };
                        assert_eq!(f(40, 2), 42);
                    }
                    1 => {
                        let buf = jit.compile_raw(&[build_sub()], &ext).expect("compile sub");
                        let f: extern "C" fn(i64, i64) -> i64 =
                            unsafe { buf.get_fn("sub").expect("sub") };
                        assert_eq!(f(50, 8), 42);
                    }
                    2 => {
                        let buf = jit.compile_raw(&[build_mul()], &ext).expect("compile mul");
                        let f: extern "C" fn(i64, i64) -> i64 =
                            unsafe { buf.get_fn("mul").expect("mul") };
                        assert_eq!(f(6, 7), 42);
                    }
                    _ => {
                        let buf = jit
                            .compile_raw(&[build_return_const()], &ext)
                            .expect("compile return_const");
                        let f: extern "C" fn() -> i64 =
                            unsafe { buf.get_fn("return_const").expect("return_const") };
                        assert_eq!(f(), 42);
                    }
                }
            })
        })
        .collect();

    for handle in handles {
        handle
            .join()
            .expect("thread should compile and execute successfully");
    }
}

// ===========================================================================
// Issue #355 + #357 — JIT soundness (lifetime-bound APIs, icache ordering)
// ===========================================================================

#[test]
fn test_jit_buffer_get_fn_bound_basic() {
    let jit = JitCompiler::new(JitConfig::default());
    let ext: HashMap<String, *const u8> = HashMap::new();

    let buf = jit
        .compile_raw(&[build_add()], &ext)
        .expect("compile_raw should succeed");

    let add = unsafe {
        buf.get_fn_bound::<extern "C" fn(i64, i64) -> i64>("add")
            .expect("should find 'add'")
    };

    assert_eq!((*add.as_ref())(10, 20), 30);
}

#[test]
fn test_jit_buffer_get_fn_ptr_bound_basic() {
    let jit = JitCompiler::new(JitConfig::default());
    let ext: HashMap<String, *const u8> = HashMap::new();

    let buf = jit
        .compile_raw(&[build_add()], &ext)
        .expect("compile_raw should succeed");

    let add_ptr = buf.get_fn_ptr_bound("add").expect("should find 'add'");
    let add: extern "C" fn(i64, i64) -> i64 = unsafe { std::mem::transmute(add_ptr.as_ptr()) };

    assert_eq!(add(7, 8), 15);
}

#[test]
fn test_jit_buffer_bound_send() {
    let jit = JitCompiler::new(JitConfig::default());
    let ext: HashMap<String, *const u8> = HashMap::new();

    let buf = jit
        .compile_raw(&[build_add()], &ext)
        .expect("compile_raw should succeed");

    let handle = std::thread::spawn(move || {
        let add = unsafe {
            buf.get_fn_bound::<extern "C" fn(i64, i64) -> i64>("add")
                .expect("should find 'add'")
        };
        (*add.as_ref())(40, 2)
    });

    assert_eq!(handle.join().unwrap(), 42);
}

/// Regression smoke test for issue #357: if the icache order regresses,
/// execution on strict implementations would fault.
#[test]
fn test_jit_icache_flush_before_mprotect_ordering() {
    let jit = JitCompiler::new(JitConfig::default());
    let ext: HashMap<String, *const u8> = HashMap::new();

    let buf = jit
        .compile_raw(&[build_add()], &ext)
        .expect("compile_raw should succeed");

    let add = unsafe {
        buf.get_fn_bound::<extern "C" fn(i64, i64) -> i64>("add")
            .expect("should find 'add'")
    };

    for i in 0..32 {
        assert_eq!((*add.as_ref())(i, i + 1), i + (i + 1));
    }
}

// ===========================================================================
// Issue #367 — process-symbol dlsym fallback in compile_raw
// ---------------------------------------------------------------------------
// ty's JIT runtime defines `#[no_mangle] pub extern "C"` helpers that it
// cannot populate into `extern_symbols` without another dlsym step itself.
// Verify that compile_raw transparently resolves such symbols via
// `dlsym(RTLD_DEFAULT, ...)` when they are absent from `extern_symbols`,
// prefers an explicit `extern_symbols` entry when both exist, and surfaces
// a clean `UnresolvedSymbol` error (no zero-addr veneer — issue #353) when
// neither path finds the symbol.
// ===========================================================================

// For the pure-dlsym path we use `abs` from libc — guaranteed visible
// through `dlsym(RTLD_DEFAULT, ...)` on any Unix host. Rust test binaries
// do not re-export their own `no_mangle` symbols, so dispatching to a
// libc symbol is the portable way to exercise the fallback.
unsafe extern "C" {
    fn abs(x: std::os::raw::c_int) -> std::os::raw::c_int;
}

#[cfg(unix)]
#[test]
fn test_jit_dlsym_fallback_resolves_libc_symbol() {
    // extern_symbols is EMPTY — compile_raw must resolve `abs` through
    // the dlsym(RTLD_DEFAULT) fallback added for #367.
    let jit = JitCompiler::new(JitConfig::default());
    let ext: HashMap<String, *const u8> = HashMap::new();

    // `resolve_extern` strips the leading underscore on macOS before the
    // dlsym lookup; on Linux the bare symbol already matches. The
    // generated-code reference uses the platform's native mangled form.
    #[cfg(target_os = "macos")]
    let sym = "_abs";
    #[cfg(not(target_os = "macos"))]
    let sym = "abs";

    // `build_extern_caller` builds a function `call_extern(x) -> extern(x)`
    // with an i64 signature; libc `abs` takes c_int (i32). We verify that
    // compile_raw resolved the symbol (no UnresolvedSymbol error) and that
    // the call lands in libc. Inputs are kept within i32 range.
    let caller = build_extern_caller(sym);
    let buf = jit
        .compile_raw(&[caller], &ext)
        .expect("compile_raw should resolve libc `abs` via dlsym fallback");

    // Sanity-check libc abs is linked into this test binary (touches the
    // extern so the linker does not GC it on some platforms).
    assert_eq!(unsafe { abs(-1) }, 1);

    // Confirm the JIT buffer actually dispatches into libc `abs`. We pass
    // non-negative i64 values (i32-safe) since `abs(i32::MIN)` is UB.
    let f: extern "C" fn(i64) -> i64 = unsafe {
        buf.get_fn("call_extern")
            .expect("should find 'call_extern'")
    };
    // abs(5) == 5, abs(12345) == 12345. The sign-extended i64 return of an
    // i32 result is the same for non-negative inputs.
    assert_eq!(f(5), 5);
    assert_eq!(f(12345), 12345);
}

// Host helper reachable only via its static address (NOT no_mangle).
extern "C" fn trust_cg_jit_test_override_shadow(x: i64) -> i64 {
    x + 9999
}

#[cfg(unix)]
#[test]
fn test_jit_extern_symbols_preferred_over_dlsym_end_to_end() {
    // `extern_symbols` must take precedence over the dlsym fallback. We use
    // the libc symbol `abs` as the name so that dlsym WOULD resolve — but
    // extern_symbols maps the name to `trust_cg_jit_test_override_shadow`,
    // which adds 9999 rather than computing absolute value.
    let jit = JitCompiler::new(JitConfig::default());

    #[cfg(target_os = "macos")]
    let sym = "_abs";
    #[cfg(not(target_os = "macos"))]
    let sym = "abs";

    let mut ext: HashMap<String, *const u8> = HashMap::new();
    ext.insert(
        sym.to_string(),
        trust_cg_jit_test_override_shadow as *const u8,
    );

    let caller = build_extern_caller(sym);
    let buf = jit
        .compile_raw(&[caller], &ext)
        .expect("compile_raw should succeed");

    let f: extern "C" fn(i64) -> i64 = unsafe {
        buf.get_fn("call_extern")
            .expect("should find 'call_extern'")
    };
    // If extern_symbols were ignored we'd get |x| (libc abs). The shadow
    // helper instead adds 9999.
    assert_eq!(f(0), 9999);
    assert_eq!(f(1), 10000);
}

#[test]
fn test_jit_missing_symbol_returns_unresolved_not_zero_addr() {
    // A symbol name unlikely to exist in any process — neither extern_symbols
    // nor dlsym can resolve it. compile_raw must surface `UnresolvedSymbol`
    // rather than emitting a veneer with address 0 (issue #353).
    let jit = JitCompiler::new(JitConfig::default());
    let ext: HashMap<String, *const u8> = HashMap::new();

    let caller = build_extern_caller("_trust_cg_jit_definitely_missing_symbol_xyzzy_367");
    // Do not use `expect_err` — `ExecutableBuffer` does not implement Debug.
    match jit.compile_raw(&[caller], &ext) {
        Ok(_) => panic!("compile_raw must fail when symbol cannot be resolved"),
        Err(JitError::UnresolvedSymbol(name)) => {
            assert!(
                name.contains("trust_cg_jit_definitely_missing_symbol_xyzzy_367"),
                "error should name the missing symbol, got: {name}"
            );
        }
        Err(other) => panic!("expected UnresolvedSymbol, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// First-class closure aggregate round-trip (#678 closure aggregates).
//
// A `Ty::Closure(ClosureTyId)` resolves through `module.closure_types` to an
// ordered list of captured value types — i.e. a struct of its captures. The
// lower adapter treats it as `Type::Struct([capture types...])` with C-layout
// (natural-alignment, in-order) offsets, so:
//   * construction stores each capture operand at its struct-layout offset
//     (`Alloca` + per-capture `InsertField` -> StructGep + Store), and
//   * `ExtractElement(Ty::Closure, idx)` loads the capture at that offset
//     (StructGep + Load).
//
// This test builds a HETEROGENEOUS closure capturing `[I32, I64, I8]` from
// runtime operands and, in three separate JIT-compiled functions, extracts
// each capture and returns it. Executing natively on aarch64 proves the
// construction + extraction round-trip preserves each value at its correct
// per-capture offset (a wrong offset would corrupt a neighbouring capture or
// read garbage).
// ---------------------------------------------------------------------------

/// Build a module with three functions `get_capture_0/1/2`, each of which:
///   1. takes the three capture operands `(i32, i64, i8)` as params,
///   2. allocates closure storage and stores each operand into its capture
///      slot via `InsertField` (the closure-aggregate construction path),
///   3. extracts capture `N` via `ExtractElement(Ty::Closure, N)`, and
///   4. returns it zero-extended to `i64`.
fn build_closure_capture_roundtrip_module() -> trust_ir::Module {
    use trust_ir::{
        Block as TrustIrBlock, BlockId, CastOp, ClosureTy, ClosureTyId, Constant, FuncId, FuncTy,
        Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, Ty, ValueId,
    };

    let mut module = TrustIrModule::new("closure_capture_roundtrip");

    // The closure's bare-fn signature is irrelevant to the capture layout, but
    // `ClosureTy` references a func type, so register a trivial one first.
    let bare_fn = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    // Heterogeneous captures: I32, I64, I8 — distinct widths exercise the
    // natural-alignment struct layout (I32 @ 0, I64 @ 8 after padding, I8 @ 16).
    let closure_id: ClosureTyId = module.add_closure_type(ClosureTy {
        func: bare_fn,
        captures: vec![Ty::I32, Ty::I64, Ty::I8],
    });
    let closure_ty = Ty::Closure(closure_id);

    // Each extractor function: (i32, i64, i8) -> i64.
    let extractor_fty = module.add_func_type(FuncTy {
        params: vec![Ty::I32, Ty::I64, Ty::I8],
        returns: vec![Ty::I64],
        is_vararg: false,
    });

    for (func_idx, capture_index) in [0u32, 1, 2].into_iter().enumerate() {
        let name = format!("get_capture_{capture_index}");
        let capture_ty = match capture_index {
            0 => Ty::I32,
            1 => Ty::I64,
            _ => Ty::I8,
        };

        // Value numbering:
        //   v0,v1,v2  = params (the I32, I64, I8 capture operands)
        //   v3        = closure storage (Alloca, typed Ptr)
        //   v4        = after InsertField field 0 (typed Closure)
        //   v5        = after InsertField field 1 (typed Closure)
        //   v6        = after InsertField field 2 (typed Closure)
        //   v7        = constant capture index
        //   v8        = ExtractElement result (the selected capture)
        //   v9        = result widened to i64 (when needed)
        let mut body = vec![
            // Allocate closure-sized storage. `Alloca { ty: Closure }` sizes the
            // slot from the struct layout via `translate_ty`.
            InstrNode::new(Inst::Alloca {
                ty: closure_ty.clone(),
                count: None,
                align: None,
            })
            .with_result(ValueId::new(3)),
            // Store each capture operand into its capture slot. The first
            // InsertField takes the raw Alloca pointer as the aggregate; its
            // result (and every subsequent one) is typed `Ty::Closure`, so the
            // later ExtractElement sees a closure source.
            InstrNode::new(Inst::InsertField {
                ty: closure_ty.clone(),
                aggregate: ValueId::new(3),
                field: 0,
                value: ValueId::new(0),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::InsertField {
                ty: closure_ty.clone(),
                aggregate: ValueId::new(4),
                field: 1,
                value: ValueId::new(1),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::InsertField {
                ty: closure_ty.clone(),
                aggregate: ValueId::new(5),
                field: 2,
                value: ValueId::new(2),
            })
            .with_result(ValueId::new(6)),
            // Capture index as a constant (ExtractElement requires a constant
            // index for a struct-layout field access).
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(capture_index as i128),
            })
            .with_result(ValueId::new(7)),
            // Extract the selected capture from the closure value.
            InstrNode::new(Inst::ExtractElement {
                ty: capture_ty.clone(),
                array: ValueId::new(6),
                index: ValueId::new(7),
            })
            .with_result(ValueId::new(8)),
        ];

        // Widen the extracted capture to i64 for the return (capture 1 is
        // already i64). Use zero-extension — the test feeds non-negative values.
        let ret_val = if capture_ty == Ty::I64 {
            ValueId::new(8)
        } else {
            body.push(
                InstrNode::new(Inst::Cast {
                    op: CastOp::ZExt,
                    src_ty: capture_ty.clone(),
                    dst_ty: Ty::I64,
                    operand: ValueId::new(8),
                })
                .with_result(ValueId::new(9)),
            );
            ValueId::new(9)
        };
        body.push(InstrNode::new(Inst::Return {
            values: vec![ret_val],
        }));

        let mut func = TrustIrFunction::new(
            FuncId::new(func_idx as u32),
            &name,
            extractor_fty,
            BlockId::new(0),
        );
        func.blocks = vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![
                (ValueId::new(0), Ty::I32),
                (ValueId::new(1), Ty::I64),
                (ValueId::new(2), Ty::I8),
            ],
            body,
        }];
        module.add_function(func);
    }

    module
}

#[test]
fn test_jit_closure_capture_aggregate_roundtrip() {
    let module = build_closure_capture_roundtrip_module();
    let ext: HashMap<String, *const u8> = HashMap::new();
    let buf = compile_trust_ir_module_with_ty_o1_pipeline(&module, &ext)
        .expect("closure-aggregate construction + extraction must lower and JIT-compile");

    // Heterogeneous, distinct capture values. Non-negative so zero-extension is
    // exact; distinct bit patterns so a swapped/overlapping offset is detected.
    let cap0: i32 = 0x1122_3344; // 287454020
    let cap1: i64 = 0x2233_4455_6677_0011u64 as i64;
    let cap2: i8 = 0x55; // 85

    let get0: extern "C" fn(i32, i64, i8) -> i64 = unsafe {
        buf.get_fn_bound("get_capture_0")
            .expect("get_capture_0")
            .into_inner()
    };
    let get1: extern "C" fn(i32, i64, i8) -> i64 = unsafe {
        buf.get_fn_bound("get_capture_1")
            .expect("get_capture_1")
            .into_inner()
    };
    let get2: extern "C" fn(i32, i64, i8) -> i64 = unsafe {
        buf.get_fn_bound("get_capture_2")
            .expect("get_capture_2")
            .into_inner()
    };

    assert_eq!(
        get0(cap0, cap1, cap2),
        cap0 as u32 as i64,
        "capture 0 (I32) must round-trip through closure construction + extraction"
    );
    assert_eq!(
        get1(cap0, cap1, cap2),
        cap1,
        "capture 1 (I64) must round-trip at its struct-layout offset (8)"
    );
    assert_eq!(
        get2(cap0, cap1, cap2),
        cap2 as u8 as i64,
        "capture 2 (I8) must round-trip at its struct-layout offset (16)"
    );
}
