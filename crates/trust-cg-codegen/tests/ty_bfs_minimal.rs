// trust-cg-codegen/tests/ty_bfs_minimal.rs - minimal ty BFS kernel as trust_ir
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Minimal end-to-end integration test for the ty model-checker BFS backend.
// Verifies compile-time-offset i64 array load/store, runtime-index i64 GEP,
// pointer+i64 calling convention, and O0/O1/O2/O3 compilation behavior.
//
// Part of #270

#![cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

#[cfg(target_arch = "x86_64")]
use trust_cg_codegen::Target;
#[cfg(target_arch = "x86_64")]
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
#[cfg(target_arch = "aarch64")]
use trust_cg_codegen::pipeline::{Pipeline, PipelineConfig};

use trust_ir::{BinOp, Inst, InstrNode};
use trust_ir::{
    Block as TrustIrBlock, Constant, FuncTy, Function as TrustIrFunction, Module as TrustIrModule,
};
use trust_ir::{BlockId, FuncId, Ty, ValueId};

// ---------------------------------------------------------------------------
// Host-native object support (GB10 re-baseline): these e2e tests emit objects
// the HOST toolchain links and runs, so emission, magic checks, PIE flags and
// disassembly must follow the host format — Mach-O on macOS, ELF elsewhere.
// ---------------------------------------------------------------------------

/// The host triple the object pipeline targets: the file is compiled only on
/// the in-process JIT hosts (`aarch64`, `x86_64`), and the object it emits is
/// linked and run by the host `cc`.
#[allow(dead_code)]
fn host_triple() -> &'static str {
    match (cfg!(target_arch = "aarch64"), cfg!(target_os = "macos")) {
        (true, true) => "aarch64-apple-darwin",
        (true, false) => "aarch64-unknown-linux-gnu",
        (false, true) => "x86_64-apple-darwin",
        (false, false) => "x86_64-unknown-linux-gnu",
    }
}

#[allow(dead_code)]
fn host_no_pie_flag() -> &'static str {
    if cfg!(target_os = "macos") {
        "-Wl,-no_pie"
    } else {
        "-no-pie"
    }
}

#[allow(dead_code)]
fn host_object_magic_u32() -> u32 {
    if cfg!(target_os = "macos") {
        0xFEED_FACF
    } else {
        u32::from_le_bytes([0x7F, b'E', b'L', b'F'])
    }
}

#[allow(dead_code)]
fn assert_host_object_magic_bytes(obj_bytes: &[u8], context: &str) {
    assert!(obj_bytes.len() >= 4, "{context}: object too small");
    let expected = host_object_magic_u32().to_le_bytes();
    assert_eq!(
        &obj_bytes[0..4],
        &expected,
        "{context}: object magic must match the host-native format"
    );
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn has_cc() -> bool {
    Command::new("cc")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn make_test_dir(test_name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("trust_cg_e2e_{}", test_name));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    dir
}

fn write_object_file(dir: &Path, filename: &str, bytes: &[u8]) -> PathBuf {
    let path = dir.join(filename);
    fs::write(&path, bytes).expect("write .o file");
    path
}

fn write_c_driver(dir: &Path, filename: &str, source: &str) -> PathBuf {
    let path = dir.join(filename);
    fs::write(&path, source).expect("write C driver");
    path
}

fn link_with_cc(dir: &Path, driver_c: &Path, obj: &Path, output_name: &str) -> PathBuf {
    let binary = dir.join(output_name);
    let result = Command::new("cc")
        .arg("-o")
        .arg(&binary)
        .arg(driver_c)
        .arg(obj)
        .arg(host_no_pie_flag())
        .output()
        .expect("run cc");
    if !result.status.success() {
        let stderr = String::from_utf8_lossy(&result.stderr);
        panic!("Linking failed: {}", stderr);
    }
    binary
}

fn run_binary(binary: &Path) -> (i32, String) {
    let result = Command::new(binary).output().expect("run binary");
    let stdout = String::from_utf8_lossy(&result.stdout).to_string();
    (result.status.code().unwrap_or(-1), stdout)
}

fn cleanup(dir: &Path) {
    let _ = fs::remove_dir_all(dir);
}

/// Leave a copy of an emitted object under
/// `CARGO_TARGET_TMPDIR/<test target>/<test_name>_ty_bfs_kernel.o` (the
/// per-test directory is removed) so a runtime or instruction-count
/// measurement links the same bytes.
fn keep_object(test_name: &str, bytes: &[u8]) {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(env!("CARGO_CRATE_NAME"));
    fs::create_dir_all(&dir).expect("create kept-object dir");
    fs::write(dir.join(format!("{test_name}_ty_bfs_kernel.o")), bytes).expect("write kept object");
}

// ---------------------------------------------------------------------------
// Compilation helper
// ---------------------------------------------------------------------------

/// Compile the kernel to a host-native object. On AArch64 this is the
/// low-level `Pipeline` (the historical path, unchanged); that pipeline emits
/// AArch64 machine code only and refuses every other triple, so x86-64 goes
/// through `Compiler::compile`, the multi-target AOT entry that owns the
/// x86-64 lowering, encoding and ELF/Mach-O emission.
fn compile_trust_ir(
    trust_ir_func: &TrustIrFunction,
    module: &TrustIrModule,
    opt_level: OptLevel,
) -> Result<Vec<u8>, String> {
    #[cfg(target_arch = "aarch64")]
    {
        let (lir_func, _proof_ctx) = trust_cg_lower::translate_function_with_license(
            trust_ir_func,
            module,
            &permit_unlicensed(),
        )
        .map_err(|e| format!("adapter: {}", e))?;
        let config = PipelineConfig {
            target_triple: host_triple().to_string(),
            opt_level,
            emit_debug: false,
            ..Default::default()
        };
        let pipeline = Pipeline::new(config);
        pipeline
            .compile_function(&lir_func)
            .map_err(|e| format!("pipeline: {}", e))
    }
    #[cfg(target_arch = "x86_64")]
    {
        let _ = trust_ir_func;
        // The TY ahead-of-time driver keeps no proof certificates and asks
        // for the certificate-free allocation.
        compile_x86(module, opt_level, false, true)
    }
}

/// One x86-64 object compile of `module` as a TY driver configures it.
#[cfg(target_arch = "x86_64")]
fn compile_x86(
    module: &TrustIrModule,
    opt_level: OptLevel,
    emit_proofs: bool,
    x86_certificate_free_allocation: bool,
) -> Result<Vec<u8>, String> {
    install_driver_ra_policy();
    Compiler::new(CompilerConfig {
        opt_level,
        target: Target::X86_64,
        emit_proofs,
        x86_certificate_free_allocation,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .map(|result| result.object_code)
    .map_err(|e| format!("compiler: {:?}", e))
}

/// The x86-64 allocation policy this binary's driver installs before it
/// compiles. As the `ty_bfs_minimal` target it installs none, which is what
/// the TY AOT path does: it requests the certificate-free allocation through
/// `CompilerConfig::x86_certificate_free_allocation` instead, and
/// `Compiler::compile` applies the four allocation-quality changes itself.
/// The `ty_bfs_ra_quality` target compiles this same file as a driver that
/// installs them enabled, as the rustc bridge does for a compile with
/// `no-proof-certs`.
#[cfg(target_arch = "x86_64")]
fn install_driver_ra_policy() {
    if env!("CARGO_CRATE_NAME") != "ty_bfs_ra_quality" {
        return;
    }
    assert!(trust_cg_codegen::set_x86_ra_abi_copy_hints_disabled(false));
    assert!(trust_cg_codegen::set_x86_ra_caller_saved_first_disabled(
        false
    ));
    assert!(trust_cg_codegen::set_x86_ra_cold_call_weight_disabled(
        false
    ));
    assert!(trust_cg_codegen::set_x86_ra_call_split_disabled(false));
}

fn assert_valid_macho(bytes: &[u8], ctx: &str) {
    assert!(
        bytes.len() >= 4,
        "{}: too small ({} bytes)",
        ctx,
        bytes.len()
    );
    assert_eq!(
        &bytes[0..4],
        &host_object_magic_u32().to_le_bytes(),
        "{}: invalid host object magic",
        ctx
    );
}

/// ValueId counter for building trust_ir functions without collisions.
struct VidCounter(u32);

impl VidCounter {
    fn new(start: u32) -> Self {
        Self(start)
    }

    fn next(&mut self) -> ValueId {
        let v = ValueId::new(self.0);
        self.0 += 1;
        v
    }
}

fn const_i64(vid: &mut VidCounter, val: i64) -> (ValueId, InstrNode) {
    let r = vid.next();
    let node = InstrNode::new(Inst::Const {
        ty: Ty::I64,
        value: Constant::Int(val as i128),
    })
    .with_result(r);
    (r, node)
}

fn gep_i64(vid: &mut VidCounter, base: ValueId, index: ValueId) -> (ValueId, InstrNode) {
    let r = vid.next();
    let node = InstrNode::new(Inst::GEP {
        pointee_ty: Ty::I64,
        base,
        indices: vec![index],
        inbounds: false,
    })
    .with_result(r);
    (r, node)
}

fn load_i64(vid: &mut VidCounter, ptr: ValueId) -> (ValueId, InstrNode) {
    let r = vid.next();
    let node = InstrNode::new(Inst::Load {
        ty: Ty::I64,
        ptr,
        volatile: false,
        align: None,
    })
    .with_result(r);
    (r, node)
}

fn store_i64(ptr: ValueId, value: ValueId) -> InstrNode {
    InstrNode::new(Inst::Store {
        ty: Ty::I64,
        ptr,
        value,
        volatile: false,
        align: None,
    })
}

fn binop_i64(vid: &mut VidCounter, op: BinOp, lhs: ValueId, rhs: ValueId) -> (ValueId, InstrNode) {
    let r = vid.next();
    let node = InstrNode::new(Inst::BinOp {
        op,
        ty: Ty::I64,
        lhs,
        rhs,
    })
    .with_result(r);
    (r, node)
}

fn add_i64(vid: &mut VidCounter, lhs: ValueId, rhs: ValueId) -> (ValueId, InstrNode) {
    binop_i64(vid, BinOp::Add, lhs, rhs)
}

fn xor_i64(vid: &mut VidCounter, lhs: ValueId, rhs: ValueId) -> (ValueId, InstrNode) {
    binop_i64(vid, BinOp::Xor, lhs, rhs)
}

fn mul_i64(vid: &mut VidCounter, lhs: ValueId, rhs: ValueId) -> (ValueId, InstrNode) {
    binop_i64(vid, BinOp::Mul, lhs, rhs)
}

// ---------------------------------------------------------------------------
// Build the ty_bfs_kernel trust_ir function
// ---------------------------------------------------------------------------

fn build_ty_bfs_kernel() -> (TrustIrFunction, TrustIrModule) {
    let mut module = TrustIrModule::new("ty_bfs");
    let ft_id = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    let entry = b(0);
    let mut func = TrustIrFunction::new(FuncId::new(0), "ty_bfs_kernel", ft_id, entry);

    // v(0) = state: Ptr
    // v(1) = succ: Ptr
    // v(2) = idx_ptr: Ptr
    // v(3) = len: I64
    let state = v(0);
    let succ = v(1);
    let idx_ptr = v(2);
    let _len = v(3);
    let mut vid = VidCounter::new(4);

    let mut body = Vec::new();

    let (c3, n) = const_i64(&mut vid, 3);
    body.push(n);
    let (c5, n) = const_i64(&mut vid, 5);
    body.push(n);
    let (c0, n) = const_i64(&mut vid, 0);
    body.push(n);
    let (c2, n) = const_i64(&mut vid, 2);
    body.push(n);

    // a = state[3]
    let (state_3_ptr, n) = gep_i64(&mut vid, state, c3);
    body.push(n);
    let (a, n) = load_i64(&mut vid, state_3_ptr);
    body.push(n);

    // b = state[5]
    let (state_5_ptr, n) = gep_i64(&mut vid, state, c5);
    body.push(n);
    let (b_val, n) = load_i64(&mut vid, state_5_ptr);
    body.push(n);

    // succ[3] = a + b
    let (sum_ab, n) = add_i64(&mut vid, a, b_val);
    body.push(n);
    let (succ_3_ptr, n) = gep_i64(&mut vid, succ, c3);
    body.push(n);
    body.push(store_i64(succ_3_ptr, sum_ab));

    // succ[5] = a ^ b
    let (xor_ab, n) = xor_i64(&mut vid, a, b_val);
    body.push(n);
    let (succ_5_ptr, n) = gep_i64(&mut vid, succ, c5);
    body.push(n);
    body.push(store_i64(succ_5_ptr, xor_ab));

    // x = idx_ptr[0]
    let (idx_ptr_0, n) = gep_i64(&mut vid, idx_ptr, c0);
    body.push(n);
    let (x, n) = load_i64(&mut vid, idx_ptr_0);
    body.push(n);

    // y = state[x]
    let (state_x_ptr, n) = gep_i64(&mut vid, state, x);
    body.push(n);
    let (y, n) = load_i64(&mut vid, state_x_ptr);
    body.push(n);

    // succ[x] = y * 2
    let (succ_x_ptr, n) = gep_i64(&mut vid, succ, x);
    body.push(n);
    let (y_times_2, n) = mul_i64(&mut vid, y, c2);
    body.push(n);
    body.push(store_i64(succ_x_ptr, y_times_2));

    // return a + b + y
    let (checksum, n) = add_i64(&mut vid, sum_ab, y);
    body.push(n);
    body.push(InstrNode::new(Inst::Return {
        values: vec![checksum],
    }));

    func.blocks = vec![TrustIrBlock {
        id: entry,
        params: vec![
            (state, Ty::Ptr),
            (succ, Ty::Ptr),
            (idx_ptr, Ty::Ptr),
            (v(3), Ty::I64),
        ],
        body,
    }];

    module
        .try_add_function(func.clone())
        .expect("Module::try_add_function: test fixture");
    (func, module)
}

const C_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>

extern int64_t ty_bfs_kernel(int64_t* state, int64_t* succ, int64_t* idx, int64_t len);

int main(void) {
    int64_t state[8] = {10, 20, 30, 40, 50, 60, 70, 80};
    int64_t succ[8] = {0};
    int64_t idx = 7;

    int64_t r = ty_bfs_kernel(state, succ, &idx, 8);

    if (succ[3] != 100) {
        printf("succ[3]=%lld expected=100\n", (long long)succ[3]);
        return 1;
    }

    if (succ[5] != (40 ^ 60)) {
        printf("succ[5]=%lld expected=%lld\n",
               (long long)succ[5],
               (long long)(40 ^ 60));
        return 2;
    }

    if (succ[7] != 160) {
        printf("succ[7]=%lld expected=160\n", (long long)succ[7]);
        return 3;
    }

    if (r != 180) {
        printf("r=%lld expected=180\n", (long long)r);
        return 4;
    }

    printf("OK\n");
    return 0;
}
"#;

fn run_ty_bfs_e2e(opt_level: OptLevel, test_name: &str) {
    if !has_cc() {
        // `SKIP:` at line start is the spelling scripts/matrix_results.py
        // recognizes; "skipping ..." is invisible to it, which would let this
        // target report green with ZERO executing legs — the floor's own
        // docstring counts a runtime SKIP as a failure, and these four legs are
        // the only ones that prove x86-64 TY code actually runs.
        eprintln!("SKIP: {test_name}: cc not available, so the executed leg did NOT run");
        return;
    }

    let dir = make_test_dir(test_name);
    let (func, module) = build_ty_bfs_kernel();
    let obj_bytes = compile_trust_ir(&func, &module, opt_level)
        .expect("ty_bfs_kernel compilation should succeed");
    assert_valid_macho(&obj_bytes, test_name);

    let obj_path = write_object_file(&dir, "ty_bfs_kernel.o", &obj_bytes);
    keep_object(test_name, &obj_bytes);
    let driver_path = write_c_driver(&dir, "driver.c", C_DRIVER);
    let binary = link_with_cc(&dir, &driver_path, &obj_path, "ty_bfs_test");

    let (exit_code, stdout) = run_binary(&binary);
    assert_eq!(
        exit_code, 0,
        "binary should exit cleanly; stdout: {}",
        stdout
    );
    assert_eq!(stdout.trim(), "OK", "unexpected driver output: {}", stdout);

    cleanup(&dir);
}

// ===========================================================================
// Tests
// ===========================================================================

#[test]
fn test_ty_bfs_compiles_o0() {
    let (func, module) = build_ty_bfs_kernel();
    let obj_bytes =
        compile_trust_ir(&func, &module, OptLevel::O0).expect("ty_bfs_kernel should compile at O0");
    assert_valid_macho(&obj_bytes, "ty_bfs O0");
}

#[test]
fn test_ty_bfs_compiles_o1() {
    let (func, module) = build_ty_bfs_kernel();
    let obj_bytes =
        compile_trust_ir(&func, &module, OptLevel::O1).expect("ty_bfs_kernel should compile at O1");
    assert_valid_macho(&obj_bytes, "ty_bfs O1");
}

#[test]
fn test_ty_bfs_compiles_o2() {
    let (func, module) = build_ty_bfs_kernel();
    let obj_bytes =
        compile_trust_ir(&func, &module, OptLevel::O2).expect("ty_bfs_kernel should compile at O2");
    assert_valid_macho(&obj_bytes, "ty_bfs O2");
}

#[test]
fn test_ty_bfs_compiles_o3() {
    let (func, module) = build_ty_bfs_kernel();
    let obj_bytes =
        compile_trust_ir(&func, &module, OptLevel::O3).expect("ty_bfs_kernel should compile at O3");
    assert_valid_macho(&obj_bytes, "ty_bfs O3");
}

/// The `.text` bytes of a 64-bit little-endian ELF relocatable object.
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
fn elf_text(obj: &[u8]) -> Vec<u8> {
    let u16_at = |o: usize| u16::from_le_bytes([obj[o], obj[o + 1]]) as usize;
    let u32_at = |o: usize| u32::from_le_bytes(obj[o..o + 4].try_into().unwrap()) as usize;
    let u64_at = |o: usize| u64::from_le_bytes(obj[o..o + 8].try_into().unwrap()) as usize;
    let (shoff, shentsize, shnum, shstrndx) =
        (u64_at(0x28), u16_at(0x3a), u16_at(0x3c), u16_at(0x3e));
    let sh = |i: usize| shoff + i * shentsize;
    let strtab = u64_at(sh(shstrndx) + 0x18);
    for i in 0..shnum {
        let name_at = strtab + u32_at(sh(i));
        let end = obj[name_at..].iter().position(|&c| c == 0).unwrap();
        if &obj[name_at..name_at + end] == b".text" {
            let (off, size) = (u64_at(sh(i) + 0x18), u64_at(sh(i) + 0x20));
            return obj[off..off + size].to_vec();
        }
    }
    panic!("no .text section");
}

/// A TY compile that keeps no proof certificates and requests the
/// certificate-free allocation gets the x86-64 allocation-quality changes
/// from `Compiler::compile` itself, with no policy installed by its driver
/// (`X86AllocationQuality::CertificateFree`): the leaf kernel saves no
/// callee-saved register and keeps its arguments in their registers. The
/// historical allocation is 75 bytes and saves RBX after the frame setup
/// (`test_ty_bfs_historical_allocation_without_the_request`).
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
#[test]
fn test_ty_bfs_certificate_free_compile_gets_the_quality_allocation() {
    let (func, module) = build_ty_bfs_kernel();
    let obj = compile_trust_ir(&func, &module, OptLevel::O2).expect("O2 compile");
    let text = elf_text(&obj);
    assert_eq!(
        &text[..4],
        &[0x55, 0x48, 0x89, 0xe5],
        "push %rbp; mov %rsp,%rbp"
    );
    let push_callee_saved =
        text[4] == 0x53 || (text[4] == 0x41 && (0x54..=0x57).contains(&text[5]));
    assert!(
        !push_callee_saved,
        "no callee-saved register is saved: {text:02x?}"
    );
    assert!(
        text.len() < 0x4b,
        "shorter than the historical 75 bytes: {}",
        text.len()
    );
}

/// Whether `.text` is the historical allocation of the O2 kernel: RBX saved
/// right after the frame setup, 75 bytes.
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
fn is_historical_allocation(text: &[u8]) -> bool {
    text.len() == 0x4b && text[..5] == [0x55, 0x48, 0x89, 0xe5, 0x53]
}

/// Without the request, and with it when the compile keeps proof
/// certificates, the TY kernel keeps the historical allocation: a default
/// configuration emits the same bytes with and without certificates, and a
/// certificate-keeping compile withholds the changes whatever was requested
/// (`X86AllocationQuality::Installed` / `Withheld`). Only meaningful where no
/// policy is installed, i.e. in the `ty_bfs_minimal` target.
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
#[test]
fn test_ty_bfs_historical_allocation_without_the_request() {
    if env!("CARGO_CRATE_NAME") != "ty_bfs_minimal" {
        return;
    }
    let (_func, module) = build_ty_bfs_kernel();
    let plain = compile_x86(&module, OptLevel::O2, false, false).expect("O2 compile");
    assert!(
        is_historical_allocation(&elf_text(&plain)),
        "{:02x?}",
        elf_text(&plain)
    );
    let requested = compile_x86(&module, OptLevel::O2, false, true).expect("O2 compile");
    assert!(!is_historical_allocation(&elf_text(&requested)));
    match compile_x86(&module, OptLevel::O2, true, true) {
        Ok(with_certificates) => assert_eq!(
            elf_text(&with_certificates),
            elf_text(&plain),
            "a certificate-keeping compile keeps the historical allocation"
        ),
        Err(error) => panic!("certificate-keeping O2 compile failed: {error}"),
    }
}

#[test]
fn test_ty_bfs_o0_vs_o2_differ() {
    let (func, module) = build_ty_bfs_kernel();
    let obj_o0 =
        compile_trust_ir(&func, &module, OptLevel::O0).expect("ty_bfs_kernel should compile at O0");
    let obj_o2 =
        compile_trust_ir(&func, &module, OptLevel::O2).expect("ty_bfs_kernel should compile at O2");
    assert_ne!(
        obj_o0, obj_o2,
        "O0 and O2 should produce different object files"
    );
}

#[test]
fn test_ty_bfs_e2e_correctness() {
    run_ty_bfs_e2e(OptLevel::O0, "ty_bfs_e2e_o0");
}

#[test]
fn test_ty_bfs_e2e_correctness_o1() {
    run_ty_bfs_e2e(OptLevel::O1, "ty_bfs_e2e_o1");
}

#[test]
fn test_ty_bfs_e2e_correctness_o2() {
    run_ty_bfs_e2e(OptLevel::O2, "ty_bfs_e2e_o2");
}

#[test]
fn test_ty_bfs_e2e_correctness_o3() {
    run_ty_bfs_e2e(OptLevel::O3, "ty_bfs_e2e_o3");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
