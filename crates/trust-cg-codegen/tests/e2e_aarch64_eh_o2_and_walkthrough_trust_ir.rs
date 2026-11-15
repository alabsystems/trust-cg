// E2E: AArch64 macOS exception handling at -O2, and unwind-THROUGH plain
// trust-cg frames — end to end through the REAL compiler pipeline, linked
// with c++, and run with a process polling deadline.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ----------------------------------------------------------------------------
// WHAT THIS PINS (vs. `e2e_aarch64_eh_invoke_trust_ir`, which compiles at O0)
// ----------------------------------------------------------------------------
// 1. THE O2 INVOKE REGRESSION: `cfg-simplify` (an O2-only pass) used to
//    rebuild CFG edges from explicit `Block` operands alone. An `Invoke`'s
//    landing pad is entered by the UNWINDER (via the LSDA), not by a branch,
//    so the pad looked unreachable, was dropped from `block_order`, and the
//    fail-closed pipeline validator rejected the function:
//      "laid-out block BlockId(0) has successor target BlockId(1) absent
//       from block_order".
//    The in-repo EH e2e tests all compiled at O0, leaving the CLI DEFAULT
//    (-O2) unpinned. These tests compile the same trust-ir Invoke/LandingPad
//    module at O2 and RUN both invoke successors (normal return AND catch).
//
// 2. UNWIND-THROUGH (the cross-module FUZZ-7 [TCG-EH-WALK] face): a frame
//    with no unwind entry stops phase-1 unwinding dead — an exception raised
//    BELOW a plain (non-EH) trust-cg frame could never reach an outer
//    handler; libc++abi terminates the process. Unwind tables used to be
//    emitted only when some function in the module carried an LSDA, so every
//    all-plain module was an unwind barrier. Now every function gets a
//    walk-through `__LD,__compact_unwind` entry (DWARF FDE fallback when the
//    compact encoding cannot describe the frame) whenever the module's frame
//    layouts are threaded — with NO personality import, so plain-C links
//    stay EH-runtime-free. The test throws a C++ exception from a callee of
//    a trust-cg-compiled function and catches it in the C++ caller of that
//    function: main [c++] -> mid [trust-cg] -> thrower [c++, throws].
//
// Execution uses a polling deadline and nonblocking termination requests.
// Kernel-blocked children can survive a timeout; host cleanup is not guaranteed.

mod common;

use std::fs;
use std::process::Command;
use std::time::Duration;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Linkage, Module as TrustIrModule, Ty, ValueId,
};

/// These fixtures parse Mach-O structure (unwind/LSDA sections), so pin the
/// aarch64-apple-darwin spec explicitly: `Compiler::new` derives the object
/// format from the HOST, which on Linux emits ELF and breaks every Mach-O
/// header parse below. Mach-O byte emission itself is host-independent.
fn macho_compiler(config: CompilerConfig) -> Compiler {
    let spec = trust_cg_codegen::target::TargetSpec::parse("aarch64-apple-darwin")
        .expect("aarch64-apple-darwin parses");
    Compiler::new_for_target_spec(config, spec).with_codegen_license(permit_unlicensed())
}

#[path = "common/native_host.rs"]
mod native_host;

#[path = "common/pinned_target.rs"]
mod pinned_target;

/// AArch64 Linux GNU (ELF: `.eh_frame` + `.gcc_except_table`, libstdc++) or
/// macOS (Mach-O: compact unwind + `__gcc_except_tab`, libc++abi) can link
/// and run the EH object with the host `c++`.
fn host_can_link_and_run_aarch64_eh() -> bool {
    native_host::NATIVE
}

/// Compile for `triple`, asserting the container and the per-format LSDA
/// section an EH-carrying object must include.
fn compile_eh_obj_for(module: &TrustIrModule, opt_level: OptLevel, triple: &str) -> Vec<u8> {
    let spec = trust_cg_codegen::target::TargetSpec::parse(triple).expect("triple parses");
    let result = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        spec,
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&pinned_target::pinned(module, triple))
    .expect("EH module compilation should succeed");
    let obj = result.object_code;
    let contains = |needle: &[u8]| obj.windows(needle.len()).any(|w| w == needle);
    if triple.contains("linux") {
        native_host::assert_elf_aarch64_object(&obj);
        assert!(contains(b".eh_frame"), "ELF EH object must carry .eh_frame");
    } else {
        native_host::assert_macho_arm64_object(&obj);
    }
    obj
}

/// Build the trust-ir module of `e2e_aarch64_eh_invoke_trust_ir`: extern
/// C++/Itanium-runtime declarations plus `tc_try` (invoke + catch-all pad).
fn build_tc_try_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("eh_invoke_o2");

    // FuncId 0: extern void cxx_throw()  — may throw a C++ exception.
    let throw_ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut cxx_throw =
        TrustIrFunction::new(FuncId::new(0), "cxx_throw", throw_ft, BlockId::new(0));
    cxx_throw.linkage = Linkage::External;
    module
        .try_add_function(cxx_throw)
        .expect("Module::try_add_function: test fixture");

    // FuncId 1: extern void* __cxa_begin_catch(void* exn)
    let begin_ft = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut begin = TrustIrFunction::new(
        FuncId::new(1),
        "__cxa_begin_catch",
        begin_ft,
        BlockId::new(0),
    );
    begin.linkage = Linkage::External;
    module
        .try_add_function(begin)
        .expect("Module::try_add_function: test fixture");

    // FuncId 2: extern void __cxa_end_catch()
    let end_ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut end = TrustIrFunction::new(FuncId::new(2), "__cxa_end_catch", end_ft, BlockId::new(0));
    end.linkage = Linkage::External;
    module
        .try_add_function(end)
        .expect("Module::try_add_function: test fixture");

    // FuncId 3: int tc_try()
    let try_ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut tc_try = TrustIrFunction::new(FuncId::new(3), "tc_try", try_ft, BlockId::new(0));
    tc_try.blocks = vec![
        // bb0: invoke cxx_throw() to bb1 unwind bb2
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![InstrNode::new(Inst::Invoke {
                callee: FuncId::new(0),
                args: vec![],
                normal_dest: BlockId::new(1),
                normal_args: vec![],
                unwind_dest: BlockId::new(2),
            })],
        },
        // bb1 (normal, no exception): return 0
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(10)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(10)],
                }),
            ],
        },
        // bb2 (landing pad, catch-all): claim the exception, return 42
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::LandingPad {
                    is_cleanup: false,
                    catch_type_indices: vec![0], // 0 == catch-all (catch(...))
                })
                .with_results(vec![ValueId::new(20), ValueId::new(21)]),
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![ValueId::new(20)],
                })
                .with_result(ValueId::new(22)),
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(2),
                    args: vec![],
                }),
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(42),
                })
                .with_result(ValueId::new(23)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(23)],
                }),
            ],
        },
    ];
    module
        .try_add_function(tc_try)
        .expect("Module::try_add_function: test fixture");

    pinned_target::pin(&mut module, "aarch64-apple-darwin");
    module
}

/// Build a module with one PLAIN function (no EH structure at all):
///   int mid() { thrower(); return 7; }
fn build_mid_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("unwind_through");

    let thrower_ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut thrower = TrustIrFunction::new(FuncId::new(0), "thrower", thrower_ft, BlockId::new(0));
    thrower.linkage = Linkage::External;
    module
        .try_add_function(thrower)
        .expect("Module::try_add_function: test fixture");

    let mid_ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut mid = TrustIrFunction::new(FuncId::new(1), "mid", mid_ft, BlockId::new(0));
    mid.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![],
            }),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(7),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module
        .try_add_function(mid)
        .expect("Module::try_add_function: test fixture");

    pinned_target::pin(&mut module, "aarch64-apple-darwin");
    module
}

fn compile_to_obj_at(module: &TrustIrModule, opt_level: OptLevel) -> Vec<u8> {
    let compiler = macho_compiler(CompilerConfig {
        opt_level,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(module)
        .expect("compilation should succeed");
    assert!(
        !result.object_code.is_empty(),
        "must produce non-empty object code"
    );
    let obj = &result.object_code;
    let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
    assert_eq!(magic, 0xFEED_FACF, "must be valid Mach-O");
    result.object_code.clone()
}

fn contains_section(obj: &[u8], name: &[u8]) -> bool {
    obj.windows(name.len()).any(|w| w == name)
}

#[test]
fn eh_invoke_trust_ir_o2_compiles_with_lsda() {
    // THE regression: this exact module failed at O2 with "laid-out block
    // BlockId(0) has successor target BlockId(1) absent from block_order"
    // (cfg-simplify dropped the landing pad as unreachable). Object
    // inspection only; runs on every host.
    let module = build_tc_try_module();
    let obj = compile_to_obj_at(&module, OptLevel::O2);
    assert!(
        contains_section(&obj, b"__gcc_except_tab"),
        "O2 object compiled from trust-ir Invoke/LandingPad must carry the LSDA \
         (__gcc_except_tab) section"
    );
}

#[test]
fn eh_plain_function_gets_walkthrough_unwind_entry_without_personality() {
    // A module with NO EH structure must still get per-function unwind
    // entries (walk-through), but must NOT import a personality routine
    // (that would force every plain-C link to pull in an EH runtime).
    let module = build_mid_module();
    let obj = compile_to_obj_at(&module, OptLevel::O2);
    assert!(
        contains_section(&obj, b"__compact_unwind"),
        "plain module must carry walk-through __compact_unwind entries"
    );
    assert!(
        !contains_section(&obj, b"__gxx_personality_v0"),
        "plain module must not import a personality routine"
    );
    assert!(
        !contains_section(&obj, b"rust_eh_personality"),
        "plain module must not import a personality routine"
    );
    assert!(
        !contains_section(&obj, b"__gcc_except_tab"),
        "plain module has no LSDA"
    );
}

#[test]
fn eh_invoke_trust_ir_o2_link_and_run_both_paths() {
    if !host_can_link_and_run_aarch64_eh() {
        eprintln!("SKIP: EH O2 e2e requires an AArch64 Linux GNU or macOS host");
        return;
    }

    let module = build_tc_try_module();
    let obj = compile_eh_obj_for(&module, OptLevel::O2, native_host::TRIPLE);

    let dir = std::env::temp_dir().join("trust_cg_eh_o2_trust_ir_e2e");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    let obj_path = dir.join("tc_try_o2.o");
    fs::write(&obj_path, &obj).expect("write .o");

    // Driver exercising BOTH invoke successors: first call returns normally
    // (normal_dest), second call throws (unwind_dest -> catch-all pad).
    let driver_path = dir.join("driver.cpp");
    fs::write(
        &driver_path,
        r#"
#include <cstdio>
extern "C" int tc_try();
static int armed = 0;
extern "C" void cxx_throw() { if (armed) throw 7; }
int main() {
    int normal = tc_try();
    armed = 1;
    int caught = tc_try();
    printf("normal=%d caught=%d\n", normal, caught);
    return (normal == 0 && caught == 42) ? 0 : 1;
}
"#,
    )
    .expect("write driver");

    let bin_path = dir.join("eh_o2_bin");
    let link = Command::new("c++")
        .args([
            driver_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            bin_path.to_str().unwrap(),
        ])
        .output()
        .expect("c++ available");
    assert!(
        link.status.success(),
        "link failed:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );

    let (exit_code, stdout, stderr, timed_out) = run_with_timeout(
        &bin_path,
        common::rosetta::exec_timeout(Duration::from_secs(10)),
    );
    assert!(
        !timed_out,
        "O2 tc_try HUNG — unwinder never resolved the landing pad. \
         stdout: {stdout}\nstderr: {stderr}"
    );
    assert_eq!(
        exit_code,
        Some(0),
        "expected normal=0 caught=42. exit={exit_code:?}\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("normal=0 caught=42"),
        "expected both invoke successors to execute. stdout: {stdout}\nstderr: {stderr}"
    );

    eprintln!("trust-ir Invoke O2 EH e2e PASSED: {}", stdout.trim());
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn eh_unwind_through_plain_trust_cg_frame() {
    if !host_can_link_and_run_aarch64_eh() {
        eprintln!("SKIP: unwind-through e2e requires an AArch64 Linux GNU or macOS host");
        return;
    }

    let module = build_mid_module();
    let obj = compile_eh_obj_for(&module, OptLevel::O2, native_host::TRIPLE);

    let dir = std::env::temp_dir().join("trust_cg_eh_walkthrough_e2e");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    let obj_path = dir.join("mid.o");
    fs::write(&obj_path, &obj).expect("write .o");

    // main [c++ catch] -> mid [trust-cg, plain] -> thrower [c++ throw].
    // Without a walk-through unwind entry for `mid`, phase-1 unwinding stops
    // at its frame and libc++abi terminates (exit 134) — the FUZZ-7
    // [TCG-EH-WALK] class.
    let driver_path = dir.join("thru.cpp");
    fs::write(
        &driver_path,
        r#"
#include <cstdio>
extern "C" int mid();
extern "C" void thrower() { throw 7; }
int main() {
    try { mid(); printf("no throw\n"); return 2; }
    catch (int e) { printf("caught %d through trust-cg frame\n", e); return e == 7 ? 0 : 1; }
}
"#,
    )
    .expect("write driver");

    let bin_path = dir.join("thru_bin");
    let link = Command::new("c++")
        .args([
            driver_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            bin_path.to_str().unwrap(),
        ])
        .output()
        .expect("c++ available");
    assert!(
        link.status.success(),
        "link failed:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );

    let (exit_code, stdout, stderr, timed_out) = run_with_timeout(
        &bin_path,
        common::rosetta::exec_timeout(Duration::from_secs(10)),
    );
    assert!(
        !timed_out,
        "unwind-through binary HUNG. stdout: {stdout}\nstderr: {stderr}"
    );
    assert_eq!(
        exit_code,
        Some(0),
        "expected the exception to unwind THROUGH the trust-cg frame and be \
         caught (exit 0). exit={exit_code:?} (134 = libc++abi terminate: the \
         frame had no unwind entry)\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("caught 7 through trust-cg frame"),
        "expected the catch to observe the thrown value. stdout: {stdout}\nstderr: {stderr}"
    );

    eprintln!("unwind-through e2e PASSED: {}", stdout.trim());
    let _ = fs::remove_dir_all(&dir);
}

/// The Linux GNU native lane's objects, checked at object level on every host:
/// the O2 invoke module carries `.eh_frame`, the LSDA and the ELF personality;
/// the plain walk-through module carries `.eh_frame` without a personality.
#[test]
fn eh_o2_and_walkthrough_linux_objects_carry_eh_frame() {
    let obj = compile_eh_obj_for(
        &build_tc_try_module(),
        OptLevel::O2,
        "aarch64-unknown-linux-gnu",
    );
    let contains = |needle: &[u8]| obj.windows(needle.len()).any(|w| w == needle);
    assert!(contains(b".gcc_except_table"), "missing .gcc_except_table");
    assert!(contains(b"__gxx_personality_v0"), "missing ELF personality");
    let plain = compile_eh_obj_for(
        &build_mid_module(),
        OptLevel::O2,
        "aarch64-unknown-linux-gnu",
    );
    assert!(
        !plain
            .windows(b"__gxx_personality_v0".len())
            .any(|w| w == b"__gxx_personality_v0"),
        "plain module must not import a personality routine"
    );
}

#[cfg(unix)]
#[path = "common/direct_timeout_contract.rs"]
mod direct_timeout_contract;

#[cfg(unix)]
#[test]
fn eh_supervisor_preserves_direct_status_and_timeout_observations() {
    direct_timeout_contract::check(run_with_timeout);
}

/// Preserve direct-child exit codes with the shared polling/termination boundary.
/// A timeout requests termination; it does not guarantee child/host cleanup.
fn run_with_timeout(
    bin: &std::path::Path,
    timeout: Duration,
) -> (Option<i32>, String, String, bool) {
    let result = common::rosetta::command_output_with_timeout(&mut Command::new(bin), timeout)
        .expect("run supervised EH binary");
    (
        if result.timed_out {
            None
        } else {
            result.output.status.code()
        },
        String::from_utf8_lossy(&result.output.stdout).into_owned(),
        String::from_utf8_lossy(&result.output.stderr).into_owned(),
        result.timed_out,
    )
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
