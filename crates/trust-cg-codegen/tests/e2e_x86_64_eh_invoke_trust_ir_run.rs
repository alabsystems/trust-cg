// E2E (x86_64-apple-darwin): the x86-64 macOS exception-handling CATCH path
// driven from trust-ir `Inst::Invoke` / `Inst::LandingPad` — end to end through
// the REAL `Compiler` pipeline (adapter -> ISel `Opcode::Invoke`/`LandingPad`
// -> `eh_info` -> `MachFunction.eh_metadata` -> post-layout `resolve_x86_eh_offsets`
// LSDA), linked with `c++ -arch x86_64`, and RUN UNDER ROSETTA (`arch -x86_64`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ----------------------------------------------------------------------------
// WHY THIS EXISTS (the x86 analog of `e2e_aarch64_eh_invoke_trust_ir`)
// ----------------------------------------------------------------------------
// `e2e_x86_64_eh_catch` proves the x86 BACKEND EH machinery by hand-authoring an
// `X86ISelFunction` and attaching EH metadata directly. THIS test proves the
// FULL trust-ir-driven path: a trust-ir `Module` whose function uses
// `Inst::Invoke` (a call that may unwind) + `Inst::LandingPad` (a catch-all
// handler) is compiled by the ordinary `Compiler` targeting x86_64-apple-darwin
// (so it flows through the whole adapter/ISel/eh-metadata/LSDA pipeline the CLI
// uses), then the x86_64 object is linked and RUN via Rosetta 2. A clean
// exit 0 / "returned 42" PROVES the trust-ir Invoke/LandingPad lowering + the
// x86-64 zPLR `__eh_frame` + `__gcc_except_tab` LSDA + personality relocation
// all resolve at runtime — the decisive proof the x86 EH tables the Compiler
// path emits are correct, not merely structurally present.
//
//   extern "C" int tc_try() {
//     try   { cxx_throw(); return 0; }     // bb0 invoke + bb1 normal
//     catch (...) { return 42; }            // bb2 landing pad (catch-all)
//   }
//
// The object is always cross-emitted for x86_64 by `Target::X86_64`; only the
// RUN needs a host, supplied here by Rosetta on an arm64 developer machine.
//
// SAFETY: the produced binary is ALWAYS run under a hard timeout so a broken
// catch (loop/abort/hang in the unwinder) becomes a fast, diagnosable failure.

use std::fs;
use std::process::Command;
use std::time::Duration;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{CompileError, Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::{OptLevel, PipelineError};
use trust_cg_codegen::target::TargetSpec;
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Linkage, Module as TrustIrModule, Ty, ValueId,
};

/// How to RUN the emitted x86_64-apple-darwin binary on this host, or `None`
/// if it cannot be run here (SKIP): native on an x86_64 host, or `arch -x86_64`
/// (Rosetta 2) on an arm64 macOS host.
fn x86_64_run_prefix() -> Option<Vec<String>> {
    if cfg!(all(target_os = "macos", target_arch = "x86_64")) {
        return Some(vec![]);
    }
    if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        let rosetta_ok = Command::new("arch")
            .args(["-x86_64", "true"])
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false);
        if rosetta_ok {
            return Some(vec!["arch".to_string(), "-x86_64".to_string()]);
        }
    }
    None
}

/// Build the trust-ir module: three extern C++/Itanium-runtime declarations plus
/// the `tc_try` function under test (identical to the aarch64 invoke fixture —
/// trust-ir is target-independent; the target is chosen at compile time).
fn build_tc_try_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("eh_invoke_x86");

    // FuncId 0: extern void cxx_throw()  — throws a C++ exception (no return).
    let throw_ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    let mut cxx_throw =
        TrustIrFunction::new(FuncId::new(0), "cxx_throw", throw_ft, BlockId::new(0));
    cxx_throw.linkage = Linkage::External;
    module.add_function(cxx_throw);

    // FuncId 1: extern void* __cxa_begin_catch(void* exn)
    let begin_ft = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::Ptr],
        is_vararg: false,
    });
    let mut begin = TrustIrFunction::new(
        FuncId::new(1),
        "__cxa_begin_catch",
        begin_ft,
        BlockId::new(0),
    );
    begin.linkage = Linkage::External;
    module.add_function(begin);

    // FuncId 2: extern void __cxa_end_catch()
    let end_ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    let mut end = TrustIrFunction::new(FuncId::new(2), "__cxa_end_catch", end_ft, BlockId::new(0));
    end.linkage = Linkage::External;
    module.add_function(end);

    // FuncId 3: int tc_try()
    let try_ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
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
    module.add_function(tc_try);

    module
}

fn compile_to_x86_64_obj(module: &TrustIrModule) -> Vec<u8> {
    // This test's assertions (and the Rosetta run) are about the
    // x86_64-apple-darwin object, so the spec is EXPLICIT: the default spec is
    // host-OS-aware and emits ELF on Linux, where x86-64 EH (LSDA /
    // personality / eh_frame) is not emitted yet and the compiler fails
    // CLOSED (pinned by `eh_invoke_trust_ir_elf_fails_closed_without_unwind_tables`
    // below). Mach-O cross-emission works on every host.
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            target: Target::X86_64,
            ..CompilerConfig::default()
        },
        TargetSpec::parse("x86_64-apple-darwin").expect("parse x86_64-apple-darwin target spec"),
    );
    let result = compiler
        .compile(module)
        .expect("tc_try x86-64 compilation should succeed");
    assert!(
        !result.object_code.is_empty(),
        "tc_try must produce non-empty object code"
    );
    let obj = &result.object_code;
    let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
    assert_eq!(magic, 0xFEED_FACF, "must be valid 64-bit Mach-O");
    result.object_code.clone()
}

#[test]
fn eh_invoke_trust_ir_x86_compiles_with_lsda() {
    // Compile-only path (runs on every host): exercises the trust-ir
    // Invoke/LandingPad lowering, eh_info -> eh_metadata forwarding, and the
    // post-layout x86 LSDA generation. Object inspection only; no link/run.
    let module = build_tc_try_module();
    let obj = compile_to_x86_64_obj(&module);
    assert!(
        obj.windows(b"__gcc_except_tab".len())
            .any(|w| w == b"__gcc_except_tab"),
        "object compiled from trust-ir Invoke/LandingPad (x86-64) must carry the \
         LSDA (__gcc_except_tab) section"
    );
    assert!(
        obj.windows(b"__eh_frame".len()).any(|w| w == b"__eh_frame"),
        "object must carry the __eh_frame section"
    );
}

#[test]
fn eh_invoke_trust_ir_elf_fails_closed_without_unwind_tables() {
    // Product-gap pin (2026-07-31 x86-Linux battery): x86-64 EH emission
    // (LSDA / personality / eh_frame) exists ONLY for Mach-O today. An ELF
    // target must NOT silently emit an object with no unwind tables — the
    // compiler fails CLOSED with a typed ISel diagnostic. When ELF
    // .eh_frame/.gcc_except_table emission lands, this test flips to the
    // positive LSDA assertions above.
    let module = build_tc_try_module();
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            target: Target::X86_64,
            ..CompilerConfig::default()
        },
        TargetSpec::parse("x86_64-unknown-linux-gnu")
            .expect("parse x86_64-unknown-linux-gnu target spec"),
    );
    let err = compiler
        .compile(&module)
        .expect_err("ELF x86-64 EH must fail closed until unwind-table emission lands");
    match err {
        CompileError::Pipeline(PipelineError::ISel(message)) => {
            assert!(
                message.contains("emitted only for Mach-O"),
                "diagnostic should name the Mach-O-only EH boundary, got: {message}"
            );
            assert!(
                message.contains("Fail-closed"),
                "diagnostic should state the fail-closed contract, got: {message}"
            );
        }
        other => panic!("expected the typed ELF EH fail-closed ISel rejection, got {other:?}"),
    }
}

#[test]
fn eh_invoke_trust_ir_x86_link_and_run_catches() {
    let Some(run_prefix) = x86_64_run_prefix() else {
        eprintln!(
            "SKIP: trust-ir Invoke EH catch e2e (x86-64) needs an x86_64-apple-darwin \
             host or an arm64 macOS host with Rosetta 2"
        );
        return;
    };
    if Command::new("c++").arg("--version").output().is_err() {
        eprintln!("SKIP: c++ (clang) not available");
        return;
    }

    let module = build_tc_try_module();
    let obj = compile_to_x86_64_obj(&module);

    let dir = std::env::temp_dir().join("trust_cg_x86_eh_invoke_trust_ir_e2e");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    let obj_path = dir.join("tc_try_x86.o");
    fs::write(&obj_path, &obj).expect("write .o");

    let driver_path = dir.join("driver.cpp");
    fs::write(
        &driver_path,
        r#"
#include <cstdio>
extern "C" int tc_try();
extern "C" void cxx_throw() { throw 7; }
int main() {
    int r = tc_try();
    printf("tc_try returned %d\n", r);
    return r == 42 ? 0 : 1;
}
"#,
    )
    .expect("write driver");

    let bin_path = dir.join("eh_invoke_x86_bin");
    // `-arch x86_64` forces the x86_64 slice on an arm64 host (harmless on a
    // native x86_64 host); `c++` pulls in libc++/libc++abi (___gxx_personality_v0,
    // __cxa_*, typeinfo).
    let link = Command::new("c++")
        .args(if cfg!(target_os = "macos") {
            &["-arch", "x86_64"][..]
        } else {
            &[][..]
        })
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

    let (exit_code, stdout, stderr, timed_out) =
        run_with_timeout(&bin_path, &run_prefix, Duration::from_secs(10));

    assert!(
        !timed_out,
        "tc_try HUNG (timed out) — the catch path did not return. A hang means the \
         unwinder never resolved the landing pad (LSDA call-site / offset bug).\n\
         stdout: {stdout}\nstderr: {stderr}"
    );
    assert_eq!(
        exit_code,
        Some(0),
        "expected a clean catch (exit 0, sentinel 42). A non-zero/abort here means \
         the personality reloc or LSDA is wrong.\nexit={exit_code:?}\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("tc_try returned 42"),
        "expected the catch sentinel in stdout.\nstdout: {stdout}\nstderr: {stderr}"
    );

    eprintln!(
        "trust-ir Invoke EH catch e2e (x86-64) PASSED: {}",
        stdout.trim()
    );
    let _ = fs::remove_dir_all(&dir);
}

/// Run `bin` (optionally under `prefix`, e.g. `["arch", "-x86_64"]` for Rosetta)
/// with a hard wall-clock timeout. On timeout the child is killed.
fn run_with_timeout(
    bin: &std::path::Path,
    prefix: &[String],
    timeout: Duration,
) -> (Option<i32>, String, String, bool) {
    use std::io::Read;

    let mut command = if let Some((launcher, rest)) = prefix.split_first() {
        let mut c = Command::new(launcher);
        c.args(rest);
        c.arg(bin);
        c
    } else {
        Command::new(bin)
    };
    let mut child = command
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("spawn EH binary");

    let start = std::time::Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let mut out = String::new();
                let mut err = String::new();
                if let Some(mut s) = child.stdout.take() {
                    let _ = s.read_to_string(&mut out);
                }
                if let Some(mut s) = child.stderr.take() {
                    let _ = s.read_to_string(&mut err);
                }
                return (status.code(), out, err, false);
            }
            Ok(None) => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    return (None, String::new(), String::new(), true);
                }
                std::thread::sleep(Duration::from_millis(25));
            }
            Err(_) => return (None, String::new(), String::new(), false),
        }
    }
}
