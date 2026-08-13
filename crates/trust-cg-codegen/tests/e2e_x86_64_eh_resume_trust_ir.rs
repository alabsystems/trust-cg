// E2E (x86_64-apple-darwin): the x86-64 macOS exception-handling RESUME /
// continue-unwind path — a cleanup-only landing pad that runs cleanup and then
// re-raises, whose re-raise MUST propagate PAST the cleanup frame to an
// enclosing handler. RUN NATIVELY. [EH flip Slice B]
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ----------------------------------------------------------------------------
// WHAT THIS PINS (the x86 analog of `e2e_aarch64_eh_resume_trust_ir`)
// ----------------------------------------------------------------------------
// The CATCH e2e (`e2e_x86_64_eh_catch`) proves an `Invoke`/CALL of a throwing
// callee with a *catching* landing pad (catch(...)) returns the sentinel. This
// test proves the RESUME / continue-unwind path on x86: a **cleanup-only**
// landing pad (is_cleanup=true, NO catch types — exactly the Rust Drop-glue
// shape) that runs cleanup and then re-raises (`_Unwind_Resume`). The re-raised
// exception MUST propagate PAST the cleanup frame to an ENCLOSING handler (a C++
// `try{ }catch(...)` in the driver). If the x86 backend EH emission for a
// cleanup pad were wrong (e.g. an LSDA call-site table with a GAP at the resume
// PC), the cleanup would run but `_Unwind_Resume` would re-consult the LSDA,
// find no covering call-site entry, and call `std::terminate()` (`libc++abi:
// terminating due to uncaught exception`, exit 134) instead of continuing the
// unwind to the enclosing catch. A clean exit 0 PROVES the full-coverage
// `[0, code_len)` call-site synthesis (`resolve_x86_eh_offsets` ->
// `x86_lsda_for_function`) makes `_Unwind_Resume` propagate — the direct proof
// the historical x86 abort is gone and the `TCG_ENABLE_UNWIND` flip is safe.
//
//   extern "C" int tc_cleanup() {
//     try   { cxx_throw(); return 0; }               // bb0 call + bb1 normal
//     cleanup { record_cleanup(exn); resume(exn); }  // bb1 cleanup pad -> Resume
//   }
//   // driver:
//   try { tc_cleanup(); } catch (...) { /* enclosing handler MUST fire */ }
//
// The runnable proof is built at the `X86ISelFunction` / `X86Pipeline::
// compile_module` level with the C++ personality (`__gxx_personality_v0`) and
// linked with `c++`, exactly like `e2e_x86_64_eh_catch`, so the enclosing
// `catch(...)` catches a plain C++ exception — no Rust runtime needed. (The
// production trust-ir -> x86 lowering emits the RUST personality
// `_rust_eh_personality` for a Rust cleanup frame; that runnable proof, which
// needs libstd / libpanic_unwind, is `unwind_cleanup_x86_64.rs` — the bridge
// split-model Slice C.) `eh_resume_trust_ir_x86_lowers_rust_personality_lsda`
// below still exercises the trust-ir `Inst::Invoke` / cleanup `Inst::LandingPad`
// / `Inst::Resume` lowering at the object level and locks the Slice A
// personality-name fix through the full `Compiler` path.
//
// The exception object is threaded THROUGH `record_cleanup` via the C ABI
// (arg0 in, return value out) so it survives the cleanup call without needing a
// hand-built spill — the SAME exn is handed to `_Unwind_Resume`.
//
// x86_64 is the HOST here, so the binary runs directly (mirrors the AArch64
// `e2e_aarch64_eh_resume_trust_ir`, which runs on an aarch64 host).
//
// SAFETY: the produced binary is ALWAYS run under a hard `timeout`.

use std::fs;
use std::process::Command;
use std::time::Duration;

use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_ir::x86_64_regs;
use trust_cg_lower::function::{EhCallSite, EhFunctionInfo, EhLandingPad, Signature};
use trust_cg_lower::instructions::Block;
use trust_cg_lower::x86_64_isel::{
    X86CallArgReg, X86CallResultReg, X86ISelFunction, X86ISelInst, X86ISelOperand,
};

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::x86_64::{X86OutputFormat, X86Pipeline, X86PipelineConfig};
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Linkage, Module as TrustIrModule, Ty, ValueId,
};

fn host_is_x86_64_macos() -> bool {
    cfg!(all(target_os = "macos", target_arch = "x86_64"))
}

fn obj_contains(obj: &[u8], needle: &[u8]) -> bool {
    obj.windows(needle.len()).any(|w| w == needle)
}

/// Build `tc_cleanup_x86`: a throwing call with a CLEANUP-ONLY landing pad that
/// runs `record_cleanup(exn)` and then `_Unwind_Resume(exn)` (re-raise). The
/// exn pointer (installed by the unwinder in RAX, Itanium eh data regno 0) is
/// threaded through `record_cleanup` (arg0 -> return) so it survives the call.
///
/// ```text
/// bb0:  CALL cxx_throw           ; may throw -> unwinder diverts to bb1
///       MOV RAX, 0               ; normal path: return 0
///       RET
/// bb1:  MOV RDI, RAX             ; exn ptr -> arg0
///       CALL record_cleanup      ; observable cleanup; returns exn in RAX
///       MOV RDI, RAX             ; exn ptr -> arg0 for the re-raise
///       CALL _Unwind_Resume      ; continue unwind PAST this cleanup frame
/// ```
fn build_tc_cleanup_x86() -> X86ISelFunction {
    let sig = Signature {
        params: vec![],
        returns: vec![],
    };
    let mut func = X86ISelFunction::new("tc_cleanup_x86".to_string(), sig);
    let entry = Block(0);
    let pad = Block(1);
    func.ensure_block(entry);
    func.ensure_block(pad);
    func.add_successor(entry, pad);

    // --- bb0: the throwing call + normal (no-exception) path ---
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::Call,
            vec![X86ISelOperand::Symbol("cxx_throw".to_string())],
        ),
    );
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovRI,
            vec![
                X86ISelOperand::PReg(x86_64_regs::RAX),
                X86ISelOperand::Imm(0),
            ],
        ),
    );
    func.push_inst(entry, X86ISelInst::new(X86Opcode::Ret, vec![]));

    // --- bb1: the CLEANUP-ONLY landing pad (Drop-glue shape) + Resume ---
    // exn ptr -> arg0 for record_cleanup.
    func.push_inst(
        pad,
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![
                X86ISelOperand::PReg(x86_64_regs::RDI),
                X86ISelOperand::PReg(x86_64_regs::RAX),
            ],
        ),
    );
    // record_cleanup(exn) -> exn : observable cleanup that preserves the exn via
    // the C ABI (arg0 RDI in, return RAX out).
    func.push_inst(
        pad,
        X86ISelInst::new(
            X86Opcode::Call,
            vec![X86ISelOperand::Symbol("record_cleanup".to_string())],
        )
        .with_call_arg_regs(vec![X86CallArgReg::new(x86_64_regs::RDI, 64)])
        .with_call_result_regs(vec![X86CallResultReg::new(x86_64_regs::RAX, 64)]),
    );
    // exn (now in RAX) -> arg0 for _Unwind_Resume.
    func.push_inst(
        pad,
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![
                X86ISelOperand::PReg(x86_64_regs::RDI),
                X86ISelOperand::PReg(x86_64_regs::RAX),
            ],
        ),
    );
    // Re-raise: continue-unwind past this cleanup frame to the enclosing catch.
    func.push_inst(
        pad,
        X86ISelInst::new(
            X86Opcode::Call,
            vec![X86ISelOperand::Symbol("_Unwind_Resume".to_string())],
        )
        .with_call_arg_regs(vec![X86CallArgReg::new(x86_64_regs::RDI, 64)])
        .with_call_result_regs(vec![]),
    );
    // `_Unwind_Resume` never returns. Keep that source-level terminator exact
    // in the machine CFG and fail closed if the external routine violates its
    // ABI contract.
    func.push_inst(pad, X86ISelInst::new(X86Opcode::Ud2, vec![]));

    // --- EH metadata: CLEANUP-ONLY landing pad + call-site over the throwing block ---
    func.eh_info = EhFunctionInfo {
        personality: Some("__gxx_personality_v0".to_string()),
        landing_pads: vec![EhLandingPad {
            block: pad,
            catch_type_indices: vec![], // pure CLEANUP (no catch types)
            is_cleanup: true,
        }],
        call_sites: vec![EhCallSite {
            call_block: entry,
            landing_pad_block: pad,
        }],
    };
    func
}

/// Build the trust-ir module driving the PRODUCTION trust-ir -> x86 lowering
/// (`Inst::Invoke` / cleanup `Inst::LandingPad` / `Inst::Resume`). Used to lock
/// that the real lowering emits an LSDA carrying the Slice A Rust personality
/// name `_rust_eh_personality` (single underscore), NOT `___rust_eh_personality`.
fn build_tc_cleanup_trust_ir_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("eh_resume_x86");

    let throw_ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    let mut cxx_throw =
        TrustIrFunction::new(FuncId::new(0), "cxx_throw", throw_ft, BlockId::new(0));
    cxx_throw.linkage = Linkage::External;
    module.add_function(cxx_throw);

    let rec_ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    let mut rec = TrustIrFunction::new(FuncId::new(1), "record_cleanup", rec_ft, BlockId::new(0));
    rec.linkage = Linkage::External;
    module.add_function(rec);

    // The rustc bridge declares the body-less external `rust_eh_personality`
    // marker for every unwinding Rust function it lowers; the adapter's
    // `default_eh_personality` detects it and selects the Rust personality
    // over the C++ `__gxx_personality_v0` default (see
    // trust-cg-lower/src/adapter.rs `RUST_EH_PERSONALITY`). This module models
    // a Rust cleanup frame, so it declares the marker exactly as the bridge
    // does.
    let personality_ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    let mut personality = TrustIrFunction::new(
        FuncId::new(2),
        "rust_eh_personality",
        personality_ft,
        BlockId::new(0),
    );
    personality.linkage = Linkage::External;
    module.add_function(personality);

    let try_ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut tc = TrustIrFunction::new(FuncId::new(3), "tc_cleanup", try_ft, BlockId::new(0));
    tc.blocks = vec![
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
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::LandingPad {
                    is_cleanup: true,
                    catch_type_indices: vec![],
                })
                .with_results(vec![ValueId::new(20), ValueId::new(21)]),
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![],
                }),
                InstrNode::new(Inst::Resume {
                    exn: ValueId::new(20),
                }),
            ],
        },
    ];
    module.add_function(tc);
    module
}

/// Compile the cleanup-only X86ISel function through the standard module path
/// (LSDA + zPLR FDE + personality) and return the Mach-O object.
fn compile_x86_isel_to_obj(func: X86ISelFunction) -> Vec<u8> {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        emit_frame: true,
        output_format: X86OutputFormat::MachO,
        ..X86PipelineConfig::default()
    });
    let obj = pipeline
        .compile_module(&[func])
        .expect("compile_module tc_cleanup_x86 with EH metadata");
    assert_eq!(
        u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]),
        0xFEED_FACF,
        "valid 64-bit Mach-O"
    );
    obj
}

#[test]
fn eh_resume_x86_compiles_with_lsda() {
    let obj = compile_x86_isel_to_obj(build_tc_cleanup_x86());
    assert!(
        obj_contains(&obj, b"__gcc_except_tab"),
        "cleanup-only landing pad must carry the LSDA (__gcc_except_tab)"
    );
    assert!(
        obj_contains(&obj, b"__eh_frame"),
        "cleanup-only landing pad must carry the __eh_frame section"
    );
}

/// Lock the Slice A personality-name fix through the PRODUCTION trust-ir -> x86
/// lowering: the emitted object references the std-provided single-underscore
/// `_rust_eh_personality`, never the undefined triple `___rust_eh_personality`.
#[test]
fn eh_resume_trust_ir_x86_lowers_rust_personality_lsda() {
    // The spec is EXPLICITLY x86_64-apple-darwin: every assertion below is a
    // Mach-O shape (`__gcc_except_tab` section, the `_`-mangled personality
    // symbol), and the default spec is host-OS-aware — on Linux it selects
    // ELF, where x86-64 EH emission does not exist yet and the compiler
    // fails closed (pinned by
    // `eh_invoke_trust_ir_elf_fails_closed_without_unwind_tables` in the
    // invoke suite). Mach-O cross-emission works on every host.
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            target: Target::X86_64,
            ..CompilerConfig::default()
        },
        TargetSpec::parse("x86_64-apple-darwin").expect("parse x86_64-apple-darwin target spec"),
    );
    let result = compiler
        .compile(&build_tc_cleanup_trust_ir_module())
        .expect("trust-ir cleanup lowering should compile for x86");
    let obj = &result.object_code;
    assert!(
        obj_contains(obj, b"__gcc_except_tab"),
        "trust-ir cleanup LandingPad must lower to an LSDA (__gcc_except_tab)"
    );
    assert!(
        obj_contains(obj, b"\x00_rust_eh_personality\x00"),
        "the trust-ir -> x86 lowering must reference the std-provided \
         _rust_eh_personality (single underscore)"
    );
    assert!(
        !obj_contains(obj, b"___rust_eh_personality"),
        "must NOT reference the undefined ___rust_eh_personality (the \
         double-prefix link failure Slice A removes)"
    );
}

#[test]
fn eh_resume_x86_link_and_run_propagates_to_enclosing_catch() {
    if !host_is_x86_64_macos() {
        eprintln!("SKIP: x86 Resume EH e2e requires an x86_64-apple-darwin host");
        return;
    }
    if Command::new("c++").arg("--version").output().is_err() {
        eprintln!("SKIP: c++ (clang) not available");
        return;
    }

    let obj = compile_x86_isel_to_obj(build_tc_cleanup_x86());

    let dir = std::env::temp_dir().join("trust_cg_x86_eh_resume_e2e");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    let obj_path = dir.join("tc_cleanup_x86.o");
    fs::write(&obj_path, &obj).expect("write .o");

    // C++ driver: throwing callee, observable cleanup hook (which returns the
    // exn it is handed so the pad can re-raise the SAME exception), and a main
    // whose try/catch(...) ENCLOSES the call. The cleanup pad must run
    // record_cleanup() and then re-raise so this enclosing catch fires.
    let driver_path = dir.join("driver.cpp");
    fs::write(
        &driver_path,
        r#"
#include <cstdio>
extern "C" int tc_cleanup_x86();
extern "C" void cxx_throw() { throw 7; }
static int g_cleanup_ran = 0;
extern "C" void* record_cleanup(void* exn) { g_cleanup_ran = 1; return exn; }
int main() {
    int caught = 0;
    try {
        tc_cleanup_x86();
    } catch (...) {
        caught = 1;
    }
    printf("cleanup_ran=%d caught=%d\n", g_cleanup_ran, caught);
    // Success: cleanup ran AND the re-raised exception reached the enclosing
    // catch (continue-unwind propagated past the cleanup frame).
    return (g_cleanup_ran == 1 && caught == 1) ? 0 : 1;
}
"#,
    )
    .expect("write driver");

    let bin_path = dir.join("eh_resume_bin");
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

    let (exit_code, stdout, stderr, timed_out) =
        run_with_timeout(&bin_path, Duration::from_secs(10));

    assert!(
        !timed_out,
        "tc_cleanup_x86 HUNG (timed out). stdout: {stdout}\nstderr: {stderr}"
    );
    assert_eq!(
        exit_code,
        Some(0),
        "expected the re-raised exception to reach the enclosing catch(...) \
         after cleanup (exit 0). A non-zero/134 exit means the cleanup ran but \
         the unwind did NOT propagate (uncaught -> terminate). \
         exit={exit_code:?}\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("cleanup_ran=1 caught=1"),
        "expected cleanup to run AND enclosing catch to fire. stdout: {stdout}\nstderr: {stderr}"
    );

    eprintln!("x86 Resume EH e2e PASSED: {}", stdout.trim());
    let _ = fs::remove_dir_all(&dir);
}

/// Run `bin` with a hard wall-clock timeout. Returns
/// `(exit_code, stdout, stderr, timed_out)`. On timeout the child is killed.
fn run_with_timeout(
    bin: &std::path::Path,
    timeout: Duration,
) -> (Option<i32>, String, String, bool) {
    use std::io::Read;

    let mut child = Command::new(bin)
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
                std::thread::sleep(Duration::from_millis(20));
            }
            Err(e) => panic!("waiting on EH binary failed: {e}"),
        }
    }
}
