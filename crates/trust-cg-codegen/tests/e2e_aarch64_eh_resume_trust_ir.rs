// E2E: AArch64 macOS exception-handling RESUME / continue-unwind path driven
// from trust-ir `Inst::Invoke` / cleanup-only `Inst::LandingPad` / `Inst::Resume`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ----------------------------------------------------------------------------
// WHAT THIS PINS (vs. the CATCH path `e2e_aarch64_eh_invoke_trust_ir`)
// ----------------------------------------------------------------------------
// The CATCH e2e proves an `Invoke` of a throwing C++ callee with a *catching*
// `LandingPad` (catch(...)) returns the sentinel. This test proves the
// RESUME / continue-unwind path: a **cleanup-only** `LandingPad`
// (is_cleanup=true, NO catch types) that runs cleanup and then `Inst::Resume`s
// the in-flight exception. The re-raised exception MUST propagate PAST the
// cleanup frame to an ENCLOSING handler (a C++ `try{ }catch(...)` in the
// driver). If the backend EH emission for a cleanup pad is wrong, the cleanup
// runs but the process aborts (`libc++abi: terminating due to uncaught
// exception`, exit 134) instead of the enclosing catch firing.
//
//   extern "C" int tc_cleanup() {
//     try   { cxx_throw(); return 0; }          // bb0 invoke + bb1 normal
//     cleanup { record_cleanup(); resume; }     // bb2 cleanup pad -> Resume
//   }
//   // driver:
//   try { tc_cleanup(); } catch (...) { /* enclosing handler MUST fire */ }
//
// SAFETY: the produced binary is ALWAYS run under a hard `timeout`.

use std::fs;
use std::process::Command;
use std::time::Duration;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Linkage, Module as TrustIrModule, Ty, ValueId,
};

fn host_is_aarch64_macos() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

/// Build the trust-ir module: extern declarations plus the `tc_cleanup`
/// function under test (cleanup-only landing pad + Resume).
fn build_tc_cleanup_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("eh_resume");

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

    // FuncId 1: extern void record_cleanup()  — observable cleanup side effect.
    let rec_ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    let mut rec = TrustIrFunction::new(FuncId::new(1), "record_cleanup", rec_ft, BlockId::new(0));
    rec.linkage = Linkage::External;
    module.add_function(rec);

    // FuncId 2: int tc_cleanup()
    let try_ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut tc = TrustIrFunction::new(FuncId::new(2), "tc_cleanup", try_ft, BlockId::new(0));
    tc.blocks = vec![
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
        // bb2 (CLEANUP-ONLY landing pad): run cleanup, then Resume.
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                // landingpad cleanup -> (exn_ptr, selector)
                InstrNode::new(Inst::LandingPad {
                    is_cleanup: true,
                    catch_type_indices: vec![], // pure cleanup (no catch)
                })
                .with_results(vec![ValueId::new(20), ValueId::new(21)]),
                // record_cleanup()  — the observable cleanup work.
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![],
                }),
                // resume the in-flight exception (re-raise to enclosing handler).
                InstrNode::new(Inst::Resume {
                    exn: ValueId::new(20),
                }),
            ],
        },
    ];
    module.add_function(tc);

    module
}

/// Compile the module at O0 and return the object code.
fn compile_to_obj(module: &TrustIrModule) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(module)
        .expect("tc_cleanup compilation should succeed");
    assert!(
        !result.object_code.is_empty(),
        "tc_cleanup must produce non-empty object code"
    );
    let obj = &result.object_code;
    let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
    assert_eq!(magic, 0xFEED_FACF, "must be valid Mach-O");
    result.object_code.clone()
}

#[test]
fn eh_resume_trust_ir_compiles_with_lsda() {
    let module = build_tc_cleanup_module();
    let obj = compile_to_obj(&module);
    assert!(
        obj.windows(b"__gcc_except_tab".len())
            .any(|w| w == b"__gcc_except_tab"),
        "object compiled from trust-ir cleanup LandingPad must carry the LSDA"
    );
}

/// Locate a Mach-O `section_64` header by its exact 16-byte section name and
/// return `(segname, size, nreloc, fileoff)`.
fn find_section_64(obj: &[u8], sectname: &[u8; 16]) -> Option<(Vec<u8>, u64, u32, u32)> {
    let pos = obj.windows(16).position(|w| w == sectname.as_slice())?;
    let seg = obj[pos + 16..pos + 32].to_vec();
    let size = u64::from_le_bytes(obj[pos + 40..pos + 48].try_into().unwrap());
    let fileoff = u32::from_le_bytes(obj[pos + 48..pos + 52].try_into().unwrap());
    let nreloc = u32::from_le_bytes(obj[pos + 60..pos + 64].try_into().unwrap());
    Some((seg, size, nreloc, fileoff))
}

/// [TCG-EH-A64-BATCH] (X1 follow-up to FUZZ-7), RESOLVED: a MULTI-function
/// module in which one function carries EH structure used to fall through to
/// the generic multi-function module emitter, which had NO unwind-table
/// emission — the object carried the landing-pad code but no
/// `__gcc_except_tab` / `__compact_unwind` (silently skipped cleanup Drops).
/// 1b37997 made that shape FAIL CLOSED; the generic emitter now builds
/// WHOLE-MODULE unwind tables for aarch64 Mach-O (the x86 EH-Lane-5 / FUZZ-7
/// [TCG-EH-WALK] analogue): one `__LD,__compact_unwind` entry per function —
/// EH functions AND plain walk-through frames — plus the real LSDA, so the
/// module COMPILES again and every frame is walkable.
#[test]
fn eh_multi_function_module_compiles_with_whole_module_unwind_tables() {
    let mut module = build_tc_cleanup_module();

    // A second BODIED function in the same module (a plain `int forty() {
    // return 40; }`) — with `tc_cleanup`'s Invoke/LandingPad this makes the
    // module a multi-function EH module: `forty` is exactly the plain
    // no-pad frame the unwinder must be able to walk THROUGH.
    let plain_ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut plain = TrustIrFunction::new(FuncId::new(3), "forty", plain_ft, BlockId::new(0));
    plain.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(40),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module.add_function(plain);

    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(&module)
        .expect("multi-function EH module must COMPILE with whole-module unwind tables");
    let obj = &result.object_code;
    assert_eq!(
        u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]),
        0xFEED_FACF,
        "must be valid Mach-O"
    );

    // One 32-byte __compact_unwind entry PER FUNCTION (tc_cleanup + forty),
    // each with a function relocation (exact atom association for ld64).
    let (seg, size, nreloc, fileoff) = find_section_64(obj, b"__compact_unwind")
        .expect("multi-function EH module must carry __LD,__compact_unwind");
    assert!(seg.starts_with(b"__LD"), "compact unwind lives in __LD");
    assert_eq!(
        size, 64,
        "expected exactly 2 compact unwind entries (32 bytes each: tc_cleanup + forty)"
    );
    assert!(
        nreloc >= 2,
        "each compact unwind entry needs at least its function relocation, got {nreloc}"
    );

    // The EH function's REAL LSDA must be present.
    let (lsda_seg, lsda_size, _, _) = find_section_64(obj, b"__gcc_except_tab")
        .expect("EH function's LSDA (__gcc_except_tab) must be emitted");
    assert!(lsda_seg.starts_with(b"__TEXT"), "LSDA lives in __TEXT");
    assert!(lsda_size > 0, "LSDA section must be non-empty");

    // The LSDA must be WIRED: either a compact-mode entry carries the
    // has-LSDA bit (0x40000000), or the EH function took the DWARF fallback
    // and an __eh_frame FDE references it. Never an orphaned LSDA.
    let entries = &obj[fileoff as usize..fileoff as usize + size as usize];
    let has_lsda_bit = entries.chunks_exact(32).any(|entry| {
        let encoding = u32::from_le_bytes(entry[12..16].try_into().unwrap());
        encoding & 0x4000_0000 != 0
    });
    let has_eh_frame = obj.windows(10).any(|w| w == b"__eh_frame".as_slice());
    assert!(
        has_lsda_bit || has_eh_frame,
        "the EH function's LSDA must be referenced from its compact unwind \
         entry (has-LSDA bit) or from a DWARF FDE (__eh_frame)"
    );

    // Every entry names a real code range (walkable frames, non-degenerate).
    for (i, entry) in entries.chunks_exact(32).enumerate() {
        let length = u32::from_le_bytes(entry[8..12].try_into().unwrap());
        assert!(length > 0, "compact unwind entry {i} has zero length");
    }
}

#[test]
fn eh_resume_trust_ir_link_and_run_propagates_to_enclosing_catch() {
    if !host_is_aarch64_macos() {
        eprintln!("SKIP: trust-ir Resume EH e2e requires an aarch64-apple-darwin host");
        return;
    }

    let module = build_tc_cleanup_module();
    let obj = compile_to_obj(&module);

    let dir = std::env::temp_dir().join("trust_cg_eh_resume_trust_ir_e2e");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    let obj_path = dir.join("tc_cleanup.o");
    fs::write(&obj_path, &obj).expect("write .o");

    // C++ driver: throwing callee, observable cleanup hook, and a main whose
    // try/catch(...) ENCLOSES the call to tc_cleanup. The cleanup pad must run
    // record_cleanup() and then re-raise so this enclosing catch fires.
    let driver_path = dir.join("driver.cpp");
    fs::write(
        &driver_path,
        r#"
#include <cstdio>
extern "C" int tc_cleanup();
extern "C" void cxx_throw() { throw 7; }
static int g_cleanup_ran = 0;
extern "C" void record_cleanup() { g_cleanup_ran = 1; }
int main() {
    int caught = 0;
    try {
        tc_cleanup();
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
        "tc_cleanup HUNG (timed out). stdout: {stdout}\nstderr: {stderr}"
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

    eprintln!("trust-ir Resume EH e2e PASSED: {}", stdout.trim());
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
