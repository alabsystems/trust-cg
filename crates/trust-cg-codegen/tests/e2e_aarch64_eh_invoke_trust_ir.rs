// E2E: AArch64 macOS exception-handling CATCH path driven from trust-ir
// `Inst::Invoke` / `Inst::LandingPad` — end to end through the REAL compiler
// pipeline (adapter -> ISel -> eh_metadata -> post-layout LSDA + compact
// unwind), linked with c++, and RUN under a hard timeout.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ----------------------------------------------------------------------------
// WHAT THIS PINS (vs. the hand-authored MachIR `e2e_aarch64_eh_catch`)
// ----------------------------------------------------------------------------
// `e2e_aarch64_eh_catch` proves the BACKEND EH machinery (LSDA call-site table,
// compact unwind, landing-pad transfer) by hand-authoring a post-regalloc
// `MachFunction` and attaching the EH metadata + byte offsets MANUALLY.
//
// This test proves the FULL trust-ir-driven path: a trust-ir `Module` whose
// function uses the new `Inst::Invoke` (a call that may unwind) and
// `Inst::LandingPad` (a catch-all handler) is compiled by the ordinary
// `Compiler` (so it flows through the adapter's EH lowering, ISel's
// `Opcode::Invoke`/`LandingPad`, the `eh_info` -> `MachFunction.eh_metadata`
// forwarding, and the pipeline's POST-LAYOUT `resolve_eh_offsets` pass that
// fills the LSDA byte offsets). The throwing callee is a C++ `throw`, caught at
// the landing pad via `__cxa_begin_catch`/`__cxa_end_catch`, returning a
// sentinel.
//
//   extern "C" int tc_try() {
//     try   { cxx_throw(); return 0; }     // bb0 invoke + bb1 normal
//     catch (...) { return 42; }            // bb2 landing pad (catch-all)
//   }
//
// SAFETY: the produced binary is ALWAYS run under a hard `timeout` so a broken
// catch (which would loop/abort/hang in the unwinder) becomes a fast,
// diagnosable failure instead of a hang.

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

/// Build the trust-ir module: three extern C++/Itanium-runtime declarations
/// plus the `tc_try` function under test.
fn build_tc_try_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("eh_invoke");

    // FuncId 0: extern void cxx_throw()  — throws a C++ exception (no return).
    let throw_ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    let mut cxx_throw =
        TrustIrFunction::new(FuncId::new(0), "cxx_throw", throw_ft, BlockId::new(0));
    cxx_throw.linkage = Linkage::External; // body-less: an external declaration
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
                // landingpad catch 0  -> (exn_ptr, selector)
                InstrNode::new(Inst::LandingPad {
                    is_cleanup: false,
                    catch_type_indices: vec![0], // 0 == catch-all (catch(...))
                })
                .with_results(vec![ValueId::new(20), ValueId::new(21)]),
                // __cxa_begin_catch(exn_ptr)
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![ValueId::new(20)],
                })
                .with_result(ValueId::new(22)),
                // __cxa_end_catch()
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(2),
                    args: vec![],
                }),
                // return 42
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

/// Build a module whose invoke region is FULLY unreachable: the entry block
/// returns directly and nothing branches to the invoke/normal/pad blocks.
/// cfg-simplify's unreachable-block removal legitimately prunes the region at
/// O1+; the `eh_metadata` entries anchored on those blocks must be pruned in
/// the same step (previously they survived and the fail-closed pipeline
/// validator rejected the function: "exception landing pad targets block ...
/// absent from block_order").
fn build_dead_invoke_region_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("eh_dead_region");

    let throw_ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![],
        is_vararg: false,
    });
    let mut cxx_throw =
        TrustIrFunction::new(FuncId::new(0), "cxx_throw", throw_ft, BlockId::new(0));
    cxx_throw.linkage = Linkage::External;
    module.add_function(cxx_throw);

    let ft = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut tc_dead = TrustIrFunction::new(FuncId::new(1), "tc_dead", ft, BlockId::new(0));
    tc_dead.blocks = vec![
        // bb0 (entry): return 7 — never reaches the invoke region.
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(7),
                })
                .with_result(ValueId::new(5)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(5)],
                }),
            ],
        },
        // bb1 (dead call site): invoke cxx_throw() to bb2 unwind bb3
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![InstrNode::new(Inst::Invoke {
                callee: FuncId::new(0),
                args: vec![],
                normal_dest: BlockId::new(2),
                normal_args: vec![],
                unwind_dest: BlockId::new(3),
            })],
        },
        // bb2 (dead normal dest): return 0
        TrustIrBlock {
            id: BlockId::new(2),
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
        // bb3 (dead landing pad, catch-all): return 42
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::LandingPad {
                    is_cleanup: false,
                    catch_type_indices: vec![0],
                })
                .with_results(vec![ValueId::new(20), ValueId::new(21)]),
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
    module.add_function(tc_dead);

    module
}

#[test]
fn eh_invoke_fully_unreachable_region_prunes_eh_metadata_in_lockstep() {
    // The previously-rejected shape: at O2, cfg-simplify prunes the dead
    // invoke region; the eh_metadata lockstep pruning must drop the orphaned
    // landing-pad/call-site entries so the fail-closed pipeline validator
    // accepts the function. Before the fix this failed with:
    //   "malformed AArch64 machine function `tc_dead`: exception landing pad
    //    targets block BlockId(2), which is absent from block_order"
    let module = build_dead_invoke_region_module();
    for opt_level in [OptLevel::O1, OptLevel::O2] {
        let compiler = Compiler::new(CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        });
        let result = compiler.compile(&module).unwrap_or_else(|e| {
            panic!("dead-invoke-region module must compile at {opt_level:?}: {e}")
        });
        // Only O2's pass pipeline actually prunes the unreachable region (O1
        // keeps the dead blocks laid out, so its LSDA is legitimately still
        // emitted). Where the region IS pruned, the EH metadata must be gone
        // with it — no orphaned LSDA.
        if opt_level == OptLevel::O2 {
            let obj = &result.object_code;
            assert!(
                !obj.windows(b"__gcc_except_tab".len())
                    .any(|w| w == b"__gcc_except_tab"),
                "{opt_level:?}: a function whose entire invoke region was pruned \
                 must not emit an LSDA"
            );
        }
    }
}

/// Compile the module at O0 and return the `tc_try` object code.
fn compile_to_obj(module: &TrustIrModule) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        ..CompilerConfig::default()
    });
    let result = compiler
        .compile(module)
        .expect("tc_try compilation should succeed");
    assert!(
        !result.object_code.is_empty(),
        "tc_try must produce non-empty object code"
    );
    let obj = &result.object_code;
    let magic = u32::from_le_bytes([obj[0], obj[1], obj[2], obj[3]]);
    assert_eq!(magic, 0xFEED_FACF, "must be valid Mach-O");
    result.object_code.clone()
}

#[test]
fn eh_invoke_trust_ir_compiles_with_lsda() {
    // Compile-only path: exercises the trust-ir Invoke/LandingPad lowering,
    // the eh_info -> eh_metadata forwarding, and post-layout LSDA generation on
    // every host (object inspection only; no link/run).
    let module = build_tc_try_module();
    let obj = compile_to_obj(&module);
    assert!(
        obj.windows(b"__gcc_except_tab".len())
            .any(|w| w == b"__gcc_except_tab"),
        "object compiled from trust-ir Invoke/LandingPad must carry the LSDA \
         (__gcc_except_tab) section — this is the post-layout resolve_eh_offsets \
         + generate_lsda_for_function path"
    );
}

#[test]
fn eh_invoke_trust_ir_link_and_run_catches() {
    if !host_is_aarch64_macos() {
        eprintln!("SKIP: trust-ir Invoke EH catch e2e requires an aarch64-apple-darwin host");
        return;
    }

    let module = build_tc_try_module();
    let obj = compile_to_obj(&module);

    let dir = std::env::temp_dir().join("trust_cg_eh_invoke_trust_ir_e2e");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    let obj_path = dir.join("tc_try.o");
    fs::write(&obj_path, &obj).expect("write .o");

    // C++ driver: provides the throwing callee and a main that calls tc_try.
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

    let bin_path = dir.join("eh_invoke_bin");
    // Link with `c++` so libc++/libc++abi (the personality `___gxx_personality_v0`,
    // `__cxa_*`, `typeinfo for int`) are pulled in.
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
        "tc_try HUNG (timed out) — the catch path did not return. A hang means \
         the unwinder never resolved the landing pad (LSDA call-site / offset bug). \
         stdout: {stdout}\nstderr: {stderr}"
    );
    assert_eq!(
        exit_code,
        Some(0),
        "expected a clean catch (exit 0, sentinel 42). \
         exit={exit_code:?}\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("tc_try returned 42"),
        "expected the catch sentinel in stdout. stdout: {stdout}\nstderr: {stderr}"
    );

    eprintln!("trust-ir Invoke EH catch e2e PASSED: {}", stdout.trim());
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
