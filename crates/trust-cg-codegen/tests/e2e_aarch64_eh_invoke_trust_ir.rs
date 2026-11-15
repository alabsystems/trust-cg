// E2E: AArch64 macOS exception-handling CATCH path driven from trust-ir
// `Inst::Invoke` / `Inst::LandingPad` — end to end through the REAL compiler
// pipeline (adapter -> ISel -> eh_metadata -> post-layout LSDA + compact
// unwind), linked with c++, and run with a process polling deadline.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ----------------------------------------------------------------------------
// WHAT THIS PINS (vs. the hand-authored MachIR `e2e_aarch64_eh_catch`)
// ----------------------------------------------------------------------------
// `e2e_aarch64_eh_catch` exercises the backend EH machinery (LSDA call-site table,
// compact unwind, landing-pad transfer) by hand-authoring a post-regalloc
// `MachFunction` and attaching the EH metadata + byte offsets MANUALLY.
//
// This fixture exercises the trust-ir-driven path: a trust-ir `Module` whose
// function uses `Inst::Invoke` (a call that may unwind) and
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
// Execution uses a polling deadline and nonblocking termination requests.
// Kernel-blocked children can survive a timeout; host cleanup is not guaranteed.

mod common;

use std::fs;
use std::process::Command;
use std::time::Duration;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction,
    ICmpOp, Inst, InstrNode, Linkage, Module as TrustIrModule, Ty, ValueId,
};

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

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

/// Build the trust-ir module: three extern C++/Itanium-runtime declarations
/// plus the `tc_try` function under test.
fn build_tc_try_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("eh_invoke");

    // FuncId 0: extern void cxx_throw()  — throws a C++ exception (no return).
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
    cxx_throw.linkage = Linkage::External; // body-less: an external declaration
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
    module
        .try_add_function(tc_try)
        .expect("Module::try_add_function: test fixture");

    pinned_target::pin(&mut module, "aarch64-apple-darwin");
    module
}

/// Build a module whose invoke region is FULLY dead: the entry block branches
/// on a constant `false`, so only its else arm (a plain return) ever runs.
/// The region stays STRUCTURALLY reachable — trust-ir refuses a block no edge
/// reaches (`UnreachableBlock`), and since WS7.3 every ingestion entry refuses
/// what the validator refuses — and the optimizer's constant-branch folding
/// plus cfg-simplify's unreachable-block removal legitimately prune it at
/// O2; the `eh_metadata` entries anchored on those blocks must be pruned in
/// the same step (previously they survived and the fail-closed pipeline
/// validator rejected the function: "exception landing pad targets block ...
/// absent from block_order").
fn build_dead_invoke_region_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("eh_dead_region");

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

    let ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut tc_dead = TrustIrFunction::new(FuncId::new(1), "tc_dead", ft, BlockId::new(0));
    tc_dead.blocks = vec![
        // bb0 (entry): `if false { invoke region } else { return 7 }` — the
        // invoke region never runs.
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::Bool,
                    value: Constant::Bool(false),
                })
                .with_result(ValueId::new(4)),
                InstrNode::new(Inst::CondBr {
                    cond: ValueId::new(4),
                    then_target: BlockId::new(1),
                    then_args: vec![],
                    else_target: BlockId::new(4),
                    else_args: vec![],
                }),
            ],
        },
        // bb4 (the arm that runs): return 7.
        TrustIrBlock {
            id: BlockId::new(4),
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
    module
        .try_add_function(tc_dead)
        .expect("Module::try_add_function: test fixture");

    pinned_target::pin(&mut module, "aarch64-apple-darwin");
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
        let compiler = macho_compiler(CompilerConfig {
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
    let compiler = macho_compiler(CompilerConfig {
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
    if !host_can_link_and_run_aarch64_eh() {
        eprintln!("SKIP: trust-ir Invoke EH catch e2e requires an AArch64 Linux GNU or macOS host");
        return;
    }

    let module = build_tc_try_module();
    let obj = compile_eh_obj_for(&module, OptLevel::O0, native_host::TRIPLE);

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

    let (exit_code, stdout, stderr, timed_out) = run_with_timeout(
        &bin_path,
        common::rosetta::exec_timeout(Duration::from_secs(10)),
    );

    assert!(
        !timed_out,
        "tc_try exceeded its polling deadline. This does not isolate an \
         unwinder defect from a loader, translation, or host failure. \
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

/// The Linux GNU native lane's object, checked at object level on every host:
/// ELF `.eh_frame` plus the LSDA and the ELF personality spelling.
#[test]
fn eh_invoke_trust_ir_linux_object_carries_eh_frame_and_lsda() {
    let obj = compile_eh_obj_for(
        &build_tc_try_module(),
        OptLevel::O0,
        "aarch64-unknown-linux-gnu",
    );
    let contains = |needle: &[u8]| obj.windows(needle.len()).any(|w| w == needle);
    assert!(contains(b".gcc_except_table"), "missing .gcc_except_table");
    assert!(contains(b"__gxx_personality_v0"), "missing ELF personality");
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

// ---------------------------------------------------------------------------
// A landing pad reads only what its invoke block computed before the call
// ---------------------------------------------------------------------------
//
// An invoke's call leaves its block for the landing pad in the middle of the
// block: what the block computes after the call returns never runs on the
// unwind path. When the invoke's normal destination is a loop header, LICM
// took the invoke block as the loop's preheader and hoisted a loop-invariant
// constant behind the call; CSE or GVN then replaced the landing pad's own
// equal constant with that def, because the invoke block dominates the pad.
// The pad then stored or returned whatever the register held when the callee
// threw: at O3 only, `out=7` against the source's 40000, compiled and linked
// without any refusal. These are the review reproducers of 2026-10-10 (the
// stack-slot loop, and the caller-memory loop in four pad shapes), run
// natively at O0-O3 against a source model.

/// One reproducer: its name, its module and the stdout its driver must print.
struct PadValueCase {
    name: String,
    module: TrustIrModule,
    expected: String,
}

fn pad_extern(module: &mut TrustIrModule, id: u32, name: &str, params: Vec<Ty>, returns: Vec<Ty>) {
    let ft = module
        .add_func_type(FuncTy {
            params,
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut decl = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    decl.linkage = Linkage::External;
    module
        .try_add_function(decl)
        .expect("Module::try_add_function: test fixture");
}

fn pad_function(
    module: &mut TrustIrModule,
    id: u32,
    name: &str,
    params: Vec<Ty>,
    blocks: Vec<TrustIrBlock>,
) {
    let ft = module
        .add_func_type(FuncTy {
            params,
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    function.blocks = blocks;
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

fn pad_v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn pad_const(value: i64, result: u32) -> InstrNode {
    InstrNode::new(Inst::Const {
        ty: Ty::I64,
        value: Constant::Int(i128::from(value)),
    })
    .with_result(pad_v(result))
}

fn pad_bin(op: BinOp, lhs: u32, rhs: u32, result: u32) -> InstrNode {
    InstrNode::new(Inst::BinOp {
        op,
        ty: Ty::I64,
        lhs: pad_v(lhs),
        rhs: pad_v(rhs),
    })
    .with_result(pad_v(result))
}

fn pad_load(ptr: u32, result: u32) -> InstrNode {
    InstrNode::new(Inst::Load {
        ty: Ty::I64,
        ptr: pad_v(ptr),
        volatile: false,
        align: Some(8),
    })
    .with_result(pad_v(result))
}

fn pad_store(ptr: u32, value: u32) -> InstrNode {
    InstrNode::new(Inst::Store {
        ty: Ty::I64,
        ptr: pad_v(ptr),
        value: pad_v(value),
        volatile: false,
        align: Some(8),
    })
}

fn pad_call(callee: u32, args: &[u32]) -> InstrNode {
    InstrNode::new(Inst::Call {
        callee: FuncId::new(callee),
        args: args.iter().copied().map(pad_v).collect(),
    })
}

fn pad_return(value: u32) -> InstrNode {
    InstrNode::new(Inst::Return {
        values: vec![pad_v(value)],
    })
}

/// A catch-all landing pad's opening: `(exception pointer, selector)`.
fn pad_landing(exception: u32, selector: u32) -> InstrNode {
    InstrNode::new(Inst::LandingPad {
        is_cleanup: false,
        catch_type_indices: vec![0],
    })
    .with_results(vec![pad_v(exception), pad_v(selector)])
}

fn pad_cond_loop(cond: u32, header: u32, exit: u32) -> InstrNode {
    InstrNode::new(Inst::CondBr {
        cond: pad_v(cond),
        then_target: BlockId::new(header),
        then_args: vec![],
        else_target: BlockId::new(exit),
        else_args: vec![],
    })
}

fn pad_alloca(result: u32) -> InstrNode {
    InstrNode::new(Inst::Alloca {
        ty: Ty::I64,
        count: None,
        align: Some(8),
    })
    .with_result(pad_v(result))
}

/// Twelve products of `x = v0` live across a plain call to function 4, their
/// xor stored through `out`: when a later callee throws, the callee-saved
/// registers hold this frame's own values, not the caller's.
fn pad_dirty_frame(out: u32) -> Vec<InstrNode> {
    let mut body = Vec::new();
    for i in 0..12u32 {
        body.push(pad_const(i64::from(i) * 7 + 3, 100 + i));
        body.push(pad_bin(BinOp::Mul, 0, 100 + i, 120 + i));
    }
    body.push(pad_call(4, &[]));
    body.push(pad_bin(BinOp::Add, 120, 121, 140));
    for i in 2..12u32 {
        body.push(pad_bin(BinOp::Xor, 140 + i - 2, 120 + i, 140 + i - 1));
    }
    body.push(pad_store(out, 150));
    body
}

const SLOT_LOOP_K: i64 = 40_000;

/// `tcp_slots(x, n, out)`: twelve products of `x` live across a plain call
/// (callee-saved registers hold this frame's values before the invoke), their
/// xor stored to `*out`, two stack slots, then `invoke tcp_may_throw(x)`
/// whose normal destination is the loop header `acc = acc * K + i`. The
/// catch-all pad materializes its own K before (`pad_const_first`) or after
/// its runtime calls, stores it to `*out` and returns 1.
fn build_slot_loop_pad_module(pad_const_first: bool) -> TrustIrModule {
    let mut module = TrustIrModule::new("eh_pad_value_slot_loop");
    pad_extern(&mut module, 0, "tcp_may_throw", vec![Ty::I64], vec![]);
    pad_extern(
        &mut module,
        1,
        "__cxa_begin_catch",
        vec![Ty::Ptr],
        vec![Ty::Ptr],
    );
    pad_extern(&mut module, 2, "__cxa_end_catch", vec![], vec![]);
    pad_extern(&mut module, 4, "tcp_note", vec![], vec![]);

    // bb0(x = v0, n = v1, out = v5)
    let mut entry = pad_dirty_frame(5);
    entry.extend([
        pad_const(0, 2),
        pad_alloca(3),
        pad_alloca(4),
        pad_store(3, 0),
        pad_store(4, 2),
        InstrNode::new(Inst::Invoke {
            callee: FuncId::new(0),
            args: vec![pad_v(0)],
            normal_dest: BlockId::new(1),
            normal_args: vec![],
            unwind_dest: BlockId::new(3),
        }),
    ]);

    let mut pad = vec![pad_landing(30, 31)];
    if pad_const_first {
        pad.push(pad_const(SLOT_LOOP_K, 33));
    }
    pad.push(pad_call(1, &[30]).with_result(pad_v(32)));
    pad.push(pad_call(2, &[]));
    if !pad_const_first {
        pad.push(pad_const(SLOT_LOOP_K, 33));
    }
    pad.extend([pad_store(5, 33), pad_const(1, 34), pad_return(34)]);

    let blocks = vec![
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![
                (pad_v(0), Ty::I64),
                (pad_v(1), Ty::I64),
                (pad_v(5), Ty::Ptr),
            ],
            body: entry,
        },
        // bb1: acc = acc * K + i; i += 1; i < n ? bb1 : bb2
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![
                pad_load(3, 11),
                pad_load(4, 10),
                pad_const(SLOT_LOOP_K, 12),
                pad_bin(BinOp::Mul, 11, 12, 13),
                pad_bin(BinOp::Add, 13, 10, 14),
                pad_store(3, 14),
                pad_const(1, 15),
                pad_bin(BinOp::Add, 10, 15, 16),
                pad_store(4, 16),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Slt,
                    ty: Ty::I64,
                    lhs: pad_v(16),
                    rhs: pad_v(1),
                })
                .with_result(pad_v(17)),
                pad_cond_loop(17, 1, 2),
            ],
        },
        // bb2: return acc
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![pad_load(3, 20), pad_return(20)],
        },
        // bb3: the catch-all landing pad
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![],
            body: pad,
        },
    ];
    pad_function(
        &mut module,
        3,
        "tcp_slots",
        vec![Ty::I64, Ty::I64, Ty::Ptr],
        blocks,
    );
    module
}

/// The stack-slot loop's source model, for its driver's two calls.
fn slot_loop_model() -> String {
    let (mut acc, mut i) = (3i64, 0i64);
    loop {
        acc = acc.wrapping_mul(SLOT_LOOP_K).wrapping_add(i);
        i += 1;
        if i >= 4 {
            break;
        }
    }
    format!("nothrow={acc} throw=1 out={SLOT_LOOP_K}")
}

const SLOT_LOOP_DRIVER: &str = r#"
#include <cstdio>
#include <cstdint>
extern "C" int64_t tcp_slots(int64_t x, int64_t n, int64_t *out);
extern "C" void tcp_may_throw(int64_t x) { if (x == 7) throw 7; }
extern "C" void tcp_note() { }
int main() {
    int64_t o1 = -1, o2 = -1;
    long long a = (long long)tcp_slots(3, 4, &o1);
    long long b = (long long)tcp_slots(7, 4, &o2);
    printf("nothrow=%lld throw=%lld out=%lld\n", a, b, (long long)o2);
    return 0;
}
"#;

const MEMORY_LOOP_K: i64 = 47_073; // one MOVZ, not a multiply immediate
const MEMORY_LOOP_PAD_RET: i64 = -5;

/// The landing pad shapes of the caller-memory loop.
#[derive(Clone, Copy, Debug, PartialEq)]
enum MemoryLoopPad {
    /// `K -> *out` before the runtime calls, then `return -5`.
    StoreBeforeCalls,
    /// The runtime calls, then `return K`.
    ReturnAfterCalls,
    /// As `ReturnAfterCalls`, with the invoke argument `sel * 3` kept across
    /// a plain call (a callee-saved register written before the invoke).
    ReturnAfterCallsDirty,
    /// As `StoreBeforeCalls`, with an invoke result the normal path uses (its
    /// copy follows the call in the invoke block).
    StoreBeforeCallsWithResult,
}

/// `rvp_probe(sel, acc_p, cnt_p, out_p)`: `invoke` whose normal destination is
/// a loop over caller memory (`*acc = *acc * K + *cnt; *cnt -= 1` while
/// `*cnt > 0`), and a catch-all pad of the given shape that uses its own K.
fn build_memory_loop_pad_module(shape: MemoryLoopPad) -> TrustIrModule {
    let mut module = TrustIrModule::new("eh_pad_value_memory_loop");
    pad_extern(&mut module, 0, "rvp_maybe_throw", vec![Ty::I64], vec![]);
    pad_extern(
        &mut module,
        1,
        "__cxa_begin_catch",
        vec![Ty::Ptr],
        vec![Ty::Ptr],
    );
    pad_extern(&mut module, 2, "__cxa_end_catch", vec![], vec![]);
    pad_extern(&mut module, 4, "rvp_note", vec![], vec![]);
    pad_extern(
        &mut module,
        5,
        "rvp_maybe_throw_r",
        vec![Ty::I64],
        vec![Ty::I64],
    );

    let mut entry = Vec::new();
    let invoke_arg = if shape == MemoryLoopPad::ReturnAfterCallsDirty {
        entry.push(pad_const(3, 50));
        entry.push(pad_bin(BinOp::Mul, 0, 50, 51));
        entry.push(pad_call(4, &[]));
        51
    } else {
        0
    };
    let with_result = shape == MemoryLoopPad::StoreBeforeCallsWithResult;
    let invoke = InstrNode::new(Inst::Invoke {
        callee: FuncId::new(if with_result { 5 } else { 0 }),
        args: vec![pad_v(invoke_arg)],
        normal_dest: BlockId::new(1),
        normal_args: vec![],
        unwind_dest: BlockId::new(3),
    });
    entry.push(if with_result {
        invoke.with_result(pad_v(40))
    } else {
        invoke
    });

    let mut pad = vec![pad_landing(30, 31)];
    let begin = pad_call(1, &[30]).with_result(pad_v(32));
    let end = pad_call(2, &[]);
    match shape {
        MemoryLoopPad::StoreBeforeCalls | MemoryLoopPad::StoreBeforeCallsWithResult => {
            pad.extend([
                pad_const(MEMORY_LOOP_K, 33),
                pad_store(3, 33),
                begin,
                end,
                pad_const(MEMORY_LOOP_PAD_RET, 34),
                pad_return(34),
            ])
        }
        MemoryLoopPad::ReturnAfterCalls | MemoryLoopPad::ReturnAfterCallsDirty => {
            pad.extend([begin, end, pad_const(MEMORY_LOOP_K, 33), pad_return(33)])
        }
    }

    let exit = if with_result {
        vec![
            pad_load(1, 20),
            pad_bin(BinOp::Add, 20, 40, 21),
            pad_return(21),
        ]
    } else {
        vec![pad_load(1, 20), pad_return(20)]
    };
    let blocks = vec![
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![
                (pad_v(0), Ty::I64),
                (pad_v(1), Ty::Ptr),
                (pad_v(2), Ty::Ptr),
                (pad_v(3), Ty::Ptr),
            ],
            body: entry,
        },
        // bb1: a = *acc_p; n = *cnt_p; *acc_p = a * K + n; *cnt_p = n - 1;
        // n - 1 > 0 ? bb1 : bb2
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![
                pad_load(1, 10),
                pad_load(2, 11),
                pad_const(MEMORY_LOOP_K, 12),
                pad_bin(BinOp::Mul, 10, 12, 13),
                pad_bin(BinOp::Add, 13, 11, 14),
                pad_store(1, 14),
                pad_const(1, 15),
                pad_bin(BinOp::Sub, 11, 15, 16),
                pad_store(2, 16),
                pad_const(0, 17),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sgt,
                    ty: Ty::I64,
                    lhs: pad_v(16),
                    rhs: pad_v(17),
                })
                .with_result(pad_v(18)),
                pad_cond_loop(18, 1, 2),
            ],
        },
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: exit,
        },
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![],
            body: pad,
        },
    ];
    pad_function(
        &mut module,
        3,
        "rvp_probe",
        vec![Ty::I64, Ty::Ptr, Ty::Ptr, Ty::Ptr],
        blocks,
    );
    module
}

/// The caller-memory loop's source model, for its driver's two calls.
fn memory_loop_model(shape: MemoryLoopPad) -> String {
    let (mut acc, mut cnt) = (5i64, 3i64);
    loop {
        acc = acc.wrapping_mul(MEMORY_LOOP_K).wrapping_add(cnt);
        cnt -= 1;
        if cnt <= 0 {
            break;
        }
    }
    let ret = if shape == MemoryLoopPad::StoreBeforeCallsWithResult {
        // rvp_maybe_throw_r(4) returns 4 + 1000.
        acc.wrapping_add(1004)
    } else {
        acc
    };
    let throw = match shape {
        MemoryLoopPad::StoreBeforeCalls | MemoryLoopPad::StoreBeforeCallsWithResult => {
            format!("throw ret={MEMORY_LOOP_PAD_RET} acc=5 cnt=3 out={MEMORY_LOOP_K}")
        }
        MemoryLoopPad::ReturnAfterCalls | MemoryLoopPad::ReturnAfterCallsDirty => {
            format!("throw ret={MEMORY_LOOP_K} acc=5 cnt=3 out=-1")
        }
    };
    format!("normal ret={ret} acc={acc} cnt={cnt} out=-1\n{throw}")
}

const MEMORY_LOOP_DRIVER: &str = r#"
#include <cstdio>
#include <cstdint>
extern "C" int64_t rvp_probe(int64_t sel, int64_t *acc, int64_t *cnt, int64_t *out);
extern "C" void rvp_maybe_throw(int64_t s) { if (s == 13 || s == 39) throw 99; }
extern "C" void rvp_note() { }
extern "C" int64_t rvp_maybe_throw_r(int64_t s) { if (s == 13) throw 99; return s + 1000; }
int main() {
    int64_t acc = 5, cnt = 3, out = -1;
    long long r = (long long)rvp_probe(4, &acc, &cnt, &out);
    printf("normal ret=%lld acc=%lld cnt=%lld out=%lld\n", r, (long long)acc, (long long)cnt, (long long)out);
    acc = 5; cnt = 3; out = -1;
    r = (long long)rvp_probe(13, &acc, &cnt, &out);
    printf("throw ret=%lld acc=%lld cnt=%lld out=%lld\n", r, (long long)acc, (long long)cnt, (long long)out);
    return 0;
}
"#;

/// Compile every case at O0-O3 for the native triple, link it with `driver`
/// through `c++`, run it, and require the model's stdout in every cell. A
/// refused compile fails the cell: the fixed backend compiles every shape.
/// Each case module is pinned to the native triple: its may-throw callee is a
/// bodyless external, an FFI boundary trust-ir's validator admits only under a
/// pinned target (`TargetInfoRequired`), which every ingestion entry refuses
/// since WS7.3.
fn run_pad_value_cases(prefix: &str, driver: &str, cases: &[PadValueCase]) {
    if !host_can_link_and_run_aarch64_eh() {
        eprintln!("SKIP: landing-pad value e2e requires an AArch64 Linux GNU or macOS host");
        return;
    }
    let dir = fresh_dir::create(prefix);
    let driver_path = dir.join("driver.cpp");
    fs::write(&driver_path, driver).expect("write driver");
    let spec = trust_cg_codegen::target::TargetSpec::parse(native_host::TRIPLE)
        .expect("native triple parses");
    let mut failures = Vec::new();
    let mut cells = 0usize;
    for case in cases {
        for (level, opt_level) in [
            ("O0", OptLevel::O0),
            ("O1", OptLevel::O1),
            ("O2", OptLevel::O2),
            ("O3", OptLevel::O3),
        ] {
            cells += 1;
            let tag = format!("{}_{level}", case.name);
            let compiled = Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level,
                    ..CompilerConfig::default()
                },
                spec,
            )
            .with_codegen_license(permit_unlicensed())
            .compile(&pinned_target::pinned(&case.module, native_host::TRIPLE));
            let obj = match compiled {
                Ok(result) => result.object_code,
                Err(error) => {
                    failures.push(format!("{tag}: compile refused: {error}"));
                    continue;
                }
            };
            let obj_path = dir.join(format!("{tag}.o"));
            fs::write(&obj_path, &obj).expect("write .o");
            let bin_path = dir.join(&tag);
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
                "{tag}: link failed:\n{}",
                String::from_utf8_lossy(&link.stderr)
            );
            let (exit_code, stdout, stderr, timed_out) = run_with_timeout(
                &bin_path,
                common::rosetta::exec_timeout(Duration::from_secs(10)),
            );
            let stdout = stdout.trim();
            if timed_out || exit_code != Some(0) || stdout != case.expected {
                failures.push(format!(
                    "{tag}: exit={exit_code:?} timed_out={timed_out}\n  got:      {}\n  \
                     expected: {}\n  stderr: {}",
                    stdout.replace('\n', " | "),
                    case.expected.replace('\n', " | "),
                    stderr.trim()
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {cells} cells diverge from the source model (a landing pad must \
         not read a value its invoke block computes after the call):\n{}",
        failures.len(),
        failures.join("\n")
    );
    eprintln!("{prefix}: {cells}/{cells} cells match the source model");
}

#[test]
fn eh_pad_reads_its_own_constant_after_an_invoke_into_a_slot_loop() {
    let cases: Vec<PadValueCase> = [("constfirst", true), ("constlast", false)]
        .into_iter()
        .map(|(name, first)| PadValueCase {
            name: format!("slot_loop_{name}"),
            module: build_slot_loop_pad_module(first),
            expected: slot_loop_model(),
        })
        .collect();
    run_pad_value_cases("trust_cg_eh_pad_value_slot_loop-", SLOT_LOOP_DRIVER, &cases);
}

#[test]
fn eh_pad_reads_its_own_constant_after_an_invoke_into_a_memory_loop() {
    let cases: Vec<PadValueCase> = [
        MemoryLoopPad::StoreBeforeCalls,
        MemoryLoopPad::ReturnAfterCalls,
        MemoryLoopPad::ReturnAfterCallsDirty,
        MemoryLoopPad::StoreBeforeCallsWithResult,
    ]
    .into_iter()
    .map(|shape| PadValueCase {
        name: format!("memory_loop_{shape:?}"),
        module: build_memory_loop_pad_module(shape),
        expected: memory_loop_model(shape),
    })
    .collect();
    run_pad_value_cases(
        "trust_cg_eh_pad_value_memory_loop-",
        MEMORY_LOOP_DRIVER,
        &cases,
    );
}

// ---------------------------------------------------------------------------
// A landing pad that heads a catch-and-retry loop
// ---------------------------------------------------------------------------
//
// A landing pad is entered only over exception edges, so when it heads a loop
// (catch, then retry through an invoke that unwinds to the same pad) the
// loop's one outside predecessor, its preheader, is the first invoke's block.
// Code a pass places in that preheader goes after the call and never runs on
// the edge into the loop, and the loop reads it directly: no CSE or GVN reuse
// is involved, so their mid-block exit rule does not cover it. LICM's refusal
// of an invoke-block preheader is the one check that keeps this shape right
// (OD-EH-PAD-VALUES-20261010). Without it, LICM hoists the pad's constant
// behind the call at O2 and O3: the dirty-frame cases then multiply by a
// product of `x` that the register held before the call, compiled, linked and
// accepted silently, and the clean-frame case is refused by the final stream
// check ([TCG-A64-SPILL-SLOT] caller-callee-saved-value-read).

const RETRY_LOOP_K_MOVZ: i64 = 40_000; // one MOVZ
const RETRY_LOOP_K_MOVK: i64 = 0x1_2345_6789; // a MOVZ/MOVK chain

/// `tcr_retry(x, n, out, out2)`: bb0 stores 0 to a counter slot and invokes
/// `tcr_may_throw(x)`, whose normal destination returns `*slot + 1000`. The
/// catch-all pad is the loop header: it counts in the slot, stores
/// `count * K` to `*out` and, while `count < n`, retries through a second
/// invoke that unwinds to the pad again; then it returns the count. With
/// `dirty_frame`, bb0 first runs [`pad_dirty_frame`] into `*out2`.
fn build_retry_loop_pad_module(k: i64, dirty_frame: bool) -> TrustIrModule {
    let mut module = TrustIrModule::new("eh_pad_value_retry_loop");
    pad_extern(&mut module, 0, "tcr_may_throw", vec![Ty::I64], vec![]);
    pad_extern(
        &mut module,
        1,
        "__cxa_begin_catch",
        vec![Ty::Ptr],
        vec![Ty::Ptr],
    );
    pad_extern(&mut module, 2, "__cxa_end_catch", vec![], vec![]);
    pad_extern(&mut module, 4, "tcr_note", vec![], vec![]);

    let invoke = || {
        InstrNode::new(Inst::Invoke {
            callee: FuncId::new(0),
            args: vec![pad_v(0)],
            normal_dest: BlockId::new(1),
            normal_args: vec![],
            unwind_dest: BlockId::new(2),
        })
    };
    // bb0(x = v0, n = v1, out = v2, out2 = v5)
    let mut entry = if dirty_frame {
        pad_dirty_frame(5)
    } else {
        Vec::new()
    };
    entry.extend([pad_alloca(3), pad_const(0, 4), pad_store(3, 4), invoke()]);

    let blocks = vec![
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![
                (pad_v(0), Ty::I64),
                (pad_v(1), Ty::I64),
                (pad_v(2), Ty::Ptr),
                (pad_v(5), Ty::Ptr),
            ],
            body: entry,
        },
        // bb1 (normal destination of both invokes): return *slot + 1000
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![],
            body: vec![
                pad_load(3, 10),
                pad_const(1000, 11),
                pad_bin(BinOp::Add, 10, 11, 12),
                pad_return(12),
            ],
        },
        // bb2 (the catch-all pad, loop header): count = *slot + 1;
        // *slot = count; *out = count * K; count < n ? bb3 : bb4
        TrustIrBlock {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                pad_landing(20, 21),
                pad_call(1, &[20]).with_result(pad_v(22)),
                pad_call(2, &[]),
                pad_load(3, 23),
                pad_const(1, 24),
                pad_bin(BinOp::Add, 23, 24, 25),
                pad_store(3, 25),
                pad_const(k, 26),
                pad_bin(BinOp::Mul, 25, 26, 27),
                pad_store(2, 27),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Slt,
                    ty: Ty::I64,
                    lhs: pad_v(25),
                    rhs: pad_v(1),
                })
                .with_result(pad_v(28)),
                pad_cond_loop(28, 3, 4),
            ],
        },
        // bb3 (the latch): retry; the exception edge is the back edge
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![],
            body: vec![invoke()],
        },
        // bb4: give up, return the count
        TrustIrBlock {
            id: BlockId::new(4),
            params: vec![],
            body: vec![pad_load(3, 30), pad_return(30)],
        },
    ];
    pad_function(
        &mut module,
        3,
        "tcr_retry",
        vec![Ty::I64, Ty::I64, Ty::Ptr, Ty::Ptr],
        blocks,
    );
    module
}

/// The retry loop's source model against its driver's thrower: `x = 3`
/// never throws, `x = 7` always throws, and `x = 9` throws three times.
fn retry_loop_model(k: i64) -> String {
    let run = |mut throws: u32| {
        let (n, mut slot, mut out) = (5i64, 0i64, -1i64);
        loop {
            if throws == 0 {
                return (slot + 1000, out);
            }
            throws -= 1;
            slot += 1;
            out = slot.wrapping_mul(k);
            if slot >= n {
                return (slot, out);
            }
        }
    };
    let (a, o1) = run(0);
    let (b, o2) = run(u32::MAX);
    let (c, o3) = run(3);
    format!("a={a} o1={o1} b={b} o2={o2} c={c} o3={o3}")
}

const RETRY_LOOP_DRIVER: &str = r#"
#include <cstdio>
#include <cstdint>
extern "C" int64_t tcr_retry(int64_t x, int64_t n, int64_t *out, int64_t *out2);
static int64_t g_left = 0;
extern "C" void tcr_may_throw(int64_t x) {
    if (x == 7) throw 7;
    if (x == 9 && g_left > 0) { g_left--; throw 9; }
}
extern "C" void tcr_note() { }
int main() {
    int64_t o1 = -1, o2 = -1, o3 = -1, d = 0;
    long long a = (long long)tcr_retry(3, 5, &o1, &d);
    long long b = (long long)tcr_retry(7, 5, &o2, &d);
    g_left = 3;
    long long c = (long long)tcr_retry(9, 5, &o3, &d);
    printf("a=%lld o1=%lld b=%lld o2=%lld c=%lld o3=%lld\n", a, (long long)o1, b,
           (long long)o2, c, (long long)o3);
    return 0;
}
"#;

#[test]
fn eh_pad_reads_its_own_constant_as_the_header_of_a_retry_loop() {
    let cases: Vec<PadValueCase> = [
        ("dirty_movz", RETRY_LOOP_K_MOVZ, true),
        ("dirty_movk", RETRY_LOOP_K_MOVK, true),
        ("clean_movz", RETRY_LOOP_K_MOVZ, false),
    ]
    .into_iter()
    .map(|(name, k, dirty_frame)| PadValueCase {
        name: format!("retry_loop_{name}"),
        module: build_retry_loop_pad_module(k, dirty_frame),
        expected: retry_loop_model(k),
    })
    .collect();
    run_pad_value_cases(
        "trust_cg_eh_pad_value_retry_loop-",
        RETRY_LOOP_DRIVER,
        &cases,
    );
}
