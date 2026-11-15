// E2E (x86-64): the x86-64 exception-handling RESUME / continue-unwind path — a
// cleanup-only landing pad that runs cleanup and then re-raises, whose re-raise
// MUST propagate PAST the cleanup frame to an enclosing handler. RUN NATIVELY on
// x86-64 Linux GNU (ELF) or x86-64 macOS (Mach-O). [EH flip Slice B]
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ----------------------------------------------------------------------------
// WHAT THIS PINS (the x86 analog of `e2e_aarch64_eh_resume_trust_ir`)
// ----------------------------------------------------------------------------
// The CATCH e2e (`e2e_x86_64_eh_catch`) checks an `Invoke`/CALL of a throwing
// callee with a *catching* landing pad (catch(...)) returns the sentinel. This
// test exercises the RESUME / continue-unwind path on x86: a **cleanup-only**
// landing pad (is_cleanup=true, NO catch types — exactly the Rust Drop-glue
// shape) that runs cleanup and then re-raises (`_Unwind_Resume`). The re-raised
// exception MUST propagate PAST the cleanup frame to an ENCLOSING handler (a C++
// `try{ }catch(...)` in the driver). If the x86 backend EH emission for a
// cleanup pad were wrong (e.g. an LSDA call-site table with a GAP at the resume
// PC), the cleanup would run but `_Unwind_Resume` would re-consult the LSDA,
// find no covering call-site entry, and call `std::terminate()` (`terminating
// due to uncaught exception`, exit 134) instead of continuing the unwind to the
// enclosing catch. Exit status and sentinels check this fixture's
// `[0, code_len)` call-site synthesis (`resolve_x86_eh_offsets` ->
// `x86_lsda_for_function`); they do not prove general unwinding correctness or
// establish that the host is safe for additional EH execution.
//
//   extern "C" int tc_cleanup() {
//     try   { cxx_throw(); return 0; }               // bb0 call + bb1 normal
//     cleanup { record_cleanup(exn); resume(exn); }  // bb1 cleanup pad -> Resume
//   }
//   // driver:
//   try { tc_cleanup(); } catch (...) { /* enclosing handler MUST fire */ }
//
// The runnable fixture is built at the `X86ISelFunction` / `X86Pipeline::
// compile_module` level with the C++ personality (`__gxx_personality_v0`) and
// linked with `c++`, exactly like `e2e_x86_64_eh_catch`, so the enclosing
// `catch(...)` catches a plain C++ exception — no Rust runtime needed. (The
// production trust-ir -> x86 lowering emits the RUST personality for a Rust
// cleanup frame; that runtime fixture, which needs libstd / libpanic_unwind, is
// `unwind_cleanup_x86_64.rs` — the bridge split-model Slice C.)
// `eh_resume_trust_ir_x86_lowers_rust_personality_lsda` below still exercises the
// trust-ir `Inst::Invoke` / cleanup `Inst::LandingPad` / `Inst::Resume` lowering
// at the object level, in BOTH containers, and locks the Slice A personality
// spelling through the full `Compiler` path.
//
// The exception object is threaded THROUGH `record_cleanup` via the C ABI
// (arg0 in, return value out) so it survives the cleanup call without needing a
// hand-built spill — the SAME exn is handed to `_Unwind_Resume`.
//
// HOST GATING IS COMPILE-TIME (`common/x86_64_native_host.rs`): the native row
// exists only on a host that links and runs x86-64 objects, so no runtime SKIP
// can be counted as a pass by a floor runner.
//
// Execution uses a polling deadline and nonblocking termination requests.
// Kernel-blocked children can survive a timeout; host cleanup is not guaranteed.

mod common;
#[path = "common/pinned_target.rs"]
mod pinned_target;

use common::x86_64_native_host as host;

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

    let rec_ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut rec = TrustIrFunction::new(FuncId::new(1), "record_cleanup", rec_ft, BlockId::new(0));
    rec.linkage = Linkage::External;
    module
        .try_add_function(rec)
        .expect("Module::try_add_function: test fixture");

    // The rustc bridge declares the body-less external `rust_eh_personality`
    // marker for every unwinding Rust function it lowers; the adapter's
    // `default_eh_personality` detects it and selects the Rust personality
    // over the C++ `__gxx_personality_v0` default (see
    // trust-cg-lower/src/adapter.rs `RUST_EH_PERSONALITY`). This module models
    // a Rust cleanup frame, so it declares the marker exactly as the bridge
    // does.
    let personality_ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut personality = TrustIrFunction::new(
        FuncId::new(2),
        "rust_eh_personality",
        personality_ft,
        BlockId::new(0),
    );
    personality.linkage = Linkage::External;
    module
        .try_add_function(personality)
        .expect("Module::try_add_function: test fixture");

    let try_ft = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
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
    module
        .try_add_function(tc)
        .expect("Module::try_add_function: test fixture");
    module
}

/// Compile the cleanup-only X86ISel function through the standard module path
/// (LSDA + zPLR FDE + personality) for `format`.
fn compile_x86_isel_to_obj(format: X86OutputFormat, func: X86ISelFunction) -> Vec<u8> {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        emit_frame: true,
        output_format: format,
        ..X86PipelineConfig::default()
    });
    pipeline
        .compile_module(&[func])
        .unwrap_or_else(|error| panic!("compile_module tc_cleanup_x86 for {format:?}: {error}"))
}

/// Host-neutral: a cleanup-only pad carries the unwind bundle in BOTH wired
/// containers.
#[test]
fn eh_resume_x86_compiles_with_lsda() {
    let macho = compile_x86_isel_to_obj(X86OutputFormat::MachO, build_tc_cleanup_x86());
    host::assert_macho_x86_64_object(&macho);
    assert!(
        host::object_contains(&macho, b"__gcc_except_tab"),
        "cleanup-only landing pad must carry the LSDA (__gcc_except_tab)"
    );
    assert!(
        host::object_contains(&macho, b"__eh_frame"),
        "cleanup-only landing pad must carry the __eh_frame section"
    );

    let elf = compile_x86_isel_to_obj(X86OutputFormat::Elf, build_tc_cleanup_x86());
    host::assert_elf_x86_64_object(&elf);
    assert!(
        host::object_contains(&elf, b".gcc_except_table"),
        "cleanup-only landing pad must carry the LSDA (.gcc_except_table)"
    );
    assert!(
        host::object_contains(&elf, b".eh_frame"),
        "cleanup-only landing pad must carry the .eh_frame section"
    );
    assert!(
        host::object_contains(&elf, b"DW.ref.__gxx_personality_v0"),
        "the zPLR CIE's DW_EH_PE_indirect personality field names a DW.ref slot"
    );
}

/// Compile the trust-ir cleanup module through the real `Compiler` for an
/// EXPLICIT x86-64 triple (the default spec is host-OS-aware, so every row names
/// its triple; both wired containers cross-emit on every host).
fn compile_trust_ir_cleanup_for(triple: &str) -> Vec<u8> {
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            target: Target::X86_64,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple)
            .unwrap_or_else(|error| panic!("parse {triple} target spec: {error}")),
    )
    .with_codegen_license(permit_unlicensed());
    compiler
        .compile(&pinned_target::pinned(
            &build_tc_cleanup_trust_ir_module(),
            triple,
        ))
        .unwrap_or_else(|error| panic!("trust-ir cleanup lowering for {triple}: {error}"))
        .object_code
}

/// Lock the Slice A personality-name fix through the PRODUCTION trust-ir -> x86
/// lowering, in BOTH containers: the emitted object references the std-provided
/// personality under its container's own spelling — Mach-O's single-underscore
/// `_rust_eh_personality` (never the undefined triple `___rust_eh_personality`)
/// and ELF's BARE `rust_eh_personality`, reached through the `DW.ref` slot.
#[test]
fn eh_resume_trust_ir_x86_lowers_rust_personality_lsda() {
    let macho = compile_trust_ir_cleanup_for("x86_64-apple-darwin");
    host::assert_macho_x86_64_object(&macho);
    assert!(
        host::object_contains(&macho, b"__gcc_except_tab"),
        "trust-ir cleanup LandingPad must lower to an LSDA (__gcc_except_tab)"
    );
    assert!(
        host::object_contains(&macho, b"\x00_rust_eh_personality\x00"),
        "the trust-ir -> x86 Mach-O lowering must reference the std-provided \
         _rust_eh_personality (single underscore)"
    );
    assert!(
        !host::object_contains(&macho, b"___rust_eh_personality"),
        "must NOT reference the undefined ___rust_eh_personality (the \
         double-prefix link failure Slice A removes)"
    );

    // The ELF twin. This row used to be Mach-O-only because the default
    // host-OS-aware spec selected ELF on Linux, where x86-64 EH emission did not
    // exist and the compiler failed closed; the ELF `.eh_frame` /
    // `.gcc_except_table` lane has landed, so the ELF shape is pinned here too.
    let elf = compile_trust_ir_cleanup_for("x86_64-unknown-linux-gnu");
    host::assert_elf_x86_64_object(&elf);
    assert!(
        host::object_contains(&elf, b".gcc_except_table"),
        "trust-ir cleanup LandingPad must lower to an LSDA (.gcc_except_table)"
    );
    assert!(
        host::object_contains(&elf, b"\x00rust_eh_personality\x00"),
        "ELF names the personality BARE, with no container prefix"
    );
    assert!(
        !host::object_contains(&elf, b"_rust_eh_personality\x00"),
        "ELF must NOT carry any underscore-prefixed spelling of the personality"
    );
    assert!(
        host::object_contains(&elf, b"DW.ref.rust_eh_personality"),
        "the zPLR CIE's DW_EH_PE_indirect personality field names a DW.ref slot"
    );
}

// ---------------------------------------------------------------------------
// Native row: link with the host `c++` and observe the re-raise reaching the
// ENCLOSING catch.
//
// COMPILE-TIME gated (`common/x86_64_native_host.rs`). On a native host the
// `c++` driver is a REQUIREMENT, not a probe: a missing one fails this row
// rather than printing a SKIP a floor runner would read as a pass.
// ---------------------------------------------------------------------------

#[cfg(any(
    all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"),
    all(target_arch = "x86_64", target_os = "macos"),
))]
#[test]
fn eh_resume_x86_link_and_run_propagates_to_enclosing_catch() {
    use std::fs;

    let format = if host::LINUX_GNU {
        X86OutputFormat::Elf
    } else {
        X86OutputFormat::MachO
    };
    let obj = compile_x86_isel_to_obj(format, build_tc_cleanup_x86());
    host::assert_native_object(&obj);
    let (lsda_section, cfi_section) = host::eh_section_names();
    assert!(host::object_contains(&obj, lsda_section));
    assert!(host::object_contains(&obj, cfi_section));

    let scratch = tempfile::Builder::new()
        .prefix("trust_cg_x86_eh_resume_e2e_")
        .tempdir()
        .expect("create owned test directory");
    let dir = scratch.path();
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
    let link = Command::new(host::CXX_COMPILER)
        .args(host::cxx_link_args())
        .args([
            driver_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            bin_path.to_str().unwrap(),
        ])
        .output()
        .unwrap_or_else(|error| {
            panic!(
                "{} is required on {}, not optional: {error}",
                host::CXX_COMPILER,
                host::HOST
            )
        });
    assert!(
        link.status.success(),
        "link failed on {}:\n{}",
        host::HOST,
        String::from_utf8_lossy(&link.stderr)
    );

    let (exit_code, stdout, stderr, timed_out) = run_with_timeout(
        &bin_path,
        common::rosetta::exec_timeout(Duration::from_secs(10)),
    );

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

    eprintln!(
        "x86 Resume EH e2e PASSED on {}: {}",
        host::HOST,
        stdout.trim()
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
