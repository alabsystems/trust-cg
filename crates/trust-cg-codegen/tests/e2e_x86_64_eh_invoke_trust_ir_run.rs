// E2E (x86-64): the x86-64 exception-handling CATCH path driven from trust-ir
// `Inst::Invoke` / `Inst::LandingPad` — end to end through the REAL `Compiler`
// pipeline (adapter -> ISel `Opcode::Invoke`/`LandingPad` -> `eh_info` ->
// `MachFunction.eh_metadata` -> post-layout `resolve_x86_eh_offsets` LSDA),
// linked with the host `c++`, and run on x86-64 Linux GNU (ELF) or x86-64 macOS
// (Mach-O, natively or through Rosetta).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ----------------------------------------------------------------------------
// WHY THIS EXISTS (the x86 analog of `e2e_aarch64_eh_invoke_trust_ir`)
// ----------------------------------------------------------------------------
// `e2e_x86_64_eh_catch` exercises backend EH with a hand-authored
// `X86ISelFunction` and explicit EH metadata. This fixture exercises the
// trust-ir-driven path: a trust-ir `Module` whose function uses
// `Inst::Invoke` (a call that may unwind) + `Inst::LandingPad` (a catch-all
// handler) is compiled by the ordinary `Compiler` (so it flows through the whole
// adapter/ISel/eh-metadata/LSDA pipeline the CLI uses), then the object is
// linked and executed. A clean exit 0 / "returned 42" exercises trust-ir
// Invoke/LandingPad lowering + the x86-64 zPLR unwind tables + LSDA +
// personality indirection at runtime for this fixture; it is not proof of every
// exception path.
//
//   extern "C" int tc_try() {
//     try   { cxx_throw(); return 0; }     // bb0 invoke + bb1 normal
//     catch (...) { return 42; }            // bb2 landing pad (catch-all)
//   }
//
// BOTH object formats are cross-emitted on every host by the compile-only rows;
// only the RUN needs a host, and that row is gated at COMPILE time
// (`common/x86_64_native_host.rs`) so no runtime SKIP can be counted as a pass
// by a floor runner.
//
// The shared supervisor bounds the executable wait without synchronously
// reaping an uninterruptible child. Timeouts fail this fixture but do not
// distinguish an unwinder defect from loader/host failure.

mod common;
#[path = "common/pinned_target.rs"]
mod pinned_target;

use common::x86_64_native_host as host;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Linkage, Module as TrustIrModule, Ty, ValueId,
};

/// Build the trust-ir module: three extern C++/Itanium-runtime declarations plus
/// the `tc_try` function under test (identical to the aarch64 invoke fixture —
/// trust-ir is target-independent; the target is chosen at compile time).
fn build_tc_try_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("eh_invoke_x86");

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

    module
}

/// Compile `module` through the real `Compiler` for an EXPLICIT x86-64 triple.
/// The default spec is host-OS-aware, so every row names its triple: both wired
/// containers cross-emit on every host.
fn compile_to_x86_64_obj_for(triple: &str, module: &TrustIrModule) -> Vec<u8> {
    compile_to_x86_64_obj_at(triple, OptLevel::O0, module)
}

/// Every optimization level the EH lane is exercised at. The invoke's unwind
/// edge, its landing pad and the call-site table all survive the optimizer, or
/// the run at that level loses the catch.
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// [`compile_to_x86_64_obj_for`] at an explicit optimization level.
fn compile_to_x86_64_obj_at(triple: &str, opt_level: OptLevel, module: &TrustIrModule) -> Vec<u8> {
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            target: Target::X86_64,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple)
            .unwrap_or_else(|error| panic!("parse {triple} target spec: {error}")),
    )
    .with_codegen_license(permit_unlicensed());
    // `cxx_throw` is an FFI boundary: the module pins the triple it is
    // compiled for (`TargetInfoRequired`; WS7.3 ingestion admission).
    let module = pinned_target::pinned(module, triple);
    let result = compiler.compile(&module).unwrap_or_else(|error| {
        panic!("tc_try x86-64 compilation for {triple} at {opt_level:?}: {error}")
    });
    assert!(
        !result.object_code.is_empty(),
        "tc_try must produce non-empty object code"
    );
    result.object_code
}

#[test]
fn eh_invoke_trust_ir_x86_compiles_with_lsda() {
    // Compile-only path (runs on every host): exercises the trust-ir
    // Invoke/LandingPad lowering, eh_info -> eh_metadata forwarding, and the
    // post-layout x86 LSDA generation. Object inspection only; no link/run.
    let module = build_tc_try_module();
    let obj = compile_to_x86_64_obj_for("x86_64-apple-darwin", &module);
    host::assert_macho_x86_64_object(&obj);
    assert!(
        host::object_contains(&obj, b"__gcc_except_tab"),
        "object compiled from trust-ir Invoke/LandingPad (x86-64) must carry the \
         LSDA (__gcc_except_tab) section"
    );
    assert!(
        host::object_contains(&obj, b"__eh_frame"),
        "object must carry the __eh_frame section"
    );
}

/// The ELF twin of the row above. This was a product-gap PIN (2026-07-31 x86-Linux
/// battery): x86-64 EH emission existed ONLY for Mach-O, and an ELF target had
/// to fail CLOSED with a typed ISel diagnostic rather than silently emit an
/// object with no unwind tables. The ELF `.eh_frame` / `.gcc_except_table` lane
/// has landed, so the row is flipped to its POSITIVE assertions — including the
/// pieces that have no Mach-O counterpart: the BARE personality name and the
/// `DW.ref.<personality>` slot the zPLR CIE's indirect encoding points at.
#[test]
fn eh_invoke_trust_ir_x86_elf_carries_its_unwind_tables() {
    let module = build_tc_try_module();
    for opt_level in LEVELS {
        let obj = compile_to_x86_64_obj_at("x86_64-unknown-linux-gnu", opt_level, &module);
        host::assert_elf_x86_64_object(&obj);
        assert!(
            host::object_contains(&obj, b".gcc_except_table"),
            "object compiled from trust-ir Invoke/LandingPad (x86-64 ELF) at \
             {opt_level:?} must carry the LSDA (.gcc_except_table) section"
        );
        assert!(
            host::object_contains(&obj, b".eh_frame"),
            "object at {opt_level:?} must carry the .eh_frame section"
        );
        assert!(
            host::object_contains(&obj, b"\x00__gxx_personality_v0\x00"),
            "ELF names the personality BARE, with no container prefix ({opt_level:?})"
        );
        assert!(
            host::object_contains(&obj, b"DW.ref.__gxx_personality_v0"),
            "the zPLR CIE's DW_EH_PE_indirect personality field names a DW.ref \
             slot ({opt_level:?})"
        );
    }
}

// ---------------------------------------------------------------------------
// Native row: link with the host `c++` and observe the catch.
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
fn eh_invoke_trust_ir_x86_link_and_run_catches() {
    for opt_level in LEVELS {
        eh_invoke_trust_ir_x86_link_and_run_catches_at(opt_level);
    }
}

/// The native row at one optimization level. Every level is run: the invoke's
/// unwind edge, its landing pad and the `[0, code_len)` call-site table all have
/// to survive the optimizer, and a level whose pad the optimizer stranded would
/// terminate instead of catching.
#[cfg(any(
    all(target_arch = "x86_64", target_os = "linux", target_env = "gnu"),
    all(target_arch = "x86_64", target_os = "macos"),
))]
fn eh_invoke_trust_ir_x86_link_and_run_catches_at(opt_level: OptLevel) {
    use common::rosetta::run_executable_with_timeout;
    use std::{fs, process::Command, time::Duration};

    let module = build_tc_try_module();
    let obj = compile_to_x86_64_obj_at(host::TRIPLE, opt_level, &module);
    host::assert_native_object(&obj);
    let (lsda_section, cfi_section) = host::eh_section_names();
    assert!(host::object_contains(&obj, lsda_section));
    assert!(host::object_contains(&obj, cfi_section));

    let scratch = tempfile::Builder::new()
        .prefix("trust_cg_x86_eh_invoke_trust_ir_e2e_")
        .tempdir()
        .expect("create owned test directory");
    let dir = scratch.path();
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
    // `c++` pulls in the C++ runtime (the personality, `__cxa_*`, typeinfo):
    // libstdc++/libgcc_s on GNU/Linux, libc++/libc++abi on macOS.
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
        "link failed on {} at {opt_level:?}:\n{}",
        host::HOST,
        String::from_utf8_lossy(&link.stderr)
    );

    let run = run_executable_with_timeout(
        &bin_path,
        common::rosetta::exec_timeout(Duration::from_secs(10)),
    )
    .expect("supervise EH executable");
    let exit_code = run.output.status.code();
    let stdout = String::from_utf8_lossy(&run.output.stdout);
    let stderr = String::from_utf8_lossy(&run.output.stderr);

    assert!(
        !run.timed_out,
        "tc_try timed out at {opt_level:?} without a catch result; this does not \
         distinguish an unwind defect from loader/host failure.\nstdout: \
         {stdout}\nstderr: {stderr}"
    );
    assert_eq!(
        exit_code,
        Some(0),
        "expected a clean catch at {opt_level:?} (exit 0, sentinel 42); inspect \
         the loader and unwind diagnostics.\nexit={exit_code:?}\nstdout: \
         {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("tc_try returned 42"),
        "expected the catch sentinel in stdout at {opt_level:?}.\nstdout: \
         {stdout}\nstderr: {stderr}"
    );

    eprintln!(
        "trust-ir Invoke EH catch e2e (x86-64) PASSED on {} at {opt_level:?}: {}",
        host::HOST,
        stdout.trim()
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
