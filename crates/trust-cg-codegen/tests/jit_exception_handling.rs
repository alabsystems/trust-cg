// Native AArch64 JIT exception handling through in-memory unwind tables.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The JIT publishes an FDE per function, each EH function's LSDA and a
// personality slot after the code, registers them with the process unwinder
// (per FDE on Darwin libunwind, per section on Linux libgcc) and deregisters
// them before the mapping is unmapped. These tests execute the published code:
//
// * a C++ exception thrown by a C++ callee crosses a JIT cleanup frame (whose
//   destructor call is counted) and is caught by a JIT catch-all frame;
// * the same exception walks through a plain JIT frame with a filler LSDA;
// * a Rust panic resumes through a JIT cleanup frame under the Rust
//   personality and reaches `catch_unwind`;
// * a `panic_unwind` module registers frame-only tables for plain frames.
//
// Fail-closed controls: proof-grade modes refuse by name, an unbound
// personality under an explicit-only policy is refused, profile hooks are
// refused, and teardown deregisters exactly when the mapping is reclaimed.
//
// The C++ helper is compiled with the host `c++` at test time and loaded with
// dlopen. Every test holds one lock: the unwinder readbacks must not race with
// another publication in this process reusing a just-unmapped address.
// This is native execution evidence, not a proof of the unwind tables.

#![cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]

#[path = "common/pinned_target.rs"]
mod pinned_target;

use std::collections::HashMap;
use std::ffi::{CStr, CString, c_char, c_void};
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, MutexGuard, OnceLock};

use trust_cg_codegen::compiler::{CompileError, Compiler, CompilerConfig, JitValidationMode};
use trust_cg_codegen::jit::{JitError, JitExternalSymbolResolutionPolicy, ProfileHookMode};
use trust_cg_codegen::jit_contract::TeardownPolicy;
use trust_cg_codegen::jit_unwind::{
    JitPersonalitySource, JitUnwindManifest, JitUnwindRegistrationScheme,
    registered_unwind_fde_for_pc,
};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Linkage, Module, Ty,
    ValueId,
};

// ---------------------------------------------------------------------------
// Serialization, host helpers and the C++ thrower library
// ---------------------------------------------------------------------------

static SERIAL: Mutex<()> = Mutex::new(());

fn serial() -> MutexGuard<'static, ()> {
    SERIAL
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

unsafe extern "C" {
    fn dlopen(path: *const c_char, mode: i32) -> *mut c_void;
    fn dlsym(handle: *mut c_void, symbol: *const c_char) -> *mut c_void;
    fn dlerror() -> *const c_char;
    /// The Rust runtime's personality routine (the `eh_personality` lang
    /// item); executables do not export it for dlsym, so bind it explicitly.
    fn rust_eh_personality();
}

const RTLD_NOW: i32 = 2;
#[cfg(target_os = "macos")]
const RTLD_GLOBAL: i32 = 0x8;
#[cfg(target_os = "linux")]
const RTLD_GLOBAL: i32 = 0x100;

struct CxxRuntime {
    handle: usize,
}

impl CxxRuntime {
    fn symbol(&self, name: &str) -> *const u8 {
        let name_c = CString::new(name).unwrap();
        // SAFETY: `handle` is a live dlopen handle; the lookup searches the
        // helper library and its dependencies (the C++ runtime).
        let address = unsafe { dlsym(self.handle as *mut c_void, name_c.as_ptr()) };
        assert!(!address.is_null(), "C++ helper does not provide `{name}`");
        address as *const u8
    }
}

/// Compile and load the C++ thrower once per test process. The library is
/// never unloaded, so its code outlives every published JIT buffer.
fn cxx_runtime() -> &'static CxxRuntime {
    static RUNTIME: OnceLock<CxxRuntime> = OnceLock::new();
    RUNTIME.get_or_init(|| {
        // Every test of this process loads the runtime built here.
        let directory: PathBuf = fresh_dir::process_scoped("trust-cg-jit-eh-");
        let source = directory.join("thrower.cpp");
        std::fs::write(
            &source,
            r#"
#include <stdexcept>
extern "C" void cxx_throw() { throw std::runtime_error("thrown by the C++ helper"); }
extern "C" int cxx_no_throw() { return 5; }
"#,
        )
        .expect("write C++ helper");
        let library = directory.join(if cfg!(target_os = "macos") {
            "libthrower.dylib"
        } else {
            "libthrower.so"
        });
        let output = Command::new("c++")
            .args(["-shared", "-fPIC", "-O1"])
            .arg(&source)
            .arg("-o")
            .arg(&library)
            .output()
            .expect("the host c++ compiler is required for the native EH floor");
        assert!(
            output.status.success(),
            "c++ failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let path = CString::new(library.to_str().unwrap()).unwrap();
        // SAFETY: loading a library this test just built; it stays loaded.
        let handle = unsafe { dlopen(path.as_ptr(), RTLD_NOW | RTLD_GLOBAL) };
        if handle.is_null() {
            // SAFETY: dlerror returns a NUL-terminated message after a failure.
            let message = unsafe { CStr::from_ptr(dlerror()) }.to_string_lossy();
            panic!("dlopen {library:?}: {message}");
        }
        CxxRuntime {
            handle: handle as usize,
        }
    })
}

static DROPS: AtomicUsize = AtomicUsize::new(0);

/// The "destructor" a cleanup landing pad runs.
extern "C" fn record_drop() {
    DROPS.fetch_add(1, Ordering::SeqCst);
}

#[derive(Debug, PartialEq, Eq)]
struct JitPanicMarker(u32);

/// A Rust callee that panics without invoking the panic hook.
extern "C-unwind" fn rust_panicker() {
    std::panic::resume_unwind(Box::new(JitPanicMarker(7)));
}

fn address<T>(function: T) -> *const u8
where
    T: Copy,
{
    assert_eq!(std::mem::size_of::<T>(), std::mem::size_of::<*const u8>());
    // SAFETY: `T` is a function-pointer type of pointer size.
    unsafe { std::mem::transmute_copy::<T, *const u8>(&function) }
}

fn compiler(opt_level: OptLevel) -> Compiler {
    Compiler::new(CompilerConfig {
        opt_level,
        parallel: false,
        ..CompilerConfig::for_host_jit_unchecked()
    })
    .with_codegen_license(permit_unlicensed())
}

// ---------------------------------------------------------------------------
// TrustIR modules
// ---------------------------------------------------------------------------

fn b(index: u32) -> BlockId {
    BlockId::new(index)
}

fn f(index: u32) -> FuncId {
    FuncId::new(index)
}

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn declare(module: &mut Module, id: u32, name: &str, params: Vec<Ty>, returns: Vec<Ty>) {
    let signature = module
        .add_func_type(FuncTy {
            params,
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(f(id), name, signature, b(0));
    function.linkage = Linkage::External;
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

fn constant_return(block: u32, value: i128, result: u32) -> Block {
    Block {
        id: b(block),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(value),
            })
            .with_result(v(result)),
            InstrNode::new(Inst::Return {
                values: vec![v(result)],
            }),
        ],
    }
}

/// `invoke callee() to normal unwind cleanup-pad { record_drop(); resume }`.
fn cleanup_function(module: &mut Module, id: u32, name: &str, callee: u32, drop_fn: u32) {
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(f(id), name, signature, b(0));
    function.blocks = vec![
        Block {
            id: b(0),
            params: vec![],
            body: vec![InstrNode::new(Inst::Invoke {
                callee: f(callee),
                args: vec![],
                normal_dest: b(1),
                normal_args: vec![],
                unwind_dest: b(2),
            })],
        },
        constant_return(1, 0, 10),
        Block {
            id: b(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::LandingPad {
                    is_cleanup: true,
                    catch_type_indices: vec![],
                })
                .with_results(vec![v(20), v(21)]),
                InstrNode::new(Inst::Call {
                    callee: f(drop_fn),
                    args: vec![],
                }),
                InstrNode::new(Inst::Resume { exn: v(20) }),
            ],
        },
    ];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

/// `invoke callee() to normal(ret normal_value) unwind catch-all
/// { __cxa_begin_catch; __cxa_end_catch; ret caught_value }`.
#[allow(clippy::too_many_arguments)]
fn catch_all_function(
    module: &mut Module,
    id: u32,
    name: &str,
    callee: u32,
    callee_returns_i32: bool,
    normal_value: i128,
    caught_value: i128,
    begin_catch: u32,
    end_catch: u32,
) {
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(f(id), name, signature, b(0));
    let invoke = InstrNode::new(Inst::Invoke {
        callee: f(callee),
        args: vec![],
        normal_dest: b(1),
        normal_args: vec![],
        unwind_dest: b(2),
    });
    let invoke = if callee_returns_i32 {
        invoke.with_result(v(5))
    } else {
        invoke
    };
    function.blocks = vec![
        Block {
            id: b(0),
            params: vec![],
            body: vec![invoke],
        },
        constant_return(1, normal_value, 10),
        Block {
            id: b(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::LandingPad {
                    is_cleanup: false,
                    catch_type_indices: vec![0],
                })
                .with_results(vec![v(20), v(21)]),
                InstrNode::new(Inst::Call {
                    callee: f(begin_catch),
                    args: vec![v(20)],
                })
                .with_result(v(22)),
                InstrNode::new(Inst::Call {
                    callee: f(end_catch),
                    args: vec![],
                }),
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(caught_value),
                })
                .with_result(v(23)),
                InstrNode::new(Inst::Return {
                    values: vec![v(23)],
                }),
            ],
        },
    ];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

/// A plain (non-EH) frame: `call callee(); ret 0`.
fn plain_call_function(module: &mut Module, id: u32, name: &str, callee: u32) {
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(f(id), name, signature, b(0));
    let mut entry = constant_return(0, 0, 10);
    entry.body.insert(
        0,
        InstrNode::new(Inst::Call {
            callee: f(callee),
            args: vec![],
        }),
    );
    function.blocks = vec![entry];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

const CXX_FUNCTIONS: [&str; 5] = [
    "inner_cleanup",
    "outer_catch",
    "passthrough",
    "outer_passthrough",
    "outer_no_throw",
];

/// C++ exception module (personality `__gxx_personality_v0`).
fn cxx_module() -> Module {
    let mut module = Module::new("jit_cxx_exceptions");
    pinned_target::pin(&mut module, pinned_target::host_triple());
    declare(&mut module, 0, "cxx_throw", vec![], vec![]);
    declare(&mut module, 1, "record_drop", vec![], vec![]);
    declare(
        &mut module,
        2,
        "__cxa_begin_catch",
        vec![Ty::Ptr],
        vec![Ty::Ptr],
    );
    declare(&mut module, 3, "__cxa_end_catch", vec![], vec![]);
    declare(&mut module, 4, "cxx_no_throw", vec![], vec![Ty::I32]);
    cleanup_function(&mut module, 5, CXX_FUNCTIONS[0], 0, 1);
    catch_all_function(&mut module, 6, CXX_FUNCTIONS[1], 5, true, 1, 42, 2, 3);
    plain_call_function(&mut module, 7, CXX_FUNCTIONS[2], 0);
    catch_all_function(&mut module, 8, CXX_FUNCTIONS[3], 7, true, 1, 43, 2, 3);
    catch_all_function(&mut module, 9, CXX_FUNCTIONS[4], 4, true, 7, 44, 2, 3);
    module
}

fn cxx_externs(runtime: &CxxRuntime, include_runtime: bool) -> HashMap<String, *const u8> {
    let mut externs = HashMap::from([
        ("cxx_throw".to_owned(), runtime.symbol("cxx_throw")),
        ("cxx_no_throw".to_owned(), runtime.symbol("cxx_no_throw")),
        (
            "record_drop".to_owned(),
            address(record_drop as extern "C" fn()),
        ),
    ]);
    if include_runtime {
        for name in [
            "__cxa_begin_catch",
            "__cxa_end_catch",
            "__gxx_personality_v0",
            "_Unwind_Resume",
        ] {
            externs.insert(name.to_owned(), runtime.symbol(name));
        }
    }
    externs
}

/// Rust panic module: declaring `rust_eh_personality` selects the Rust
/// personality for the module's EH functions.
fn rust_module() -> Module {
    let mut module = Module::new("jit_rust_panic");
    pinned_target::pin(&mut module, pinned_target::host_triple());
    declare(&mut module, 0, "rust_panicker", vec![], vec![]);
    declare(&mut module, 1, "record_drop", vec![], vec![]);
    declare(&mut module, 2, "rust_eh_personality", vec![], vec![]);
    cleanup_function(&mut module, 3, "rust_cleanup", 0, 1);
    module
}

fn rust_externs() -> HashMap<String, *const u8> {
    HashMap::from([
        (
            "rust_panicker".to_owned(),
            address(rust_panicker as extern "C-unwind" fn()),
        ),
        (
            "record_drop".to_owned(),
            address(record_drop as extern "C" fn()),
        ),
        (
            "rust_eh_personality".to_owned(),
            address(rust_eh_personality as unsafe extern "C" fn()),
        ),
    ])
}

// ---------------------------------------------------------------------------
// Helpers over the published buffer
// ---------------------------------------------------------------------------

type EntryFn = extern "C-unwind" fn() -> i32;

fn entry(result: &trust_cg_codegen::compiler::JitCompilationResult, name: &str) -> EntryFn {
    // SAFETY: every module function has the C signature `() -> i32`; the
    // caller keeps `result` alive across every call. "C-unwind" admits the
    // exceptions and panics these tests send through the JIT frames.
    unsafe {
        result
            .buffer
            .get_fn_bound::<EntryFn>(name)
            .unwrap_or_else(|| panic!("missing JIT symbol {name}"))
            .into_inner()
    }
}

/// Check the manifest against the live unwinder: every function's entry PC
/// maps to exactly the FDE the manifest records.
fn assert_registered(
    result: &trust_cg_codegen::compiler::JitCompilationResult,
) -> JitUnwindManifest {
    let manifest = result
        .buffer
        .unwind_tables()
        .expect("EH module must publish unwind tables")
        .clone();
    assert!(result.buffer.unwind_tables_registered());
    let expected_scheme = if cfg!(target_os = "macos") {
        JitUnwindRegistrationScheme::PerFde
    } else {
        JitUnwindRegistrationScheme::WholeSection
    };
    assert_eq!(manifest.registration_scheme, expected_scheme);
    let base = result.buffer.code_slice().as_ptr() as u64;
    assert!(
        manifest.eh_frame_offset >= result.buffer.code_len() as u64,
        "tables live after the code"
    );
    for record in &manifest.functions {
        assert_eq!(
            registered_unwind_fde_for_pc(base + record.code_offset).unwrap(),
            Some(base + record.fde_offset),
            "{}",
            record.function
        );
    }
    manifest
}

// ---------------------------------------------------------------------------
// Positive native controls
// ---------------------------------------------------------------------------

#[test]
fn cxx_exception_crosses_jit_cleanup_and_is_caught_by_jit_catch_all() {
    let _guard = serial();
    let runtime = cxx_runtime();
    let module = cxx_module();
    let mut calls = 0usize;
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let result = compiler(opt_level)
            .compile_module_to_jit(&module, &cxx_externs(runtime, true))
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        let manifest = assert_registered(&result);
        let personality = manifest.personality.as_ref().expect("C++ personality");
        assert_eq!(personality.symbol, "__gxx_personality_v0");
        assert_eq!(personality.source, JitPersonalitySource::ExplicitBinding);
        assert_eq!(
            personality.address,
            runtime.symbol("__gxx_personality_v0") as u64
        );
        for name in CXX_FUNCTIONS {
            let record = manifest.function(name).expect("every function has an FDE");
            assert!(record.frame_pointer, "{name} calls, so it has a frame");
            assert_eq!(
                record.lsda_is_filler,
                name == "passthrough",
                "{opt_level:?}: only the plain frame gets the filler LSDA"
            );
        }
        let outer_catch = entry(&result, "outer_catch");
        let before = DROPS.load(Ordering::SeqCst);
        for _ in 0..64 {
            assert_eq!(outer_catch(), 42, "{opt_level:?}: catch-all must claim it");
            calls += 1;
        }
        assert_eq!(
            DROPS.load(Ordering::SeqCst) - before,
            64,
            "{opt_level:?}: the cleanup pad must run exactly once per throw"
        );
    }
    println!("JIT_EH_CXX_CLEANUP_CATCH calls={calls} opt_levels=4");
}

#[test]
fn cxx_exception_walks_through_a_plain_jit_frame() {
    let _guard = serial();
    let runtime = cxx_runtime();
    let result = compiler(OptLevel::O2)
        .compile_module_to_jit(&cxx_module(), &cxx_externs(runtime, true))
        .unwrap();
    assert_registered(&result);
    let outer = entry(&result, "outer_passthrough");
    let before = DROPS.load(Ordering::SeqCst);
    for _ in 0..32 {
        assert_eq!(outer(), 43);
    }
    assert_eq!(
        DROPS.load(Ordering::SeqCst),
        before,
        "no cleanup lies on this path"
    );
}

#[test]
fn invoke_normal_path_runs_no_landing_pad() {
    let _guard = serial();
    let runtime = cxx_runtime();
    let result = compiler(OptLevel::O1)
        .compile_module_to_jit(&cxx_module(), &cxx_externs(runtime, true))
        .unwrap();
    let no_throw = entry(&result, "outer_no_throw");
    let before = DROPS.load(Ordering::SeqCst);
    for _ in 0..32 {
        assert_eq!(no_throw(), 7, "the normal successor must return");
    }
    assert_eq!(DROPS.load(Ordering::SeqCst), before);
}

#[test]
fn process_lookup_binds_the_cxx_runtime_when_policy_permits() {
    let _guard = serial();
    let runtime = cxx_runtime();
    let result = compiler(OptLevel::O0)
        .compile_module_to_jit(&cxx_module(), &cxx_externs(runtime, false))
        .unwrap();
    let manifest = assert_registered(&result);
    let personality = manifest.personality.as_ref().unwrap();
    assert_eq!(personality.source, JitPersonalitySource::ProcessLookup);
    assert_ne!(personality.address, 0);
    assert_eq!(entry(&result, "outer_catch")(), 42);
}

#[test]
fn rust_panic_resumes_through_jit_cleanup_to_catch_unwind() {
    let _guard = serial();
    let mut caught = 0usize;
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let result = compiler(opt_level)
            .compile_module_to_jit(&rust_module(), &rust_externs())
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        let manifest = assert_registered(&result);
        let personality = manifest.personality.as_ref().unwrap();
        assert_eq!(personality.symbol, "rust_eh_personality");
        assert_eq!(personality.source, JitPersonalitySource::ExplicitBinding);
        let cleanup = entry(&result, "rust_cleanup");
        let before = DROPS.load(Ordering::SeqCst);
        for _ in 0..32 {
            let payload = std::panic::catch_unwind(|| cleanup())
                .expect_err("the panic must resume past the JIT frame");
            assert_eq!(
                payload.downcast_ref::<JitPanicMarker>(),
                Some(&JitPanicMarker(7)),
                "{opt_level:?}: the original payload must arrive"
            );
            caught += 1;
        }
        assert_eq!(
            DROPS.load(Ordering::SeqCst) - before,
            32,
            "{opt_level:?}: the Rust personality must run the cleanup pad"
        );
    }
    println!("JIT_EH_RUST_RESUME caught={caught}");
}

#[test]
fn panic_unwind_registers_frame_only_tables_for_plain_frames() {
    let _guard = serial();
    let mut module = Module::new("jit_panic_unwind_walk");
    pinned_target::pin(&mut module, pinned_target::host_triple());
    declare(&mut module, 0, "rust_panicker", vec![], vec![]);
    plain_call_function(&mut module, 1, "walk_frame", 0);
    let externs = HashMap::from([(
        "rust_panicker".to_owned(),
        address(rust_panicker as extern "C-unwind" fn()),
    )]);
    let result = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O1,
        parallel: false,
        panic_unwind: true,
        ..CompilerConfig::for_host_jit_unchecked()
    })
    .with_codegen_license(permit_unlicensed())
    .compile_module_to_jit(&module, &externs)
    .unwrap();
    let manifest = assert_registered(&result);
    assert!(manifest.personality.is_none());
    assert!(!manifest.carries_exception_handling());
    assert!(
        manifest
            .functions
            .iter()
            .all(|record| record.lsda_offset.is_none())
    );
    let walk = entry(&result, "walk_frame");
    let payload = std::panic::catch_unwind(|| walk()).expect_err("panic walks through");
    assert_eq!(
        payload.downcast_ref::<JitPanicMarker>(),
        Some(&JitPanicMarker(7))
    );
    // Without `panic_unwind` a plain module publishes no tables at all.
    let plain = compiler(OptLevel::O1)
        .compile_module_to_jit(&module, &externs)
        .unwrap();
    assert!(plain.buffer.unwind_tables().is_none());
    assert!(!plain.buffer.unwind_tables_registered());
}

#[test]
fn exceptions_cross_jit_frames_on_other_threads() {
    let _guard = serial();
    let runtime = cxx_runtime();
    let result = compiler(OptLevel::O2)
        .compile_module_to_jit(&cxx_module(), &cxx_externs(runtime, true))
        .unwrap();
    assert_registered(&result);
    let before = DROPS.load(Ordering::SeqCst);
    let threads: Vec<_> = (0..4)
        .map(|_| {
            let leased = result.buffer.leased_symbol_ptr("outer_catch").unwrap();
            std::thread::spawn(move || {
                leased.prepare_current_thread();
                // SAFETY: the lease keeps the code and its registered tables
                // mapped; the signature is `() -> i32`.
                let outer: EntryFn = unsafe { std::mem::transmute(leased.as_ptr()) };
                (0..64).filter(|_| outer() == 42).count()
            })
        })
        .collect();
    let caught: usize = threads
        .into_iter()
        .map(|thread| thread.join().unwrap())
        .sum();
    assert_eq!(caught, 256);
    assert_eq!(DROPS.load(Ordering::SeqCst) - before, 256);
    println!("JIT_EH_CROSS_THREAD threads=4 caught={caught}");
}

// ---------------------------------------------------------------------------
// Teardown
// ---------------------------------------------------------------------------

#[test]
fn teardown_deregisters_only_when_the_mapping_is_reclaimed() {
    let _guard = serial();
    let runtime = cxx_runtime();
    let result = compiler(OptLevel::O0)
        .compile_module_to_jit(&cxx_module(), &cxx_externs(runtime, true))
        .unwrap();
    let manifest = assert_registered(&result);
    let base = result.buffer.code_slice().as_ptr() as u64;
    let record = manifest.function("outer_catch").unwrap().clone();
    let pc = base + record.code_offset;
    let leased = result.buffer.leased_symbol_ptr("outer_catch").unwrap();
    let probe = result.buffer.reclamation_probe();
    drop(result);
    // Retired, still leased: the tables stay registered and usable.
    assert_eq!(
        registered_unwind_fde_for_pc(pc).unwrap(),
        Some(base + record.fde_offset)
    );
    leased.prepare_current_thread();
    // SAFETY: the lease keeps the mapping and its tables alive.
    let outer: EntryFn = unsafe { std::mem::transmute(leased.as_ptr()) };
    assert_eq!(outer(), 42);
    drop(leased);
    assert_eq!(
        probe.state(),
        trust_cg_codegen::jit::JitReclamationState::Reclaimed
    );
    assert_eq!(
        registered_unwind_fde_for_pc(pc).unwrap(),
        None,
        "reclamation must deregister before unmapping"
    );

    // Process lifetime: the mapping and its registration are retained.
    let mut retained = compiler(OptLevel::O0)
        .compile_module_to_jit(&cxx_module(), &cxx_externs(runtime, true))
        .unwrap();
    retained
        .buffer
        .set_teardown_policy(TeardownPolicy::ProcessLifetime)
        .unwrap();
    let manifest = assert_registered(&retained);
    let base = retained.buffer.code_slice().as_ptr() as u64;
    let record = manifest.function("outer_catch").unwrap().clone();
    let raw = retained
        .buffer
        .get_fn_ptr_bound("outer_catch")
        .unwrap()
        .as_ptr() as usize;
    drop(retained);
    assert_eq!(
        registered_unwind_fde_for_pc(base + record.code_offset).unwrap(),
        Some(base + record.fde_offset)
    );
    // SAFETY: the process-lifetime policy keeps this code and its tables.
    let outer: EntryFn = unsafe { std::mem::transmute(raw) };
    trust_cg_codegen::jit::ensure_jit_execute_mode();
    assert_eq!(outer(), 42);
}

// ---------------------------------------------------------------------------
// Fail-closed controls
// ---------------------------------------------------------------------------

fn assert_proof_refusal(
    result: Result<trust_cg_codegen::compiler::JitCompilationResult, CompileError>,
    expected: &str,
) {
    match result {
        Err(CompileError::Jit(JitError::JitUnwindProofEvidenceUnavailable { function })) => {
            assert_eq!(function, expected);
        }
        Err(other) => panic!("expected the named proof refusal, got {other}"),
        Ok(_) => panic!("proof-grade EH publication must be refused"),
    }
}

#[test]
fn proof_grade_modes_refuse_exception_handling_by_name() {
    let _guard = serial();
    let runtime = cxx_runtime();
    let externs = cxx_externs(runtime, true);
    for mode in [
        JitValidationMode::AlwaysVerify,
        JitValidationMode::CachedVerified,
    ] {
        let result = Compiler::new(CompilerConfig {
            opt_level: OptLevel::O0,
            parallel: false,
            jit_validation_mode_override: Some(mode),
            ..CompilerConfig::for_host_jit()
        })
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(&cxx_module(), &externs);
        assert_proof_refusal(result, "inner_cleanup");
    }
    let result = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        parallel: false,
        emit_proofs: true,
        ..CompilerConfig::for_host_jit()
    })
    .with_codegen_license(permit_unlicensed())
    .compile_module_to_jit(&cxx_module(), &externs);
    assert_proof_refusal(result, "inner_cleanup");

    // panic_unwind frames are refused on proof-grade paths as well.
    let mut plain = Module::new("proof_grade_walk");
    pinned_target::pin(&mut plain, pinned_target::host_triple());
    declare(&mut plain, 0, "rust_panicker", vec![], vec![]);
    plain_call_function(&mut plain, 1, "walk_frame", 0);
    let result = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        parallel: false,
        panic_unwind: true,
        jit_validation_mode_override: Some(JitValidationMode::AlwaysVerify),
        ..CompilerConfig::for_host_jit()
    })
    .with_codegen_license(permit_unlicensed())
    .compile_module_to_jit(&plain, &HashMap::new());
    // No function carries EH here, so the refusal names the first defined one.
    assert_proof_refusal(result, "walk_frame");
}

#[test]
fn explicit_only_policy_refuses_an_unbound_personality() {
    let _guard = serial();
    let runtime = cxx_runtime();
    let mut externs = cxx_externs(runtime, true);
    externs.remove("__gxx_personality_v0");
    let result = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        parallel: false,
        jit_external_symbol_resolution: JitExternalSymbolResolutionPolicy::ExplicitOnly,
        ..CompilerConfig::for_host_jit_unchecked()
    })
    .with_codegen_license(permit_unlicensed())
    .compile_module_to_jit(&cxx_module(), &externs);
    match result {
        Err(CompileError::Jit(JitError::JitUnwindPersonalityUnresolved { personality })) => {
            assert_eq!(personality, "__gxx_personality_v0");
        }
        Err(other) => panic!("expected the named personality refusal, got {other}"),
        Ok(_) => panic!("an unbound personality must never publish"),
    }
    // With the binding the same policy publishes.
    let result = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        parallel: false,
        jit_external_symbol_resolution: JitExternalSymbolResolutionPolicy::ExplicitOnly,
        ..CompilerConfig::for_host_jit_unchecked()
    })
    .with_codegen_license(permit_unlicensed())
    .compile_module_to_jit(&cxx_module(), &cxx_externs(runtime, true))
    .unwrap();
    assert_eq!(entry(&result, "outer_catch")(), 42);
}

#[test]
fn profile_hooks_refuse_exception_handling() {
    let _guard = serial();
    let runtime = cxx_runtime();
    let result = compiler(OptLevel::O0).compile_module_to_jit_with_profile_hooks(
        &cxx_module(),
        &cxx_externs(runtime, true),
        ProfileHookMode::CallCounts,
    );
    assert!(
        matches!(
            result,
            Err(CompileError::Jit(
                JitError::JitUnwindProfileHooksUnsupported {
                    mode: ProfileHookMode::CallCounts,
                    ..
                }
            ))
        ),
        "{:?}",
        result.err()
    );
}

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
