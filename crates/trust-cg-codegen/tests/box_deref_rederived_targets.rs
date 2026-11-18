// trust-cg-codegen/tests/box_deref_rederived_targets.rs - a re-derived BoxDeref at the opt-in re-derived floor on every target
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! trust-ir v74 `Inst::BoxDeref` whose three conjuncts this backend
//! re-derives from the function itself (`trust_cg_lower::box_deref_rederive`),
//! through the real compile entries, on x86-64, AArch64 (Linux and macOS
//! objects), RISC-V and WASM.
//!
//! What each test is evidence of:
//!
//! * **the default and the proof claim refuse**: at the DEFAULT license the
//!   module is refused on every target, and a proof-emitting compile
//!   (`emit_proofs`, which is also verified promotion) refuses it on every
//!   native target under every license, including the re-derived floor and
//!   the named-premise floor; so do both proof-grade JIT modes on the host.
//!   The refusal is trust-ir's verdict, with no re-derivation consulted.
//! * **acceptance parity**: the same module is admitted on every target at
//!   the opt-in floor (`trust_cg_locally_rederived_v1`), and its one-escape
//!   near miss is refused on every target with the same typed error and the
//!   same text, because one target-independent function decides both.
//! * **lowering**: every target writes an object (WASM: the slot shape only;
//!   the WASM lane has no `HeapAlloc` lowering, which is a capability of that
//!   lane, not an admission difference). Off the target's host this is
//!   "written, compiled, not executed".
//! * **execution**: on an x86-64 Linux host the objects are linked with a C
//!   driver and return the stored value at O0 and O2; WASM runs under node
//!   when node is on `PATH`. AArch64 and RISC-V are not executed here.
//!
//! None of this is proof evidence. The re-derivation is a consumer decision
//! that is never written into the module, and an admitted `BoxDeref` is
//! still lowered as the identity on its pointer.

mod common;

use std::fs;

#[cfg(feature = "verify")]
use std::sync::Arc;

use common::rosetta::{
    codegen_link_timeout, codegen_run_timeout, command_output_with_timeout,
    run_executable_with_timeout, x86_64_cc, x86_64_link_run_or_skip,
};
#[cfg(feature = "verify")]
use trust_cg_codegen::compiler::JitValidationMode;
use trust_cg_codegen::compiler::{CompileError, Compiler, CompilerConfig};
#[cfg(feature = "verify")]
use trust_cg_codegen::core_admission::CoreHostJitTarget;
#[cfg(feature = "verify")]
use trust_cg_codegen::jit_cert::JitCertCache;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_lower::adapter::AdapterError;
use trust_cg_lower::box_deref::BoxDerefRefusal;
use trust_cg_lower::box_deref_rederive::NotRederived;
use trust_cg_lower::{BoxDerefDisclosure, CodegenLicensePolicy, UnlicensedBodyPolicy};
use trust_ir::box_validity::{BoxDerefSite, BoxFactSession, BoxValidityFact, PremiseRoot};
use trust_ir::inst::{AllocOrigin, CastOp, ICmpOp};
use trust_ir::{Endianness, Module, StructPassingPolicy, TargetInfo, Ty};
use trust_ir_build::ModuleBuilder;

const X86_64_LINUX: &str = "x86_64-unknown-linux-gnu";

const NATIVE_TARGETS: [&str; 4] = [
    X86_64_LINUX,
    "aarch64-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "riscv64-unknown-linux-gnu",
];

const SLOT: &str = "tcg_box_slot";
const HEAP: &str = "tcg_box_heap";

fn native_target(triple: &str) -> TargetInfo {
    TargetInfo {
        triple: triple.to_owned(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn fact(ordinal: u32) -> BoxValidityFact {
    BoxValidityFact::premise(
        BoxDerefSite {
            item: [0x71; 16],
            ordinal,
        },
        BoxFactSession::PROOF_SNAPSHOT,
        PremiseRoot::ParamByValue,
    )
}

/// With `slot`, `tcg_box_slot(v: i64) -> i64`: a stack slot holding `v`,
/// dereffed as a box and read back. With `escaping`, the slot's address is first stored
/// into `*q` (a second parameter), an escape before the deref.
/// With `heap`, also `tcg_box_heap(v: i64) -> i64`: a Rust-heap allocation
/// whose null result returns -1, holding `v`, dereffed and read back.
fn module(target: TargetInfo, heap: bool, escaping: bool) -> Module {
    module_of(target, true, heap, escaping)
}

fn module_of(target: TargetInfo, slot: bool, heap: bool, escaping: bool) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("box_deref_rederived_targets", target);
    let slot_params = if escaping {
        vec![Ty::I64, Ty::Ptr]
    } else {
        vec![Ty::I64]
    };
    let slot_ty = mb.add_func_type(slot_params, vec![Ty::I64]);
    if slot {
        let mut fb = mb.function(SLOT, slot_ty);
        let entry = fb.create_block();
        let value = fb.add_block_param(entry, Ty::I64);
        let sink = escaping.then(|| fb.add_block_param(entry, Ty::Ptr));
        fb.switch_to_block(entry);
        let slot = fb.alloca(Ty::I64);
        fb.store(Ty::I64, slot, value);
        if let Some(sink) = sink {
            fb.store(Ty::Ptr, sink, slot);
        }
        let boxed = fb.box_deref(Ty::I64, slot, fact(0));
        let read = fb.load(Ty::I64, boxed);
        fb.ret(vec![read]);
        fb.build();
    }
    if heap {
        let heap_ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function(HEAP, heap_ty);
        let entry = fb.create_block();
        let value = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let raw = fb.heap_alloc(Ty::I64, None, None, AllocOrigin::RustHeap);
        let bits = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::I64, raw);
        let zero = fb.iconst(Ty::I64, 0);
        let failed = fb.icmp(ICmpOp::Eq, Ty::I64, bits, zero);
        let error = fb.create_block();
        let ready = fb.create_block();
        fb.condbr(failed, error, vec![], ready, vec![]);
        fb.switch_to_block(error);
        let minus_one = fb.iconst(Ty::I64, -1);
        fb.ret(vec![minus_one]);
        fb.switch_to_block(ready);
        fb.store(Ty::I64, raw, value);
        let boxed = fb.box_deref(Ty::I64, raw, fact(1));
        let read = fb.load(Ty::I64, boxed);
        fb.ret(vec![read]);
        fb.build();
    }
    mb.build().expect("the fixture builds")
}

/// The default license (claim-less bodies permitted, as these fixtures carry
/// no codegen license; no verdict below is the claim-less refusal).
fn default_license() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit)
}

/// The opt-in consumer-local floor.
fn rederived_license() -> CodegenLicensePolicy {
    default_license().with_locally_rederived_box_floor()
}

fn compile_native(
    module: &Module,
    triple: &str,
    opt_level: OptLevel,
) -> Result<Vec<u8>, Box<CompileError>> {
    compile_native_with(module, triple, opt_level, false, &rederived_license())
        .map(|(object, _)| object)
}

/// The object and the proof certificates' count, or the refusal.
fn compile_native_with(
    module: &Module,
    triple: &str,
    opt_level: OptLevel,
    emit_proofs: bool,
    license: &CodegenLicensePolicy,
) -> Result<(Vec<u8>, Option<usize>), Box<CompileError>> {
    let spec = TargetSpec::parse(triple).unwrap_or_else(|e| panic!("{triple}: {e:?}"));
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            emit_proofs,
            ..CompilerConfig::default()
        },
        spec,
    )
    .with_codegen_license(license.clone())
    .compile(module)
    .map(|result| (result.object_code, result.proofs.as_ref().map(Vec::len)))
    .map_err(Box::new)
}

/// trust-ir's verdict on the fixture's first deref with no re-derivation
/// consulted: the `nonnull` premise, below its `ConsumerRederived` floor.
fn unconsulted_refusal() -> BoxDerefRefusal {
    BoxDerefRefusal::EvidenceBelowFloor {
        conjunct: "nonnull",
        tier: "named_premise",
        floor: "consumer_rederived",
        not_rederived: None,
    }
}

fn assert_unconsulted_refusal(label: &str, error: &CompileError) {
    let CompileError::Adapter(AdapterError::BoxDerefNotAdmitted { reason, .. }) = error else {
        panic!("{label}: refused, but not as a BoxDeref: {error}");
    };
    assert_eq!(*reason, unconsulted_refusal(), "{label}: {error}");
}

#[test]
fn the_default_floor_refuses_a_rederivable_box_deref_on_every_target() {
    for triple in NATIVE_TARGETS {
        for (shape, slot, heap) in [("slot", true, false), ("heap", false, true)] {
            let input = module_of(native_target(triple), slot, heap, false);
            let label = format!("{triple} {shape}");
            match compile_native_with(&input, triple, OptLevel::O0, false, &default_license()) {
                Ok(_) => panic!("{label}: compiled at the default floor"),
                Err(error) => assert_unconsulted_refusal(&label, &error),
            }
        }
    }
    let wasm = module(trust_cg_codegen::wasm::wasm32_target_info(), false, false);
    for (lane, entry) in wasm_entries() {
        let error = entry(&wasm, &default_license()).expect_err(lane);
        assert!(
            error.contains("below this lane's Box validity floor consumer_rederived")
                && !error.contains("re-derive"),
            "{lane}: {error}"
        );
    }
}

/// The review probe's shape (2026-11-15): a proof-emitting compile (which is
/// also the verified-promotion lane) of the wholly re-derivable slot and heap
/// modules, under every license. Before the fix, x86-64 compiled the slot
/// module with proof certificates beside it. Every target must refuse it at
/// the proof-claim gate, with trust-ir's verdict and no re-derivation.
#[test]
fn a_proof_claim_refuses_a_wholly_rederived_box_deref_on_every_native_target() {
    let licenses = [
        ("default", default_license()),
        ("locally_rederived", rederived_license()),
        (
            "named_premise",
            default_license().with_named_premise_box_floor(&BoxDerefDisclosure::new()),
        ),
    ];
    for triple in NATIVE_TARGETS {
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            for (shape, slot, heap) in [("slot", true, false), ("heap", false, true)] {
                let input = module_of(native_target(triple), slot, heap, false);
                for (name, license) in &licenses {
                    let label = format!("{triple} {opt_level:?} {shape} {name} emit_proofs");
                    match compile_native_with(&input, triple, opt_level, true, license) {
                        Ok((object, proofs)) => panic!(
                            "{label}: compiled {} bytes with proofs {proofs:?}",
                            object.len()
                        ),
                        Err(error) => assert_unconsulted_refusal(&label, &error),
                    }
                }
            }
        }
    }
}

/// Both proof-grade JIT modes refuse the wholly re-derivable module under
/// the re-derived floor before translation and before the certificate cache
/// is consulted. Host only (the JIT runs here).
#[cfg(feature = "verify")]
#[test]
fn proof_grade_jit_modes_refuse_a_wholly_rederived_box_deref() {
    let host = CoreHostJitTarget::detect().expect("supported host JIT target");
    let input = module_of(host.trust_ir_target_info().clone(), true, false, false);
    for mode in [
        JitValidationMode::CachedVerified,
        JitValidationMode::AlwaysVerify,
    ] {
        let cache = Arc::new(JitCertCache::new());
        let compiler = Compiler::new_for_target_spec(
            CompilerConfig {
                emit_proofs: false,
                jit_validation_mode_override: Some(mode),
                ..CompilerConfig::for_host_jit()
            },
            host.target_spec(),
        )
        .with_codegen_license(rederived_license())
        .with_jit_cert_cache(cache.clone());
        let error = match compiler.compile_module_to_jit(&input, &Default::default()) {
            Ok(_) => panic!("{mode:?}: proof-grade JIT compiled a re-derived BoxDeref"),
            Err(error) => error,
        };
        assert_unconsulted_refusal(&format!("{mode:?}"), &error);
        assert_eq!(
            cache.stats(),
            (0, 0, 0, 0),
            "{mode:?}: the refusal must precede every certificate-cache action"
        );
    }
}

type WasmEntry = fn(&Module, &CodegenLicensePolicy) -> Result<Vec<u8>, String>;

fn wasm_entries() -> [(&'static str, WasmEntry); 2] {
    [
        ("wasm-module", |module, license| {
            trust_cg_codegen::wasm::compile_module_with_license(module, license)
                .map_err(|e| e.to_string())
        }),
        ("wasm-object", |module, license| {
            trust_cg_codegen::wasm::compile_object_with_license(module, license)
                .map_err(|e| e.to_string())
        }),
    ]
}

/// The RISC-V minimal instruction selector has no stack-slot address
/// (`StackAddr`), so the slot shape stops there, AFTER admission: the error
/// is the selector's, never a Box refusal. The heap shape lowers.
fn riscv_selector_gap(triple: &str, error: &CompileError) -> bool {
    triple.starts_with("riscv64")
        && !matches!(
            error,
            CompileError::Adapter(AdapterError::BoxDerefNotAdmitted { .. })
        )
        && error.to_string().contains("RISC-V minimal ISel")
        && error.to_string().contains("StackAddr")
}

#[test]
fn a_rederived_box_deref_compiles_at_the_rederived_floor_on_every_target() {
    for triple in NATIVE_TARGETS {
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            for (shape, slot, heap) in [("slot", true, false), ("heap", false, true)] {
                let input = module_of(native_target(triple), slot, heap, false);
                match compile_native(&input, triple, opt_level) {
                    Ok(object) => {
                        assert!(!object.is_empty(), "{triple} {opt_level:?} {shape}");
                        eprintln!(
                            "[box_deref_rederived] {triple} {opt_level:?} {shape}: compiled at \
                             the re-derived floor, {} bytes",
                            object.len()
                        );
                    }
                    Err(error) if shape == "slot" && riscv_selector_gap(triple, &error) => {
                        eprintln!(
                            "[box_deref_rederived] {triple} {opt_level:?} {shape}: admitted; \
                             lowering stops at the selector: {error}"
                        );
                    }
                    Err(error) => panic!("{triple} {opt_level:?} {shape}: {error}"),
                }
            }
        }
    }
    let wasm = module(trust_cg_codegen::wasm::wasm32_target_info(), false, false);
    for (lane, entry) in wasm_entries() {
        let bytes =
            entry(&wasm, &rederived_license()).unwrap_or_else(|error| panic!("{lane}: {error}"));
        assert_eq!(&bytes[..4], b"\0asm", "{lane}");
        eprintln!(
            "[box_deref_rederived] {lane}: compiled at the re-derived floor, {} bytes",
            bytes.len()
        );
    }
}

#[test]
fn the_one_escape_near_miss_is_refused_identically_on_every_target() {
    let expected = BoxDerefRefusal::EvidenceBelowFloor {
        conjunct: "dereferenceable",
        tier: "named_premise",
        floor: "consumer_rederived",
        not_rederived: Some(NotRederived::EscapesBeforeDeref.reason()),
    };
    let mut texts = Vec::new();
    for triple in NATIVE_TARGETS {
        let result = compile_native(
            &module(native_target(triple), false, true),
            triple,
            OptLevel::O0,
        );
        let error = match result {
            Ok(_) => panic!("{triple}: compiled; it must be refused"),
            Err(error) => error,
        };
        let CompileError::Adapter(adapter @ AdapterError::BoxDerefNotAdmitted { reason, .. }) =
            error.as_ref()
        else {
            panic!("{triple}: refused, but not as a BoxDeref: {error}");
        };
        assert_eq!(*reason, expected, "{triple}");
        texts.push((triple.to_owned(), adapter.to_string()));
    }
    let wasm = module(trust_cg_codegen::wasm::wasm32_target_info(), false, true);
    for (lane, entry) in wasm_entries() {
        let error = entry(&wasm, &rederived_license()).expect_err(lane);
        texts.push((lane.to_owned(), error));
    }
    let reference = &texts[0].1;
    for (lane, text) in &texts {
        assert!(
            text.contains(reference.as_str()),
            "{lane}: `{text}` does not carry `{reference}`"
        );
    }
}

const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern int64_t tcg_box_slot(int64_t v);
extern int64_t tcg_box_heap(int64_t v);

/* The allocator a lowered `HeapAlloc` (origin RustHeap) calls. */
void *__rust_alloc(size_t size, size_t align) {
    void *p = NULL;
    if (posix_memalign(&p, align < sizeof(void *) ? sizeof(void *) : align, size)) return NULL;
    return p;
}

int main(void) {
    int failures = 0;
    const int64_t values[] = {0, 1, -1, 0x1122334455667788LL, INT64_MIN, INT64_MAX};
    for (unsigned i = 0; i < sizeof values / sizeof values[0]; i++) {
        int64_t slot = tcg_box_slot(values[i]);
        int64_t heap = tcg_box_heap(values[i]);
        if (slot != values[i] || heap != values[i]) {
            printf("MISMATCH value=%lld slot=%lld heap=%lld\n",
                   (long long)values[i], (long long)slot, (long long)heap);
            failures++;
        }
    }
    printf("failures=%d\n", failures);
    return failures ? 1 : 0;
}
"#;

#[test]
fn a_rederived_box_deref_executes_on_x86_64_with_the_right_result() {
    let test = "a_rederived_box_deref_executes_on_x86_64_with_the_right_result";
    let mut objects = Vec::new();
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let object = compile_native(
            &module(native_target(X86_64_LINUX), true, false),
            X86_64_LINUX,
            opt_level,
        )
        .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        objects.push((opt_level, object));
    }
    if !cfg!(all(target_arch = "x86_64", target_os = "linux")) {
        eprintln!("[{test}] not an x86-64 Linux host: compiled, not executed");
        return;
    }
    if !x86_64_link_run_or_skip(test, "x86-64 link/run leg") {
        return;
    }
    let dir = std::env::temp_dir().join(format!("trust_cg_{test}_{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let driver = dir.join("driver.c");
    fs::write(&driver, DRIVER).unwrap();
    for (opt_level, object) in objects {
        let object_path = dir.join(format!("rederived_{opt_level:?}.o"));
        fs::write(&object_path, &object).unwrap();
        let binary = dir.join(format!("rederived_{opt_level:?}"));
        let mut link = x86_64_cc();
        link.arg("-o").arg(&binary).arg(&driver).arg(&object_path);
        let linked = command_output_with_timeout(&mut link, codegen_link_timeout()).unwrap();
        assert!(
            !linked.timed_out && linked.output.status.success(),
            "{opt_level:?}: link failed: {}",
            String::from_utf8_lossy(&linked.output.stderr)
        );
        let run = run_executable_with_timeout(&binary, codegen_run_timeout()).unwrap();
        let stdout = String::from_utf8_lossy(&run.output.stdout).into_owned();
        eprintln!("[{test}] {opt_level:?} EXECUTED:\n{stdout}");
        assert!(
            !run.timed_out && run.output.status.success(),
            "{opt_level:?}: status {:?}:\n{stdout}",
            run.output.status
        );
        assert!(stdout.contains("failures=0"), "{opt_level:?}:\n{stdout}");
    }
    let _ = fs::remove_dir_all(&dir);
}

fn node() -> Option<std::path::PathBuf> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|directory| directory.join("node"))
        .find(|candidate| candidate.is_file())
}

const WASM_DRIVER: &str = r#"
const fs = require('fs');
const m = new WebAssembly.Module(fs.readFileSync(process.argv[2]));
const imports = {};
for (const i of WebAssembly.Module.imports(m)) { imports[i.module] ??= {}; }
const inst = new WebAssembly.Instance(m, imports);
let failures = 0;
for (const value of [0n, 1n, -1n, 0x1122334455667788n, -(2n ** 63n), 2n ** 63n - 1n]) {
  const slot = inst.exports.tcg_box_slot(value);
  if (slot !== value) { console.log(`MISMATCH value=${value} slot=${slot}`); failures++; }
}
console.log(`failures=${failures}`);
process.exit(failures ? 1 : 0);
"#;

#[test]
fn a_rederived_box_deref_executes_in_wasm_under_node_with_the_right_result() {
    let test = "a_rederived_box_deref_executes_in_wasm_under_node_with_the_right_result";
    let wasm = module(trust_cg_codegen::wasm::wasm32_target_info(), false, false);
    let bytes = trust_cg_codegen::wasm::compile_module_with_license(&wasm, &rederived_license())
        .unwrap_or_else(|error| panic!("wasm module: {error}"));
    wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
        .validate_all(&bytes)
        .unwrap_or_else(|error| panic!("the module does not validate: {error}"));
    let Some(node) = node() else {
        eprintln!("[{test}] node not found: wasm32 validated, not executed");
        return;
    };
    let dir = std::env::temp_dir().join(format!("trust_cg_{test}_{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("m.wasm"), &bytes).unwrap();
    fs::write(dir.join("run.js"), WASM_DRIVER).unwrap();
    let out = std::process::Command::new(&node)
        .arg(dir.join("run.js"))
        .arg(dir.join("m.wasm"))
        .output()
        .expect("run node");
    let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
    eprintln!("[{test}] EXECUTED under node:\n{stdout}");
    assert!(
        out.status.success(),
        "node failed: {stdout}{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(stdout.contains("failures=0"), "{stdout}");
    let _ = fs::remove_dir_all(&dir);
}
