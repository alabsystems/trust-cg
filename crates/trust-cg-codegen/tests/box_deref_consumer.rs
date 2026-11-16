// trust-cg-codegen/tests/box_deref_consumer.rs - trust-ir Inst::BoxDeref on every target
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! trust-ir v74 `Inst::BoxDeref` through this backend's real entry points, on
//! x86-64, AArch64, RISC-V and WASM.
//!
//! What each test is evidence of:
//!
//! * **refusal parity** (every target, host-independent): the default
//!   license refuses a module holding a `BoxDeref`; the named-premise license
//!   refuses an assumed root, a reserved evidence kind and a fact a trust-ir
//!   rule rejects; a proof-emitting compile refuses whatever the license
//!   says. Each refusal is the SAME typed error
//!   (`AdapterError::BoxDerefNotAdmitted`) with the same text on every
//!   target, because one function decides it
//!   (`trust_cg_lower::admit_box_derefs`). These are the host-independent
//!   twins of the bridge's macOS/AArch64-only `[TCG-BOX-DEREF]` refusal test:
//!   they need no rustc and no particular host.
//! * **lowering** (every target): under the named-premise license the module
//!   compiles to an object. On a host that is not the target this is
//!   "written, compiled, not executed".
//! * **execution**: the object returns the pointee, at O0 and O2, and a null
//!   check AFTER the deref is still executed. The second leg is the
//!   no-licence clause as a run: code that removed the check on the strength
//!   of the fact would read through a null pointer. x86-64 Linux runs on an
//!   x86-64 Linux host; AArch64 runs only on an AArch64 host; WASM runs under
//!   node when node is present. RISC-V has no execution leg.
//!
//! None of this is proof evidence. An admitted `BoxDeref` is compiled under a
//! named assumption, and these are tests of the consumer.

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
use trust_cg_lower::{BoxDerefDisclosure, CodegenLicensePolicy, UnlicensedBodyPolicy};
use trust_ir::box_validity::{
    BoxDerefSite, BoxFactSession, BoxValidityFact, PremiseRoot, ValidityConjunct, ValidityEvidence,
};
use trust_ir::inst::{AllocOrigin, ICmpOp};
use trust_ir::{Endianness, Module, StructPassingPolicy, TargetInfo, Ty};
use trust_ir_build::ModuleBuilder;

const X86_64_LINUX: &str = "x86_64-unknown-linux-gnu";

/// The native targets, by triple. Every one has 8-byte pointers.
const NATIVE_TARGETS: [&str; 4] = [
    X86_64_LINUX,
    "aarch64-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "riscv64-unknown-linux-gnu",
];

const READ: &str = "tcg_box_read";
const CHECKED: &str = "tcg_box_checked";
const IDENTITY: &str = "tcg_box_identity";

fn native_target(triple: &str) -> TargetInfo {
    TargetInfo {
        triple: triple.to_owned(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn fact(root: PremiseRoot) -> BoxValidityFact {
    BoxValidityFact::premise(
        BoxDerefSite {
            item: [0x5a; 16],
            ordinal: 0,
        },
        BoxFactSession::PROOF_SNAPSHOT,
        root,
    )
}

/// Two functions over `fact`:
///
/// * `tcg_box_read(p: ptr) -> i64`: the deref of the parameter, then a load
///   through the result;
/// * `tcg_box_checked(p: ptr) -> i64`: the deref, then a null check of the
///   RESULT, returning -1 on null and the load otherwise.
fn module(target: TargetInfo, fact: &BoxValidityFact) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("box_deref_consumer", target);
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
    {
        let mut fb = mb.function(READ, ft);
        let entry = fb.create_block();
        let pointer = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        let boxed = fb.box_deref(Ty::I64, pointer, fact.clone());
        let read = fb.load(Ty::I64, boxed);
        fb.ret(vec![read]);
        fb.build();
    }
    {
        let mut fb = mb.function(CHECKED, ft);
        let entry = fb.create_block();
        let is_null = fb.create_block();
        let not_null = fb.create_block();
        let pointer = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        let boxed = fb.box_deref(Ty::I64, pointer, fact.clone());
        let null = fb.null_ptr();
        let cond = fb.icmp(ICmpOp::Eq, Ty::Ptr, boxed, null);
        fb.condbr(cond, is_null, vec![], not_null, vec![]);
        fb.switch_to_block(is_null);
        let minus_one = fb.iconst(Ty::I64, -1);
        fb.ret(vec![minus_one]);
        fb.switch_to_block(not_null);
        let read = fb.load(Ty::I64, boxed);
        fb.ret(vec![read]);
        fb.build();
    }
    mb.build().expect("the module builds")
}

/// The smallest Box consumer: the returned pointer is exactly the admitted
/// operand. It lets the wasm control distinguish the Box operation itself
/// from the explicit loads in [`module`].
fn identity_module(target: TargetInfo, fact: &BoxValidityFact) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("box_deref_identity", target);
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Ptr]);
    let mut fb = mb.function(IDENTITY, ft);
    let entry = fb.create_block();
    let pointer = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    let boxed = fb.box_deref(Ty::I64, pointer, fact.clone());
    fb.ret(vec![boxed]);
    fb.build();
    mb.build().expect("the Box identity module builds")
}

/// A consumer fixture whose premise has the concrete anchor its name claims:
/// an in-body `HeapAlloc` for `alloc_postcondition`, or a direct call result
/// for `returned_box_discharged`. These are not parameter fixtures relabelled
/// with another root; TrustIR rule 9 validates each real shape.
fn rooted_module(target: TargetInfo, root: PremiseRoot) -> Module {
    assert!(matches!(
        root,
        PremiseRoot::AllocPostcondition | PremiseRoot::ReturnedBoxDischarged
    ));
    let mut mb = ModuleBuilder::new_with_target_info("box_deref_rooted_consumer", target);
    let make_ty = mb.add_func_type(vec![], vec![Ty::Ptr]);
    let make = {
        let mut fb = mb.function("make_box_storage", make_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let raw = fb.heap_alloc(Ty::I64, None, None, AllocOrigin::RustHeap);
        fb.ret(vec![raw]);
        fb.build()
    };
    let consume_ty = mb.add_func_type(vec![], vec![Ty::Ptr]);
    let mut fb = mb.function("consume_rooted_box", consume_ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let returned = fb.call(make, vec![]);
    let allocated = fb.heap_alloc(Ty::I64, None, None, AllocOrigin::RustHeap);
    let operand = match root {
        PremiseRoot::AllocPostcondition => allocated,
        PremiseRoot::ReturnedBoxDischarged => returned,
        _ => unreachable!(),
    };
    let boxed = fb.box_deref(Ty::I64, operand, fact(root));
    fb.ret(vec![boxed]);
    fb.build();
    mb.build().expect("the rooted Box consumer builds")
}

/// The fixtures carry no codegen license (`body_gate` absent), which this
/// backend refuses by default; every compile here states `Permit`, so no
/// verdict below is the claim-less refusal.
fn refusing_license() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit)
}

/// The diagnostic lane's opt-in: trust-ir's `NamedPremise` floor, reporting
/// to a report the caller does not read (the refusal rows admit nothing).
fn named_premise_license() -> CodegenLicensePolicy {
    named_premise_license_reporting_to(&BoxDerefDisclosure::new())
}

/// The opt-in, reporting every admission to `disclosure`: the only way the
/// named-premise floor can be selected.
fn named_premise_license_reporting_to(disclosure: &BoxDerefDisclosure) -> CodegenLicensePolicy {
    refusing_license().with_named_premise_box_floor(disclosure)
}

/// The report of exactly one compile of the two-function fixture under a
/// named assumption: one module, one row per `BoxDeref`, each naming
/// `param_by_value`, and a line that says "assumed", in no proof vocabulary.
fn assert_reported(label: &str, disclosure: &BoxDerefDisclosure) {
    let records = disclosure.records();
    assert_eq!(records.len(), 1, "{label}: {records:?}");
    let rows = &records[0].manifest.rows;
    assert_eq!(rows.len(), 2, "{label}: one row per BoxDeref: {rows:?}");
    assert!(
        rows.iter().all(|row| row.root == PremiseRoot::ParamByValue),
        "{label}: {rows:?}"
    );
    let lines = disclosure.lines();
    assert_eq!(lines.len(), 1, "{label}: {lines:?}");
    assert!(
        lines[0].contains("admitted for compilation under named assumptions")
            && lines[0].contains("assumed for admission, not established")
            && lines[0].contains("param_by_value x2"),
        "{label}: {}",
        lines[0]
    );
}

fn compile_native(
    module: &Module,
    triple: &str,
    opt_level: OptLevel,
    emit_proofs: bool,
    license: &CodegenLicensePolicy,
) -> Result<Vec<u8>, Box<CompileError>> {
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
    .map(|result| result.object_code)
    .map_err(Box::new)
}

/// The typed refusal a native compile returned, or a panic naming what it
/// returned instead.
fn box_refusal(
    label: &str,
    result: Result<Vec<u8>, Box<CompileError>>,
) -> (String, BoxDerefRefusal) {
    match result {
        Ok(_) => panic!("{label}: compiled; it must be refused"),
        Err(error) => match error.as_ref() {
            CompileError::Adapter(error) => match error {
                AdapterError::BoxDerefNotAdmitted { reason, .. } => {
                    (error.to_string(), reason.clone())
                }
                other => panic!("{label}: refused, but not as a BoxDeref: {other}"),
            },
            other => panic!("{label}: refused outside the adapter: {other}"),
        },
    }
}

/// Every wasm entry over the module retargeted to wasm32: the closed module
/// and the relocatable object.
fn compile_wasm(
    fact: &BoxValidityFact,
    license: &CodegenLicensePolicy,
) -> [(&'static str, Result<Vec<u8>, String>); 2] {
    let module = module(trust_cg_codegen::wasm::wasm32_target_info(), fact);
    [
        (
            "wasm-module",
            trust_cg_codegen::wasm::compile_module_with_license(&module, license)
                .map_err(|e| e.to_string()),
        ),
        (
            "wasm-object",
            trust_cg_codegen::wasm::compile_object_with_license(&module, license)
                .map_err(|e| e.to_string()),
        ),
    ]
}

/// One refusal row: the fact, the license, the reason expected, and a
/// fragment the message must contain.
struct RefusalRow {
    name: &'static str,
    fact: BoxValidityFact,
    license: CodegenLicensePolicy,
    emit_proofs: bool,
    expect: fn(&BoxDerefRefusal) -> bool,
    fragment: &'static str,
}

fn refusal_rows() -> Vec<RefusalRow> {
    let below =
        |tier: &'static str, floor: &'static str| -> (fn(&BoxDerefRefusal) -> bool, &'static str) {
            let _ = (tier, floor);
            (
                |reason| matches!(reason, BoxDerefRefusal::EvidenceBelowFloor { .. }),
                "below this lane's Box validity floor",
            )
        };
    let mut reserved = fact(PremiseRoot::ParamByValue);
    reserved.evidence[0].evidence = ValidityEvidence::DominatingCheck { align: None };
    let mut uncovered = fact(PremiseRoot::ParamByValue);
    uncovered
        .evidence
        .retain(|entry| entry.conjunct != ValidityConjunct::Dereferenceable);
    let mut unpinned = fact(PremiseRoot::ParamByValue);
    unpinned.not_claimed.pop();
    vec![
        RefusalRow {
            name: "default license refuses a named premise",
            fact: fact(PremiseRoot::ParamByValue),
            license: refusing_license(),
            emit_proofs: false,
            expect: below("named_premise", "consumer_rederived").0,
            fragment: "backed at tier named_premise, below this lane's Box validity floor \
                       consumer_rederived",
        },
        RefusalRow {
            name: "named-premise license refuses an assumed root",
            fact: fact(PremiseRoot::ReferenceArgBoxValid),
            license: named_premise_license(),
            emit_proofs: false,
            expect: below("assumed_root_premise", "named_premise").0,
            fragment: "backed at tier assumed_root_premise, below this lane's Box validity floor \
                       named_premise",
        },
        RefusalRow {
            name: "named-premise license refuses a reserved evidence kind",
            fact: reserved,
            license: named_premise_license(),
            emit_proofs: false,
            expect: |reason| {
                matches!(
                    reason,
                    BoxDerefRefusal::FactRefused {
                        rule: "BoxDerefDominatingCheckInvalid",
                        ..
                    }
                )
            },
            fragment: "trust-ir refuses its validity fact (BoxDerefDominatingCheckInvalid)",
        },
        RefusalRow {
            name: "named-premise license refuses a fact with a conjunct stripped",
            fact: uncovered,
            license: named_premise_license(),
            emit_proofs: false,
            expect: |reason| {
                matches!(
                    reason,
                    BoxDerefRefusal::FactRefused {
                        rule: "BoxDerefConjunctCover",
                        ..
                    }
                )
            },
            fragment: "trust-ir refuses its validity fact (BoxDerefConjunctCover)",
        },
        RefusalRow {
            name: "named-premise license refuses a fact with a non-claim dropped",
            fact: unpinned,
            license: named_premise_license(),
            emit_proofs: false,
            expect: |reason| {
                matches!(
                    reason,
                    BoxDerefRefusal::FactRefused {
                        rule: "BoxDerefNonClaimsNotPinned",
                        ..
                    }
                )
            },
            fragment: "trust-ir refuses its validity fact (BoxDerefNonClaimsNotPinned)",
        },
        RefusalRow {
            name: "a proof-emitting compile refuses under the named-premise license",
            fact: fact(PremiseRoot::ParamByValue),
            license: named_premise_license(),
            emit_proofs: true,
            expect: below("named_premise", "consumer_rederived").0,
            fragment: "backed at tier named_premise, below this lane's Box validity floor \
                       consumer_rederived",
        },
    ]
}

/// Every refusal is the same typed error, with the same text, on all four
/// targets and on both wasm entries. The control (the same module under the
/// named-premise license, no proofs) compiles on each, so no refusal here is
/// the target's or the fixture's.
#[test]
fn a_box_deref_below_the_floor_is_refused_with_one_typed_error_on_every_target() {
    for row in refusal_rows() {
        let mut texts: Vec<(String, String)> = Vec::new();
        for triple in NATIVE_TARGETS {
            let label = format!("{}: {triple}", row.name);
            let (text, reason) = box_refusal(
                &label,
                compile_native(
                    &module(native_target(triple), &row.fact),
                    triple,
                    OptLevel::O0,
                    row.emit_proofs,
                    &row.license,
                ),
            );
            assert!((row.expect)(&reason), "{label}: {reason:?}");
            assert!(text.contains(row.fragment), "{label}: {text}");
            texts.push((triple.to_owned(), text));
        }
        // One function decides, so one text: the refusal names the function,
        // block and instruction, never the target.
        let first = texts[0].1.clone();
        for (triple, text) in &texts {
            assert_eq!(
                *text, first,
                "{}: {triple} spells another refusal",
                row.name
            );
        }
        // The wasm entries take no `emit_proofs`; the proof-lane row is a
        // native-compiler row.
        if row.emit_proofs {
            continue;
        }
        for (lane, result) in compile_wasm(&row.fact, &row.license) {
            let error = match result {
                Ok(_) => panic!("{}: {lane}: compiled; it must be refused", row.name),
                Err(error) => error,
            };
            assert!(
                error.contains(&first),
                "{}: {lane} does not carry the native refusal `{first}`: {error}",
                row.name
            );
        }
    }
}

#[test]
fn core_admission_keeps_the_default_box_floor() {
    let host = CoreHostJitTarget::detect().expect("supported closed-JIT host");
    let input = module(
        host.trust_ir_target_info().clone(),
        &fact(PremiseRoot::ParamByValue),
    );
    let error = trust_cg_codegen::admit_identity_core_module_for_host_jit(
        input,
        &host,
        trust_cg_codegen::CoreDeclaredImportManifest::empty(),
    )
    .expect_err("identity-Core admission must keep the consumer-rederived Box floor");
    assert!(
        matches!(
            &error,
            trust_cg_codegen::CoreAdmissionError::StrictAdapter(_)
        ),
        "the refusal must be the strict adapter's Box admission: {error}"
    );
    let text = error.to_string();
    assert!(text.contains("Inst::BoxDeref is not admitted"), "{text}");
    assert!(text.contains("consumer_rederived"), "{text}");
}

/// A named-premise Box can enter only a diagnostic, non-proof lane. Both
/// proof-grade JIT modes must reject it before translation and before the
/// certificate cache is even consulted. Otherwise the adapter could turn it
/// into `Copy` and the JIT could issue (or reuse) a verified certificate for
/// machine code whose Box validity remains only assumed.
#[cfg(feature = "verify")]
#[test]
fn proof_grade_jit_modes_refuse_before_translation_or_certificate_cache() {
    let host = CoreHostJitTarget::detect().expect("supported host JIT target");
    let input = module(
        host.trust_ir_target_info().clone(),
        &fact(PremiseRoot::ParamByValue),
    );
    for mode in [
        JitValidationMode::CachedVerified,
        JitValidationMode::AlwaysVerify,
    ] {
        let disclosure = BoxDerefDisclosure::new();
        let cache = Arc::new(JitCertCache::new());
        let compiler = Compiler::new_for_target_spec(
            CompilerConfig {
                emit_proofs: false,
                jit_validation_mode_override: Some(mode),
                ..CompilerConfig::for_host_jit()
            },
            host.target_spec(),
        )
        .with_codegen_license(named_premise_license_reporting_to(&disclosure))
        .with_jit_cert_cache(cache.clone());
        let error = match compiler.compile_module_to_jit(&input, &Default::default()) {
            Ok(_) => panic!("{mode:?}: proof-grade JIT compiled a named-premise BoxDeref"),
            Err(error) => error,
        };
        assert!(
            matches!(
                &error,
                CompileError::Adapter(AdapterError::BoxDerefNotAdmitted {
                    reason: BoxDerefRefusal::EvidenceBelowFloor { .. },
                    ..
                })
            ),
            "{mode:?}: {error}"
        );
        assert_eq!(
            cache.stats(),
            (0, 0, 0, 0),
            "{mode:?}: refusal must precede every certificate-cache action"
        );
        assert!(
            disclosure.is_empty(),
            "{mode:?}: a proof-grade refusal must not report a successful named-premise admission"
        );
    }
}

/// License admission is not a successful compile. Keep that distinction in
/// the disclosure when a later structural admission rejects the module.
#[test]
fn a_later_failure_is_reported_as_admission_not_as_compilation() {
    let mut input = module(
        native_target(X86_64_LINUX),
        &fact(PremiseRoot::ParamByValue),
    );
    let return_node = input.functions[0].blocks[0]
        .body
        .last_mut()
        .expect("read has a return");
    return_node.inst = trust_ir::Inst::Return { values: Vec::new() };

    let disclosure = BoxDerefDisclosure::new();
    let license = named_premise_license_reporting_to(&disclosure);
    let error = compile_native(&input, X86_64_LINUX, OptLevel::O0, false, &license)
        .expect_err("the malformed return must fail after license admission");
    assert!(
        matches!(error.as_ref(), CompileError::InvalidTrustIr(_)),
        "unexpected failure: {error}"
    );
    let lines = disclosure.lines();
    assert_eq!(
        lines.len(),
        1,
        "the successful policy admission is recorded"
    );
    assert!(
        lines[0].contains("admitted for compilation under named assumptions")
            && !lines[0].contains("compiled under named assumptions"),
        "a failed compile must not be described as compiled: {}",
        lines[0]
    );
}

/// An admitted module lowers on every target, at O0 and O2. On a host that
/// is not the target, this is "written, compiled, not executed".
#[test]
fn an_admitted_box_deref_lowers_on_every_target() {
    let admitted = fact(PremiseRoot::ParamByValue);
    for triple in NATIVE_TARGETS {
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            // A fresh report per compile: the assumption must reach the
            // caller of THIS entry, not be left over from another.
            let disclosure = BoxDerefDisclosure::new();
            let license = named_premise_license_reporting_to(&disclosure);
            let object = compile_native(
                &module(native_target(triple), &admitted),
                triple,
                opt_level,
                false,
                &license,
            )
            .unwrap_or_else(|error| panic!("{triple} {opt_level:?}: {error}"));
            assert!(!object.is_empty(), "{triple} {opt_level:?}: empty object");
            assert_reported(&format!("{triple} {opt_level:?}"), &disclosure);
            eprintln!(
                "[box_deref_consumer] {triple} {opt_level:?}: compiled, {} bytes; {}",
                object.len(),
                disclosure.lines()[0]
            );
        }
    }
    let wasm_module = module(trust_cg_codegen::wasm::wasm32_target_info(), &admitted);
    type WasmEntry = fn(&Module, &CodegenLicensePolicy) -> Result<Vec<u8>, String>;
    let entries: [(&str, WasmEntry); 2] = [
        ("wasm-module", |module, license| {
            trust_cg_codegen::wasm::compile_module_with_license(module, license)
                .map_err(|e| e.to_string())
        }),
        ("wasm-object", |module, license| {
            trust_cg_codegen::wasm::compile_object_with_license(module, license)
                .map_err(|e| e.to_string())
        }),
    ];
    for (lane, entry) in entries {
        let disclosure = BoxDerefDisclosure::new();
        let license = named_premise_license_reporting_to(&disclosure);
        let bytes = entry(&wasm_module, &license).unwrap_or_else(|error| panic!("{lane}: {error}"));
        assert_eq!(&bytes[..4], b"\0asm", "{lane}: not a wasm binary");
        assert_reported(lane, &disclosure);
        eprintln!(
            "[box_deref_consumer] {lane}: compiled, {} bytes; {}",
            bytes.len(),
            disclosure.lines()[0]
        );
    }
    // Both wasm evidence entries say, in the evidence itself, that the Box
    // validity was not established.
    let marker = trust_cg_codegen::wasm::BOX_VALIDITY_NOT_ESTABLISHED;
    let disclosure = BoxDerefDisclosure::new();
    let license = named_premise_license_reporting_to(&disclosure);
    let (_, evidence) = trust_cg_codegen::wasm::compile_module_with_evidence_policy_and_license(
        &wasm_module,
        &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
        &license,
    )
    .unwrap_or_else(|error| panic!("wasm module evidence: {error}"));
    assert!(evidence.not_run.contains(&marker), "{:?}", evidence.not_run);
    assert!(!evidence.ran.contains(&marker));
    assert_reported("wasm module evidence", &disclosure);
    let disclosure = BoxDerefDisclosure::new();
    let license = named_premise_license_reporting_to(&disclosure);
    let (_, evidence) =
        trust_cg_codegen::wasm::compile_object_with_evidence_and_license(&wasm_module, &license)
            .unwrap_or_else(|error| panic!("wasm object evidence: {error}"));
    assert!(evidence.not_run.contains(&marker), "{:?}", evidence.not_run);
    assert_reported("wasm object evidence", &disclosure);
}

#[test]
fn allocation_and_discharged_return_roots_have_real_accepted_consumer_fixtures() {
    for root in [
        PremiseRoot::AllocPostcondition,
        PremiseRoot::ReturnedBoxDischarged,
    ] {
        let input = rooted_module(native_target(X86_64_LINUX), root);
        let errors = trust_ir_build::validate_module(&input);
        assert!(errors.is_empty(), "{root:?}: {errors:?}");
        let disclosure = BoxDerefDisclosure::new();
        let license = named_premise_license_reporting_to(&disclosure);
        let object = compile_native(&input, X86_64_LINUX, OptLevel::O0, false, &license)
            .unwrap_or_else(|error| panic!("{root:?}: {error}"));
        assert!(!object.is_empty(), "{root:?}: empty object");
        let records = disclosure.records();
        assert_eq!(records.len(), 1, "{root:?}: {records:?}");
        assert_eq!(records[0].manifest.rows.len(), 1, "{root:?}");
        assert_eq!(records[0].manifest.rows[0].root, root);
        assert!(
            disclosure.lines()[0].contains(root.name()),
            "{root:?}: {:?}",
            disclosure.lines()
        );
    }
}

/// The wasm lowering is a value-preserving alias, not an implicit dereference:
/// the complete exported body contains only `local.get 0` and the structural
/// terminators. This independently pins the no-memory-effect half of SPEC
/// section 28; the native lowering twin pins exactly one LIR `Copy`.
#[test]
fn wasm_box_deref_is_a_fact_preserving_alias_with_no_memory_effect() {
    let input = identity_module(
        trust_cg_codegen::wasm::wasm32_target_info(),
        &fact(PremiseRoot::ParamByValue),
    );
    let bytes =
        trust_cg_codegen::wasm::compile_module_with_license(&input, &named_premise_license())
            .expect("the diagnostic named-premise lane admits the Box identity");

    let mut imported_functions = 0u32;
    let mut export = None;
    let mut bodies = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(&bytes) {
        match payload.expect("parse the emitted wasm") {
            wasmparser::Payload::ImportSection(reader) => {
                for import in reader {
                    if matches!(import.expect("import").ty, wasmparser::TypeRef::Func(_)) {
                        imported_functions += 1;
                    }
                }
            }
            wasmparser::Payload::ExportSection(reader) => {
                for item in reader {
                    let item = item.expect("export");
                    if item.name == IDENTITY && item.kind == wasmparser::ExternalKind::Func {
                        export = Some(item.index);
                    }
                }
            }
            wasmparser::Payload::CodeSectionEntry(body) => bodies.push(body),
            _ => {}
        }
    }
    let defined_index = export
        .expect("the Box identity is exported")
        .checked_sub(imported_functions)
        .expect("the Box identity is defined, not imported") as usize;
    let body = bodies
        .get(defined_index)
        .unwrap_or_else(|| panic!("missing code body {defined_index}"));
    let operators: Vec<_> = body
        .get_operators_reader()
        .expect("operators")
        .into_iter()
        .map(|operator| operator.expect("operator"))
        .collect();
    assert!(
        matches!(
            operators.as_slice(),
            [
                wasmparser::Operator::LocalGet { local_index: 0 },
                wasmparser::Operator::End
            ] | [
                wasmparser::Operator::LocalGet { local_index: 0 },
                wasmparser::Operator::Return,
                wasmparser::Operator::End
            ]
        ),
        "BoxDeref must emit only the value-preserving parameter read, never a memory op: \
         {operators:?}"
    );
}

const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern int64_t tcg_box_read(int64_t *p);
extern int64_t tcg_box_checked(int64_t *p);

int main(void) {
    int failures = 0;
    int64_t *cell = malloc(sizeof *cell);
    if (!cell) return 2;
    const int64_t values[] = {0, 1, -1, 0x1122334455667788LL, INT64_MIN, INT64_MAX};
    for (unsigned i = 0; i < sizeof values / sizeof values[0]; i++) {
        *cell = values[i];
        int64_t read = tcg_box_read(cell);
        int64_t checked = tcg_box_checked(cell);
        if (read != values[i] || checked != values[i]) {
            printf("MISMATCH value=%lld read=%lld checked=%lld\n",
                   (long long)values[i], (long long)read, (long long)checked);
            failures++;
        }
    }
    /* The null check after the deref is still executed: a build that removed
       it on the strength of the validity fact would load through NULL. */
    int64_t on_null = tcg_box_checked(NULL);
    if (on_null != -1) {
        printf("MISMATCH null check returned %lld\n", (long long)on_null);
        failures++;
    }
    free(cell);
    printf("failures=%d\n", failures);
    return failures != 0;
}
"#;

/// x86-64 Linux, executed: the admitted module returns the pointee and keeps
/// the null check that follows the deref.
#[test]
fn an_admitted_box_deref_executes_on_x86_64_with_the_right_result() {
    let test = "an_admitted_box_deref_executes_on_x86_64_with_the_right_result";
    let admitted = fact(PremiseRoot::ParamByValue);
    let license = named_premise_license();
    let mut objects = Vec::new();
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let object = compile_native(
            &module(native_target(X86_64_LINUX), &admitted),
            X86_64_LINUX,
            opt_level,
            false,
            &license,
        )
        .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        objects.push((opt_level, object));
    }
    if !cfg!(all(target_arch = "x86_64", target_os = "linux")) {
        // Not a runtime skip: on another host the lowering test above is
        // this target's evidence, and it is "written, compiled, not executed".
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
        let object_path = dir.join(format!("box_deref_{opt_level:?}.o"));
        fs::write(&object_path, &object).unwrap();
        let binary = dir.join(format!("box_deref_{opt_level:?}"));
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

/// AArch64, executed on an AArch64 host only (macOS or Linux GNU): the same
/// driver and the same two properties as the x86-64 leg. On any other host
/// this compiles the object for `aarch64-apple-darwin` and stops: "written,
/// compiled, not executed". `reports/2026-11-14-box-deref-consumer/
/// AARCH64_VALIDATION.md` is the handoff for running it.
#[test]
fn an_admitted_box_deref_executes_on_an_aarch64_host_with_the_right_result() {
    let test = "an_admitted_box_deref_executes_on_an_aarch64_host_with_the_right_result";
    let triple = if cfg!(all(target_arch = "aarch64", target_os = "linux")) {
        "aarch64-unknown-linux-gnu"
    } else {
        "aarch64-apple-darwin"
    };
    let admitted = fact(PremiseRoot::ParamByValue);
    let license = named_premise_license();
    let mut objects = Vec::new();
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let object = compile_native(
            &module(native_target(triple), &admitted),
            triple,
            opt_level,
            false,
            &license,
        )
        .unwrap_or_else(|error| panic!("{triple} {opt_level:?}: {error}"));
        objects.push((opt_level, object));
    }
    let can_execute = cfg!(all(
        target_arch = "aarch64",
        any(
            target_os = "macos",
            all(target_os = "linux", target_env = "gnu")
        )
    ));
    if !can_execute {
        eprintln!("[{test}] not an AArch64 host: {triple} compiled, not executed");
        return;
    }
    let dir = std::env::temp_dir().join(format!("trust_cg_{test}_{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let driver = dir.join("driver.c");
    fs::write(&driver, DRIVER).unwrap();
    for (opt_level, object) in objects {
        let object_path = dir.join(format!("box_deref_{opt_level:?}.o"));
        fs::write(&object_path, &object).unwrap();
        let binary = dir.join(format!("box_deref_{opt_level:?}"));
        let mut link = std::process::Command::new("cc");
        link.arg("-o").arg(&binary).arg(&driver).arg(&object_path);
        let linked = command_output_with_timeout(&mut link, codegen_link_timeout())
            .expect("a native C compiler is required on an AArch64 host");
        assert!(
            !linked.timed_out && linked.output.status.success(),
            "{opt_level:?}: link failed: {}",
            String::from_utf8_lossy(&linked.output.stderr)
        );
        let run = run_executable_with_timeout(&binary, codegen_run_timeout()).unwrap();
        let stdout = String::from_utf8_lossy(&run.output.stdout).into_owned();
        eprintln!("[{test}] {triple} {opt_level:?} EXECUTED:\n{stdout}");
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
const view = new DataView(inst.exports.memory.buffer);
const at = 1024;
let failures = 0;
for (const value of [0n, 1n, -1n, 0x1122334455667788n, -(2n ** 63n), 2n ** 63n - 1n]) {
  view.setBigInt64(at, value, true);
  const read = inst.exports.tcg_box_read(at);
  const checked = inst.exports.tcg_box_checked(at);
  if (read !== value || checked !== value) {
    console.log(`MISMATCH value=${value} read=${read} checked=${checked}`);
    failures++;
  }
}
const onNull = inst.exports.tcg_box_checked(0);
if (onNull !== -1n) { console.log(`MISMATCH null check returned ${onNull}`); failures++; }
console.log(`failures=${failures}`);
process.exit(failures ? 1 : 0);
"#;

/// WASM, executed under node when node is on `PATH`: the closed module reads
/// the pointee out of its own linear memory, and the null check after the
/// deref is still executed. In linear memory address 0 is readable, so a
/// build that dropped the check would return the eight bytes at 0 (zero),
/// not -1. Without node the module is validated and not executed.
#[test]
fn an_admitted_box_deref_executes_in_wasm_under_node_with_the_right_result() {
    use trust_cg_codegen::wasm::{WasmMemoryPolicy, WasmModulePolicy, WasmOptOptions};
    let test = "an_admitted_box_deref_executes_in_wasm_under_node_with_the_right_result";
    let admitted = fact(PremiseRoot::ParamByValue);
    let module = module(trust_cg_codegen::wasm::wasm32_target_info(), &admitted);
    // The closed module with its memory exported, so the driver can place
    // the pointee. `mid_end: true` asks for the trust-ir mid-end, which
    // declines a module holding a `BoxDeref`.
    let policy = WasmModulePolicy {
        memory: WasmMemoryPolicy::Owned {
            pages: 2,
            export: Some("memory".to_string()),
        },
        ..WasmModulePolicy::closed()
    };
    let Some(node) = node() else {
        eprintln!("[{test}] node not found: wasm32 not executed");
        return;
    };
    for level in [OptLevel::O0, OptLevel::O2] {
        let (bytes, _evidence) =
            trust_cg_codegen::wasm::compile_module_with_evidence_policy_license_options(
                &module,
                &policy,
                &named_premise_license(),
                WasmOptOptions {
                    level,
                    mid_end: true,
                },
            )
            .unwrap_or_else(|error| panic!("wasm module {level:?}: {error}"));
        wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
            .validate_all(&bytes)
            .unwrap_or_else(|error| panic!("{level:?}: the module does not validate: {error}"));
        let dir =
            std::env::temp_dir().join(format!("trust_cg_{test}_{level:?}_{}", std::process::id()));
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
        eprintln!("[{test}] {level:?} EXECUTED under node:\n{stdout}");
        assert!(
            out.status.success(),
            "{level:?}: node failed: {stdout}{}",
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(stdout.contains("failures=0"), "{level:?}: {stdout}");
        let _ = fs::remove_dir_all(&dir);
    }
}
