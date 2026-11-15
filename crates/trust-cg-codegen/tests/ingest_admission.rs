// trust-cg-codegen/tests/ingest_admission.rs - WS7.3 (F-113): every ingestion
// entry refuses what trust-ir's own validator refuses.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Before WS7.3 the object/CLI path (`Compiler::compile`), the host JIT, the
// compile service and the wasm lane enforced only the codegen LICENSE: a module
// trust-ir refuses (the c06(g) shape — an `Int(0)` seed at a `RefMut` tuple
// lane, `ConstTypeMismatch`) compiled. Each entry now admits the module through
// `trust_cg_codegen::ingest::admit_module` (trust-ir's composed codegen
// admission, every finding a refusal) and re-admits the module a dialect
// rewrite produced before lowering THAT.
//
// The rows here:
//   * positive: the valid twin compiles on every entry;
//   * negative twin: the same module plus one `ConstTypeMismatch` is refused
//     on the object path, the JIT, the compile service and the wasm lane, each
//     with the named finding (`general_consumer_accepts_head_invalid_modules`
//     is the proof program's GAP row, ported);
//   * adversarial: a store-form InsertField, an overlapping StructDef, a
//     `Dealloc` (lowerability layer), a `global_asm` block that survives JSON,
//     and a registered dialect lowering (a caller-supplied legalization
//     registry) that emits an ill-typed instruction, or a drop no glue row
//     states — the latter refused only by the POST-rewrite admission;
//   * mutation control: a source scan holds every public `compile*` /
//     `translate_*` entry that accepts a trust-ir module to admission, to a
//     named route into an admitting entry, or to a shrink-only allowlist of
//     diagnostic entries (`DIAGNOSTIC_BASELINE`, enforced) — so a new entry that
//     skips admission fails here.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};

use trust_cg_codegen::compiler::{
    CompileError, Compiler, CompilerConfig, CompilerTraceLevel, JitValidationMode,
};
use trust_cg_codegen::dialect_pipeline::DialectPipelineError;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{
    CompileGeneration, CompileRequest, CompileService, CompileServiceConfig, CompileStatus, Target,
    wasm,
};
use trust_cg_lower::{
    AdapterError, AdmissionStage, CodegenLicensePolicy, InvalidTrustIr, UnlicensedBodyPolicy,
};
use trust_ir::dialect::DialectInst;
use trust_ir::value::{StructId, ValueId};
use trust_ir::{
    Block, BlockId, Constant, FieldDef, FuncId, FuncTy, Function, Inst, InstrNode, Module,
    StructDef, Ty,
};
use trust_ir_build::ValidationError;

// =============================================================================
// Fixtures
// =============================================================================

/// The codegen license every row here compiles under. The hand-built
/// fixtures carry no license (`body_gate: None`), which the default policy
/// refuses since WS7.5 (DG-73) BEFORE the admission this file is about; so,
/// as every non-licensing test since WS7.5, the rows state `Permit`
/// explicitly. The license itself is held by `codegen_license_evidence.rs`.
fn license() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit)
}

/// `entry: () -> i64` returning 7: valid, and admitted with no finding.
fn valid_module() -> Module {
    let mut m = Module::new("ws7_3_valid");
    let sig = m
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut entry = Function::new(FuncId::new(0), "entry", sig, BlockId::new(0));
    entry.blocks.push(Block {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(7),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ],
    });
    m.functions.push(entry);
    m
}

/// The negative twin: [`valid_module`] plus ONE dead constant that trust-ir
/// refuses with `ConstTypeMismatch` — an `Int(0)` seed at a `RefMut` tuple
/// lane (the proof program's c06(g) shape, the 18-module class).
fn const_type_mismatch_twin() -> Module {
    let mut m = valid_module();
    m.name = "ws7_3_const_type_mismatch".to_string();
    let body = &mut m.functions[0].blocks[0].body;
    body.insert(
        1,
        InstrNode::new(Inst::Const {
            ty: Ty::Tuple(vec![Ty::RefMut(Box::new(Ty::I64)), Ty::I64]),
            value: Constant::Aggregate(vec![Constant::Int(0), Constant::Int(7)]),
        })
        .with_result(ValueId::new(1)),
    );
    m
}

fn is_const_type_mismatch(error: &ValidationError) -> bool {
    matches!(error, ValidationError::ConstTypeMismatch { .. })
}

fn wasm_twin(mut m: Module) -> Module {
    m.target_info = Some(wasm::wasm32_target_info());
    m
}

const TRIPLES: [(&str, Target); 4] = [
    ("x86_64-apple-darwin", Target::X86_64),
    ("aarch64-apple-darwin", Target::Aarch64),
    ("x86_64-unknown-linux-gnu", Target::X86_64),
    ("aarch64-unknown-linux-gnu", Target::Aarch64),
];

fn config(target: Target) -> CompilerConfig {
    CompilerConfig {
        opt_level: OptLevel::O0,
        target,
        emit_proofs: false,
        trace_level: CompilerTraceLevel::None,
        emit_debug: false,
        parallel: false,
        cegis_superopt_budget_sec: None,
        enable_fsym_trust_ir_preflight: false,
        enable_jit_fast_regalloc: false,
        jit_validation_mode_override: None,
        jit_external_symbol_resolution:
            trust_cg_codegen::JitExternalSymbolResolutionPolicy::ExplicitThenProcess,
        panic_unwind: false,
        relocation_model: trust_cg_codegen::RelocationModel::Static,
        function_sections: false,
        aarch64_isa_profile: None,
        ..CompilerConfig::default()
    }
}

fn compiler_for(triple: &str, target: Target) -> Compiler {
    Compiler::new_for_target_spec(
        config(target),
        TargetSpec::parse(triple).expect("target triple"),
    )
    .with_codegen_license(license())
}

fn host_target() -> Target {
    if cfg!(target_arch = "aarch64") {
        Target::Aarch64
    } else {
        Target::X86_64
    }
}

fn host_compiler() -> Compiler {
    Compiler::new(config(host_target())).with_codegen_license(license())
}

/// [`host_compiler`] with its JIT validation mode stated rather than the
/// host architecture's default.
fn host_jit_compiler(mode: JitValidationMode) -> Compiler {
    Compiler::new(CompilerConfig {
        jit_validation_mode_override: Some(mode),
        ..config(host_target())
    })
    .with_codegen_license(license())
}

fn service() -> CompileService {
    CompileService::new(CompileServiceConfig {
        codegen_license: license(),
        ..CompileServiceConfig::default()
    })
}

/// The ingestion refusal of `error`, or a panic naming what came instead.
fn invalid_trust_ir(error: CompileError, lane: &str) -> InvalidTrustIr {
    match error {
        CompileError::InvalidTrustIr(refusal) => refusal,
        other => panic!("{lane}: expected CompileError::InvalidTrustIr, got {other:?}"),
    }
}

// =============================================================================
// Fixture self-checks: the twins are exactly what they claim to be
// =============================================================================

#[test]
fn fixtures_valid_twin_is_admitted_and_the_negative_twin_carries_one_const_type_mismatch() {
    let license = license();
    let registered = trust_cg_codegen::ingest::registered_dialect_namespaces();
    assert_eq!(
        trust_cg_lower::admission_findings(&valid_module(), &license, registered),
        Vec::<ValidationError>::new(),
        "the valid twin must have no admission finding"
    );
    let findings =
        trust_cg_lower::admission_findings(&const_type_mismatch_twin(), &license, registered);
    assert_eq!(findings.len(), 1, "exactly one finding: {findings:?}");
    assert!(is_const_type_mismatch(&findings[0]), "{findings:?}");
    // The wasm twins differ only by the pinned wasm32 target shape.
    assert_eq!(
        trust_cg_lower::admission_findings(&wasm_twin(valid_module()), &license, &[]),
        Vec::<ValidationError>::new()
    );
}

// =============================================================================
// Positive: the valid twin compiles on every ingestion entry
// =============================================================================

#[test]
fn valid_twin_compiles_on_every_ingestion_entry() {
    let m = valid_module();
    for (triple, target) in TRIPLES {
        let object = compiler_for(triple, target)
            .compile(&m)
            .unwrap_or_else(|error| panic!("{triple}: the valid twin compiles: {error}"));
        assert!(!object.object_code.is_empty(), "{triple}");
    }
    host_compiler()
        .compile_module_to_jit(&m, &HashMap::new())
        .unwrap_or_else(|error| panic!("JIT: the valid twin compiles: {error}"));
    let response = service().compile(CompileRequest::new("valid", CompileGeneration::new(1)), &m);
    assert_eq!(
        response.status,
        CompileStatus::Compiled,
        "service: {:?}",
        response.diagnostics
    );
    let bytes = wasm::compile_module_with_license(&wasm_twin(m), &license())
        .expect("wasm: the valid twin compiles");
    assert!(!bytes.is_empty());
}

// =============================================================================
// Negative twin: refused on every ingestion entry with the named finding
// =============================================================================

/// The proof program's row GENERAL.consumer.accepts_head_invalid_modules
/// (CONSUMER-GAP at 2026-09-17: trust-cg compiled modules the trust-ir CLI
/// refuses with `ConstTypeMismatch`), ported onto an injected invalid module
/// so the PASS is not vacuous: the object/CLI path refuses it on every
/// object format, naming the finding.
#[test]
fn general_consumer_accepts_head_invalid_modules() {
    let twin = const_type_mismatch_twin();
    for (triple, target) in TRIPLES {
        let error = compiler_for(triple, target)
            .compile(&twin)
            .expect_err("the object path must refuse a module trust-ir refuses");
        assert_named_const_type_mismatch(error, triple);
    }
}

/// `ConstTypeMismatch` is one of the findings this backend consumes BY NAME
/// (`named_validation_refusal`): the shared source-contract verdict
/// `AdapterError::TrustIrAdmissionRefused`, carrying trust-ir's own text,
/// which `constant_permission_source_admission.rs` and
/// `switch_case_source_contract.rs` pin on the same entries. Admission
/// reports a named finding through its name, so the refusal is that one and
/// never a residual `InvalidTrustIr`; the text is the validator's finding.
fn assert_named_const_type_mismatch(error: CompileError, lane: &str) {
    match error {
        CompileError::Adapter(AdapterError::TrustIrAdmissionRefused { error }) => {
            assert!(
                error.contains("const type mismatch"),
                "{lane}: the refusal carries the ConstTypeMismatch finding: {error}"
            );
        }
        other => panic!("{lane}: expected the named ConstTypeMismatch refusal, got {other:?}"),
    }
}

#[test]
fn const_type_mismatch_twin_is_refused_by_the_jit() {
    let error = host_compiler()
        .compile_module_to_jit(&const_type_mismatch_twin(), &HashMap::new())
        .expect_err("the JIT must refuse a module trust-ir refuses");
    assert_named_const_type_mismatch(error, "JIT");
}

#[test]
fn const_type_mismatch_twin_is_refused_by_the_compile_service() {
    let response = service().compile(
        CompileRequest::new("const-type-mismatch", CompileGeneration::new(1)),
        &const_type_mismatch_twin(),
    );
    assert_ne!(response.status, CompileStatus::Compiled);
    assert!(
        response.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "trust_ir_invalid_module"
                && diagnostic.message.contains("ConstTypeMismatch")
        }),
        "the service names the finding under trust_ir_invalid_module: {:?}",
        response.diagnostics
    );
}

#[test]
fn const_type_mismatch_twin_is_refused_by_the_wasm_lane() {
    match wasm::compile_module_with_license(&wasm_twin(const_type_mismatch_twin()), &license()) {
        Err(wasm::WasmLowerError::CodegenAdmission(message)) => {
            assert!(
                message.contains("const type mismatch"),
                "wasm: the refusal carries the ConstTypeMismatch finding: {message}"
            );
        }
        other => panic!("the wasm lane must refuse the named finding, got {other:?}"),
    }
}

#[test]
fn invalid_trust_ir_names_three_findings_and_counts_the_rest() {
    let refusal = InvalidTrustIr {
        module: "m".to_string(),
        stage: AdmissionStage::Rewritten,
        errors: (0..5)
            .map(|index| ValidationError::ConstTypeMismatch {
                location: format!("site {index}"),
                expected: "i64".to_string(),
                actual: "bool".to_string(),
            })
            .collect(),
    };
    let text = refusal.to_string();
    assert!(
        text.contains("module `m` (after pre-adapter rewrite)"),
        "{text}"
    );
    assert!(text.contains("5 finding(s)"), "{text}");
    assert!(text.contains("site 0") && text.contains("site 2"), "{text}");
    assert!(!text.contains("site 3"), "{text}");
    assert!(text.ends_with("and 2 more"), "{text}");
}

// =============================================================================
// Adversarial rows
// =============================================================================

/// WS7.1 (b): the STORE FORM of `insertfield` is invalid trust-ir
/// (`FieldAccessInvalid`); ingestion refuses it before the adapter's own named
/// `AggregateInsertNotValueForm` refusal is reached.
#[test]
fn store_form_insert_field_is_refused_at_ingestion() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/insert_field/store_form.trust_ir");
    let text = std::fs::read_to_string(&path).expect("store-form fixture");
    let module = trust_ir::parser::parse_module(&text).expect("store-form fixture parses");
    for (triple, target) in TRIPLES {
        let refusal = invalid_trust_ir(
            compiler_for(triple, target)
                .compile(&module)
                .expect_err("store form refused"),
            triple,
        );
        assert!(
            refusal.any(|error| matches!(error, ValidationError::FieldAccessInvalid { .. })),
            "{triple}: {refusal}"
        );
    }
}

/// WS2.3 (F-031): a StructDef whose declared field byte ranges intersect is
/// refused at ingestion with trust-ir's `StructLayoutInconsistent`.
#[test]
fn overlapping_struct_def_is_refused_at_ingestion() {
    let mut m = valid_module();
    m.structs.push(StructDef {
        id: StructId::new(0),
        name: "Overlap".to_string(),
        fields: vec![
            FieldDef {
                name: "a".to_string(),
                ty: Ty::U64,
                offset: Some(0),
            },
            FieldDef {
                name: "b".to_string(),
                ty: Ty::U32,
                offset: Some(4),
            },
        ],
        size: Some(8),
        align: Some(4),
        repr: Default::default(),
        origin: None,
    });
    for (triple, target) in TRIPLES {
        let refusal = invalid_trust_ir(
            compiler_for(triple, target)
                .compile(&m)
                .expect_err("overlapping struct refused"),
            triple,
        );
        assert!(
            refusal.any(|error| matches!(error, ValidationError::StructLayoutInconsistent { .. })),
            "{triple}: {refusal}"
        );
    }
}

/// trust-ir's LOWERABILITY layer refuses every `Dealloc` (it names neither the
/// owning runtime nor the layout); the adapter's named Dealloc verdict carries
/// it on every ingestion entry.
#[test]
fn dealloc_is_refused_by_the_lowerability_layer() {
    let mut m = Module::new("ws7_3_dealloc");
    let sig = m
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "free_it", sig, BlockId::new(0));
    f.blocks.push(Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr)],
        body: vec![
            InstrNode::new(Inst::Dealloc {
                ptr: ValueId::new(0),
            }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    });
    m.functions.push(f);
    assert!(
        trust_cg_lower::admission_findings(&m, &license(), &[])
            .iter()
            .any(|error| matches!(
                error,
                ValidationError::UnlowerableForCodegen {
                    inst: "Dealloc",
                    ..
                }
            )),
        "fixture: the lowerability layer names the Dealloc"
    );
    for (triple, target) in TRIPLES {
        let message = compiler_for(triple, target)
            .compile(&m)
            .expect_err("Dealloc refused")
            .to_string();
        assert!(message.contains("Dealloc"), "{triple}: {message}");
    }
    let message = host_compiler()
        .compile_module_to_jit(&m, &HashMap::new())
        .expect_err("JIT refuses Dealloc")
        .to_string();
    assert!(message.contains("Dealloc"), "JIT: {message}");
}

/// A `global_asm` block survives the JSON codec, and ingestion refuses it
/// (`GlobalAsmNotConsumable`) rather than drop it.
#[test]
fn global_asm_that_survives_json_is_refused() {
    let mut m = valid_module();
    m.global_asm
        .push(".globl ws7_3_marker\nws7_3_marker:\n".to_string());
    let json = serde_json::to_string(&m).expect("serialize");
    let decoded: Module = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(decoded.global_asm, m.global_asm, "the block survives JSON");
    for (triple, target) in TRIPLES {
        let refusal = invalid_trust_ir(
            compiler_for(triple, target)
                .compile(&decoded)
                .expect_err("global_asm refused"),
            triple,
        );
        assert!(
            refusal.any(|error| matches!(error, ValidationError::GlobalAsmNotConsumable { .. })),
            "{triple}: {refusal}"
        );
    }
}

/// The authority tier's import rule: a module whose contract is backed by a
/// PROOF-BEARING import row is `UnauthenticatedImport` at ingestion — a lone
/// module carries no dependency that could authenticate the row (WS7.9's
/// `--link` is what may supply one). Plain `validate_module` (the structural
/// import floor) does NOT raise it, so the refusal is the admission's.
#[test]
fn a_proof_bearing_import_is_refused_at_ingestion() {
    let path = workspace_crates()
        .join("../tests/fixtures/trust_ir_binary_container/conformance/composition.json");
    let json = std::fs::read_to_string(&path).expect("composition fixture");
    let m: Module = serde_json::from_str(&json).expect("composition fixture decodes");
    let is_unauthenticated =
        |error: &ValidationError| matches!(error, ValidationError::UnauthenticatedImport { .. });
    assert!(
        !trust_ir_build::validate_module(&m)
            .iter()
            .any(&is_unauthenticated),
        "fixture: the structural floor takes the import row on faith"
    );
    for (triple, target) in TRIPLES {
        let refusal = invalid_trust_ir(
            compiler_for(triple, target)
                .compile(&m)
                .expect_err("an unauthenticated proof-bearing import is refused"),
            triple,
        );
        assert!(refusal.any(is_unauthenticated), "{triple}: {refusal}");
    }
    let refusal = invalid_trust_ir(
        host_compiler()
            .compile_module_to_jit(&m, &HashMap::new())
            .expect_err("the JIT refuses the unauthenticated import"),
        "JIT",
    );
    assert!(refusal.any(is_unauthenticated), "JIT: {refusal}");
}

// -----------------------------------------------------------------------------
// VALIDATE WHAT IS LOWERED: a dialect rewrite produces core IR the received
// module's admission never saw. The registry is caller-supplied
// (`Compiler::with_dialect_legalization_registry`), so a "mutated lowering" is
// simply a registered rewrite rule that emits the defect; the received module
// (one well-formed `ws73.probe` op) is admitted, and only the rewritten one is
// refused.
// -----------------------------------------------------------------------------

const PROBE_NS: &str = "ws73";

/// `ws73.probe(p: ptr)`: no result.
fn probe_op(operand: ValueId) -> DialectInst {
    DialectInst::new(PROBE_NS, "probe").with_operand(operand)
}

/// `entry(p: ptr) { ws73.probe(p); return }`.
fn probe_module(name: &str) -> Module {
    let mut m = Module::new(name);
    let sig = m
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    // `Owned { v: i64 }`: a struct, so not trivially droppable — a drop of
    // it is a real destructor call that only a `drop_glue` row can state.
    m.structs.push(StructDef {
        id: StructId::new(0),
        name: "Owned".to_string(),
        fields: vec![FieldDef {
            name: "v".to_string(),
            ty: Ty::I64,
            offset: None,
        }],
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });
    let mut entry = Function::new(FuncId::new(0), "entry", sig, BlockId::new(0));
    entry.blocks.push(Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr)],
        body: vec![
            InstrNode::new(Inst::DialectOp(Box::new(probe_op(ValueId::new(0))))),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    });
    m.functions.push(entry);
    m
}

/// The mutated lowering: `ws73.probe(p)` becomes `drop<Owned>(p)`, a drop
/// trust-ir's STRUCTURAL validator admits (a struct is not trivially
/// droppable, so this is the one spelling of its drop) but whose destructor
/// no `drop_glue` row states, so only the CODEGEN lowerability layer refuses
/// it ("a drop is never lowered as nothing"). The legalization's own
/// re-validation is structural, so this is the defect only the post-rewrite
/// ADMISSION sees. (A drop of `i64` would not do: it is not the one spelling
/// of a drop, which the structural re-validation already refuses.)
fn probe_to_unresolved_drop(
    _node: &InstrNode,
    op: &DialectInst,
    _results: &[ValueId],
    _context: &mut trust_ir::dialect::lowering::LoweringContext<'_>,
) -> trust_ir::dialect::RewriteOutcome {
    let [operand] = op.operands.as_slice() else {
        return trust_ir::dialect::RewriteOutcome::Err("ws73.probe takes one operand".into());
    };
    trust_ir::dialect::RewriteOutcome::Replace(vec![InstrNode::new(Inst::Drop {
        ty: Ty::Struct(StructId::new(0)),
        ptr: *operand,
    })])
}

/// The mutated lowering: `ws73.probe(p)` becomes `%9 = add.i64 p, p`, an
/// ill-typed core instruction (a `ptr` operand of an `i64` add).
fn probe_to_ill_typed_add(
    _node: &InstrNode,
    op: &DialectInst,
    _results: &[ValueId],
    _context: &mut trust_ir::dialect::lowering::LoweringContext<'_>,
) -> trust_ir::dialect::RewriteOutcome {
    let [operand] = op.operands.as_slice() else {
        return trust_ir::dialect::RewriteOutcome::Err("ws73.probe takes one operand".into());
    };
    trust_ir::dialect::RewriteOutcome::Replace(vec![
        InstrNode::new(Inst::BinOp {
            op: trust_ir::BinOp::Add,
            ty: Ty::I64,
            lhs: *operand,
            rhs: *operand,
        })
        .with_result(ValueId::new(9)),
    ])
}

/// The default registry plus `ws73` with `probe` lowered by `rewrite`.
fn probe_registry(
    rule: &'static str,
    rewrite: trust_cg_codegen::dialect_legalization::RewriteFn,
) -> trust_cg_codegen::dialect_legalization::DialectLegalizationRegistry {
    use trust_cg_codegen::dialect_legalization::{
        DialectGrammar, DialectLegalizationRegistry, DialectRegistration, LegalizationEvidence,
        OpLowering, OpRule, RewriteRule, RuleTargets,
    };
    use trust_ir::dialect::schema::{OperandType, OperationSchema};
    let mut registrations = DialectLegalizationRegistry::default_registrations();
    registrations.push(DialectRegistration {
        namespace: PROBE_NS.to_string(),
        version: 1,
        owner: "trust-cg ingest_admission.rs (a deliberately defective lowering)".to_string(),
        grammar: DialectGrammar::Exact(vec![OperationSchema {
            name: "probe".to_string(),
            operands: vec![OperandType::Exact(Ty::Ptr)],
            results: vec![],
            attributes: vec![],
        }]),
        ops: vec![OpRule::single(
            "probe",
            format!("ws73.probe/{rule}"),
            OpLowering::Rewrite(RewriteRule {
                name: rule,
                targets: RuleTargets::Any,
                rewrite,
            }),
            LegalizationEvidence::TestedOnly {
                tests: "ingest_admission.rs".to_string(),
            },
        )],
        types: Vec::new(),
    });
    DialectLegalizationRegistry::new(registrations).expect("well-formed test registry")
}

/// The received module is admitted under `registry` (its op's namespace is
/// one the registry lowers, so trust-ir's "no registered lowering" does not
/// apply) — the defect exists only after the rewrite.
fn assert_received_is_admitted(
    m: &Module,
    registry: &trust_cg_codegen::dialect_legalization::DialectLegalizationRegistry,
) {
    let namespaces = trust_cg_codegen::ingest::registry_dialect_namespaces(registry);
    assert!(namespaces.contains(&PROBE_NS), "{namespaces:?}");
    assert_eq!(
        trust_cg_lower::admission_findings(m, &license(), &namespaces),
        Vec::<ValidationError>::new(),
        "fixture: the RECEIVED module is admitted"
    );
    // ... and refused without the registry's namespace (adversarial: the
    // exemption is the registry's, never a blanket one).
    assert!(
        trust_cg_lower::admission_findings(m, &license(), &[])
            .iter()
            .any(|error| matches!(
                error,
                ValidationError::UnlowerableForCodegen {
                    inst: "DialectOp",
                    ..
                }
            )),
        "fixture: an unregistered namespace has no lowering"
    );
}

#[test]
fn a_codegen_only_defect_in_a_dialect_rewrite_is_refused_after_the_rewrite() {
    let m = probe_module("ws7_3_dialect_rewrite_drop");
    let registry = probe_registry("unresolved-drop", probe_to_unresolved_drop);
    assert_received_is_admitted(&m, &registry);
    let is_unresolved_drop = |error: &ValidationError| {
        matches!(
            error,
            ValidationError::UnlowerableForCodegen { inst: "Drop", .. }
        )
    };
    for (triple, target) in TRIPLES {
        let refusal = invalid_trust_ir(
            compiler_for(triple, target)
                .with_dialect_legalization_registry(registry.clone())
                .compile(&m)
                .expect_err("the rewritten module's unresolved drop is refused"),
            triple,
        );
        assert_eq!(
            refusal.stage,
            AdmissionStage::Rewritten,
            "{triple}: {refusal}"
        );
        assert!(refusal.any(is_unresolved_drop), "{triple}: {refusal}");
    }
    // The JIT runs a `tested-only` rule only in a mode that makes no proof
    // claim, so the mode is stated, not inherited from the host: `Unchecked`
    // is AArch64's default, and x86-64's default verifies (JIT-5). The
    // rewrite runs, and its output is refused after it.
    let refusal = invalid_trust_ir(
        host_jit_compiler(JitValidationMode::Unchecked)
            .with_dialect_legalization_registry(registry.clone())
            .compile_module_to_jit(&m, &HashMap::new())
            .expect_err("the JIT refuses the rewritten module"),
        "JIT",
    );
    assert_eq!(refusal.stage, AdmissionStage::Rewritten, "JIT: {refusal}");
    assert!(refusal.any(is_unresolved_drop), "JIT: {refusal}");
    // A verifying JIT (x86-64's default) admits only legalization rules whose
    // evidence the compile checks: it refuses the tested-only rule by name
    // before the rewrite runs (decision LD-W7-6).
    for mode in [
        JitValidationMode::CachedVerified,
        JitValidationMode::AlwaysVerify,
    ] {
        match host_jit_compiler(mode)
            .with_dialect_legalization_registry(registry.clone())
            .compile_module_to_jit(&m, &HashMap::new())
            .expect_err("a verifying JIT refuses the tested-only rule")
        {
            CompileError::DialectPipeline(DialectPipelineError::ProofPolicy {
                rule,
                evidence,
                ..
            }) => {
                assert_eq!(rule, "ws73.probe/unresolved-drop", "JIT {mode:?}");
                assert!(
                    evidence.starts_with("tested-only"),
                    "JIT {mode:?}: {evidence}"
                );
            }
            other => panic!("JIT {mode:?}: expected the legalization proof policy, got {other:?}"),
        }
    }
}

#[test]
fn an_ill_typed_dialect_rewrite_is_refused_after_the_rewrite() {
    let m = probe_module("ws7_3_dialect_rewrite_ill_typed");
    let registry = probe_registry("ill-typed-add", probe_to_ill_typed_add);
    assert_received_is_admitted(&m, &registry);
    // The legalization re-validates its output structurally and refuses a
    // new finding by name (`LegalizedModuleInvalid`) before the post-rewrite
    // admission runs; either way nothing is lowered.
    for (triple, target) in TRIPLES {
        let error = compiler_for(triple, target)
            .with_dialect_legalization_registry(registry.clone())
            .compile(&m)
            .expect_err("the ill-typed rewrite is refused");
        match &error {
            CompileError::DialectPipeline(
                trust_cg_codegen::dialect_pipeline::DialectPipelineError::LegalizedModuleInvalid {
                    ..
                },
            ) => {}
            CompileError::InvalidTrustIr(refusal) => {
                assert_eq!(
                    refusal.stage,
                    AdmissionStage::Rewritten,
                    "{triple}: {refusal}"
                );
            }
            other => panic!("{triple}: expected a post-rewrite refusal, got {other:?}"),
        }
    }
}

// =============================================================================
// Mutation control: every public ingestion entry reaches admission
// =============================================================================

/// How an entry that accepts a trust-ir module is held to admission.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Held {
    /// Its body calls an admission function, or it takes an `AdmittedModule`.
    Admits,
    /// Its body calls EVERY named admitting entry (checked textually).
    RoutesThrough(&'static [&'static str]),
    /// Not ingestion authority (the stated reason); shrink-only.
    Diagnostic(&'static str),
}

/// Files scanned, relative to the workspace `crates/` directory.
const SCANNED_ROOTS: [&str; 2] = ["trust-cg-codegen/src", "trust-cg-lower/src"];

/// Every public `compile*` / `translate_*` entry of the scanned crates that
/// accepts a trust-ir module or function, keyed `<file>::<name>`.
fn classification() -> BTreeMap<&'static str, Held> {
    use Held::*;
    const RAW_ADAPTER: &str = "raw adapter entry: lowers under the tolerant prerequisites walk; \
         used by tests, differential tools and the in-crate callers of an ALREADY ADMITTED module, \
         never by an ingestion path of this workspace";
    BTreeMap::from([
        // ---- trust-cg-codegen: the ingestion entries ----
        ("compiler.rs::compile", Admits),
        (
            "compiler.rs::compile_module_to_jit_with_profile_hooks",
            Admits,
        ),
        (
            "compiler.rs::compile_module_to_jit",
            RoutesThrough(&["compile_module_to_jit_with_profile_hooks"]),
        ),
        (
            "compile_service.rs::compile",
            RoutesThrough(&["compile_plan"]),
        ),
        (
            "compile_service.rs::compile_plan",
            RoutesThrough(&["compile_plan_with_extern_symbols"]),
        ),
        (
            "compile_service.rs::compile_with_extern_symbols",
            RoutesThrough(&["compile_plan_with_extern_symbols"]),
        ),
        (
            "compile_service.rs::compile_plan_with_extern_symbols",
            // The service's pre-allocation verifier verdict
            // (`verifier_rejection_response`) is a structural pre-check with
            // its own failure codes, not the admission: both payload routes
            // compile through an admitting `Compiler` entry.
            RoutesThrough(&["compile_object_payload", "compile_executable_payload"]),
        ),
        (
            "pgo_runner.rs::compile_host_jit_with_profile_use",
            RoutesThrough(&["compile_host_jit_with_profile_use_and_symbols"]),
        ),
        (
            "pgo_runner.rs::compile_host_jit_with_profile_use_and_symbols",
            RoutesThrough(&["compile_host_jit_with_profile_use_and_symbols_and_license"]),
        ),
        (
            "pgo_runner.rs::compile_host_jit_with_profile_use_and_symbols_and_license",
            RoutesThrough(&["compile_module_to_jit"]),
        ),
        // The wasm lane: the closed-module and the object (relocatable) routes.
        (
            "lower.rs::compile_module",
            RoutesThrough(&["compile_module_with_policy"]),
        ),
        (
            "lower.rs::compile_module_with_policy",
            RoutesThrough(&["compile_module_with_policy_and_license"]),
        ),
        (
            "lower.rs::compile_module_with_license",
            RoutesThrough(&["compile_module_with_policy_and_license"]),
        ),
        (
            "lower.rs::compile_module_with_policy_and_license",
            RoutesThrough(&["compile_module_parts"]),
        ),
        (
            "lower.rs::compile_module_with_evidence",
            RoutesThrough(&["compile_module_with_evidence_and_policy"]),
        ),
        (
            "lower.rs::compile_module_with_evidence_and_policy",
            RoutesThrough(&["compile_module_with_evidence_policy_and_license"]),
        ),
        (
            "lower.rs::compile_module_with_evidence_and_policy_optimized",
            RoutesThrough(&["compile_module_with_evidence_policy_license_optimized"]),
        ),
        (
            "lower.rs::compile_module_with_evidence_policy_and_license",
            RoutesThrough(&["compile_module_with_evidence_policy_license_optimized"]),
        ),
        (
            "lower.rs::compile_module_with_evidence_policy_license_optimized",
            RoutesThrough(&["compile_module_with_evidence_policy_license_options"]),
        ),
        (
            "lower.rs::compile_module_with_evidence_policy_license_options",
            RoutesThrough(&["compile_module_evidence"]),
        ),
        (
            "lower.rs::compile_sized_closed_module_with_evidence_license_optimized",
            RoutesThrough(&["compile_sized_closed_module_with_evidence_license_options"]),
        ),
        (
            "lower.rs::compile_sized_closed_module_with_evidence_license_options",
            RoutesThrough(&["compile_module_evidence"]),
        ),
        (
            "lower.rs::compile_object",
            RoutesThrough(&["compile_object_with_license"]),
        ),
        (
            "lower.rs::compile_object_optimized",
            RoutesThrough(&["compile_object_with_license_optimized"]),
        ),
        (
            "lower.rs::compile_object_with_license",
            RoutesThrough(&["compile_object_with_license_optimized"]),
        ),
        (
            "lower.rs::compile_object_with_license_optimized",
            RoutesThrough(&["compile_object_with_license_options"]),
        ),
        (
            "lower.rs::compile_object_with_license_options",
            RoutesThrough(&["compile_object_with_license_options_hints"]),
        ),
        (
            "lower.rs::compile_object_with_license_options_hints",
            RoutesThrough(&["compile_object_parts"]),
        ),
        (
            "lower.rs::compile_object_with_evidence",
            RoutesThrough(&["compile_object_with_evidence_and_license"]),
        ),
        (
            "lower.rs::compile_object_with_evidence_optimized",
            RoutesThrough(&["compile_object_with_evidence_license_optimized"]),
        ),
        (
            "lower.rs::compile_object_with_evidence_and_license",
            RoutesThrough(&["compile_object_with_evidence_license_optimized"]),
        ),
        (
            "lower.rs::compile_object_with_evidence_license_optimized",
            RoutesThrough(&["compile_object_with_evidence_license_options"]),
        ),
        (
            "lower.rs::compile_object_with_evidence_license_options",
            RoutesThrough(&["compile_object_with_evidence_license_options_hints"]),
        ),
        (
            "lower.rs::compile_object_with_evidence_license_options_hints",
            RoutesThrough(&["compile_object_parts"]),
        ),
        // The Core lane's raw-module DIAGNOSTIC entries: by their own docs
        // not Core admission authority; production Core admission validates
        // the full report first (`core_admission.rs`).
        (
            "strict_adapter.rs::translate_core_module_for_target_with_validation",
            Diagnostic("raw Core-lane diagnostic entry; not Core admission authority"),
        ),
        (
            "strict_adapter.rs::translate_core_module_for_target_with_validation_and_license",
            Diagnostic("raw Core-lane diagnostic entry; not Core admission authority"),
        ),
        // ---- trust-cg-lower: the admitted adapter entries ----
        (
            "adapter.rs::translate_admitted_module_for_arch_with_access_model_and_stats",
            Admits,
        ),
        (
            "adapter.rs::translate_admitted_module_for_native_scalar_c_abi",
            Admits,
        ),
        (
            "adapter.rs::translate_admitted_module_for_arch_with_tls_and_validation",
            Admits,
        ),
        // ---- trust-cg-lower: diagnostic entries (shrink-only) ----
        (
            "adapter.rs::translate_type_in_module",
            Diagnostic("a type query; lowers no body"),
        ),
        ("adapter.rs::translate_module", Diagnostic(RAW_ADAPTER)),
        (
            "adapter.rs::translate_module_for_arch",
            Diagnostic(RAW_ADAPTER),
        ),
        (
            "adapter.rs::translate_module_for_arch_with_tls",
            Diagnostic(RAW_ADAPTER),
        ),
        (
            "adapter.rs::translate_module_for_arch_with_tls_with_license",
            Diagnostic(RAW_ADAPTER),
        ),
        (
            "adapter.rs::translate_module_for_arch_with_tls_and_validation",
            Diagnostic(RAW_ADAPTER),
        ),
        (
            "adapter.rs::translate_module_for_arch_with_tls_and_validation_with_license",
            Diagnostic(RAW_ADAPTER),
        ),
        (
            "adapter.rs::translate_module_strict_for_arch_with_tls_and_validation",
            Diagnostic(RAW_ADAPTER),
        ),
        (
            "adapter.rs::translate_module_strict_for_arch_with_tls_and_validation_with_license",
            Diagnostic(
                "the strict adapter entry the core lane (strict_adapter.rs) calls only after \
                 trust-ir's full validate_module_report",
            ),
        ),
        (
            "adapter.rs::translate_module_for_arch_with_tls_and_stats",
            Diagnostic(RAW_ADAPTER),
        ),
        (
            "adapter.rs::translate_module_for_arch_with_tls_and_stats_with_license",
            Diagnostic(RAW_ADAPTER),
        ),
        (
            "adapter.rs::translate_module_for_arch_with_tls_and_stats_with_license_and_weak_references",
            Diagnostic(RAW_ADAPTER),
        ),
        (
            "adapter.rs::translate_module_for_arch_with_tls_and_stats_and_validation",
            Diagnostic(RAW_ADAPTER),
        ),
        (
            "adapter.rs::translate_module_for_arch_with_tls_and_stats_and_validation_with_license",
            Diagnostic(RAW_ADAPTER),
        ),
        (
            "adapter.rs::translate_inline_only_bodies",
            Diagnostic(
                "called by lir_module_prep on the module Compiler::compile already admitted",
            ),
        ),
        (
            "adapter.rs::translate_body_template",
            Diagnostic(
                "called by lir_module_prep on the module Compiler::compile already admitted",
            ),
        ),
        (
            "adapter.rs::translate_function",
            Diagnostic("single-function diagnostic translation (module merge checks, tests)"),
        ),
        (
            "adapter.rs::translate_function_with_license",
            Diagnostic("single-function diagnostic translation"),
        ),
        (
            "adapter.rs::translate_function_with_names",
            Diagnostic("single-function diagnostic translation"),
        ),
        (
            "adapter.rs::translate_function_with_names_and_license",
            Diagnostic("single-function diagnostic translation"),
        ),
    ])
}

/// The diagnostic allowlist as it stands: SHRINK-ONLY. A `Diagnostic` row
/// not listed here fails [`diagnostic_rows_are_the_baseline`], so a new
/// public entry cannot skip admission by joining the allowlist; a listed
/// key that is no longer a `Diagnostic` row fails too, so the baseline
/// shrinks with the allowlist. Moving an entry to `AdmittedModule` (roadmap
/// WS7.3's typestate) deletes its line here.
const DIAGNOSTIC_BASELINE: [&str; 22] = [
    "strict_adapter.rs::translate_core_module_for_target_with_validation",
    "strict_adapter.rs::translate_core_module_for_target_with_validation_and_license",
    "adapter.rs::translate_type_in_module",
    "adapter.rs::translate_module",
    "adapter.rs::translate_module_for_arch",
    "adapter.rs::translate_module_for_arch_with_tls",
    "adapter.rs::translate_module_for_arch_with_tls_with_license",
    "adapter.rs::translate_module_for_arch_with_tls_and_validation",
    "adapter.rs::translate_module_for_arch_with_tls_and_validation_with_license",
    "adapter.rs::translate_module_strict_for_arch_with_tls_and_validation",
    "adapter.rs::translate_module_strict_for_arch_with_tls_and_validation_with_license",
    "adapter.rs::translate_module_for_arch_with_tls_and_stats",
    "adapter.rs::translate_module_for_arch_with_tls_and_stats_with_license",
    "adapter.rs::translate_module_for_arch_with_tls_and_stats_with_license_and_weak_references",
    "adapter.rs::translate_module_for_arch_with_tls_and_stats_and_validation",
    "adapter.rs::translate_module_for_arch_with_tls_and_stats_and_validation_with_license",
    "adapter.rs::translate_inline_only_bodies",
    "adapter.rs::translate_body_template",
    "adapter.rs::translate_function",
    "adapter.rs::translate_function_with_license",
    "adapter.rs::translate_function_with_names",
    "adapter.rs::translate_function_with_names_and_license",
];

fn diagnostic_rows_are_the_baseline(
    classification: &BTreeMap<&'static str, Held>,
) -> Result<(), String> {
    let rows: BTreeSet<&str> = classification
        .iter()
        .filter(|(_, held)| matches!(held, Held::Diagnostic(_)))
        .map(|(key, _)| *key)
        .collect();
    let baseline: BTreeSet<&str> = DIAGNOSTIC_BASELINE.iter().copied().collect();
    let added: Vec<&&str> = rows.difference(&baseline).collect();
    let dropped: Vec<&&str> = baseline.difference(&rows).collect();
    if !added.is_empty() {
        return Err(format!(
            "the diagnostic allowlist is shrink-only; new rows: {added:?}"
        ));
    }
    if !dropped.is_empty() {
        return Err(format!(
            "no longer Diagnostic rows — delete them from DIAGNOSTIC_BASELINE: {dropped:?}"
        ));
    }
    Ok(())
}

/// One discovered entry: the key `<file name>::<fn name>`, its parameter text
/// and its body text.
struct Entry {
    key: String,
    params: String,
    body: String,
}

fn workspace_crates() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .to_path_buf()
}

fn rust_files(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).expect("read_dir") {
        let path = entry.expect("dir entry").path();
        if path.is_dir() {
            rust_files(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            out.push(path);
        }
    }
}

/// The byte index just past the delimiter matching the one at `open`.
fn matching(text: &[u8], open: usize, left: u8, right: u8) -> usize {
    let mut depth = 0usize;
    let mut index = open;
    while index < text.len() {
        if text[index] == left {
            depth += 1;
        } else if text[index] == right {
            depth -= 1;
            if depth == 0 {
                return index + 1;
            }
        }
        index += 1;
    }
    text.len()
}

/// The source offset where in-file unit tests begin (`#[cfg(test)]` followed
/// by a `mod`), so test helpers are not scanned as entries.
fn test_module_start(source: &str) -> usize {
    let mut from = 0;
    while let Some(found) = source[from..].find("#[cfg(test)]") {
        let at = from + found;
        let rest = source[at + "#[cfg(test)]".len()..].trim_start();
        if rest.starts_with("mod ") || rest.starts_with("pub(crate) mod ") {
            return at;
        }
        from = at + 1;
    }
    source.len()
}

/// Whether `params` names a trust-ir module or function. In `wasm/lower.rs`
/// the bare `Module` IS trust-ir's (imported by name there).
fn takes_trust_ir(file: &str, source: &str, params: &str) -> bool {
    const NAMES: [&str; 5] = [
        "trust_ir::Module",
        "TrustIrModule",
        "TrustIrFunction",
        "trust_ir::Function",
        "AdmittedModule",
    ];
    if NAMES.iter().any(|name| params.contains(name)) {
        return true;
    }
    let imports_module = source.contains("use trust_ir::Module;")
        || source.contains("use trust_ir::{Module")
        || (file == "lower.rs" && source.contains("use trust_ir::{"));
    imports_module && (params.contains("&Module") || params.contains("&'module Module"))
}

/// Every public `compile*` / `translate_*` fn in `source` that accepts a
/// trust-ir module or function (outside the in-file test module).
fn entries_in(file: &str, source: &str) -> Vec<Entry> {
    let scanned = &source[..test_module_start(source)];
    let bytes = scanned.as_bytes();
    let mut entries = Vec::new();
    let mut from = 0;
    while let Some(found) = scanned[from..].find("pub fn ") {
        let name_start = from + found + "pub fn ".len();
        from = name_start;
        let name: String = scanned[name_start..]
            .chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_')
            .collect();
        if !(name.starts_with("compile") || name.starts_with("translate")) {
            continue;
        }
        let Some(paren) = scanned[name_start..].find('(').map(|i| name_start + i) else {
            continue;
        };
        let params_end = matching(bytes, paren, b'(', b')');
        let params = scanned[paren..params_end].to_string();
        let Some(brace) = scanned[params_end..].find('{').map(|i| params_end + i) else {
            continue;
        };
        // A trait method declaration without a body ends at ';' first.
        if scanned[params_end..brace].contains(';') {
            continue;
        }
        let body_end = matching(bytes, brace, b'{', b'}');
        if takes_trust_ir(file, source, &params) {
            entries.push(Entry {
                key: format!("{file}::{name}"),
                params,
                body: scanned[brace..body_end].to_string(),
            });
        }
    }
    entries
}

fn discovered_entries() -> Vec<Entry> {
    let crates = workspace_crates();
    let mut entries = Vec::new();
    for root in SCANNED_ROOTS {
        let mut files = Vec::new();
        rust_files(&crates.join(root), &mut files);
        files.sort();
        for path in files {
            let file = path.file_name().unwrap().to_string_lossy().to_string();
            if file.contains("test") {
                continue;
            }
            let source = std::fs::read_to_string(&path).expect("read source");
            entries.extend(entries_in(&file, &source));
        }
    }
    entries
}

/// The verdict for one entry, or why it fails the gate.
fn judge(entry: &Entry, held: Option<Held>) -> Result<(), String> {
    let admits = entry.params.contains("AdmittedModule")
        || entry.body.contains("admit_module(")
        || entry.body.contains("admit_rewritten(");
    match held {
        None => Err(format!(
            "{}: a public entry that accepts a trust-ir module is not classified — admit it \
             (crate::ingest::admit_module) or route it through an admitting entry",
            entry.key
        )),
        Some(Held::Admits) if admits => Ok(()),
        Some(Held::Admits) => Err(format!("{}: classified Admits but never admits", entry.key)),
        Some(Held::RoutesThrough(callees)) => match callees
            .iter()
            .find(|callee| !entry.body.contains(&format!("{callee}(")))
        {
            None => Ok(()),
            Some(callee) => Err(format!(
                "{}: classified as routing through `{callee}`, which its body no longer calls",
                entry.key
            )),
        },
        Some(Held::Diagnostic(_)) if admits => Err(format!(
            "{}: now admits — move it out of the diagnostic allowlist (it only shrinks)",
            entry.key
        )),
        Some(Held::Diagnostic(_)) => Ok(()),
    }
}

/// Private helpers a route may end at, each with the token its body must
/// still contain: the admission call (`admit_module(`), or a call into
/// ANOTHER helper of this list in the same file — a chain that must reach the
/// admission call without a cycle ([`route_targets_admit`] walks it).
const PRIVATE_ADMITTING: [(&str, &str, &str); 8] = [
    (
        "wasm/lower.rs",
        "compile_module_parts",
        "admit_closed_module(",
    ),
    (
        "wasm/lower.rs",
        "compile_module_evidence",
        "compile_module_parts(",
    ),
    ("wasm/lower.rs", "compile_object_parts", "admit_object("),
    ("wasm/lower.rs", "admit_closed_module", "admit_ingestion("),
    ("wasm/lower.rs", "admit_object", "admit_ingestion("),
    ("wasm/lower.rs", "admit_ingestion", "admit_module("),
    (
        "compile_service.rs",
        "compile_object_payload",
        ".compile(module)",
    ),
    (
        "compile_service.rs",
        "compile_executable_payload",
        ".compile_module_to_jit_with_profile_hooks(",
    ),
];

/// The tokens that END a private chain: the admission call itself, or a call
/// into a public entry this test classifies `Admits` (`Compiler::compile`,
/// the JIT entry).
const CHAIN_ENDS: [&str; 3] = [
    "admit_module(",
    ".compile(module)",
    ".compile_module_to_jit_with_profile_hooks(",
];

/// Every route must end at an entry that admits (or at a private helper
/// [`PRIVATE_ADMITTING`] names): a route through a diagnostic entry would be a
/// hole.
fn route_targets_admit(classification: &BTreeMap<&'static str, Held>) -> Result<(), String> {
    let names: BTreeMap<&str, Held> = classification
        .iter()
        .map(|(key, held)| (key.rsplit("::").next().unwrap(), *held))
        .collect();
    for (key, held) in classification {
        let Held::RoutesThrough(callees) = held else {
            continue;
        };
        for callee in *callees {
            match names.get(callee) {
                Some(Held::Diagnostic(_)) => {
                    return Err(format!("{key} routes through diagnostic entry {callee}"));
                }
                Some(_) => {}
                None if PRIVATE_ADMITTING.iter().any(|(_, name, _)| name == callee) => {}
                None => return Err(format!("{key} routes through unknown entry {callee}")),
            }
        }
    }
    let crates = workspace_crates();
    for (file, helper, token) in PRIVATE_ADMITTING {
        let source = std::fs::read_to_string(crates.join("trust-cg-codegen/src").join(file))
            .expect("read private helper source");
        let start = source
            .find(&format!("fn {helper}("))
            .ok_or_else(|| format!("{file}: fn {helper} not found"))?;
        let brace = start + source[start..].find('{').expect("fn body");
        let body = &source[brace..matching(source.as_bytes(), brace, b'{', b'}')];
        if !body.contains(token) {
            return Err(format!("{file}::{helper} no longer calls {token}"));
        }
    }
    chains_reach_admission(&PRIVATE_ADMITTING)
}

/// Each helper chain of `helpers` ends at a [`CHAIN_ENDS`] token, with no
/// cycle: a helper whose token names another helper must reach an end.
fn chains_reach_admission(helpers: &[(&str, &str, &str)]) -> Result<(), String> {
    for (file, helper, _) in helpers {
        let mut seen = BTreeSet::new();
        let mut current = *helper;
        loop {
            if !seen.insert(current) {
                return Err(format!("{file}::{helper}: the admission chain cycles"));
            }
            let Some((_, _, token)) = helpers
                .iter()
                .find(|(f, name, _)| f == file && *name == current)
            else {
                return Err(format!("{file}::{current}: not a listed admitting helper"));
            };
            if CHAIN_ENDS.contains(token) {
                break;
            }
            let Some(next) = token.strip_suffix('(') else {
                return Err(format!("{file}::{current}: token {token} is not a call"));
            };
            current = next;
        }
    }
    Ok(())
}

#[test]
fn every_ingestion_entry_reaches_admission() {
    let classification = classification();
    let entries = discovered_entries();
    let mut failures = Vec::new();
    let mut seen = BTreeSet::new();
    for entry in &entries {
        seen.insert(entry.key.clone());
        if let Err(failure) = judge(entry, classification.get(entry.key.as_str()).copied()) {
            failures.push(failure);
        }
    }
    for key in classification.keys() {
        if !seen.contains(*key) {
            failures.push(format!(
                "{key}: classified but no longer a public entry — delete its row"
            ));
        }
    }
    if let Err(failure) = route_targets_admit(&classification) {
        failures.push(failure);
    }
    if let Err(failure) = diagnostic_rows_are_the_baseline(&classification) {
        failures.push(failure);
    }
    assert!(failures.is_empty(), "{failures:#?}");
    // The two lanes this increment closed are discovered by the scan (it is
    // not vacuous).
    for key in [
        "compiler.rs::compile",
        "lower.rs::compile_module_with_policy",
    ] {
        assert!(seen.contains(key), "scan did not discover {key}");
    }
}

/// The scanner's negative twins: a new public entry that skips admission, an
/// `Admits` entry whose admission was deleted, and a diagnostic entry that a
/// route now depends on are each reported.
#[test]
fn every_ingestion_entry_reaches_admission_negative_twins() {
    let source = "use trust_ir::Module;\n\
        pub fn compile_new_lane(module: &trust_ir::Module) -> u8 { lower(module) }\n\
        pub fn compile_admitting(module: &trust_ir::Module) -> u8 { \
            let a = admit_module(module, &p)?; lower(a) }\n\
        pub fn compile_other(x: u8) -> u8 { x }\n";
    let entries = entries_in("fake.rs", source);
    let keys: Vec<&str> = entries.iter().map(|entry| entry.key.as_str()).collect();
    assert_eq!(
        keys,
        ["fake.rs::compile_new_lane", "fake.rs::compile_admitting"]
    );
    assert!(
        judge(&entries[0], None).is_err(),
        "an unclassified entry fails"
    );
    assert!(
        judge(&entries[0], Some(Held::Admits)).is_err(),
        "a non-admitting Admits fails"
    );
    assert!(judge(&entries[1], Some(Held::Admits)).is_ok());
    assert!(
        judge(&entries[1], Some(Held::Diagnostic("x"))).is_err(),
        "an admitting entry left in the allowlist fails (shrink-only)"
    );
    assert!(
        judge(
            &entries[0],
            Some(Held::RoutesThrough(&["compile_admitting"]))
        )
        .is_err()
    );

    // A helper chain must end at the admission: a cycle, and a chain that
    // ends at a helper this list does not name, are both reported.
    assert!(chains_reach_admission(&PRIVATE_ADMITTING).is_ok());
    assert!(
        chains_reach_admission(&[("x.rs", "lane_a", "lane_b("), ("x.rs", "lane_b", "lane_a("),])
            .is_err(),
        "a cyclic chain never reaches admission"
    );
    assert!(
        chains_reach_admission(&[("x.rs", "lane_a", "lower_without_admission(")]).is_err(),
        "a chain ending at an unlisted helper fails"
    );

    // The allowlist is shrink-only: a new Diagnostic row fails, and so does a
    // baseline key whose row left the allowlist.
    assert!(diagnostic_rows_are_the_baseline(&classification()).is_ok());
    let mut grown = classification();
    grown.insert("fake.rs::compile_new_lane", Held::Diagnostic("x"));
    assert!(
        diagnostic_rows_are_the_baseline(&grown).is_err(),
        "a new Diagnostic row fails"
    );
    let mut shrunk = classification();
    shrunk.insert("adapter.rs::translate_function", Held::Admits);
    assert!(
        diagnostic_rows_are_the_baseline(&shrunk).is_err(),
        "a stale baseline line fails"
    );

    let mut routed = classification();
    routed.insert(
        "compiler.rs::compile",
        Held::RoutesThrough(&["translate_module_for_arch"]),
    );
    assert!(
        route_targets_admit(&routed).is_err(),
        "a route through a diagnostic entry fails"
    );
}
