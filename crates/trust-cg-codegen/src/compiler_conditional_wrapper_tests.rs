//! Historical original TY Core replay against the current backend.
//! This does not reconstruct TY's checked source owner or prove providers.
use super::*;
use crate::compiler::{CompilerConfig, JitValidationMode};
use crate::*;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs::File;
use std::io::Read;
use std::path::Path;
use trust_ir::ProofDigest;
const FIXTURE: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../reports/2026-11-12-original-e1-machine/fixture"
);
const MAX_FIXTURE_BYTES: usize = 16 * 1024 * 1024;

pub(super) fn emit_local_materialization_queries(
    consumer: &str,
    observed: &trust_cg_verify::source_bound_frame::NativeAggregateTargetObservations,
) {
    emit_provider_footprint_queries(consumer, observed);
    let rows = observed.local_materialization_queries().unwrap();
    assert_eq!(rows.len(), 1);
    for row in rows {
        assert_eq!(row.call().outstanding_requirements().len(), 6);
        let mut premises = row.obligations()[0].clone();
        premises.trust_ir_expr = trust_cg_verify::smt::SmtExpr::BoolConst(false);
        let mut missing_relation = row.obligations()[0].clone();
        missing_relation.trust_ir_expr = row
            .source_event()
            .continuation_guard()
            .clone()
            .not_expr()
            .or_expr(row.loads()[0].guard.clone().not_expr())
            .or_expr(
                row.loads()[0]
                    .value
                    .clone()
                    .eq_expr(row.source_event().record().fields()[0].clone()),
            );
        let queries = row
            .obligations()
            .iter()
            .map(|q| (q, "local", "unsat"))
            .chain([
                (&premises, "premises_satisfiable", "sat"),
                (&missing_relation, "missing_source_product_relation", "sat"),
            ]);
        let mapped = observed
            .materializations()
            .iter()
            .find(|m| m.plan().intent() == row.call().intent())
            .unwrap();
        for (index, (obligation, kind, expected)) in queries.enumerate() {
            let query = trust_cg_verify::ay_bridge::generate_smt2_query_raw(
                obligation,
                &trust_cg_verify::ay_bridge::AYConfig {
                    solver: None,
                    timeout_ms: 30_000,
                    produce_models: true,
                },
            );
            println!(
                "ACTUAL_AGGREGATE_LOCAL_QUERY={}",
                serde_json::json!({
                    "consumer": consumer, "index": index, "query": query,
                    "kind": kind, "expected": expected,
                    "bytes": query.len(), "sha256": format!("{:x}", Sha256::digest(query.as_bytes())),
                    "caller": row.source_event().intent().caller().index(),
                    "source_origin": format!("{:?}", row.source_event().intent().source_origin()),
                    "callee": row.call().intent().callee().index(),
                    "binding": format!("{:?}", row.call().binding()),
                    "source_type": row.source_event().record().layout().source_type().index(),
                    "module_digest": format!("{:?}", observed.original_module_digest()),
                    "retained_function_digest": format!("{:x?}", observed.retained_function_digest()),
                    "call_id": format!("{:?}", mapped.call()),
                    "store_ids": format!("{:?}", mapped.stores()),
                    "field_load_ids": mapped.fields().iter().map(|f| format!("{:?}", f.load())).collect::<Vec<_>>(),
                    "normality_assumed": false, "geometry_assumed": false,
                    "provider_relation_assumed": false, "six_pending": true,
                    "complete_body": false, "native_credit": false,
                })
            );
        }
    }
}

fn emit_provider_footprint_queries(
    consumer: &str,
    observed: &trust_cg_verify::source_bound_frame::NativeAggregateTargetObservations,
) {
    use trust_cg_verify::smt::SmtExpr as E;
    use trust_cg_verify::source_bound_frame::NativeProviderWriteRegion;
    let regions = [NativeProviderWriteRegion::new(
        E::var("provider_write_start", 64),
        E::var("provider_write_bytes", 64),
    )
    .unwrap()];
    for call in observed.calls() {
        let required = observed
            .provider_footprint_requirements(call.site(), &regions)
            .unwrap();
        // This numeric interval is deliberately UNBOUND to a physical caller
        // frame here. The original 80-byte native frame remains unchanged and
        // unproved; provider and geometry requirements are not a replacement.
        let framing = required
            .conditional_framing_obligation(E::var("provider_saved_start", 64), 80)
            .unwrap();
        let mut missing = framing.clone();
        missing.preconditions.pop();
        let mut outcome = framing.clone();
        outcome.preconditions = observed
            .source()
            .definitions()
            .iter()
            .chain(observed.definitions())
            .cloned()
            .collect();
        outcome.trust_ir_expr = required.required_outcome_relation().clone();
        let mut registers = outcome.clone();
        registers.trust_ir_expr = required.required_register_preservation().clone();
        let mut footprint = outcome.clone();
        footprint.trust_ir_expr = required.required_outside_byte_relation().clone();
        for (kind, obligation, expected) in [
            ("conditional_frame", framing, "unsat"),
            ("missing_footprint_law", missing, "sat"),
            ("required_complete_outcome", outcome, "sat"),
            ("required_register_preservation", registers, "sat"),
            ("required_native_footprint", footprint, "sat"),
        ] {
            let query = trust_cg_verify::ay_bridge::generate_smt2_query_raw(
                &obligation,
                &trust_cg_verify::ay_bridge::AYConfig {
                    solver: None,
                    timeout_ms: 30_000,
                    produce_models: true,
                },
            );
            println!(
                "NATIVE_PROVIDER_FOOTPRINT_QUERY={}",
                serde_json::json!({
                    "consumer": consumer, "kind": kind, "expected": expected,
                    "query": query, "source_function": call.intent().callee().index(),
                    "binding": format!("{:?}",call.binding()), "site": format!("{:?}",call.site()),
                    "result_lanes": required.source_event().record().fields().len(),
                    "gpr_sp_lanes": call.before_registers().len(),
                    "provider_effects_proved": false,"frame_coordinate_bound":false,
                    "whole_body":false,"native_credit":false,
                })
            );
        }
    }
}
#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Identities {
    schema: String,
    core_tmbc_sha256: String,
    imports_sha256: String,
    frontend_dag_sha256: String,
    core_dag_sha256: String,
    module_digest: ProofDigest,
    manifest_digest: ProofDigest,
    target_info: trust_ir::TargetInfo,
    plan_digest: ProofDigest,
    retained_lir_digest: ProofDigest,
    function_names: Vec<String>,
    import_symbols: Vec<String>,
    entry_symbols: Vec<String>,
    strict_function_count: usize,
    exact_module_call_count: usize,
    declared_external_call_count: usize,
    frontend_micro_checked: bool,
    core_micro_checked: bool,
}

// Mirror only the serialized fixture's data. Reconstruct all sealed import
// values through their existing fallible constructors, never Deserialize them.
#[derive(Deserialize)]
enum ImportData {
    Function(FunctionImportData),
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct FunctionImportData {
    symbol: String,
    signature: trust_ir::FuncTy,
    calling_conv: trust_ir::CallingConv,
    parameter_attrs: Vec<trust_ir::ParamAttrs>,
    effects: EffectsData,
    implementation_contract_version: String,
    runtime: RuntimeData,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct EffectsData {
    memory: MemoryData,
    may_unwind: bool,
    may_not_return: bool,
    determinism: DeterminismData,
}

#[derive(Deserialize)]
enum MemoryData {
    None,
    ReadOnly,
    ReadWrite,
}

#[derive(Deserialize)]
enum DeterminismData {
    Deterministic,
    Nondeterministic,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RuntimeData {
    provider: String,
    binary_digest: ProofDigest,
}

fn read_fixture(name: &str) -> Vec<u8> {
    let path = Path::new(FIXTURE).join(name);
    let mut bytes = Vec::new();
    File::open(&path)
        .unwrap_or_else(|error| panic!("open {}: {error}", path.display()))
        .take((MAX_FIXTURE_BYTES + 1) as u64)
        .read_to_end(&mut bytes)
        .expect("bounded fixture read");
    assert!(bytes.len() <= MAX_FIXTURE_BYTES, "oversized fixture {name}");
    bytes
}

fn check_hash(bytes: &[u8], expected: &str, name: &str) {
    assert!(
        expected.len() == 64
            && expected
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)),
        "invalid SHA256 for {name}"
    );
    assert_eq!(
        format!("{:x}", Sha256::digest(bytes)),
        expected,
        "{name} bytes changed"
    );
}

fn load_fixture() -> (Identities, trust_ir::Module, CoreDeclaredImportManifest) {
    let identities: Identities = serde_json::from_slice(&read_fixture("identities.json")).unwrap();
    assert_eq!(identities.schema, "ty.checked-core-machine-input.v1");
    let bytes = read_fixture("core.tmbc");
    check_hash(&bytes, &identities.core_tmbc_sha256, "core.tmbc");
    let module = crate::pipeline::decode_tmbc(&bytes).expect("exact Core fixture must decode");
    assert_eq!(
        crate::pipeline::encode_tmbc(&module).unwrap(),
        bytes,
        "lossless Core roundtrip"
    );
    assert_eq!(module.stable_digest(), identities.module_digest);
    assert_eq!(module.target_info.as_ref(), Some(&identities.target_info));
    assert_eq!(
        module
            .functions
            .iter()
            .filter(|f| !f.blocks.is_empty())
            .map(|f| &f.name)
            .collect::<Vec<_>>(),
        identities.function_names.iter().collect::<Vec<_>>()
    );
    assert!(!identities.entry_symbols.is_empty());
    // Source roots are ordered occurrences, not a set of exports: Yes/No/Yes
    // deliberately repeats the first symbol. Preserve every occurrence.
    for entry in &identities.entry_symbols {
        assert!(
            identities.function_names.contains(entry),
            "missing entry {entry}"
        );
    }
    for (name, hash) in [
        ("frontend.dag-v2", &identities.frontend_dag_sha256),
        ("core.dag-v2", &identities.core_dag_sha256),
    ] {
        check_hash(&read_fixture(name), hash, name);
    }
    let imports_bytes = read_fixture("imports.json");
    check_hash(&imports_bytes, &identities.imports_sha256, "imports.json");
    let rows: Vec<ImportData> = serde_json::from_slice(&imports_bytes).unwrap();
    let imports = rows
        .into_iter()
        .map(|ImportData::Function(row)| {
            let effects = CoreHostFunctionEffects {
                memory: match row.effects.memory {
                    MemoryData::None => CoreHostMemoryEffect::None,
                    MemoryData::ReadOnly => CoreHostMemoryEffect::ReadOnly,
                    MemoryData::ReadWrite => CoreHostMemoryEffect::ReadWrite,
                },
                may_unwind: row.effects.may_unwind,
                may_not_return: row.effects.may_not_return,
                determinism: match row.effects.determinism {
                    DeterminismData::Deterministic => CoreHostDeterminism::Deterministic,
                    DeterminismData::Nondeterministic => CoreHostDeterminism::Nondeterministic,
                },
            };
            CoreHostImport::Function(
                CoreHostFunctionImport::try_new(
                    row.symbol,
                    row.signature,
                    row.calling_conv,
                    row.parameter_attrs,
                    effects,
                    row.implementation_contract_version,
                    CoreRuntimeIdentity::try_new(row.runtime.provider, row.runtime.binary_digest)
                        .unwrap(),
                )
                .unwrap(),
            )
        })
        .collect();
    let manifest = CoreDeclaredImportManifest::try_new(imports).unwrap();
    assert_eq!(manifest.digest(), identities.manifest_digest);
    assert_eq!(
        serde_json::to_value(manifest.imports()).unwrap(),
        serde_json::from_slice::<serde_json::Value>(&imports_bytes).unwrap(),
        "checked constructors must preserve the exact fixture imports"
    );
    assert_eq!(
        manifest
            .imports()
            .iter()
            .map(CoreHostImport::symbol)
            .collect::<Vec<_>>(),
        identities
            .import_symbols
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>()
    );
    (identities, module, manifest)
}

#[test]
fn conditional_wrapper_original_core_plan_retains_complete_call_provider_census() {
    let (identities, module, manifest) = load_fixture();
    let target = CoreHostJitTarget::detect().expect("actual ARM64/macOS host");
    assert_eq!(target.trust_ir_target_info(), &identities.target_info);
    let core = admit_identity_core_module_for_host_jit(module, &target, manifest).unwrap();
    let mut config = CompilerConfig::for_host_jit();
    config.emit_proofs = true;
    config.jit_validation_mode_override = Some(JitValidationMode::AlwaysVerify);
    config.jit_external_symbol_resolution = JitExternalSymbolResolutionPolicy::ExplicitOnly;
    let compiler = Compiler::new_for_target_spec(config, target.target_spec())
        .with_codegen_license(
            CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit),
        );
    let plan = compiler.plan_core_module_for_jit_compilation(core).unwrap();
    assert_eq!(plan.retained_strict_function_count(), 6);
    assert_eq!(plan.retained_exact_module_call_count(), 4);
    assert_eq!(plan.retained_declared_external_call_count(), 10);
    assert_eq!(plan.native_runtime_catalog().entries().len(), 6);
    assert_eq!(plan.lir_native_dependency_bindings().entries().len(), 10);
    let aggregate = plan
        .inspect_aggregate_result_transports()
        .expect("original aggregate transport through ordinary sealed-Core selector");
    assert_eq!(aggregate.plan_identity(), plan.identity());
    assert_eq!(
        aggregate.retained_lir_proof_context_digest(),
        plan.retained_lir_proof_context_digest()
    );
    let aggregate_calls = aggregate
        .functions()
        .iter()
        .map(|f| f.materializations().len())
        .sum::<usize>();
    let aggregate_fields = aggregate
        .functions()
        .iter()
        .map(|f| f.fields().len())
        .sum::<usize>();
    assert_eq!(aggregate_calls, 10);
    assert_eq!(aggregate_fields, 20);
    let observed = plan
        .observe_native_aggregate_source_events("tla_def_0")
        .unwrap();
    let target = plan
        .observe_native_aggregate_target_events("tla_def_0")
        .unwrap();
    assert_eq!(target.plan_identity(), plan.identity());
    let target = target.target();
    assert_eq!(target.calls().len(), 1);
    assert_eq!(target.calls()[0].intent().callee().index(), 4);
    assert_eq!(target.accesses().iter().filter(|a| a.load).count(), 2);
    assert_eq!(target.accesses().iter().filter(|a| !a.load).count(), 2);
    assert_eq!(target.calls()[0].outstanding_requirements().len(), 6);
    emit_local_materialization_queries("original_e1_tla_def_0", target);
    println!(
        "ORIGINAL_E1_NATIVE_AGGREGATE_TARGET calls=1 reads=2 writes=2 frontier={:?} source_function=4 dependency=1 Struct=0 preoptimization_only=true all_six_pending=true complete_body=false native_credit=false",
        target.frontier()
    );
    assert_eq!(observed.plan_identity(), plan.identity());
    let first = &observed.source_events().events()[0];
    assert_eq!(first.intent().callee().index(), 4);
    assert_eq!(first.intent().layout().source_type().index(), 0);
    assert!(
        matches!(first.binding(), trust_cg_lower::instructions::DirectCallBinding::NativeDependency { function: 4, dependency } if dependency.index() == 1)
    );
    assert_ne!(first.prior_world(), first.post_world());
    assert_eq!(
        observed.source_events().first_retained_field_load(),
        Some(trust_cg_verify::source_bound_frame::ReadOnlySite {
            block: 0,
            instruction: 2
        })
    );
    println!(
        "ORIGINAL_E1_NATIVE_AGGREGATE_SOURCE events={} first_function=4 first_dependency=1 Struct=0 first_normal={:?} first_post_world={:?} target_load={:?} target_frontier={} body_proof=false native_credit=false",
        observed.source_events().events().len(),
        first.returned_normally(),
        first.post_world(),
        observed.source_events().first_retained_field_load(),
        observed.source_events().retained_field_load_frontier()
    );
    for function in aggregate.functions() {
        for value in function.materializations() {
            assert_eq!(value.plan().unresolved_requirements().len(), 6);
            println!(
                "ORIGINAL_E1_AGGREGATE_TRANSPORT function={} caller={} callee={} source={:?} binding={:?} slot={} call={:?} stores={:?} unsolved={:?} body_proof=false native_credit=false",
                function.name(),
                function.caller().index(),
                value.plan().intent().callee().index(),
                value.plan().intent().source_origin(),
                value.plan().binding(),
                value.plan().slot(),
                value.call(),
                value.stores(),
                value.plan().unresolved_requirements()
            );
        }
    }
    println!(
        "CONDITIONAL_WRAPPER_PLAN={}",
        serde_json::json!({
            "module_digest":plan.module_digest(),"manifest_digest":plan.declared_import_manifest().digest(),
            "plan_digest":plan.identity().full_digest(),"retained_lir_proof_context_digest":plan.retained_lir_proof_context_digest(),
            "native_catalog_digest":plan.native_runtime_catalog().digest(),"native_bindings_digest":plan.lir_native_dependency_bindings().digest(),
            "historical_plan_digest":identities.plan_digest,"historical_retained_lir_digest":identities.retained_lir_digest,
            "entry_occurrences":identities.entry_symbols,
        })
    );
    let original_lir: serde_json::Value = serde_json::from_str(include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reports/2026-11-12-original-e1-conditional-wrappers/retained-lir-comparison.json"
    )))
    .unwrap();
    for (function, context) in &plan.parts.lir_functions {
        let mut canonical = String::new();
        function
            .write_canonical_verifier_identity(&mut canonical)
            .unwrap();
        let previous = original_lir
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["name"].as_str() == Some(function.name.as_str()))
            .unwrap();
        assert_eq!(
            format!("{:x}", Sha256::digest(canonical.as_bytes())),
            previous["current_sha256"].as_str().unwrap(),
            "complete original retained LIR changed for {}",
            function.name
        );
        println!(
            "CONDITIONAL_WRAPPER_RETAINED_LIR={}\n{}",
            function.name, canonical
        );
        println!(
            "CONDITIONAL_WRAPPER_RETAINED_CONTEXT={} {context:#?}",
            function.name
        );
    }
    println!(
        "CONDITIONAL_WRAPPER_NATIVE_CATALOG={:#?}",
        plan.native_runtime_catalog()
    );
    let module = &plan.parts.module;
    let lir = plan
        .parts
        .lir_functions
        .iter()
        .map(|(f, _)| f.clone())
        .collect::<Vec<_>>();
    let custody =
        trust_cg_verify::source_bound_frame::PendingCalleeRelations::capture(module, &lir).unwrap();
    for name in ["tla_def_0", "tla_def_1"] {
        let ordinal = module
            .functions
            .iter()
            .position(|f| f.name == name)
            .unwrap();
        let retained = lir.iter().find(|f| f.name == name).unwrap();
        let projection = trust_cg_verify::source_bound_frame::check_scalar_block_arguments(
            module, ordinal, retained,
        )
        .unwrap();
        let edges = projection
            .transports()
            .iter()
            .filter(|e| !e.source_arguments.is_empty())
            .collect::<Vec<_>>();
        assert_eq!(edges.len(), 1);
        assert_eq!(edges[0].source_arguments.len(), 5);
        assert_eq!(edges[0].copy_instructions.len(), 5);
        println!(
            "ORIGINAL_E1_PLAN_SCALAR_EDGE {name} copies=5 functions=6 exact_calls=4 external_calls=10 providers=6 body_proof=false native_credit=false"
        );
        let next = trust_cg_verify::source_bound_frame::bind_scalar_return_source(
            module, ordinal, retained,
        )
        .err()
        .unwrap();
        assert_eq!(
            next,
            trust_cg_verify::source_bound_frame::ReadOnlySourceError::Source(
                "scalar-return calls require a checked callee/aggregate ABI owner",
            )
        );
        println!(
            "ORIGINAL_E1_PLAN_SCALAR_RETURN {name} returns=5 functions=6 exact_calls=4 external_calls=10 providers=6 refusal={next} body_proof=false native_credit=false"
        );
    }
    for name in &identities.entry_symbols {
        let index = module
            .functions
            .iter()
            .position(|f| &f.name == name)
            .unwrap();
        let queries = trust_cg_verify::source_bound_frame::bind_conditional_wrapper_source(
            module,
            index,
            &lir,
            Some(&custody),
        )
        .unwrap();
        assert_eq!(queries.source_writes().len(), 5);
        assert_eq!(queries.outstanding_relations()[0].result_codecs.len(), 5);
        println!(
            "CONDITIONAL_WRAPPER_ORDINARY entry={name} functions=6 exact_calls=4 external_calls=10 providers=6 pending_relation_lanes=5 conditional_queries={}",
            queries.conditional_obligations().len()
        );
    }
    // The diagnostic query borrow cannot qualify or replace the plan. All
    // ordinary verification requirements are still checked by this transition.
    let _unchanged_policy = plan.qualify_for_proof_grade_compilation().unwrap();
}
