// Copyright 2026 Andrew Yates | Apache-2.0
//! Source/catalog-bound aggregate materialization transport. No execution,
//! provider refinement, conditional theorem or private-memory authority.

use super::*;
use crate::core_admission::CoreHostImport;
use trust_cg_lower::aggregate_call_transport::{
    AggregateFieldIntent, MappedAggregateMaterialization,
};

#[cfg(all(test, feature = "verify", target_arch = "aarch64", target_os = "macos"))]
#[path = "compiler_aggregate_transport_tests.rs"]
mod tests;

// The canonical observed identity owns payload traversal and recursion. Admit
// the complete original module BEFORE the existing plan replay hashes it;
// unrelated bodies/attributes/constants cannot hide work outside local intent
// limits. These are the existing pending-query inventory bounds, not solver
// policy or semantic assumptions.
fn preflight_original(module: &trust_ir::Module) -> Result<(), CoreAggregateResultTransportError> {
    use trust_ir::interpret::{
        ExecutionObserver, ExecutionProgress, ExecutionSite, InterpretOptions, ObservedSession,
    };
    struct Inventory {
        work: usize,
        bytes: usize,
    }
    impl ExecutionObserver for Inventory {
        type Refusal = ();
        fn admit(&mut self, p: ExecutionProgress) -> Result<(), ()> {
            self.work = self
                .work
                .checked_add(p.work)
                .filter(|n| *n <= 262_144)
                .ok_or(())?;
            self.bytes = self
                .bytes
                .checked_add(p.copy_bytes)
                .filter(|n| *n <= 4 * 1024 * 1024)
                .ok_or(())?;
            Ok(())
        }
    }
    if module.functions.len() > 384 || module.func_types.len() > 384 {
        return Err(CoreAggregateResultTransportError::Binding(
            "aggregate complete original inventory",
        ));
    }
    let mut inventory = Inventory { work: 0, bytes: 0 };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut inventory);
    module
        .checked_stable_digest_observed(
            &mut session,
            ExecutionSite::Entry(trust_ir::FuncId::new(0)),
        )
        .map_err(|_| {
            CoreAggregateResultTransportError::Binding("aggregate complete original inventory")
        })?;
    Ok(())
}

#[derive(Debug, thiserror::Error)]
pub enum CoreAggregateResultTransportError {
    #[cfg(feature = "verify")]
    #[error(transparent)]
    SourceObservation(#[from] trust_cg_verify::source_bound_frame::ReadOnlySourceError),
    #[error(transparent)]
    Integrity(#[from] crate::core_admission::CoreJitPlanIntegrityError),
    #[error(transparent)]
    Pipeline(#[from] PipelineError),
    #[error("aggregate transport requires the admitted ARM64/Darwin profile")]
    Target,
    #[error("aggregate transport binding refused: {0}")]
    Binding(&'static str),
    #[error("aggregate transport environment changed or cannot be retained")]
    Environment,
}

/// Source-event observations borrowed through the real sealed plan boundary.
/// Catalog identity is checked; provider behavior and storage remain unproved.
#[cfg(feature = "verify")]
pub struct CoreNativeAggregateSourceEvents {
    plan: CoreJitPlanIdentity,
    events: trust_cg_verify::source_bound_frame::NativeAggregateSourceEvents,
}
/// Pending actual preoptimization target interval. No provider/storage proof,
/// complete-body or native conversion is supplied by retaining these effects.
#[cfg(feature = "verify")]
pub struct CoreNativeAggregateTargetEvents {
    plan: CoreJitPlanIdentity,
    target: trust_cg_verify::source_bound_frame::NativeAggregateTargetObservations,
}
#[cfg(feature = "verify")]
impl CoreNativeAggregateTargetEvents {
    pub fn plan_identity(&self) -> CoreJitPlanIdentity {
        self.plan
    }
    pub fn target(
        &self,
    ) -> &trust_cg_verify::source_bound_frame::NativeAggregateTargetObservations {
        &self.target
    }
}
#[cfg(feature = "verify")]
impl CoreNativeAggregateSourceEvents {
    pub fn plan_identity(&self) -> CoreJitPlanIdentity {
        self.plan
    }
    pub fn source_events(
        &self,
    ) -> &trust_cg_verify::source_bound_frame::NativeAggregateSourceEvents {
        &self.events
    }
}

#[cfg(feature = "verify")]
impl PolicyQualifiedCoreJitCompilationPlan {
    /// Observe the same retained original source and preoptimization interval
    /// after policy qualification or a recovered machine refusal. This does
    /// not expose/peel the raw plan, reset a proof budget, or grant provider,
    /// complete-body, storage or native authority.
    pub fn observe_native_aggregate_target_events(
        &self,
        function: &str,
    ) -> Result<CoreNativeAggregateTargetEvents, CoreAggregateResultTransportError> {
        self.plan.observe_native_aggregate_target_events(function)
    }
}

/// One original function's independently rechecked pre-optimization transport.
/// The private constructor checks actual source, LIR, selector and arena data.
/// The public rows remain coordinates and UNSOLVED requirements, not a buffer
/// lease, proof of input equivalence, callee relation, or machine certificate.
#[derive(Debug)]
pub struct CoreAggregateResultFunction {
    caller: trust_ir::FuncId,
    name: String,
    fields: Vec<AggregateFieldIntent>,
    materializations: Vec<MappedAggregateMaterialization>,
}

impl CoreAggregateResultFunction {
    pub fn caller(&self) -> trust_ir::FuncId {
        self.caller
    }
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn fields(&self) -> &[AggregateFieldIntent] {
        &self.fields
    }
    pub fn materializations(&self) -> &[MappedAggregateMaterialization] {
        &self.materializations
    }
}

/// Pending transport inventory for the complete retained Core plan. This
/// exposes no raw source/LIR, addresses, machine function or executable bytes.
/// There is intentionally no Checked/SourceBoundReplay/installation conversion.
#[derive(Debug)]
pub struct CoreAggregateResultTransports {
    plan: CoreJitPlanIdentity,
    retained: trust_ir::proof::ProofDigest,
    functions: Vec<CoreAggregateResultFunction>,
}

impl CoreAggregateResultTransports {
    pub fn plan_identity(&self) -> CoreJitPlanIdentity {
        self.plan
    }
    pub fn retained_lir_proof_context_digest(&self) -> trust_ir::proof::ProofDigest {
        self.retained
    }
    pub fn functions(&self) -> &[CoreAggregateResultFunction] {
        &self.functions
    }
}

impl CoreJitCompilationPlan {
    /// Reauthenticate the complete real plan, then observe only its explicitly
    /// delimited preoptimization target entry interval. No source/target
    /// outcomes or worlds are equated; all six requirements remain pending.
    #[cfg(feature = "verify")]
    pub fn observe_native_aggregate_target_events(
        &self,
        function: &str,
    ) -> Result<CoreNativeAggregateTargetEvents, CoreAggregateResultTransportError> {
        if function.len() > 4096 {
            return Err(CoreAggregateResultTransportError::Binding(
                "native target function name limit",
            ));
        }
        let transports = self.inspect_aggregate_result_transports()?;
        let permit = trust_cg_process_env::artifact_reuse_permit()
            .ok_or(CoreAggregateResultTransportError::Environment)?;
        if transports
            .functions()
            .iter()
            .filter(|f| f.name() == function)
            .count()
            != 1
        {
            return Err(CoreAggregateResultTransportError::Binding(
                "missing or ambiguous native target function",
            ));
        }
        let (lir, context) = self
            .parts
            .lir_functions
            .iter()
            .find(|(f, _)| f.name == function)
            .ok_or(CoreAggregateResultTransportError::Binding(
                "missing native target retained function",
            ))?;
        let profile = self
            .effective_options
            .machine_profile
            .aarch64()
            .ok_or(CoreAggregateResultTransportError::Target)?;
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level: self.effective_options.compiler_config.opt_level,
            target_triple: self.effective_options.target_spec.triple(),
            ..PipelineConfig::default()
        })
        .with_aarch64_isa_profile(profile)
        .with_raw_dataflow_policy(Aarch64DataflowIntegrityPolicy::ProofGradeEnforce);
        let (selected, machine, mapped) =
            pipeline.select_aggregate_transports_for_sealed_core(lir, context)?;
        let target = trust_cg_verify::source_bound_frame::observe_native_aggregate_target(
            &self.parts.module,
            lir,
            &context.aggregate_call_intents,
            &selected,
            &machine,
            &mapped,
        )?;
        if !permit.is_valid() {
            return Err(CoreAggregateResultTransportError::Environment);
        }
        Ok(CoreNativeAggregateTargetEvents {
            plan: self.identity,
            target,
        })
    }
    /// Observe one complete original function in the bounded native-event
    /// source profile. This reuses actual catalog/retained reauthentication;
    /// it does not interpret the retained aggregate pointer or its loads.
    #[cfg(feature = "verify")]
    pub fn observe_native_aggregate_source_events(
        &self,
        function: &str,
    ) -> Result<CoreNativeAggregateSourceEvents, CoreAggregateResultTransportError> {
        if function.len() > 4096 {
            return Err(CoreAggregateResultTransportError::Binding(
                "native aggregate function name limit",
            ));
        }
        let transport = self.inspect_aggregate_result_transports()?;
        if transport
            .functions()
            .iter()
            .filter(|f| f.name() == function)
            .count()
            != 1
        {
            return Err(CoreAggregateResultTransportError::Binding(
                "missing or ambiguous native aggregate source function",
            ));
        }
        let ordinal = self
            .parts
            .module
            .functions
            .iter()
            .position(|f| f.name == function)
            .ok_or(CoreAggregateResultTransportError::Binding(
                "missing native aggregate original function",
            ))?;
        let (lir, context) = self
            .parts
            .lir_functions
            .iter()
            .find(|(f, _)| f.name == function)
            .ok_or(CoreAggregateResultTransportError::Binding(
                "missing native aggregate retained function",
            ))?;
        let events = trust_cg_verify::source_bound_frame::observe_native_aggregate_source(
            &self.parts.module,
            ordinal,
            lir,
            &context.aggregate_call_intents,
        )?;
        Ok(CoreNativeAggregateSourceEvents {
            plan: self.identity,
            events,
        })
    }
    /// Reauthenticate the sealed Core source, actual import catalog/reference
    /// map, every direct-call occurrence and complete retained proof contexts;
    /// then run the ordinary sealed-Core selector and same arena conversion.
    ///
    /// This diagnostic supports only source C records of two scalar 64-bit
    /// fields. Unsupported shapes and incomplete capture refuse. Import effect
    /// and ABI declarations are not provider refinement. Each returned plan
    /// retains every required input/world, normality, storage, initialization
    /// and source/private-memory relation as OUTSTANDING. In particular an
    /// Unchecked predecessor remains non-executable after this borrow.
    pub fn inspect_aggregate_result_transports(
        &self,
    ) -> Result<CoreAggregateResultTransports, CoreAggregateResultTransportError> {
        preflight_original(&self.parts.module)?;
        crate::resource_limits::admit_compilation_budget().map_err(PipelineError::from)?;
        self.parts.check_planned_integrity(
            &self.native_runtime_catalog,
            &self.native_dependency_references,
            &self.lir_native_dependency_bindings,
        )?;
        self.parts
            .check_retained_lir_proof_context_integrity(self.retained_lir_proof_context_digest)?;
        if self.effective_options.target_spec.architecture != Target::Aarch64
            || self.effective_options.target_spec != self.parts.target_contract.target_spec()
            || self.effective_options.machine_profile
                != self.parts.target_contract.host_jit_machine_profile()
            || !self
                .effective_options
                .target_spec
                .triple()
                .contains("apple")
        {
            return Err(CoreAggregateResultTransportError::Target);
        }
        let permit = trust_cg_process_env::artifact_reuse_permit()
            .ok_or(CoreAggregateResultTransportError::Environment)?;
        let profile = self
            .effective_options
            .machine_profile
            .aarch64()
            .ok_or(CoreAggregateResultTransportError::Target)?;
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level: self.effective_options.compiler_config.opt_level,
            target_triple: self.effective_options.target_spec.triple(),
            ..PipelineConfig::default()
        })
        .with_aarch64_isa_profile(profile)
        .with_raw_dataflow_policy(Aarch64DataflowIntegrityPolicy::ProofGradeEnforce);
        let mut functions = Vec::new();
        for (ordinal, (lir, context)) in self.parts.lir_functions.iter().enumerate() {
            let intents = &context.aggregate_call_intents;
            let mut expected = 0usize;
            for binding in self
                .lir_native_dependency_bindings
                .entries()
                .iter()
                .filter(|b| b.lir_function() == ordinal)
            {
                let entry = self
                    .native_runtime_catalog
                    .entries()
                    .iter()
                    .find(|e| e.id() == binding.dependency())
                    .ok_or(CoreAggregateResultTransportError::Binding(
                        "missing aggregate catalog dependency",
                    ))?;
                let CoreHostImport::Function(import) = entry.import() else {
                    return Err(CoreAggregateResultTransportError::Binding(
                        "non-function aggregate catalog entry",
                    ));
                };
                if import.signature().returns.iter().any(|ty| {
                    !matches!(
                        ty,
                        trust_ir::Ty::I64 | trust_ir::Ty::U64 | trust_ir::Ty::Ptr
                    )
                }) {
                    expected += 1;
                    if !intents.calls().iter().any(|call| {
                        call.lir_block().0 == binding.block()
                            && call.lir_instruction() == binding.instruction()
                            && call.source_origin() == binding.source_origin()
                            && call.callee() == binding.imported_function()
                    }) {
                        return Err(CoreAggregateResultTransportError::Binding(
                            "unsupported or missing original aggregate call intent",
                        ));
                    }
                }
            }
            if expected != intents.calls().len() {
                return Err(CoreAggregateResultTransportError::Binding(
                    "aggregate source/catalog occurrence census differs",
                ));
            }
            intents
                .validate(&self.parts.module, lir)
                .map_err(CoreAggregateResultTransportError::Binding)?;
            if intents.calls().is_empty() {
                continue;
            }
            let (selected, machine, materializations) =
                pipeline.select_aggregate_transports_for_sealed_core(lir, context)?;
            if materializations.len() != intents.calls().len()
                || materializations
                    .iter()
                    .enumerate()
                    .any(|(index, value)| value.plan().intent() != &intents.calls()[index])
            {
                return Err(CoreAggregateResultTransportError::Binding(
                    "aggregate materialization occurrence census differs",
                ));
            }
            for value in &materializations {
                value
                    .validate(&self.parts.module, lir, intents, &selected, &machine)
                    .map_err(CoreAggregateResultTransportError::Binding)?;
            }
            functions.push(CoreAggregateResultFunction {
                caller: intents
                    .caller()
                    .ok_or(CoreAggregateResultTransportError::Binding(
                        "missing aggregate caller",
                    ))?,
                name: lir.name.clone(),
                fields: intents.fields().to_vec(),
                materializations,
            });
        }
        if !permit.is_valid() {
            return Err(CoreAggregateResultTransportError::Environment);
        }
        Ok(CoreAggregateResultTransports {
            plan: self.identity,
            retained: self.retained_lir_proof_context_digest,
            functions,
        })
    }
}
