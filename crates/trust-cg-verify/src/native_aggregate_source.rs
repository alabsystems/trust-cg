// Copyright 2026 Andrew Yates | Apache-2.0
//! Pending original Struct-valued native events in the existing graph driver.
//! No target load projection, provider refinement, permission or proof owner.
//! Byte arrays carry no initializedness, liveness or provenance facts. A false
//! normal flag leaves non-normal behavior opaque; it proves no totality claim.

use super::*;
use trust_cg_lower::aggregate_call_transport::{
    AggregateCallIntent, AggregateCallIntents, AggregateFieldCodec, FlatAggregateLayout,
};
use trust_cg_lower::instructions::DirectCallBinding;
use trust_ir::{Inst, Ty, ValueId};

#[cfg(test)]
#[path = "native_aggregate_source_tests.rs"]
pub(super) mod tests;

/// ONE typed source product, never a replacement scalar return signature.
#[derive(Clone, Debug)]
pub struct NativeAggregateRecord {
    layout: FlatAggregateLayout,
    fields: [E; 2],
}
impl NativeAggregateRecord {
    pub fn layout(&self) -> &FlatAggregateLayout {
        &self.layout
    }
    pub fn fields(&self) -> &[E; 2] {
        &self.fields
    }
}

#[derive(Clone)]
pub(super) struct RecordState {
    pub(super) layout: FlatAggregateLayout,
    pub(super) fields: [Term; 2],
}

/// The SAME six unresolved transport requirements; none is a permission.
pub use trust_cg_lower::aggregate_call_transport::AggregateTransportRequirement as NativeAggregateRequirement;

/// Independent source event outcomes, not assumptions or callee facts. The
/// numeric dependency binding is nominal until the sealed Core catalog owner
/// reauthenticates it; even that replay does not refine a runtime provider.
#[derive(Clone, Debug)]
pub struct PendingNativeAggregateEvent {
    pub(super) intent: AggregateCallIntent,
    pub(super) binding: DirectCallBinding,
    pub(super) site: ReadOnlySite,
    pub(super) guard: E,
    pub(super) arguments: Vec<E>,
    pub(super) before: E,
    pub(super) record: NativeAggregateRecord,
    pub(super) after: E,
    pub(super) normal: E,
    pub(super) continuation: E,
}
impl PendingNativeAggregateEvent {
    pub fn intent(&self) -> &AggregateCallIntent {
        &self.intent
    }
    pub fn binding(&self) -> DirectCallBinding {
        self.binding
    }
    pub fn site(&self) -> ReadOnlySite {
        self.site
    }
    pub fn guard(&self) -> &E {
        &self.guard
    }
    pub fn arguments(&self) -> &[E] {
        &self.arguments
    }
    pub fn prior_world(&self) -> &E {
        &self.before
    }
    pub fn record(&self) -> &NativeAggregateRecord {
        &self.record
    }
    pub fn post_world(&self) -> &E {
        &self.after
    }
    pub fn returned_normally(&self) -> &E {
        &self.normal
    }
    pub fn continuation_guard(&self) -> &E {
        &self.continuation
    }
    pub fn outstanding_requirements(&self) -> [NativeAggregateRequirement; 6] {
        use NativeAggregateRequirement::*;
        [
            MatchingInputsAndPriorWorld,
            RuntimeProviderAbiAndOutcomeRelation,
            NormalContinuation,
            LiveAlignedNonwrappingResultStorage,
            InitializationAndFieldLoadSemantics,
            SourcePrivateMemoryRelation,
        ]
    }
    pub(super) fn product(
        layout: FlatAggregateLayout,
        fields: &[Term; 2],
    ) -> NativeAggregateRecord {
        NativeAggregateRecord {
            layout,
            fields: fields.clone().map(|x| x.expr),
        }
    }
}

/// Complete bounded SOURCE observation only. Definitions describe the source
/// driver, not external relations. No target, complete-body query, Checked,
/// SourceBoundReplay, native or publication conversion exists.
pub struct NativeAggregateSourceEvents {
    module_digest: trust_ir::ProofDigest,
    retained_digest: [u8; 32],
    caller: trust_ir::FuncId,
    events: Vec<PendingNativeAggregateEvent>,
    definitions: Vec<E>,
    reads: Vec<scalar_memory::ScalarMemoryAccess>,
    writes: Vec<scalar_memory::ScalarMemoryAccess>,
    geometry: Vec<E>,
    terminal_guards: Vec<E>,
    terminal_worlds: Vec<E>,
    retained_load: Option<ReadOnlySite>,
}
impl NativeAggregateSourceEvents {
    pub fn original_module_digest(&self) -> trust_ir::ProofDigest {
        self.module_digest
    }
    pub fn retained_function_digest(&self) -> &[u8; 32] {
        &self.retained_digest
    }
    pub fn caller(&self) -> trust_ir::FuncId {
        self.caller
    }
    pub fn events(&self) -> &[PendingNativeAggregateEvent] {
        &self.events
    }
    pub fn definitions(&self) -> &[E] {
        &self.definitions
    }
    pub fn reads(&self) -> &[scalar_memory::ScalarMemoryAccess] {
        &self.reads
    }
    pub fn writes(&self) -> &[scalar_memory::ScalarMemoryAccess] {
        &self.writes
    }
    pub fn geometry(&self) -> &[E] {
        &self.geometry
    }
    pub fn normal_terminal_guards(&self) -> &[E] {
        &self.terminal_guards
    }
    pub fn normal_terminal_worlds(&self) -> &[E] {
        &self.terminal_worlds
    }
    /// Actual validated LIR coordinate, not a readability receipt.
    pub fn first_retained_field_load(&self) -> Option<ReadOnlySite> {
        self.retained_load
    }
    /// An applicability refusal, never a proof that private storage exists.
    pub fn retained_field_load_frontier(&self) -> ReadOnlySourceError {
        ReadOnlySourceError::Lowering(
            "native aggregate StructGep/Load requires live initialized result storage and source/private-world ownership",
        )
    }
}

pub(super) struct Bindings<'a> {
    pub(super) intents: &'a AggregateCallIntents,
    pub(super) lir: &'a Function,
}
impl Bindings<'_> {
    fn call(
        &self,
        block: u32,
        instruction: usize,
    ) -> Result<(&AggregateCallIntent, DirectCallBinding), ReadOnlySourceError> {
        let mut calls = self
            .intents
            .calls()
            .iter()
            .filter(|x| x.source_block() == block && x.source_instruction() == instruction);
        let call = calls.next().ok_or(ReadOnlySourceError::Source(
            "native aggregate source call lacks exact intent",
        ))?;
        if calls.next().is_some() {
            return Err(ReadOnlySourceError::Source(
                "duplicate native aggregate source call",
            ));
        }
        let actual = self
            .lir
            .blocks
            .get(&call.lir_block())
            .and_then(|b| b.instructions.get(call.lir_instruction()))
            .ok_or(ReadOnlySourceError::Lowering(
                "missing native aggregate call",
            ))?;
        let Opcode::Call {
            binding: binding @ DirectCallBinding::NativeDependency { function, .. },
            ..
        } = actual.opcode
        else {
            return Err(ReadOnlySourceError::Lowering(
                "native aggregate event requires a retained NativeDependency",
            ));
        };
        if function != call.callee().index() {
            return Err(ReadOnlySourceError::Lowering(
                "native aggregate callee differs",
            ));
        }
        Ok((call, binding))
    }
    fn field(
        &self,
        block: u32,
        instruction: usize,
    ) -> Result<(&AggregateCallIntent, usize), ReadOnlySourceError> {
        let mut fields = self
            .intents
            .fields()
            .iter()
            .filter(|x| x.source_block() == block && x.source_instruction() == instruction);
        let field = fields.next().ok_or(ReadOnlySourceError::Source(
            "native aggregate field lacks exact source intent",
        ))?;
        if fields.next().is_some() {
            return Err(ReadOnlySourceError::Source(
                "duplicate native aggregate field",
            ));
        }
        let call = self
            .intents
            .calls()
            .get(field.call())
            .ok_or(ReadOnlySourceError::Source(
                "foreign native aggregate field",
            ))?;
        Ok((call, field.field() as usize))
    }
    pub(super) fn result_type(
        &self,
        block: u32,
        instruction: usize,
        inst: &Inst,
    ) -> Option<Result<Ty, ReadOnlySourceError>> {
        match inst {
            Inst::Call { .. } => Some(
                self.call(block, instruction)
                    .map(|(c, _)| Ty::Struct(c.layout().source_type())),
            ),
            Inst::ExtractField { ty, .. } => {
                Some(self.field(block, instruction).map(|_| ty.clone()))
            }
            _ => None,
        }
    }
    pub(super) fn operation(
        &self,
        block: u32,
        instruction: usize,
        node: &trust_ir::InstrNode,
        values: &HashMap<ValueId, Ty>,
    ) -> Option<Result<Operation, ReadOnlySourceError>> {
        let refuse = || {
            ReadOnlySourceError::Source("native aggregate original argument/field codec differs")
        };
        match &node.inst {
            Inst::Call { args, .. } => Some((|| {
                let (intent, binding) = self.call(block, instruction)?;
                if args.len() != intent.argument_codecs().len()
                    || node.results.as_slice() != [intent.source_result()]
                {
                    return Err(refuse());
                }
                for (arg, codec) in args.iter().zip(intent.argument_codecs()) {
                    if values.get(arg).and_then(codec_source) != Some(*codec) {
                        return Err(refuse());
                    }
                }
                Ok(Operation::NativeAggregateCall {
                    intent: intent.clone(),
                    binding,
                    record: intent.source_result().index(),
                    args: args.iter().map(|v| v.index()).collect(),
                })
            })()),
            Inst::ExtractField { aggregate, ty, .. } => Some((|| {
                let (call, field) = self.field(block, instruction)?;
                if field >= 2
                    || values.get(aggregate) != Some(&Ty::Struct(call.layout().source_type()))
                    || codec_source(ty) != Some(call.layout().fields()[field])
                {
                    return Err(refuse());
                }
                Ok(Operation::AggregateField {
                    record: aggregate.index(),
                    layout: call.layout().clone(),
                    field,
                })
            })()),
            _ => None,
        }
    }
}
fn codec_source(ty: &Ty) -> Option<AggregateFieldCodec> {
    match ty {
        Ty::I64 => Some(AggregateFieldCodec::Signed64),
        Ty::U64 => Some(AggregateFieldCodec::Unsigned64),
        Ty::Ptr => Some(AggregateFieldCodec::Pointer),
        _ => None,
    }
}
pub(super) fn codec_kind(codec: AggregateFieldCodec) -> Kind {
    match codec {
        AggregateFieldCodec::Pointer => Kind::Pointer,
        _ => Kind::Word,
    }
}

/// Observe exact original source semantics with nominal retained bindings.
/// The ordinary sealed Core consumer separately reauthenticates its catalog.
/// This does not observe the retained pointer carrier or its field loads.
pub fn observe_native_aggregate_source(
    module: &Module,
    ordinal: usize,
    lir: &Function,
    intents: &AggregateCallIntents,
) -> Result<NativeAggregateSourceEvents, ReadOnlySourceError> {
    let module_digest = conditional_wrapper::module_digest(module)?;
    let retained_digest = conditional_wrapper::lowering_digest(std::slice::from_ref(lir))?;
    intents
        .validate(module, lir)
        .map_err(ReadOnlySourceError::Source)?;
    let original = module
        .functions
        .get(ordinal)
        .ok_or(ReadOnlySourceError::Source(
            "missing native aggregate source",
        ))?;
    if intents.caller() != Some(original.id)
        || original.name != lir.name
        || intents.calls().is_empty()
    {
        return Err(ReadOnlySourceError::Source(
            "foreign or empty native aggregate source binding",
        ));
    }
    let bindings = Bindings { intents, lir };
    let signature =
        module
            .func_types
            .get(original.ty.index() as usize)
            .ok_or(ReadOnlySourceError::Source(
                "missing native source signature",
            ))?;
    if signature
        .returns
        .iter()
        .any(|ty| codec_source(ty).is_none())
    {
        return Err(ReadOnlySourceError::Source(
            "native source event consumer requires scalar64 or void returns",
        ));
    }
    let graph = core::graph_native(module, ordinal, &bindings)?;
    let inputs = (0..graph.parameters.len())
        .map(|i| (format!("abi_x{i}"), 64))
        .collect::<Vec<_>>();
    let entry = E::uf("entry_memory", vec![], memory_sort());
    let observed = graph::observe_profile(
        &graph,
        &inputs,
        &entry,
        Boundary::Source,
        Profile::NativeAggregates(scalar_memory::Endpoint::Core),
    )?;
    let memory = observed
        .memory
        .ok_or(ReadOnlySourceError::Source("missing native source memory"))?;
    Ok(NativeAggregateSourceEvents {
        module_digest,
        retained_digest,
        caller: original.id,
        events: observed.native,
        reads: observed
            .reads
            .iter()
            .map(scalar_memory::access)
            .collect::<Result<_, _>>()?,
        writes: memory
            .writes
            .iter()
            .map(scalar_memory::write_access)
            .collect(),
        terminal_guards: memory.returns.iter().map(|(g, _)| g.expr.clone()).collect(),
        terminal_worlds: memory.returns.iter().map(|(_, m)| m.expr.clone()).collect(),
        retained_load: intents.fields().first().map(|field| ReadOnlySite {
            block: field.lir_block().0,
            instruction: field.lir_instruction() + 1,
        }),
        definitions: memory.definitions.equations.clone(),
        geometry: observed.geometry,
    })
}
