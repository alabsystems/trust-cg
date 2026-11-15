// Copyright 2026 Andrew Yates | Apache-2.0

//! Conditional original-Core/LIR call-and-memory observations.
//!
//! All call outcomes are independent nondeterministic inputs, including the
//! entire post-call memory. The conclusion is explicitly conditional on the
//! exposed, OUTSTANDING eventwise callee/ABI relations and source access geometry.
//! No relation, permission, normal return, determinism or private storage is
//! established here. Call-input queries use only earlier call relations.
//! Ordered-store conclusions use the relations and normal-return flags of
//! preceding call events; later calls are not their antecedents. Final-memory
//! and access-demand conclusions use ALL call relations and normal-return
//! flags. No divergence/exception refinement is claimed. This owner cannot
//! enter SourceBoundReplay or promotion.

use super::*;
use sha2::{Digest, Sha256};
use trust_cg_lower::instructions::DirectCallBinding;
use trust_ir::{CallingConv, Constant, FuncId, Inst, Linkage, Ty, ValueId};

#[path = "conditional_wrapper_inventory.rs"]
mod inventory;

type Result<T> = std::result::Result<T, ReadOnlySourceError>;

/// Exact original codec, before the retained LIR's I64 carrier erasure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallCodec {
    Signed64,
    Unsigned64,
    Pointer,
}
impl CallCodec {
    fn source(ty: &Ty) -> Result<Self> {
        match ty {
            Ty::I64 => Ok(Self::Signed64),
            Ty::U64 => Ok(Self::Unsigned64),
            Ty::Ptr => Ok(Self::Pointer),
            _ => Err(ReadOnlySourceError::Source(
                "conditional wrapper needs exact 64-bit scalar codecs",
            )),
        }
    }
    fn kind(self) -> Kind {
        if self == Self::Pointer {
            Kind::Pointer
        } else {
            Kind::Word
        }
    }
}

/// Custody of unresolved relations, NEVER a callee theorem or checked fact.
/// Creating fresh custody does not discharge any relation.
pub struct PendingCalleeRelations {
    module_digest: trust_ir::ProofDigest,
    lowering_digest: [u8; 32],
}
struct HashWriter {
    hash: Sha256,
    bytes: usize,
}
impl std::fmt::Write for HashWriter {
    fn write_str(&mut self, text: &str) -> std::fmt::Result {
        self.bytes = self
            .bytes
            .checked_add(text.len())
            .filter(|n| *n <= 4 * 1024 * 1024)
            .ok_or(std::fmt::Error)?;
        self.hash.update(text.as_bytes());
        Ok(())
    }
}

pub(super) fn lowering_digest(lowerings: &[Function]) -> Result<[u8; 32]> {
    if lowerings.len() > MAX_VALUES {
        return Err(ReadOnlySourceError::Budget(
            "conditional retained functions",
        ));
    }
    let mut inventory = inventory::Inventory::default();
    for f in lowerings {
        inventory
            .inspect(f)
            .map_err(|_| ReadOnlySourceError::Budget("conditional retained full payload"))?;
        inventory
            .charge(f.trust_ir_origins.len(), 0)
            .map_err(|_| ReadOnlySourceError::Budget("conditional origins"))?;
        for origins in f.trust_ir_origins.values() {
            inventory
                .charge(
                    origins.len(),
                    origins
                        .len()
                        .checked_mul(std::mem::size_of::<Option<trust_cg_ir::TrustIrInstId>>())
                        .ok_or(ReadOnlySourceError::Budget("conditional origins"))?,
                )
                .map_err(|_| ReadOnlySourceError::Budget("conditional origins"))?;
        }
    }
    let mut writer = HashWriter {
        hash: Sha256::new(),
        bytes: 0,
    };
    writer
        .hash
        .update(b"trust-cg.conditional-wrapper.bindings.v1");
    let mut total = 0usize;
    for f in lowerings {
        if f.blocks.len() > MAX_BLOCKS
            || f.value_types.len() > MAX_VALUES
            || f.signature.params.len() > 8
            || f.signature.returns.len() > 8
        {
            return Err(ReadOnlySourceError::Budget(
                "conditional retained function shape",
            ));
        }
        for block in f.blocks.values() {
            total =
                total
                    .checked_add(block.instructions.len())
                    .ok_or(ReadOnlySourceError::Budget(
                        "conditional retained instructions",
                    ))?;
            if block.instructions.len() > MAX_INSTRUCTIONS || total > MAX_TOTAL_QUERY_NODES {
                return Err(ReadOnlySourceError::Budget(
                    "conditional retained instructions",
                ));
            }
        }
        f.write_canonical_verifier_identity(&mut writer)
            .map_err(|_| {
                ReadOnlySourceError::Lowering("cannot retain exact conditional LIR identity")
            })?;
        // The existing verifier rendering predates the separate EH type table.
        // Custody also binds that complete retained field, after full preflight.
        use std::fmt::Write as _;
        writeln!(writer, "conditional_eh_type_table={:?}", f.eh_type_table)
            .map_err(|_| ReadOnlySourceError::Budget("conditional full identity bytes"))?;
    }
    Ok(writer.hash.finalize().into())
}
// The existing original observed identity traverses every source field,
// constant, attribute and canonical pass under one nonrenewable allowance.
pub(super) fn module_digest(module: &Module) -> Result<trust_ir::ProofDigest> {
    use trust_ir::interpret::{
        ExecutionObserver, ExecutionProgress, ExecutionSite, InterpretOptions, ObservedSession,
    };
    struct Budget {
        work: usize,
        bytes: usize,
    }
    impl ExecutionObserver for Budget {
        type Refusal = ();
        fn admit(&mut self, p: ExecutionProgress) -> std::result::Result<(), ()> {
            self.work = self
                .work
                .checked_add(p.work)
                .filter(|n| *n <= MAX_TOTAL_QUERY_NODES)
                .ok_or(())?;
            self.bytes = self
                .bytes
                .checked_add(p.copy_bytes)
                .filter(|n| *n <= 4 * 1024 * 1024)
                .ok_or(())?;
            Ok(())
        }
    }
    let mut budget = Budget { work: 0, bytes: 0 };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut budget);
    module
        .checked_stable_digest_observed(&mut session, ExecutionSite::Entry(FuncId::new(0)))
        .map_err(|_| ReadOnlySourceError::Budget("conditional complete original identity"))
}
impl PendingCalleeRelations {
    pub fn capture(module: &Module, lowerings: &[Function]) -> Result<Self> {
        if module.functions.len() > MAX_VALUES || module.func_types.len() > MAX_VALUES {
            return Err(ReadOnlySourceError::Budget("conditional module shape"));
        }
        let module_digest = module_digest(module)?;
        let lowering_digest = lowering_digest(lowerings)?;
        let mut source_ids = HashSet::new();
        let mut source_names = HashSet::new();
        if module
            .functions
            .iter()
            .any(|f| !source_ids.insert(f.id) || !source_names.insert(f.name.as_str()))
        {
            return Err(ReadOnlySourceError::Source(
                "duplicate conditional source identity",
            ));
        }
        let mut names = HashSet::new();
        for f in lowerings {
            if !names.insert(f.name.as_str()) {
                return Err(ReadOnlySourceError::Lowering(
                    "duplicate retained conditional function",
                ));
            }
            if module
                .functions
                .iter()
                .filter(|source| !source.blocks.is_empty() && source.name == f.name)
                .count()
                != 1
            {
                return Err(ReadOnlySourceError::Lowering(
                    "foreign retained conditional function",
                ));
            }
        }
        if module
            .functions
            .iter()
            .filter(|f| !f.blocks.is_empty())
            .count()
            != lowerings.len()
        {
            return Err(ReadOnlySourceError::Lowering(
                "missing retained conditional function",
            ));
        }
        Ok(Self {
            module_digest,
            lowering_digest,
        })
    }
}

#[derive(Clone)]
pub(super) struct CallEvent {
    site: ReadOnlySite,
    callee: u32,
    guard: Term,
    arguments: Vec<Term>,
    before: Term,
    values: Vec<Term>,
    after: Term,
    normal: Term,
}
#[derive(Clone)]
#[allow(clippy::large_enum_variant)]
pub(super) enum Effect {
    Call(usize),
    Store {
        site: ReadOnlySite,
        guard: Term,
        address: Term,
        value: Term,
        byte_width: u32,
        alignment: u64,
        kind: Kind,
    },
}
#[derive(Default)]
pub(super) struct ObservedEffects {
    pub(super) calls: Vec<CallEvent>,
    effects: Vec<Effect>,
}
impl ObservedEffects {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn push_call(
        &mut self,
        site: ReadOnlySite,
        callee: u32,
        guard: Term,
        arguments: Vec<Term>,
        before: Term,
        values: Vec<Term>,
        after: Term,
        normal: Term,
    ) -> Result<()> {
        if self.effects.len() >= MAX_INSTRUCTIONS {
            return Err(ReadOnlySourceError::Budget("conditional effect events"));
        }
        self.effects.push(Effect::Call(self.calls.len()));
        self.calls.push(CallEvent {
            site,
            callee,
            guard,
            arguments,
            before,
            values,
            after,
            normal,
        });
        Ok(())
    }
    #[allow(clippy::too_many_arguments)]
    pub(super) fn push_store(
        &mut self,
        site: ReadOnlySite,
        guard: Term,
        address: Term,
        value: Term,
        byte_width: u32,
        alignment: u64,
        kind: Kind,
    ) -> Result<()> {
        if self.effects.len() >= MAX_INSTRUCTIONS {
            return Err(ReadOnlySourceError::Budget("conditional effect events"));
        }
        self.effects.push(Effect::Store {
            site,
            guard,
            address,
            value,
            byte_width,
            alignment,
            kind,
        });
        Ok(())
    }
}

/// Required relation between one pair of normal-returning call executions.
/// The distinct outcomes below are NOT equated as facts or definitions.
/// An actual callee/ABI proof must separately establish `required_relation`.
pub struct OutstandingCallRelation {
    pub occurrence: usize,
    pub callee: FuncId,
    pub calling_convention: CallingConv,
    pub source_site: ReadOnlySite,
    pub lowering_site: ReadOnlySite,
    pub argument_codecs: Vec<CallCodec>,
    pub result_codecs: Vec<CallCodec>,
    pub source_arguments: Vec<E>,
    pub lowering_arguments: Vec<E>,
    pub source_prior_memory: E,
    pub lowering_prior_memory: E,
    pub source_results: Vec<E>,
    pub lowering_results: Vec<E>,
    pub source_post_memory: E,
    pub lowering_post_memory: E,
    pub source_returned_normally: E,
    pub lowering_returned_normally: E,
    matching_inputs: E,
    required_relation: E,
}
impl OutstandingCallRelation {
    pub fn matching_inputs(&self) -> &E {
        &self.matching_inputs
    }
    /// Explicit unresolved hypothesis in a conditional conclusion, never a
    /// proved source assumption, permission or reusable receipt.
    pub fn required_relation(&self) -> &E {
        &self.required_relation
    }
}

/// A pending conditional statement. No Checked/Valid/source/native conversion.
pub struct ConditionalWrapperQueries<'a> {
    module: &'a Module,
    ordinal: usize,
    lowerings: &'a [Function],
    caller: usize,
    relations: Vec<OutstandingCallRelation>,
    queries: Vec<ProofObligation>,
    source_reads: Vec<scalar_memory::ScalarMemoryAccess>,
    lowering_reads: Vec<scalar_memory::ScalarMemoryAccess>,
    source_writes: Vec<scalar_memory::ScalarMemoryAccess>,
    lowering_writes: Vec<scalar_memory::ScalarMemoryAccess>,
    geometry: Vec<E>,
    definitions: Vec<E>,
}
impl<'a> ConditionalWrapperQueries<'a> {
    pub fn module(&self) -> &'a Module {
        self.module
    }
    pub fn source(&self) -> &'a trust_ir::Function {
        &self.module.functions[self.ordinal]
    }
    pub fn lir(&self) -> &'a Function {
        &self.lowerings[self.caller]
    }
    pub fn retained_functions(&self) -> &'a [Function] {
        self.lowerings
    }
    pub fn outstanding_relations(&self) -> &[OutstandingCallRelation] {
        &self.relations
    }
    /// Call-input queries use earlier relations only. Ordered-store queries
    /// use preceding call relations/normal flags; final-memory and access
    /// queries use all call relations/normal flags. All remain outstanding.
    pub fn conditional_obligations(&self) -> &[ProofObligation] {
        &self.queries
    }
    pub fn source_reads(&self) -> &[scalar_memory::ScalarMemoryAccess] {
        &self.source_reads
    }
    pub fn lowering_reads(&self) -> &[scalar_memory::ScalarMemoryAccess] {
        &self.lowering_reads
    }
    pub fn source_writes(&self) -> &[scalar_memory::ScalarMemoryAccess] {
        &self.source_writes
    }
    pub fn lowering_writes(&self) -> &[scalar_memory::ScalarMemoryAccess] {
        &self.lowering_writes
    }
    pub fn outstanding_source_geometry(&self) -> &[E] {
        &self.geometry
    }
    pub fn encoding_definitions(&self) -> &[E] {
        &self.definitions
    }
    pub fn callee_source(
        &self,
        relation: &OutstandingCallRelation,
    ) -> Option<&'a trust_ir::Function> {
        self.module
            .functions
            .iter()
            .find(|f| f.id == relation.callee)
    }
    pub fn callee_lir(&self, relation: &OutstandingCallRelation) -> Option<&'a Function> {
        let original = self.callee_source(relation)?;
        self.lowerings.iter().find(|f| f.name == original.name)
    }
}

struct Signature {
    params: Vec<CallCodec>,
    returns: Vec<CallCodec>,
}
fn signature(module: &Module, source: &trust_ir::Function) -> Result<Signature> {
    let sig = module
        .func_types
        .get(source.ty.index() as usize)
        .ok_or(ReadOnlySourceError::Source("missing conditional signature"))?;
    if !matches!(source.calling_conv, CallingConv::C | CallingConv::Fast)
        || sig.is_vararg
        || sig.params.len() > 8
        || sig.returns.len() > 8
    {
        return Err(ReadOnlySourceError::Source(
            "conditional C/Fast scalar register signature",
        ));
    }
    Ok(Signature {
        params: sig
            .params
            .iter()
            .map(CallCodec::source)
            .collect::<Result<_>>()?,
        returns: sig
            .returns
            .iter()
            .map(CallCodec::source)
            .collect::<Result<_>>()?,
    })
}
fn callee<'a>(
    module: &'a Module,
    lowerings: &'a [Function],
    id: u32,
) -> Result<(&'a trust_ir::Function, Signature)> {
    let original = module
        .functions
        .iter()
        .find(|f| f.id.index() == id)
        .ok_or(ReadOnlySourceError::Source("missing conditional callee"))?;
    if !matches!(original.linkage, Linkage::Internal | Linkage::Private)
        || original.blocks.is_empty()
    {
        return Err(ReadOnlySourceError::Source(
            "conditional callee is not an exact module definition",
        ));
    }
    let sig = signature(module, original)?;
    if sig.returns.is_empty() {
        return Err(ReadOnlySourceError::Source(
            "conditional call needs a nonempty typed result vector",
        ));
    }
    let lir =
        lowerings
            .iter()
            .find(|f| f.name == original.name)
            .ok_or(ReadOnlySourceError::Lowering(
                "missing retained conditional callee",
            ))?;
    if lir.signature.params != vec![LirType::I64; sig.params.len()]
        || lir.signature.returns != vec![LirType::I64; sig.returns.len()]
    {
        return Err(ReadOnlySourceError::Lowering(
            "conditional callee erased carrier signature differs",
        ));
    }
    Ok((original, sig))
}
fn ensure_wrapper(
    source: &trust_ir::Function,
    lir: &Function,
    module: &Module,
) -> Result<Signature> {
    let sig = signature(module, source)?;
    if source.calling_conv != CallingConv::C {
        return Err(ReadOnlySourceError::Source(
            "conditional caller requires ordinary C convention",
        ));
    }
    if source.attrs.params.len() > sig.params.len()
        || source
            .attrs
            .params
            .iter()
            .any(|a| a.byval || a.sret || a.ext != trust_ir::ArgExt::None || a.pass.is_some())
        || !source.attrs.ret.is_empty()
        || source.attrs.naked
        || !source.attrs.target_features.is_empty()
        || source.body_gate.is_some()
    {
        return Err(ReadOnlySourceError::Source(
            "unsupported conditional caller ABI metadata",
        ));
    }
    if !sig.returns.is_empty()
        || source.blocks.len() != 1
        || source.blocks[0].id != source.entry
        || sig.params.is_empty()
        || source.blocks[0].body.len() > MAX_INSTRUCTIONS
    {
        return Err(ReadOnlySourceError::Source(
            "conditional wrapper needs one complete void block",
        ));
    }
    if lir.blocks.len() != 1
        || !lir.blocks.contains_key(&lir.entry_block)
        || !lir.signature.returns.is_empty()
        || lir.signature.params != vec![LirType::I64; sig.params.len()]
        || !lir.stack_slots.is_empty()
        || !lir.eh_info.is_empty()
        || !lir.eh_type_table.is_empty()
        || lir.stack_protector != trust_cg_ir::function::StackProtectorMode::None
        || lir.stack_limit.is_some()
        || lir.abi_sret_param.is_some()
        || !lir.sret_arg_callees.is_empty()
        || !lir.sret_arg_indirect_callees.is_empty()
        || !lir.param_pointee_types.is_empty()
        || !lir.pure_callees.is_empty()
        || !lir.libm_pure_callees.is_empty()
        || !lir.target_features.is_empty()
        || lir.value_types.len() > MAX_VALUES
        || !lir.block_order.is_empty() && lir.block_order != [lir.entry_block]
    {
        return Err(ReadOnlySourceError::Lowering(
            "conditional wrapper metadata, carrier signature or complete block differs",
        ));
    }
    if lir.blocks[&lir.entry_block].instructions.len() > MAX_INSTRUCTIONS {
        return Err(ReadOnlySourceError::Budget(
            "conditional wrapper instructions",
        ));
    }
    Ok(sig)
}

fn core_graph(
    module: &Module,
    source: &trust_ir::Function,
    lowerings: &[Function],
    sig: &Signature,
) -> Result<Graph> {
    let block = &source.blocks[0];
    if block.params.len() != sig.params.len() {
        return Err(ReadOnlySourceError::Source(
            "conditional wrapper entry arity",
        ));
    }
    let mut values: HashMap<ValueId, Ty> = HashMap::new();
    let mut parameters = Vec::new();
    for ((id, ty), codec) in block.params.iter().zip(&sig.params) {
        if CallCodec::source(ty)? != *codec || values.insert(*id, ty.clone()).is_some() {
            return Err(ReadOnlySourceError::Source(
                "conditional wrapper entry type or duplicate",
            ));
        }
        parameters.push((id.index(), codec.kind()));
    }
    let mut nodes = Vec::new();
    for (instruction, node) in block.body.iter().enumerate() {
        if node.results.len() > 8 || !node.proofs.is_empty() || node.proof_context.is_some() {
            return Err(ReadOnlySourceError::Source(
                "conditional wrapper node metadata",
            ));
        }
        let require = |value: &ValueId, ty: &Ty| -> Result<()> {
            if values.get(value) == Some(ty) {
                Ok(())
            } else {
                Err(ReadOnlySourceError::Source(
                    "conditional wrapper undefined or wrong operand type",
                ))
            }
        };
        let mut result = None;
        let mut produced = Vec::new();
        let operation = match &node.inst {
            Inst::Const {
                ty,
                value: Constant::Int(value),
            } if matches!(ty, Ty::I64 | Ty::U64) => {
                if node.results.len() != 1
                    || matches!(ty, Ty::I64) && i64::try_from(*value).is_err()
                    || matches!(ty, Ty::U64) && u64::try_from(*value).is_err()
                {
                    return Err(ReadOnlySourceError::Source("conditional wrapper constant"));
                }
                result = Some((node.results[0].index(), Kind::Word));
                produced.push((node.results[0], ty.clone()));
                Operation::Constant(*value as u64)
            }
            Inst::NullPtr if node.results.len() == 1 => {
                result = Some((node.results[0].index(), Kind::Pointer));
                produced.push((node.results[0], Ty::Ptr));
                Operation::NullPointer
            }
            Inst::Copy { ty, operand: value } => {
                if node.results.len() != 1 {
                    return Err(ReadOnlySourceError::Source(
                        "conditional wrapper copy arity",
                    ));
                }
                require(value, ty)?;
                result = Some((node.results[0].index(), CallCodec::source(ty)?.kind()));
                produced.push((node.results[0], ty.clone()));
                Operation::Copy(value.index())
            }
            Inst::Call { callee: id, args } => {
                let (original, call) = callee(module, lowerings, id.index())?;
                if args.len() != call.params.len() || node.results.len() != call.returns.len() {
                    return Err(ReadOnlySourceError::Source("conditional exact-call arity"));
                }
                let ty = &module.func_types[original.ty.index() as usize];
                for (arg, expected) in args.iter().zip(&ty.params) {
                    require(arg, expected)?;
                }
                produced.extend(node.results.iter().copied().zip(ty.returns.iter().cloned()));
                Operation::ExactModuleCall {
                    callee: id.index(),
                    args: args.iter().map(|v| v.index()).collect(),
                    results: node
                        .results
                        .iter()
                        .zip(&call.returns)
                        .map(|(id, c)| (id.index(), c.kind()))
                        .collect(),
                }
            }
            Inst::GEP {
                base,
                indices,
                pointee_ty,
                inbounds: false,
            } if indices.len() == 1 => {
                if node.results.len() != 1 {
                    return Err(ReadOnlySourceError::Source(
                        "conditional wrapper byte GEP arity",
                    ));
                }
                require(base, &Ty::Ptr)?;
                let index_ty = values.get(&indices[0]).ok_or(ReadOnlySourceError::Source(
                    "conditional wrapper GEP undefined index",
                ))?;
                if !matches!(index_ty, Ty::I64 | Ty::U64) {
                    return Err(ReadOnlySourceError::Source(
                        "conditional wrapper GEP index codec",
                    ));
                }
                result = Some((node.results[0].index(), Kind::Pointer));
                produced.push((node.results[0], Ty::Ptr));
                Operation::ScaledOffset {
                    base: base.index(),
                    index: indices[0].index(),
                    scale: match pointee_ty {
                        Ty::I8 | Ty::U8 => 1,
                        Ty::I64 | Ty::U64 | Ty::Ptr => 8,
                        _ => {
                            return Err(ReadOnlySourceError::Source(
                                "conditional wrapper GEP stride",
                            ));
                        }
                    },
                    signed: matches!(index_ty, Ty::I64),
                }
            }
            Inst::Store {
                ty,
                ptr: addr,
                value,
                volatile: false,
                align,
            } => {
                if !node.results.is_empty()
                    || align.is_some_and(|a| a == 0 || a > 8 || !a.is_power_of_two())
                {
                    return Err(ReadOnlySourceError::Source(
                        "conditional wrapper store arity/alignment",
                    ));
                }
                CallCodec::source(ty)?;
                require(addr, &Ty::Ptr)?;
                require(value, ty)?;
                Operation::Store {
                    address: addr.index(),
                    value: value.index(),
                    alignment: align.unwrap_or(8),
                    byte_width: 8,
                }
            }
            Inst::Return { values } if values.is_empty() && node.results.is_empty() => {
                Operation::VoidReturn
            }
            _ => {
                return Err(ReadOnlySourceError::Source(
                    "unsupported complete conditional wrapper instruction",
                ));
            }
        };
        for (id, ty) in produced {
            if values.insert(id, ty).is_some() {
                return Err(ReadOnlySourceError::Source(
                    "duplicate conditional wrapper definition",
                ));
            }
        }
        if values.len() > MAX_VALUES {
            return Err(ReadOnlySourceError::Budget(
                "conditional wrapper SSA values",
            ));
        }
        nodes.push(Node {
            site: ReadOnlySite {
                block: block.id.index(),
                instruction,
            },
            result,
            operation,
        });
    }
    Ok(Graph {
        entry: block.id.index(),
        parameters: parameters.clone(),
        blocks: vec![Block {
            id: block.id.index(),
            parameters,
            nodes,
        }],
    })
}

fn lir_graph(
    module: &Module,
    source: &trust_ir::Function,
    lir: &Function,
    lowerings: &[Function],
    sig: &Signature,
) -> Result<Graph> {
    let block = &lir.blocks[&lir.entry_block];
    if block.params.len() != sig.params.len()
        || block
            .params
            .iter()
            .enumerate()
            .any(|(i, (v, ty))| v.0 as usize != i || *ty != LirType::I64)
    {
        return Err(ReadOnlySourceError::Lowering(
            "conditional wrapper entry carriers",
        ));
    }
    let mut values: HashSet<u32> = block.params.iter().map(|(v, _)| v.0).collect();
    let mut nodes = Vec::new();
    for (instruction, node) in block.instructions.iter().enumerate() {
        if node.args.len() > 8
            || node.results.len() > 8
            || node.args.iter().any(|v| !values.contains(&v.0))
        {
            return Err(ReadOnlySourceError::Lowering(
                "conditional wrapper operand arity or definition",
            ));
        }
        let mut result = None;
        let operation = match &node.opcode {
            Opcode::Iconst {
                ty: LirType::I64,
                imm,
            } if node.args.is_empty() && node.results.len() == 1 => {
                result = Some((node.results[0].0, Kind::Word));
                Operation::Constant(*imm as u64)
            }
            Opcode::Copy if node.args.len() == 1 && node.results.len() == 1 => {
                result = Some((node.results[0].0, Kind::Word));
                Operation::Copy(node.args[0].0)
            }
            Opcode::Call {
                name,
                binding: DirectCallBinding::ExactModuleFunction { function },
            } => {
                let (original, call) = callee(module, lowerings, *function)?;
                if original.name != *name
                    || node.args.len() != call.params.len()
                    || node.results.len() != call.returns.len()
                {
                    return Err(ReadOnlySourceError::Lowering(
                        "conditional exact-call identity or arity",
                    ));
                }
                let origin = lir
                    .trust_ir_origins
                    .get(&lir.entry_block)
                    .and_then(|origins| origins.get(instruction))
                    .and_then(|o| *o)
                    .ok_or(ReadOnlySourceError::Lowering(
                        "missing conditional call source origin",
                    ))?;
                let original_node = source.blocks[0].body.get(origin.0 as usize).ok_or(
                    ReadOnlySourceError::Lowering("foreign conditional call source origin"),
                )?;
                if !matches!(&original_node.inst,Inst::Call {callee,..} if callee.index()==*function)
                {
                    return Err(ReadOnlySourceError::Lowering(
                        "stale conditional call source origin",
                    ));
                }
                Operation::ExactModuleCall {
                    callee: *function,
                    args: node.args.iter().map(|v| v.0).collect(),
                    results: node.results.iter().map(|v| (v.0, Kind::Word)).collect(),
                }
            }
            Opcode::ArrayGep {
                elem_ty: LirType::I8,
            } if node.args.len() == 2 && node.results.len() == 1 => {
                result = Some((node.results[0].0, Kind::Word));
                Operation::ScaledOffset {
                    base: node.args[0].0,
                    index: node.args[1].0,
                    scale: 1,
                    signed: false,
                }
            }
            Opcode::Store {
                ty: LirType::I64,
                align,
            } if node.args.len() == 2
                && node.results.is_empty()
                && align.is_none_or(|a| a > 0 && a <= 8 && a.is_power_of_two()) =>
            {
                Operation::Store {
                    address: node.args[1].0,
                    value: node.args[0].0,
                    alignment: u64::from(align.unwrap_or(8)),
                    byte_width: 8,
                }
            }
            Opcode::Return if node.args.is_empty() && node.results.is_empty() => {
                Operation::VoidReturn
            }
            _ => {
                return Err(ReadOnlySourceError::Lowering(
                    "unsupported complete conditional wrapper instruction",
                ));
            }
        };
        for id in &node.results {
            if !values.insert(id.0) {
                return Err(ReadOnlySourceError::Lowering(
                    "duplicate conditional wrapper definition",
                ));
            }
        }
        if values.len() > MAX_VALUES {
            return Err(ReadOnlySourceError::Budget(
                "conditional wrapper SSA values",
            ));
        }
        nodes.push(Node {
            site: ReadOnlySite {
                block: lir.entry_block.0,
                instruction,
            },
            result,
            operation,
        });
    }
    if lir
        .value_types
        .iter()
        .any(|(id, ty)| !values.contains(&id.0) || *ty != LirType::I64)
    {
        return Err(ReadOnlySourceError::Lowering(
            "conditional wrapper value hint differs from producing carrier",
        ));
    }
    let parameters = block
        .params
        .iter()
        .map(|(v, _)| (v.0, Kind::Word))
        .collect::<Vec<_>>();
    Ok(Graph {
        entry: lir.entry_block.0,
        parameters: parameters.clone(),
        blocks: vec![Block {
            id: lir.entry_block.0,
            parameters,
            nodes,
        }],
    })
}

fn equal(a: &Term, b: &Term) -> Result<Term> {
    let nodes = a
        .nodes
        .checked_add(b.nodes)
        .and_then(|n| n.checked_add(1))
        .filter(|n| *n <= MAX_QUERY_NODES)
        .ok_or(ReadOnlySourceError::Budget("conditional equality"))?;
    Ok(Term {
        expr: a.expr.clone().eq_expr(b.expr.clone()),
        nodes,
    })
}
fn conjunction(mut terms: Vec<Term>) -> Result<Term> {
    if terms.is_empty() {
        return Ok(Term::leaf(E::BoolConst(true)));
    }
    while terms.len() > 1 {
        let mut next = Vec::with_capacity(terms.len().div_ceil(2));
        let mut iter = terms.into_iter();
        while let Some(left) = iter.next() {
            next.push(if let Some(right) = iter.next() {
                let nodes = left
                    .nodes
                    .checked_add(right.nodes)
                    .and_then(|n| n.checked_add(1))
                    .filter(|n| *n <= MAX_QUERY_NODES)
                    .ok_or(ReadOnlySourceError::Budget("conditional conjunction"))?;
                Term {
                    expr: left.expr.and_expr(right.expr),
                    nodes,
                }
            } else {
                left
            });
        }
        terms = next;
    }
    Ok(terms.pop().unwrap())
}
fn conditional_query(
    name: String,
    antecedent: &Term,
    conclusion: Term,
    inputs: &[(String, u32)],
    definitions: &[E],
    definition_nodes: usize,
    total: &mut usize,
) -> Result<ProofObligation> {
    let expression = Term {
        nodes: antecedent
            .nodes
            .checked_add(conclusion.nodes)
            .and_then(|n| n.checked_add(2))
            .ok_or(ReadOnlySourceError::Budget("conditional query"))?,
        expr: antecedent.expr.clone().not_expr().or_expr(conclusion.expr),
    };
    for definition in definitions {
        crate::smt_raw_print::preflight(definition)
            .map_err(|_| ReadOnlySourceError::Budget("conditional definition graph"))?;
    }
    // Charge the shared driver's complete raw-tree costs, including duplicate
    // occurrences. DAG census alone is only a depth/shape guard.
    let count = expression
        .nodes
        .checked_add(definition_nodes)
        .and_then(|n| n.checked_add(definitions.len()))
        .and_then(|n| n.checked_add(2))
        .ok_or(ReadOnlySourceError::Budget(
            "conditional complete query collection",
        ))?;
    reserve_query(total, count)?;
    let obligation = pending(
        name,
        E::BoolConst(true),
        expression.expr,
        inputs,
        definitions,
    );
    crate::smt_raw_print::preflight(&obligation.negated_equivalence())
        .map_err(|_| ReadOnlySourceError::Budget("conditional query depth or graph"))?;
    Ok(obligation)
}
fn store_access(effect: &Effect) -> Option<scalar_memory::ScalarMemoryAccess> {
    let Effect::Store {
        site,
        guard,
        address,
        byte_width,
        alignment,
        kind,
        ..
    } = effect
    else {
        return None;
    };
    Some(scalar_memory::ScalarMemoryAccess {
        site: *site,
        guard: guard.expr.clone(),
        address: address.expr.clone(),
        byte_width: *byte_width,
        alignment: *alignment,
        codec: if *kind == Kind::Pointer {
            scalar_memory::ScalarMemoryCodec::Pointer
        } else {
            scalar_memory::ScalarMemoryCodec::Word64
        },
    })
}

/// Construct only conditional queries for complete bounded void wrappers.
/// `relations` is mandatory unresolved CUSTODY, not a supplied proof. All
/// endpoint outcomes remain distinct; relation conditions occur only in the
/// conclusion's antecedent, never among asserted source/definition premises.
pub fn bind_conditional_wrapper_source<'a>(
    module: &'a Module,
    ordinal: usize,
    lowerings: &'a [Function],
    relations: Option<&PendingCalleeRelations>,
) -> Result<ConditionalWrapperQueries<'a>> {
    let scope = relations.ok_or(ReadOnlySourceError::Source(
        "missing outstanding callee relation custody",
    ))?;
    if scope.module_digest != module_digest(module)?
        || scope.lowering_digest != lowering_digest(lowerings)?
    {
        return Err(ReadOnlySourceError::Source(
            "foreign or stale conditional relation custody",
        ));
    }
    let target = module
        .target_info
        .as_ref()
        .ok_or(ReadOnlySourceError::Source("missing conditional target"))?;
    if target.pointer_size != 8 || target.endianness != Endianness::Little {
        return Err(ReadOnlySourceError::Source(
            "conditional wrapper requires 64-bit little-endian target",
        ));
    }
    let source = module
        .functions
        .get(ordinal)
        .ok_or(ReadOnlySourceError::Source("missing conditional caller"))?;
    let caller = lowerings
        .iter()
        .position(|f| f.name == source.name)
        .ok_or(ReadOnlySourceError::Lowering("missing conditional caller"))?;
    let lir = &lowerings[caller];
    let sig = ensure_wrapper(source, lir, module)?;
    let source_graph = core_graph(module, source, lowerings, &sig)?;
    let lower_graph = lir_graph(module, source, lir, lowerings, &sig)?;
    let mut inputs = (0..sig.params.len())
        .map(|i| (format!("abi_x{i}"), 64))
        .collect::<Vec<_>>();
    inputs.push(("observe".into(), 64));
    let entry = E::uf("entry_memory", vec![], memory_sort());
    let mut source = graph::observe_profile(
        &source_graph,
        &inputs,
        &entry,
        Boundary::Source,
        Profile::ConditionalWrapper(scalar_memory::Endpoint::Core),
    )?;
    let mut lower = graph::observe_profile(
        &lower_graph,
        &inputs,
        &entry,
        Boundary::Lowering,
        Profile::ConditionalWrapper(scalar_memory::Endpoint::Lir),
    )?;
    if source.result.is_some() || lower.result.is_some() {
        return Err(ReadOnlySourceError::Source(
            "conditional wrapper did not preserve genuine void",
        ));
    }
    let source_effects = source
        .conditional
        .take()
        .ok_or(ReadOnlySourceError::Source(
            "missing conditional source effects",
        ))?;
    let lower_effects = lower
        .conditional
        .take()
        .ok_or(ReadOnlySourceError::Lowering(
            "missing conditional target effects",
        ))?;
    let source_memory = source.memory.take().ok_or(ReadOnlySourceError::Source(
        "missing conditional source memory",
    ))?;
    let lower_memory = lower.memory.take().ok_or(ReadOnlySourceError::Lowering(
        "missing conditional target memory",
    ))?;
    if source_effects.effects.len() != lower_effects.effects.len()
        || source_effects.calls.len() != lower_effects.calls.len()
        || source_effects.calls.is_empty()
    {
        return Err(ReadOnlySourceError::Lowering(
            "conditional effect occurrence/order differs",
        ));
    }
    let mut definitions = source_memory.definitions.equations.clone();
    definitions.extend(lower_memory.definitions.equations.iter().cloned());
    let definition_nodes = source_memory
        .definitions
        .nodes
        .checked_add(lower_memory.definitions.nodes)
        .ok_or(ReadOnlySourceError::Budget(
            "conditional raw definition occurrences",
        ))?;
    let geometry = source.geometry.clone();
    let mut hypotheses = Vec::new();
    let mut geometry_term = conjunction(
        geometry
            .iter()
            .map(|e| {
                let scan = crate::smt_raw_print::preflight(e)
                    .map_err(|_| ReadOnlySourceError::Budget("conditional source geometry"))?;
                Ok(Term {
                    expr: e.clone(),
                    nodes: scan.order.len(),
                })
            })
            .collect::<Result<_>>()?,
    )?;
    geometry_term.nodes = source
        .geometry_nodes
        .checked_add(geometry.len())
        .map(|n| n.max(1))
        .filter(|n| *n <= MAX_QUERY_NODES)
        .ok_or(ReadOnlySourceError::Budget(
            "conditional complete source geometry",
        ))?;
    hypotheses.push(geometry_term);
    let mut queries = Vec::new();
    let mut demands = Vec::new();
    let mut total = 0usize;
    for (event, (left, right)) in source_effects
        .effects
        .iter()
        .zip(&lower_effects.effects)
        .enumerate()
    {
        let prior = conjunction(hypotheses.clone())?;
        match (left, right) {
            (Effect::Call(a), Effect::Call(b)) => {
                let a = &source_effects.calls[*a];
                let b = &lower_effects.calls[*b];
                if a.callee != b.callee
                    || a.arguments.len() != b.arguments.len()
                    || a.values.len() != b.values.len()
                {
                    return Err(ReadOnlySourceError::Lowering(
                        "conditional exact-call event identity/arity differs",
                    ));
                }
                let (callee_source, signature) = callee(module, lowerings, a.callee)?;
                let mut inputs_equal =
                    vec![equal(&a.guard, &b.guard)?, equal(&a.before, &b.before)?];
                for (x, y) in a.arguments.iter().zip(&b.arguments) {
                    inputs_equal.push(equal(x, y)?);
                }
                let matching = conjunction(inputs_equal)?;
                queries.push(conditional_query(format!("Conditional wrapper call {event} inputs/prior world (earlier relations only)"),&prior,matching.clone(),&inputs,&definitions,definition_nodes,&mut total)?);
                let mut outcomes = vec![
                    matching.clone(),
                    a.normal.clone(),
                    b.normal.clone(),
                    equal(&a.after, &b.after)?,
                ];
                for (x, y) in a.values.iter().zip(&b.values) {
                    outcomes.push(equal(x, y)?);
                }
                let required = conjunction(outcomes)?;
                demands.push(OutstandingCallRelation {
                    occurrence: demands.len(),
                    callee: FuncId::new(a.callee),
                    calling_convention: callee_source.calling_conv,
                    source_site: a.site,
                    lowering_site: b.site,
                    argument_codecs: signature.params,
                    result_codecs: signature.returns,
                    source_arguments: a.arguments.iter().map(|v| v.expr.clone()).collect(),
                    lowering_arguments: b.arguments.iter().map(|v| v.expr.clone()).collect(),
                    source_prior_memory: a.before.expr.clone(),
                    lowering_prior_memory: b.before.expr.clone(),
                    source_results: a.values.iter().map(|v| v.expr.clone()).collect(),
                    lowering_results: b.values.iter().map(|v| v.expr.clone()).collect(),
                    source_post_memory: a.after.expr.clone(),
                    lowering_post_memory: b.after.expr.clone(),
                    source_returned_normally: a.normal.expr.clone(),
                    lowering_returned_normally: b.normal.expr.clone(),
                    matching_inputs: matching.expr,
                    required_relation: required.expr.clone(),
                });
                hypotheses.push(required);
            }
            (
                Effect::Store {
                    guard: a,
                    address: b,
                    value: c,
                    byte_width: d,
                    alignment: e,
                    ..
                },
                Effect::Store {
                    guard: x,
                    address: y,
                    value: z,
                    byte_width: w,
                    alignment: v,
                    ..
                },
            ) => {
                if d != w || v > e {
                    return Err(ReadOnlySourceError::Lowering(
                        "conditional ordered-store codec/alignment differs",
                    ));
                }
                let same = conjunction(vec![equal(a, x)?, equal(b, y)?, equal(c, z)?])?;
                queries.push(conditional_query(
                    format!("Conditional wrapper ordered store {event}"),
                    &prior,
                    same,
                    &inputs,
                    &definitions,
                    definition_nodes,
                    &mut total,
                )?);
            }
            _ => {
                return Err(ReadOnlySourceError::Lowering(
                    "conditional call/store order differs",
                ));
            }
        }
    }
    let all_relations = conjunction(hypotheses)?;
    let source_byte = scalar_memory::final_byte(&source_memory, &entry)?;
    let lower_byte = scalar_memory::final_byte(&lower_memory, &entry)?;
    queries.push(conditional_query(
        "Conditional wrapper all final bytes (outstanding callee/ABI relations)".into(),
        &all_relations,
        equal(&source_byte, &lower_byte)?,
        &inputs,
        &definitions,
        definition_nodes,
        &mut total,
    )?);
    for (index, read) in lower.reads.iter().enumerate() {
        let demand = scalar_memory::demand(
            &read.guard,
            &read.address,
            read.byte_width,
            read.alignment,
            source.reads.iter().map(|r| {
                (
                    r.guard.clone(),
                    r.address.clone(),
                    r.byte_width,
                    r.alignment,
                )
            }),
        )?;
        queries.push(conditional_query(
            format!("Conditional wrapper read demand {index}"),
            &all_relations,
            demand,
            &inputs,
            &definitions,
            definition_nodes,
            &mut total,
        )?);
    }
    for (index, write) in lower_memory.writes.iter().enumerate() {
        let demand = scalar_memory::demand(
            &write.guard,
            &write.address,
            write.byte_width,
            write.alignment,
            source_memory.writes.iter().map(|w| {
                (
                    w.guard.clone(),
                    w.address.clone(),
                    w.byte_width,
                    w.alignment,
                )
            }),
        )?;
        queries.push(conditional_query(
            format!("Conditional wrapper write demand {index}"),
            &all_relations,
            demand,
            &inputs,
            &definitions,
            definition_nodes,
            &mut total,
        )?);
    }
    Ok(ConditionalWrapperQueries {
        module,
        ordinal,
        lowerings,
        caller,
        relations: demands,
        queries,
        source_reads: source
            .reads
            .iter()
            .map(scalar_memory::access)
            .collect::<Result<_>>()?,
        lowering_reads: lower
            .reads
            .iter()
            .map(scalar_memory::access)
            .collect::<Result<_>>()?,
        source_writes: source_effects
            .effects
            .iter()
            .filter_map(store_access)
            .collect(),
        lowering_writes: lower_effects
            .effects
            .iter()
            .filter_map(store_access)
            .collect(),
        geometry,
        definitions,
    })
}

#[cfg(test)]
#[path = "conditional_wrapper_source_tests.rs"]
mod tests;
