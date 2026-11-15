// Copyright 2026 Andrew Yates | Apache-2.0
//! Pending preoptimization entry-interval observations, never permissions or
//! complete bodies. Virtual values, architectural inputs and unresolved slot
//! addresses remain distinct. Every call gives ALL architectural state fresh
//! symbols: neither SP/FP nor saved registers are assumed preserved.
use super::*;
use trust_cg_ir::{
    AArch64Opcode as A, InstId, MachFunction, MachInst, MachOperand as O, RegClass, VReg,
};
use trust_cg_lower::aggregate_call_transport::{
    AggregateCallIntent, AggregateCallIntents, MappedAggregateMaterialization,
};

#[path = "native_aggregate_materialization.rs"]
mod materialization;
pub use materialization::PendingNativeAggregateMaterialization;

#[path = "native_provider_footprint.rs"]
mod provider_footprint;
pub use provider_footprint::{NativeProviderWriteRegion, PendingNativeProviderFootprint};

#[derive(Clone, Debug)]
pub struct TargetCall {
    pub(super) binding: trust_cg_lower::instructions::DirectCallBinding,
    pub(super) site: ReadOnlySite,
    pub(super) intent: AggregateCallIntent,
    pub(super) arguments: Vec<E>,
    pub(super) guard: E,
    pub(super) prior_world: E,
    pub(super) post_world: E,
    pub(super) normal: E,
    pub(super) before: Vec<E>,
    pub(super) after: Vec<E>,
}
impl TargetCall {
    pub fn binding(&self) -> trust_cg_lower::instructions::DirectCallBinding {
        self.binding
    }
    pub fn site(&self) -> ReadOnlySite {
        self.site
    }
    pub fn intent(&self) -> &AggregateCallIntent {
        &self.intent
    }
    pub fn arguments(&self) -> &[E] {
        &self.arguments
    }
    pub fn guard(&self) -> &E {
        &self.guard
    }
    pub fn prior_world(&self) -> &E {
        &self.prior_world
    }
    pub fn post_world(&self) -> &E {
        &self.post_world
    }
    pub fn returned_normally(&self) -> &E {
        &self.normal
    }
    /// X0..X30 then SP. These are independent, not preservation equalities.
    pub fn before_registers(&self) -> &[E] {
        &self.before
    }
    pub fn after_registers(&self) -> &[E] {
        &self.after
    }
    pub fn outstanding_requirements(&self) -> [native_aggregates::NativeAggregateRequirement; 6] {
        use native_aggregates::NativeAggregateRequirement::*;
        [
            MatchingInputsAndPriorWorld,
            RuntimeProviderAbiAndOutcomeRelation,
            NormalContinuation,
            LiveAlignedNonwrappingResultStorage,
            InitializationAndFieldLoadSemantics,
            SourcePrivateMemoryRelation,
        ]
    }
}
#[derive(Clone, Debug)]
pub struct TargetSlotAddress {
    pub site: ReadOnlySite,
    pub slot: u32,
    pub observed_sp: E,
    pub address: E,
    pub call_site: ReadOnlySite,
}
#[derive(Clone, Debug)]
pub struct TargetAccess {
    pub site: ReadOnlySite,
    pub load: bool,
    pub guard: E,
    pub address: E,
    pub value: E,
    pub prior_world: E,
    /// Actual driver snapshot after this access; loads retain their input.
    /// This is byte-array observation data, not a successful-access fact.
    pub post_world: E,
    pub byte_width: u32,
    pub alignment: u64,
    /// Candidate actual writes after the latest opaque call, NOT a proof
    /// that they cover/readably initialize live storage at this point.
    pub initialization_writes: Vec<usize>,
    /// Sufficient post-call write coverage at every free observed byte. This
    /// remains a DEMAND, conditional on live successful stores, not init proof.
    pub initialization_coverage_demand: Option<E>,
}
#[derive(Default)]
pub(super) struct Effects {
    pub(super) calls: Vec<TargetCall>,
    pub(super) slots: Vec<TargetSlotAddress>,
    pub(super) accesses: Vec<TargetAccess>,
    nodes: usize,
    last_call_access: usize,
    access_nodes: Vec<(usize, usize)>,
}
impl Effects {
    fn admit(&mut self, nodes: usize) -> Result<(), ReadOnlySourceError> {
        self.nodes = self
            .nodes
            .checked_add(nodes)
            .filter(|n| *n <= MAX_TOTAL_QUERY_NODES)
            .ok_or(ReadOnlySourceError::Budget("native target event terms"))?;
        Ok(())
    }
    #[allow(clippy::too_many_arguments)]
    pub(super) fn access(
        &mut self,
        site: ReadOnlySite,
        guard: &Term,
        address: &Term,
        value: &Term,
        world: &Term,
        post_world: &Term,
        load: bool,
        byte_width: u32,
        alignment: u64,
    ) -> Result<(), ReadOnlySourceError> {
        if self.accesses.len() >= MAX_INSTRUCTIONS {
            return Err(ReadOnlySourceError::Budget("native target accesses"));
        }
        let initializers = if load {
            self.accesses
                .iter()
                .enumerate()
                .skip(self.last_call_access)
                .filter_map(|(i, a)| (!a.load).then_some(i))
                .collect::<Vec<_>>()
        } else {
            vec![]
        };
        let basic = guard.nodes
            + address.nodes
            + value.nodes
            + world.nodes
            + post_world.nodes
            + initializers.len();
        let available = MAX_TOTAL_QUERY_NODES
            .checked_sub(self.nodes)
            .and_then(|n| n.checked_sub(basic))
            .ok_or(ReadOnlySourceError::Budget(
                "native target access inventory",
            ))?;
        let coverage = if load {
            Some(
                crate::scalar_memory_relations::demand(
                    (&guard.expr, guard.nodes),
                    (&address.expr, address.nodes),
                    byte_width,
                    alignment,
                    initializers.iter().map(|i| {
                        let a = &self.accesses[*i];
                        let n = self.access_nodes[*i];
                        (
                            a.guard.clone(),
                            n.0,
                            a.address.clone(),
                            n.1,
                            a.byte_width,
                            a.alignment,
                        )
                    }),
                    MAX_QUERY_NODES.min(available),
                )
                .map_err(ReadOnlySourceError::Budget)?,
            )
        } else {
            None
        };
        self.admit(basic + coverage.as_ref().map_or(0, |(_, n)| *n))?;
        self.accesses.push(TargetAccess {
            site,
            load,
            guard: guard.expr.clone(),
            address: address.expr.clone(),
            value: value.expr.clone(),
            prior_world: world.expr.clone(),
            post_world: post_world.expr.clone(),
            byte_width,
            alignment,
            initialization_writes: initializers,
            initialization_coverage_demand: coverage.map(|(e, _)| e),
        });
        self.access_nodes.push((guard.nodes, address.nodes));
        Ok(())
    }
}
pub(super) fn input(
    defs: &mut scalar_memory::Definitions,
    sort: crate::smt::SmtSort,
) -> Result<E, ReadOnlySourceError> {
    defs.native_target_input(sort).map_err(|e| match e {
        crate::scalar_memory_definitions::Error::Invalid(s) => ReadOnlySourceError::Lowering(s),
        crate::scalar_memory_definitions::Error::Budget(s) => ReadOnlySourceError::Budget(s),
    })
}
#[allow(clippy::large_enum_variant)]
pub(super) enum Operation {
    Input,
    Call {
        binding: trust_cg_lower::instructions::DirectCallBinding,
        intent: AggregateCallIntent,
        before: Vec<u32>,
        args: Vec<u32>,
        results: Vec<(u32, Kind)>,
    },
    Slot {
        slot: u32,
        sp: u32,
        call_site: ReadOnlySite,
    },
}
impl Operation {
    pub(super) fn operands(&self, mut visit: impl FnMut(u32)) {
        match self {
            Self::Input => {}
            Self::Call { before, args, .. } => before.iter().chain(args).copied().for_each(visit),
            Self::Slot { sp, .. } => visit(*sp),
        }
    }
    pub(super) fn execute(
        &self,
        site: ReadOnlySite,
        values: &mut HashMap<u32, Value>,
        memory: &mut Option<Term>,
        guard: &mut Term,
        defs: &mut scalar_memory::Definitions,
        effects: &mut Effects,
    ) -> Result<Option<Value>, ReadOnlySourceError> {
        let get = |id| {
            values
                .get(&id)
                .cloned()
                .ok_or(ReadOnlySourceError::Lowering(
                    "undefined native target value",
                ))
        };
        let word = |expr| Value {
            kind: Kind::Word,
            term: Term::leaf(expr),
            literal: None,
        };
        match self {
            Self::Input => Ok(Some(word(input(defs, crate::smt::SmtSort::BitVec(64))?))),
            Self::Slot {
                slot,
                sp,
                call_site,
            } => {
                if effects.calls.last().map(|c| c.site) != Some(*call_site) {
                    return Err(refused("foreign native target slot occurrence"));
                }
                if effects.slots.len() >= MAX_READS {
                    return Err(ReadOnlySourceError::Budget(
                        "native target slot occurrences",
                    ));
                }
                let sp = get(*sp)?;
                effects.admit(guard.nodes + sp.term.nodes + 1)?;
                let address = input(defs, crate::smt::SmtSort::BitVec(64))?;
                effects.slots.push(TargetSlotAddress {
                    site,
                    slot: *slot,
                    observed_sp: sp.term.expr,
                    address: address.clone(),
                    call_site: *call_site,
                });
                Ok(Some(word(address)))
            }
            Self::Call {
                binding,
                intent,
                before,
                args,
                results,
            } => {
                if effects.calls.len() >= MAX_READS || before.len() != 32 || results.len() != 32 {
                    return Err(ReadOnlySourceError::Budget(
                        "native target call occurrences/registers",
                    ));
                }
                let prior = memory
                    .as_ref()
                    .ok_or(ReadOnlySourceError::Lowering("missing target call world"))?;
                let charge = before
                    .iter()
                    .chain(args)
                    .try_fold(
                        guard.nodes + prior.nodes + 36 + intent.callee_name().len(),
                        |n, id| n.checked_add(get(*id).ok()?.term.nodes),
                    )
                    .ok_or(ReadOnlySourceError::Budget("native target call terms"))?;
                effects.admit(charge)?;
                let before = before
                    .iter()
                    .map(|id| Ok(get(*id)?.term.expr))
                    .collect::<Result<Vec<_>, ReadOnlySourceError>>()?;
                let arguments = args
                    .iter()
                    .map(|id| Ok(get(*id)?.term.expr))
                    .collect::<Result<Vec<_>, ReadOnlySourceError>>()?;
                let after = (0..32)
                    .map(|_| input(defs, crate::smt::SmtSort::BitVec(64)))
                    .collect::<Result<Vec<_>, _>>()?;
                let post = input(defs, memory_sort())?;
                let normal = input(defs, crate::smt::SmtSort::Bool)?;
                effects.calls.push(TargetCall {
                    binding: *binding,
                    site,
                    intent: intent.clone(),
                    arguments,
                    guard: guard.expr.clone(),
                    prior_world: prior.expr.clone(),
                    post_world: post.clone(),
                    normal: normal.clone(),
                    before,
                    after: after.clone(),
                });
                for ((id, kind), expr) in results.iter().zip(after) {
                    if *kind != Kind::Word || values.insert(*id, word(expr)).is_some() {
                        return Err(ReadOnlySourceError::Lowering(
                            "native target register definition",
                        ));
                    }
                }
                *memory = Some(Term::leaf(post));
                let nodes = guard
                    .nodes
                    .checked_add(2)
                    .filter(|n| *n <= MAX_QUERY_NODES)
                    .ok_or(ReadOnlySourceError::Budget("native target normal guard"))?;
                *guard = Term {
                    nodes,
                    expr: guard.expr.clone().and_expr(normal),
                };
                effects.last_call_access = effects.accesses.len();
                Ok(None)
            }
        }
    }
}
/// Explicit observed interval; the rest of the function is unobserved. No
/// complete body, query/certificate attachment, row credit or native conversion.
pub struct NativeAggregateTargetObservations {
    source: native_aggregates::NativeAggregateSourceEvents,
    module: trust_ir::ProofDigest,
    retained: [u8; 32],
    instructions: Vec<(InstId, MachInst)>,
    frontier: ReadOnlySite,
    frontier_instruction: (InstId, MachInst),
    materializations: Vec<MappedAggregateMaterialization>,
    effects: Effects,
    definitions: Vec<E>,
    demands: Vec<E>,
    normal_frontier_guard: E,
    frontier_world: E,
}
impl NativeAggregateTargetObservations {
    pub fn source(&self) -> &native_aggregates::NativeAggregateSourceEvents {
        &self.source
    }
    pub fn original_module_digest(&self) -> trust_ir::ProofDigest {
        self.module
    }
    pub fn retained_function_digest(&self) -> &[u8; 32] {
        &self.retained
    }
    pub fn observed_instructions(&self) -> &[(InstId, MachInst)] {
        &self.instructions
    }
    pub fn frontier(&self) -> ReadOnlySite {
        self.frontier
    }
    pub fn frontier_instruction(&self) -> &(InstId, MachInst) {
        &self.frontier_instruction
    }
    pub fn materializations(&self) -> &[MappedAggregateMaterialization] {
        &self.materializations
    }
    pub fn calls(&self) -> &[TargetCall] {
        &self.effects.calls
    }
    pub fn slot_address_demands(&self) -> &[TargetSlotAddress] {
        &self.effects.slots
    }
    pub fn accesses(&self) -> &[TargetAccess] {
        &self.effects.accesses
    }
    pub fn definitions(&self) -> &[E] {
        &self.definitions
    }
    pub fn access_geometry_demands(&self) -> &[E] {
        &self.demands
    }
    pub fn normal_frontier_guard(&self) -> &E {
        &self.normal_frontier_guard
    }
    pub fn frontier_world(&self) -> &E {
        &self.frontier_world
    }
}
fn refused(s: &'static str) -> ReadOnlySourceError {
    ReadOnlySourceError::Lowering(s)
}
struct Adapter {
    nodes: Vec<Node>,
    next: u32,
    physical: Vec<u32>,
    virtuals: HashMap<VReg, u32>,
    site: ReadOnlySite,
}
impl Adapter {
    fn node(
        &mut self,
        operation: super::Operation,
        result: bool,
    ) -> Result<u32, ReadOnlySourceError> {
        if self.nodes.len() >= MAX_INSTRUCTIONS || result && self.next as usize >= MAX_VALUES {
            return Err(ReadOnlySourceError::Budget("native target graph"));
        }
        let id = self.next;
        if result {
            self.next += 1;
        }
        self.nodes.push(Node {
            site: self.site,
            result: result.then_some((id, Kind::Word)),
            operation,
        });
        Ok(id)
    }
    fn read(&mut self, o: &O) -> Result<u32, ReadOnlySourceError> {
        match o {
            O::VReg(r) if r.class == RegClass::Gpr64 => self
                .virtuals
                .get(r)
                .copied()
                .ok_or(refused("undefined native target virtual value")),
            O::PReg(r) if r.encoding() < 31 => Ok(self.physical[r.encoding() as usize]),
            O::PReg(r) if *r == trust_cg_ir::regs::SP => Ok(self.physical[31]),
            O::Special(trust_cg_ir::SpecialReg::SP) => Ok(self.physical[31]),
            _ => Err(refused("native target register bank/width/operand")),
        }
    }
    fn write(&mut self, o: &O, id: u32) -> Result<(), ReadOnlySourceError> {
        match o {
            O::VReg(r) if r.class == RegClass::Gpr64 => {
                if self.virtuals.insert(*r, id).is_some() {
                    return Err(refused("multiply defined native target virtual value"));
                }
            }
            O::PReg(r) if r.encoding() < 31 => self.physical[r.encoding() as usize] = id,
            _ => return Err(refused("native target destination bank/width")),
        }
        Ok(())
    }
    fn offset(&mut self, base: &O, offset: i64) -> Result<u32, ReadOnlySourceError> {
        let base = self.read(base)?;
        if offset == 0 {
            return Ok(base);
        }
        let index = self.node(super::Operation::Constant(offset as u64), true)?;
        self.node(
            super::Operation::Binary {
                opcode: Opcode::Iadd,
                left: base,
                right: index,
            },
            true,
        )
    }
}
/// Observe the actual preoptimization ENTRY interval, stopping explicitly at
/// its first control/terminal instruction. All actual instructions/effects in
/// that interval must adapt. Later CFG/body, optimized/final bytes and provider
/// behavior remain unobserved. Raw inputs carry only nominal dependency data;
/// the ordinary Core consumer must separately authenticate the real catalog.
pub fn observe_native_aggregate_target(
    module: &Module,
    lir: &Function,
    intents: &AggregateCallIntents,
    selected: &trust_cg_lower::isel::ISelFunction,
    machine: &MachFunction,
    mapped: &[MappedAggregateMaterialization],
) -> Result<NativeAggregateTargetObservations, ReadOnlySourceError> {
    if module.functions.len() > MAX_VALUES {
        return Err(ReadOnlySourceError::Budget(
            "native target original functions",
        ));
    }
    let ordinal = module
        .functions
        .iter()
        .position(|f| f.name == lir.name)
        .ok_or(refused("missing native target original function"))?;
    // Independently admit the complete original graph, including return arity,
    // before relating its still-pending call inventory to this target slice.
    let source = native_aggregates::observe_native_aggregate_source(module, ordinal, lir, intents)?;
    let module_digest = source.original_module_digest();
    let retained = *source.retained_function_digest();
    if machine.insts.len() > MAX_INSTRUCTIONS
        || machine.blocks.len() > MAX_BLOCKS
        || machine.stack_slots.len() > MAX_VALUES
        || mapped.len() > MAX_READS
    {
        return Err(ReadOnlySourceError::Budget(
            "native target selected inventory",
        ));
    }
    if machine.name != lir.name
        || machine.signature.params.len() > 8
        || machine
            .signature
            .params
            .iter()
            .any(|ty| *ty != trust_cg_ir::Type::I64)
        || machine.insts.iter().any(|i| {
            i.operands.len() > 8
                || i.implicit_defs.len() > 128
                || i.implicit_uses.len() > 32
                || i.proof.is_some()
                || i.operands
                    .iter()
                    .any(|o| matches!(o,O::Symbol(s) if s.len()>4096))
        })
    {
        return Err(refused("native target selected profile"));
    }
    if mapped.len() != intents.calls().len() {
        return Err(refused("native target call census"));
    }
    for (m, c) in mapped.iter().zip(intents.calls()) {
        if m.plan().intent() != c {
            return Err(refused("native target foreign owner"));
        }
        m.validate(module, lir, intents, selected, machine)
            .map_err(refused)?;
    }
    let entry = machine
        .blocks
        .get(machine.entry.0 as usize)
        .ok_or(refused("native target entry"))?;
    if entry.insts.len() > MAX_INSTRUCTIONS {
        return Err(ReadOnlySourceError::Budget("native target entry interval"));
    }
    let mut adapter = Adapter {
        nodes: vec![],
        next: 0,
        physical: vec![],
        virtuals: HashMap::new(),
        site: ReadOnlySite {
            block: machine.entry.0,
            instruction: 0,
        },
    };
    for _ in 0..32 {
        let id = adapter.node(super::Operation::NativeTarget(Operation::Input), true)?;
        adapter.physical.push(id);
    }
    let mut instructions = Vec::new();
    let mut frontier = None;
    let mut called = HashSet::new();
    let mut observed_fields = HashSet::new();
    let mut seen_ids = HashSet::new();
    for (index, id) in entry.insts.iter().copied().enumerate() {
        if !seen_ids.insert(id) {
            return Err(refused("duplicate native target interval instruction"));
        }
        adapter.site = ReadOnlySite {
            block: machine.entry.0,
            instruction: index,
        };
        let inst = machine
            .insts
            .get(id.0 as usize)
            .ok_or(refused("native target instruction identity"))?;
        if matches!(
            inst.opcode,
            A::Ret | A::B | A::Bcc | A::Cbz | A::Cbnz | A::CmpRI | A::CmpRR | A::CSet
        ) {
            frontier = Some(adapter.site);
            break;
        }
        if inst.opcode != A::Bl && !inst.implicit_defs.is_empty() {
            return Err(refused("native target implicit write"));
        }
        let mut flags = inst.flags;
        if matches!(inst.opcode, A::MovR | A::MOVXrr | A::Copy) {
            flags.remove(trust_cg_ir::InstFlags::IS_CALL_ARG_SETUP);
        }
        if inst.opcode == A::Nop {
            flags.remove(trust_cg_ir::InstFlags::IS_PSEUDO);
        }
        let mut expected = inst.opcode.default_flags();
        if inst.opcode == A::Nop {
            expected.remove(trust_cg_ir::InstFlags::IS_PSEUDO);
        }
        if flags != expected
            || inst.opcode != A::Bl && inst.implicit_uses.iter().any(|r| r.encoding() >= 8)
        {
            return Err(refused("native target extra instruction effects"));
        }
        match (inst.opcode, inst.operands.as_slice()) {
            (A::Nop, []) => {}
            (A::Bl, [O::Symbol(_)]) => {
                let owner = mapped
                    .iter()
                    .position(|m| m.call() == id)
                    .ok_or(refused("unbound native target call"))?;
                if !called.insert(owner) {
                    return Err(refused("duplicate native target call"));
                }
                let intent = mapped[owner].plan().intent().clone();
                let args = adapter
                    .physical
                    .iter()
                    .take(intent.argument_codecs().len())
                    .copied()
                    .collect();
                let before = adapter.physical.clone();
                let mut results = Vec::new();
                for _ in 0..32 {
                    if adapter.next as usize >= MAX_VALUES {
                        return Err(ReadOnlySourceError::Budget(
                            "native target register versions",
                        ));
                    }
                    results.push((adapter.next, Kind::Word));
                    adapter.next += 1;
                }
                adapter.physical = results.iter().map(|(i, _)| *i).collect();
                adapter.node(
                    super::Operation::NativeTarget(Operation::Call {
                        binding: mapped[owner].plan().binding(),
                        intent,
                        before,
                        args,
                        results,
                    }),
                    false,
                )?;
            }
            (A::AddPCRel, [dst, base, O::StackSlot(slot)]) => {
                let owner = mapped
                    .iter()
                    .find(|m| m.address() == id && m.plan().slot() == slot.0)
                    .ok_or(refused("unbound native target slot address"))?;
                if !matches!(base,O::PReg(r) if *r==trust_cg_ir::regs::SP) {
                    return Err(refused("native target slot SP spelling"));
                }
                let sp = adapter.physical[31];
                let next = adapter.node(
                    super::Operation::NativeTarget(Operation::Slot {
                        slot: slot.0,
                        sp,
                        call_site: ReadOnlySite {
                            block: owner.plan().block().0,
                            instruction: owner.plan().call_instruction(),
                        },
                    }),
                    true,
                )?;
                adapter.write(dst, next)?;
            }
            (A::MovR | A::MOVXrr | A::Copy, [dst, src]) => {
                let source = adapter.read(src)?;
                let next = adapter.node(super::Operation::Copy(source), true)?;
                adapter.write(dst, next)?;
            }
            (A::Madd, [dst, left, right, addend]) => {
                let ordinary = |o: &O| {
                    matches!(o,O::VReg(r) if r.class==RegClass::Gpr64)
                        || matches!(o,O::PReg(r) if r.encoding()<31)
                };
                if ![left, right, addend].into_iter().all(ordinary) {
                    return Err(refused("native target Madd bank/width"));
                }
                let left = adapter.read(left)?;
                let right = adapter.read(right)?;
                let addend = adapter.read(addend)?;
                let product = adapter.node(
                    super::Operation::Binary {
                        opcode: Opcode::Imul,
                        left,
                        right,
                    },
                    true,
                )?;
                let next = adapter.node(
                    super::Operation::Binary {
                        opcode: Opcode::Iadd,
                        left: product,
                        right: addend,
                    },
                    true,
                )?;
                adapter.write(dst, next)?;
            }
            (A::AddRI | A::SubRI, [dst, base, O::Imm(imm)]) if (0..=4095).contains(imm) => {
                let base = adapter.read(base)?;
                let constant = adapter.node(super::Operation::Constant(*imm as u64), true)?;
                let next = adapter.node(
                    super::Operation::Binary {
                        opcode: if inst.opcode == A::AddRI {
                            Opcode::Iadd
                        } else {
                            Opcode::Isub
                        },
                        left: base,
                        right: constant,
                    },
                    true,
                )?;
                adapter.write(dst, next)?;
            }
            (A::Movz, [dst, O::Imm(imm)] | [dst, O::Imm(imm), O::Imm(0)])
                if (0..=65535).contains(imm) =>
            {
                let next = adapter.node(super::Operation::Constant(*imm as u64), true)?;
                adapter.write(dst, next)?;
            }
            (A::LdrRI, [dst, base, O::Imm(offset)]) => {
                let address = adapter.offset(base, *offset)?;
                let next = adapter.node(
                    super::Operation::MemoryLoad {
                        address,
                        alignment: 1,
                        byte_width: 8,
                    },
                    true,
                )?;
                adapter.write(dst, next)?;
                for (owner, m) in mapped.iter().enumerate() {
                    for (field, f) in m.fields().iter().enumerate() {
                        if f.load() == id {
                            observed_fields.insert((owner, field));
                        }
                    }
                }
            }
            (A::StrRI, [value, base, O::Imm(offset)]) => {
                let address = adapter.offset(base, *offset)?;
                let value = adapter.read(value)?;
                adapter.node(
                    super::Operation::Store {
                        address,
                        value,
                        alignment: 1,
                        byte_width: 8,
                    },
                    false,
                )?;
            }
            _ => {
                return Err(ReadOnlySourceError::TargetInstruction {
                    site: adapter.site,
                    opcode: inst.opcode,
                });
            }
        }
        instructions.push((id, inst.clone()));
    }
    let frontier = frontier.ok_or(refused("native target interval lacks explicit frontier"))?;
    let frontier_id = entry.insts[frontier.instruction];
    let frontier_instruction = (frontier_id, machine.inst(frontier_id).clone());
    if called.is_empty() {
        return Err(refused("native target interval has no bound call"));
    }
    for owner in &called {
        for field in 0..mapped[*owner].fields().len() {
            if !observed_fields.contains(&(*owner, field)) {
                return Err(refused("native target frontier precedes bound field load"));
            }
        }
    }
    adapter.site = frontier;
    adapter.node(super::Operation::NativeTargetFrontier, false)?;
    let graph = Graph {
        entry: machine.entry.0,
        parameters: vec![],
        blocks: vec![Block {
            id: machine.entry.0,
            parameters: vec![],
            nodes: adapter.nodes,
        }],
    };
    let observed = graph::observe_profile(
        &graph,
        &[],
        &E::uf("entry_memory", vec![], memory_sort()),
        Boundary::Lowering,
        Profile::NativeTarget,
    )?;
    let memory = observed
        .memory
        .ok_or(refused("native target memory inventory"))?;
    let [(guard, world)] = memory.returns.as_slice() else {
        return Err(refused("native target frontier inventory"));
    };
    Ok(NativeAggregateTargetObservations {
        source,
        module: module_digest,
        retained,
        instructions,
        frontier,
        frontier_instruction,
        materializations: mapped
            .iter()
            .enumerate()
            .filter(|(i, _)| called.contains(i))
            .map(|(_, m)| m.clone())
            .collect(),
        effects: observed.target,
        definitions: memory.definitions.equations.clone(),
        demands: observed.geometry,
        normal_frontier_guard: guard.expr.clone(),
        frontier_world: world.expr.clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_lower::isel::InstructionSelector;
    pub(super) fn fixture(
        calls: usize,
    ) -> (
        Module,
        Function,
        trust_cg_lower::ProofContext,
        trust_cg_lower::isel::ISelFunction,
        MachFunction,
        Vec<MappedAggregateMaterialization>,
    ) {
        let (module, _, lir, context) = native_aggregates::tests::fixture(calls, false);
        let mut selector = InstructionSelector::new(lir.name.clone(), lir.signature.clone());
        selector.enable_sealed_core_native_calls();
        selector.set_abi_variant(trust_cg_lower::AArch64AbiVariant::Darwin);
        selector.seed_aggregate_call_intents(&context.aggregate_call_intents);
        selector.seed_value_types(&lir.value_types);
        selector.seed_iconst_origins(lir.blocks.values().map(|b| b.instructions.as_slice()));
        selector.seed_function_value_use_counts(&lir);
        selector
            .lower_formal_arguments(&lir.signature, lir.entry_block)
            .unwrap();
        for block in lir.layout_order() {
            let b = &lir.blocks[&block];
            selector
                .select_block_with_provenance(
                    block,
                    &b.instructions,
                    &b.source_locs,
                    &lir.trust_ir_origins[&block],
                )
                .unwrap();
        }
        let selected = selector.finalize();
        let (machine, mapped) = selected
            .try_to_ir_func_with_aggregate_materializations()
            .unwrap();
        (module, lir, context, selected, machine, mapped)
    }
    #[test]
    fn actual_native_target_retains_independent_world_registers_slots_and_accesses() {
        let (m, l, c, s, t, b) = fixture(2);
        let observed =
            observe_native_aggregate_target(&m, &l, &c.aggregate_call_intents, &s, &t, &b).unwrap();
        assert_eq!(observed.calls().len(), 2);
        assert_eq!(observed.slot_address_demands().len(), 2);
        for call in observed.calls() {
            assert_eq!(call.before_registers().len(), 32);
            assert_eq!(call.after_registers().len(), 32);
            for (a, b) in call.before_registers().iter().zip(call.after_registers()) {
                assert_ne!(a, b);
            }
            assert_ne!(call.prior_world(), call.post_world());
            assert_eq!(call.outstanding_requirements().len(), 6);
        }
        assert_ne!(
            observed.calls()[0].post_world(),
            observed.calls()[1].post_world()
        );
        assert_ne!(
            observed.slot_address_demands()[0].observed_sp,
            observed.slot_address_demands()[1].observed_sp
        );
        assert_ne!(
            observed.slot_address_demands()[0].address,
            observed.slot_address_demands()[1].address
        );
        assert_eq!(observed.accesses().iter().filter(|a| a.load).count(), 5);
        assert_eq!(observed.accesses().iter().filter(|a| !a.load).count(), 5);
        assert!(observed.accesses().iter().all(|a| {
            a.guard
                .to_string()
                .contains("scalar_memory_machine_d_native")
        }));
        let source = native_aggregates::observe_native_aggregate_source(
            &m,
            1,
            &l,
            &c.aggregate_call_intents,
        )
        .unwrap();
        assert_ne!(
            source.events()[0].post_world(),
            observed.calls()[0].post_world()
        );
        assert_ne!(
            source.events()[0].record().fields()[0],
            observed.calls()[0].after_registers()[0]
        );
        assert!(observed.definitions().iter().any(|e| {
            e.to_string()
                .contains(&observed.calls()[1].post_world().to_string())
        }));
        println!(
            "NATIVE_TARGET calls={} accesses={} SP_preserved=false source_relation=pending native_credit=false",
            observed.calls().len(),
            observed.accesses().len()
        );
    }
    #[test]
    fn actual_native_target_foreign_order_offset_width_and_removed_store_refuse() {
        let (m, l, c, s, t, b) = fixture(1);
        for mutation in 0..6 {
            let mut changed = t.clone();
            match mutation {
                0 => changed.name.push_str("_foreign"),
                1 => changed.inst_mut(b[0].fields()[1].address()).operands[2] = O::Imm(0),
                2 => {
                    changed.inst_mut(b[0].fields()[0].load()).operands[0] = O::VReg(VReg::new(
                        b[0].fields()[0].plan().result().id,
                        RegClass::Gpr32,
                    ))
                }
                3 => {
                    let block = &mut changed.blocks[b[0].plan().block().0 as usize];
                    block.insts.retain(|id| *id != b[0].stores()[0]);
                }
                4 => {
                    let block = &mut changed.blocks[b[0].plan().block().0 as usize];
                    let a = block
                        .insts
                        .iter()
                        .position(|id| *id == b[0].fields()[0].load())
                        .unwrap();
                    let z = block
                        .insts
                        .iter()
                        .position(|id| *id == b[0].fields()[1].load())
                        .unwrap();
                    block.insts.swap(a, z);
                }
                _ => {
                    let id = changed.blocks[changed.entry.0 as usize].insts[0];
                    changed
                        .inst_mut(id)
                        .flags
                        .insert(trust_cg_ir::InstFlags::WRITES_MEMORY);
                }
            }
            assert!(
                observe_native_aggregate_target(
                    &m,
                    &l,
                    &c.aggregate_call_intents,
                    &s,
                    &changed,
                    &b
                )
                .is_err(),
                "mutation{mutation}"
            );
        }
        let (m2, l2, c2, s2, t2, mut b2) = fixture(2);
        b2.swap(0, 1); // Same callee/layout, foreign execution occurrence.
        assert!(
            observe_native_aggregate_target(&m2, &l2, &c2.aggregate_call_intents, &s2, &t2, &b2)
                .is_err()
        );
        b2.swap(0, 1);
        let mut foreign_slot = t2.clone();
        foreign_slot.inst_mut(b2[0].address()).operands[2] =
            O::StackSlot(trust_cg_ir::types::StackSlotId(b2[1].plan().slot()));
        assert!(
            observe_native_aggregate_target(
                &m2,
                &l2,
                &c2.aggregate_call_intents,
                &s2,
                &foreign_slot,
                &b2
            )
            .is_err()
        );
        let mut malformed = m.clone();
        for block in &mut malformed.functions[1].blocks {
            for node in &mut block.body {
                if let trust_ir::Inst::Return { values } = &mut node.inst {
                    values.clear();
                }
            }
        }
        assert!(
            observe_native_aggregate_target(&malformed, &l, &c.aggregate_call_intents, &s, &t, &b)
                .is_err()
        );
        let mut source = m.clone();
        source.structs[0].fields.swap(0, 1);
        assert!(
            observe_native_aggregate_target(&source, &l, &c.aggregate_call_intents, &s, &t, &b)
                .is_err()
        );
        let (_, _, _, _, _, foreign) = fixture(2);
        assert!(
            observe_native_aggregate_target(&m, &l, &c.aggregate_call_intents, &s, &t, &foreign)
                .is_err()
        );
    }
    #[test]
    fn actual_native_target_physical_register_and_implicit_write_mutations_refuse() {
        use trust_cg_ir::regs::{NZCV, SP, V0, W0, WSP, WZR, X0, XZR};
        let (m, l, c, s, t, b) = fixture(1);
        let entry = &t.blocks[t.entry.0 as usize];
        let setup=entry.insts.iter().copied().take_while(|id|*id!=b[0].call()).find(|id| {
            let inst=t.inst(*id);
            matches!(inst.opcode,A::Copy|A::MovR|A::MOVXrr)
                && matches!(inst.operands.as_slice(),[O::PReg(dst),O::VReg(src)] if *dst==X0 && src.class==RegClass::Gpr64)
        }).expect("actual physical ABI argument setup before the bound call");
        let positive =
            observe_native_aggregate_target(&m, &l, &c.aggregate_call_intents, &s, &t, &b).unwrap();
        assert_eq!(positive.calls().len(), 1);
        assert_eq!(positive.calls()[0].outstanding_requirements().len(), 6);
        for (label, destination) in [
            ("W0", O::PReg(W0)),
            ("XZR", O::PReg(XZR)),
            ("V0", O::PReg(V0)),
            ("SP", O::PReg(SP)),
            ("WSP", O::PReg(WSP)),
            ("WZR", O::PReg(WZR)),
            ("SpecialSP", O::Special(trust_cg_ir::SpecialReg::SP)),
            ("SpecialXZR", O::Special(trust_cg_ir::SpecialReg::XZR)),
            ("SpecialWZR", O::Special(trust_cg_ir::SpecialReg::WZR)),
        ] {
            let mut changed = t.clone();
            changed.inst_mut(setup).operands[0] = destination;
            b[0].validate(&m, &l, &c.aggregate_call_intents, &s, &changed)
                .unwrap();
            let error = observe_native_aggregate_target(
                &m,
                &l,
                &c.aggregate_call_intents,
                &s,
                &changed,
                &b,
            )
            .err();
            assert_eq!(
                error,
                Some(refused("native target destination bank/width")),
                "{label}"
            );
            println!(
                "NATIVE_TARGET_PHYSICAL_DESTINATION {label} instruction={setup:?} refusal={error:?}"
            );
        }
        for (label, source) in [
            ("W0", O::PReg(W0)),
            ("XZR", O::PReg(XZR)),
            ("V0", O::PReg(V0)),
            ("NZCV", O::PReg(NZCV)),
        ] {
            let mut changed = t.clone();
            changed.inst_mut(setup).operands[1] = source;
            b[0].validate(&m, &l, &c.aggregate_call_intents, &s, &changed)
                .unwrap();
            let error = observe_native_aggregate_target(
                &m,
                &l,
                &c.aggregate_call_intents,
                &s,
                &changed,
                &b,
            )
            .err();
            assert_eq!(
                error,
                Some(refused("native target register bank/width/operand")),
                "{label}"
            );
            println!(
                "NATIVE_TARGET_PHYSICAL_SOURCE {label} instruction={setup:?} refusal={error:?}"
            );
        }
        let writes: [(&str, &'static [trust_cg_ir::PReg]); 3] =
            [("NZCV", &[NZCV]), ("X0", &[X0]), ("SP", &[SP])];
        for (label, definitions) in writes {
            let mut changed = t.clone();
            changed.inst_mut(setup).implicit_defs = definitions;
            b[0].validate(&m, &l, &c.aggregate_call_intents, &s, &changed)
                .unwrap();
            let error = observe_native_aggregate_target(
                &m,
                &l,
                &c.aggregate_call_intents,
                &s,
                &changed,
                &b,
            )
            .err();
            assert_eq!(
                error,
                Some(refused("native target implicit write")),
                "{label}"
            );
            println!(
                "NATIVE_TARGET_IMPLICIT_WRITE {label} instruction={setup:?} refusal={error:?}"
            );
        }
        let mut changed = t.clone();
        changed.inst_mut(setup).implicit_uses = &[NZCV];
        b[0].validate(&m, &l, &c.aggregate_call_intents, &s, &changed)
            .unwrap();
        let error =
            observe_native_aggregate_target(&m, &l, &c.aggregate_call_intents, &s, &changed, &b)
                .err();
        assert_eq!(
            error,
            Some(refused("native target extra instruction effects"))
        );
        println!("NATIVE_TARGET_NZCV_USE instruction={setup:?} refusal={error:?}");
    }
    #[test]
    fn actual_native_target_normal_false_has_no_later_normal_access_or_frontier_claim() {
        use super::super::scalar_memory::tests::{Substitutions, evaluate};
        use crate::smt::{EvalEnv, EvalResult, SmtSort};
        let (m, l, c, s, t, b) = fixture(2);
        let observed =
            observe_native_aggregate_target(&m, &l, &c.aggregate_call_intents, &s, &t, &b).unwrap();
        for a in [false, true] {
            for z in [false, true] {
                let mut substitutions = Substitutions::new();
                for (call, value) in observed.calls().iter().zip([a, z]) {
                    let E::UF { name, .. } = call.returned_normally() else {
                        panic!("fresh Bool")
                    };
                    substitutions.insert(name.clone(), (SmtSort::Bool, E::BoolConst(value)));
                }
                assert_eq!(
                    evaluate(
                        observed.calls()[1].guard(),
                        &substitutions,
                        &EvalEnv::default()
                    ),
                    EvalResult::Bool(a)
                );
                assert_eq!(
                    evaluate(
                        observed.normal_frontier_guard(),
                        &substitutions,
                        &EvalEnv::default()
                    ),
                    EvalResult::Bool(a && z)
                );
                assert_eq!(
                    evaluate(
                        &observed.accesses().last().unwrap().guard,
                        &substitutions,
                        &EvalEnv::default()
                    ),
                    EvalResult::Bool(a && z)
                );
            }
        }
        let second = observed
            .accesses()
            .iter()
            .position(|a| a.site.instruction > observed.calls()[1].site().instruction && a.load)
            .unwrap();
        assert!(
            observed.accesses()[second]
                .initialization_writes
                .iter()
                .all(|i| observed.accesses()[*i].site.instruction
                    > observed.calls()[1].site().instruction)
        );
    }
    #[test]
    fn actual_native_target_raw_controls_keep_missing_relations_and_state_unproved() {
        use sha2::{Digest, Sha256};
        let (m, l, c, s, t, b) = fixture(2);
        let observed =
            observe_native_aggregate_target(&m, &l, &c.aggregate_call_intents, &s, &t, &b).unwrap();
        let source = native_aggregates::observe_native_aggregate_source(
            &m,
            1,
            &l,
            &c.aggregate_call_intents,
        )
        .unwrap();
        let first = &observed.calls()[0];
        let first_read = observed.accesses().iter().find(|a| a.load).unwrap();
        let q = E::var("observe", 64);
        for (name, claim, expected, normal) in [
            (
                "missing_source_product_relation",
                first_read
                    .value
                    .clone()
                    .eq_expr(source.events()[0].record().fields()[0].clone()),
                "sat",
                true,
            ),
            (
                "missing_source_target_postworld_relation",
                E::select(first.post_world().clone(), q.clone())
                    .eq_expr(E::select(source.events()[0].post_world().clone(), q)),
                "sat",
                true,
            ),
            (
                "missing_callee_sp_preservation",
                first.before_registers()[31]
                    .clone()
                    .eq_expr(first.after_registers()[31].clone()),
                "sat",
                true,
            ),
            (
                "repeated_callee_independent_returns",
                first.after_registers()[0]
                    .clone()
                    .eq_expr(observed.calls()[1].after_registers()[0].clone()),
                "sat",
                true,
            ),
            (
                "actual_normal_false_suppresses_access",
                first
                    .returned_normally()
                    .clone()
                    .or_expr(observed.accesses().last().unwrap().guard.clone().not_expr()),
                "unsat",
                false,
            ),
            (
                "local_actual_store_load_bits",
                first_read
                    .value
                    .clone()
                    .eq_expr(first.after_registers()[0].clone()),
                "unsat",
                true,
            ),
        ] {
            let mut premises = source.definitions().to_vec();
            premises.extend_from_slice(observed.definitions());
            if normal {
                premises.extend(
                    source
                        .events()
                        .iter()
                        .map(|e| e.returned_normally().clone()),
                );
                premises.extend(
                    observed
                        .calls()
                        .iter()
                        .map(|e| e.returned_normally().clone()),
                );
            }
            let obligation = ProofObligation {
                name: format!("Pending native target diagnostic {name}"),
                trust_ir_expr: claim,
                aarch64_expr: E::BoolConst(true),
                inputs: vec![
                    ("abi_x0".into(), 64),
                    ("abi_x1".into(), 64),
                    ("observe".into(), 64),
                ],
                preconditions: premises,
                fp_inputs: vec![],
                category: Some(TransvalCheckKind::MemoryModel),
                machine_side_provenance: MachineSideProvenance::StaticDb,
            };
            let query = crate::ay_bridge::generate_smt2_query_raw(
                &obligation,
                &crate::ay_bridge::AYConfig {
                    solver: None,
                    timeout_ms: crate::ay_bridge::DEFAULT_AY_TIMEOUT_MS,
                    produce_models: true,
                },
            );
            println!(
                "NATIVE_AGGREGATE_TARGET_CONTROL={}",
                serde_json::json!({"name":name,"expected":expected,"query":query,"bytes":query.len(),"sha256":format!("{:x}",Sha256::digest(query.as_bytes())),"diagnostic_normal_inputs":normal,"relations_assumed":false,"storage_permission":false,"complete_body":false,"native_credit":false})
            );
        }
    }
    #[test]
    fn native_target_selected_instruction_budget_is_unchanged_and_preallocation() {
        let (m, l, c, s, mut t, b) = fixture(1);
        t.insts
            .resize(MAX_INSTRUCTIONS + 1, MachInst::new(A::Nop, vec![]));
        assert!(matches!(
            observe_native_aggregate_target(&m, &l, &c.aggregate_call_intents, &s, &t, &b),
            Err(ReadOnlySourceError::Budget(
                "native target selected inventory"
            ))
        ));
    }
    #[test]
    fn actual_target_field_loads_read_the_store_time_bits_in_finite_dirty_worlds() {
        use super::super::scalar_memory::tests::{evaluate, expand};
        use crate::smt::{EvalEnv, EvalResult, SmtSort};
        let (m, l, c, s, t, b) = fixture(2);
        let observed =
            observe_native_aggregate_target(&m, &l, &c.aggregate_call_intents, &s, &t, &b).unwrap();
        let mut defined = HashSet::new();
        for equation in observed.definitions() {
            let E::Eq { lhs, .. } = equation else {
                panic!("semantic equation")
            };
            let E::UF { name, .. } = lhs.as_ref() else {
                panic!("defined occurrence")
            };
            defined.insert(name.clone());
        }
        let mut free = std::collections::BTreeMap::new();
        let mut pending = observed.definitions().iter().collect::<Vec<_>>();
        pending.extend(observed.calls().iter().map(|c| c.returned_normally()));
        while let Some(node) = pending.pop() {
            if let E::UF {
                name,
                args,
                ret_sort,
            } = node
            {
                assert!(args.is_empty());
                if !defined.contains(name) {
                    free.insert(name.clone(), ret_sort.clone());
                }
            }
            node.for_each_child(&mut |child| pending.push(child));
        }
        for (alias, normal) in [(false, true), (true, true), (false, false), (true, false)] {
            let bits = [
                [0x0123456789abcdef, 0xfedcba9876543210],
                [u64::MAX, 0x8080808080808080],
            ];
            let mut concrete = free
                .iter()
                .map(|(name, sort)| {
                    let value = match sort {
                        SmtSort::BitVec(64) => E::bv_const(0x55, 64),
                        SmtSort::Bool => E::BoolConst(normal),
                        _ if *sort == memory_sort() => {
                            E::const_array(SmtSort::BitVec(64), E::bv_const(0xa5, 8))
                        }
                        _ => panic!("bounded target input"),
                    };
                    (name.clone(), value)
                })
                .collect::<std::collections::BTreeMap<_, _>>();
            for (call, words) in observed.calls().iter().zip(bits) {
                for (word, value) in call.after_registers().iter().take(2).zip(words) {
                    let E::UF { name, .. } = word else {
                        panic!("independent bits")
                    };
                    concrete.insert(name.clone(), E::bv_const(value, 64));
                }
            }
            for (i, slot) in observed.slot_address_demands().iter().enumerate() {
                let E::UF { name, .. } = &slot.address else {
                    panic!("pending slot base")
                };
                concrete.insert(
                    name.clone(),
                    E::bv_const(0x1000 + if alias { 0 } else { i as u64 * 32 }, 64),
                );
            }
            let mut equations = free
                .iter()
                .map(|(name, sort)| {
                    E::uf(name, vec![], sort.clone()).eq_expr(concrete[name].clone())
                })
                .collect::<Vec<_>>();
            equations.extend_from_slice(observed.definitions());
            let substitutions = expand(
                &equations,
                &E::const_array(SmtSort::BitVec(64), E::bv_const(0x73, 8)),
            );
            for (occurrence, materialization) in observed.materializations().iter().enumerate() {
                for field in materialization.fields() {
                    let access = observed
                        .accesses()
                        .iter()
                        .find(|a| a.load && a.site.instruction == field.plan().load_instruction())
                        .unwrap();
                    assert_eq!(
                        evaluate(&access.value, &substitutions, &EvalEnv::default()),
                        EvalResult::Bv(bits[occurrence][field.plan().intent().field() as usize])
                    );
                }
            }
            // Finite controls for the ACTUAL retained snapshots, not a new
            // evaluator or a proof. Exercise interior and dirty outside bytes.
            for row in observed.local_materialization_queries().unwrap() {
                for q in [0x0fff, 0x1000, 0x1007, 0x1008, 0x100f, 0x1010, 0x1020] {
                    let mut env = EvalEnv::default();
                    env.insert("observe".into(), q);
                    for query in row.obligations() {
                        assert_eq!(
                            evaluate(&query.trust_ir_expr, &substitutions, &env),
                            EvalResult::Bool(true)
                        );
                    }
                }
            }
        }
    }
}
