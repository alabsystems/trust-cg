// Copyright 2026 Andrew Yates | Apache-2.0

//! Compiler-generated aggregate-result intent and exact materialization plans.
//! These are source/retained transport inputs, not provider refinement, storage
//! permissions, private-frame separation, machine proof or publication credit.

use crate::declared_layout::{LayoutTables, emitted_struct_layout};
use crate::instructions::{Block, DirectCallBinding, Instruction, Opcode, Value};
use crate::{Function, Type};
use trust_cg_ir::{SourceInstId, TrustIrInstId};
use trust_ir::{
    CallingConv, Endianness, FuncId, Inst, Linkage, Module, StructId, StructRepr, Ty, ValueId,
};

const MAX_CALLS: usize = 256;
const MAX_FIELDS: usize = 512;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AggregateFieldCodec {
    Signed64,
    Unsigned64,
    Pointer,
}
impl AggregateFieldCodec {
    fn source(ty: &Ty) -> Option<Self> {
        match ty {
            Ty::I64 => Some(Self::Signed64),
            Ty::U64 => Some(Self::Unsigned64),
            Ty::Ptr => Some(Self::Pointer),
            _ => None,
        }
    }
}

/// A bounded flat source record. Its fields remain ONE Struct-valued result;
/// field codecs are never a replacement scalar return signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlatAggregateLayout {
    source_type: StructId,
    fields: [AggregateFieldCodec; 2],
    offsets: [u64; 2],
    bytes: u64,
    align: u64,
}
impl FlatAggregateLayout {
    pub fn source_type(&self) -> StructId {
        self.source_type
    }
    pub fn fields(&self) -> &[AggregateFieldCodec; 2] {
        &self.fields
    }
    pub fn offsets(&self) -> &[u64; 2] {
        &self.offsets
    }
    pub fn bytes(&self) -> u64 {
        self.bytes
    }
    pub fn align(&self) -> u64 {
        self.align
    }
    pub fn carrier(&self) -> Type {
        Type::Struct(vec![Type::I64, Type::I64])
    }
    fn source(module: &Module, ty: &Ty) -> Option<Self> {
        let target = module.target_info.as_ref()?;
        if target.pointer_size != 8
            || target.endianness != Endianness::Little
            || target.struct_passing != trust_ir::StructPassingPolicy::NativeC
            || module.structs.len() > 384
            || module.functions.len() > 384
            || module.func_types.len() > 384
        {
            return None;
        }
        let Ty::Struct(id) = ty else { return None };
        let mut definitions = module.structs.iter().filter(|s| s.id == *id);
        let definition = definitions.next()?;
        if definitions.next().is_some()
            || definition.repr != StructRepr::C
            || definition.name.len() > 4096
            || definition.fields.len() != 2
        {
            return None;
        }
        let fields = [
            AggregateFieldCodec::source(&definition.fields[0].ty)?,
            AggregateFieldCodec::source(&definition.fields[1].ty)?,
        ];
        let actual = emitted_struct_layout(
            definition,
            LayoutTables {
                structs: &module.structs,
                types: &module.types,
                enums: &module.enums,
                records: &module.records,
                closures: &module.closure_types,
            },
        )
        .ok()?;
        if actual.offsets != [0, 8] || actual.size != 16 || actual.align != 8 {
            return None;
        }
        Some(Self {
            source_type: *id,
            fields,
            offsets: [0, 8],
            bytes: actual.size,
            align: actual.align,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AggregateCallIntent {
    caller: FuncId,
    source_block: u32,
    source_instruction: usize,
    source_origin: TrustIrInstId,
    callee: FuncId,
    callee_name: String,
    source_arguments: Vec<ValueId>,
    argument_codecs: Vec<AggregateFieldCodec>,
    source_result: ValueId,
    layout: FlatAggregateLayout,
    lir_block: Block,
    lir_instruction: usize,
    lir_arguments: Vec<Value>,
    lir_result: Value,
}
impl AggregateCallIntent {
    pub fn caller(&self) -> FuncId {
        self.caller
    }
    pub fn source_block(&self) -> u32 {
        self.source_block
    }
    pub fn source_instruction(&self) -> usize {
        self.source_instruction
    }
    pub fn source_origin(&self) -> TrustIrInstId {
        self.source_origin
    }
    pub fn callee(&self) -> FuncId {
        self.callee
    }
    pub fn callee_name(&self) -> &str {
        &self.callee_name
    }
    pub fn source_arguments(&self) -> &[ValueId] {
        &self.source_arguments
    }
    pub fn argument_codecs(&self) -> &[AggregateFieldCodec] {
        &self.argument_codecs
    }
    pub fn source_result(&self) -> ValueId {
        self.source_result
    }
    pub fn layout(&self) -> &FlatAggregateLayout {
        &self.layout
    }
    pub fn lir_block(&self) -> Block {
        self.lir_block
    }
    pub fn lir_instruction(&self) -> usize {
        self.lir_instruction
    }
    pub fn lir_arguments(&self) -> &[Value] {
        &self.lir_arguments
    }
    pub fn lir_result(&self) -> Value {
        self.lir_result
    }
    pub fn source_site(&self) -> SourceInstId {
        SourceInstId {
            block: self.lir_block.0,
            index: self.lir_instruction as u32,
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn from_adapter(
        module: &Module,
        caller: &trust_ir::Function,
        block: u32,
        instruction: usize,
        origin: TrustIrInstId,
        node: &trust_ir::InstrNode,
        lir_block: Block,
        lir_instruction: usize,
        emitted: &[Instruction],
    ) -> Option<Self> {
        if module.functions.len() > 384
            || module.func_types.len() > 384
            || module.structs.len() > 384
            || caller.name.len() > 4096
        {
            return None;
        }
        let Inst::Call { callee, args } = &node.inst else {
            return None;
        };
        let [source_result] = node.results.as_slice() else {
            return None;
        };
        let [actual] = emitted else { return None };
        let Opcode::Call {
            name,
            binding: DirectCallBinding::DeclaredExternalFunction { function },
        } = &actual.opcode
        else {
            return None;
        };
        if *function != callee.index()
            || name.len() > 4096
            || args.len() > 8
            || actual.args.len() != args.len()
        {
            return None;
        }
        let mut declarations = module.functions.iter().filter(|f| f.id == *callee);
        let declaration = declarations.next()?;
        if declarations.next().is_some()
            || declaration.name != *name
            || declaration.calling_conv != CallingConv::C
            || declaration.attrs.params.len() > 8
            || !declaration.blocks.is_empty()
            || declaration.linkage != Linkage::External
            || !declaration.attrs.is_empty()
        {
            return None;
        }
        let signature = module.func_types.get(declaration.ty.index() as usize)?;
        if signature.is_vararg
            || signature.abi.is_some()
            || signature.params.len() != args.len()
            || signature.returns.len() != 1
        {
            return None;
        }
        let argument_codecs = signature
            .params
            .iter()
            .map(AggregateFieldCodec::source)
            .collect::<Option<Vec<_>>>()?;
        let layout = FlatAggregateLayout::source(module, &signature.returns[0])?;
        let [lir_result] = actual.results.as_slice() else {
            return None;
        };
        Some(Self {
            caller: caller.id,
            source_block: block,
            source_instruction: instruction,
            source_origin: origin,
            callee: *callee,
            callee_name: name.clone(),
            source_arguments: args.clone(),
            argument_codecs,
            source_result: *source_result,
            layout,
            lir_block,
            lir_instruction,
            lir_arguments: actual.args.clone(),
            lir_result: *lir_result,
        })
    }
    pub fn matches_lir(
        &self,
        block: Block,
        index: usize,
        origin: Option<TrustIrInstId>,
        actual: &Instruction,
    ) -> bool {
        self.lir_block == block
            && self.lir_instruction == index
            && origin == Some(self.source_origin)
            && actual.args == self.lir_arguments
            && actual.results == [self.lir_result]
            && matches!(&actual.opcode, Opcode::Call { name, binding: DirectCallBinding::NativeDependency { function, .. } | DirectCallBinding::DeclaredExternalFunction { function } } if *function == self.callee.index() && name == &self.callee_name)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AggregateFieldIntent {
    call: usize,
    source_block: u32,
    source_instruction: usize,
    source_origin: TrustIrInstId,
    source_result: ValueId,
    field: u32,
    lir_block: Block,
    lir_instruction: usize,
    pointer: Value,
    result: Value,
}
impl AggregateFieldIntent {
    pub fn call(&self) -> usize {
        self.call
    }
    pub fn source_block(&self) -> u32 {
        self.source_block
    }
    pub fn source_instruction(&self) -> usize {
        self.source_instruction
    }
    pub fn source_origin(&self) -> TrustIrInstId {
        self.source_origin
    }
    pub fn source_result(&self) -> ValueId {
        self.source_result
    }
    pub fn field(&self) -> u32 {
        self.field
    }
    pub fn lir_block(&self) -> Block {
        self.lir_block
    }
    pub fn lir_instruction(&self) -> usize {
        self.lir_instruction
    }
    pub fn pointer(&self) -> Value {
        self.pointer
    }
    pub fn result(&self) -> Value {
        self.result
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn from_adapter(
        call_index: usize,
        call: &AggregateCallIntent,
        source_block: u32,
        source_instruction: usize,
        source_origin: TrustIrInstId,
        node: &trust_ir::InstrNode,
        lir_block: Block,
        lir_instruction: usize,
        emitted: &[Instruction],
    ) -> Option<Self> {
        let Inst::ExtractField {
            ty,
            aggregate,
            field,
        } = &node.inst
        else {
            return None;
        };
        if *aggregate != call.source_result
            || source_block != call.source_block
            || source_instruction <= call.source_instruction
            || *field >= 2
        {
            return None;
        }
        if AggregateFieldCodec::source(ty)? != call.layout.fields[*field as usize] {
            return None;
        }
        let [source_result] = node.results.as_slice() else {
            return None;
        };
        let [gep, load] = emitted else { return None };
        let [pointer] = gep.results.as_slice() else {
            return None;
        };
        let [result] = load.results.as_slice() else {
            return None;
        };
        if !matches!(&gep.opcode, Opcode::StructGep { struct_ty, field_index } if *struct_ty == call.layout.carrier() && *field_index == *field)
            || gep.args != [call.lir_result]
            || load.args != [*pointer]
            || !matches!(
                load.opcode,
                Opcode::Load {
                    ty: Type::I64,
                    align: None
                }
            )
        {
            return None;
        }
        Some(Self {
            call: call_index,
            source_block,
            source_instruction,
            source_origin,
            source_result: *source_result,
            field: *field,
            lir_block,
            lir_instruction,
            pointer: *pointer,
            result: *result,
        })
    }
}

/// Production adapter output, with bounded record-specific intent. It proves
/// no source operation, callee behavior, memory permission or frame property.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AggregateCallIntents {
    caller: Option<FuncId>,
    caller_name: String,
    calls: Vec<AggregateCallIntent>,
    fields: Vec<AggregateFieldIntent>,
    truncated: bool,
}
impl AggregateCallIntents {
    pub fn calls(&self) -> &[AggregateCallIntent] {
        &self.calls
    }
    pub fn fields(&self) -> &[AggregateFieldIntent] {
        &self.fields
    }
    pub fn caller(&self) -> Option<FuncId> {
        self.caller
    }
    pub fn caller_name(&self) -> &str {
        &self.caller_name
    }
    pub fn truncated(&self) -> bool {
        self.truncated
    }
    pub(crate) fn admit_source_origin(&mut self, origin: TrustIrInstId) -> bool {
        if origin.0 >= 256 {
            self.truncated = true;
        }
        !self.truncated
    }
    pub(crate) fn compact(&mut self) {
        self.calls.shrink_to_fit();
        self.fields.shrink_to_fit();
    }
    pub(crate) fn record_call(
        &mut self,
        caller: &trust_ir::Function,
        value: AggregateCallIntent,
    ) -> Option<usize> {
        if self.truncated {
            return None;
        }
        if self.calls.len() == MAX_CALLS || caller.name.len() > 4096 {
            self.truncated = true;
            return None;
        }
        self.caller = Some(caller.id);
        if self.caller_name.is_empty() {
            self.caller_name = caller.name.clone();
        }
        let index = self.calls.len();
        self.calls.push(value);
        Some(index)
    }
    pub(crate) fn record_field(&mut self, value: AggregateFieldIntent) {
        if self.truncated {
            return;
        }
        if self.fields.len() == MAX_FIELDS {
            self.truncated = true;
            return;
        }
        self.fields.push(value);
    }
    /// Recheck exact original call/field occurrences and retained instructions.
    /// Input-value/world equivalence and all storage/provider facts remain owed.
    pub fn validate(&self, module: &Module, lir: &Function) -> Result<(), &'static str> {
        if self.truncated {
            return Err("truncated aggregate source intent");
        }
        if self.calls.is_empty() {
            return if self.fields.is_empty() {
                Ok(())
            } else {
                Err("aggregate fields without calls")
            };
        }
        if module.functions.len() > 384
            || self.calls.len() > MAX_CALLS
            || self.fields.len() > MAX_FIELDS
        {
            return Err("aggregate source intent resources");
        }
        let mut sources = module
            .functions
            .iter()
            .filter(|f| Some(f.id) == self.caller);
        let source = sources.next().ok_or("foreign aggregate source intent")?;
        if sources.next().is_some()
            || source.name != self.caller_name
            || module
                .functions
                .iter()
                .filter(|f| f.name == self.caller_name)
                .count()
                != 1
            || lir.name != self.caller_name
            || source.blocks.len() > 16
        {
            return Err("ambiguous aggregate source intent");
        }
        let mut total = 0usize;
        let mut count = 0usize;
        for block in &source.blocks {
            total = total
                .checked_add(block.body.len())
                .filter(|n| *n <= 256)
                .ok_or("aggregate source intent resources")?;
            if block.params.len() > 8 {
                return Err("aggregate source parameter resources");
            }
            count = count
                .checked_add(block.params.len())
                .filter(|n| *n <= 384)
                .ok_or("aggregate source values")?;
            for node in &block.body {
                if node.results.len() > 8 {
                    return Err("aggregate source result resources");
                }
                count = count
                    .checked_add(node.results.len())
                    .filter(|n| *n <= 384)
                    .ok_or("aggregate source values")?;
            }
        }
        let mut block_ids = std::collections::HashSet::new();
        let mut definitions = std::collections::HashSet::new();
        for block in &source.blocks {
            if !block_ids.insert(block.id) {
                return Err("duplicate aggregate source block");
            }
            for value in block
                .params
                .iter()
                .map(|(id, _)| id)
                .chain(block.body.iter().flat_map(|n| &n.results))
            {
                if !definitions.insert(*value) {
                    return Err("duplicate aggregate source definition");
                }
            }
        }
        let node = |block: u32,
                    index: usize,
                    origin: TrustIrInstId|
         -> Result<&trust_ir::InstrNode, &'static str> {
            let mut base = 0usize;
            let mut result = None;
            for b in &source.blocks {
                if b.id.index() == block {
                    if result.is_some() {
                        return Err("duplicate aggregate source block");
                    }
                    result = b.body.get(index);
                    if base + index != origin.0 as usize {
                        return Err("stale aggregate source origin");
                    }
                }
                base += b.body.len();
            }
            result.ok_or("missing aggregate source occurrence")
        };
        let mut call_origins = std::collections::HashSet::new();
        for call in &self.calls {
            if !call_origins.insert(call.source_origin) {
                return Err("duplicate aggregate call intent");
            }
            let source_node = node(
                call.source_block,
                call.source_instruction,
                call.source_origin,
            )?;
            let actual = lir
                .blocks
                .get(&call.lir_block)
                .and_then(|b| b.instructions.get(call.lir_instruction))
                .ok_or("missing aggregate retained call")?;
            let origin = lir
                .trust_ir_origins
                .get(&call.lir_block)
                .and_then(|o| o.get(call.lir_instruction))
                .copied()
                .flatten();
            if !call.matches_lir(call.lir_block, call.lir_instruction, origin, actual) {
                return Err("stale aggregate retained call");
            }
            // Independently rebuild the source input from its original node.
            let mut pending = actual.clone();
            if let Opcode::Call { binding, .. } = &mut pending.opcode {
                *binding = DirectCallBinding::DeclaredExternalFunction {
                    function: call.callee.index(),
                };
            }
            let rebuilt = AggregateCallIntent::from_adapter(
                module,
                source,
                call.source_block,
                call.source_instruction,
                call.source_origin,
                source_node,
                call.lir_block,
                call.lir_instruction,
                &[pending],
            )
            .ok_or("unsupported aggregate original call/layout")?;
            if rebuilt != *call
                || lir.value_types.get(&call.lir_result) != Some(&call.layout.carrier())
            {
                return Err("aggregate original call/layout differs");
            }
        }
        let mut field_origins = std::collections::HashSet::new();
        for field in &self.fields {
            if !field_origins.insert(field.source_origin) {
                return Err("duplicate aggregate field intent");
            }
            let call = self
                .calls
                .get(field.call)
                .ok_or("foreign aggregate field owner")?;
            let source_node = node(
                field.source_block,
                field.source_instruction,
                field.source_origin,
            )?;
            let block = lir
                .blocks
                .get(&field.lir_block)
                .ok_or("missing aggregate field block")?;
            let group = block
                .instructions
                .get(
                    field.lir_instruction
                        ..field
                            .lir_instruction
                            .checked_add(2)
                            .ok_or("aggregate field index overflow")?,
                )
                .ok_or("missing aggregate field instructions")?;
            let origins = lir
                .trust_ir_origins
                .get(&field.lir_block)
                .and_then(|o| o.get(field.lir_instruction..field.lir_instruction + 2))
                .ok_or("missing aggregate field origins")?;
            if origins != [Some(field.source_origin); 2] {
                return Err("stale aggregate field origins");
            }
            let rebuilt = AggregateFieldIntent::from_adapter(
                field.call,
                call,
                field.source_block,
                field.source_instruction,
                field.source_origin,
                source_node,
                field.lir_block,
                field.lir_instruction,
                group,
            )
            .ok_or("aggregate original field/retained load differs")?;
            if rebuilt != *field {
                return Err("aggregate field binding differs");
            }
        }
        let source_fields = source
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .filter(|n| {
                matches!(&n.inst, Inst::ExtractField { aggregate, .. }
                if self.calls.iter().any(|c| c.source_result == *aggregate))
            })
            .count();
        if source_fields != self.fields.len() {
            return Err("aggregate original field occurrence census differs");
        }
        Ok(())
    }
}

/// Obligations that this syntactic transport deliberately does NOT discharge.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AggregateTransportRequirement {
    MatchingInputsAndPriorWorld,
    RuntimeProviderAbiAndOutcomeRelation,
    NormalContinuation,
    LiveAlignedNonwrappingResultStorage,
    InitializationAndFieldLoadSemantics,
    SourcePrivateMemoryRelation,
}

/// Coordinates recorded by the real selector at allocation/emission time.
/// A plan is neither a memory owner nor a proof that any provider satisfies C.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AggregateMaterializationPlan {
    intent: AggregateCallIntent,
    binding: DirectCallBinding,
    abi: crate::abi::AArch64AbiVariant,
    block: Block,
    call: usize,
    address: usize,
    stores: [usize; 2],
    slot: u32,
    pointer: trust_cg_ir::VReg,
    registers: [crate::abi::PReg; 2],
    fields: Vec<AggregateFieldMaterializationPlan>,
}

/// Actual selector-created field address/load coordinates. No memory license.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AggregateFieldMaterializationPlan {
    intent: AggregateFieldIntent,
    address: usize,
    load: usize,
    pointer: trust_cg_ir::VReg,
    result: trust_cg_ir::VReg,
}
impl AggregateFieldMaterializationPlan {
    pub fn intent(&self) -> &AggregateFieldIntent {
        &self.intent
    }
    pub fn address_instruction(&self) -> usize {
        self.address
    }
    pub fn load_instruction(&self) -> usize {
        self.load
    }
    pub fn pointer(&self) -> trust_cg_ir::VReg {
        self.pointer
    }
    pub fn result(&self) -> trust_cg_ir::VReg {
        self.result
    }
    pub(crate) fn emitted(
        intent: AggregateFieldIntent,
        address: usize,
        load: usize,
        owner: &AggregateMaterializationPlan,
        actual: &crate::isel::ISelFunction,
    ) -> Result<Self, &'static str> {
        use crate::isel::ISelOperand as O;
        let block = actual
            .blocks
            .get(&owner.block)
            .ok_or("missing aggregate field block")?;
        let pointer = match block.insts.get(address).and_then(|i| i.operands.first()) {
            Some(O::VReg(r)) if r.class == trust_cg_ir::RegClass::Gpr64 => *r,
            _ => return Err("aggregate field pointer class"),
        };
        let result = match block.insts.get(load).and_then(|i| i.operands.first()) {
            Some(O::VReg(r)) if r.class == trust_cg_ir::RegClass::Gpr64 => *r,
            _ => return Err("aggregate field result class"),
        };
        let value = Self {
            intent,
            address,
            load,
            pointer,
            result,
        };
        value.validate(owner, actual)?;
        Ok(value)
    }
    fn validate(
        &self,
        owner: &AggregateMaterializationPlan,
        actual: &crate::isel::ISelFunction,
    ) -> Result<(), &'static str> {
        use crate::isel::ISelOperand as O;
        use trust_cg_ir::{AArch64Opcode as A, LoweringProvenance};
        let block = actual
            .blocks
            .get(&owner.block)
            .ok_or("missing aggregate field block")?;
        if self.intent.lir_block != owner.block
            || self.intent.field >= 2
            || !(owner.stores[1] < self.address && self.address < self.load)
            || self.pointer.class != trust_cg_ir::RegClass::Gpr64
            || self.result.class != trust_cg_ir::RegClass::Gpr64
        {
            return Err("aggregate field owner/order/class");
        }
        let offset = owner.intent.layout.offsets[self.intent.field as usize] as i64;
        let address = block
            .insts
            .get(self.address)
            .ok_or("missing aggregate field address")?;
        let mut operands = vec![O::VReg(self.pointer), O::VReg(owner.pointer)];
        let opcode = if offset == 0 {
            A::MovR
        } else {
            operands.push(O::Imm(offset));
            A::AddRI
        };
        if address.opcode != opcode || address.operands != operands {
            return Err("aggregate field address differs");
        }
        let load = block
            .insts
            .get(self.load)
            .ok_or("missing aggregate field load")?;
        if load.opcode != A::LdrRI
            || load.operands != [O::VReg(self.result), O::VReg(self.pointer), O::Imm(0)]
        {
            return Err("aggregate field load differs");
        }
        for (selected, lir) in [
            (self.address, self.intent.lir_instruction),
            (self.load, self.intent.lir_instruction + 1),
        ] {
            if !matches!(block.lowering_provenance.get(selected),Some(LoweringProvenance::SourceInst{id,trust_ir_inst:Some(origin),..}) if id.block==self.intent.lir_block.0 && id.index==lir as u32 && *origin==self.intent.source_origin)
            {
                return Err("aggregate field selected source occurrence differs");
            }
        }
        Ok(())
    }
}
impl AggregateMaterializationPlan {
    pub fn intent(&self) -> &AggregateCallIntent {
        &self.intent
    }
    pub fn binding(&self) -> DirectCallBinding {
        self.binding
    }
    pub fn block(&self) -> Block {
        self.block
    }
    pub fn call_instruction(&self) -> usize {
        self.call
    }
    pub fn address_instruction(&self) -> usize {
        self.address
    }
    pub fn store_instructions(&self) -> &[usize; 2] {
        &self.stores
    }
    pub fn slot(&self) -> u32 {
        self.slot
    }
    pub fn pointer(&self) -> trust_cg_ir::VReg {
        self.pointer
    }
    pub fn return_registers(&self) -> &[crate::abi::PReg; 2] {
        &self.registers
    }
    pub fn fields(&self) -> &[AggregateFieldMaterializationPlan] {
        &self.fields
    }
    pub(crate) fn record_field(&mut self, field: AggregateFieldMaterializationPlan) {
        self.fields.push(field);
    }
    pub fn unresolved_requirements(&self) -> [AggregateTransportRequirement; 6] {
        use AggregateTransportRequirement::*;
        [
            MatchingInputsAndPriorWorld,
            RuntimeProviderAbiAndOutcomeRelation,
            NormalContinuation,
            LiveAlignedNonwrappingResultStorage,
            InitializationAndFieldLoadSemantics,
            SourcePrivateMemoryRelation,
        ]
    }
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn emitted(
        intent: AggregateCallIntent,
        binding: DirectCallBinding,
        abi: crate::abi::AArch64AbiVariant,
        block: Block,
        call: usize,
        address: usize,
        stores: [usize; 2],
        slot: u32,
        pointer: trust_cg_ir::VReg,
        registers: [crate::abi::PReg; 2],
        actual: &crate::isel::ISelFunction,
    ) -> Result<Self, &'static str> {
        let value = Self {
            intent,
            binding,
            abi,
            block,
            call,
            address,
            stores,
            slot,
            pointer,
            registers,
            fields: Vec::new(),
        };
        value.validate_emitted(actual)?;
        Ok(value)
    }
    fn validate_emitted(&self, actual: &crate::isel::ISelFunction) -> Result<(), &'static str> {
        use crate::isel::ISelOperand as O;
        use trust_cg_ir::{AArch64Opcode as A, LoweringProvenance};
        let intent = &self.intent;
        if actual.name.is_empty()
            || self.abi != crate::abi::AArch64AbiVariant::Darwin
            || !matches!(self.binding, DirectCallBinding::NativeDependency { function, .. } if function==intent.callee.index())
        {
            return Err("aggregate native call binding/ABI");
        }
        let expected = crate::abi::AppleAArch64ABI::classify_returns(&[intent.layout.carrier()]);
        if !matches!(expected.as_slice(),[crate::abi::ArgLocation::RegPair(a,b)] if self.registers==[*a,*b])
        {
            return Err("aggregate return locations differ from original layout");
        }
        let slot = actual
            .stack_slots
            .get(self.slot as usize)
            .ok_or("missing aggregate result slot")?;
        if u64::from(slot.size) != intent.layout.bytes
            || u64::from(slot.align) != intent.layout.align
            || slot.allocation != trust_cg_ir::function::StackSlotAllocationKind::Fixed
        {
            return Err("aggregate result slot extent/alignment differs");
        }
        let block = actual
            .blocks
            .get(&self.block)
            .ok_or("missing aggregate materialization block")?;
        let at = |index| {
            block
                .insts
                .get(index)
                .ok_or("missing aggregate materialization instruction")
        };
        let call = at(self.call)?;
        if call.opcode != A::Bl
            || call.operands != [O::Symbol(intent.callee_name.clone())]
            || !self
                .registers
                .iter()
                .all(|r| call.implicit_defs.contains(r))
        {
            return Err("aggregate call/return register use differs");
        }
        if !(self.call < self.address
            && self.address < self.stores[0]
            && self.stores[0] < self.stores[1])
        {
            return Err("aggregate materialization order differs");
        }
        let address = at(self.address)?;
        if address.opcode != A::AddPCRel
            || address.operands
                != [
                    O::VReg(self.pointer),
                    O::PReg(trust_cg_ir::regs::SP),
                    O::StackSlot(self.slot),
                ]
        {
            return Err("aggregate slot address differs");
        }
        for (field, index) in self.stores.iter().copied().enumerate() {
            let store = at(index)?;
            if store.opcode != A::StrRI
                || store.operands
                    != [
                        O::PReg(self.registers[field]),
                        O::VReg(self.pointer),
                        O::Imm(intent.layout.offsets[field] as i64),
                    ]
            {
                return Err("aggregate return-lane store differs");
            }
        }
        for index in [self.call, self.address, self.stores[0], self.stores[1]] {
            if !matches!(block.lowering_provenance.get(index),Some(LoweringProvenance::SourceInst { id, trust_ir_inst:Some(origin), .. }) if *id==intent.source_site() && *origin==intent.source_origin)
            {
                return Err("aggregate materialization source occurrence differs");
            }
        }
        Ok(())
    }
    /// Independently recheck current original inputs and actual emitted slots/
    /// operations; a stale/foreign plan cannot be rebound by matching a digest.
    pub fn validate(
        &self,
        module: &Module,
        lir: &Function,
        intents: &AggregateCallIntents,
        actual: &crate::isel::ISelFunction,
    ) -> Result<(), &'static str> {
        intents.validate(module, lir)?;
        if actual.name != lir.name || !intents.calls.iter().any(|c| c == &self.intent) {
            return Err("foreign aggregate materialization intent");
        }
        let call = lir
            .blocks
            .get(&self.intent.lir_block)
            .and_then(|b| b.instructions.get(self.intent.lir_instruction))
            .ok_or("missing aggregate bound call")?;
        if !matches!(call.opcode,Opcode::Call{binding,..} if binding==self.binding) {
            return Err("stale aggregate native dependency binding");
        }
        self.validate_emitted(actual)?;
        let call = intents
            .calls
            .iter()
            .position(|c| c == &self.intent)
            .ok_or("foreign aggregate field owner")?;
        let expected = intents
            .fields
            .iter()
            .filter(|f| f.call == call)
            .collect::<Vec<_>>();
        if expected.len() != self.fields.len()
            || !expected
                .iter()
                .zip(&self.fields)
                .all(|(a, b)| **a == b.intent)
        {
            return Err("aggregate selected field census differs");
        }
        for field in &self.fields {
            field.validate(self, actual)?;
        }
        Ok(())
    }
}

/// The SAME conversion's arena IDs, never inferred from opcode adjacency.
/// This is pre-optimization transport data, with no native or memory authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MappedAggregateMaterialization {
    plan: AggregateMaterializationPlan,
    call: trust_cg_ir::InstId,
    address: trust_cg_ir::InstId,
    stores: [trust_cg_ir::InstId; 2],
    fields: Vec<MappedAggregateField>,
}
/// Same-conversion arena IDs of a retained field address and load.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MappedAggregateField {
    plan: AggregateFieldMaterializationPlan,
    address: trust_cg_ir::InstId,
    load: trust_cg_ir::InstId,
}
impl MappedAggregateField {
    pub fn plan(&self) -> &AggregateFieldMaterializationPlan {
        &self.plan
    }
    pub fn address(&self) -> trust_cg_ir::InstId {
        self.address
    }
    pub fn load(&self) -> trust_cg_ir::InstId {
        self.load
    }
}
impl MappedAggregateMaterialization {
    pub fn plan(&self) -> &AggregateMaterializationPlan {
        &self.plan
    }
    pub fn call(&self) -> trust_cg_ir::InstId {
        self.call
    }
    pub fn address(&self) -> trust_cg_ir::InstId {
        self.address
    }
    pub fn stores(&self) -> &[trust_cg_ir::InstId; 2] {
        &self.stores
    }
    pub fn fields(&self) -> &[MappedAggregateField] {
        &self.fields
    }
    pub(crate) fn converted(
        plan: AggregateMaterializationPlan,
        ids: [trust_cg_ir::InstId; 4],
        fields: Vec<[trust_cg_ir::InstId; 2]>,
    ) -> Self {
        let fields = plan
            .fields
            .iter()
            .cloned()
            .zip(fields)
            .map(|(plan, [address, load])| MappedAggregateField {
                plan,
                address,
                load,
            })
            .collect();
        Self {
            plan,
            call: ids[0],
            address: ids[1],
            stores: [ids[2], ids[3]],
            fields,
        }
    }
    pub fn validate(
        &self,
        module: &Module,
        lir: &Function,
        intents: &AggregateCallIntents,
        isel: &crate::isel::ISelFunction,
        actual: &trust_cg_ir::MachFunction,
    ) -> Result<(), &'static str> {
        use trust_cg_ir::{AArch64Opcode as A, LoweringProvenance, MachOperand as O};
        self.plan.validate(module, lir, intents, isel)?;
        if actual.name != lir.name {
            return Err("foreign aggregate machine function");
        }
        let block = actual
            .blocks
            .get(self.plan.block.0 as usize)
            .ok_or("missing aggregate machine block")?;
        for (position, id) in [
            self.plan.call,
            self.plan.address,
            self.plan.stores[0],
            self.plan.stores[1],
        ]
        .into_iter()
        .zip([self.call, self.address, self.stores[0], self.stores[1]])
        {
            if block.insts.get(position) != Some(&id) || actual.insts.get(id.0 as usize).is_none() {
                return Err("stale aggregate conversion coordinate");
            }
            if !matches!(actual.inst_lowering_provenance(id),LoweringProvenance::SourceInst{id:source,trust_ir_inst:Some(origin),..} if source==self.plan.intent.source_site() && origin==self.plan.intent.source_origin)
            {
                return Err("aggregate converted source occurrence differs");
            }
        }
        let call = actual.inst(self.call);
        if call.opcode != A::Bl
            || call.operands.as_slice() != [O::Symbol(self.plan.intent.callee_name.clone())]
            || !self
                .plan
                .registers
                .iter()
                .all(|r| call.implicit_defs.contains(r))
        {
            return Err("aggregate converted call differs");
        }
        let address = actual.inst(self.address);
        if address.opcode != A::AddPCRel
            || address.operands.as_slice()
                != [
                    O::VReg(self.plan.pointer),
                    O::PReg(trust_cg_ir::regs::SP),
                    O::StackSlot(trust_cg_ir::types::StackSlotId(self.plan.slot)),
                ]
        {
            return Err("aggregate converted slot address differs");
        }
        for (field, id) in self.stores.iter().copied().enumerate() {
            let store = actual.inst(id);
            if store.opcode != A::StrRI
                || store.operands.as_slice()
                    != [
                        O::PReg(self.plan.registers[field]),
                        O::VReg(self.plan.pointer),
                        O::Imm(self.plan.intent.layout.offsets[field] as i64),
                    ]
            {
                return Err("aggregate converted field store differs");
            }
        }
        let slot = actual
            .stack_slots
            .get(self.plan.slot as usize)
            .ok_or("missing aggregate converted slot")?;
        if slot.size != self.plan.intent.layout.bytes as u32
            || slot.align != self.plan.intent.layout.align as u32
            || slot.allocation != trust_cg_ir::function::StackSlotAllocationKind::Fixed
        {
            return Err("aggregate converted slot facts differ");
        }
        if self.fields.len() != self.plan.fields.len() {
            return Err("aggregate converted field census differs");
        }
        for (field, expected) in self.fields.iter().zip(&self.plan.fields) {
            if &field.plan != expected {
                return Err("aggregate converted foreign field");
            }
            for (position, id) in [
                (expected.address, field.address),
                (expected.load, field.load),
            ] {
                if block.insts.get(position) != Some(&id)
                    || actual.insts.get(id.0 as usize).is_none()
                {
                    return Err("stale aggregate field conversion coordinate");
                }
                let selected = &isel.blocks[&self.plan.block].insts[position];
                let target = actual.inst(id);
                let operands = selected
                    .operands
                    .iter()
                    .map(|o| match o {
                        crate::isel::ISelOperand::VReg(r) => Ok(O::VReg(*r)),
                        crate::isel::ISelOperand::Imm(n) => Ok(O::Imm(*n)),
                        _ => Err("unsupported aggregate field conversion operand"),
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                if target.opcode != selected.opcode || target.operands.as_slice() != operands {
                    return Err("aggregate converted field operands differ");
                }
                let lir = if position == expected.address {
                    expected.intent.lir_instruction
                } else {
                    expected.intent.lir_instruction + 1
                };
                if !matches!(actual.inst_lowering_provenance(id),LoweringProvenance::SourceInst{id:site,trust_ir_inst:Some(origin),..} if site.block==expected.intent.lir_block.0 && site.index==lir as u32 && origin==expected.intent.source_origin)
                {
                    return Err("aggregate converted field origin differs");
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "aggregate_call_transport_tests.rs"]
mod tests;
