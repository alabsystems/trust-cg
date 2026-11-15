// Copyright 2026 Andrew Yates | Apache-2.0

//! Checked projection of retained scalar edge-copy groups into SSA arguments.
//!
//! This is a local LIR transport check, not a source-body, call/ABI, memory,
//! machine or publication theorem. Original source and LIR remain borrowed and
//! unchanged. Every omitted Copy must belong to a checked exact source edge;
//! arbitrary repeated definitions remain invalid. Other body semantics still
//! require the ordinary complete observation owner.

use super::*;
use trust_cg_lower::instructions::{Block as LirBlock, Value as LirValue};
use trust_cg_lower::{Function, Type};
use trust_ir::{BlockId, Constant, Inst, Ty, ValueId};

type Result<T> = std::result::Result<T, ReadOnlySourceError>;
fn refuse(s: &'static str) -> ReadOnlySourceError {
    ReadOnlySourceError::Lowering(s)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScalarEdgeCodec {
    Signed64,
    Unsigned64,
    Pointer,
    Signed32,
    Unsigned32,
    Boolean,
}
impl ScalarEdgeCodec {
    pub(super) fn source(ty: &Ty) -> Option<Self> {
        Some(match ty {
            Ty::I64 => Self::Signed64,
            Ty::U64 => Self::Unsigned64,
            Ty::Ptr => Self::Pointer,
            Ty::I32 => Self::Signed32,
            Ty::U32 => Self::Unsigned32,
            Ty::Bool => Self::Boolean,
            _ => return None,
        })
    }
    pub(super) fn carrier(self) -> Type {
        match self {
            Self::Signed64 | Self::Unsigned64 | Self::Pointer => Type::I64,
            Self::Signed32 | Self::Unsigned32 => Type::I32,
            Self::Boolean => Type::B1,
        }
    }
}

/// One exact original edge and its checked retained copy suffix. The ordered
/// argument vector denotes simultaneous intake, independent of scheduler order.
pub struct ScalarEdgeTransport {
    pub source_block: u32,
    pub source_instruction: usize,
    pub source_edge: usize,
    pub source_target: u32,
    pub lowering_block: u32,
    pub lowering_target: u32,
    pub copy_instructions: Vec<usize>,
    pub source_arguments: Vec<u32>,
    pub lowering_arguments: Vec<u32>,
    pub parameter_codecs: Vec<ScalarEdgeCodec>,
}

/// Immutable custody of precisely the checked borrowed endpoints, never a
/// transferable source, body or native receipt. A foreign endpoint cannot reuse
/// this projection, and Rust's shared borrows prevent mutation while it lives.
pub struct CheckedScalarBlockArguments<'a> {
    module: &'a Module,
    ordinal: usize,
    lir: &'a Function,
    transports: Vec<ScalarEdgeTransport>,
    omitted: HashSet<(u32, usize)>,
    jump_arguments: HashMap<u32, Vec<u32>>,
}
impl<'a> CheckedScalarBlockArguments<'a> {
    pub fn module(&self) -> &'a Module {
        self.module
    }
    pub fn source(&self) -> &'a trust_ir::Function {
        &self.module.functions[self.ordinal]
    }
    pub fn lir(&self) -> &'a Function {
        self.lir
    }
    pub fn transports(&self) -> &[ScalarEdgeTransport] {
        &self.transports
    }
    pub(super) fn matches(&self, module: &Module, ordinal: usize, lir: &Function) -> bool {
        std::ptr::eq(self.module, module) && self.ordinal == ordinal && std::ptr::eq(self.lir, lir)
    }
    pub(super) fn omitted(&self, block: u32, instruction: usize) -> bool {
        self.omitted.contains(&(block, instruction))
    }
    pub(super) fn jump_arguments(&self, block: u32) -> Option<&[u32]> {
        self.jump_arguments.get(&block).map(Vec::as_slice)
    }
}

struct SourceBlock<'a> {
    block: &'a trust_ir::Block,
    terminal: u32,
}
struct SourceEdge<'a> {
    block: BlockId,
    instruction: usize,
    ordinal: usize,
    target: BlockId,
    args: &'a [ValueId],
}

fn source_edges<'a>(
    source: &'a trust_ir::Function,
) -> Result<(Vec<SourceBlock<'a>>, Vec<SourceEdge<'a>>)> {
    if source.blocks.is_empty() || source.blocks.len() > MAX_BLOCKS {
        return Err(ReadOnlySourceError::Budget("scalar edge source blocks"));
    }
    // Admit complete local instruction/definition counts before any identity
    // maps are built. The separately observed module identity is not this
    // profile's 256-node/384-definition admission.
    let mut admitted_nodes = 0usize;
    let mut admitted_definitions = 0usize;
    for block in &source.blocks {
        admitted_nodes = admitted_nodes
            .checked_add(block.body.len())
            .filter(|n| *n <= MAX_INSTRUCTIONS)
            .ok_or(ReadOnlySourceError::Budget(
                "scalar edge source instructions",
            ))?;
        admitted_definitions = admitted_definitions
            .checked_add(block.params.len())
            .filter(|n| *n <= MAX_VALUES)
            .ok_or(ReadOnlySourceError::Budget("scalar edge source values"))?;
        for node in &block.body {
            if node.results.len() > 8 {
                return Err(ReadOnlySourceError::Budget(
                    "scalar edge source result arity",
                ));
            }
            admitted_definitions = admitted_definitions
                .checked_add(node.results.len())
                .filter(|n| *n <= MAX_VALUES)
                .ok_or(ReadOnlySourceError::Budget("scalar edge source values"))?;
        }
    }
    let mut blocks = Vec::new();
    let mut edges = Vec::new();
    let mut total = 0usize;
    let mut ids = HashSet::new();
    let mut defs = HashSet::new();
    for b in &source.blocks {
        if !ids.insert(b.id) || b.body.is_empty() || b.params.len() > 8 {
            return Err(refuse("scalar edge source block identity/arity"));
        }
        for (id, _) in &b.params {
            if !defs.insert(*id) {
                return Err(refuse("duplicate scalar edge source definition"));
            }
        }
        for (i, n) in b.body.iter().enumerate() {
            if n.results.len() > 8 || n.results.iter().any(|id| !defs.insert(*id)) {
                return Err(refuse("duplicate scalar edge source definition"));
            }
            let terminal = matches!(
                n.inst,
                Inst::Br { .. } | Inst::CondBr { .. } | Inst::Return { .. }
            );
            if terminal != (i + 1 == b.body.len()) {
                return Err(refuse("scalar edge source terminator position"));
            }
        }
        total = total
            .checked_add(b.body.len())
            .filter(|n| *n <= MAX_INSTRUCTIONS)
            .ok_or(ReadOnlySourceError::Budget(
                "scalar edge source instructions",
            ))?;
        blocks.push(SourceBlock {
            block: b,
            terminal: (total - 1) as u32,
        });
        let i = b.body.len() - 1;
        match &b.body[i].inst {
            Inst::Br { target, args } => edges.push(SourceEdge {
                block: b.id,
                instruction: i,
                ordinal: 0,
                target: *target,
                args,
            }),
            Inst::CondBr {
                then_target,
                then_args,
                else_target,
                else_args,
                ..
            } => {
                edges.push(SourceEdge {
                    block: b.id,
                    instruction: i,
                    ordinal: 0,
                    target: *then_target,
                    args: then_args,
                });
                edges.push(SourceEdge {
                    block: b.id,
                    instruction: i,
                    ordinal: 1,
                    target: *else_target,
                    args: else_args,
                });
            }
            Inst::Return { values } if values.len() <= 8 => {}
            _ => return Err(refuse("unsupported scalar edge source terminator")),
        }
    }
    if defs.len() > MAX_VALUES {
        return Err(ReadOnlySourceError::Budget("scalar edge source values"));
    }
    for edge in &edges {
        if edge.args.len() > 8 || !ids.contains(&edge.target) {
            return Err(refuse("scalar edge source target/arity"));
        }
        let target = source.blocks.iter().find(|b| b.id == edge.target).unwrap();
        if edge.args.len() != target.params.len() {
            return Err(refuse("scalar edge source argument arity"));
        }
    }
    Ok((blocks, edges))
}

fn target_successors(inst: &trust_cg_lower::instructions::Instruction) -> Result<Vec<LirBlock>> {
    match &inst.opcode {
        Opcode::Jump { dest } if inst.args.is_empty() && inst.results.is_empty() => Ok(vec![*dest]),
        Opcode::Brif {
            cond,
            then_dest,
            else_dest,
        } if inst.args.as_slice() == [*cond] && inst.results.is_empty() => {
            Ok(vec![*then_dest, *else_dest])
        }
        Opcode::Return if inst.results.is_empty() && inst.args.len() <= 8 => Ok(vec![]),
        _ => Err(refuse("unsupported scalar edge retained terminator")),
    }
}

// Complete bounded acyclic census. No branch or cold block is pruned.
fn dominators(ids: &[u32], entry: u32, edges: &[(u32, u32)]) -> Result<HashMap<u32, HashSet<u32>>> {
    let all: HashSet<_> = ids.iter().copied().collect();
    if all.len() != ids.len() || !all.contains(&entry) {
        return Err(refuse("scalar edge CFG identity"));
    }
    let mut pred: HashMap<u32, Vec<u32>> = ids.iter().map(|id| (*id, vec![])).collect();
    let mut degree: HashMap<u32, usize> = ids.iter().map(|id| (*id, 0)).collect();
    for (from, to) in edges {
        if !all.contains(from) || !all.contains(to) {
            return Err(refuse("scalar edge missing CFG target"));
        }
        pred.get_mut(to).unwrap().push(*from);
        *degree.get_mut(to).unwrap() += 1;
    }
    let mut ready = vec![entry];
    let mut done = HashSet::new();
    let mut dom: HashMap<u32, HashSet<u32>> = HashMap::new();
    if degree[&entry] != 0 {
        return Err(refuse("cyclic scalar edge CFG"));
    }
    while let Some(id) = ready.pop() {
        if !done.insert(id) {
            continue;
        }
        let mut d = all.clone();
        for p in &pred[&id] {
            let pd = dom.get(p).ok_or(refuse("nondominating scalar edge CFG"))?;
            d.retain(|v| pd.contains(v));
        }
        if id == entry {
            d.clear();
        }
        d.insert(id);
        dom.insert(id, d);
        for (_, to) in edges.iter().filter(|(from, _)| *from == id) {
            let n = degree.get_mut(to).unwrap();
            *n -= 1;
            if *n == 0 {
                ready.push(*to);
            }
        }
    }
    if done.len() != ids.len() {
        return Err(refuse("cyclic or unreachable scalar edge CFG"));
    }
    Ok(dom)
}

fn result_codecs(module: &Module, node: &trust_ir::InstrNode) -> Vec<Option<ScalarEdgeCodec>> {
    let one = match &node.inst {
        Inst::Const { ty, .. }
        | Inst::Copy { ty, .. }
        | Inst::BinOp { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::Select { ty, .. } => ScalarEdgeCodec::source(ty),
        Inst::ICmp { .. } => Some(ScalarEdgeCodec::Boolean),
        Inst::NullPtr | Inst::GEP { .. } => Some(ScalarEdgeCodec::Pointer),
        Inst::Call { callee, .. } => {
            let Some(function) = module.functions.iter().find(|f| f.id == *callee) else {
                return vec![None; node.results.len()];
            };
            let Some(sig) = module.func_types.get(function.ty.index() as usize) else {
                return vec![None; node.results.len()];
            };
            return sig.returns.iter().map(ScalarEdgeCodec::source).collect();
        }
        _ => None,
    };
    if node.results.len() == 1 {
        vec![one]
    } else {
        vec![None; node.results.len()]
    }
}

/// Only bind source result positions at their actual original instruction
/// occurrence. This is a carrier census, not a theorem about that operation.
/// The complete body observer still independently models every operation.
fn result_carriers(
    module: &Module,
    node: &trust_ir::InstrNode,
    group: &[&trust_cg_lower::instructions::Instruction],
) -> Option<Vec<LirValue>> {
    let [inst] = group else { return None };
    if node.results.len() != inst.results.len() {
        return None;
    }
    let same = match (&node.inst, &inst.opcode) {
        (
            Inst::Const {
                ty,
                value: Constant::Int(value),
            },
            Opcode::Iconst { ty: actual, imm },
        ) => {
            ScalarEdgeCodec::source(ty).is_some_and(|c| c.carrier() == *actual)
                && match ty {
                    Ty::I64 => i64::try_from(*value).ok() == Some(*imm),
                    Ty::U64 => u64::try_from(*value).ok().map(|n| n as i64) == Some(*imm),
                    Ty::I32 => i32::try_from(*value)
                        .ok()
                        .is_some_and(|n| n as u32 == *imm as u32),
                    Ty::U32 => u32::try_from(*value).ok().is_some_and(|n| n == *imm as u32),
                    _ => false,
                }
        }
        (
            Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(value),
            },
            Opcode::Iconst { ty: Type::B1, imm },
        ) => *imm == i64::from(*value),
        (
            Inst::NullPtr,
            Opcode::Iconst {
                ty: Type::I64,
                imm: 0,
            },
        ) => true,
        (Inst::Copy { .. }, Opcode::Copy) => true,
        (Inst::ICmp { op, .. }, Opcode::Icmp { cond }) => {
            trust_cg_lower::instructions::intcc_of_icmp(*op) == *cond
        }
        (
            Inst::Load {
                ty,
                volatile: false,
                align,
                ..
            },
            Opcode::Load {
                ty: actual,
                align: actual_align,
            },
        ) => {
            ScalarEdgeCodec::source(ty).is_some_and(|c| c.carrier() == *actual)
                && match align {
                    None => actual_align.is_none(),
                    Some(n) => u32::try_from(*n).ok() == *actual_align,
                }
        }
        (
            Inst::Select { .. },
            Opcode::Select {
                cond: IntCC::NotEqual,
            },
        ) => true,
        (Inst::Call { callee, args }, Opcode::Call { name, binding }) => {
            let id = match binding {
                trust_cg_lower::instructions::DirectCallBinding::ExactModuleFunction {
                    function,
                }
                | trust_cg_lower::instructions::DirectCallBinding::DeclaredExternalFunction {
                    function,
                }
                | trust_cg_lower::instructions::DirectCallBinding::NativeDependency {
                    function,
                    ..
                } => *function,
                _ => return None,
            };
            id == callee.index()
                && args.len() == inst.args.len()
                && module
                    .functions
                    .iter()
                    .any(|f| f.id == *callee && f.name == *name)
        }
        _ => false,
    };
    same.then(|| inst.results.clone())
}

/// Check an exact original source function and its retained LIR, then retain
/// only the simultaneous scalar edge transfers that have actually been emitted.
/// This accepts no source/body/native proof and changes neither input.
pub fn check_scalar_block_arguments<'a>(
    module: &'a Module,
    ordinal: usize,
    lir: &'a Function,
) -> Result<CheckedScalarBlockArguments<'a>> {
    // Reuse the complete existing charged input identity inventory, including
    // unused bodies/metadata/deep types, before building projection maps.
    if module.functions.len() > MAX_VALUES || module.func_types.len() > MAX_VALUES {
        return Err(ReadOnlySourceError::Budget("scalar edge module inventory"));
    }
    conditional_wrapper::module_digest(module)?;
    conditional_wrapper::lowering_digest(std::slice::from_ref(lir))?;
    let source = module
        .functions
        .get(ordinal)
        .ok_or(refuse("missing scalar edge source"))?;
    if source.name != lir.name || lir.blocks.is_empty() || lir.blocks.len() > MAX_BLOCKS {
        return Err(refuse("foreign scalar edge function"));
    }
    if module
        .functions
        .iter()
        .filter(|f| f.id == source.id)
        .count()
        != 1
        || module
            .functions
            .iter()
            .filter(|f| f.name == source.name)
            .count()
            != 1
    {
        return Err(refuse("ambiguous scalar edge source identity"));
    }
    let (source_blocks, edges) = source_edges(source)?;
    let source_cfg: Vec<_> = edges
        .iter()
        .map(|e| (e.block.index(), e.target.index()))
        .collect();
    let source_ids: Vec<_> = source.blocks.iter().map(|b| b.id.index()).collect();
    let source_dom = dominators(&source_ids, source.entry.index(), &source_cfg)?;
    let signature = module
        .func_types
        .get(source.ty.index() as usize)
        .ok_or(refuse("missing scalar edge source signature"))?;
    let params = signature
        .params
        .iter()
        .map(|t| {
            ScalarEdgeCodec::source(t)
                .map(ScalarEdgeCodec::carrier)
                .ok_or(refuse("unsupported scalar edge signature codec"))
        })
        .collect::<Result<Vec<_>>>()?;
    let returns = signature
        .returns
        .iter()
        .map(|t| {
            ScalarEdgeCodec::source(t)
                .map(ScalarEdgeCodec::carrier)
                .ok_or(refuse("unsupported scalar edge return codec"))
        })
        .collect::<Result<Vec<_>>>()?;
    if signature.is_vararg || params != lir.signature.params || returns != lir.signature.returns {
        return Err(refuse("scalar edge signature/carrier mismatch"));
    }
    let mut target_cfg = Vec::new();
    let mut total = 0usize;
    let mut incoming: HashMap<u32, usize> = HashMap::new();
    for (id, b) in &lir.blocks {
        total = total
            .checked_add(b.instructions.len())
            .filter(|n| *n <= MAX_INSTRUCTIONS)
            .ok_or(ReadOnlySourceError::Budget(
                "scalar edge retained instructions",
            ))?;
        if b.instructions.is_empty()
            || b.params.len() > 8
            || b.instructions
                .iter()
                .any(|n| n.args.len() > 8 || n.results.len() > 8)
        {
            return Err(refuse("scalar edge retained arity"));
        }
        if lir
            .trust_ir_origins
            .get(id)
            .is_none_or(|v| v.len() != b.instructions.len())
        {
            return Err(refuse("missing scalar edge origin inventory"));
        }
        for (i, n) in b.instructions.iter().enumerate() {
            if !matches!(
                n.opcode,
                Opcode::Iconst { .. }
                    | Opcode::Copy
                    | Opcode::Icmp { .. }
                    | Opcode::Select { .. }
                    | Opcode::Load { .. }
                    | Opcode::Store { .. }
                    | Opcode::ArrayGep { .. }
                    | Opcode::StructGep { .. }
                    | Opcode::Call { .. }
                    | Opcode::Iadd
                    | Opcode::Isub
                    | Opcode::Imul
                    | Opcode::Band
                    | Opcode::Bor
                    | Opcode::Bxor
                    | Opcode::Ishl
                    | Opcode::Ushr
                    | Opcode::Sshr
                    | Opcode::Jump { .. }
                    | Opcode::Brif { .. }
                    | Opcode::Return
            ) {
                return Err(refuse("uninspected retained scalar edge operand inventory"));
            }
            let terminal = matches!(
                n.opcode,
                Opcode::Jump { .. } | Opcode::Brif { .. } | Opcode::Return
            );
            if terminal != (i + 1 == b.instructions.len()) {
                return Err(refuse("scalar edge retained terminator position"));
            }
        }
        for to in target_successors(b.instructions.last().unwrap())? {
            target_cfg.push((id.0, to.0));
            *incoming.entry(to.0).or_default() += 1;
        }
    }
    let target_ids: Vec<_> = lir.blocks.keys().map(|b| b.0).collect();
    let target_dom = dominators(&target_ids, lir.entry_block.0, &target_cfg)?;
    let mut block_map = HashMap::new();
    let mut main_blocks = HashSet::new();
    let mut scalar_values: HashMap<ValueId, (LirValue, ScalarEdgeCodec)> = HashMap::new();
    let mut source_definitions = HashMap::new();
    let mut origin_start = 0u32;
    for sb in &source_blocks {
        let candidates: Vec<_> = lir
            .blocks
            .iter()
            .filter(|(id, b)| {
                let Some(last) = b.instructions.last() else {
                    return false;
                };
                let Some(Some(origin)) = lir.trust_ir_origins.get(id).and_then(|o| o.last()) else {
                    return false;
                };
                if origin.0 != sb.terminal {
                    return false;
                }
                matches!(
                    (&sb.block.body.last().unwrap().inst, &last.opcode),
                    (Inst::Br { .. }, Opcode::Jump { .. })
                        | (Inst::CondBr { .. }, Opcode::Brif { .. })
                        | (Inst::Return { .. }, Opcode::Return)
                )
            })
            .map(|(id, _)| *id)
            .collect();
        let [target] = candidates.as_slice() else {
            return Err(refuse("ambiguous or missing original scalar edge block"));
        };
        if !main_blocks.insert(target.0)
            || sb.block.id == source.entry && *target != lir.entry_block
        {
            return Err(refuse("foreign scalar edge entry/block binding"));
        }
        let b = &lir.blocks[target];
        if b.params.len() != sb.block.params.len() {
            return Err(refuse("scalar edge parameter arity differs"));
        }
        for ((src, ty), (dst, actual)) in sb.block.params.iter().zip(&b.params) {
            let codec =
                ScalarEdgeCodec::source(ty).ok_or(refuse("aggregate/non-scalar edge parameter"))?;
            if lir.value_types.get(dst).is_some_and(|hint| hint != actual)
                || codec.carrier() != *actual
            {
                return Err(refuse("scalar edge parameter codec differs"));
            }
            scalar_values.insert(*src, (*dst, codec));
            source_definitions.insert(*src, (sb.block.id.index(), None));
        }
        let origins = &lir.trust_ir_origins[target];
        if origins
            .iter()
            .any(|o| o.is_none_or(|o| o.0 < origin_start || o.0 > sb.terminal))
            || origins
                .windows(2)
                .any(|w| w[0].unwrap().0 > w[1].unwrap().0)
        {
            return Err(refuse("foreign or reordered scalar edge origins"));
        }
        for (i, node) in sb.block.body.iter().enumerate() {
            for result in &node.results {
                source_definitions.insert(*result, (sb.block.id.index(), Some(i)));
            }
            let origin = origin_start + i as u32;
            let group: Vec<_> = b
                .instructions
                .iter()
                .zip(origins)
                .filter(|(_, o)| o.is_some_and(|o| o.0 == origin))
                .map(|(n, _)| n)
                .collect();
            let codecs = result_codecs(module, node);
            if let Some(values) = result_carriers(module, node, &group) {
                if codecs.len() != values.len() {
                    return Err(refuse("scalar edge source result arity differs"));
                }
                for ((src, dst), codec) in node.results.iter().zip(values).zip(codecs) {
                    if let Some(codec) = codec {
                        scalar_values.insert(*src, (dst, codec));
                    }
                }
            }
        }
        origin_start = sb.terminal + 1;
        block_map.insert(sb.block.id, *target);
    }
    let source_entry = source
        .blocks
        .iter()
        .find(|b| b.id == source.entry)
        .ok_or(refuse("missing scalar edge source entry"))?;
    if source_entry.params.len() != signature.params.len()
        || source_entry
            .params
            .iter()
            .zip(&signature.params)
            .any(|((_, actual), expected)| actual != expected)
        || lir.blocks[&lir.entry_block]
            .params
            .iter()
            .map(|(_, ty)| ty)
            .ne(lir.signature.params.iter())
    {
        return Err(refuse("scalar edge entry signature mismatch"));
    }
    for sb in &source_blocks {
        if let Inst::CondBr { cond, .. } = &sb.block.body.last().unwrap().inst {
            let (value, codec) = scalar_values
                .get(cond)
                .ok_or(refuse("unbound original scalar edge condition carrier"))?;
            if *codec != ScalarEdgeCodec::Boolean
                || !matches!(lir.blocks[&block_map[&sb.block.id]].instructions.last().unwrap().opcode,Opcode::Brif{cond,..} if cond==*value)
            {
                return Err(refuse("wrong original scalar edge condition"));
            }
        }
    }
    let mut result = CheckedScalarBlockArguments {
        module,
        ordinal,
        lir,
        transports: vec![],
        omitted: HashSet::new(),
        jump_arguments: HashMap::new(),
    };
    let mut owned_copy_blocks = HashSet::new();
    for edge in &edges {
        let from = block_map[&edge.block];
        let to = block_map[&edge.target];
        let source_block = source_blocks
            .iter()
            .find(|b| b.block.id == edge.block)
            .unwrap();
        let source_target = source.blocks.iter().find(|b| b.id == edge.target).unwrap();
        let terminal = lir.blocks[&from].instructions.last().unwrap();
        let next = target_successors(terminal)?
            .get(edge.ordinal)
            .copied()
            .ok_or(refuse("wrong scalar edge ordinal"))?;
        let (copy_block, first) = if matches!(
            source_block.block.body.last().unwrap().inst,
            Inst::Br { .. }
        ) {
            if next != to {
                return Err(refuse("wrong unconditional scalar edge target"));
            }
            let origins = &lir.trust_ir_origins[&from];
            let start = origins
                .iter()
                .position(|o| o.is_some_and(|o| o.0 == source_block.terminal))
                .ok_or(refuse("missing scalar edge instruction origin"))?;
            (from, start)
        } else if next == to {
            if !edge.args.is_empty() {
                return Err(refuse("missing conditional scalar edge copy block"));
            }
            (from, lir.blocks[&from].instructions.len() - 1)
        } else {
            if main_blocks.contains(&next.0)
                || incoming.get(&next.0) != Some(&1)
                || !owned_copy_blocks.insert(next.0)
            {
                return Err(refuse("shared/foreign conditional scalar edge block"));
            }
            let b = lir
                .blocks
                .get(&next)
                .ok_or(refuse("missing scalar edge copy block"))?;
            if !b.params.is_empty()
                || !matches!(b.instructions.last().unwrap().opcode,Opcode::Jump{dest} if dest==to)
                || lir.trust_ir_origins[&next].iter().any(Option::is_some)
            {
                return Err(refuse("foreign conditional copy block binding"));
            }
            (next, 0)
        };
        let mut args = Vec::new();
        let mut codecs = Vec::new();
        for (arg, (_, ty)) in edge.args.iter().zip(&source_target.params) {
            let (value, codec) = scalar_values
                .get(arg)
                .copied()
                .ok_or(refuse("unbound scalar edge source argument carrier"))?;
            if lir
                .value_types
                .get(&value)
                .is_some_and(|actual| *actual != codec.carrier())
                || ScalarEdgeCodec::source(ty) != Some(codec)
            {
                return Err(refuse("wrong original scalar edge argument codec"));
            }
            let (owner, position) = source_definitions
                .get(arg)
                .ok_or(refuse("undefined scalar edge source argument"))?;
            if !source_dom[&edge.block.index()].contains(owner)
                || *owner == edge.block.index() && position.is_some_and(|p| p >= edge.instruction)
            {
                return Err(refuse("nondominating original scalar edge argument"));
            }
            args.push(value);
            codecs.push(codec);
        }
        let destinations: Vec<_> = lir.blocks[&to].params.iter().map(|(v, _)| *v).collect();
        if args.iter().any(|v| destinations.contains(v)) {
            return Err(refuse("cyclic/self scalar edge transport unsupported"));
        }
        let pairs: Vec<_> = args
            .iter()
            .copied()
            .zip(destinations.iter().copied())
            .collect();
        let expected =
            trust_cg_lower::block_arguments::schedule_parallel_copies(pairs, || LirValue(u32::MAX));
        let b = &lir.blocks[&copy_block];
        let end = b.instructions.len() - 1;
        if first > end || b.instructions[first..end] != expected {
            return Err(refuse("missing/wrong/reordered scalar edge copies"));
        }
        // Independent symbolic replay: every destination must receive its
        // original incoming symbol and no unrelated value may be overwritten.
        let mut state: HashMap<LirValue, LirValue> = args.iter().copied().map(|v| (v, v)).collect();
        for (offset, copy) in b.instructions[first..end].iter().enumerate() {
            if !matches!(copy.opcode, Opcode::Copy)
                || copy.args.len() != 1
                || copy.results.len() != 1
                || !destinations.contains(&copy.results[0])
            {
                return Err(refuse("invalid scalar edge copy operation"));
            }
            let value = *state
                .get(&copy.args[0])
                .ok_or(refuse("undefined or clobbered scalar edge copy source"))?;
            state.insert(copy.results[0], value);
            if !result.omitted.insert((copy_block.0, first + offset)) {
                return Err(refuse("reused scalar edge copy occurrence"));
            }
        }
        for (input, dest) in args.iter().zip(&destinations) {
            if state.get(dest) != Some(input) {
                return Err(refuse("scalar edge parallel-copy relation differs"));
            }
        }
        if !args.is_empty() {
            result
                .jump_arguments
                .insert(copy_block.0, args.iter().map(|v| v.0).collect());
        }
        result.transports.push(ScalarEdgeTransport {
            source_block: edge.block.index(),
            source_instruction: edge.instruction,
            source_edge: edge.ordinal,
            source_target: edge.target.index(),
            lowering_block: copy_block.0,
            lowering_target: to.0,
            copy_instructions: (first..end).collect(),
            source_arguments: edge.args.iter().map(|v| v.index()).collect(),
            lowering_arguments: args.iter().map(|v| v.0).collect(),
            parameter_codecs: codecs,
        });
    }
    if main_blocks.len() + owned_copy_blocks.len() != lir.blocks.len() {
        return Err(refuse("unowned scalar edge retained block"));
    }
    validate_retained_definitions(&result, &target_dom)?;
    let scalar_kinds = retained_scalar_codecs(&result)?;
    for edge in &result.transports {
        for (value, codec) in edge.lowering_arguments.iter().zip(&edge.parameter_codecs) {
            let expected = match codec.carrier() {
                Type::I64 => Kind::Word,
                Type::I32 => Kind::Word32,
                Type::B1 => Kind::Boolean,
                _ => unreachable!(),
            };
            if scalar_kinds.get(value) != Some(&Some(expected)) {
                return Err(refuse(
                    "scalar edge argument differs from real producing codec",
                ));
            }
        }
    }
    Ok(result)
}

fn validate_retained_definitions(
    projection: &CheckedScalarBlockArguments<'_>,
    dom: &HashMap<u32, HashSet<u32>>,
) -> Result<()> {
    let mut definitions = HashMap::new();
    for (id, b) in &projection.lir.blocks {
        for (value, _) in &b.params {
            if definitions.insert(value.0, (id.0, None)).is_some() {
                return Err(refuse("duplicate projected scalar LIR definition"));
            }
        }
        for (i, node) in b.instructions.iter().enumerate() {
            if !projection.omitted(id.0, i) {
                for value in &node.results {
                    if definitions.insert(value.0, (id.0, Some(i))).is_some() {
                        return Err(refuse("unclaimed duplicate scalar LIR definition"));
                    }
                }
            }
        }
    }
    if definitions.len() > MAX_VALUES {
        return Err(ReadOnlySourceError::Budget("projected scalar edge values"));
    }
    let check = |value: u32, block: u32, instruction: usize| -> Result<()> {
        let (owner, position) = definitions
            .get(&value)
            .ok_or(refuse("undefined projected scalar LIR operand"))?;
        if !dom[&block].contains(owner)
            || *owner == block && position.is_some_and(|p| p >= instruction)
        {
            return Err(refuse("nondominating projected scalar LIR operand"));
        }
        Ok(())
    };
    for (id, b) in &projection.lir.blocks {
        for (i, node) in b.instructions.iter().enumerate() {
            if projection.omitted(id.0, i) {
                continue;
            }
            for arg in &node.args {
                check(arg.0, id.0, i)?;
            }
            if let Some(args) = projection.jump_arguments(id.0)
                && i + 1 == b.instructions.len()
            {
                for arg in args {
                    check(*arg, id.0, i)?;
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
#[path = "scalar_edge_projection_tests.rs"]
mod tests;

// This census checks retained scalar carriers only. An aggregate call result
// remains None/unmodelled; no native result-register, layout or ABI theorem is
// inferred from that declaration. Hints may not retype real scalar operations.
fn retained_scalar_codecs(
    projection: &CheckedScalarBlockArguments<'_>,
) -> Result<HashMap<u32, Option<Kind>>> {
    let scalar = |ty: &Type| match ty {
        Type::I64 => Some(Kind::Word),
        Type::I32 => Some(Kind::Word32),
        Type::B1 => Some(Kind::Boolean),
        _ => None,
    };
    let mut kinds = HashMap::new();
    let mut pending = Vec::new();
    for (id, b) in &projection.lir.blocks {
        for (value, ty) in &b.params {
            kinds.insert(value.0, scalar(ty));
        }
        for (i, n) in b.instructions.iter().enumerate() {
            if projection.omitted(id.0, i) || n.results.is_empty() {
                continue;
            }
            let fixed = match &n.opcode {
                Opcode::Iconst { ty, .. } | Opcode::Load { ty, .. } => Some(scalar(ty)),
                Opcode::Icmp { .. } => Some(Some(Kind::Boolean)),
                Opcode::ArrayGep { .. } | Opcode::StructGep { .. } => Some(Some(Kind::Word)),
                Opcode::Call { .. } => {
                    for value in &n.results {
                        kinds.insert(
                            value.0,
                            projection
                                .lir
                                .value_types
                                .get(value)
                                .map_or(Some(Kind::Word), scalar),
                        );
                    }
                    continue;
                }
                Opcode::Copy
                | Opcode::Select { .. }
                | Opcode::Iadd
                | Opcode::Isub
                | Opcode::Imul
                | Opcode::Band
                | Opcode::Bor
                | Opcode::Bxor
                | Opcode::Ishl
                | Opcode::Ushr
                | Opcode::Sshr => None,
                _ => return Err(refuse("unsupported retained scalar edge result codec")),
            };
            if n.results.len() != 1 {
                return Err(refuse("scalar edge operation result arity"));
            }
            if let Some(kind) = fixed {
                kinds.insert(n.results[0].0, kind);
            } else {
                pending.push(n);
            }
        }
    }
    while !pending.is_empty() {
        let before = pending.len();
        let mut next = Vec::new();
        for n in pending {
            if n.args.iter().any(|v| !kinds.contains_key(&v.0)) {
                next.push(n);
                continue;
            }
            let kind = match n.opcode {
                Opcode::Copy if n.args.len() == 1 => kinds[&n.args[0].0],
                Opcode::Select { .. } if n.args.len() == 3 => {
                    if kinds[&n.args[0].0] != Some(Kind::Boolean)
                        || kinds[&n.args[1].0] != kinds[&n.args[2].0]
                    {
                        return Err(refuse("retained scalar edge select codec mismatch"));
                    }
                    kinds[&n.args[1].0]
                }
                _ if n.args.len() == 2 => {
                    let left = kinds[&n.args[0].0];
                    let right = kinds[&n.args[1].0];
                    if left.is_none()
                        || left != right
                        || left == Some(Kind::Boolean)
                            && !matches!(n.opcode, Opcode::Band | Opcode::Bor | Opcode::Bxor)
                    {
                        return Err(refuse("retained scalar edge arithmetic codec mismatch"));
                    }
                    left
                }
                _ => return Err(refuse("retained scalar edge inference arity")),
            };
            kinds.insert(n.results[0].0, kind);
        }
        if before == next.len() {
            return Err(refuse("undefined/cyclic retained scalar edge codec"));
        }
        pending = next;
    }
    for (value, hint) in &projection.lir.value_types {
        if kinds.get(&value.0) != Some(&scalar(hint)) {
            return Err(refuse("retained scalar edge hint disagrees with producer"));
        }
    }
    Ok(kinds)
}
