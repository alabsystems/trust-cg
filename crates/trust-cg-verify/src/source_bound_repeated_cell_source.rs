// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Bind a bounded F32 caller's original TrustIR and LIR to the same ordered
//! memory/call trace. Unresolved reads retain their preceding world identity;
//! no disjointness, readonly-callee, or last-private-store assumption is made.
//! This comparison grants no machine, ABI, proof, or promotion authority.
//!
//! The bounded domain has one F32 cell, an F32 result, an F32 parameter
//! prefix and one public F32 output pointer. Opaque C callbacks take the cell
//! pointer and either F32 bits or a U32 tag. Every store and every call advances
//! the memory world. A read names that world, including intervening public
//! stores: the output pointer is never assumed disjoint from the cell here.
//! The paired-callee entry additionally admits an exact module-local callback
//! whose complete original AND retained lowered bodies store its F32 argument
//! through its pointer argument and return. That checked effect supplies later
//! caller cell loads, until any possibly aliasing write or opaque call. A name
//! or FuncId without both bodies never supplies that effect. Native callee
//! correctness, ABI and actual private-frame separation remain unproved.
//! The ordinary compiler must still admit the complete module. The original
//! endpoints, including transient LIR origins, stay borrowed and unchanged.
//! Allocation must precede every memory observation or effect; its placement
//! is otherwise omitted from this trace and carries no allocation theorem.
use std::collections::{HashMap, HashSet};
use trust_cg_lower::instructions::{DirectCallBinding, Opcode as L, Value as LV};
use trust_cg_lower::{Function, Type};
use trust_ir::{CallingConv, CastOp, Constant, Inst, Linkage, Module, Ty, ValueId};

#[derive(Debug, Clone, PartialEq, Eq)]
/// A refused input fragment or a difference between its two traces.
pub enum Error {
    /// The original fragment is outside the interpreted domain.
    Source(&'static str),
    /// The lowered fragment is outside the interpreted domain.
    Lowering(&'static str),
    /// The independently read original and lowered traces differ.
    Mismatch,
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Source(why) => write!(f, "unsupported repeated-cell original TrustIR: {why}"),
            Self::Lowering(why) => write!(f, "unsupported repeated-cell LIR: {why}"),
            Self::Mismatch => {
                f.write_str("original and lowered cell memory/call observations differ")
            }
        }
    }
}
impl std::error::Error for Error {}
type Result<T> = std::result::Result<T, Error>;
#[derive(Debug, Clone, PartialEq, Eq)]
/// A symbolic address root; distinct roots are not a disjointness theorem.
pub enum Base {
    /// The function's one stack cell.
    Cell,
    /// The original signature position of the public pointer parameter.
    Parameter(usize),
}
#[derive(Debug, Clone, PartialEq, Eq)]
/// A 64-bit address expression, with addition wrapping at pointer width.
pub struct Address {
    /// Symbolic address root.
    pub base: Base,
    /// Constant byte offset modulo 2^64.
    pub offset: u64,
}
#[derive(Debug, Clone, PartialEq, Eq)]
/// F32 bits, without floating-point arithmetic or NaN canonicalization.
pub enum Bits {
    /// A scalar parameter's original signature position.
    Parameter(usize),
    /// A read after exactly `world` preceding trace events. The complete
    /// memory world is retained, including opaque calls and public stores.
    Read { world: usize, address: Address },
}
#[derive(Debug, Clone, PartialEq, Eq)]
/// The second logical argument of an ordinary opaque C callback.
pub enum Argument {
    /// F32 argument bits.
    Float(Bits),
    /// U32 argument bits.
    Tag(u32),
}
#[derive(Debug, Clone, PartialEq, Eq)]
/// One ordered effect on the entire memory world.
pub enum Event {
    /// A private-cell or public-output write, retaining its original alignment.
    Store {
        address: Address,
        value: Bits,
        align: Option<u64>,
    },
    /// Opaque over the complete memory world, including the cell and public
    /// output. A symbol named `record` has no special memory permission.
    Call { symbol: String, argument: Argument },
    /// A logical call to the exact module definition whose complete original
    /// body is one F32 store through parameter zero followed by return. This
    /// describes ORIGINAL source effects, not the native callee's behavior.
    /// The logical memory update is the checked store; subsequent cell loads
    /// consume its value until another possibly aliasing effect intervenes.
    DefinedStoreCall {
        function: u32,
        symbol: String,
        argument: Bits,
        align: Option<u64>,
    },
}
#[derive(Debug, Clone, PartialEq, Eq)]
/// A comparison trace. Constructing or inspecting one is not proof credit.
pub struct Contract {
    /// Number of leading F32 parameters before the public output pointer.
    pub float_parameters: usize,
    /// Complete ordered stores, opaque calls and paired defined-store calls.
    pub events: Vec<Event>,
    /// The returned F32 bits and their memory-world dependency.
    pub returned: Bits,
}
/// Immutable endpoints whose independently interpreted traces agree.
pub struct Checked<'a> {
    module: &'a Module,
    original: &'a trust_ir::Function,
    lir: &'a Function,
    callees: &'a [Function],
    contract: Contract,
}
impl<'a> Checked<'a> {
    /// Original complete module; this object does not grant module admission.
    pub fn module(&self) -> &'a Module {
        self.module
    }
    /// Original caller within that module.
    pub fn original(&self) -> &'a trust_ir::Function {
        self.original
    }
    /// Exact borrowed lowered endpoint, including its provenance metadata.
    pub fn lir(&self) -> &'a Function {
        self.lir
    }
    /// Exact independently checked callee lowering endpoints. Empty on the
    /// original opaque-callback route. These are not installed native bodies.
    pub fn callees(&self) -> &'a [Function] {
        self.callees
    }
    /// The matching ordered memory/call trace; it grants no execution authority.
    pub fn contract(&self) -> &Contract {
        &self.contract
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
enum Data {
    Float(Bits),
    Address(Address),
    Integer { width: u8, bits: u64 },
}
impl Data {
    fn float(&self) -> Option<Bits> {
        if let Self::Float(b) = self {
            Some(b.clone())
        } else {
            None
        }
    }
    fn address(&self) -> Option<Address> {
        if let Self::Address(p) = self {
            Some(p.clone())
        } else {
            None
        }
    }
    fn tag(&self) -> Option<u32> {
        if let Self::Integer { width: 32, bits } = self {
            Some(*bits as u32)
        } else {
            None
        }
    }
    fn ty(&self) -> Type {
        match self {
            Self::Float(_) => Type::F32,
            Self::Address(_) => Type::I64,
            Self::Integer { width: 32, .. } => Type::I32,
            Self::Integer { .. } => Type::I64,
        }
    }
}
fn cell() -> Address {
    Address {
        base: Base::Cell,
        offset: 0,
    }
}
fn pointer_ty(t: &Ty) -> bool {
    matches!(t, Ty::Ptr) || *t == Ty::PtrMut(Box::new(Ty::F32))
}
fn align_ok(a: Option<u64>) -> bool {
    a.is_none_or(|n| n.is_power_of_two() && n <= 4)
}
fn arithmetic(add: bool, a: &Data, b: &Data) -> Option<Data> {
    match (a, b) {
        (Data::Integer { width: 64, bits: x }, Data::Integer { width: 64, bits: y }) => {
            Some(Data::Integer {
                width: 64,
                bits: if add {
                    x.wrapping_add(*y)
                } else {
                    x.wrapping_mul(*y)
                },
            })
        }
        (Data::Address(p), Data::Integer { width: 64, bits: k })
        | (Data::Integer { width: 64, bits: k }, Data::Address(p))
            if add =>
        {
            Some(Data::Address(Address {
                base: p.base.clone(),
                offset: p.offset.wrapping_add(*k),
            }))
        }
        _ => None,
    }
}

/// Byte GEPs preserve the address root. This comparison projects numeric
/// addresses only; it does not discharge GEP definedness or object validity.
fn byte_gep(base: &Data, index: &Data) -> Option<Data> {
    let (Data::Address(address), Data::Integer { width: 64, bits }) = (base, index) else {
        return None;
    };
    if *bits > i64::MAX as u64 {
        return None;
    }
    Some(Data::Address(Address {
        base: address.base.clone(),
        offset: address.offset.checked_add(*bits)?,
    }))
}

fn ordinary(f: &trust_ir::Function, arity: usize) -> bool {
    f.calling_conv == CallingConv::C
        && f.linkage == Linkage::External
        && f.attrs.is_empty()
        && f.attrs.params.len() <= arity
        && f.proofs.is_empty()
        && f.summary.is_none()
        && f.body_gate.is_none()
        && f.source_provenance.is_none()
}
struct Callee {
    argument: Ty,
    binding: DirectCallBinding,
    /// None is opaque; Some(alignment) requires BOTH complete store bodies.
    store_alignment: Option<Option<u64>>,
}

fn defined_store(module: &Module, f: &trust_ir::Function) -> Option<Option<u64>> {
    if !f.linkage.is_module_local()
        || f.calling_conv != CallingConv::C
        || f.attrs.params.len() > 2
        || !f.attrs.is_empty()
        || !f.proofs.is_empty()
        || f.summary.is_some()
        || f.body_gate.is_some()
        || f.source_provenance.is_some()
        || f.blocks.len() != 1
    {
        return None;
    }
    let t = module.func_types.get(f.ty.index() as usize)?;
    let b = &f.blocks[0];
    if t.is_vararg
        || t.abi.is_some()
        || !t.returns.is_empty()
        || t.params != [Ty::PtrMut(Box::new(Ty::F32)), Ty::F32]
        || b.id != f.entry
        || b.params.len() != 2
        || b.body.len() != 2
        || b.params[0].1 != t.params[0]
        || b.params[1].1 != Ty::F32
        || b.params[0].0 == b.params[1].0
        || b.body
            .iter()
            .any(|n| !n.results.is_empty() || !n.proofs.is_empty() || n.proof_context.is_some())
    {
        return None;
    }
    match (&b.body[0].inst, &b.body[1].inst) {
        (
            Inst::Store {
                ty: Ty::F32,
                ptr,
                value,
                volatile: false,
                align,
            },
            Inst::Return { values },
        ) if *ptr == b.params[0].0
            && *value == b.params[1].0
            && values.is_empty()
            && align_ok(*align) =>
        {
            Some(*align)
        }
        _ => None,
    }
}

fn lowered_store(f: &Function, alignment: Option<u64>) -> bool {
    use trust_cg_ir::function::StackProtectorMode;
    if f.signature.params != [Type::I64, Type::F32]
        || !f.signature.returns.is_empty()
        || !f.stack_slots.is_empty()
        || f.stack_protector != StackProtectorMode::None
        || f.stack_limit.is_some()
        || !f.eh_info.is_empty()
        || !f.eh_type_table.is_empty()
        || !f.target_features.is_empty()
        || !f.param_pointee_types.is_empty()
        || f.abi_sret_param.is_some()
        || !f.sret_arg_callees.is_empty()
        || !f.sret_arg_indirect_callees.is_empty()
        || !f.pure_callees.is_empty()
        || !f.libm_pure_callees.is_empty()
        || f.blocks.len() != 1
        || (!f.block_order.is_empty() && f.block_order != [f.entry_block])
        || f.value_types
            .iter()
            .any(|(v, t)| !matches!((v.0, t), (0, Type::I64) | (1, Type::F32)))
        || f.trust_ir_origins
            .iter()
            .any(|(id, origins)| *id != f.entry_block || origins.len() != 2)
    {
        return false;
    }
    let Some(b) = f.blocks.get(&f.entry_block) else {
        return false;
    };
    if b.params != [(LV(0), Type::I64), (LV(1), Type::F32)] || b.instructions.len() != 2 {
        return false;
    }
    let store = &b.instructions[0];
    let ret = &b.instructions[1];
    matches!(store.opcode, L::Store { ty: Type::F32, align } if align.map(u64::from) == alignment)
        && store.args == [LV(1), LV(0)]
        && store.results.is_empty()
        && ret.opcode == L::Return
        && ret.args.is_empty()
        && ret.results.is_empty()
}

fn signatures(module: &Module, lowered_callees: &[Function]) -> Result<HashMap<String, Callee>> {
    if lowered_callees.len() > 16 {
        return Err(Error::Lowering("callee count limit"));
    }
    let mut lowered_names = HashSet::new();
    if lowered_callees
        .iter()
        .any(|f| !lowered_names.insert(&f.name))
    {
        return Err(Error::Lowering("duplicate callee identity"));
    }
    let mut names = HashSet::new();
    let mut ids = HashSet::new();
    let mut callees = HashMap::new();
    for f in &module.functions {
        if f.name.is_empty()
            || f.name.as_bytes().contains(&0)
            || !names.insert(&f.name)
            || !ids.insert(f.id)
        {
            return Err(Error::Source("ambiguous function identity"));
        }
        if !f.blocks.is_empty() {
            if let Some(align) = defined_store(module, f) {
                let Some(lowered) = lowered_callees
                    .iter()
                    .find(|lowered| lowered.name == f.name)
                else {
                    // An exact FuncId alone never establishes callee lowering.
                    continue;
                };
                if !lowered_store(lowered, align) {
                    return Err(Error::Lowering(
                        "defined callee body differs from original store",
                    ));
                }
                callees.insert(
                    f.name.clone(),
                    Callee {
                        argument: Ty::F32,
                        binding: DirectCallBinding::ExactModuleFunction {
                            function: f.id.index(),
                        },
                        store_alignment: Some(align),
                    },
                );
            }
            continue;
        }
        let t = module
            .func_types
            .get(f.ty.index() as usize)
            .ok_or(Error::Source("missing declaration type"))?;
        if !ordinary(f, 2)
            || t.is_vararg
            || t.abi.is_some()
            || !t.returns.is_empty()
            || t.params.len() != 2
            || t.params[0] != Ty::PtrMut(Box::new(Ty::F32))
            || !matches!(t.params[1], Ty::F32 | Ty::U32)
        {
            return Err(Error::Source("unsupported opaque declaration"));
        }
        callees.insert(
            f.name.clone(),
            Callee {
                argument: t.params[1].clone(),
                binding: DirectCallBinding::Interposable,
                store_alignment: None,
            },
        );
    }
    if lowered_callees.iter().any(|f| {
        callees
            .get(&f.name)
            .is_none_or(|c| c.store_alignment.is_none())
    }) {
        return Err(Error::Lowering("unbound retained callee"));
    }
    Ok(callees)
}
struct Trace {
    events: Vec<Event>,
    allocated: bool,
    initialized: bool,
    defined_cell: Option<Bits>,
}
impl Trace {
    fn new() -> Self {
        Self {
            events: Vec::new(),
            allocated: false,
            initialized: false,
            defined_cell: None,
        }
    }
    fn load(&self, p: Address) -> Option<Data> {
        if !self.allocated || (p.base == Base::Cell && (p.offset != 0 || !self.initialized)) {
            return None;
        }
        if p == cell()
            && let Some(value) = &self.defined_cell
        {
            return Some(Data::Float(value.clone()));
        }
        Some(Data::Float(Bits::Read {
            world: self.events.len(),
            address: p,
        }))
    }
    fn store(&mut self, p: Address, v: Bits, align: Option<u64>) -> Option<()> {
        if !self.allocated || !align_ok(align) || (p.base == Base::Cell && p.offset != 0) {
            return None;
        }
        if p.base == Base::Cell {
            self.initialized = true;
        }
        // A public-pointer store may alias the cell. Never carry a known
        // defined-call result through an intervening write, even at another
        // symbolic root.
        self.defined_cell = None;
        self.events.push(Event::Store {
            address: p,
            value: v,
            align,
        });
        Some(())
    }
    fn call(&mut self, name: String, p: Address, arg: Argument, callee: &Callee) -> Option<()> {
        if p != cell() || !self.initialized {
            return None;
        }
        self.defined_cell = None;
        self.events.push(match (callee.store_alignment, arg) {
            (Some(align), Argument::Float(argument)) => {
                self.defined_cell = Some(argument.clone());
                Event::DefinedStoreCall {
                    function: match callee.binding {
                        DirectCallBinding::ExactModuleFunction { function } => function,
                        _ => return None,
                    },
                    symbol: name,
                    argument,
                    align,
                }
            }
            (None, argument) => Event::Call {
                symbol: name,
                argument,
            },
            _ => return None,
        });
        Some(())
    }
    fn finish(self, n: usize, b: Bits) -> Option<Contract> {
        if !self.allocated
            || !self
                .events
                .iter()
                .any(|e| matches!(e, Event::Call { .. } | Event::DefinedStoreCall { .. }))
            || !self.events.iter().any(|e| {
                matches!(
                    e,
                    Event::Store {
                        address: Address {
                            base: Base::Parameter(_),
                            ..
                        },
                        ..
                    }
                )
            })
        {
            return None;
        }
        Some(Contract {
            float_parameters: n,
            events: self.events,
            returned: b,
        })
    }
}
fn const_int(t: &Ty, v: i128) -> Option<Data> {
    let (width, bits) = match t {
        Ty::U32 => (32, u32::try_from(v).ok()? as u64),
        Ty::I32 => (32, i32::try_from(v).ok()? as u32 as u64),
        Ty::U64 => (64, u64::try_from(v).ok()?),
        Ty::I64 => (64, i64::try_from(v).ok()? as u64),
        _ => return None,
    };
    Some(Data::Integer { width, bits })
}
#[derive(Clone)]
struct SourceValue {
    ty: Ty,
    data: Data,
}
fn source(
    module: &Module,
    f: &trust_ir::Function,
    decls: &HashMap<String, Callee>,
) -> Result<Contract> {
    let bad = |s| Error::Source(s);
    let t = module
        .func_types
        .get(f.ty.index() as usize)
        .ok_or(bad("missing caller type"))?;
    let n = t
        .params
        .len()
        .checked_sub(1)
        .ok_or(bad("missing parameters"))?;
    if !(1..=8).contains(&n)
        || !ordinary(f, n + 1)
        || t.is_vararg
        || t.abi.is_some()
        || t.returns != [Ty::F32]
        || t.params[n] != Ty::PtrMut(Box::new(Ty::F32))
        || t.params[..n].iter().any(|t| *t != Ty::F32)
    {
        return Err(bad(
            "requires F32 parameters and one mutable F32 output pointer",
        ));
    }
    if f.blocks.is_empty() || f.blocks.len() > 16 {
        return Err(bad("block limit"));
    }
    let blocks: HashMap<_, _> = f.blocks.iter().map(|b| (b.id, b)).collect();
    if blocks.len() != f.blocks.len() {
        return Err(bad("duplicate block"));
    }
    let entry = blocks.get(&f.entry).ok_or(bad("missing entry"))?;
    if entry.params.len() != n + 1 {
        return Err(bad("entry arity"));
    }
    let mut values: HashMap<ValueId, SourceValue> = HashMap::new();
    for (i, (id, ty)) in entry.params.iter().enumerate() {
        if *ty != t.params[i]
            || values
                .insert(
                    *id,
                    SourceValue {
                        ty: ty.clone(),
                        data: if i == n {
                            Data::Address(Address {
                                base: Base::Parameter(i),
                                offset: 0,
                            })
                        } else {
                            Data::Float(Bits::Parameter(i))
                        },
                    },
                )
                .is_some()
        {
            return Err(bad("entry type or identity"));
        }
    }
    let mut trace = Trace::new();
    let mut visited = HashSet::new();
    let mut next = f.entry;
    let mut total = 0;
    loop {
        if !visited.insert(next) {
            return Err(bad("loop"));
        }
        let b = blocks.get(&next).ok_or(bad("missing branch target"))?;
        if b.body.is_empty() || (next != f.entry && !b.params.is_empty()) {
            return Err(bad("empty block or block arguments"));
        }
        total += b.body.len();
        if total > 256 {
            return Err(bad("instruction limit"));
        }
        let mut branch = None;
        for (index, node) in b.body.iter().enumerate() {
            if branch.is_some() || !node.proofs.is_empty() || node.proof_context.is_some() {
                return Err(bad(
                    "unsupported proof metadata or instruction after branch",
                ));
            }
            let read = |id: &ValueId| values.get(id).cloned().ok_or(bad("undefined value"));
            let made = match &node.inst {
                Inst::Alloca {
                    ty: Ty::F32,
                    count: None,
                    align,
                } if !trace.allocated && align.is_none_or(|a| a == 4) => {
                    trace.allocated = true;
                    Some(SourceValue {
                        ty: Ty::Ptr,
                        data: Data::Address(cell()),
                    })
                }
                Inst::Const {
                    ty,
                    value: Constant::Int(k),
                } => Some(SourceValue {
                    ty: ty.clone(),
                    data: const_int(ty, *k).ok_or(bad("integer constant type or range"))?,
                }),
                Inst::Copy { ty, operand } => {
                    let v = read(operand)?;
                    if v.ty != *ty {
                        return Err(bad("copy type"));
                    }
                    Some(v)
                }
                Inst::GEP {
                    pointee_ty: Ty::U8,
                    base,
                    indices,
                    inbounds: true,
                } if indices.len() == 1 => {
                    let base = read(base)?;
                    let index = read(&indices[0])?;
                    if base.ty != Ty::Ptr || index.ty != Ty::I64 {
                        return Err(bad("byte GEP operand types"));
                    }
                    Some(SourceValue {
                        ty: Ty::Ptr,
                        data: byte_gep(&base.data, &index.data)
                            .ok_or(bad("byte GEP address or signed constant index"))?,
                    })
                }
                Inst::Cast {
                    op,
                    src_ty,
                    dst_ty,
                    operand,
                } => {
                    let v = read(operand)?;
                    if v.ty != *src_ty {
                        return Err(bad("cast source type"));
                    }
                    let good = match op {
                        CastOp::PtrToPtr => {
                            pointer_ty(src_ty) && pointer_ty(dst_ty) && v.data.address().is_some()
                        }
                        CastOp::PtrToInt => {
                            pointer_ty(src_ty) && *dst_ty == Ty::I64 && v.data.address().is_some()
                        }
                        CastOp::IntToPtr => {
                            *src_ty == Ty::I64 && pointer_ty(dst_ty) && v.data.address().is_some()
                        }
                        CastOp::Bitcast => matches!(
                            (src_ty, dst_ty),
                            (Ty::U64, Ty::I64)
                                | (Ty::I64, Ty::U64)
                                | (Ty::I32, Ty::U32)
                                | (Ty::U32, Ty::I32)
                        ),
                        _ => false,
                    };
                    if !good {
                        return Err(bad("unsupported cast"));
                    }
                    Some(SourceValue {
                        ty: dst_ty.clone(),
                        data: v.data,
                    })
                }
                Inst::BinOp {
                    op,
                    ty: Ty::I64,
                    lhs,
                    rhs,
                } if matches!(op, trust_ir::BinOp::Add | trust_ir::BinOp::Mul) => {
                    let a = read(lhs)?;
                    let b = read(rhs)?;
                    if a.ty != Ty::I64 || b.ty != Ty::I64 {
                        return Err(bad("integer arithmetic operand type"));
                    }
                    Some(SourceValue {
                        ty: Ty::I64,
                        data: arithmetic(*op == trust_ir::BinOp::Add, &a.data, &b.data)
                            .ok_or(bad("unsupported address arithmetic"))?,
                    })
                }
                Inst::Load {
                    ty: Ty::F32,
                    ptr,
                    volatile: false,
                    align,
                } if align_ok(*align) => {
                    let p = read(ptr)?;
                    if !pointer_ty(&p.ty) {
                        return Err(bad("load pointer type"));
                    }
                    Some(SourceValue {
                        ty: Ty::F32,
                        data: trace
                            .load(p.data.address().ok_or(bad("load pointer"))?)
                            .ok_or(bad("uninitialized or out-of-cell load"))?,
                    })
                }
                Inst::Store {
                    ty: Ty::F32,
                    ptr,
                    value,
                    volatile: false,
                    align,
                } => {
                    let p = read(ptr)?;
                    let v = read(value)?;
                    if !pointer_ty(&p.ty) || v.ty != Ty::F32 {
                        return Err(bad("store type"));
                    }
                    trace
                        .store(
                            p.data.address().ok_or(bad("store pointer"))?,
                            v.data.float().ok_or(bad("store float"))?,
                            *align,
                        )
                        .ok_or(bad("store alignment or cell bounds"))?;
                    None
                }
                Inst::Call { callee, args } if args.len() == 2 => {
                    let d = module
                        .functions
                        .iter()
                        .find(|d| d.id == *callee)
                        .ok_or(bad("unknown callee"))?;
                    let spec = decls.get(&d.name).ok_or(bad(
                        "callee has no checked declaration or paired definition",
                    ))?;
                    let p = read(&args[0])?;
                    let v = read(&args[1])?;
                    let ty = &spec.argument;
                    if p.ty != Ty::PtrMut(Box::new(Ty::F32)) || v.ty != *ty {
                        return Err(bad("call argument types"));
                    }
                    let argument = if *ty == Ty::F32 {
                        Argument::Float(v.data.float().ok_or(bad("call float"))?)
                    } else {
                        Argument::Tag(v.data.tag().ok_or(bad("call tag"))?)
                    };
                    trace
                        .call(
                            d.name.clone(),
                            p.data.address().ok_or(bad("call address"))?,
                            argument,
                            spec,
                        )
                        .ok_or(bad("call cell"))?;
                    None
                }
                Inst::Br { target, args }
                    if args.is_empty() && node.results.is_empty() && index + 1 == b.body.len() =>
                {
                    branch = Some(*target);
                    None
                }
                Inst::Return { values: returned }
                    if returned.len() == 1
                        && node.results.is_empty()
                        && index + 1 == b.body.len()
                        && visited.len() == blocks.len() =>
                {
                    let v = read(&returned[0])?;
                    if v.ty != Ty::F32 {
                        return Err(bad("return type"));
                    }
                    return trace
                        .finish(n, v.data.float().ok_or(bad("return float"))?)
                        .ok_or(bad("requires an opaque call and public output"));
                }
                _ => return Err(bad("instruction outside source domain")),
            };
            match (made, node.results.as_slice()) {
                (Some(v), [id]) if !values.contains_key(id) => {
                    values.insert(*id, v);
                }
                (None, []) => {}
                _ => return Err(bad("result arity or duplicate identity")),
            }
        }
        next = branch.ok_or(bad("missing terminator"))?;
    }
}
fn lowering(f: &Function, n: usize, decls: &HashMap<String, Callee>) -> Result<Contract> {
    use trust_cg_ir::function::{StackProtectorMode, StackSlotAllocationKind};
    let bad = |s| Error::Lowering(s);
    if f.signature.params.len() != n + 1
        || f.signature.params[..n].iter().any(|t| *t != Type::F32)
        || f.signature.params[n] != Type::I64
        || f.signature.returns != [Type::F32]
        || f.stack_slots.len() != 1
        || f.stack_slots[0].size != 4
        || f.stack_slots[0].align != 4
        || f.stack_slots[0].allocation != StackSlotAllocationKind::Fixed
        || f.stack_protector != StackProtectorMode::None
        || f.stack_limit.is_some()
        || !f.eh_info.is_empty()
        || !f.eh_type_table.is_empty()
        || !f.target_features.is_empty()
        || !f.param_pointee_types.is_empty()
        || f.abi_sret_param.is_some()
        || !f.sret_arg_callees.is_empty()
        || !f.sret_arg_indirect_callees.is_empty()
        || !f.pure_callees.is_empty()
        || !f.libm_pure_callees.is_empty()
    {
        return Err(bad("unsupported signature, stack or semantic metadata"));
    }
    // Retain provenance in the borrowed LIR; structural consistency only.
    // It is never the evidence of source agreement or proof credit.
    if f.trust_ir_origins.iter().any(|(id, origins)| {
        f.blocks
            .get(id)
            .is_none_or(|b| origins.len() != b.instructions.len())
    }) {
        return Err(bad("malformed origin map"));
    }
    if f.blocks.is_empty()
        || f.blocks.len() > 16
        || (!f.block_order.is_empty()
            && (f.block_order.len() != f.blocks.len()
                || f.block_order.iter().collect::<HashSet<_>>().len() != f.blocks.len()
                || f.block_order.iter().any(|b| !f.blocks.contains_key(b))))
    {
        return Err(bad("block layout"));
    }
    let entry = f.blocks.get(&f.entry_block).ok_or(bad("missing entry"))?;
    if entry.params.len() != n + 1
        || entry
            .params
            .iter()
            .enumerate()
            .any(|(i, (v, t))| v.0 as usize != i || *t != f.signature.params[i])
    {
        return Err(bad("entry parameter identities"));
    }
    let mut values: HashMap<LV, Data> = (0..=n)
        .map(|i| {
            (
                LV(i as u32),
                if i == n {
                    Data::Address(Address {
                        base: Base::Parameter(i),
                        offset: 0,
                    })
                } else {
                    Data::Float(Bits::Parameter(i))
                },
            )
        })
        .collect();
    let mut trace = Trace::new();
    let mut visited = HashSet::new();
    let mut next = f.entry_block;
    let mut total = 0;
    loop {
        if !visited.insert(next) {
            return Err(bad("loop"));
        }
        let b = f.blocks.get(&next).ok_or(bad("missing jump target"))?;
        if b.instructions.is_empty() || (next != f.entry_block && !b.params.is_empty()) {
            return Err(bad("empty block or block arguments"));
        }
        total += b.instructions.len();
        if total > 256 {
            return Err(bad("instruction limit"));
        }
        let mut branch = None;
        for (index, i) in b.instructions.iter().enumerate() {
            if branch.is_some() {
                return Err(bad("instruction after jump"));
            }
            let read = |v: &LV| values.get(v).cloned().ok_or(bad("undefined value"));
            let made = match &i.opcode {
                L::StackAddr { slot: 0 } if i.args.is_empty() && !trace.allocated => {
                    trace.allocated = true;
                    Some(Data::Address(cell()))
                }
                L::Iconst { ty: Type::I32, imm } if i.args.is_empty() => Some(Data::Integer {
                    width: 32,
                    bits: *imm as u32 as u64,
                }),
                L::Iconst { ty: Type::I64, imm } if i.args.is_empty() => Some(Data::Integer {
                    width: 64,
                    bits: *imm as u64,
                }),
                L::Copy if i.args.len() == 1 => Some(read(&i.args[0])?),
                L::Bitcast { to_ty } if i.args.len() == 1 => {
                    let v = read(&i.args[0])?;
                    if v.ty() != *to_ty {
                        return Err(bad("bitcast width"));
                    }
                    Some(v)
                }
                L::Iadd | L::Imul if i.args.len() == 2 => Some(
                    arithmetic(i.opcode == L::Iadd, &read(&i.args[0])?, &read(&i.args[1])?)
                        .ok_or(bad("address arithmetic"))?,
                ),
                L::ArrayGep { elem_ty: Type::I8 } if i.args.len() == 2 => Some(
                    byte_gep(&read(&i.args[0])?, &read(&i.args[1])?)
                        .ok_or(bad("byte GEP address or signed constant index"))?,
                ),
                L::Load {
                    ty: Type::F32,
                    align,
                } if i.args.len() == 1 && align_ok(align.map(u64::from)) => Some(
                    trace
                        .load(read(&i.args[0])?.address().ok_or(bad("load pointer"))?)
                        .ok_or(bad("uninitialized or out-of-cell load"))?,
                ),
                L::Store {
                    ty: Type::F32,
                    align,
                } if i.args.len() == 2 => {
                    trace
                        .store(
                            read(&i.args[1])?.address().ok_or(bad("store pointer"))?,
                            read(&i.args[0])?.float().ok_or(bad("store value"))?,
                            align.map(u64::from),
                        )
                        .ok_or(bad("store alignment or cell bounds"))?;
                    None
                }
                L::Call { name, binding } if i.args.len() == 2 => {
                    let spec = decls.get(name).ok_or(bad("unknown C symbol"))?;
                    if *binding != spec.binding {
                        return Err(bad("call binding differs from original callee identity"));
                    }
                    let ty = &spec.argument;
                    let v = read(&i.args[1])?;
                    let arg = if *ty == Ty::F32 {
                        Argument::Float(v.float().ok_or(bad("call float"))?)
                    } else {
                        Argument::Tag(v.tag().ok_or(bad("call tag"))?)
                    };
                    trace
                        .call(
                            name.clone(),
                            read(&i.args[0])?.address().ok_or(bad("call pointer"))?,
                            arg,
                            spec,
                        )
                        .ok_or(bad("call cell"))?;
                    None
                }
                L::Jump { dest }
                    if i.args.is_empty()
                        && i.results.is_empty()
                        && index + 1 == b.instructions.len() =>
                {
                    branch = Some(*dest);
                    None
                }
                L::Return
                    if i.args.len() == 1
                        && i.results.is_empty()
                        && index + 1 == b.instructions.len()
                        && visited.len() == f.blocks.len() =>
                {
                    if f.value_types
                        .iter()
                        .any(|(id, ty)| values.get(id).is_none_or(|v| v.ty() != *ty))
                    {
                        return Err(bad("value type metadata"));
                    }
                    return trace
                        .finish(n, read(&i.args[0])?.float().ok_or(bad("return float"))?)
                        .ok_or(bad("missing call or public output"));
                }
                _ => return Err(bad("instruction outside LIR domain")),
            };
            match (made, i.results.as_slice()) {
                (Some(v), [id]) if !values.contains_key(id) => {
                    values.insert(*id, v);
                }
                (None, []) => {}
                _ => return Err(bad("result arity or duplicate identity")),
            }
        }
        next = branch.ok_or(bad("missing terminator"))?;
    }
}
/// Compare the original F32 cell fragment with its lowered endpoint.
/// Module admission, callee ABI/linking, machine correspondence and independent
/// theorem replay remain separate requirements. Without supplied callee bodies
/// this entry retains the original opaque-declaration-only profile.
pub fn check<'a>(module: &'a Module, lir: &'a Function) -> Result<Checked<'a>> {
    check_with_callees(module, lir, &[])
}

/// Compose independently checked complete original/retained callee stores
/// into the actual caller observations. A callee identity without its exact
/// lowered body is refused. This remains source/LIR checking, not native,
/// allocation, ABI, private-frame separation or theorem-replay authority.
pub fn check_with_callees<'a>(
    module: &'a Module,
    lir: &'a Function,
    callees: &'a [Function],
) -> Result<Checked<'a>> {
    let target = module
        .target_info
        .as_ref()
        .ok_or(Error::Source("missing target"))?;
    if target.triple != "aarch64-unknown-linux-gnu"
        || target.pointer_size != 8
        || target.endianness != trust_ir::Endianness::Little
        || target.abi.is_some()
        || target.struct_passing != trust_ir::StructPassingPolicy::NativeC
        || !module.globals.is_empty()
        || !module.global_asm.is_empty()
        || !module.imports.is_empty()
    {
        return Err(Error::Source("unsupported target or module context"));
    }
    let declarations = signatures(module, callees)?;
    let original = module
        .functions
        .iter()
        .find(|f| f.name == lir.name)
        .ok_or(Error::Source("missing original caller"))?;
    let expected = source(module, original, &declarations)?;
    let observed = lowering(lir, expected.float_parameters, &declarations)?;
    if expected != observed {
        return Err(Error::Mismatch);
    }
    Ok(Checked {
        module,
        original,
        lir,
        callees,
        contract: expected,
    })
}

#[cfg(test)]
#[path = "source_bound_repeated_cell_source_tests.rs"]
mod tests;
