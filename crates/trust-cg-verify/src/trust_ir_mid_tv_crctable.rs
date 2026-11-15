// trust-cg-verify/trust_ir_mid_tv_crctable.rs - a bit-serial byte loop as a table lookup
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker of the CRC-table rewrite ([`CrcTableWitness`]), deriving
//! every premise from the SOURCE function and the module with this module's
//! own code. The witness names a region, its input, the polynomial and the
//! table; nothing the pass computed is trusted.
//!
//! **The region.** A block `E`, an index `s` in it, and a join block `X`
//! (not `E`) with exactly one parameter `p`. The region is `E`'s
//! instructions from `s` on (its terminator among them) and the INNER blocks:
//! every block reachable from `E`'s terminator without passing through `X`.
//! It must be acyclic, every inner block's entering edges must come from `E`
//! or inner blocks, `X`'s entering edges likewise (so after the rewrite `E`
//! alone enters `X`), and neither the entry block nor `E` itself is inner.
//! Every instruction of the region is a pure integer operation the checker
//! evaluates: `const` (integer or `bool`), `copy`, `add`, `sub`, `mul`,
//! `and`, `or`, `xor`, `shl`, `lshr`, `ashr`, `icmp`, `select`, and the
//! integer casts `zext`, `sext`, `trunc` and same-width `bitcast`; every
//! terminator is `br`, `condbr` or `switch` to an inner block or `X`. Values
//! the region defines are used only inside it. Every operand the region
//! reads from outside it is either the claimed INPUT `x` or a value an
//! integer `const` defines.
//!
//! **The input's range.** Derived from `x`'s definition: `and` with an
//! integer constant `c` (either order) is in `[0, c]`; a `zext` from a type
//! of at most 8 bits is below `2^b`; a `urem` by a constant `c > 0` is below
//! `c`; an `lshr` by a constant `k` of a `w`-bit value is below `2^(w - k)`;
//! a constant is itself. Anything else, or a bound above 255, is refused: a
//! table has 256 entries, so the region must be a function of one byte.
//!
//! **Exhaustive evaluation.** For every `v` in `0..256` the region is run
//! from `E[s]` with `x = v` (each integer held as its bits at its type's
//! width): a shift by the width or more, a value of an unexpected type, a
//! `switch` case that is not an integer, or a walk longer than the region
//! refuses the whole claim. The value `p` receives at `X` is entry `v` of
//! the table. The region therefore equals the table on every input the
//! range admits, and on the ones above it too.
//!
//! **The polynomial.** Every `xor` of the region with an operand a `const`
//! defines must xor the same constant, and there must be at least one; that
//! constant is the polynomial, and the witness's claim must equal it. The
//! exhaustive evaluation is the proof; the polynomial names the loop.
//!
//! **The table.** A fresh, read-only, internal global `[u8 x 256 * n]`, `n`
//! the byte width of `p`'s integer type (at most 8), holding entry `v` at
//! bytes `v * n ..` little-endian, aligned to `n`; the witness appends its
//! globals after the module's (each named by at least one region; regions
//! whose tables are equal may name one), and a `u8` type only when the
//! module has none.
//!
//! **The rewrite.** `E` keeps its instructions before `s` and ends in
//!
//! `g = global_addr G; i = <x as i32>; k = const i32 n; o = mul i32 i, k;
//! a = gep inbounds u8, ptr g, o; r = load T, ptr a; br X(r)`,
//!
//! the six values being the witness's fresh names in that order (`<x as
//! i32>` is a `copy` when `x` is an `i32`, a `bitcast` from another 32-bit
//! integer, a `zext` from a narrower one and a `trunc` from a wider one:
//! exact, since `x` is below 256), and the inner blocks go. The address is
//! in bounds of `G` (`o <= 255 * n`), so `inbounds` holds. Exact: on every
//! defined `x` the load reads the entry the region computes; on a poison
//! `x` the source branches on poison and the target loads through a poison
//! address, both undefined.

use std::collections::{HashMap, HashSet};

use trust_ir::value::GlobalId;
use trust_ir::{
    BinOp, Block, BlockId, CastOp, Constant, Function, Global, ICmpOp, Inst, InstrNode, Module, Ty,
    ValueId,
};

use super::{
    Defs, MidTvError, WitnessVerdict, block_positions, drop_names, incoming_edges, int_shape,
    used_values,
};

/// The number of entries of every table: the region is a function of one
/// byte.
pub const CRC_TABLE_ENTRIES: u32 = 256;

/// One region replaced by a table lookup (module docs). `values` are the
/// six fresh names of the lookup, in order: the global's address, the index,
/// the entry size, the byte offset, the entry's address and the entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CrcTable {
    pub block: BlockId,
    pub start: usize,
    pub exit: BlockId,
    pub input: ValueId,
    pub polynomial: u128,
    pub global: GlobalId,
    pub values: Vec<ValueId>,
}

/// The CRC-table rewrite's claim, with the module entries it appends:
/// `new_types` after the module's types (a `u8` when it has none) and
/// `new_globals` after its globals, one per table.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct CrcTableWitness {
    pub tables: Vec<CrcTable>,
    pub new_types: Vec<Ty>,
    pub new_globals: Vec<Global>,
}

/// An integer value as its bits at a width.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Bits {
    raw: u128,
    width: u32,
}

fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

impl Bits {
    fn new(raw: u128, width: u32) -> Self {
        Self {
            raw: raw & mask(width),
            width,
        }
    }

    fn signed(self) -> i128 {
        if self.width == 0 || self.width >= 128 {
            return self.raw as i128;
        }
        let shift = 128 - self.width;
        ((self.raw << shift) as i128) >> shift
    }
}

/// The width and signedness of an integer or `bool` type.
fn shape(ty: &Ty, pointer_bits: u32) -> Option<(u32, bool)> {
    if *ty == Ty::Bool {
        return Some((1, false));
    }
    int_shape(ty, pointer_bits)
}

/// The value an integer or `bool` constant instruction defines.
fn constant_bits(inst: &Inst, pointer_bits: u32) -> Option<Bits> {
    let Inst::Const { ty, value } = inst else {
        return None;
    };
    let (width, _) = shape(ty, pointer_bits)?;
    match value {
        Constant::Int(k) => Some(Bits::new(*k as u128, width)),
        Constant::Bool(b) if width == 1 => Some(Bits::new(u128::from(*b), 1)),
        _ => None,
    }
}

/// Whether the region may hold `inst` (module docs).
fn pure_op(inst: &Inst) -> bool {
    match inst {
        Inst::Const { .. } | Inst::Copy { .. } | Inst::ICmp { .. } | Inst::Select { .. } => true,
        Inst::BinOp { op, .. } => matches!(
            op,
            BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::And
                | BinOp::Or
                | BinOp::Xor
                | BinOp::Shl
                | BinOp::LShr
                | BinOp::AShr
        ),
        Inst::Cast { op, .. } => matches!(
            op,
            CastOp::ZExt | CastOp::SExt | CastOp::Trunc | CastOp::Bitcast
        ),
        _ => false,
    }
}

/// `inst` evaluated on `get`'s operand values, or why not.
fn evaluate(
    inst: &Inst,
    pointer_bits: u32,
    get: &dyn Fn(ValueId) -> Option<Bits>,
) -> Result<Bits, String> {
    let read = |v: ValueId| get(v).ok_or_else(|| format!("%{v} has no value here"));
    let width_of = |ty: &Ty| {
        shape(ty, pointer_bits)
            .map(|(w, _)| w)
            .ok_or_else(|| format!("{ty:?} is not an integer"))
    };
    if let Some(bits) = constant_bits(inst, pointer_bits) {
        return Ok(bits);
    }
    match inst {
        Inst::Copy { ty, operand } => {
            let v = read(*operand)?;
            (v.width == width_of(ty)?)
                .then_some(v)
                .ok_or_else(|| "a copy changes the width".to_string())
        }
        Inst::BinOp { op, ty, lhs, rhs } => {
            let w = width_of(ty)?;
            let (a, b) = (read(*lhs)?, read(*rhs)?);
            if a.width != w || b.width != w {
                return Err("an operand is not of the operation's width".to_string());
            }
            let shift = |b: Bits| -> Result<u32, String> {
                u32::try_from(b.raw)
                    .ok()
                    .filter(|k| *k < w)
                    .ok_or_else(|| "a shift by the width or more".to_string())
            };
            let raw = match op {
                BinOp::Add => a.raw.wrapping_add(b.raw),
                BinOp::Sub => a.raw.wrapping_sub(b.raw),
                BinOp::Mul => a.raw.wrapping_mul(b.raw),
                BinOp::And => a.raw & b.raw,
                BinOp::Or => a.raw | b.raw,
                BinOp::Xor => a.raw ^ b.raw,
                BinOp::Shl => a.raw << shift(b)?,
                BinOp::LShr => a.raw >> shift(b)?,
                BinOp::AShr => (a.signed() >> shift(b)?) as u128,
                _ => return Err(format!("{op:?} is not evaluated")),
            };
            Ok(Bits::new(raw, w))
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            let w = width_of(ty)?;
            let (a, b) = (read(*lhs)?, read(*rhs)?);
            if a.width != w || b.width != w {
                return Err("an operand is not of the compare's width".to_string());
            }
            let holds = match op {
                ICmpOp::Eq => a.raw == b.raw,
                ICmpOp::Ne => a.raw != b.raw,
                ICmpOp::Ult => a.raw < b.raw,
                ICmpOp::Ule => a.raw <= b.raw,
                ICmpOp::Ugt => a.raw > b.raw,
                ICmpOp::Uge => a.raw >= b.raw,
                ICmpOp::Slt => a.signed() < b.signed(),
                ICmpOp::Sle => a.signed() <= b.signed(),
                ICmpOp::Sgt => a.signed() > b.signed(),
                ICmpOp::Sge => a.signed() >= b.signed(),
            };
            Ok(Bits::new(u128::from(holds), 1))
        }
        Inst::Select {
            ty,
            cond,
            then_val,
            else_val,
        } => {
            let w = width_of(ty)?;
            let c = read(*cond)?;
            if c.width != 1 {
                return Err("a select's condition is not a bool".to_string());
            }
            let v = read(if c.raw == 1 { *then_val } else { *else_val })?;
            (v.width == w)
                .then_some(v)
                .ok_or_else(|| "a select arm is not of its width".to_string())
        }
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => {
            let (sw, dw) = (width_of(src_ty)?, width_of(dst_ty)?);
            let v = read(*operand)?;
            if v.width != sw {
                return Err("a cast's operand is not of its source width".to_string());
            }
            match op {
                CastOp::ZExt if dw >= sw => Ok(Bits::new(v.raw, dw)),
                CastOp::SExt if dw >= sw => Ok(Bits::new(v.signed() as u128, dw)),
                CastOp::Trunc if dw <= sw => Ok(Bits::new(v.raw, dw)),
                CastOp::Bitcast if dw == sw => Ok(v),
                _ => Err(format!("{op:?} from {sw} to {dw} bits is not evaluated")),
            }
        }
        _ => Err("not a pure integer operation".to_string()),
    }
}

/// The upper bound of `x`'s range, from its definition (module docs).
fn input_bound(defs: &Defs<'_>, pointer_bits: u32, x: ValueId) -> Option<u128> {
    let constant = |v: ValueId| constant_bits(defs.inst(v)?, pointer_bits).map(|b| b.raw);
    match defs.inst(x)? {
        inst @ Inst::Const { .. } => constant_bits(inst, pointer_bits).map(|b| b.raw),
        Inst::BinOp {
            op: BinOp::And,
            lhs,
            rhs,
            ..
        } => match (constant(*lhs), constant(*rhs)) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (Some(c), None) | (None, Some(c)) => Some(c),
            (None, None) => None,
        },
        Inst::BinOp {
            op: BinOp::URem,
            rhs,
            ..
        } => constant(*rhs).filter(|c| *c > 0).map(|c| c - 1),
        Inst::BinOp {
            op: BinOp::LShr,
            ty,
            rhs,
            ..
        } => {
            let (w, _) = int_shape(ty, pointer_bits)?;
            let k = constant(*rhs).filter(|k| *k < u128::from(w))?;
            Some(mask(w - u32::try_from(k).ok()?))
        }
        Inst::Cast {
            op: CastOp::ZExt,
            src_ty,
            ..
        } => {
            let (w, _) = shape(src_ty, pointer_bits)?;
            (w <= 8).then(|| mask(w))
        }
        _ => None,
    }
}

/// The region of `table` in `source` (module docs): the inner blocks by
/// position, in layout order.
struct Region {
    e: usize,
    x: usize,
    inner: Vec<usize>,
}

fn region(
    source: &Function,
    positions: &HashMap<BlockId, usize>,
    table: &CrcTable,
) -> Result<Region, String> {
    let &e = positions.get(&table.block).ok_or("no such block")?;
    let &x = positions.get(&table.exit).ok_or("no such exit block")?;
    let entry = positions.get(&source.entry).copied();
    if e == x {
        return Err("the region's block is its exit".to_string());
    }
    let eb = &source.blocks[e];
    if table.start >= eb.body.len() {
        return Err("the start is past the block's end".to_string());
    }
    if source.blocks[x].params.len() != 1 {
        return Err("the exit block does not have exactly one parameter".to_string());
    }
    let succs = |b: usize| -> Vec<usize> {
        source.blocks[b]
            .body
            .last()
            .map(|t| t.inst.successor_edges())
            .unwrap_or_default()
            .iter()
            .filter_map(|edge| positions.get(&edge.target).copied())
            .collect()
    };
    let mut inner: HashSet<usize> = HashSet::new();
    let mut work = succs(e);
    while let Some(b) = work.pop() {
        if b == x || inner.contains(&b) {
            continue;
        }
        if b == e || Some(b) == entry {
            return Err("the region reaches its own block or the entry".to_string());
        }
        if inner.len() >= source.blocks.len() {
            return Err("the region does not close".to_string());
        }
        inner.insert(b);
        work.extend(succs(b));
    }
    let preds = incoming_edges(source, positions);
    for &b in inner.iter().chain([&x]) {
        if preds[b].iter().any(|p| *p != e && !inner.contains(p)) {
            return Err(format!(
                "block {} is entered from outside the region",
                source.blocks[b].id
            ));
        }
    }
    // Acyclic: a topological order of the inner blocks exists.
    let mut indegree: HashMap<usize, usize> = inner.iter().map(|b| (*b, 0)).collect();
    for &b in &inner {
        for s in succs(b) {
            if let Some(d) = indegree.get_mut(&s) {
                *d += 1;
            }
        }
    }
    let mut ready: Vec<usize> = indegree
        .iter()
        .filter(|(_, d)| **d == 0)
        .map(|(b, _)| *b)
        .collect();
    let mut seen = 0usize;
    while let Some(b) = ready.pop() {
        seen += 1;
        for s in succs(b) {
            if let Some(d) = indegree.get_mut(&s) {
                *d -= 1;
                if *d == 0 {
                    ready.push(s);
                }
            }
        }
    }
    if seen != inner.len() {
        return Err("the region has a cycle".to_string());
    }
    let mut inner: Vec<usize> = inner.into_iter().collect();
    inner.sort_unstable();
    Ok(Region { e, x, inner })
}

/// The region run with `x = v`: the value `X`'s parameter receives.
fn run_region(
    source: &Function,
    positions: &HashMap<BlockId, usize>,
    pointer_bits: u32,
    reg: &Region,
    table: &CrcTable,
    outside: &HashMap<ValueId, Bits>,
    v: Bits,
) -> Result<Bits, String> {
    let mut env: HashMap<ValueId, Bits> = HashMap::new();
    env.insert(table.input, v);
    let mut block = reg.e;
    let mut from = table.start;
    for _ in 0..=reg.inner.len() + 1 {
        let body = &source.blocks[block].body;
        for node in &body[from..] {
            let get = |id: ValueId| env.get(&id).or_else(|| outside.get(&id)).copied();
            let edge = match &node.inst {
                Inst::Br { target, args } => Some((*target, args)),
                Inst::CondBr {
                    cond,
                    then_target,
                    then_args,
                    else_target,
                    else_args,
                } => {
                    let c = get(*cond).ok_or("the condition has no value")?;
                    if c.width != 1 {
                        return Err("a condbr's condition is not a bool".to_string());
                    }
                    Some(if c.raw == 1 {
                        (*then_target, then_args)
                    } else {
                        (*else_target, else_args)
                    })
                }
                Inst::Switch {
                    value,
                    default,
                    default_args,
                    cases,
                    ..
                } => {
                    let s = get(*value).ok_or("the switch value has no value")?;
                    let mut taken = (*default, default_args);
                    for case in cases {
                        let Constant::Int(k) = case.value else {
                            return Err("a switch case is not an integer".to_string());
                        };
                        if Bits::new(k as u128, s.width) == s {
                            taken = (case.target, &case.args);
                            break;
                        }
                    }
                    Some(taken)
                }
                inst => {
                    let [r] = node.results.as_slice() else {
                        return Err("an instruction without one result".to_string());
                    };
                    let value = evaluate(inst, pointer_bits, &get)?;
                    env.insert(*r, value);
                    None
                }
            };
            let Some((target, args)) = edge else {
                continue;
            };
            let &t = positions.get(&target).ok_or("an edge to no block")?;
            let values: Vec<Bits> = args
                .iter()
                .map(|a| {
                    env.get(a)
                        .or_else(|| outside.get(a))
                        .copied()
                        .ok_or_else(|| format!("argument %{a} has no value"))
                })
                .collect::<Result<_, _>>()?;
            let params = &source.blocks[t].params;
            if params.len() != values.len() {
                return Err("an edge passes the wrong arity".to_string());
            }
            if t == reg.x {
                let (_, ty) = &params[0];
                let (w, _) =
                    shape(ty, pointer_bits).ok_or("the exit parameter is not an integer")?;
                return if values[0].width == w {
                    Ok(values[0])
                } else {
                    Err("the exit argument is not of the parameter's width".to_string())
                };
            }
            for ((p, ty), value) in params.iter().zip(values) {
                let (w, _) = shape(ty, pointer_bits).ok_or("a parameter is not an integer")?;
                if value.width != w {
                    return Err("an argument is not of its parameter's width".to_string());
                }
                env.insert(*p, value);
            }
            block = t;
            from = 0;
            break;
        }
    }
    Err("the walk does not reach the exit".to_string())
}

pub(super) fn rebuild_crc_table(
    module: &Module,
    pointer_bits: u32,
    source: &Function,
    witness: &CrcTableWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let bad_global = |why: String| MidTvError::BadGlobal { why };
    let base_global = module.globals.len();
    for (i, global) in witness.new_globals.iter().enumerate() {
        let id = u32::try_from(base_global + i).map(GlobalId::new).ok();
        if !witness.tables.iter().any(|t| Some(t.global) == id) {
            return Err(bad_global(format!(
                "`{}` is no table's global",
                global.name
            )));
        }
    }
    let base_type = module.types.len();
    for (i, ty) in witness.new_types.iter().enumerate() {
        if *ty != Ty::U8 || module.types.contains(&Ty::U8) || i > 0 {
            return Err(bad_global(format!(
                "new type {} is not the module's first u8",
                base_type + i
            )));
        }
    }
    let resolve_ty = |id: trust_ir::TyId| -> Option<&Ty> {
        module
            .ty(id)
            .or_else(|| witness.new_types.get(id.as_usize().checked_sub(base_type)?))
    };
    let defs = Defs::of(source);
    let positions = block_positions(source);
    let mut taken: HashSet<ValueId> = used_values(source);
    for block in &source.blocks {
        taken.extend(block.params.iter().map(|(v, _)| *v));
        for node in &block.body {
            taken.extend(node.results.iter().copied());
        }
    }
    if let Some(names) = &source.value_names {
        taken.extend(names.iter().map(|(v, _)| *v));
    }
    let mut names: HashSet<&str> = module
        .globals
        .iter()
        .map(|g| g.name.as_str())
        .chain(module.functions.iter().map(|f| f.name.as_str()))
        .collect();
    let mut claimed_blocks: HashSet<usize> = HashSet::new();
    let mut expected = source.clone();
    let mut removed_blocks: HashSet<BlockId> = HashSet::new();
    let mut removed_values: HashSet<ValueId> = HashSet::new();
    let mut rewritten: Vec<(usize, usize, Vec<InstrNode>)> = Vec::new();
    let mut named: HashSet<usize> = HashSet::new();
    for table in &witness.tables {
        let bad = |why: String| MidTvError::NotCrcTable {
            block: table.block,
            why,
        };
        let id = table.global;
        let global = id
            .as_usize()
            .checked_sub(base_global)
            .and_then(|i| witness.new_globals.get(i))
            .ok_or_else(|| {
                bad(format!(
                    "the table names global {id}, not one the rewrite appends"
                ))
            })?;
        let reg = region(source, &positions, table).map_err(bad)?;
        for b in reg.inner.iter().chain([&reg.e]) {
            if !claimed_blocks.insert(*b) {
                return Err(bad("two regions share a block".to_string()));
            }
        }
        // ---- Purity, and what the region defines and reads.
        let mut defined: HashSet<ValueId> = HashSet::new();
        let mut nodes: Vec<&InstrNode> = source.blocks[reg.e].body[table.start..].iter().collect();
        for &b in &reg.inner {
            defined.extend(source.blocks[b].params.iter().map(|(v, _)| *v));
            nodes.extend(&source.blocks[b].body);
        }
        for node in &nodes {
            defined.extend(node.results.iter().copied());
            let ok = if node.inst.is_terminator() {
                matches!(
                    node.inst,
                    Inst::Br { .. } | Inst::CondBr { .. } | Inst::Switch { .. }
                )
            } else {
                pure_op(&node.inst) && node.results.len() == 1
            };
            if !ok {
                return Err(bad(
                    "the region holds an instruction that is not a pure integer operation"
                        .to_string(),
                ));
            }
        }
        let mut outside: HashMap<ValueId, Bits> = HashMap::new();
        for node in &nodes {
            let mut stray = None;
            node.inst.visit_value_operands(|v| {
                if defined.contains(&v) || v == table.input {
                    return;
                }
                match defs.inst(v).and_then(|i| constant_bits(i, pointer_bits)) {
                    Some(bits) => {
                        outside.insert(v, bits);
                    }
                    None => stray = Some(v),
                }
            });
            if let Some(v) = stray {
                return Err(bad(format!(
                    "the region reads %{v}, neither the input nor a constant"
                )));
            }
        }
        if defined.contains(&table.input) {
            return Err(bad("the input is defined inside the region".to_string()));
        }
        // The input is read inside the region, so its definition dominates
        // the end of `E`, where the lookup reads it: every path into the
        // region passes `E`'s terminator, and the region does not define it.
        let mut read = false;
        for node in &nodes {
            node.inst.visit_value_operands(|v| read |= v == table.input);
        }
        if !read {
            return Err(bad("the region does not read the input".to_string()));
        }
        let region_blocks: HashSet<usize> = reg.inner.iter().copied().collect();
        for (bi, block) in source.blocks.iter().enumerate() {
            if region_blocks.contains(&bi) {
                continue;
            }
            let from = if bi == reg.e {
                table.start
            } else {
                block.body.len()
            };
            for node in &block.body[..from] {
                let mut leak = false;
                node.inst
                    .visit_value_operands(|v| leak |= defined.contains(&v));
                if leak {
                    return Err(bad("a value of the region is used outside it".to_string()));
                }
            }
            if bi != reg.e {
                for node in &block.body {
                    let mut leak = false;
                    node.inst
                        .visit_value_operands(|v| leak |= defined.contains(&v));
                    if leak {
                        return Err(bad("a value of the region is used outside it".to_string()));
                    }
                }
            }
        }
        // ---- The input.
        let input_ty = defs
            .value_type(table.input)
            .ok_or_else(|| bad("the input has no type".to_string()))?;
        let (in_width, _) = int_shape(&input_ty, pointer_bits)
            .ok_or_else(|| bad("the input is not an integer".to_string()))?;
        let bound = input_bound(&defs, pointer_bits, table.input).ok_or_else(|| {
            bad("the input's range is not derived from its definition".to_string())
        })?;
        if bound >= u128::from(CRC_TABLE_ENTRIES) {
            return Err(bad(format!(
                "the input reaches {bound}, past a table of {CRC_TABLE_ENTRIES} entries"
            )));
        }
        // ---- The polynomial.
        let mut polynomial: Option<u128> = None;
        for node in &nodes {
            if let Inst::BinOp {
                op: BinOp::Xor,
                lhs,
                rhs,
                ..
            } = &node.inst
            {
                for side in [lhs, rhs] {
                    if let Some(c) = defs
                        .inst(*side)
                        .and_then(|i| constant_bits(i, pointer_bits))
                    {
                        if polynomial.is_some_and(|p| p != c.raw) {
                            return Err(bad("the region xors two different constants".to_string()));
                        }
                        polynomial = Some(c.raw);
                    }
                }
            }
        }
        let polynomial =
            polynomial.ok_or_else(|| bad("the region xors no constant".to_string()))?;
        if polynomial != table.polynomial {
            return Err(bad(format!(
                "the polynomial is {polynomial:#x}, not {:#x}",
                table.polynomial
            )));
        }
        // ---- The entries.
        let (_, out_ty) = &source.blocks[reg.x].params[0];
        let (out_width, _) = int_shape(out_ty, pointer_bits)
            .ok_or_else(|| bad("the exit parameter is not an integer".to_string()))?;
        if out_width % 8 != 0 || out_width > 64 {
            return Err(bad(
                "the entry is not a whole number of bytes up to 8".to_string()
            ));
        }
        let n = out_width / 8;
        let mut data: Vec<u8> = Vec::with_capacity((CRC_TABLE_ENTRIES * n) as usize);
        for v in 0..CRC_TABLE_ENTRIES {
            let entry = run_region(
                source,
                &positions,
                pointer_bits,
                &reg,
                table,
                &outside,
                Bits::new(u128::from(v), in_width),
            )
            .map_err(|why| bad(format!("input {v}: {why}")))?;
            data.extend_from_slice(&entry.raw.to_le_bytes()[..n as usize]);
        }
        // ---- The global.
        let Ty::Array(elem, len) = &global.ty else {
            return Err(bad_global(format!("`{}` is not a byte array", global.name)));
        };
        if *len != u64::from(CRC_TABLE_ENTRIES * n) || resolve_ty(*elem) != Some(&Ty::U8) {
            return Err(bad_global(format!(
                "`{}` is not a [u8 x {}]",
                global.name,
                CRC_TABLE_ENTRIES * n
            )));
        }
        let expected_global = Global {
            name: global.name.clone(),
            ty: global.ty.clone(),
            mutable: false,
            initializer: Some(Constant::Bytes { data, utf8: false }),
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: Some(n),
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
        };
        if *global != expected_global {
            return Err(bad_global(format!(
                "`{}` is not the table of the region",
                global.name
            )));
        }
        if named.insert(id.as_usize()) && !names.insert(global.name.as_str()) {
            return Err(bad_global(format!("`{}` is not a fresh name", global.name)));
        }
        // ---- The lookup.
        let [g, i, k, o, a, r] = table.values.as_slice() else {
            return Err(bad("the lookup takes six fresh values".to_string()));
        };
        for v in &table.values {
            if !taken.insert(*v) {
                return Err(bad(format!("%{v} is not fresh")));
            }
        }
        let index_ty = Ty::I32;
        let index = if pointer_bits != 32 {
            return Err(bad("the lookup is spelled for 32-bit pointers".to_string()));
        } else if input_ty == index_ty {
            Inst::Copy {
                ty: index_ty.clone(),
                operand: table.input,
            }
        } else {
            let op = match in_width.cmp(&32) {
                std::cmp::Ordering::Equal => CastOp::Bitcast,
                std::cmp::Ordering::Less => CastOp::ZExt,
                std::cmp::Ordering::Greater => CastOp::Trunc,
            };
            Inst::Cast {
                op,
                src_ty: input_ty.clone(),
                dst_ty: index_ty.clone(),
                operand: table.input,
            }
        };
        let lookup = vec![
            InstrNode::new(Inst::GlobalAddr { global: id }).with_results([*g]),
            InstrNode::new(index).with_results([*i]),
            InstrNode::new(Inst::Const {
                ty: index_ty.clone(),
                value: Constant::Int(i128::from(n)),
            })
            .with_results([*k]),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: index_ty,
                lhs: *i,
                rhs: *k,
            })
            .with_results([*o]),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::U8,
                base: *g,
                indices: vec![*o],
                inbounds: true,
            })
            .with_results([*a]),
            InstrNode::new(Inst::Load {
                ty: out_ty.clone(),
                ptr: *a,
                volatile: false,
                align: Some(u64::from(n)),
            })
            .with_results([*r]),
            InstrNode::new(Inst::Br {
                target: table.exit,
                args: vec![*r],
            }),
        ];
        rewritten.push((reg.e, table.start, lookup));
        for &b in &reg.inner {
            removed_blocks.insert(source.blocks[b].id);
        }
        removed_values.extend(defined.iter().copied());
    }
    for (e, start, lookup) in rewritten {
        let block: &mut Block = &mut expected.blocks[e];
        block.body.truncate(start);
        block.body.extend(lookup);
    }
    expected.blocks.retain(|b| !removed_blocks.contains(&b.id));
    drop_names(&mut expected, &removed_values);
    Ok((
        expected,
        WitnessVerdict {
            exact: witness.tables.len(),
            refinements: 0,
        },
    ))
}

#[cfg(test)]
#[path = "trust_ir_mid_tv_crctable_tests.rs"]
mod tests;
