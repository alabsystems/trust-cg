// trust-cg-verify/trust_ir_mid_tv_bytecopy.rs - byte copies as `memcopy`, stores forwarded
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker of the byte-copy rewrite ([`ByteCopyWitness`]), deriving its
//! premises from the SOURCE function and the module with this module's own
//! code.
//!
//! The rustc bridge copies a value of a byte-array type (a `#[repr(packed)]`
//! struct is one: its fields are unaligned) lane by lane: a `load i8` of each
//! byte of the source and a `store i8` (or a write-through `insertfield`,
//! which field-access lowering has made a store) of it into the
//! destination. A 15-byte packed struct returned through its out-pointer
//! was 15 byte loads and stores after four typed stores into a temporary;
//! LLVM stores the four fields into the out-pointer. Two rewrites, applied
//! in the witness's order (every run first, then every forward):
//!
//! **A run** ([`ByteCopyRun`]) names a block and the positions `first` and
//! `last` of its source body. Every instruction from `first` to `last` is
//! either part of the copy or inert: a non-volatile `load` of a one-byte
//! integer whose result is used by exactly one instruction of the function,
//! a non-volatile `store` of that result at that type (the pair), or a
//! `const`, `copy`, cast, `gep` or integer `add`/`sub`/`mul`/`and`/`or`/
//! `xor`/shift, which write no memory, call nothing and assert nothing.
//! `last` is a store. The pairs' source addresses are the bytes `s, s + 1,
//! ..., s + k - 1` of one base and their destination addresses `d + (that
//! byte's offset - s)` of another, each base resolved by this module's walk
//! ([`Root`]: an `alloca`, an entry parameter or a global's address, then
//! copies, `ptrtoptr`s and `gep`s by non-negative constants), `k >= 2`. The
//! two ranges are disjoint: two different `alloca`s, an `alloca` and a
//! parameter or global (an allocation this activation made is not one its
//! caller could name), two different globals, or one base with
//! non-overlapping ranges. The run's loads and stores go, and at `last`
//! the rewrite defines `count = const usize k` and does `memcopy dst, src,
//! count` (not overlapping) from the lowest pair's addresses. Over
//! disjoint ranges the sequential byte copies write exactly the bytes
//! `memcopy` writes; the inert instructions observe no memory, so
//! performing the writes at `last` is unobservable, and an instruction
//! among them that raises makes the source undefined. A REFINEMENT: a byte
//! load of part of a pointer drops its provenance where `memcopy` keeps it.
//!
//! **A forward** ([`ByteCopyForward`]) names a `memcopy dst, src, count`
//! (after the runs) whose count is a constant `k`, whose `src` is `(T, t)`
//! inside an `alloca` `T` and whose `dst` resolves disjoint from it, and a
//! list of earlier stores of the same block: non-volatile, each through a
//! pointer `(T, o)`, pairwise disjoint, together covering exactly the
//! bytes `[t, t + k)`. `T` must not escape: every use of a pointer derived
//! from it (by copies, `ptrtoptr`s and constant `gep`s) is a load or store
//! through it, a `memcopy` or `memset` operand, or a further such
//! derivation, so only the function's own accesses reach its bytes; and no
//! other store, `memcopy` or `memset` writes through such a pointer between
//! the first named store and the `memcopy`. The `memcopy` becomes, in
//! place, for each named store in order of offset, `off = const usize (o -
//! t); at = gep u8, ptr dst, off; store <its type> <its value>, at` with
//! alignment 1, the fresh values named by the witness. Exact: `T`'s bytes
//! at the copy are the images the named stores wrote, which the stores
//! write again into the destination. Dead-slot removal then drops the
//! stores into `T` when nothing else reads it.

use std::collections::{HashMap, HashSet};

use trust_ir::{BinOp, BlockId, CastOp, Constant, Function, Inst, InstrNode, Module, Ty, ValueId};

use super::{Defs, MidTvError, WitnessVerdict, block_positions, use_positions};
use trust_ir::value::GlobalId;

use crate::fsym_layout::FsymLayout;

/// A run of byte copies in block `block`, from position `first` to
/// position `last` of the source body, rewritten as one `memcopy` of the
/// fresh `const usize` `count` at `last`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ByteCopyRun {
    pub block: BlockId,
    pub first: usize,
    pub last: usize,
    pub count: ValueId,
}

/// One store forwarded through a `memcopy`: the store at position `store`
/// of the block, and the fresh offset constant and address the rewrite
/// stores it at.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ForwardedStore {
    pub store: usize,
    pub offset: ValueId,
    pub address: ValueId,
}

/// A `memcopy` (position `copy` of block `block` after the runs) replaced
/// by the stores its source bytes came from, in order of offset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ByteCopyForward {
    pub block: BlockId,
    pub copy: usize,
    pub stores: Vec<ForwardedStore>,
}

/// The byte-copy rewrite's claim.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ByteCopyWitness {
    pub runs: Vec<ByteCopyRun>,
    pub forwards: Vec<ByteCopyForward>,
}

impl ByteCopyWitness {
    /// Number of claimed rewrites.
    pub fn rewrite_count(&self) -> usize {
        self.runs.len() + self.forwards.len()
    }
}

/// The allocation an address is derived from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Root {
    Alloca(ValueId),
    Param(ValueId),
    Global(GlobalId),
}

const MAX_WALK: usize = 64;

/// `(root, displacement)` of the address `v`: the root, then copies,
/// `ptrtoptr`s and `gep`s by non-negative integer constants (the
/// interpreter's flat GEP: `size(pointee) * sum(indices)` bytes on).
fn resolve(
    layout: &FsymLayout<'_>,
    defs: &Defs<'_>,
    entry_params: &HashSet<ValueId>,
    mut v: ValueId,
) -> Option<(Root, u64)> {
    let mut disp: u64 = 0;
    for _ in 0..MAX_WALK {
        if entry_params.contains(&v) {
            return Some((Root::Param(v), disp));
        }
        match defs.inst(v)? {
            Inst::Alloca { .. } => return Some((Root::Alloca(v), disp)),
            Inst::GlobalAddr { global } => return Some((Root::Global(*global), disp)),
            Inst::Copy { operand, .. }
            | Inst::Cast {
                op: CastOp::PtrToPtr,
                operand,
                ..
            } => v = *operand,
            Inst::GEP {
                pointee_ty,
                base,
                indices,
                ..
            } => {
                let elem = layout.size(pointee_ty).ok()?;
                for k in indices {
                    let Some(Inst::Const {
                        ty,
                        value: Constant::Int(k),
                    }) = defs.inst(*k)
                    else {
                        return None;
                    };
                    if !ty.is_integer() {
                        return None;
                    }
                    let k = u64::try_from(*k).ok()?;
                    disp = disp.checked_add(elem.checked_mul(k)?)?;
                }
                v = *base;
            }
            _ => return None,
        }
    }
    None
}

/// Whether the byte ranges `[a, a + n)` of root `ra` and `[b, b + n)` of
/// root `rb` are disjoint on every execution.
fn disjoint(ra: Root, a: u64, rb: Root, b: u64, n: u64) -> bool {
    match (ra, rb) {
        (Root::Alloca(x), Root::Alloca(y)) if x == y => a + n <= b || b + n <= a,
        (Root::Global(x), Root::Global(y)) if x == y => a + n <= b || b + n <= a,
        (Root::Alloca(_), _) | (_, Root::Alloca(_)) => true,
        (Root::Global(_), Root::Global(_)) => true,
        _ => false,
    }
}

fn one_byte(ty: &Ty) -> bool {
    matches!(ty, Ty::I8 | Ty::U8)
}

/// An instruction a run may contain besides its pairs: it writes no
/// memory, calls nothing and asserts nothing.
fn inert(inst: &Inst) -> bool {
    match inst {
        Inst::Const { .. } | Inst::Copy { .. } | Inst::Cast { .. } | Inst::GEP { .. } => true,
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
        _ => false,
    }
}

fn node_like(template: &InstrNode, inst: Inst, results: Vec<ValueId>) -> InstrNode {
    let mut node = template.clone();
    node.inst = inst;
    node.results = results;
    node
}

/// The values derived from the `alloca` `slot` by copies, `ptrtoptr`s and
/// `gep`s whose base is derived (indices of any form), or `None` when one
/// escapes: used other than as the address of a load or store, a
/// `memcopy` or `memset` operand, or the operand of a further derivation.
fn non_escaping_family(func: &Function, slot: ValueId) -> Option<HashSet<ValueId>> {
    let mut family: HashSet<ValueId> = HashSet::from([slot]);
    loop {
        let mut grew = false;
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            let derived = match &node.inst {
                Inst::Copy { operand, .. }
                | Inst::Cast {
                    op: CastOp::PtrToPtr,
                    operand,
                    ..
                } => family.contains(operand),
                Inst::GEP { base, .. } => family.contains(base),
                _ => false,
            };
            if derived && let [r] = node.results.as_slice() {
                grew |= family.insert(*r);
            }
        }
        if !grew {
            break;
        }
    }
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        let mut operands = Vec::new();
        node.inst.visit_value_operands(|v| operands.push(v));
        let ok = match &node.inst {
            Inst::Load { .. } => true,
            Inst::Store { value, .. } => !family.contains(value),
            Inst::MemCopy { .. } | Inst::MemSet { .. } => true,
            Inst::Copy { .. }
            | Inst::Cast {
                op: CastOp::PtrToPtr,
                ..
            } => true,
            Inst::GEP { indices, .. } => !indices.iter().any(|i| family.contains(i)),
            _ => !operands.iter().any(|v| family.contains(v)),
        };
        if !ok {
            return None;
        }
    }
    Some(family)
}

fn rebuild_runs(
    module: &Module,
    source: &Function,
    runs: &[ByteCopyRun],
    taken: &mut HashSet<ValueId>,
) -> Result<Function, MidTvError> {
    let layout = FsymLayout::new(module);
    let defs = Defs::of(source);
    let uses = use_positions(source);
    let positions = block_positions(source);
    let entry_params: HashSet<ValueId> = source
        .blocks
        .iter()
        .find(|b| b.id == source.entry)
        .map(|b| b.params.iter().map(|(v, _)| *v).collect())
        .unwrap_or_default();
    // (block position) -> (removed positions, inserted nodes at a position).
    let mut removed: HashSet<(usize, usize)> = HashSet::new();
    let mut inserted: HashMap<(usize, usize), Vec<InstrNode>> = HashMap::new();
    for run in runs {
        let bad = |why: &str| MidTvError::NotByteCopy {
            block: run.block,
            index: run.first,
            why: why.to_string(),
        };
        let &bi = positions
            .get(&run.block)
            .ok_or_else(|| bad("no such block"))?;
        let body = &source.blocks[bi].body;
        if run.first > run.last || run.last >= body.len() {
            return Err(bad("the run's positions are not in the block"));
        }
        if (run.first..=run.last)
            .any(|ni| removed.contains(&(bi, ni)) || inserted.contains_key(&(bi, ni)))
        {
            return Err(bad("the run overlaps another run"));
        }
        // The pairs: the load's result is used once, by the store.
        let mut loads: HashMap<ValueId, (u64, Root, ValueId)> = HashMap::new();
        let mut pairs: Vec<(u64, Root, ValueId, u64, Root, ValueId)> = Vec::new();
        for node in &body[run.first..=run.last] {
            match &node.inst {
                Inst::Load {
                    ty,
                    ptr,
                    volatile: false,
                    ..
                } if one_byte(ty) => {
                    let [r] = node.results.as_slice() else {
                        return Err(bad("a load without one result"));
                    };
                    let (root, off) = resolve(&layout, &defs, &entry_params, *ptr)
                        .ok_or_else(|| bad("a load's address does not resolve"))?;
                    loads.insert(*r, (off, root, *ptr));
                }
                Inst::Store {
                    ty,
                    ptr,
                    value,
                    volatile: false,
                    ..
                } if one_byte(ty) => {
                    let (s_off, s_root, s_ptr) = loads
                        .remove(value)
                        .ok_or_else(|| bad("a store does not store a byte the run loaded"))?;
                    if defs.value_type(*value).as_ref() != Some(ty) {
                        return Err(bad("a store's type is not its load's"));
                    }
                    let used: usize = uses.get(value).map_or(0, Vec::len);
                    if used != 1 {
                        return Err(bad("a loaded byte has another use"));
                    }
                    let (root, off) = resolve(&layout, &defs, &entry_params, *ptr)
                        .ok_or_else(|| bad("a store's address does not resolve"))?;
                    pairs.push((s_off, s_root, s_ptr, off, root, *ptr));
                }
                inst if inert(inst) => {}
                _ => return Err(bad("the run holds an instruction with an effect")),
            }
        }
        if !loads.is_empty() {
            return Err(bad("a load of the run is not stored by it"));
        }
        if !matches!(body[run.last].inst, Inst::Store { .. }) {
            return Err(bad("the run does not end with a store"));
        }
        let k = u64::try_from(pairs.len()).map_err(|_| bad("too many pairs"))?;
        if k < 2 {
            return Err(bad("a run copies at least two bytes"));
        }
        let lowest = pairs
            .iter()
            .min_by_key(|p| p.0)
            .copied()
            .ok_or_else(|| bad("no pairs"))?;
        let (s0, s_root, src, d0, d_root, dst) = lowest;
        let mut seen: HashSet<u64> = HashSet::new();
        for &(s, sr, _, d, dr, _) in &pairs {
            if sr != s_root || dr != d_root || s < s0 || d < d0 || s - s0 != d - d0 || s - s0 >= k {
                return Err(bad("the pairs are not one contiguous copy"));
            }
            if !seen.insert(s - s0) {
                return Err(bad("a byte is copied twice"));
            }
        }
        if !disjoint(s_root, s0, d_root, d0, k) {
            return Err(bad("the source and destination may overlap"));
        }
        if !taken.insert(run.count) {
            return Err(bad("the count is not a fresh value"));
        }
        for (ni, node) in body.iter().enumerate().take(run.last + 1).skip(run.first) {
            if matches!(node.inst, Inst::Load { .. } | Inst::Store { .. }) {
                removed.insert((bi, ni));
            }
        }
        let template = &body[run.last];
        inserted.insert(
            (bi, run.last),
            vec![
                node_like(
                    template,
                    Inst::Const {
                        ty: Ty::Usize,
                        value: Constant::Int(i128::from(k)),
                    },
                    vec![run.count],
                ),
                node_like(
                    template,
                    Inst::MemCopy {
                        dst,
                        src,
                        bytes: run.count,
                        overlap: false,
                    },
                    Vec::new(),
                ),
            ],
        );
    }
    let mut out = source.clone();
    let dead: HashSet<ValueId> = removed
        .iter()
        .flat_map(|&(bi, ni)| source.blocks[bi].body[ni].results.iter().copied())
        .collect();
    super::drop_names(&mut out, &dead);
    for (bi, block) in out.blocks.iter_mut().enumerate() {
        let body = std::mem::take(&mut block.body);
        for (ni, node) in body.into_iter().enumerate() {
            if let Some(nodes) = inserted.remove(&(bi, ni)) {
                block.body.extend(nodes);
            } else if !removed.contains(&(bi, ni)) {
                block.body.push(node);
            }
        }
    }
    Ok(out)
}

fn rebuild_forwards(
    module: &Module,
    func: &Function,
    forwards: &[ByteCopyForward],
    taken: &mut HashSet<ValueId>,
) -> Result<Function, MidTvError> {
    let layout = FsymLayout::new(module);
    let defs = Defs::of(func);
    let positions = block_positions(func);
    let entry_params: HashSet<ValueId> = func
        .blocks
        .iter()
        .find(|b| b.id == func.entry)
        .map(|b| b.params.iter().map(|(v, _)| *v).collect())
        .unwrap_or_default();
    let mut replaced: HashMap<(usize, usize), Vec<InstrNode>> = HashMap::new();
    for fwd in forwards {
        let bad = |why: &str| MidTvError::NotByteCopy {
            block: fwd.block,
            index: fwd.copy,
            why: why.to_string(),
        };
        let &bi = positions
            .get(&fwd.block)
            .ok_or_else(|| bad("no such block"))?;
        let body = &func.blocks[bi].body;
        let node = body
            .get(fwd.copy)
            .ok_or_else(|| bad("no such instruction"))?;
        if replaced.contains_key(&(bi, fwd.copy)) {
            return Err(bad("forwarded twice"));
        }
        let Inst::MemCopy {
            dst, src, bytes, ..
        } = &node.inst
        else {
            return Err(bad("not a memcopy"));
        };
        let k = match defs.inst(*bytes) {
            Some(Inst::Const {
                ty,
                value: Constant::Int(k),
            }) if ty.is_integer() && *k > 0 => u64::try_from(*k).map_err(|_| bad("bad count"))?,
            _ => return Err(bad("the count is not a positive constant")),
        };
        let (Some((Root::Alloca(slot), t)), Some((d_root, d))) = (
            resolve(&layout, &defs, &entry_params, *src),
            resolve(&layout, &defs, &entry_params, *dst),
        ) else {
            return Err(bad(
                "the source is not inside an alloca, or the destination does not resolve",
            ));
        };
        if !disjoint(Root::Alloca(slot), t, d_root, d, k) {
            return Err(bad("the source and destination may overlap"));
        }
        let family = non_escaping_family(func, slot).ok_or_else(|| bad("the slot escapes"))?;
        // The named stores: earlier in the block, through the slot, pairwise
        // disjoint, covering [t, t + k) exactly.
        let mut pieces: Vec<(u64, u64, &ForwardedStore, Ty, ValueId)> = Vec::new();
        let mut first = fwd.copy;
        for fs in &fwd.stores {
            if fs.store >= fwd.copy {
                return Err(bad("a named store does not precede the copy"));
            }
            first = first.min(fs.store);
            let Inst::Store {
                ty,
                ptr,
                value,
                volatile: false,
                ..
            } = &body[fs.store].inst
            else {
                return Err(bad("a named store is not a plain store"));
            };
            let (root, o) = resolve(&layout, &defs, &entry_params, *ptr)
                .ok_or_else(|| bad("a named store's address does not resolve"))?;
            if root != Root::Alloca(slot) {
                return Err(bad("a named store is not into the copied slot"));
            }
            let size = layout
                .size(ty)
                .map_err(|_| bad("a stored type has no size"))?;
            if size == 0 || o < t || o + size > t + k {
                return Err(bad("a named store is not inside the copied bytes"));
            }
            pieces.push((o, size, fs, ty.clone(), *value));
        }
        pieces.sort_by_key(|p| p.0);
        let mut at = t;
        for p in &pieces {
            if p.0 != at {
                return Err(bad(
                    "the named stores do not cover the copied bytes exactly",
                ));
            }
            at += p.1;
        }
        if at != t + k {
            return Err(bad(
                "the named stores do not cover the copied bytes exactly",
            ));
        }
        let named: HashSet<usize> = fwd.stores.iter().map(|s| s.store).collect();
        for (ni, other) in body.iter().enumerate().take(fwd.copy).skip(first) {
            if named.contains(&ni) {
                continue;
            }
            let writes = match &other.inst {
                Inst::Store { ptr, .. } => family.contains(ptr),
                Inst::MemCopy { dst, .. } | Inst::MemSet { dst, .. } => family.contains(dst),
                _ => false,
            };
            if writes {
                return Err(bad("another write reaches the slot before the copy"));
            }
        }
        let mut nodes = Vec::new();
        for (o, _, fs, ty, value) in pieces {
            if !taken.insert(fs.offset) || !taken.insert(fs.address) {
                return Err(bad("a named value is not fresh"));
            }
            nodes.push(node_like(
                node,
                Inst::Const {
                    ty: Ty::Usize,
                    value: Constant::Int(i128::from(o - t)),
                },
                vec![fs.offset],
            ));
            nodes.push(node_like(
                node,
                Inst::GEP {
                    pointee_ty: Ty::U8,
                    base: *dst,
                    indices: vec![fs.offset],
                    inbounds: false,
                },
                vec![fs.address],
            ));
            nodes.push(node_like(
                node,
                Inst::Store {
                    ty,
                    ptr: fs.address,
                    value,
                    volatile: false,
                    align: Some(1),
                },
                Vec::new(),
            ));
        }
        replaced.insert((bi, fwd.copy), nodes);
    }
    let mut out = func.clone();
    for (bi, block) in out.blocks.iter_mut().enumerate() {
        let body = std::mem::take(&mut block.body);
        block.body = body
            .into_iter()
            .enumerate()
            .flat_map(|(ni, node)| replaced.remove(&(bi, ni)).unwrap_or_else(|| vec![node]))
            .collect();
    }
    Ok(out)
}

pub(super) fn rebuild_byte_copy(
    module: &Module,
    source: &Function,
    witness: &ByteCopyWitness,
) -> Result<(Function, WitnessVerdict), MidTvError> {
    let mut taken: HashSet<ValueId> = HashSet::new();
    for block in &source.blocks {
        taken.extend(block.params.iter().map(|(v, _)| *v));
        for node in &block.body {
            taken.extend(node.results.iter().copied());
            node.inst.visit_value_operands(|v| {
                taken.insert(v);
            });
        }
    }
    if let Some(names) = &source.value_names {
        taken.extend(names.iter().map(|(v, _)| *v));
    }
    let after_runs = rebuild_runs(module, source, &witness.runs, &mut taken)?;
    let expected = rebuild_forwards(module, &after_runs, &witness.forwards, &mut taken)?;
    Ok((
        expected,
        WitnessVerdict {
            exact: witness.forwards.len(),
            refinements: witness.runs.len(),
        },
    ))
}

#[cfg(test)]
#[path = "trust_ir_mid_tv_bytecopy_tests.rs"]
mod tests;
