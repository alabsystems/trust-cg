// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 17: private stack accesses at a non-constant offset (ruling OD-183
//! in `docs/decision-record.md`).
//!
//! An `Iadd` of a private frame address `(slot, c)` and a value `d` that is
//! neither a constant of the chain nor a private address, and an `ArrayGep`
//! of one at such an index `d` with element size `s` (OD-185's stride), is
//! an INDEXED address [`IndexedAddr`]: no SMT term of its own, the 64-bit
//! OFFSET term `o = c + d * s` (`s = 1` for `Iadd`; wrapping,
//! [`IndexedAddr::offset`]). It stays indexed through `Copy`, `Bitcast` to
//! `I64`, `Iadd` of a constant, `StructGep` and `ArrayGep` at a constant
//! index. An access of `w` bytes through it (a load, a store; a direct call's
//! argument is `w = 0`) into a slot of `n` bytes has the CANDIDATE offsets
//! ([`candidates`]) `k` in `0..=n - w` with `k ≡ c` modulo the ALIGNMENT
//! MODULUS `l`, the power of two the offset's variable part is a multiple
//! of ([`modulus_of`], [`stride_modulus`]).
//!
//! - A load reads [`select`], the LOW-BIT select over the candidates' reads
//!   `B(k)` (what a load at the constant offset `k` reads): a balanced
//!   `ite` tree on the bits of `o` above the modulus, which name the
//!   candidate's index where `o` is one.
//! - A store of `x` makes each byte `p` some candidate covers the
//!   [`update`] `(ite (= o k) byte_{p-k}(x) (ite ... old_p))` over the
//!   candidates that cover it ([`covering`]).
//! - Each side CLAIMS, for each of its indexed accesses, that its own offset
//!   is a candidate ([`in_bounds`]): `(bvule o (n - w))` and, when `l > 1`,
//!   `(= (bvand o (l - 1)) (c mod l))`. In-bounds is a claim the solver
//!   proves, never a premise (trust-ir's `IntToPtr` resolves provenance by
//!   address, and LIR lowers a GEP and integer pointer arithmetic alike to
//!   an `Iadd`, so a premise could waive a defined run).
//!
//! **Exactness lemma** (trusted, unit-swept against a concrete byte array by
//! `the_indexed_spelling_is_exact_on_every_candidate`): where `in_bounds(o)`
//! holds, `o` is a candidate, `select` is the `w` bytes at `o`, and `update`
//! is the store of `x` at `o`. Both walks call these functions and no other
//! spelling of them exists.
//!
//! Admission also requires a BOUND ([`check_bounds`]): in every region that
//! reaches the use, a dominating guard edge whose compare of the index
//! against a constant, or the index's own definition (a narrow extension, a
//! mask, a shift, a remainder by a constant), implies the offset is a
//! candidate. The bound finder decides admission only: the claim is proved
//! by the solver anyway, so a wrong bound refuses or refutes, never credits;
//! its purpose is to refuse, rather than refute, a correct body whose
//! in-bounds fact the region does not hold.

use super::*;
use trust_cg_lower::instructions::Instruction;

/// The most candidate offsets one indexed access may have, and the most all
/// the indexed accesses of one source have together (each a named refusal;
/// host qualification sets them, as OD-72 set the row bound). Slice 20
/// (ruling OD-194) raised them from 256 and 1024 (slice 17) to 1024 and
/// 4096: `dec2flt::parse_decimal_seq` stores through 784 candidate offsets
/// of `Decimal`'s digit array.
pub(super) const MAX_CANDIDATES: usize = 1024;
pub(super) const MAX_SOURCE_CANDIDATES: usize = 4096;

/// The largest alignment modulus the walks state (a stride a multiple of a
/// larger power of two states this one, a weaker and still exact claim).
const MAX_MODULUS: u64 = 1 << 32;

/// A private stack address at a non-constant offset (slice 17): slot `slot`
/// plus the constant `base` plus the value `delta` (an `I64` of the chain)
/// times `stride` (1 for an `Iadd`; an `ArrayGep`'s element size, OD-185),
/// wrapping. `modulus` is the alignment modulus read from `delta`'s
/// definition and the stride ([`modulus_of`], [`stride_modulus`]), a power
/// of two.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct IndexedAddr {
    pub(super) slot: u32,
    pub(super) base: i64,
    pub(super) delta: Value,
    pub(super) stride: u64,
    pub(super) modulus: u64,
}

impl IndexedAddr {
    /// The same address plus a constant.
    pub(super) fn offset_by(self, delta: i64) -> Option<Self> {
        Some(Self {
            base: self.base.checked_add(delta)?,
            ..self
        })
    }

    /// The offset's residue modulo the alignment modulus: the base's.
    pub(super) fn residue(self) -> u64 {
        residue(self.base, self.modulus)
    }

    /// The 64-bit offset term, `delta` being `variable`: the product
    /// `variable * stride` plus `base`, wrapping ([`array_element_offset`]
    /// spells the product, as the machine's scaled index does;
    /// [`offset_term`] adds the base).
    pub(super) fn offset(self, variable: E) -> E {
        let scaled = if matches!(self.stride, 3 | 5 | 9) {
            // OD-185's spelling of these strides: `v * (s - 1) + v`, the
            // selector's `lea; add`.
            array_element_offset(variable.clone(), self.stride - 1).bvadd(variable)
        } else {
            array_element_offset(variable, self.stride)
        };
        offset_term(self.base, scaled)
    }

    pub(super) fn describe(self) -> String {
        match self.stride {
            1 => format!(
                "private stack slot {} + {} + {:?} (indexed)",
                self.slot, self.base, self.delta
            ),
            stride => format!(
                "private stack slot {} + {} + {:?} * {stride} (indexed)",
                self.slot, self.base, self.delta
            ),
        }
    }
}

/// The alignment modulus of an `ArrayGep`'s indexed offset `index * stride`
/// (slice 17): the index's own modulus ([`modulus_of`]) times the largest
/// power of two dividing the stride, at most [`MAX_MODULUS`] (a smaller power
/// of two is a weaker, still exact claim).
pub(super) fn stride_modulus(stride: u64, index_modulus: u64) -> u64 {
    let product = u128::from(index_modulus) << stride.trailing_zeros().min(63);
    u64::try_from(product.min(u128::from(MAX_MODULUS))).unwrap_or(MAX_MODULUS)
}

/// `base mod modulus`, the canonical residue in `0..modulus`.
pub(super) fn residue(base: i64, modulus: u64) -> u64 {
    (base as u64) & (modulus - 1)
}

/// The candidate offsets of an indexed access of `width` bytes into a slot
/// of `size` bytes ([`IndexedAddr`]): every `k` in `0..=size - width` with `k
/// mod modulus = residue`, ascending. Empty when the access does not fit.
pub(super) fn candidates(size: u32, width: u32, modulus: u64, residue: u64) -> Vec<i64> {
    debug_assert!(modulus.is_power_of_two() && residue < modulus);
    let Some(last) = size.checked_sub(width) else {
        return Vec::new();
    };
    (0..=u64::from(last))
        .filter(|k| k & (modulus - 1) == residue)
        .map(|k| k as i64)
        .collect()
}

/// The 64-bit offset term of an indexed address: `variable` plus the
/// constant `base`, wrapping (the variable part alone when `base` is 0).
/// Both walks spell an offset so.
pub(super) fn offset_term(base: i64, variable: E) -> E {
    match base {
        0 => variable,
        base => variable.bvadd(E::bv_const(base as u64, 64)),
    }
}

/// The in-bounds claim of an access of `width` bytes at offset term `offset`
/// into a slot of `size` bytes: the offset is one of the [`candidates`].
/// `(bvule o (size - width))`, and `(= (bvand o (modulus - 1)) residue)` when
/// `modulus > 1`.
pub(super) fn in_bounds(offset: E, size: u32, width: u32, modulus: u64, residue: u64) -> E {
    // No offset fits an access wider than its slot (admission refuses one).
    let Some(last) = size.checked_sub(width).map(u64::from) else {
        return E::bool_const(false);
    };
    let within = offset.clone().bvule(E::bv_const(last, 64));
    if modulus == 1 {
        within
    } else {
        within.and_expr(
            offset
                .bvand(E::bv_const(modulus - 1, 64))
                .eq_expr(E::bv_const(residue, 64)),
        )
    }
}

/// The observed item of an indexed call argument (and of a frame address
/// passed where the source passes an indexed one): the slot's address input
/// `slot{s}` plus the offset term, wrapping. Equal on the two sides exactly
/// when the offsets are.
pub(super) fn argument_term(slot: u32, offset: E) -> E {
    E::var(slot_address_name(slot), 64).bvadd(offset)
}

/// The value an indexed load reads, over the candidates' reads `arms`
/// (ascending: `k_i = r + i * 2^s`, `r < 2^s`, as [`candidates`] gives them):
/// the LOW-BIT select, a balanced tree that tests bit `s + j` of `o` at depth
/// `d - 1 - j` (`d` the bits of `N - 1`): `(ite (= ((_ extract b b) o) #b1)
/// UPPER LOWER)`. Where `o` is a candidate `k_i`, bits `s..s + d` of `o` are
/// `i` (`r < 2^s` carries nothing into them), so the tree reads `B_i`; a
/// subtree past the last candidate is never tested. Host qualification chose
/// it over the linear chain `(ite (= o k1) B1 (ite ... BN))`: AY build 12713
/// certifies a 256-arm table lookup in this form and rejects the chain's
/// proof (an unverified trust rule); see the slice-17 record. Arms that are
/// not such a progression (never produced) keep the chain.
pub(super) fn select(offset: &E, arms: Vec<(i64, E)>) -> E {
    let progression = arms.len() >= 2 && {
        let step = arms[1].0 - arms[0].0;
        step > 0
            && step.count_ones() == 1
            && arms[0].0 >= 0
            && arms[0].0 < step
            && arms
                .iter()
                .enumerate()
                .all(|(i, (k, _))| *k == arms[0].0 + i as i64 * step)
    };
    if !progression {
        let mut arms = arms.into_iter().rev();
        let (_, mut chosen) = arms.next().expect("an indexed access has a candidate");
        for (k, term) in arms {
            chosen = E::ite(
                offset.clone().eq_expr(E::bv_const(k as u64, 64)),
                term,
                chosen,
            );
        }
        return chosen;
    }
    let shift = (arms[1].0 - arms[0].0).trailing_zeros();
    let values: Vec<E> = arms.into_iter().map(|(_, term)| term).collect();
    let depth = usize::BITS - (values.len() - 1).leading_zeros();
    // The arms whose index agrees with `low` below bit `bit + 1`, by the
    // index bits `bit..=0` (`low` the index bits above them, already
    // chosen).
    fn tree(offset: &E, values: &[E], shift: u32, low: usize, bit: Option<u32>) -> E {
        let Some(bit) = bit else {
            return values[low].clone();
        };
        let next = bit.checked_sub(1);
        let upper = low + (1usize << bit);
        if upper >= values.len() {
            return tree(offset, values, shift, low, next);
        }
        let position = shift + bit;
        E::ite(
            offset
                .clone()
                .extract(position, position)
                .eq_expr(E::bv_const(1, 1)),
            tree(offset, values, shift, upper, next),
            tree(offset, values, shift, low, next),
        )
    }
    tree(offset, &values, shift, 0, depth.checked_sub(1))
}

/// The candidates of an access of `width` bytes that cover byte `position`
/// (`k <= position < k + width`), ascending, with the index of that byte in
/// the access (`position - k`).
pub(super) fn covering(candidates: &[i64], width: u32, position: i64) -> Vec<(i64, u32)> {
    candidates
        .iter()
        .filter(|k| **k <= position && position < **k + i64::from(width))
        .map(|k| (*k, (position - *k) as u32))
        .collect()
}

/// The byte an indexed store leaves at a position: `(ite (= o k) new_k (ite
/// ... old))` over the candidates that cover it (`arms`, ascending, each
/// with the stored value's byte there).
pub(super) fn update(offset: &E, arms: Vec<(i64, E)>, old: E) -> E {
    let mut chosen = old;
    for (k, byte) in arms.into_iter().rev() {
        chosen = E::ite(
            offset.clone().eq_expr(E::bv_const(k as u64, 64)),
            byte,
            chosen,
        );
    }
    chosen
}

/// The alignment modulus of an indexed address whose variable part is
/// `delta`: `2^j`, `j` the trailing zeros of the constant multiplier when
/// `delta` is (through `Copy` and same-carrier `Bitcast`) an `Imul` by a
/// constant of the chain or an `Ishl` by one; else 1. Read from the source's
/// own definition and stated in the claim, so a wrong modulus refutes.
pub(super) fn modulus_of(source: &Function, delta: Value, constants: &HashMap<Value, u64>) -> u64 {
    let mut value = delta;
    for _ in 0..64 {
        let Some(inst) = defining_instruction(source, value) else {
            return 1;
        };
        match &inst.opcode {
            L::Copy => value = inst.args[0],
            L::Bitcast { to_ty } if *to_ty == Type::I64 => value = inst.args[0],
            L::Imul => {
                let multiplier = inst.args.iter().find_map(|arg| constants.get(arg).copied());
                return match multiplier {
                    Some(0) | None => 1,
                    Some(k) => (1u64 << k.trailing_zeros().min(63)).min(MAX_MODULUS),
                };
            }
            L::Ishl => {
                return match constants.get(&inst.args[1]) {
                    Some(amount) if *amount < 64 => (1u64 << *amount).min(MAX_MODULUS),
                    _ => 1,
                };
            }
            _ => return 1,
        }
    }
    1
}

/// The one instruction that defines `value` in `source`, if exactly one does.
pub(super) fn defining_instruction(source: &Function, value: Value) -> Option<&Instruction> {
    let mut found = None;
    for block in source.blocks.values() {
        for inst in &block.instructions {
            if inst.results.contains(&value) {
                if found.is_some() {
                    return None;
                }
                found = Some(inst);
            }
        }
    }
    found
}

/// The free name of the `id`-th byte an indexed store writes (slice 17;
/// [`IndexedByte`]): its [`update`], defined where the store runs.
pub(super) fn indexed_byte_name(id: usize) -> String {
    format!("ix{id}")
}

/// One indexed access or argument of the admitted source (slice 17), which
/// the theorem claims in bounds, the bound finder checks, and the machine
/// walk sizes its own select by (the row's TV-1 stamp names it).
#[derive(Debug, Clone)]
pub(super) struct IndexedSite {
    pub(super) address: IndexedAddr,
    /// The access's width in bytes; 0 for a call argument (a pointer into
    /// the slot or one past its end).
    pub(super) width: u32,
    /// The slot's size in bytes.
    pub(super) size: u32,
    /// How many of the program's stops precede it (its claim is stated where
    /// the source has not stopped by then).
    pub(super) stops: usize,
    pub(super) block: Block,
    pub(super) index: usize,
}

impl IndexedSite {
    pub(super) fn candidates(&self) -> Vec<i64> {
        candidates(
            self.size,
            self.width,
            self.address.modulus,
            self.address.residue(),
        )
    }
}

/// One byte an indexed store writes (slice 17): at `address`, the [`update`]
/// of the old byte by `value`'s byte at each covering candidate (`arms`:
/// the candidate and the index of the byte of `value` it stores there).
#[derive(Debug, Clone)]
pub(super) struct IndexedByte {
    pub(super) address: FrameAddr,
    pub(super) store: IndexedAddr,
    pub(super) value: Value,
    pub(super) carrier: Carrier,
    pub(super) arms: Vec<(i64, u32)>,
    pub(super) old: Option<SlotByte>,
}

impl IndexedByte {
    /// The byte's term: the [`update`] of the old byte's term by the stored
    /// value's bytes, with `value` the store's terms.
    pub(super) fn term(&self, value: &dyn Fn(&Value) -> E, walks: &BodyWalks) -> E {
        let offset = self.store.offset(value(&self.store.delta));
        let stored = self.carrier.memory_value(value(&self.value));
        let width = self.carrier.bytes();
        let arms = self
            .arms
            .iter()
            .map(|(k, byte)| {
                let term = if width == 1 {
                    stored.clone()
                } else {
                    stored.clone().extract(8 * byte + 7, 8 * byte)
                };
                (*k, term)
            })
            .collect();
        let old = source_slot_byte(self.address, &self.old, value, walks);
        update(&offset, arms, old)
    }
}

// ---------------------------------------------------------------------------
// The bound finder (admission only)
// ---------------------------------------------------------------------------

/// One region of the source as the bound finder sees it: its blocks in
/// topological order (the start first), each block's predecessors inside
/// it, and each block's successors.
pub(super) struct RegionView<'a> {
    pub(super) order: &'a [Block],
    pub(super) predecessors: &'a HashMap<Block, Vec<Block>>,
    pub(super) successors: &'a HashMap<Block, Vec<Block>>,
}

/// The values the LIR defines exactly once by an `Iconst` of at most 64 bits
/// (through copies), with their bits.
fn lir_constants(source: &Function) -> HashMap<Value, u64> {
    let mut constants: HashMap<Value, u64> = HashMap::new();
    let mut copies: Vec<(Value, Value)> = Vec::new();
    for block in source.blocks.values() {
        for inst in &block.instructions {
            match (&inst.opcode, inst.results.as_slice()) {
                (L::Iconst { ty, imm }, [result]) if *ty != Type::I128 => {
                    if let Some(carrier) = Carrier::of(ty) {
                        constants.insert(*result, (*imm as u64) & carrier.mask());
                    }
                }
                (L::Copy | L::Bitcast { .. }, [result]) => copies.push((*result, inst.args[0])),
                _ => {}
            }
        }
    }
    for _ in 0..copies.len().min(64) {
        let mut grown = false;
        for (result, from) in &copies {
            if !constants.contains_key(result)
                && let Some(bits) = constants.get(from).copied()
            {
                constants.insert(*result, bits);
                grown = true;
            }
        }
        if !grown {
            break;
        }
    }
    // A value defined more than once (a block parameter) is no constant.
    let mut definitions: HashMap<Value, usize> = HashMap::new();
    for inst in source.blocks.values().flat_map(|block| &block.instructions) {
        for result in &inst.results {
            *definitions.entry(*result).or_default() += 1;
        }
    }
    constants.retain(|value, _| definitions.get(value) == Some(&1));
    constants
}

/// What an index is: `delta` through `Copy`/`Bitcast` (the root), and the
/// constant stride it is multiplied by (`Imul` by a constant, `Ishl` by one).
struct IndexChain {
    root: Value,
    stride: u64,
}

/// Follow `value` through `Copy` and `Bitcast` to the value it is.
fn canonical(source: &Function, mut value: Value) -> Value {
    for _ in 0..64 {
        match defining_instruction(source, value) {
            Some(inst) if matches!(inst.opcode, L::Copy | L::Bitcast { .. }) => {
                value = inst.args[0];
            }
            _ => return value,
        }
    }
    value
}

fn index_chain(source: &Function, delta: Value, constants: &HashMap<Value, u64>) -> IndexChain {
    let value = canonical(source, delta);
    if let Some(inst) = defining_instruction(source, value) {
        match &inst.opcode {
            L::Imul => {
                for (k, arg) in inst.args.iter().enumerate() {
                    if let Some(stride) = constants.get(arg) {
                        return IndexChain {
                            root: canonical(source, inst.args[1 - k]),
                            stride: *stride,
                        };
                    }
                }
            }
            L::Ishl => {
                if let Some(amount) = constants.get(&inst.args[1]).filter(|amount| **amount < 64) {
                    return IndexChain {
                        root: canonical(source, inst.args[0]),
                        stride: 1u64 << amount,
                    };
                }
            }
            _ => {}
        }
    }
    IndexChain {
        root: value,
        stride: 1,
    }
}

/// The largest value of `value` (unsigned) its own definition implies: a
/// constant, a narrow extension, a truncation, a mask, a logical shift right
/// or a remainder by a constant, a narrow load; `None` when nothing bounds it.
fn own_range(
    source: &Function,
    value: Value,
    constants: &HashMap<Value, u64>,
    types: &HashMap<Value, Carrier>,
    depth: u32,
) -> Option<u64> {
    if let Some(bits) = constants.get(&value) {
        return Some(*bits);
    }
    // A value's carrier bounds it.
    let carrier_max = types
        .get(&value)
        .map(|carrier| carrier.mask())
        .unwrap_or(u64::MAX);
    if depth > 12 {
        return (carrier_max < u64::MAX).then_some(carrier_max);
    }
    let width_max = |ty: &Type| Carrier::of(ty).filter(|c| c.bits() < 64).map(|c| c.mask());
    let inner = |value: Value| own_range(source, value, constants, types, depth + 1);
    let found = defining_instruction(source, value).and_then(|inst| match &inst.opcode {
        L::Copy | L::Bitcast { .. } => inner(inst.args[0]),
        L::Uextend { from_ty, .. } => {
            let full = width_max(from_ty)?;
            Some(inner(inst.args[0]).map_or(full, |range| range.min(full)))
        }
        L::Trunc { to_ty } => width_max(to_ty),
        L::Band => inst
            .args
            .iter()
            .filter_map(|arg| constants.get(arg))
            .copied()
            .min()
            .or_else(|| inst.args.iter().filter_map(|arg| inner(*arg)).min()),
        L::Ushr => {
            let amount = *constants.get(&inst.args[1])?;
            let operand = inner(inst.args[0]).unwrap_or(u64::MAX);
            Some(operand.checked_shr(amount as u32).unwrap_or(0))
        }
        L::Urem => constants
            .get(&inst.args[1])
            .filter(|k| **k > 0)
            .map(|k| k - 1),
        L::Load { ty, .. } => width_max(ty),
        _ => None,
    });
    match found {
        Some(range) => Some(range.min(carrier_max)),
        None => (carrier_max < u64::MAX).then_some(carrier_max),
    }
}

/// Slice 20 (ruling OD-194): the bound below 128 that the amount of a
/// variable `I128` shift has by its own definition, if any: followed through
/// `Copy`, `Bitcast` and `Uextend` to a value of at most 64 bits whose own
/// range ([`own_range`]: a constant, a mask, a narrow extension, a logical
/// shift right, a remainder by a constant) is below 128 (`u128::
/// unchecked_shl`'s `and u32 n, 127`, then `zext` to `u128`). Admission only:
/// the theorem states the shift modulo 128, so a wrong bound is refuted,
/// never credited.
pub(super) fn shift_amount_bound(
    source: &Function,
    amount: Value,
    types: &HashMap<Value, Carrier>,
) -> Option<u64> {
    let mut value = amount;
    for _ in 0..64 {
        if types
            .get(&value)
            .is_some_and(|carrier| carrier.bits() <= 64)
        {
            return own_range(source, value, &lir_constants(source), types, 0)
                .filter(|bound| *bound < 128);
        }
        let inst = defining_instruction(source, value)?;
        match inst.opcode {
            L::Copy | L::Bitcast { .. } | L::Uextend { .. } => value = inst.args[0],
            _ => return None,
        }
    }
    None
}

/// The values `root` equals, as a compare may name it: itself (through
/// copies), and the operand of a zero extension it is.
fn index_names(source: &Function, root: Value) -> HashSet<Value> {
    let mut names = HashSet::from([root]);
    if let Some(inst) = defining_instruction(source, root)
        && matches!(inst.opcode, L::Uextend { .. })
    {
        names.insert(canonical(source, inst.args[0]));
    }
    names
}

/// The dominators of each block of a region (over its in-region edges).
fn dominators(region: &RegionView<'_>) -> HashMap<Block, HashSet<Block>> {
    let mut dominators: HashMap<Block, HashSet<Block>> = HashMap::new();
    for block in region.order {
        let predecessors = &region.predecessors[block];
        let mut set: Option<HashSet<Block>> = None;
        for predecessor in predecessors {
            let Some(known) = dominators.get(predecessor) else {
                continue;
            };
            set = Some(match set {
                None => known.clone(),
                Some(set) => set.intersection(known).copied().collect(),
            });
        }
        let mut set = set.unwrap_or_default();
        set.insert(*block);
        dominators.insert(*block, set);
    }
    dominators
}

/// The largest index value a guard edge of `region` implies at a use in
/// `block`: an edge `g -> s` (`s` dominates `block` in the region, `g` its
/// only in-region predecessor) of a `Brif` on an unsigned or equality
/// `Icmp` of one of `names` against a constant. Returns the tightest bound
/// and its edge.
fn guard_bound(
    source: &Function,
    region: &RegionView<'_>,
    dominators: &HashMap<Block, HashSet<Block>>,
    block: Block,
    names: &HashSet<Value>,
    constants: &HashMap<Value, u64>,
) -> Option<(u64, (Block, Block))> {
    let dominating = dominators.get(&block)?;
    let mut best: Option<(u64, (Block, Block))> = None;
    for guard in region.order {
        let Some(last) = source.blocks[guard].instructions.last() else {
            continue;
        };
        let L::Brif {
            then_dest,
            else_dest,
            ..
        } = &last.opcode
        else {
            continue;
        };
        let mut test = canonical(source, last.args[0]);
        let compare = loop {
            match defining_instruction(source, test) {
                Some(inst) if matches!(inst.opcode, L::Copy) => test = inst.args[0],
                other => break other,
            }
        };
        let Some(compare) = compare else {
            continue;
        };
        let L::Icmp { cond } = &compare.opcode else {
            continue;
        };
        let (x, y) = (compare.args[0], compare.args[1]);
        for (successor, taken) in [(*then_dest, true), (*else_dest, false)] {
            if !dominating.contains(&successor)
                || region.predecessors.get(&successor).map(Vec::as_slice) != Some(&[*guard])
            {
                continue;
            }
            // `index op C` (or `C op index`) holds on the `then` edge and
            // fails on the `else` edge.
            let bound = if names.contains(&canonical(source, x)) {
                constants.get(&y).and_then(|c| match (cond, taken) {
                    (IntCC::UnsignedLessThan, true)
                    | (IntCC::UnsignedGreaterThanOrEqual, false) => c.checked_sub(1),
                    (IntCC::UnsignedLessThanOrEqual, true)
                    | (IntCC::UnsignedGreaterThan, false)
                    | (IntCC::Equal, true) => Some(*c),
                    _ => None,
                })
            } else if names.contains(&canonical(source, y)) {
                constants.get(&x).and_then(|c| match (cond, taken) {
                    (IntCC::UnsignedGreaterThan, true)
                    | (IntCC::UnsignedLessThanOrEqual, false) => c.checked_sub(1),
                    (IntCC::UnsignedGreaterThanOrEqual, true)
                    | (IntCC::UnsignedLessThan, false)
                    | (IntCC::Equal, true) => Some(*c),
                    _ => None,
                })
            } else {
                None
            };
            if let Some(bound) = bound
                && best.is_none_or(|(known, _)| bound < known)
            {
                best = Some((bound, (*guard, successor)));
            }
        }
    }
    best
}

/// How an indexed use is bounded in one region: by a guard edge, or by the
/// index's own range.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Bound {
    Guard { guard: Block, successor: Block },
    Range,
}

/// The bound of an indexed use at `block` of `address` (`width` bytes into
/// `size`) in `region`, or `None` when the region holds none that keeps
/// every offset the index may take there a candidate.
#[allow(clippy::too_many_arguments)]
fn use_bound(
    source: &Function,
    region: &RegionView<'_>,
    dominators: &HashMap<Block, HashSet<Block>>,
    constants: &HashMap<Value, u64>,
    types: &HashMap<Value, Carrier>,
    block: Block,
    address: IndexedAddr,
    width: u32,
    size: u32,
) -> Option<Bound> {
    let chain = index_chain(source, address.delta, constants);
    // The address's own stride (an `ArrayGep`'s element size) times the
    // index's.
    let fits = |largest: u64| {
        let base = i128::from(address.base);
        let step = i128::from(chain.stride) * i128::from(address.stride);
        let end = i128::from(largest)
            .checked_mul(step)
            .and_then(|span| span.checked_add(base))
            .and_then(|end| end.checked_add(i128::from(width)));
        base >= 0 && end.is_some_and(|end| end <= i128::from(size))
    };
    let names = index_names(source, chain.root);
    if let Some((largest, (guard, successor))) =
        guard_bound(source, region, dominators, block, &names, constants)
        && fits(largest)
    {
        return Some(Bound::Guard { guard, successor });
    }
    own_range(source, chain.root, constants, types, 0)
        .filter(|largest| fits(*largest))
        .map(|_| Bound::Range)
}

/// Every indexed use of the admitted units (`programs`) must be bounded in
/// every region of `regions` that contains its block ([`use_bound`]), else
/// [`X86BodyUnsupported::SourceDomain`] naming it (IndexedUnbounded). Returns
/// the guard edge each guarded use relies on, by region start (the slice-16
/// planner keeps them uncut).
pub(super) fn check_bounds(
    source: &Function,
    regions: &[(Block, RegionView<'_>)],
    programs: &[&SourceProgram],
) -> Result<(), (Option<Block>, X86BodyRefusal)> {
    if programs.iter().all(|program| program.indexed.is_empty()) {
        return Ok(());
    }
    let constants = lir_constants(source);
    // Every value's carrier, as the admitted units give it.
    let types: HashMap<Value, Carrier> = programs
        .iter()
        .flat_map(|program| {
            program
                .types
                .iter()
                .map(|(value, carrier)| (*value, *carrier))
        })
        .collect();
    let mut checked: HashSet<(Block, usize, u32)> = HashSet::new();
    for (start, region) in regions {
        let dominators = dominators(region);
        for program in programs {
            for site in &program.indexed {
                if !region.predecessors.contains_key(&site.block)
                    || !checked.insert((site.block, site.index, start.0))
                {
                    continue;
                }
                let bound = use_bound(
                    source,
                    region,
                    &dominators,
                    &constants,
                    &types,
                    site.block,
                    site.address,
                    site.width,
                    site.size,
                );
                if bound.is_none() {
                    return Err((
                        Some(*start),
                        unsupported(X86BodyUnsupported::SourceDomain(format!(
                            "IndexedUnbounded: instruction {} of block {:?} accesses {} with no \
                             bound in the region of {start:?} (a dominating guard or the index's \
                             own range) that keeps its offset a candidate",
                            site.index,
                            site.block,
                            site.address.describe()
                        ))),
                    ));
                }
            }
        }
    }
    Ok(())
}

/// The program points a slice-16 plan must not cut at (slice 17): for each
/// indexed use of the LIR that a guard bounds in its slice-12 region, every
/// block start from the guard's successor up to the use's block, and every
/// point inside those blocks before the use (a cut there would forget the
/// guard's condition, and the part's in-bounds claim would be refuted on a
/// correct body). Found from the LIR alone ([`scan_uses`]).
pub(super) fn guard_spans(
    source: &Function,
    cfg: &SourceCfg,
) -> std::collections::BTreeSet<(Block, usize)> {
    let mut banned = std::collections::BTreeSet::new();
    let uses = scan_uses(source);
    if uses.is_empty() {
        return banned;
    }
    let constants = lir_constants(source);
    for region in source_regions(cfg) {
        let view = RegionView {
            order: &region.order,
            predecessors: &region.predecessors,
            successors: &region.successors,
        };
        let dominators = dominators(&view);
        for (block, index, address, width, size) in &uses {
            if !region.predecessors.contains_key(block) {
                continue;
            }
            let Some(Bound::Guard { successor, .. }) = use_bound(
                source,
                &view,
                &dominators,
                &constants,
                &HashMap::new(),
                *block,
                *address,
                *width,
                *size,
            ) else {
                continue;
            };
            // The blocks from the guard's successor that reach the use.
            let mut span: HashSet<Block> = HashSet::new();
            for candidate in &region.order {
                if dominators[candidate].contains(&successor) && reaches(&view, *candidate, *block)
                {
                    span.insert(*candidate);
                }
            }
            for member in span {
                let end = if member == *block {
                    *index
                } else {
                    source.blocks[&member].instructions.len()
                };
                for point in 0..=end {
                    banned.insert((member, point));
                }
            }
        }
    }
    banned
}

/// Whether `to` is reachable from `from` inside a region (in-region edges).
fn reaches(region: &RegionView<'_>, from: Block, to: Block) -> bool {
    let mut seen = HashSet::from([from]);
    let mut work = vec![from];
    while let Some(block) = work.pop() {
        if block == to {
            return true;
        }
        for target in &region.successors[&block] {
            if region.predecessors.contains_key(target)
                && region.predecessors[target].contains(&block)
                && seen.insert(*target)
            {
                work.push(*target);
            }
        }
    }
    false
}

/// The indexed uses of the LIR, flow-insensitively (for the slice-16 planner
/// only): `(block, index, address, width, slot size)` of every load, store
/// or direct call argument through an indexed address of a `StackAddr` slot.
fn scan_uses(source: &Function) -> Vec<(Block, usize, IndexedAddr, u32, u32)> {
    let constants = lir_constants(source);
    let sizes: Vec<u32> = source.stack_slots.iter().map(|slot| slot.size).collect();
    let mut frame: HashMap<Value, (u32, i64)> = HashMap::new();
    let mut indexed: HashMap<Value, IndexedAddr> = HashMap::new();
    let mut blocks: Vec<&Block> = source.blocks.keys().collect();
    blocks.sort();
    for _ in 0..8 {
        let mut grown = false;
        for block in &blocks {
            for inst in &source.blocks[block].instructions {
                let [result] = inst.results.as_slice() else {
                    continue;
                };
                if frame.contains_key(result) || indexed.contains_key(result) {
                    continue;
                }
                match &inst.opcode {
                    L::StackAddr { slot } => {
                        frame.insert(*result, (*slot, 0));
                        grown = true;
                    }
                    L::Copy | L::Bitcast { .. } => {
                        if let Some(address) = frame.get(&inst.args[0]).copied() {
                            frame.insert(*result, address);
                            grown = true;
                        } else if let Some(address) = indexed.get(&inst.args[0]).copied() {
                            indexed.insert(*result, address);
                            grown = true;
                        }
                    }
                    L::StructGep {
                        struct_ty,
                        field_index,
                    } => {
                        let Some(offset) = field_offset(struct_ty, *field_index) else {
                            continue;
                        };
                        if let Some((slot, base)) = frame.get(&inst.args[0]).copied() {
                            frame.insert(*result, (slot, base + offset as i64));
                            grown = true;
                        } else if let Some(address) = indexed.get(&inst.args[0]).copied()
                            && let Some(address) = address.offset_by(offset as i64)
                        {
                            indexed.insert(*result, address);
                            grown = true;
                        }
                    }
                    L::Iadd => {
                        let (a, b) = (inst.args[0], inst.args[1]);
                        let (base, other) = if frame.contains_key(&a) || indexed.contains_key(&a) {
                            (a, b)
                        } else {
                            (b, a)
                        };
                        match (frame.get(&base), indexed.get(&base), constants.get(&other)) {
                            (Some((slot, offset)), _, Some(k)) => {
                                frame.insert(*result, (*slot, offset + *k as i64));
                            }
                            (Some((slot, offset)), _, None) => {
                                indexed.insert(
                                    *result,
                                    IndexedAddr {
                                        slot: *slot,
                                        base: *offset,
                                        delta: other,
                                        stride: 1,
                                        modulus: modulus_of(source, other, &constants),
                                    },
                                );
                            }
                            (None, Some(address), Some(k)) => {
                                if let Some(address) = address.offset_by(*k as i64) {
                                    indexed.insert(*result, address);
                                }
                            }
                            _ => continue,
                        }
                        grown = true;
                    }
                    // OD-185 and slice 17: an array element of a private
                    // address, as `admit_blocks` reads it.
                    L::ArrayGep { elem_ty } => {
                        let (base, index) = (inst.args[0], inst.args[1]);
                        let Some(stride) = array_element_stride(elem_ty)
                            .and_then(|stride| i64::try_from(stride).ok())
                        else {
                            continue;
                        };
                        let element = constants
                            .get(&index)
                            .and_then(|k| (*k as i64).checked_mul(stride));
                        match (frame.get(&base), indexed.get(&base), constants.get(&index)) {
                            (Some((slot, offset)), _, Some(_)) => {
                                let Some(offset) = element.and_then(|e| offset.checked_add(e))
                                else {
                                    continue;
                                };
                                frame.insert(*result, (*slot, offset));
                            }
                            (Some((slot, offset)), _, None) => {
                                indexed.insert(
                                    *result,
                                    IndexedAddr {
                                        slot: *slot,
                                        base: *offset,
                                        delta: index,
                                        stride: stride as u64,
                                        modulus: stride_modulus(
                                            stride as u64,
                                            modulus_of(source, index, &constants),
                                        ),
                                    },
                                );
                            }
                            (None, Some(address), Some(_)) => {
                                let Some(address) = element.and_then(|e| address.offset_by(e))
                                else {
                                    continue;
                                };
                                indexed.insert(*result, address);
                            }
                            _ => continue,
                        }
                        grown = true;
                    }
                    _ => {}
                }
            }
        }
        if !grown {
            break;
        }
    }
    let mut uses = Vec::new();
    for block in blocks {
        for (index, inst) in source.blocks[block].instructions.iter().enumerate() {
            let (address, width) = match &inst.opcode {
                L::Load { ty, .. } => (inst.args[0], Carrier::of(ty).map(Carrier::bytes)),
                L::Store { ty, .. } => (inst.args[1], Carrier::of(ty).map(Carrier::bytes)),
                L::Call { .. } => {
                    for arg in &inst.args {
                        if let Some(address) = indexed.get(arg)
                            && let Some(size) = sizes.get(address.slot as usize)
                        {
                            uses.push((*block, index, *address, 0, *size));
                        }
                    }
                    continue;
                }
                _ => continue,
            };
            if let (Some(address), Some(width)) = (indexed.get(&address), width)
                && let Some(size) = sizes.get(address.slot as usize)
            {
                uses.push((*block, index, *address, width, *size));
            }
        }
    }
    uses
}
