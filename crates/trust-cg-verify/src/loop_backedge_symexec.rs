// trust-cg-verify/loop_backedge_symexec.rs - trust-ir loop back-edge symbolic model
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Proof-gap item #84 (the euclid / #71 loop-threading class), IMPLEMENTATION
// side. `ssa_loop_complete`'s sub-check (2) (`LoopCarriedSlotMisthreaded`) is a
// STRUCTURAL judgment over the lowered trust-ir: it fires when a loop header's
// back-edge argument provably derives from a DIFFERENT header slot. That
// judgment cannot distinguish a legitimate ROTATION
// (`while b != 0 { let t = b; b = a % b; a = t; }` — new `a` IS old `b`) from a
// buggy SWAP, because the two are structurally identical. The sound resolution
// is SEMANTIC: when the structural check fires, prove (via SMT) that the VALUE
// the produced trust-ir actually threads to each header slot across the
// back-edge equals the MIR source program's dataflow for that slot — admit only
// on a full `Refined` verdict, fail closed otherwise.
//
// This module builds the IMPLEMENTATION side of that verification condition: a
// bounded symbolic execution of the produced trust-ir function along the unique
// in-loop path `header -> ... -> latch`, expressing the latch's back-edge
// block arguments as `SmtExpr`s over caller-named header-parameter variables.
// The caller (the rustc bridge) pairs these against the MIR-derived
// specification via `mir_semantics::check_back_edge_threading`.
//
// SOUNDNESS POSTURE (fail-closed by construction):
//   * The walk models bounded two-way diamonds, empty arms, conditional exits
//     with one continuing path, and supported tail diamonds. It REFUSES
//     nested branching arms/back-edges, ambiguous switches, unsupported latch
//     shapes and width mismatches. A conditional exit adds no VC assumption.
//   * An instruction whose semantics are not encoded (loads, calls, FP
//     arithmetic, overflow flags, GEPs, ...) binds its results to FRESH OPAQUE
//     input variables. An opaque variable can only make the equality VC HARDER
//     to prove (the solver may choose its value adversarially), so unmodeled
//     instructions can cause a false REFUTATION (fail closed) but never a false
//     admission.
//   * Division/remainder are encoded with the SAME total-function forms the MIR
//     spec encoder uses for the defined inputs (`l - (l div r) * r`); the
//     singular inputs (`r == 0`, `INT_MIN / -1`) differ from the MIR spec's
//     trap model and are expected to be EXCLUDED by the caller's source-derived
//     preconditions (the MIR `Assert` terminators guarding every Rust `/`/`%`).
//     If a caller fails to supply them the VC simply refutes — fail closed.
//   * Shifts are encoded only for in-range amounts (`amt < width`); the
//     out-of-range result is an opaque variable (trust-ir's lowering-defined
//     out-of-range shift behavior is deliberately NOT assumed here).

//! Bounded symbolic execution of a trust-ir loop's `header -> latch` path,
//! producing the back-edge block-argument values as [`SmtExpr`]s over named
//! header-parameter variables — the IMPLEMENTATION side of the loop-carried
//! block-arg threading VC (`mir_semantics::check_back_edge_threading`).

use std::collections::{HashMap, HashSet, VecDeque};

use crate::smt::SmtExpr;
use trust_ir::{
    BinOp, Block, BlockId, CastOp, Constant, FuncId, Function, ICmpOp, Inst, OverflowOp, Ty, UnOp,
    ValueId,
};

use crate::ssa_loop_complete::block_successors;

/// Result of modeling a back-edge: one `SmtExpr` per header-parameter slot (the
/// value the trust-ir latch actually threads to that slot), plus every OPAQUE
/// input variable the model minted (these must be declared as inputs of any
/// obligation the expressions appear in).
#[derive(Debug, Clone)]
pub struct BackEdgeModel {
    /// Back-edge argument values, in header-parameter slot order.
    pub args: Vec<SmtExpr>,
    /// Fresh symbolic inputs minted during the walk: the caller-supplied
    /// bindings (name, width) plus every opaque `__tir_*` variable.
    pub extra_inputs: Vec<(String, u32)>,
}

/// Symbolic value environment for the walk.
#[derive(Clone)]
struct Env {
    /// ValueId -> its symbolic value.
    vals: HashMap<ValueId, SmtExpr>,
    /// ValueIds produced by instructions we cannot even WIDTH-type. Resolving
    /// one of these is an error (fail closed), not an opaque.
    untyped: HashSet<ValueId>,
    /// In the unconditional all-paths model, a typed consumer may give an
    /// unknown producer a width. It remains a marked opaque, never a header
    /// input, and must disappear from every final expression. Other models
    /// retain their existing immediate refusal on an untyped operand.
    abstract_untyped: bool,
    /// Inputs minted (bindings + opaques), deduped by name.
    inputs: Vec<(String, u32)>,
    /// The module's type table, so a `TyId` inside an aggregate type (`Ty::Array(lane, n)`,
    /// the O(1) spelling of the `{ data, len }` lane tuple on newer trust-ir) can be
    /// resolved to a width. Empty when the caller has no module (unit tests through
    /// `model_back_edge_args`); an unresolvable id stays UNTYPED, exactly as before.
    types: Vec<Ty>,
    opaque_counter: u32,
    /// `FuncId`s of value-IDENTITY calls (`core::hint::black_box`): a `Call` to one
    /// is modeled as `result = arg` rather than left untyped, so a loop whose
    /// bound/inputs are black-boxed can be PROVEN. Restricted by the caller to the
    /// genuine std `black_box` (never a user fn) so this is sound.
    identity_calls: HashSet<FuncId>,
    /// Names of symbols minted because an instruction was NOT MODELED (`Load` /
    /// `AtomicLoad` / `AtomicRMW` / `Alloca` / `GEP` / `PtrData` / `GlobalAddr` /
    /// `NullPtr` / `Undef` / an unmodeled `Cast` / a wide-or-float `Const` / FP
    /// arithmetic / an out-of-range shift). It does NOT contain the
    /// caller-supplied bindings, and it does NOT contain the `__tir_v{id}` minted
    /// by [`Env::resolve`] for a value DEFINED OUTSIDE the walked path (that class
    /// is legitimately opaque and is already covered by the caller's
    /// header-slot / loop-invariant bindings).
    ///
    /// STAGE-0 FAIL-CLOSED GUARD: if a back-edge argument's expression mentions
    /// any of these, the walk returns `Err` instead of an expression the spec
    /// side can never match. Without this, WIDENING the modeled control flow
    /// (integer-discriminant diamonds, whose arms materialize `Option<iN>`
    /// through memory) would manufacture FALSE `REFUTED` verdicts — an operator
    /// reads a REFUTED as a miscompile, so an honest "out of model" `Err` is
    /// strictly better. The compile declines either way.
    unmodeled_opaques: HashSet<String>,
    /// Opaque names minted for an `Inst::Alloca` result. These are the only
    /// unmodeled opaques a forwarded store/load POINTER expression may mention:
    /// a stack slot the walk itself created is a KNOWN, non-escaping base, so
    /// two syntactically identical addresses over it denote the same location.
    alloca_opaques: HashSet<String>,
    /// Store-to-load forwarding window: `(pointer expr, width) -> stored value`.
    /// Keyed by STRUCTURAL `SmtExpr` equality. Deliberately tiny (at most one
    /// entry): a `Store` keeps only an entry at its own, syntactically identical
    /// pointer and width, so forwarding is confined to a same-pointer,
    /// no-intervening-store window inside ONE straight-line block chain.
    mem: Vec<(SmtExpr, u32, SmtExpr)>,
    /// Set once anything could have written memory unobservably (a non-identity
    /// call, an atomic, a fence, a volatile access, a heap allocation, a store
    /// through a pointer the walk did not itself construct). Never re-armed:
    /// all forwarding stops for the rest of the walk.
    mem_poisoned: bool,
}

impl Env {
    fn declare_input(&mut self, name: &str, width: u32) -> Result<(), String> {
        if let Some((_, w)) = self.inputs.iter().find(|(n, _)| n == name) {
            if *w != width {
                return Err(format!(
                    "symbolic input `{name}` declared at two widths ({w} vs {width})"
                ));
            }
            return Ok(());
        }
        self.inputs.push((name.to_string(), width));
        Ok(())
    }

    /// Mint a fresh opaque input of the given width. Every call site is an
    /// UNMODELED instruction, so the name is recorded in `unmodeled_opaques`
    /// (see that field's doc for why).
    fn fresh_opaque(&mut self, width: u32) -> Result<SmtExpr, String> {
        let name = format!("__tir_op{}", self.opaque_counter);
        self.opaque_counter += 1;
        self.declare_input(&name, width)?;
        self.unmodeled_opaques.insert(name.clone());
        Ok(SmtExpr::var(name, width))
    }

    /// Bind a ValueId to an opaque input of the given width. Every call site is
    /// an UNMODELED instruction (`resolve`'s outside-the-walk opaque mints its
    /// own name and is deliberately NOT recorded here).
    fn bind_opaque(&mut self, v: ValueId, width: u32) -> Result<(), String> {
        let name = format!("__tir_v{}", v.index());
        self.declare_input(&name, width)?;
        self.unmodeled_opaques.insert(name.clone());
        self.vals.insert(v, SmtExpr::var(name, width));
        Ok(())
    }

    /// The bit width a ValueId is ALREADY bound at, if any. Used where the
    /// instruction itself does not carry the operand type (`Inst::Switch` has no
    /// `ty` field): an unbound selector has no derivable width, so the caller
    /// fails closed rather than guessing one.
    fn bound_width(&self, v: ValueId) -> Option<u32> {
        if self.untyped.contains(&v) {
            return None;
        }
        self.vals.get(&v).and_then(|e| e.try_bv_width().ok())
    }

    /// Invalidate the whole store-to-load forwarding window and stop forwarding
    /// for the rest of the walk.
    fn poison_memory(&mut self) {
        self.mem.clear();
        self.mem_poisoned = true;
    }

    /// Drop the forwarding window WITHOUT poisoning (a control-flow join, where
    /// the two incoming memory states differ and merging them is out of model).
    fn clear_memory_window(&mut self) {
        self.mem.clear();
    }

    /// Every free variable of `e` that was minted for an UNMODELED instruction.
    fn unmodeled_free_vars(&self, e: &SmtExpr) -> Vec<String> {
        e.free_vars()
            .into_iter()
            .filter(|n| self.unmodeled_opaques.contains(n))
            .collect()
    }
    /// Resolve a ValueId at an EXPECTED width. A bound value must match the
    /// width exactly; an unbound value becomes a fresh opaque input (a value
    /// defined outside the walked path — sound: opacity can only cause a
    /// fail-closed refutation, never an admission).
    fn resolve(&mut self, v: ValueId, expected_width: u32) -> Result<SmtExpr, String> {
        if self.abstract_untyped && self.untyped.remove(&v) {
            self.bind_opaque(v, expected_width)?;
        }
        if self.untyped.contains(&v) {
            return Err(format!(
                "back-edge threading depends on value {v:?} produced by an \
                 unmodeled instruction with no width-typeable result"
            ));
        }
        if let Some(e) = self.vals.get(&v) {
            let w = e
                .try_bv_width()
                .map_err(|err| format!("value {v:?} has a non-bitvector sort: {err:?}"))?;
            if w != expected_width {
                return Err(format!(
                    "value {v:?} has width {w} but is used at width {expected_width}"
                ));
            }
            return Ok(e.clone());
        }
        let name = format!("__tir_v{}", v.index());
        self.declare_input(&name, expected_width)?;
        let e = SmtExpr::var(name, expected_width);
        self.vals.insert(v, e.clone());
        Ok(e)
    }

    /// Resolve a SHIFT AMOUNT and coerce it to the shifted-value width `value_w`.
    ///
    /// A Rust/trust-ir shift may be mixed-width — the MIR `Shl(_3: u64, 23_i32)`
    /// lowers to a trust-ir `Shl { ty: I64, rhs: <i32 const> }`, so the amount is
    /// bound here at its OWN (narrower/wider) width. `bvshl`/`bvlshr`/`bvashr`
    /// require both operands to share a sort, so we coerce the amount to
    /// `value_w`: ZERO-extend a narrower amount (a shift count is unsigned — never
    /// sign-extend), truncate a wider one to its low `value_w` bits.
    ///
    /// FAITHFUL: a well-defined shift has `amount < width(value)` (`>= width` is
    /// UB), so on every well-defined input the coerced count equals the original
    /// count, and the shift arm's `in_range` guard (evaluated on the COERCED
    /// amount) is the same predicate. UB is garbage-in, so the model need only be
    /// faithful for well-defined inputs. An UNBOUND amount is resolved directly at
    /// `value_w` (no bound width to disagree — identical to the prior behavior).
    fn resolve_shift_amount(&mut self, v: ValueId, value_w: u32) -> Result<SmtExpr, String> {
        if self.untyped.contains(&v) {
            return Err(format!(
                "back-edge threading depends on value {v:?} produced by an \
                 unmodeled instruction with no width-typeable result"
            ));
        }
        let Some(e) = self.vals.get(&v).cloned() else {
            // Unbound: resolve at the value width exactly as before.
            return self.resolve(v, value_w);
        };
        let w = e
            .try_bv_width()
            .map_err(|err| format!("value {v:?} has a non-bitvector sort: {err:?}"))?;
        Ok(match w.cmp(&value_w) {
            std::cmp::Ordering::Equal => e,
            std::cmp::Ordering::Less => e.zero_ext(value_w - w),
            std::cmp::Ordering::Greater => e.extract(value_w - 1, 0),
        })
    }
}

/// STAGE-0 GUARD: reject a back-edge model whose argument expressions depend on
/// a value the symbolic executor did not model (see [`Env::unmodeled_opaques`]).
///
/// An unmodeled opaque can only make the threading equality SAT, i.e. produce a
/// `Refuted` verdict that reads to an operator exactly like a miscompile when it
/// really means "out of model". Returning `Err` fails the compile closed with a
/// DIAGNOSABLE message instead. The compile declines either way — this only
/// changes WHICH decline the operator sees, and it is what makes it safe to
/// widen the modeled control flow (integer-discriminant diamonds, whose arms
/// materialize `Option<iN>` through memory).
fn reject_unmodeled_args(env: &Env, args: &[SmtExpr]) -> Result<(), String> {
    for (slot, a) in args.iter().enumerate() {
        if let Some(name) = env.unmodeled_free_vars(a).first() {
            return Err(format!(
                "back-edge arg for slot {slot} derives from an unmodeled trust-ir value \
                 (`{name}`) — out of model"
            ));
        }
    }
    Ok(())
}

/// A CONSERVATIVE upper bound on the unsigned value of `e`, when one is
/// syntactically evident. `None` means "no bound known" — callers must then
/// assume the full range.
///
/// Used only to recognize a shift amount that is PROVABLY in range, so the
/// shift model can drop its out-of-range `ite` (whose else-branch is an opaque)
/// instead of handing the solver an obligation it can never discharge. Rust's
/// `x.wrapping_shl(n & 15)` idiom — and rustc's own `& (width-1)` masking —
/// produce exactly the `bvand`-with-a-constant shape this recognizes.
///
/// Every arm must be an over-approximation:
///   * `x & m <= min(x, m)` for unsigned values, so a known bound on EITHER
///     operand bounds the `bvand`;
///   * zero-extension preserves the value;
///   * truncating to the low `hi+1` bits preserves a value that already FITS in
///     those bits (and is otherwise unknown);
///   * an `ite` is bounded by the larger of its branches.
fn smt_max_value_bound(e: &SmtExpr) -> Option<u64> {
    match e {
        SmtExpr::BvConst { value, width } => {
            if *width >= 64 {
                Some(*value)
            } else {
                Some(*value & ((1u64 << *width) - 1))
            }
        }
        SmtExpr::BvAnd { lhs, rhs, .. } => {
            match (smt_max_value_bound(lhs), smt_max_value_bound(rhs)) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (Some(a), None) | (None, Some(a)) => Some(a),
                (None, None) => None,
            }
        }
        SmtExpr::ZeroExtend { operand, .. } => smt_max_value_bound(operand),
        SmtExpr::Extract {
            high,
            low: 0,
            operand,
            ..
        } => {
            let b = smt_max_value_bound(operand)?;
            let w = *high + 1;
            if w >= 64 || b < (1u64 << w) {
                Some(b)
            } else {
                None
            }
        }
        SmtExpr::Ite {
            then_expr,
            else_expr,
            ..
        } => {
            let t = smt_max_value_bound(then_expr)?;
            let f = smt_max_value_bound(else_expr)?;
            Some(t.max(f))
        }
        _ => None,
    }
}

/// Bit width of a trust-ir type for this scalar model. Pointer-like values are
/// modeled as 64-bit opaques (they never receive arithmetic encodings here).
/// `None` for aggregate / unit / vector types — an instruction producing one is
/// "untyped" for this model.
fn ty_bit_width(ty: &Ty) -> Option<u32> {
    match ty {
        Ty::I8 | Ty::U8 => Some(8),
        Ty::I16 | Ty::U16 | Ty::F16 => Some(16),
        Ty::I32 | Ty::U32 | Ty::F32 => Some(32),
        Ty::I64 | Ty::U64 | Ty::F64 => Some(64),
        Ty::I128 | Ty::U128 => Some(128),
        Ty::Bool => Some(1),
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) | Ty::FatPtr(_) => {
            Some(64)
        }
        _ => None,
    }
}

fn block_of(func: &Function, id: BlockId) -> Result<&Block, String> {
    func.blocks
        .iter()
        .find(|b| b.id == id)
        .ok_or_else(|| format!("block {id:?} not found in function"))
}

/// The natural-loop block set of the back-edge `latch -> header`: `header`,
/// `latch`, and every block that reaches `latch` without passing through
/// `header` (standard natural-loop construction over predecessor edges).
fn natural_loop_blocks(func: &Function, header: BlockId, latch: BlockId) -> HashSet<BlockId> {
    let mut preds: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for b in &func.blocks {
        for s in block_successors(b) {
            preds.entry(s).or_default().push(b.id);
        }
    }
    let mut set: HashSet<BlockId> = HashSet::new();
    set.insert(header);
    set.insert(latch);
    let mut work: VecDeque<BlockId> = VecDeque::new();
    if latch != header {
        work.push_back(latch);
    }
    while let Some(n) = work.pop_front() {
        for p in preds.get(&n).cloned().unwrap_or_default() {
            if set.insert(p) {
                work.push_back(p);
            }
        }
    }
    set
}

/// The tail-diamond arm region: augment `base` (the natural-loop set of the tail
/// latch, whose backward walk STOPS at the header and so EXCLUDES the tail-arm
/// blocks — they are predecessors of the header, not of the latch) with every
/// block forward-reachable FROM the latch that can ALSO reach the HEADER (the
/// loop's cyclic region). A tail arm reconverges at the header (so its blocks are
/// in this region); a `break`/exit arm CANNOT reach the header, so it is NOT
/// added and stays fail-closed. Used ONLY for the tail-diamond arm walk; the
/// mid-loop diamond keeps the unaugmented `base`. Soundness rests on
/// `model_diamond_arm`'s single-predecessor + `join == header` + modeled-inst
/// checks; this only widens the coarse in-loop membership gate to the true
/// cyclic region.
fn tail_arm_loop_blocks(
    func: &Function,
    header: BlockId,
    latch: BlockId,
    base: &HashSet<BlockId>,
) -> HashSet<BlockId> {
    let mut preds: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for b in &func.blocks {
        for s in block_successors(b) {
            preds.entry(s).or_default().push(b.id);
        }
    }
    // B = blocks that can reach the header (backward reachability).
    let mut back: HashSet<BlockId> = HashSet::new();
    back.insert(header);
    let mut work: VecDeque<BlockId> = VecDeque::new();
    work.push_back(header);
    while let Some(n) = work.pop_front() {
        for p in preds.get(&n).cloned().unwrap_or_default() {
            if back.insert(p) {
                work.push_back(p);
            }
        }
    }
    // Add every block forward-reachable from the latch that is ALSO in B.
    let mut set = base.clone();
    let succs: HashMap<BlockId, Vec<BlockId>> = func
        .blocks
        .iter()
        .map(|b| (b.id, block_successors(b)))
        .collect();
    let mut seen: HashSet<BlockId> = HashSet::new();
    seen.insert(latch);
    let mut work: VecDeque<BlockId> = VecDeque::new();
    work.push_back(latch);
    while let Some(n) = work.pop_front() {
        for s in succs.get(&n).cloned().unwrap_or_default() {
            if seen.insert(s) {
                work.push_back(s);
            }
            if back.contains(&s) {
                set.insert(s);
            }
        }
    }
    set
}

/// Predecessor count of every block over the real trust-ir successor edges
/// (`Br`/`CondBr`/`Switch` targets, via [`block_successors`]). Used by the
/// diamond-arm walker to tell a single-predecessor intermediate chain block (a
/// `-O0` wrapping-call RETURN block to HOP through) apart from the reconvergence
/// join, which has >= 2 predecessors (both arms merge there).
/// Predecessor SETS, not counts.
///
/// Rule T's licence to model a triangle with ONE `ite` is the invariant
/// `preds(join) == {diamond_entry, other_arm}` — an identity a count cannot
/// state. Two predecessors that are the WRONG two blocks admit a third value
/// set into the join's params that one `ite` cannot express.
fn predecessors_of(func: &Function) -> HashMap<BlockId, Vec<BlockId>> {
    let mut preds: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for b in &func.blocks {
        for s in block_successors(b) {
            preds.entry(s).or_default().push(b.id);
        }
    }
    preds
}

/// Is `cand` the JOIN of a triangle whose entry is `diamond_entry`?
///
/// A TRIANGLE is an `if` with no `else`: one arm's edge target IS the join, so
/// that edge threads its values straight in. The arm walker has no notion of the
/// shape: it treats the fall-through edge as an ARM, walks it onward through the
/// latch to the header, and refuses it there as a nested back-edge (the latch is
/// the only natural-loop block whose in-loop successor is the header) — correct
/// about what it sees, wrong about what it is.
///
/// Returns the OTHER predecessor (the arm that must be walked) when `cand`
/// qualifies. ADMISSION-NARROWING at every clause; anything unmatched falls
/// through to the existing code unchanged:
///
/// * `cand` is in-loop and is not the header. An interior triangle may join at
///   the latch: the walked arm stops BEFORE that join, and the merged values
///   then execute the latch once. Header-entry latch joins remain out of this
///   rule; they retain the existing fail-closed diamond handling.
/// * `preds(cand)` is EXACTLY 2. Not `>= 2`: a third in-loop predecessor threads
///   a third value set into the join's params, which a single `ite` cannot
///   express — that is the wrong-admit class, and
///   `latch_triangle_rejects_a_third_join_predecessor` pins it.
/// * one of those two IS `diamond_entry` (the fall-through edge), and
/// * the other is in-loop and is none of the latch, the header, or the entry.
fn triangle_join(
    cand: BlockId,
    diamond_entry: BlockId,
    header: BlockId,
    latch: BlockId,
    loop_set: &HashSet<BlockId>,
    preds: &HashMap<BlockId, Vec<BlockId>>,
) -> Option<BlockId> {
    if !loop_set.contains(&cand) || cand == header || (cand == latch && diamond_entry == header) {
        return None;
    }
    let p = preds.get(&cand)?;
    if p.len() != 2 || !p.contains(&diamond_entry) {
        return None;
    }
    let via = *p.iter().find(|b| **b != diamond_entry)?;
    (loop_set.contains(&via) && via != latch && via != header && via != diamond_entry)
        .then_some(via)
}

fn predecessor_counts(func: &Function) -> HashMap<BlockId, usize> {
    let mut counts: HashMap<BlockId, usize> = HashMap::new();
    for b in &func.blocks {
        for s in block_successors(b) {
            *counts.entry(s).or_default() += 1;
        }
    }
    counts
}

/// Encode one non-terminator instruction into the environment. Encoded ops get
/// their exact bitvector semantics; width-typeable but unmodeled ops bind their
/// results to opaque inputs (sound, see module header); untypeable ops mark
/// their results as untyped (resolving them later is an error).
fn exec_inst(env: &mut Env, inst: &Inst, results: &[ValueId]) -> Result<(), String> {
    // Helper: bind the single result.
    fn bind1(env: &mut Env, results: &[ValueId], e: SmtExpr) -> Result<(), String> {
        if results.len() != 1 {
            return Err(format!(
                "expected exactly one result, got {}",
                results.len()
            ));
        }
        env.vals.insert(results[0], e);
        Ok(())
    }
    // Helper: opaque-bind every result at the given widths.
    fn bind_opaques(env: &mut Env, results: &[ValueId], widths: &[u32]) -> Result<(), String> {
        if results.len() != widths.len() {
            // Shape mismatch — be conservative: mark untyped.
            for r in results {
                env.untyped.insert(*r);
            }
            return Ok(());
        }
        for (r, w) in results.iter().zip(widths) {
            env.bind_opaque(*r, *w)?;
        }
        Ok(())
    }

    match inst {
        Inst::Const { ty, value } => {
            let Some(w) = ty_bit_width(ty) else {
                for r in results {
                    env.untyped.insert(*r);
                }
                return Ok(());
            };
            match value {
                Constant::Int(i) if w <= 64 => {
                    // Two's-complement truncation to `w` bits; `bv_const` masks.
                    bind1(env, results, SmtExpr::bv_const(*i as u64, w))
                }
                Constant::Int(i) if w == 128 => bind1(
                    env,
                    results,
                    crate::mir_semantics::encode_u128_constant(*i as u128),
                ),
                Constant::U128(i) if matches!(ty, Ty::U128) && *i > i128::MAX as u128 => {
                    bind1(env, results, crate::mir_semantics::encode_u128_constant(*i))
                }
                Constant::Bool(bv) if w == 1 => {
                    bind1(env, results, SmtExpr::bv_const(*bv as u64, 1))
                }
                // Other / float / aggregate constants: opaque (sound).
                _ => bind_opaques(env, results, &[w]),
            }
        }
        Inst::BinOp { op, ty, lhs, rhs } => {
            let Some(w) = ty_bit_width(ty) else {
                for r in results {
                    env.untyped.insert(*r);
                }
                return Ok(());
            };
            // FP arithmetic is out of this scalar model: opaque.
            if matches!(
                op,
                BinOp::FAdd
                    | BinOp::FSub
                    | BinOp::FMul
                    | BinOp::FDiv
                    | BinOp::FRem
                    | BinOp::FMin
                    | BinOp::FMax
                    | BinOp::FCopySign
            ) {
                return bind_opaques(env, results, &[w]);
            }
            let l = env.resolve(*lhs, w)?;
            // A SHIFT may be mixed-width (`u64 << i32`): coerce the AMOUNT to the
            // value width (zero-extend/truncate). Every other binop requires
            // same-width operands, so resolve the RHS strictly at the value width
            // (a genuine width mismatch there stays fail-closed, unchanged).
            let is_shift = matches!(op, BinOp::Shl | BinOp::LShr | BinOp::AShr);
            let r = if is_shift {
                env.resolve_shift_amount(*rhs, w)?
            } else {
                env.resolve(*rhs, w)?
            };
            let e = match op {
                BinOp::Add => l.bvadd(r),
                BinOp::Sub => l.bvsub(r),
                BinOp::Mul => l.bvmul(r),
                BinOp::UDiv => l.bvudiv(r),
                BinOp::SDiv => l.bvsdiv(r),
                // Same defined-input forms as the MIR spec encoder
                // (`encode_mir_binop`); singular inputs are excluded by the
                // caller's source-derived preconditions or refute (fail closed).
                BinOp::URem => {
                    let q = l.clone().bvudiv(r.clone());
                    l.bvsub(q.bvmul(r))
                }
                BinOp::SRem => {
                    let q = l.clone().bvsdiv(r.clone());
                    l.bvsub(q.bvmul(r))
                }
                BinOp::And => l.bvand(r),
                BinOp::Or => l.bvor(r),
                BinOp::Xor => l.bvxor(r),
                // Trust: the BOOLEAN connectives (trust-ir 4b06918) -- exact on the
                // 1-bit `Bool` carrier their validator restricts them to, where the
                // bitwise BV op IS the logical one.
                BinOp::BAnd => l.bvand(r),
                BinOp::BOr => l.bvor(r),
                BinOp::BXor => l.bvxor(r),
                // Shifts: exact for in-range amounts; OPAQUE out of range (the
                // trust-ir out-of-range shift value is not assumed).
                BinOp::Shl | BinOp::LShr | BinOp::AShr => {
                    let raw = match op {
                        BinOp::Shl => l.clone().bvshl(r.clone()),
                        BinOp::LShr => l.clone().bvlshr(r.clone()),
                        _ => l.clone().bvashr(r.clone()),
                    };
                    // A shift amount that is SYNTACTICALLY bounded below the
                    // value width (the `n & (width-1)` idiom rustc and Rust
                    // source both emit) makes `in_range` a tautology, so the
                    // guarded form collapses to the raw shift with NO opaque.
                    // That matters beyond tidiness: an opaque here is an
                    // UNMODELED symbol, and a back-edge arg carrying one is
                    // declined outright by `reject_unmodeled_args`.
                    if smt_max_value_bound(&r).is_some_and(|b| b < u64::from(w)) {
                        raw
                    } else {
                        // Out-of-range shifts stay UNASSUMED (trust-ir's
                        // lowering-defined behavior is deliberately not adopted
                        // here), so a bridge that forgets the mask is refuted.
                        let in_range = r.bvult(SmtExpr::bv_const(u64::from(w), w));
                        let opaque = env.fresh_opaque(w)?;
                        SmtExpr::ite(in_range, raw, opaque)
                    }
                }
                // trust-ir WS3.20 rotates are TOTAL (the amount is reduced
                // modulo the width), so this is exact for every amount: with
                // `a = r mod w`, `rotl = (l << a) | (l >>u (w - a))`. At
                // `a = 0` the second shift is by exactly `w`, which is 0 under
                // SMT-LIB's saturating shifts and `l` under a masking reading;
                // either way the OR is `l`.
                BinOp::RotL | BinOp::RotR => {
                    let width = SmtExpr::bv_const(u64::from(w), w);
                    let toward = r.bvurem(width.clone());
                    let back = width.bvsub(toward.clone());
                    if matches!(op, BinOp::RotL) {
                        l.clone().bvshl(toward).bvor(l.bvlshr(back))
                    } else {
                        l.clone().bvlshr(toward).bvor(l.bvshl(back))
                    }
                }
                BinOp::FAdd
                | BinOp::FSub
                | BinOp::FMul
                | BinOp::FDiv
                | BinOp::FRem
                | BinOp::FMin
                | BinOp::FMax
                | BinOp::FCopySign => {
                    unreachable!("handled above")
                }
            };
            bind1(env, results, e)
        }
        Inst::UnOp { op, ty, operand } => {
            let Some(w) = ty_bit_width(ty) else {
                for r in results {
                    env.untyped.insert(*r);
                }
                return Ok(());
            };
            match op {
                UnOp::Neg => {
                    let o = env.resolve(*operand, w)?;
                    bind1(env, results, o.bvneg())
                }
                UnOp::Not => {
                    let o = env.resolve(*operand, w)?;
                    // Bitwise NOT; at width 1 this is exactly logical NOT.
                    let all_ones = SmtExpr::bv_const(u64::MAX, w.min(64));
                    if w <= 64 {
                        bind1(env, results, o.bvxor(all_ones))
                    } else if w == 128 {
                        bind1(env, results, o.bvxor(crate::mir_semantics::encode_u128_constant(u128::MAX)))
                    } else {
                        bind_opaques(env, results, &[w])
                    }
                }
                // Float-rounding unops (FFloor/FCeil/FTrunc), like the other float
                // unops here, have no bit-vector encoding; bind the result as an
                // opaque (unconstrained) value — sound: the symbolic engine learns
                // nothing about it rather than assuming wrong semantics.
                UnOp::FNeg
                | UnOp::FAbs
                | UnOp::FSqrt
                | UnOp::FFloor
                | UnOp::FCeil
                | UnOp::FTrunc
                | UnOp::CtPop
                // trust-ir WS3.20 bit intrinsics: not modeled, so opaque like
                // CtPop — the engine assumes nothing about the result.
                | UnOp::CtLz
                | UnOp::CtTz
                | UnOp::BSwap
                | UnOp::BitReverse => bind_opaques(env, results, &[w]),
            }
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            let Some(w) = ty_bit_width(ty) else {
                for r in results {
                    env.untyped.insert(*r);
                }
                return Ok(());
            };
            let l = env.resolve(*lhs, w)?;
            let r = env.resolve(*rhs, w)?;
            let cond = match op {
                ICmpOp::Eq => l.eq_expr(r),
                ICmpOp::Ne => l.eq_expr(r).not_expr(),
                ICmpOp::Ult => l.bvult(r),
                ICmpOp::Ule => l.bvule(r),
                ICmpOp::Ugt => l.bvugt(r),
                ICmpOp::Uge => l.bvuge(r),
                ICmpOp::Slt => l.bvslt(r),
                ICmpOp::Sle => l.bvsle(r),
                ICmpOp::Sgt => l.bvsgt(r),
                ICmpOp::Sge => l.bvsge(r),
            };
            bind1(
                env,
                results,
                SmtExpr::ite(cond, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1)),
            )
        }
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => {
            let (Some(sw), Some(dw)) = (ty_bit_width(src_ty), ty_bit_width(dst_ty)) else {
                for r in results {
                    env.untyped.insert(*r);
                }
                return Ok(());
            };
            match op {
                CastOp::ZExt if dw >= sw => {
                    let o = env.resolve(*operand, sw)?;
                    let e = if dw == sw { o } else { o.zero_ext(dw - sw) };
                    bind1(env, results, e)
                }
                CastOp::SExt if dw >= sw => {
                    let o = env.resolve(*operand, sw)?;
                    let e = if dw == sw { o } else { o.sign_ext(dw - sw) };
                    bind1(env, results, e)
                }
                CastOp::Trunc if dw <= sw => {
                    let o = env.resolve(*operand, sw)?;
                    let e = if dw == sw { o } else { o.extract(dw - 1, 0) };
                    bind1(env, results, e)
                }
                // Same-width bit-identity casts preserve the bit pattern.
                CastOp::Bitcast | CastOp::Transmute if dw == sw => {
                    let o = env.resolve(*operand, sw)?;
                    bind1(env, results, o)
                }
                // A pointer<->integer round trip at EQUAL width is a bit
                // identity, exactly like `Bitcast`/`Transmute` above: the trust-ir
                // `PtrToInt`/`IntToPtr` pair carries the address value through
                // unchanged. Modeling it (rather than minting a fresh opaque) is
                // what makes the aggregate-construction address expressions
                // `alloca + k` STRUCTURALLY COMPARABLE, which the store-to-load
                // forwarding window below relies on. SOUND for the same reason as
                // the bitcast arm — no value is invented, and a genuinely
                // different address still produces a different expression.
                CastOp::PtrToInt | CastOp::IntToPtr if dw == sw => {
                    let o = env.resolve(*operand, sw)?;
                    bind1(env, results, o)
                }
                // Everything else (FP converts, width-changing pointer casts, ...):
                // opaque.
                _ => bind_opaques(env, results, &[dw]),
            }
        }
        // Pseudo copy: identity at the value level.
        Inst::Copy { ty, operand } => {
            let Some(w) = ty_bit_width(ty) else {
                for r in results {
                    env.untyped.insert(*r);
                }
                return Ok(());
            };
            let o = env.resolve(*operand, w)?;
            bind1(env, results, o)
        }
        Inst::Select {
            ty,
            cond,
            then_val,
            else_val,
        } => {
            let Some(w) = ty_bit_width(ty) else {
                for r in results {
                    env.untyped.insert(*r);
                }
                return Ok(());
            };
            let c = env.resolve(*cond, 1)?;
            let t = env.resolve(*then_val, w)?;
            let e = env.resolve(*else_val, w)?;
            bind1(
                env,
                results,
                SmtExpr::ite(c.eq_expr(SmtExpr::bv_const(0, 1)).not_expr(), t, e),
            )
        }
        // A NON-volatile `Load` whose (pointer, width) is still live in the
        // forwarding window reads back exactly the value the matching `Store`
        // wrote. That window is the ONLY memory the model understands; see
        // `Inst::Store` below for the (deliberately tiny) invariant it maintains.
        //
        // WHY THIS EXISTS: the bridge materializes an `Option<iN>` aggregate in
        // memory (`Alloca` + tag `Store` + payload `Store` + payload `Load`), so
        // an in-loop `checked_div`/`checked_rem` arm threads its value through a
        // stack slot. Without forwarding, that value is a fresh opaque and the
        // threading VC can never refine (Stage-0 declines it).
        Inst::Load {
            ty,
            ptr,
            volatile: false,
            ..
        } if !env.mem_poisoned && !env.mem.is_empty() => {
            let Some(w) = ty_bit_width(ty) else {
                for r in results {
                    env.untyped.insert(*r);
                }
                return Ok(());
            };
            // A pointer this model cannot resolve at 64 bits simply does not
            // forward — the load stays opaque, exactly as before.
            let forwarded = env.resolve(*ptr, 64).ok().and_then(|p| {
                env.mem
                    .iter()
                    .find(|(kp, kw, _)| *kp == p && *kw == w)
                    .map(|(_, _, v)| v.clone())
            });
            match forwarded {
                Some(v) => bind1(env, results, v),
                None => bind_opaques(env, results, &[w]),
            }
        }
        // Width-typeable but unmodeled value producers: opaque results.
        Inst::Load { ty, .. } | Inst::AtomicLoad { ty, .. } | Inst::AtomicRMW { ty, .. } => {
            // An ATOMIC access (or a volatile load) can observe/publish writes
            // this model does not track: stop forwarding for the rest of the walk.
            if !matches!(
                inst,
                Inst::Load {
                    volatile: false,
                    ..
                }
            ) {
                env.poison_memory();
            }
            match ty_bit_width(ty) {
                Some(w) => bind_opaques(env, results, &[w]),
                None => {
                    for r in results {
                        env.untyped.insert(*r);
                    }
                    Ok(())
                }
            }
        }
        Inst::Overflow { op, ty, lhs, rhs } => match ty_bit_width(ty) {
            // The WRAPPED value (result 0) of a checked / overflowing / wrapping
            // Add/Sub/Mul is the two's-complement `bvadd`/`bvsub`/`bvmul` at
            // width `w` — bit-identical to the plain `Inst::BinOp` arm above and
            // to the MIR spec's `encode_mir_binop`. Modeling it (rather than an
            // opaque) lets a euclid-class rotation that ALSO carries a wrapping
            // accumulator — `s = s.wrapping_add(x)`, or any `+`/`-`/`*` under
            // `-Coverflow-checks=on` (the default debug build) — be PROVEN
            // instead of spuriously Refuted (the loop-VC only runs on a
            // structural false-reject, i.e. already-correct code). The overflow
            // FLAG (result 1) is bound to the SHARED loop-VC uninterpreted symbol
            // `overflow_flag_uf(op, w, lhs, rhs)` — the SAME function application
            // the MIR SPEC's `_6.1` extract denotes (see
            // `mir_semantics::CheckedOverflowPacked`). That lets a loop CARRYING
            // the flag — `let mut p:(iN,bool); while { p = x.overflowing_add(k) }`,
            // whose O2/O3 scalarization threads the flag through a header slot — be
            // PROVEN value-correct by UF congruence WITHOUT the exact (signedness-
            // dependent) flag formula the `Inst::Overflow` opcode drops. The flag's
            // VALUE-correctness is proven separately by the per-inst `Inst::Overflow`
            // cert; this UF is confined to the threading obligation.
            //
            // SOUND: a MISLABELED lowering (`wrapping_sub` emitted as `AddOverflow`)
            // changes BOTH the wrapped slot (bvsub vs the spec's bvadd) AND the flag
            // symbol (`__tir_ovf_sub` vs `__tir_ovf_add`), so it still Refutes; a
            // WRONG threading (a stale value / a different op's flag in the flag
            // slot) is not congruent and Refutes. This only ever turns a false-Refute
            // into a Refine — never a wrong admit. Width <= 128 covers every
            // canonical `Inst::Overflow`, including wide multiplication. The
            // bridge still composes wide add/sub from ordinary operations, which
            // the walk models concretely in their respective instruction arms.
            // `bvadd`/`bvsub`/`bvmul` and `overflow_flag_uf` are width-generic, so
            // nothing in this arm was ever specialized to <= 64. An unexpected
            // result arity still falls through to the opaque binding (sound).
            Some(w) if w <= 128 && results.len() == 2 => {
                let l = env.resolve(*lhs, w)?;
                let r = env.resolve(*rhs, w)?;
                let (wrapped, tag) = match op {
                    OverflowOp::AddOverflow => (l.clone().bvadd(r.clone()), "add"),
                    OverflowOp::SubOverflow => (l.clone().bvsub(r.clone()), "sub"),
                    OverflowOp::MulOverflow => (l.clone().bvmul(r.clone()), "mul"),
                };
                env.vals.insert(results[0], wrapped);
                let flag = crate::mir_semantics::overflow_flag_uf(tag, w, l, r);
                env.vals.insert(results[1], flag);
                Ok(())
            }
            // A wider value or an unexpected (value, flag) result shape:
            // opaque both, exactly as before (sound — only ever a fail-closed).
            Some(w) => bind_opaques(env, results, &[w, 1]),
            None => {
                for r in results {
                    env.untyped.insert(*r);
                }
                Ok(())
            }
        },
        // `ExtractField` on a TUPLE aggregate — the shape a slice fat pointer takes
        // (`Tuple([I64, I64])` = (ptr, len)). Without a width rule the result is
        // marked `untyped`, and `reject_unmodeled_args` then refuses ANY back-edge
        // slot whose value depends on it. Measured on
        // `core::str::pattern::TwoWaySearcher::maximal_suffix`: `arr.len()` is
        // `ExtractField { ty: Tuple([I64, I64]), field: 1 }`, it feeds the
        // `right + offset < arr.len()` bounds check, and the branch conditions
        // built from it reach every carried slot.
        //
        // `ty` is the AGGREGATE type at the sites that matter here, so index it by
        // `field`; a non-aggregate `ty` is the RESULT type and is width-typed
        // directly. Anything else stays untyped, exactly as before.
        //
        // SOUND: this only ASSIGNS A WIDTH so the value can be an OPAQUE. The value
        // stays unconstrained, so a threading that depends on it discharges only if
        // the SPEC side names the same symbol, and otherwise refutes — never a wrong
        // admit. It converts a hard "no width-typeable result" refusal into the
        // ordinary opaque path.
        Inst::ExtractField { ty, field, .. } => {
            let elem_width = match ty {
                Ty::Tuple(elems) => elems.get(*field as usize).and_then(ty_bit_width),
                // `Ty::Array(elem, n)` is the O(1) spelling of the same lane tuple on
                // newer trust-ir: the bridge's `{ data, len }` slot is `Array(lane, 2)`
                // (see `memory_slot_lane_ty`), so `arr.len()` arrives here as
                // `ExtractField { ty: Array(lane, 2), field: 1 }`. The element's
                // width IS the field's width for any in-range field. Measured: after
                // the 2026-09-21 merge of `origin/main` this exact shape put
                // `maximal_suffix` back to a failed root with "no width-typeable
                // result" — the rule below was written against the tuple spelling
                // only.
                Ty::Array(elem, n) if u64::from(*field) < *n => {
                    env.types.get(elem.0 as usize).and_then(ty_bit_width)
                }
                other => ty_bit_width(other),
            };
            match elem_width {
                Some(w) => bind_opaques(env, results, &[w]),
                None => {
                    for r in results {
                        env.untyped.insert(*r);
                    }
                    Ok(())
                }
            }
        }
        Inst::Undef { ty } => match ty_bit_width(ty) {
            Some(w) => bind_opaques(env, results, &[w]),
            None => {
                for r in results {
                    env.untyped.insert(*r);
                }
                Ok(())
            }
        },
        // An `Alloca` result is an opaque 64-bit base like the other pointer
        // producers, but it is a base the WALK ITSELF created: a fresh,
        // non-escaping stack slot. Recording its name lets the store/load window
        // below tell "an address I built from a known stack slot" apart from "an
        // address that came out of nowhere".
        Inst::Alloca { .. } => {
            bind_opaques(env, results, &vec![64; results.len()])?;
            for r in results {
                env.alloca_opaques.insert(format!("__tir_v{}", r.index()));
            }
            Ok(())
        }
        // A HEAP allocation can also publish/observe memory this model does not
        // track (the allocator writes its own metadata), so it poisons the window.
        Inst::HeapAlloc { .. } => {
            env.poison_memory();
            bind_opaques(env, results, &vec![64; results.len()])
        }
        Inst::GEP { .. } | Inst::PtrData { .. } | Inst::GlobalAddr { .. } | Inst::NullPtr => {
            bind_opaques(env, results, &vec![64; results.len()])
        }
        // A NON-volatile `Store` through an address built from a KNOWN stack slot
        // opens (or replaces) the one-entry forwarding window. Any other store —
        // through an address the walk did not construct, or volatile — poisons it.
        //
        // The window is deliberately at most ONE entry: a store retains only an
        // entry at its OWN, syntactically identical pointer and width, so a
        // forwarded load is always a same-pointer / same-width read with NO
        // intervening store. That is exactly the aggregate-construction shape
        // (`Store payload@p; Load @p`) and nothing wider; a differing offset, a
        // differing width, or an intervening store all fall back to an opaque
        // (Stage-0 then declines the compile rather than refuting it).
        Inst::Store {
            ty,
            ptr,
            value,
            volatile: false,
            ..
        } if !env.mem_poisoned => {
            let Some(w) = ty_bit_width(ty) else {
                // A store of a value this model cannot width-type could alias
                // anything the window holds.
                env.poison_memory();
                return Ok(());
            };
            // A pointer this model cannot resolve at 64 bits has unknown
            // provenance: poison rather than open a window on it.
            let Ok(p) = env.resolve(*ptr, 64) else {
                env.poison_memory();
                return Ok(());
            };
            // Every unmodeled symbol in the ADDRESS must be an `Alloca` result;
            // otherwise the pointer's provenance is unknown to the model and two
            // syntactically equal expressions need not denote the same location.
            let unknown_base = env
                .unmodeled_free_vars(&p)
                .into_iter()
                .any(|n| !env.alloca_opaques.contains(&n));
            if unknown_base {
                env.poison_memory();
                return Ok(());
            }
            let Ok(v) = env.resolve(*value, w) else {
                env.poison_memory();
                return Ok(());
            };
            // A store MAY alias any entry whose address is not syntactically
            // identical, and a same-address store at a different width overlaps
            // it. Drop everything, then bind this one — the window holds exactly
            // the most recent store.
            env.mem.clear();
            env.mem.push((p, w, v));
            Ok(())
        }
        // Volatile / atomic stores and fences: unobservable-to-this-model writes.
        Inst::Store { .. } | Inst::AtomicStore { .. } | Inst::Fence { .. } => {
            env.poison_memory();
            Ok(())
        }
        // A value-IDENTITY call (`core::hint::black_box`, registered by the caller in
        // `identity_calls`): `black_box(x) = x`, so bind the result to the arg's
        // value. This lets the threading VC PROVE a loop whose bound/inputs are
        // black-boxed (`while a < black_box(N)`) instead of bailing on an unmodeled
        // call. SOUND: only the genuine std `black_box` is registered (a non-identity
        // call is never in the set), and if the arg is itself unmodeled we leave the
        // result untyped (fail-closed), never guessing a value.
        Inst::Call { callee, args }
            if env.identity_calls.contains(callee) && args.len() == 1 && results.len() == 1 =>
        {
            if let Some(arg) = env.vals.get(&args[0]).cloned() {
                env.vals.insert(results[0], arg);
            } else {
                env.untyped.insert(results[0]);
            }
            Ok(())
        }
        // Anything else: results exist but cannot be width-typed from the
        // instruction alone — mark untyped (error if the threading needs them).
        other => {
            // A call this model does not interpret (anything but the registered
            // value-identity `black_box`) can write memory arbitrarily, and so can
            // any other unmodeled effectful instruction. Stop forwarding for the
            // rest of the walk rather than read a stale value back.
            env.poison_memory();
            let _ = other;
            for r in results {
                env.untyped.insert(*r);
            }
            Ok(())
        }
    }
}

/// One arm of an in-loop 2-way diamond: the values threaded to the join block's
/// params on that arm (resolved over the shared `env`), and the block the arm
/// reaches. An arm is a bounded, strictly SINGLE-PREDECESSOR chain of straight-
/// line blocks (usually one, but >1 at `-O0` when a `wrapping_*` call is lowered
/// with its own RETURN block: `bb_arm: … br bb_ret` / `bb_ret: t = call_ret; br
/// join`) ending in `Br join(args)`. Anything else (an arm with its own branch /
/// a nested diamond / a back-edge / a non-`Br` terminator / a shared merge block
/// mid-chain) is rejected.
struct DiamondArm {
    join: BlockId,
    /// The block whose terminator produced the join edge. `model_triangle`
    /// checks it against the CFG-classified other predecessor of the join, so
    /// the walked arm is known to be the second of `preds(join) == {entry,
    /// other_arm}` — the identity Rule T's single `ite` rests on.
    via: BlockId,
    /// The block args this arm threads to the join's params (in slot order),
    /// resolved over `env`.
    join_args: Vec<ValueId>,
}

/// Model one arm of an in-loop diamond as a bounded single-predecessor chain.
/// `edge_target` is the `CondBr` arm target and `edge_args` the args it threads.
/// Executes each chain block's body into `env`, HOPPING through any intermediate
/// block that has exactly ONE predecessor and is forward-in-loop (a call-return
/// block), and stops at the reconvergence join (>= 2 predecessors — both arms).
/// Returns the join block + the args threaded to it. Fail-closed (`Err`) on any
/// shape outside that (a non-`Br` terminator = nested diamond, an in-arm
/// back-edge, an over-long chain). SOUNDNESS: hopping only executes MORE of the
/// arm's own (uniquely-reached) blocks, making the IMPL model of the threaded
/// value strictly MORE faithful to the emitted trust-ir; a wrong emitted value
/// still refutes the MIR spec.
///
/// `allow_header_join` decides what an arm that `Br`s to the HEADER is:
///
/// * `false` — callers passing the UNAUGMENTED natural-loop set
///   (`model_in_loop_diamond`, `model_triangle`). There such an arm is REFUSED,
///   and the refusal is a theorem, not a policy: `natural_loop_blocks` is
///   `{header, latch}` plus backward reachability from the latch in which the
///   header is pre-inserted and never enqueued, so every member other than the
///   header or the latch has a successor in the set that is NOT the header. The
///   block `cur` that reports `join == header` is in the set and is not the
///   header (entry check below, and the hop condition), and its successors are
///   the header plus at most one OUT-of-loop block (the guard normalization) —
///   so `cur` can only BE the latch, and the arm takes the very back-edge under
///   obligation. That is a nested back-edge, not a reconverging arm; the latch
///   would be reachable from both arms and one `ite` could not describe the
///   values the back-edge carries.
/// * `true` — ONLY `tail_arm_header_args`, over `tail_arm_loop_blocks`, whose
///   augmented set contains the tail-arm blocks that the theorem above excludes
///   (they are predecessors of the header, not of the latch). There the header
///   IS the tail diamond's join and is returned as such.
#[allow(clippy::too_many_arguments)] // Explicit graph roles keep this proof boundary auditable.
fn model_diamond_arm(
    env: &mut Env,
    func: &Function,
    loop_set: &HashSet<BlockId>,
    header: BlockId,
    diamond_entry: BlockId,
    edge_target: BlockId,
    edge_args: &[ValueId],
    pred_counts: &HashMap<BlockId, usize>,
    allow_header_join: bool,
) -> Result<DiamondArm, String> {
    // The arm target must be strictly inside the loop and must not be the
    // header (a back-edge from an arm is out of model) nor re-enter the diamond
    // entry.
    if !loop_set.contains(&edge_target) || edge_target == header {
        return Err(format!(
            "diamond arm at {diamond_entry:?} targets {edge_target:?}, which is not a \
             forward in-loop block (out of model)"
        ));
    }
    // A tight bound on the arm chain length (one wrapping call adds one return
    // block; the straight-line arm gap between `if` and the join is short). Any
    // longer chain is out of model (fail closed).
    const MAX_ARM_BLOCKS: usize = 8;
    let mut cur = edge_target;
    let mut cur_args: Vec<ValueId> = edge_args.to_vec();
    let mut hops = 0usize;
    loop {
        if hops >= MAX_ARM_BLOCKS {
            return Err(format!(
                "diamond arm at {diamond_entry:?} exceeds the {MAX_ARM_BLOCKS}-block chain \
                 bound (out of model)"
            ));
        }
        let arm_block = block_of(func, cur)?;
        let Some((term, body)) = arm_block.body.split_last() else {
            return Err(format!("diamond arm block {cur:?} is empty"));
        };
        // Normalize the arm terminator to ONE continuation edge.
        //
        // `Br` is that edge already. A `CondBr` whose two successors split into
        // exactly one IN-loop and one OUT-of-loop target is a GUARD, not a nested
        // diamond — it is what a MIR `Assert` lowers to (and what a `break` looks
        // like), and an execution taking the out-of-loop edge NEVER REACHES this
        // back-edge, so it contributes nothing to THIS obligation. Follow the
        // surviving in-loop edge. This mirrors the MIR spec side, where
        // `vc_walk_mir_arm` walks through an `Assert` to its success target.
        //
        // The guard condition is deliberately NOT recorded as a path condition.
        // That is sound in one direction only, and it is the safe one: omitting a
        // path condition ENLARGES the input space the obligation must hold over,
        // so it can only make the VC fail to refine (a refusal), never license a
        // threading it should have refused.
        //
        // Both targets in-loop is a genuine nested diamond and both out-of-loop
        // leaves no continuation; each stays out of model, fail closed.
        let (edge_target_next, edge_args_next) = match &term.inst {
            Inst::Br { target, args } => (*target, args.clone()),
            Inst::CondBr {
                then_target,
                then_args,
                else_target,
                else_args,
                ..
            } => match (
                loop_set.contains(then_target),
                loop_set.contains(else_target),
            ) {
                (true, false) => (*then_target, then_args.clone()),
                (false, true) => (*else_target, else_args.clone()),
                (true, true) => {
                    return Err(format!(
                        "diamond arm {cur:?} ends in a CondBr with BOTH targets in-loop \
                         (nested diamond is out of model)"
                    ));
                }
                (false, false) => {
                    return Err(format!(
                        "diamond arm {cur:?} ends in a CondBr with NEITHER target in-loop \
                         (no continuation to the join; out of model)"
                    ));
                }
            },
            Inst::Switch {
                cases,
                default,
                default_args,
                ..
            } if cases.len() == 1 => {
                let first = &cases[0];
                match (loop_set.contains(&first.target), loop_set.contains(default)) {
                    (true, false) => (first.target, first.args.clone()),
                    (false, true) => (*default, default_args.clone()),
                    _ => {
                        return Err(format!(
                            "diamond arm {cur:?} has a Switch without exactly one in-loop continuation"
                        ));
                    }
                }
            }
            other => {
                return Err(format!(
                    "diamond arm {cur:?} does not end in a single `Br` to the join \
                     (got {other:?}); nested/branching arms are out of model"
                ));
            }
        };
        {
            {
                let (target, args) = (&edge_target_next, &edge_args_next);
                thread_args_into_params(env, arm_block, &cur_args)?;
                // Store-to-load forwarding is confined to ONE block: at a block
                // boundary the incoming memory state is whatever the predecessor
                // (or the OTHER arm) left, and merging those is out of model.
                env.clear_memory_window();
                for node in body {
                    exec_inst(env, &node.inst, &node.results)?;
                }
                if *target == header {
                    // A TAIL diamond arm reconverges AT the header (the whole
                    // diamond is the loop tail). Accept it as the join only when
                    // the caller opts in; over the natural-loop set the arm can
                    // only be the latch (see the doc above), so a MID-loop
                    // diamond arm branching to the header is a nested back-edge,
                    // out of model (fail closed).
                    if allow_header_join {
                        return Ok(DiamondArm {
                            join: header,
                            via: cur,
                            join_args: args.clone(),
                        });
                    }
                    return Err(format!(
                        "diamond arm {cur:?} (diamond at {diamond_entry:?}) branches back to \
                         the header {header:?}: {cur:?} is in the natural-loop set and its \
                         only in-loop successor is the header, so it can reach the latch only \
                         by BEING the latch — the arm takes the very back-edge under \
                         obligation (a nested back-edge, not a reconverging arm; out of \
                         model, the structural gate stays authoritative)"
                    ));
                }
                // A forward in-loop block reached ONLY from this chain (exactly
                // one predecessor) is an intermediate call-return block: HOP
                // through it. The reconvergence join is reached from BOTH arms
                // (>= 2 predecessors), so the walk stops there and the caller
                // merges the two arms' threaded args with an `ite`.
                let is_intermediate =
                    loop_set.contains(target) && pred_counts.get(target).copied().unwrap_or(0) == 1;
                if is_intermediate {
                    cur = *target;
                    cur_args = args.clone();
                    hops += 1;
                    continue;
                }
                return Ok(DiamondArm {
                    join: *target,
                    via: cur,
                    join_args: args.clone(),
                });
            }
        }
    }
}

/// Thread `args` into `block`'s params over `env` (the same binding the main
/// walk does at an edge): each param gets the resolved value of the matching
/// arg. Width/arity are checked. Used at a diamond arm's entry and at the join.
fn thread_args_into_params(env: &mut Env, block: &Block, args: &[ValueId]) -> Result<(), String> {
    if block.params.len() != args.len() {
        return Err(format!(
            "edge into {:?} passes {} arg(s) to a block with {} param(s)",
            block.id,
            args.len(),
            block.params.len()
        ));
    }
    for ((pv, pty), av) in block.params.iter().zip(args) {
        let w = ty_bit_width(pty).ok_or_else(|| {
            format!("block param {pv:?} has a non-scalar type {pty:?} (out of model)")
        })?;
        let e = env.resolve(*av, w)?;
        env.vals.insert(*pv, e);
    }
    Ok(())
}

/// Model a TRIANGLE: one arm's edge target IS the join, so that edge threads its
/// values straight in and runs no block body.
///
/// The merge is the SAME `ite(taken, then, else)` the 2-arm diamond builds — a
/// TOTAL function of the branch condition, so the single obligation constrains
/// both branches at once. Nothing is partitioned and no coverage side-condition
/// is needed (`ProofObligation.preconditions` is a conjunction and could not
/// state one anyway).
///
/// The fall-through args are resolved BEFORE the other arm is walked: that edge
/// executes no body, so its values are exactly those live at the diamond entry.
/// Resolving after would read values the walked arm defined.
#[allow(clippy::too_many_arguments)]
fn model_triangle(
    env: &mut Env,
    func: &Function,
    loop_set: &HashSet<BlockId>,
    header: BlockId,
    diamond_entry: BlockId,
    taken: SmtExpr,
    join_id: BlockId,
    fallthrough_args: &[ValueId],
    walk_target: BlockId,
    walk_args: &[ValueId],
    expected_via: BlockId,
    fallthrough_is_then: bool,
    pred_counts: &HashMap<BlockId, usize>,
) -> Result<BlockId, String> {
    let join_block = block_of(func, join_id)?;
    if fallthrough_args.len() != join_block.params.len() {
        return Err(format!(
            "triangle join {join_id:?} has {} param(s) but the fall-through edge threads {}",
            join_block.params.len(),
            fallthrough_args.len()
        ));
    }
    let mut fallthrough_vals = Vec::with_capacity(join_block.params.len());
    for (slot, (_pv, pty)) in join_block.params.iter().enumerate() {
        let w = ty_bit_width(pty).ok_or_else(|| {
            format!("triangle join param slot {slot} has a non-scalar type {pty:?} (out of model)")
        })?;
        fallthrough_vals.push(env.resolve(fallthrough_args[slot], w)?);
    }

    // The other arm must land on THIS join, via the block the CFG predicate named.
    //
    // `allow_header_join=false`: an arm reaching the header here is the nested
    // back-edge shape, and stays refused — over the natural-loop set such an arm
    // can only be the latch (the theorem in `model_diamond_arm`'s doc).
    //
    // This rule briefly classified such an arm as an early `continue` and
    // threaded the fall-through args instead. That branch was UNREACHABLE by the
    // same theorem and is gone; measured at the time, removing it left
    // `library/core` at 0 failed roots. The two-arm rule in
    // `model_in_loop_diamond` that it was modelled on was unreachable for exactly
    // the same reason and has been removed since as well.
    let arm = model_diamond_arm(
        env,
        func,
        loop_set,
        header,
        diamond_entry,
        walk_target,
        walk_args,
        pred_counts,
        /*allow_header_join=*/ false,
    )?;
    if arm.join != join_id || arm.via != expected_via {
        return Err(format!(
            "triangle at {diamond_entry:?}: the walked arm reconverges at {:?} via {:?}, but \
             the CFG says the join is {join_id:?} via {expected_via:?} (out of model)",
            arm.join, arm.via
        ));
    }
    if arm.join_args.len() != join_block.params.len() {
        return Err(format!(
            "triangle join {join_id:?} has {} param(s) but the walked arm threads {}",
            join_block.params.len(),
            arm.join_args.len()
        ));
    }
    for (slot, (pv, pty)) in join_block.params.iter().enumerate() {
        let w = ty_bit_width(pty).ok_or_else(|| {
            format!("triangle join param {pv:?} has a non-scalar type {pty:?} (out of model)")
        })?;
        let walked = env.resolve(arm.join_args[slot], w)?;
        let merged = if fallthrough_is_then {
            SmtExpr::ite(taken.clone(), fallthrough_vals[slot].clone(), walked)
        } else {
            SmtExpr::ite(taken.clone(), walked, fallthrough_vals[slot].clone())
        };
        env.vals.insert(*pv, merged);
    }
    Ok(join_id)
}

/// What `short_circuit_region` recognizes: the region's blocks in topological
/// order, and its TWO exits, each paired with the arguments its edges carry.
/// Borrowed from the `Function` the region was recognized in.
type ShortCircuitRegion<'f> = (Vec<BlockId>, [(BlockId, &'f [ValueId]); 2]);

/// Recognize a SHORT-CIRCUIT CONDITION REGION rooted at `at`: the region's blocks
/// in topological order, and its TWO exits with the arguments their edges carry.
/// The caller decides what the region IS from how the exits sit in `loop_set` —
/// one in-loop makes it a compound GUARD, two a compound DIAMOND — and must
/// execute the interior blocks' instructions.
///
/// This is the trust-ir half of `vc_short_circuit_shape` on the MIR spec side.
/// A `&&`/`||` chain is ONE source branch lowered to a CHAIN of `CondBr`s
/// converging on two blocks; the arm walker rightly refuses the second link,
/// because it is not an arm.
///
/// Measured on `core::str::pattern::TwoWaySearcher::maximal_suffix`, whose
/// `if (a < b && !g) || (a > b && g)` lowers to a four-block chain. Its loop has
/// FOUR back-edges and `loop_set` is backward reachability from ONE latch, so the
/// SAME region classifies differently per obligation — a guard for the back-edge
/// whose latch only one exit reaches, a diamond for the one both reach.
///
/// Returns `None` — leaving the caller byte-identical — unless ALL of:
///
/// * every region block ends in a `CondBr` with two distinct targets;
/// * every non-entry region block has ALL its predecessors inside the region, so
///   `at` is the region's sole entry;
/// * every region-internal edge runs FORWARD in `order`, making the region a DAG
///   that every path leaves;
/// * exactly TWO distinct exits;
/// * every non-entry region block has NO block params — the interior is executed
///   unconditionally, and a param would need a merge this does not build;
/// * every region edge into a given exit carries the SAME arguments, so there is
///   one value to thread however the region was traversed.
///
/// Executing the interior unconditionally is value-correct for the same reason it
/// is on the MIR side, and more simply: trust-ir is SSA, so a use is dominated by
/// its definition, and the region is walked in topological order.
fn short_circuit_region<'f>(
    func: &'f Function,
    loop_set: &HashSet<BlockId>,
    header: BlockId,
    latch: BlockId,
    at: BlockId,
    preds: &HashMap<BlockId, Vec<BlockId>>,
) -> Option<ShortCircuitRegion<'f>> {
    const MAX_REGION: usize = 8;
    // Under `-Ztrust-ir-cg-args=backedge-trace`, say WHY a candidate region was
    // refused. Every clause here is a silent `None` otherwise, and a silent
    // fallback reads exactly like a recognizer that never ran.
    macro_rules! sc_refuse {
        ($($arg:tt)*) => {{
            if crate::diag::backedge_trace_enabled() {
                eprintln!("[tir-short-circuit] {at:?}: {}", format!($($arg)*));
            }
            return None;
        }};
    }

    let link_of = |b: BlockId| -> Option<(BlockId, BlockId)> {
        let term = &block_of(func, b).ok()?.body.last()?.inst;
        let Inst::CondBr {
            then_target,
            else_target,
            ..
        } = term
        else {
            return None;
        };
        (then_target != else_target).then_some((*then_target, *else_target))
    };

    if link_of(at).is_none() {
        sc_refuse!("the entry does not end in a two-target CondBr");
    }
    // KAHN's ORDER, not a plain BFS: append a candidate only once ALL of its
    // predecessors are already in `order`. A plain BFS is NOT topological here
    // and that silently destroyed the answer — trust-ir lowers a MIR `Assert` to
    // a `CondBr`, so the assert guard right after the condition looks like a link
    // and a BFS enqueues it BEFORE the chain's last link. The good region is then
    // no longer a PREFIX of the order, every prefix containing it fails the
    // forward test, and the search settles on a two-block region that is correct
    // but useless. Measured on `maximal_suffix`: BFS gave [6,7,8,10,9,...] and
    // picked [6,7]; Kahn gives [6,7,8,9,10,...] and picks [6,7,8,9].
    let mut order: Vec<BlockId> = vec![at];
    while order.len() < MAX_REGION {
        let mut next: Option<BlockId> = None;
        'scan: for b in &order {
            let (t, e) = link_of(*b).expect("only links are enqueued");
            for succ in [t, e] {
                // The HEADER and the LATCH are both in `loop_set` by construction
                // (`natural_loop_blocks` inserts them), and a tail-diamond latch
                // ends in a `CondBr`, so `link_of` accepts it. Absorbing either
                // swallows the very back-edge under obligation — and since the
                // search keeps the LARGEST valid prefix, it actively prefers the
                // region that does. The sibling predicate `triangle_join` opens by
                // excluding both; so does this one.
                if succ == header
                    || succ == latch
                    || order.contains(&succ)
                    || !loop_set.contains(&succ)
                    || link_of(succ).is_none()
                {
                    continue;
                }
                if preds
                    .get(&succ)
                    .is_some_and(|ps| ps.iter().all(|p| order.contains(p)))
                {
                    next = Some(succ);
                    break 'scan;
                }
            }
        }
        match next {
            Some(n) => order.push(n),
            None => break,
        }
    }

    let exits_of = |region: &[BlockId]| -> Vec<BlockId> {
        let mut exits: Vec<BlockId> = Vec::new();
        for b in region {
            let (t, e) = link_of(*b).expect("only links are enqueued");
            for succ in [t, e] {
                if !region.contains(&succ) && !exits.contains(&succ) {
                    exits.push(succ);
                }
            }
        }
        exits
    };

    // The LARGEST valid prefix: a shorter one is also a correct region but leaves
    // the rest of the chain as an arm that branches, which is the refusal this
    // exists to clear. The FULL closure is wrong — it runs past the end of the
    // condition into the next `else if` and lands on three exits.
    let mut best: Option<usize> = None;
    for k in 2..=order.len() {
        let region = &order[..k];
        if region[1..].iter().any(|b| {
            !block_of(func, *b).is_ok_and(|blk| blk.params.is_empty())
                || !preds
                    .get(b)
                    .is_some_and(|ps| ps.iter().all(|p| region.contains(p)))
        }) {
            continue;
        }
        if region.iter().enumerate().any(|(idx, b)| {
            let (t, e) = link_of(*b).expect("only links are enqueued");
            [t, e].iter().any(|succ| {
                region
                    .iter()
                    .position(|x| x == succ)
                    .is_some_and(|j| j <= idx)
            })
        }) {
            continue;
        }
        if exits_of(region).len() == 2 {
            best = Some(k);
        }
    }
    let Some(k) = best else {
        if crate::diag::backedge_trace_enabled() {
            for j in 2..=order.len() {
                eprintln!(
                    "[tir-short-circuit] {at:?}: prefix {:?} -> exits {:?} params_ok={}",
                    &order[..j],
                    exits_of(&order[..j]),
                    order[1..j]
                        .iter()
                        .all(|b| block_of(func, *b).is_ok_and(|blk| blk.params.is_empty()))
                );
            }
        }
        sc_refuse!("no prefix of the link BFS {order:?} is a closed 2-exit region");
    };
    let region: Vec<BlockId> = order[..k].to_vec();

    // Every region edge into a given exit must carry the same arguments, so
    // there is ONE value to thread however the region was traversed.
    let exits = exits_of(&region);
    let mut args: [Option<&'f [ValueId]>; 2] = [None, None];
    for b in &region {
        let Some(Inst::CondBr {
            then_target,
            then_args,
            else_target,
            else_args,
            ..
        }) = block_of(func, *b)
            .ok()
            .and_then(|blk| blk.body.last())
            .map(|n| &n.inst)
        else {
            sc_refuse!("{b:?} is not a CondBr on the second pass");
        };
        for (target, edge) in [(then_target, then_args), (else_target, else_args)] {
            let Some(slot) = exits.iter().position(|x| x == target) else {
                continue;
            };
            match args[slot] {
                Some(prev) if prev != edge.as_slice() => sc_refuse!(
                    "edges into {target:?} disagree: {prev:?} vs {:?}",
                    edge.as_slice()
                ),
                _ => args[slot] = Some(edge.as_slice()),
            }
        }
    }
    let ([Some(a0), Some(a1)], [e0, e1]) = (args, [exits[0], exits[1]]) else {
        sc_refuse!("an exit of {region:?} is reached by no region edge");
    };
    if crate::diag::backedge_trace_enabled() {
        eprintln!(
            "[tir-short-circuit] {at:?}: region {region:?} -> {e0:?}{a0:?} | {e1:?}{a1:?} \
             (in-loop: {} {})",
            loop_set.contains(&e0),
            loop_set.contains(&e1)
        );
    }
    Some((region, [(e0, a0), (e1, a1)]))
}

/// The SmtExpr under which a short-circuit region reaches `exit`: `reach(entry)`
/// is `true`, and for an edge `p -> s` under `c`, `reach(s) |= reach(p) & c`.
/// `region` is in topological order, so one accumulating pass is a fixpoint.
///
/// Every path through the region leaves by exactly one of its two exits, so the
/// other exit's condition is this one's negation — which is why the diamond only
/// needs the one.
fn short_circuit_taken(
    env: &mut Env,
    func: &Function,
    region: &[BlockId],
    exit: BlockId,
) -> Result<SmtExpr, String> {
    let mut reach: HashMap<BlockId, Option<SmtExpr>> = HashMap::new();
    reach.insert(region[0], None); // `None` is the constant `true`.
    for b in region {
        let Some(Inst::CondBr {
            cond,
            then_target,
            else_target,
            ..
        }) = block_of(func, *b)?.body.last().map(|n| &n.inst)
        else {
            return Err(format!("short-circuit region block {b:?} is not a CondBr"));
        };
        // `cond != 0` is the THEN edge, mirroring `Inst::CondBr` everywhere else.
        let c = env
            .resolve(*cond, 1)?
            .eq_expr(SmtExpr::bv_const(0, 1))
            .not_expr();
        let here = reach.get(b).cloned().flatten();
        for (succ, edge) in [
            (*then_target, c.clone()),
            (*else_target, c.clone().not_expr()),
        ] {
            let leg = match &here {
                None => edge,
                Some(r) => r.clone().and_expr(edge),
            };
            let merged = match reach.get(&succ).cloned() {
                Some(Some(prev)) => prev.or_expr(leg),
                Some(None) => {
                    return Err(format!(
                        "short-circuit region reaches {succ:?} unconditionally \
                         ({:?} is not its sole entry)",
                        region[0]
                    ));
                }
                None => leg,
            };
            reach.insert(succ, Some(merged));
        }
    }
    reach
        .get(&exit)
        .cloned()
        .flatten()
        .ok_or_else(|| format!("short-circuit region builds no condition for exit {exit:?}"))
}

/// Model a 2-way diamond inside the loop, INDEPENDENTLY of the MIR spec: both
/// arms must be single straight-line blocks reconverging at ONE join block;
/// each join param is bound to `ite(cond, then_arg, else_arg)` over the EMITTED
/// trust-ir arm args (the bridge's chosen merge values), and the join block id
/// is returned for the caller to resume the path walk from.
///
/// SOUNDNESS: the merged value is derived from the EMITTED block args at the
/// join (not from any spec), so the back-edge equality VC `bridge == mir` stays
/// a genuine check, never a tautology. Every shape outside a single 2-way
/// reconverging diamond (nested diamond, an arm with its own branch/back-edge,
/// non-reconverging arms, a >2-way switch) returns `Err` (fail closed: the
/// structural P1.3 gate stays authoritative).
///
/// `taken` is the ALREADY-RESOLVED, Bool-sorted predicate "the THEN edge is the
/// one taken", supplied by the caller so this one modeler serves both branch
/// primitives the bridge emits:
///   * `Inst::CondBr` — `taken = cond != 0` (a 1-bit discriminant);
///   * `Inst::Switch`  — `taken = OR_i (selector == case_value_i)` over the case
///     values that reach the THEN side (an INTEGER discriminant; the shape
///     rustc's inlined `checked_div`/`checked_rem` zero-guard lowers to).
///
/// Resolving it in the caller keeps the SSA read order unchanged: the selector is
/// defined before the terminator, and the arms only ADD bindings.
#[allow(clippy::too_many_arguments)] // Explicit graph roles keep this proof boundary auditable.
fn model_in_loop_diamond(
    env: &mut Env,
    func: &Function,
    loop_set: &HashSet<BlockId>,
    header: BlockId,
    latch: BlockId,
    diamond_entry: BlockId,
    taken: SmtExpr,
    then_target: BlockId,
    then_args: &[ValueId],
    else_target: BlockId,
    else_args: &[ValueId],
) -> Result<BlockId, String> {
    // The two arms must reconverge at one join. One edge may reach that join
    // directly; the arm walker then contributes that edge's incoming values.
    if then_target == else_target {
        return Err(format!(
            "diamond at {diamond_entry:?} has both arms targeting the same block \
             {then_target:?} (degenerate; out of model)"
        ));
    }
    // Predecessor counts (computed once) let each arm HOP through its own
    // single-predecessor call-return blocks and stop at the shared join.
    let pred_counts = predecessor_counts(func);

    // RULE T — TRIANGLE. Classified from the CFG ALONE, before anything touches
    // `env`: walking an arm and discarding it would leave spurious inputs and
    // opaques behind and make `reject_unmodeled_args` refuse a shape it should
    // have modelled. Neither candidate => today's code path, byte-identical.
    let preds = predecessors_of(func);
    let then_tri = triangle_join(then_target, diamond_entry, header, latch, loop_set, &preds);
    let else_tri = triangle_join(else_target, diamond_entry, header, latch, loop_set, &preds);
    match (then_tri, else_tri) {
        (Some(_), Some(_)) => {
            return Err(format!(
                "diamond at {diamond_entry:?}: BOTH arms classify as the triangle join \
                 (degenerate shape; out of model)"
            ));
        }
        (Some(via), None) => {
            return model_triangle(
                env,
                func,
                loop_set,
                header,
                diamond_entry,
                taken,
                then_target,
                then_args,
                else_target,
                else_args,
                via,
                /*fallthrough_is_then=*/ true,
                &pred_counts,
            );
        }
        (None, Some(via)) => {
            return model_triangle(
                env,
                func,
                loop_set,
                header,
                diamond_entry,
                taken,
                else_target,
                else_args,
                then_target,
                then_args,
                via,
                /*fallthrough_is_then=*/ false,
                &pred_counts,
            );
        }
        (None, None) => {}
    }

    // Both arms are walked with `allow_header_join=false`: over the natural-loop
    // set an arm that reaches the header can only be the latch (the theorem in
    // `model_diamond_arm`'s doc), so it is refused inside the arm walk with that
    // reason. Consequently neither arm's `join` is the header past this point.
    //
    // HISTORY, so nobody rebuilds it: this function used to walk both arms with
    // `true` and classify a single header-reaching arm as an early `continue`,
    // threading the OTHER arm's args into the join with no `ite`. A guard
    // (`early.via == latch`) sat in front of that admit path, and by the theorem
    // it fired on every entry — the path never ran once. Had it run it would
    // have been WRONG (the branch condition was dropped, so the join's values
    // were bound to one arm's regardless of which edge was taken), which is why
    // the MIR-side mirror it cited was removed as unsound. The refusal is now
    // stated once, where it is decided.
    let then_arm = model_diamond_arm(
        env,
        func,
        loop_set,
        header,
        diamond_entry,
        then_target,
        then_args,
        &pred_counts,
        /*allow_header_join=*/ false,
    )?;
    let else_arm = model_diamond_arm(
        env,
        func,
        loop_set,
        header,
        diamond_entry,
        else_target,
        else_args,
        &pred_counts,
        /*allow_header_join=*/ false,
    )?;
    if then_arm.join != else_arm.join {
        return Err(format!(
            "diamond at {diamond_entry:?} arms do not reconverge: then -> {:?}, else -> {:?} \
             (non-reconverging branch is out of model)",
            then_arm.join, else_arm.join
        ));
    }
    let join_id = then_arm.join;
    if !loop_set.contains(&join_id) {
        return Err(format!(
            "diamond at {diamond_entry:?} reconverges outside the loop at {join_id:?}"
        ));
    }
    let join_block = block_of(func, join_id)?;
    // Both arms thread to the SAME join params; merge each slot with an `ite`
    // over the EMITTED arm values, then bind the merged value into the join
    // param. (The bridge realizes the merge as join block-params; we reconstruct
    // its value `ite(cond, then_arg, else_arg)` from the arm edges.)
    if then_arm.join_args.len() != join_block.params.len()
        || else_arm.join_args.len() != join_block.params.len()
    {
        return Err(format!(
            "diamond join {join_id:?} has {} param(s) but arms thread {} (then) / {} (else)",
            join_block.params.len(),
            then_arm.join_args.len(),
            else_arm.join_args.len()
        ));
    }
    for (slot, (pv, pty)) in join_block.params.iter().enumerate() {
        let w = ty_bit_width(pty).ok_or_else(|| {
            format!("join param {pv:?} has a non-scalar type {pty:?} (out of model)")
        })?;
        let then_val = env.resolve(then_arm.join_args[slot], w)?;
        let else_val = env.resolve(else_arm.join_args[slot], w)?;
        // `ite(taken, then, else)` — the bridge's merge value for this slot.
        let merged = SmtExpr::ite(taken.clone(), then_val, else_val);
        env.vals.insert(*pv, merged);
    }
    Ok(join_id)
}

/// The values a tail-diamond arm threads to the HEADER's params, in slot order.
/// A `target == header` arm is a trivial fall-through: its edge args ARE the
/// header-threaded values. Otherwise it is a straight-line single-predecessor
/// chain that Brs to the header (REUSING `model_diamond_arm` with
/// `allow_header_join=true`, requiring the join to be the header).
#[allow(clippy::too_many_arguments)]
fn tail_arm_header_args(
    env: &mut Env,
    func: &Function,
    loop_set: &HashSet<BlockId>,
    header: BlockId,
    latch: BlockId,
    edge_target: BlockId,
    edge_args: &[ValueId],
    pred_counts: &HashMap<BlockId, usize>,
) -> Result<Vec<ValueId>, String> {
    if edge_target == header {
        return Ok(edge_args.to_vec());
    }
    let arm = model_diamond_arm(
        env,
        func,
        loop_set,
        header,
        latch,
        edge_target,
        edge_args,
        pred_counts,
        /*allow_header_join=*/ true,
    )?;
    if arm.join != header {
        return Err(format!(
            "tail diamond arm at {edge_target:?} reconverges at {:?}, not the header {header:?}",
            arm.join
        ));
    }
    Ok(arm.join_args)
}

/// Model a bool 2-way TAIL diamond at the latch (a `CondBr` whose BOTH arms
/// reconverge at the header) as the back-edge args: each header slot becomes
/// `ite(cond != 0, then_value, else_value)` over the EMITTED arm values, matching
/// the MIR SPEC's `select(cond, then, else)`. Fail-closed on any shape whose arms
/// do not both reach the header (e.g. a bottom loop-guard whose else-arm exits:
/// the exit block is not in `loop_set`, so `model_diamond_arm` rejects it).
#[allow(clippy::too_many_arguments)]
fn model_tail_diamond(
    env: &mut Env,
    func: &Function,
    loop_set: &HashSet<BlockId>,
    header: BlockId,
    latch: BlockId,
    cond: ValueId,
    then_target: BlockId,
    then_args: &[ValueId],
    else_target: BlockId,
    else_args: &[ValueId],
    slot_widths: &[u32],
) -> Result<Vec<SmtExpr>, String> {
    // Resolve `cond` BEFORE walking the arms. SSA makes this order-independent
    // (`cond` is defined before the latch terminator); the arms only ADD
    // bindings, so a future reorder that relied on arm-defined state would be
    // unsound — keep the resolve here.
    let cond_expr = env.resolve(cond, 1)?;
    if then_target == else_target {
        return Err(format!(
            "tail diamond at {latch:?} has both arms targeting the same block {then_target:?}"
        ));
    }
    let pred_counts = predecessor_counts(func);
    // The tail-arm blocks are NOT in `loop_set` (the natural-loop backward walk
    // stops at the header). Widen the in-loop membership gate to the true cyclic
    // region for the arm walk; a `break`/exit arm (cannot reach the header) is NOT
    // added and stays fail-closed.
    let arm_loop_set = tail_arm_loop_blocks(func, header, latch, loop_set);
    let then_join_args = tail_arm_header_args(
        env,
        func,
        &arm_loop_set,
        header,
        latch,
        then_target,
        then_args,
        &pred_counts,
    )?;
    let else_join_args = tail_arm_header_args(
        env,
        func,
        &arm_loop_set,
        header,
        latch,
        else_target,
        else_args,
        &pred_counts,
    )?;
    if then_join_args.len() != slot_widths.len() || else_join_args.len() != slot_widths.len() {
        return Err(format!(
            "tail diamond at {latch:?}: arms thread {} (then) / {} (else) args to a header \
             with {} params",
            then_join_args.len(),
            else_join_args.len(),
            slot_widths.len()
        ));
    }
    // `cond != 0` is the THEN edge, mirroring `Inst::CondBr` and the SPEC
    // `select(cond, then, else)`.
    let taken = cond_expr.eq_expr(SmtExpr::bv_const(0, 1)).not_expr();
    let mut out = Vec::with_capacity(slot_widths.len());
    for (slot, w) in slot_widths.iter().enumerate() {
        let t = env.resolve(then_join_args[slot], *w)?;
        let e = env.resolve(else_join_args[slot], *w)?;
        out.push(SmtExpr::ite(taken.clone(), t, e));
    }
    Ok(out)
}

/// Walk the unique in-loop path `header -> ... -> latch` of `func` and return
/// the latch's back-edge block arguments (to `header`) as symbolic values over
/// the caller-supplied `bindings` (header-parameter / loop-invariant ValueIds
/// mapped to named input variables of a given width).
///
/// Fails (caller fails closed) on every shape outside the exact model: see the
/// module header for the list. `bindings` entries for ValueIds that are
/// re-defined along the path are harmlessly shadowed by the definition (SSA
/// dominance means any USE of such a value can only see the definition).
pub fn model_back_edge_args(
    func: &Function,
    header: BlockId,
    latch: BlockId,
    bindings: &[(ValueId, String, u32)],
    identity_calls: &HashSet<FuncId>,
) -> Result<BackEdgeModel, String> {
    model_back_edge_args_with_types(func, header, latch, bindings, identity_calls, &[])
}

/// [`model_back_edge_args`] with the module's type table, so `ExtractField` over
/// `Ty::Array(lane, n)` can width-type its result. The bridge calls this one.
pub fn model_back_edge_args_with_types(
    func: &Function,
    header: BlockId,
    latch: BlockId,
    bindings: &[(ValueId, String, u32)],
    identity_calls: &HashSet<FuncId>,
    types: &[Ty],
) -> Result<BackEdgeModel, String> {
    let loop_set = natural_loop_blocks(func, header, latch);
    let header_block = block_of(func, header)?;

    let mut env = Env {
        vals: HashMap::new(),
        untyped: HashSet::new(),
        abstract_untyped: false,
        inputs: Vec::new(),
        types: types.to_vec(),
        opaque_counter: 0,
        identity_calls: identity_calls.clone(),
        unmodeled_opaques: HashSet::new(),
        alloca_opaques: HashSet::new(),
        mem: Vec::new(),
        mem_poisoned: false,
    };
    for (v, name, w) in bindings {
        env.declare_input(name, *w)?;
        env.vals.insert(*v, SmtExpr::var(name.clone(), *w));
    }

    // Header-parameter slot widths: the widths the final back-edge args are
    // resolved at.
    let mut slot_widths = Vec::with_capacity(header_block.params.len());
    for (pv, pty) in &header_block.params {
        let w = ty_bit_width(pty).ok_or_else(|| {
            format!("header param {pv:?} has a non-scalar type {pty:?} (out of model)")
        })?;
        slot_widths.push(w);
    }

    let mut cur = header;
    let mut visited: HashSet<BlockId> = HashSet::new();
    loop {
        if !visited.insert(cur) {
            return Err(format!(
                "loop path revisits block {cur:?} (nested loop or irreducible shape)"
            ));
        }
        let blk = block_of(func, cur)?;
        let Some((term, body)) = blk.body.split_last() else {
            return Err(format!("block {cur:?} is empty"));
        };
        // Store-to-load forwarding is confined to ONE block (see `Env::mem`).
        env.clear_memory_window();
        for node in body {
            exec_inst(&mut env, &node.inst, &node.results)?;
        }

        // Terminator: either the back-edge (done) or the unique in-loop step.
        let (next, next_args): (BlockId, &[ValueId]) = match &term.inst {
            Inst::Br { target, args } => {
                if cur == latch {
                    if *target != header {
                        return Err(format!(
                            "latch {latch:?} branches to {target:?}, not the header {header:?}"
                        ));
                    }
                    if args.len() != slot_widths.len() {
                        return Err(format!(
                            "back-edge passes {} arg(s) to a header with {} param(s)",
                            args.len(),
                            slot_widths.len()
                        ));
                    }
                    let mut out = Vec::with_capacity(args.len());
                    for (a, w) in args.iter().zip(&slot_widths) {
                        out.push(env.resolve(*a, *w)?);
                    }
                    reject_unmodeled_args(&env, &out)?;
                    return Ok(BackEdgeModel {
                        args: out,
                        extra_inputs: env.inputs,
                    });
                }
                if *target == header {
                    return Err(format!(
                        "block {cur:?} takes a back-edge to the header before the latch"
                    ));
                }
                (*target, args.as_slice())
            }
            Inst::CondBr {
                cond,
                then_target,
                then_args,
                else_target,
                else_args,
            } => {
                if cur == latch {
                    // TAIL DIAMOND at the latch: `for/while { ...; if cond { ... } }`.
                    // Both arms reconverge at the HEADER (one may be the header
                    // directly, the other a straight-line chain that Brs to the
                    // header). Model each header slot as `ite(cond, then, else)`. A
                    // CondBr at the latch whose arms do NOT both reach the header
                    // (e.g. a bottom loop-guard whose else exits) stays fail-closed
                    // inside the helper.
                    let args = model_tail_diamond(
                        &mut env,
                        func,
                        &loop_set,
                        header,
                        latch,
                        *cond,
                        *then_target,
                        then_args,
                        *else_target,
                        else_args,
                        &slot_widths,
                    )?;
                    reject_unmodeled_args(&env, &args)?;
                    return Ok(BackEdgeModel {
                        args,
                        extra_inputs: env.inputs,
                    });
                }
                let then_in = loop_set.contains(then_target) && *then_target != header;
                let else_in = loop_set.contains(else_target) && *else_target != header;
                match (then_in, else_in) {
                    (true, false) => (*then_target, then_args.as_slice()),
                    (false, true) => (*else_target, else_args.as_slice()),
                    (true, true) => {
                        // A 2-WAY DIAMOND inside the loop. Model it: both arms
                        // must be single straight-line blocks that RECONVERGE at
                        // one join block; merge each join param via
                        // `ite(cond, then_arg, else_arg)` and continue from the
                        // join. Any shape outside that (nested diamond, an arm
                        // with its own branch/back-edge, non-reconverging arms)
                        // is rejected (Err -> caller fails closed). This binds
                        // the join params into `env` and advances `cur`/`visited`
                        // directly, so the outer loop resumes at the join.
                        // `cond != 0` is the THEN edge, mirroring `Inst::CondBr`.
                        // Resolved BEFORE walking the arms (SSA: the cond is
                        // defined before the terminator; the arms only ADD
                        // bindings, so a reorder that relied on arm-defined state
                        // would be unsound).
                        // COMPOUND GUARD — a `&&`/`||` chain is ONE source
                        // branch lowered to a CHAIN of CondBrs. When its two
                        // exits split one in-loop / one out-of-loop it is a
                        // GUARD, not a diamond, and the single-CondBr guard rule
                        // above applies unchanged. Classified from the CFG ALONE
                        // before anything touches `env`, on the same discipline
                        // as Rule T: a walk that is then discarded would leave
                        // spurious inputs and opaques behind.
                        if let Some((region, exits)) = short_circuit_region(
                            func,
                            &loop_set,
                            header,
                            latch,
                            cur,
                            &predecessors_of(func),
                        ) {
                            // The interior runs UNCONDITIONALLY. Value-correct
                            // because trust-ir is SSA — a use is dominated by its
                            // definition and the region is walked in topological
                            // order — and because a region block carries no params
                            // (a clause of the recognizer), so nothing needs a
                            // merge on the way in.
                            for b in &region[1..] {
                                let blk = block_of(func, *b)?;
                                let Some((_, body)) = blk.body.split_last() else {
                                    return Err(format!("block {b:?} is empty"));
                                };
                                env.clear_memory_window();
                                for node in body {
                                    exec_inst(&mut env, &node.inst, &node.results)?;
                                }
                            }
                            let [(e0, a0), (e1, a1)] = exits;
                            let e0_in = loop_set.contains(&e0) && e0 != header;
                            let e1_in = loop_set.contains(&e1) && e1 != header;
                            match (e0_in, e1_in) {
                                // COMPOUND GUARD — only one exit can reach THIS
                                // back-edge, so the other contributes nothing and
                                // the survivor is the only continuation.
                                (true, false) => (e0, a0),
                                (false, true) => (e1, a1),
                                // COMPOUND DIAMOND — both exits are live, so the
                                // collapsed condition IS the diamond's condition
                                // and the two exits ARE its arms. Handing the raw
                                // CondBr arms to the diamond model instead is what
                                // fails: an arm of a `&&`/`||` chain is another
                                // link of the chain, not an arm.
                                (true, true) => {
                                    let taken = short_circuit_taken(&mut env, func, &region, e0)?;
                                    let join = model_in_loop_diamond(
                                        &mut env, func, &loop_set, header, latch, cur, taken, e0,
                                        a0, e1, a1,
                                    )?;
                                    cur = join;
                                    continue;
                                }
                                (false, false) => {
                                    return Err(format!(
                                        "short-circuit region at {cur:?} has no in-loop exit \
                                         toward the latch"
                                    ));
                                }
                            }
                        } else {
                            let taken = env
                                .resolve(*cond, 1)?
                                .eq_expr(SmtExpr::bv_const(0, 1))
                                .not_expr();
                            let join = model_in_loop_diamond(
                                &mut env,
                                func,
                                &loop_set,
                                header,
                                latch,
                                cur,
                                taken,
                                *then_target,
                                then_args,
                                *else_target,
                                else_args,
                            )?;
                            // Resume the path walk at the join. The top of the loop
                            // re-checks `visited`, so a join that re-enters the path
                            // (== an already-walked block) is caught there as an
                            // irreducible/nested shape.
                            cur = join;
                            continue;
                        }
                    }
                    (false, false) => {
                        return Err(format!(
                            "block {cur:?} has no in-loop successor toward the latch"
                        ));
                    }
                }
            }
            Inst::Switch {
                value,
                default,
                default_args,
                cases,
                ..
            } => {
                if cur == latch {
                    return Err("latch ends in a switch (out of model)".to_string());
                }
                // Collect every in-loop edge (target + args + the case values that
                // reach it; an EMPTY value list marks the `default` edge).
                let mut candidates: Vec<(BlockId, &[ValueId])> = Vec::new();
                candidates.push((*default, default_args.as_slice()));
                for c in cases {
                    candidates.push((c.target, c.args.as_slice()));
                }
                candidates.retain(|(t, _)| loop_set.contains(t) && *t != header);
                let Some(&(first_t, first_a)) = candidates.first() else {
                    return Err(format!(
                        "block {cur:?} switch has no in-loop successor toward the latch"
                    ));
                };
                if !candidates
                    .iter()
                    .any(|(t, a)| *t != first_t || *a != first_a)
                {
                    // Every in-loop edge agrees on ONE target with identical args:
                    // an unambiguous single continuation (unchanged behavior).
                    (first_t, first_a)
                } else {
                    // TWO distinct in-loop successors: an integer-discriminant
                    // 2-WAY DIAMOND. This is what rustc's inlined
                    // `checked_div`/`checked_rem` zero-guard lowers to — the bridge
                    // emits `Inst::Switch` (not `CondBr`) for a non-bool selector
                    // (see the `SwitchInt` lowering), so without this arm the whole
                    // class was unreachable for the threading VC.
                    //
                    // GATE (mirrors the MIR spec side): the switch's FULL distinct
                    // successor set must be EXACTLY those two blocks. A third,
                    // out-of-loop successor would mean some selector values leave
                    // the loop here, and a 2-way `ite` is then not an exact model of
                    // which edge was taken — fail closed instead.
                    const MAX_SWITCH_CASES: usize = 4;
                    if cases.len() > MAX_SWITCH_CASES {
                        return Err(format!(
                            "block {cur:?} switch has {} cases (over the {MAX_SWITCH_CASES} \
                             modeled-diamond bound)",
                            cases.len()
                        ));
                    }
                    let mut distinct: Vec<(BlockId, &[ValueId])> =
                        vec![(*default, default_args.as_slice())];
                    for c in cases {
                        match distinct.iter().find(|(t, _)| *t == c.target) {
                            Some((_, a)) if *a == c.args.as_slice() => {}
                            Some(_) => {
                                return Err(format!(
                                    "block {cur:?} switch threads different args to the same \
                                     target {:?} (out of model)",
                                    c.target
                                ));
                            }
                            None => distinct.push((c.target, c.args.as_slice())),
                        }
                    }
                    if distinct.len() != 2 {
                        return Err(format!(
                            "block {cur:?} switch has {} distinct successors (only a 2-way \
                             in-loop diamond is modeled)",
                            distinct.len()
                        ));
                    }
                    if distinct
                        .iter()
                        .any(|(t, _)| !loop_set.contains(t) || *t == header)
                    {
                        return Err(format!(
                            "block {cur:?} switch does not have BOTH arms forward-in-loop \
                             (out of model)"
                        ));
                    }
                    // THEN = the CASE arm, ELSE = the default arm. With exactly
                    // two distinct successors and the default being one of them,
                    // each explicit case value targets EITHER the case arm or
                    // (aliasing) the default arm, so the predicate is folded
                    // ONLY over the cases whose target is the case arm:
                    //   case arm taken  <=>  some case value WITH THAT TARGET
                    //                        matches.
                    // (An earlier revision of this comment claimed every case
                    // value targets the case arm. That is false — a switch may
                    // alias a case back to the default — and the fold below has
                    // always filtered on `target == then_target`, so the code
                    // was right and only the comment overclaimed. Adversarial
                    // review 2026-08-31.)
                    //
                    // This orientation is not arbitrary: it is the one the MIR
                    // SPEC side uses (`vc_diamond_shape` puts the case side in
                    // `then`), and matching it lets the whole slot expression come
                    // out SYNTACTICALLY IDENTICAL on both sides, which
                    // `edge_equality_holds_structurally` discharges as a proof with
                    // no solver at all.
                    let (else_target, else_args) = distinct[0];
                    let (then_target, then_args) = distinct[1];
                    // The selector width is not on the instruction; take it from
                    // the binding the walk already has. An UNBOUND selector has no
                    // derivable width — fail closed rather than guess one.
                    let w = env.bound_width(*value).ok_or_else(|| {
                        format!(
                            "block {cur:?} switch selector {value:?} has no modeled width \
                             (out of model)"
                        )
                    })?;
                    if w > 128 {
                        return Err(format!(
                            "block {cur:?} switch selector is {w} bits wide (out of model)"
                        ));
                    }
                    // Resolved BEFORE the arms are walked (same SSA read-order
                    // discipline as the `CondBr` diamond).
                    let selector = env.resolve(*value, w)?;
                    // Build the predicate in the SAME 1-bit "bool carrier" domain
                    // the MIR spec encoder uses — one `ite(sel == v, 1, 0)` per
                    // case value, `bvor`-folded, then compared `!= 0` — so the two
                    // independently-derived expressions come out term-identical on
                    // a correct lowering. This mirrors `mir_semantics`' `bool1` +
                    // `encode_mir_select` exactly; it is a sort round-trip, not an
                    // assumption, and a swapped arm / wrong case value / stale arg
                    // still changes the term and refutes.
                    let mut sel_bit: Option<SmtExpr> = None;
                    for c in cases {
                        let v = match c.value {
                            Constant::Int(v) => v as u128,
                            Constant::U128(v) if w == 128 && v > i128::MAX as u128 => v,
                            _ => {
                                return Err(format!(
                                    "block {cur:?} switch has an unsupported case value (out of model)"
                                ));
                            }
                        };
                        if c.target != then_target {
                            continue;
                        }
                        // Two's-complement truncation to the selector width — the
                        // same conversion `Inst::Const` applies to a case constant.
                        let constant = if w == 128 {
                            crate::mir_semantics::encode_u128_constant(v)
                        } else {
                            SmtExpr::bv_const(v as u64, w)
                        };
                        let bit = SmtExpr::ite(
                            selector.clone().eq_expr(constant),
                            SmtExpr::bv_const(1, 1),
                            SmtExpr::bv_const(0, 1),
                        );
                        sel_bit = Some(match sel_bit {
                            Some(a) => a.bvor(bit),
                            None => bit,
                        });
                    }
                    let taken = sel_bit
                        .ok_or_else(|| {
                            format!(
                                "block {cur:?} switch: no case value reaches the modeled `then` \
                                 arm (out of model)"
                            )
                        })?
                        .eq_expr(SmtExpr::bv_const(0, 1))
                        .not_expr();
                    let join = model_in_loop_diamond(
                        &mut env,
                        func,
                        &loop_set,
                        header,
                        latch,
                        cur,
                        taken,
                        then_target,
                        then_args,
                        else_target,
                        else_args,
                    )?;
                    cur = join;
                    continue;
                }
            }
            other => {
                return Err(format!(
                    "block {cur:?} ends in an unsupported terminator for the loop-path model: {other:?}"
                ));
            }
        };

        if !loop_set.contains(&next) {
            return Err(format!(
                "loop path leaves the loop at {cur:?} -> {next:?} before reaching the latch"
            ));
        }
        // Thread the edge's block arguments into the successor's parameters.
        let next_block = block_of(func, next)?;
        if next_block.params.len() != next_args.len() {
            return Err(format!(
                "edge {cur:?} -> {next:?} passes {} arg(s) to a block with {} param(s)",
                next_args.len(),
                next_block.params.len()
            ));
        }
        for ((pv, pty), av) in next_block.params.iter().zip(next_args) {
            let w = ty_bit_width(pty).ok_or_else(|| {
                format!("block param {pv:?} has a non-scalar type {pty:?} (out of model)")
            })?;
            let e = env.resolve(*av, w)?;
            env.vals.insert(*pv, e);
        }
        cur = next;
    }
}

/// Independently enumerate every CFG path from the header to one direct latch.
/// Accept only when each path produces identical expressions over the supplied
/// header bindings. Conditions impose NO assumptions. Loads stay opaque and all
/// memory forwarding is disabled. Thus an irrelevant load or nested branch can
/// coexist with an unconditional proof of scalar threading; a load-dependent
/// result, path disagreement, nested cycle or exhausted budget is rejected.
/// This does not prove branch reachability or memory semantics.
pub fn model_back_edge_args_all_paths(
    func: &Function,
    header: BlockId,
    latch: BlockId,
    bindings: &[(ValueId, String, u32)],
) -> Result<BackEdgeModel, String> {
    model_back_edge_args_all_paths_with_types(func, header, latch, bindings, &[])
}

/// Path consensus with the module's nominal type table available to the encoder.
pub fn model_back_edge_args_all_paths_with_types(
    func: &Function,
    header: BlockId,
    latch: BlockId,
    bindings: &[(ValueId, String, u32)],
    types: &[Ty],
) -> Result<BackEdgeModel, String> {
    let region = natural_loop_blocks(func, header, latch);
    let header_block = block_of(func, header)?;
    let widths: Vec<_> = header_block
        .params
        .iter()
        .map(|(_, ty)| {
            ty_bit_width(ty).ok_or_else(|| "path-consensus header is not scalar".to_owned())
        })
        .collect::<Result<_, _>>()?;
    let mut allowed = HashSet::new();
    let mut bound = HashSet::new();
    for (value, name, width) in bindings {
        let valid = header_block
            .params
            .iter()
            .any(|(param, ty)| param == value && ty_bit_width(ty) == Some(*width));
        if !valid || !bound.insert(*value) || !allowed.insert(name.clone()) {
            return Err(
                "path-consensus bindings must name distinct, width-matched header parameters"
                    .to_owned(),
            );
        }
    }
    let mut env = Env {
        types: types.to_vec(),
        vals: HashMap::new(),
        untyped: HashSet::new(),
        abstract_untyped: true,
        inputs: Vec::new(),
        opaque_counter: 0,
        identity_calls: HashSet::new(),
        unmodeled_opaques: HashSet::new(),
        alloca_opaques: HashSet::new(),
        mem: Vec::new(),
        mem_poisoned: true,
    };
    for (value, name, width) in bindings {
        env.declare_input(name, *width)?;
        env.vals.insert(*value, SmtExpr::var(name.clone(), *width));
    }
    let mut work = vec![(header, env, vec![header])];
    let mut answer: Option<BackEdgeModel> = None;
    let mut visits = 0;
    let mut paths = 0;
    while let Some((current, mut env, path)) = work.pop() {
        visits += 1;
        if visits > 4096 || path.len() > 128 || paths >= 256 {
            return Err("implementation path-consensus traversal budget exceeded".to_owned());
        }
        let block = block_of(func, current)?;
        let (term, body) = block
            .body
            .split_last()
            .ok_or("path-consensus block is empty")?;
        for node in body {
            exec_inst(&mut env, &node.inst, &node.results)?;
        }
        if current == latch {
            let Inst::Br { target, args } = &term.inst else {
                return Err("path-consensus latch is not a direct back-edge".to_owned());
            };
            if *target != header || args.len() != widths.len() {
                return Err("path-consensus latch target or arity mismatch".to_owned());
            }
            let values: Vec<_> = args
                .iter()
                .zip(&widths)
                .map(|(arg, width)| env.resolve(*arg, *width))
                .collect::<Result<_, _>>()?;
            reject_unmodeled_args(&env, &values)?;
            if values
                .iter()
                .any(|v| v.free_vars().iter().any(|name| !allowed.contains(name)))
            {
                return Err(
                    "implementation path-consensus result depends on a non-header value".to_owned(),
                );
            }
            if let Some(expected) = &answer {
                if expected.args != values {
                    return Err(
                        "implementation paths to the latch disagree on threaded values".to_owned(),
                    );
                }
            } else {
                answer = Some(BackEdgeModel {
                    args: values,
                    extra_inputs: env
                        .inputs
                        .iter()
                        .filter(|(name, _)| allowed.contains(name))
                        .cloned()
                        .collect(),
                });
            }
            paths += 1;
            continue;
        }
        let edges: Vec<(BlockId, &[ValueId])> = match &term.inst {
            Inst::Br { target, args } => vec![(*target, args)],
            Inst::CondBr {
                then_target,
                then_args,
                else_target,
                else_args,
                ..
            } => vec![(*then_target, then_args), (*else_target, else_args)],
            Inst::Switch {
                default,
                default_args,
                cases,
                ..
            } => {
                let mut edges = vec![(*default, default_args.as_slice())];
                edges.extend(cases.iter().map(|case| (case.target, case.args.as_slice())));
                edges
            }
            _ => return Err("implementation path-consensus has an unmodeled terminator".to_owned()),
        };
        for (next, args) in edges {
            if next == header || !region.contains(&next) {
                continue;
            }
            if path.contains(&next) {
                return Err("implementation path-consensus contains a nested cycle".to_owned());
            }
            let mut branch = env.clone();
            thread_args_into_params(&mut branch, block_of(func, next)?, args)?;
            let mut next_path = path.clone();
            next_path.push(next);
            work.push((next, branch, next_path));
        }
    }
    answer.ok_or_else(|| "implementation path-consensus has no path to the latch".to_owned())
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{FuncId, FuncTyId, Function, InstrNode, SwitchCase, TyId};

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }
    fn b(n: u32) -> BlockId {
        BlockId::new(n)
    }

    fn empty_fn() -> Function {
        Function::new(FuncId::new(0), "test", FuncTyId::new(0), b(0))
    }

    /// The euclid loop shape as the bridge lowers it (i32, header params
    /// `(a, b)` = (%10, %11)):
    ///
    ///   bb0: br bb1(%0, %1)                      ; preheader (args opaque here)
    ///   bb1(%10: i32, %11: i32):                 ; header
    ///       %2 = const 0
    ///       %3 = icmp ne %11, %2
    ///       condbr %3, bb2(), bb3()              ; bb3 = exit
    ///   bb2:                                      ; latch (folded body)
    ///       %4 = srem %10, %11
    ///       br bb1(%11, %4)                       ; ROTATION: a' = b, b' = a%b
    ///   bb3: return %10
    /// PROVES THE `ExtractField` WIDTH RULE FIRES.
    ///
    /// Without it, a back-edge arg deriving from `ExtractField` on a tuple is
    /// `untyped` and `reject_unmodeled_args` refuses the whole edge with "no
    /// width-typeable result" — measured on
    /// `core::str::pattern::TwoWaySearcher::maximal_suffix`, where `arr.len()` is
    /// `ExtractField { ty: Tuple([I64, I64]), field: 1 }` feeding a bounds check.
    ///
    /// The value stays an OPAQUE; this test pins that it becomes width-typed, not
    /// that it becomes known.
    #[test]
    fn extract_field_on_a_tuple_is_width_typed_not_untyped() {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0));
        bb0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(0)],
        }));
        let mut bb1 = Block::new(b(1)).with_param(v(10), Ty::I64);
        // The aggregate is itself opaque; only its FIELD WIDTH is at issue.
        bb1.body.push(
            InstrNode::new(Inst::Undef {
                ty: Ty::Tuple(vec![Ty::I64, Ty::I64]),
            })
            .with_result(v(20)),
        );
        bb1.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: Ty::Tuple(vec![Ty::I64, Ty::I64]),
                aggregate: v(20),
                field: 1,
            })
            .with_result(v(21)),
        );
        // The back-edge arg DEPENDS on the extracted field.
        bb1.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: v(10),
                rhs: v(21),
            })
            .with_result(v(22)),
        );
        bb1.body.push(InstrNode::new(Inst::Br {
            target: b(2),
            args: vec![v(22)],
        }));
        let mut bb2 = Block::new(b(2)).with_param(v(30), Ty::I64);
        bb2.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(30)],
        }));
        f.blocks.extend([bb0, bb1, bb2]);

        let got = model_back_edge_args(
            &f,
            b(1),
            b(2),
            &[(v(10), "l1".to_string(), 64)],
            &::std::collections::HashSet::new(),
        );
        match got {
            Ok(m) => assert_eq!(m.args.len(), 1, "one header slot"),
            Err(e) => {
                assert!(
                    !e.contains("no width-typeable result"),
                    "the ExtractField width rule did not fire: {e}"
                );
            }
        }
    }

    /// The SAME rule for the `Ty::Array(lane, n)` spelling newer trust-ir uses for
    /// the `{ data, len }` lane tuple, resolved through the module type table.
    /// Measured after the 2026-09-21 merge of `origin/main`: `arr.len()` arrives as
    /// `ExtractField { ty: Array(TyId(3), 2), field: 1 }` and, without the table,
    /// `maximal_suffix` went back to a failed root with "no width-typeable result".
    #[test]
    fn extract_field_on_an_array_lane_tuple_is_width_typed_through_the_type_table() {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0));
        bb0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(0)],
        }));
        let mut bb1 = Block::new(b(1)).with_param(v(10), Ty::I64);
        // The aggregate is itself opaque; only its FIELD WIDTH is at issue.
        bb1.body.push(
            InstrNode::new(Inst::Undef {
                ty: Ty::Array(TyId::new(0), 2),
            })
            .with_result(v(20)),
        );
        bb1.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: Ty::Array(TyId::new(0), 2),
                aggregate: v(20),
                field: 1,
            })
            .with_result(v(21)),
        );
        // The back-edge arg DEPENDS on the extracted field.
        bb1.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: v(10),
                rhs: v(21),
            })
            .with_result(v(22)),
        );
        bb1.body.push(InstrNode::new(Inst::Br {
            target: b(2),
            args: vec![v(22)],
        }));
        let mut bb2 = Block::new(b(2)).with_param(v(30), Ty::I64);
        bb2.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(30)],
        }));
        f.blocks.extend([bb0, bb1, bb2]);

        let got = model_back_edge_args_with_types(
            &f,
            b(1),
            b(2),
            &[(v(10), "l1".to_string(), 64)],
            &::std::collections::HashSet::new(),
            &[Ty::I64],
        );
        match got {
            Ok(m) => assert_eq!(m.args.len(), 1, "one header slot"),
            Err(e) => {
                assert!(
                    !e.contains("no width-typeable result"),
                    "the ExtractField width rule did not fire: {e}"
                );
            }
        }
    }

    /// A TRIANGLE: an `if` with NO else, where the else edge goes STRAIGHT to the
    /// join. Modelled on the MEASURED shape of `core::num::<uN>::overflowing_pow`
    /// (vc-trace of `library/core`: bb15 -> {bb16, bb18}, bb16 -> bb17 -> bb18,
    /// and bb18 is a 2-predecessor in-loop join carrying the arm-varying values
    /// as block params).
    ///
    /// The arm walker has no notion of this shape, so it treats the fall-through
    /// edge as an ARM, walks it through the latch to the header, and refuses it
    /// there as a nested back-edge (`model_diamond_arm` with
    /// `allow_header_join=false`). The refusal is RIGHT about what it sees and
    /// wrong about what it is: bb4 is the join, not an arm.
    ///
    ///   bb0: br bb1(v0, v1)
    ///   bb1(v10 acc, v11 n):  HEADER   condbr (n != 0) -> bb2 | bb6
    ///   bb2:                  triangle entry; condbr (acc > 1) -> bb3 | bb4(v10)
    ///   bb3:                  v6 = acc + n ; br bb4(v6)          THEN arm
    ///   bb4(v12):             JOIN, preds {bb2, bb3} == EXACTLY 2
    ///   bb5(v13, v14):        LATCH -> br bb1
    ///   bb6:                  return
    fn triangle_tir() -> Function {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0));
        bb0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(0), v(1)],
        }));
        let mut bb1 = Block::new(b(1))
            .with_param(v(10), Ty::I32)
            .with_param(v(11), Ty::I32);
        bb1.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(2)),
        );
        bb1.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I32,
                lhs: v(11),
                rhs: v(2),
            })
            .with_result(v(3)),
        );
        bb1.body.push(InstrNode::new(Inst::CondBr {
            cond: v(3),
            then_target: b(2),
            then_args: vec![],
            else_target: b(6),
            else_args: vec![],
        }));
        // Triangle entry: the ELSE edge threads the header param straight to the join.
        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(4)),
        );
        bb2.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Sgt,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(4),
            })
            .with_result(v(5)),
        );
        bb2.body.push(InstrNode::new(Inst::CondBr {
            cond: v(5),
            then_target: b(3),
            then_args: vec![],
            else_target: b(4),
            else_args: vec![v(10)],
        }));
        let mut bb3 = Block::new(b(3));
        bb3.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(11),
            })
            .with_result(v(6)),
        );
        bb3.body.push(InstrNode::new(Inst::Br {
            target: b(4),
            args: vec![v(6)],
        }));
        let mut bb4 = Block::new(b(4)).with_param(v(12), Ty::I32);
        bb4.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(7)),
        );
        bb4.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I32,
                lhs: v(11),
                rhs: v(7),
            })
            .with_result(v(8)),
        );
        bb4.body.push(InstrNode::new(Inst::Br {
            target: b(5),
            args: vec![v(12), v(8)],
        }));
        let mut bb5 = Block::new(b(5))
            .with_param(v(13), Ty::I32)
            .with_param(v(14), Ty::I32);
        bb5.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(13), v(14)],
        }));
        let mut bb6 = Block::new(b(6));
        bb6.body.push(InstrNode::new(Inst::Return {
            values: vec![v(10)],
        }));
        f.blocks.extend([bb0, bb1, bb2, bb3, bb4, bb5, bb6]);
        f
    }

    /// THE CONTROL for triangle-aware join detection.
    ///
    /// Asserts the model BUILDS and that the fall-through arm contributed the
    /// header param VERBATIM — `ite(cond, acc + n, acc)` — rather than a value the
    /// walk synthesized. Before the fix this Errs with "nested back-edge"; that
    /// exact failure is what distinguishes "the model now builds" from "the
    /// refusal text changed".
    #[test]
    fn triangle_fallthrough_arm_merges_with_ite() {
        let f = triangle_tir();
        let got = model_back_edge_args(
            &f,
            b(1),
            b(5),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        );
        let model = match got {
            Ok(m) => m,
            Err(e) => panic!("triangle must model, got Err: {e}"),
        };
        assert_eq!(model.args.len(), 2, "two header slots");
        match &model.args[0] {
            SmtExpr::Ite {
                then_expr,
                else_expr,
                ..
            } => {
                assert!(
                    matches!(&**then_expr, SmtExpr::BvAdd { .. }),
                    "then arm is acc + n, got {then_expr:?}"
                );
                assert_eq!(
                    **else_expr,
                    SmtExpr::var("l1", 32),
                    "the FALL-THROUGH arm must contribute the header param VERBATIM"
                );
            }
            other => panic!("slot 0 must merge with an ite, got {other:?}"),
        }
    }

    fn euclid_tir() -> Function {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0));
        bb0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(0), v(1)],
        }));
        let mut bb1 = Block::new(b(1))
            .with_param(v(10), Ty::I32)
            .with_param(v(11), Ty::I32);
        bb1.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(2)),
        );
        bb1.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I32,
                lhs: v(11),
                rhs: v(2),
            })
            .with_result(v(3)),
        );
        bb1.body.push(InstrNode::new(Inst::CondBr {
            cond: v(3),
            then_target: b(2),
            then_args: vec![],
            else_target: b(3),
            else_args: vec![],
        }));
        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::SRem,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(11),
            })
            .with_result(v(4)),
        );
        bb2.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(11), v(4)],
        }));
        let mut bb3 = Block::new(b(3));
        bb3.body.push(InstrNode::new(Inst::Return {
            values: vec![v(10)],
        }));
        f.blocks = vec![bb0, bb1, bb2, bb3];
        f
    }

    /// The rotation latch models as `(b, a srem b)` over the bound header vars.
    #[test]
    fn euclid_rotation_models_b_and_rem() {
        let f = euclid_tir();
        let model = model_back_edge_args(
            &f,
            b(1),
            b(2),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect("euclid path must model");
        assert_eq!(model.args.len(), 2);
        // Slot 0 (a') must be EXACTLY the header var l2 (old b).
        assert_eq!(model.args[0], SmtExpr::var("l2", 32));
        // Slot 1 (b') must mention both l1 and l2 (the remainder expression).
        let free = model.args[1].free_vars();
        assert!(free.contains(&"l1".to_string()) && free.contains(&"l2".to_string()));
        // No opaque inputs were needed: the whole path is encoded.
        assert!(
            model
                .extra_inputs
                .iter()
                .all(|(n, _)| !n.starts_with("__tir_op")),
            "no opaque should be minted on the fully-encoded euclid path"
        );
    }

    /// A loop-carried WRAPPING accumulator whose back-edge threads the wrapped
    /// result of an `Inst::Overflow{AddOverflow}` (what `s = s.wrapping_add(x)`
    /// and `s = s + x` under `-Coverflow-checks=on` both lower to) must model the
    /// wrapped value as the EXACT `bvadd` over the header vars — not an opaque.
    /// LOAD-BEARING: before the fix this slot was an opaque input, so a euclid-
    /// class rotation carrying such an accumulator Refuted on correct code.
    ///
    ///   bb1(s=%10, x=%11): guard; condbr bb2/bb3
    ///   bb2: (%4,%5) = AddOverflow(%10,%11); br bb1(%4, %11)   ; s' = s+x ; x kept
    #[test]
    fn overflow_wrapped_result_models_as_bvadd_not_opaque() {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0));
        bb0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(0), v(1)],
        }));
        let mut bb1 = Block::new(b(1))
            .with_param(v(10), Ty::I32)
            .with_param(v(11), Ty::I32);
        bb1.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(2)),
        );
        bb1.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I32,
                lhs: v(11),
                rhs: v(2),
            })
            .with_result(v(3)),
        );
        bb1.body.push(InstrNode::new(Inst::CondBr {
            cond: v(3),
            then_target: b(2),
            then_args: vec![],
            else_target: b(3),
            else_args: vec![],
        }));
        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::Overflow {
                op: OverflowOp::AddOverflow,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(11),
            })
            .with_results([v(4), v(5)]),
        );
        bb2.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(4), v(11)],
        }));
        let mut bb3 = Block::new(b(3));
        bb3.body.push(InstrNode::new(Inst::Return {
            values: vec![v(10)],
        }));
        f.blocks = vec![bb0, bb1, bb2, bb3];

        let model = model_back_edge_args(
            &f,
            b(1),
            b(2),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect("wrapping-accumulator loop must model");
        assert_eq!(model.args.len(), 2);
        // Slot 0 (s') is EXACTLY bvadd(s, x) over the header vars — the fix.
        assert_eq!(
            model.args[0],
            SmtExpr::var("l1", 32).bvadd(SmtExpr::var("l2", 32)),
            "the AddOverflow wrapped result must model as bvadd(l1,l2), got {:?}",
            model.args[0]
        );
        // Slot 1 (x) unchanged.
        assert_eq!(model.args[1], SmtExpr::var("l2", 32));
        // The load-bearing proof it is MODELED, not opaque: no opaque minted.
        assert!(
            model
                .extra_inputs
                .iter()
                .all(|(n, _)| !n.starts_with("__tir_op")),
            "the Overflow wrapped result must be encoded (bvadd), not an opaque input; \
             extra_inputs = {:?}",
            model.extra_inputs
        );
    }

    /// SubOverflow / MulOverflow wrapped results model as bvsub / bvmul.
    #[test]
    fn overflow_sub_mul_wrapped_results_model() {
        /// Build the `s' = OVERFLOW_OP(s, x); x kept` loop for one overflow op.
        fn overflow_loop(op: OverflowOp) -> Function {
            let mut f = empty_fn();
            let mut bb0 = Block::new(b(0));
            bb0.body.push(InstrNode::new(Inst::Br {
                target: b(1),
                args: vec![v(0), v(1)],
            }));
            let mut bb1 = Block::new(b(1))
                .with_param(v(10), Ty::I32)
                .with_param(v(11), Ty::I32);
            bb1.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(0),
                })
                .with_result(v(2)),
            );
            bb1.body.push(
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ne,
                    ty: Ty::I32,
                    lhs: v(11),
                    rhs: v(2),
                })
                .with_result(v(3)),
            );
            bb1.body.push(InstrNode::new(Inst::CondBr {
                cond: v(3),
                then_target: b(2),
                then_args: vec![],
                else_target: b(3),
                else_args: vec![],
            }));
            let mut bb2 = Block::new(b(2));
            bb2.body.push(
                InstrNode::new(Inst::Overflow {
                    op,
                    ty: Ty::I32,
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_results([v(4), v(5)]),
            );
            bb2.body.push(InstrNode::new(Inst::Br {
                target: b(1),
                args: vec![v(4), v(11)],
            }));
            let mut bb3 = Block::new(b(3));
            bb3.body.push(InstrNode::new(Inst::Return {
                values: vec![v(10)],
            }));
            f.blocks = vec![bb0, bb1, bb2, bb3];
            f
        }
        let bindings = [(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)];
        let l1 = SmtExpr::var("l1", 32);
        let l2 = SmtExpr::var("l2", 32);

        let sub = model_back_edge_args(
            &overflow_loop(OverflowOp::SubOverflow),
            b(1),
            b(2),
            &bindings,
            &::std::collections::HashSet::new(),
        )
        .expect("sub-overflow loop must model");
        assert_eq!(
            sub.args[0],
            l1.clone().bvsub(l2.clone()),
            "SubOverflow wrapped result"
        );

        let mul = model_back_edge_args(
            &overflow_loop(OverflowOp::MulOverflow),
            b(1),
            b(2),
            &bindings,
            &::std::collections::HashSet::new(),
        )
        .expect("mul-overflow loop must model");
        assert_eq!(mul.args[0], l1.bvmul(l2), "MulOverflow wrapped result");
    }

    // -----------------------------------------------------------------------
    // OVERFLOW-TUPLE `(iN, bool)` CARRIED ACROSS THE LOOP (the piece-3 gap).
    // The O2/O3 scalarizer lowers `while ... { p = p.0.overflowing_add(k) }` to a
    // header carrying the wrapped value AND the overflow FLAG as separate slots;
    // the latch computes `(w, o) = AddOverflow(p0, k)` and threads `(w, o)` back.
    // The flag now models as the SHARED `overflow_flag_uf`, so the threading is
    // PROVABLE (was: opaque flag => fail-closed).
    // -----------------------------------------------------------------------

    /// The `(s:i32, f:bool)` overflow-tuple loop, as the O2/O3 scalarizer lowers
    /// `while s != 0 { let (s, f) = s.overflowing_add(100); }`:
    ///   bb0: br bb1(%0, %1)                       ; preheader
    ///   bb1(s=%10:i32, f=%11:bool):               ; header
    ///       %2 = const 0; %3 = icmp ne %10, %2; condbr %3, bb2(), bb3()
    ///   bb2:                                       ; latch
    ///       %4 = const 100
    ///       (%5, %6) = AddOverflow(%10, %4)        ; %5 wrapped, %6 flag
    ///       br bb1(<back_args>)                    ; correct = (%5, %6)
    ///   bb3: return %10
    fn ovf_tuple_tir(back_args: Vec<ValueId>) -> Function {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0));
        bb0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(0), v(1)],
        }));
        let mut bb1 = Block::new(b(1))
            .with_param(v(10), Ty::I32)
            .with_param(v(11), Ty::Bool);
        bb1.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(2)),
        );
        bb1.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(2),
            })
            .with_result(v(3)),
        );
        bb1.body.push(InstrNode::new(Inst::CondBr {
            cond: v(3),
            then_target: b(2),
            then_args: vec![],
            else_target: b(3),
            else_args: vec![],
        }));
        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(100),
            })
            .with_result(v(4)),
        );
        bb2.body.push(
            InstrNode::new(Inst::Overflow {
                op: OverflowOp::AddOverflow,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(4),
            })
            .with_results([v(5), v(6)]),
        );
        bb2.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: back_args,
        }));
        let mut bb3 = Block::new(b(3));
        bb3.body.push(InstrNode::new(Inst::Return {
            values: vec![v(10)],
        }));
        f.blocks = vec![bb0, bb1, bb2, bb3];
        f
    }

    /// A `(a && b) || c` CHAIN in the loop body, as the bridge lowers it: THREE
    /// `CondBr` blocks converging on two, not a diamond whose arm branches.
    ///
    ///   bb0: br bb1(%0)
    ///   bb1(%10: i32):                 ; header
    ///       %2 = const 0
    ///       %3 = icmp ne %10, %2
    ///       condbr %3 -> bb2, bb9      ; loop guard (bb9 exits)
    ///   bb2:  %4 = const 1; %5 = icmp sgt %10, %4     ; a
    ///       condbr %5 -> bb3, bb4
    ///   bb3:  %6 = icmp slt %10, %4                   ; b
    ///       condbr %6 -> bb5, bb4
    ///   bb4:  %7 = icmp eq %10, %2                    ; c
    ///       condbr %7 -> bb5, bb6
    ///   bb5:  %8 = add %10, %4      br bb7(%8)        ; TRUE  exit
    ///   bb6:  %9 = sub %10, %4      br bb7(%9)        ; FALSE exit
    ///   bb7(%11: i32): br bb1(%11)                    ; latch
    ///   bb9: return %10
    ///
    /// `region_has_params` puts a block param on bb4, which the recognizer must
    /// refuse — a region block's params would need a merge this does not build.
    fn short_circuit_tir(region_has_params: bool) -> Function {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0));
        bb0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(0)],
        }));
        let mut bb1 = Block::new(b(1)).with_param(v(10), Ty::I32);
        bb1.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(2)),
        );
        bb1.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(2),
            })
            .with_result(v(3)),
        );
        bb1.body.push(InstrNode::new(Inst::CondBr {
            cond: v(3),
            then_target: b(2),
            then_args: vec![],
            else_target: b(9),
            else_args: vec![],
        }));
        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(4)),
        );
        bb2.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Sgt,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(4),
            })
            .with_result(v(5)),
        );
        bb2.body.push(InstrNode::new(Inst::CondBr {
            cond: v(5),
            then_target: b(3),
            then_args: vec![],
            else_target: b(4),
            else_args: if region_has_params {
                vec![v(2)]
            } else {
                vec![]
            },
        }));
        let mut bb3 = Block::new(b(3));
        bb3.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(4),
            })
            .with_result(v(6)),
        );
        bb3.body.push(InstrNode::new(Inst::CondBr {
            cond: v(6),
            then_target: b(5),
            then_args: vec![],
            else_target: b(4),
            else_args: if region_has_params {
                vec![v(2)]
            } else {
                vec![]
            },
        }));
        let mut bb4 = Block::new(b(4));
        if region_has_params {
            bb4 = bb4.with_param(v(12), Ty::I32);
        }
        bb4.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(2),
            })
            .with_result(v(7)),
        );
        bb4.body.push(InstrNode::new(Inst::CondBr {
            cond: v(7),
            then_target: b(5),
            then_args: vec![],
            else_target: b(6),
            else_args: vec![],
        }));
        let mut bb5 = Block::new(b(5));
        bb5.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(4),
            })
            .with_result(v(8)),
        );
        bb5.body.push(InstrNode::new(Inst::Br {
            target: b(7),
            args: vec![v(8)],
        }));
        let mut bb6 = Block::new(b(6));
        bb6.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(4),
            })
            .with_result(v(9)),
        );
        bb6.body.push(InstrNode::new(Inst::Br {
            target: b(7),
            args: vec![v(9)],
        }));
        let mut bb7 = Block::new(b(7)).with_param(v(11), Ty::I32);
        bb7.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(11)],
        }));
        let mut bb9 = Block::new(b(9));
        bb9.body.push(InstrNode::new(Inst::Return {
            values: vec![v(10)],
        }));
        f.blocks = vec![bb0, bb1, bb2, bb3, bb4, bb5, bb6, bb7, bb9];
        f
    }

    /// A `&&`/`||` CHAIN collapses to ONE diamond on the combined condition.
    ///
    /// Without the collapse this shape fails closed: bb2's "arm" bb3 is another
    /// link of the chain, so the arm walker sees a `CondBr` with both targets
    /// in-loop and refuses. Measured on
    /// `core::str::pattern::TwoWaySearcher::maximal_suffix`, that was the last
    /// refusal on the last failed `library/core` root.
    ///
    /// The pin is the EXACT merged term: `ite(reach(bb5), s+1, s-1)` where
    /// `reach(bb5) = (a & b) | ((!a | (a & !b)) & c)` — the region's reaching
    /// condition, not any one link's.
    #[test]
    fn short_circuit_chain_collapses_to_one_diamond() {
        let f = short_circuit_tir(/*region_has_params=*/ false);
        let model = model_back_edge_args(
            &f,
            b(1),
            b(7),
            &[(v(10), "s".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect("a short-circuit chain must model as one diamond");
        assert_eq!(model.args.len(), 1);

        let s = SmtExpr::var("s", 32);
        let one = SmtExpr::bv_const(1, 32);
        let zero = SmtExpr::bv_const(0, 32);
        // An `ICmp` result is a 1-BIT value, and `CondBr` tests it against 0 —
        // so a link's condition is `ite(cmp, 1, 0) != 0`, not `cmp`. Spelling it
        // out here keeps the pin on the exact term the model builds.
        let bit = |cmp: SmtExpr| {
            SmtExpr::ite(cmp, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
                .eq_expr(SmtExpr::bv_const(0, 1))
                .not_expr()
        };
        let a = bit(s.clone().bvsgt(one.clone()));
        let b_cond = bit(s.clone().bvslt(one.clone()));
        let c = bit(s.clone().eq_expr(zero.clone()));
        // reach(bb4) = !a | (a & !b); reach(bb5) = (a & b) | (reach(bb4) & c).
        let reach_bb4 = a
            .clone()
            .not_expr()
            .or_expr(a.clone().and_expr(b_cond.clone().not_expr()));
        let reach_bb5 = a
            .clone()
            .and_expr(b_cond.clone())
            .or_expr(reach_bb4.and_expr(c.clone()));
        let expected = SmtExpr::ite(
            reach_bb5,
            s.clone().bvadd(one.clone()),
            s.clone().bvsub(one.clone()),
        );
        assert_eq!(
            model.args[0], expected,
            "the merged back-edge value must be an `ite` on the WHOLE chain's \
             reaching condition, got {:?}",
            model.args[0]
        );
    }

    /// A bool-`CondBr` link, for the direct recognizer fixtures below.
    fn link(f: &mut Function, id: u32, cond: u32, t: u32, e: u32, stmt: bool) {
        let mut blk = Block::new(b(id));
        if stmt {
            blk.body.push(
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Slt,
                    ty: Ty::I32,
                    lhs: v(10),
                    rhs: v(99),
                })
                .with_result(v(cond)),
            );
        }
        blk.body.push(InstrNode::new(Inst::CondBr {
            cond: v(cond),
            then_target: b(t),
            then_args: vec![],
            else_target: b(e),
            else_args: vec![],
        }));
        f.blocks.push(blk);
    }

    /// The `maximal_suffix` CONDITION SHAPE, reduced to what the recognizer sees:
    /// a four-link chain `6 -> {7,8}`, `7 -> {8,10}`, `8 -> {9,14}`, `9 -> {10,14}`
    /// converging on `10` and `14`, where `10` is ITSELF a bool link (in trust-ir an
    /// `Assert` lowers to a `CondBr`, so the guard right after the condition is
    /// indistinguishable from a chain link) reached from both `7` and `9`.
    ///
    /// That last fact is the whole point: a breadth-first walk enqueues `10` from
    /// `7` BEFORE it reaches `9`, and since `9 -> 10` the order is then not
    /// topological and `[6,7,8,9]` is not a PREFIX of it.
    fn sc_chain_tir(param_on_9: bool) -> Function {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0));
        bb0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(0)],
        }));
        f.blocks.push(bb0);
        let mut bb1 = Block::new(b(1)).with_param(v(10), Ty::I32);
        bb1.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(99)),
        );
        bb1.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(99),
            })
            .with_result(v(3)),
        );
        bb1.body.push(InstrNode::new(Inst::CondBr {
            cond: v(3),
            then_target: b(6),
            then_args: vec![],
            else_target: b(30),
            else_args: vec![],
        }));
        f.blocks.push(bb1);
        link(&mut f, 6, 21, 7, 8, true);
        link(&mut f, 7, 2, 8, 10, false);
        link(&mut f, 8, 22, 9, 14, true);
        if param_on_9 {
            // Same chain, but link 9 carries a block param. The interior runs
            // UNCONDITIONALLY, and a param is a per-edge value that would need a
            // merge the recognizer does not build — so 9 must be refused.
            let mut bb9 = Block::new(b(9)).with_param(v(50), Ty::I32);
            bb9.body.push(InstrNode::new(Inst::CondBr {
                cond: v(2),
                then_target: b(10),
                then_args: vec![],
                else_target: b(14),
                else_args: vec![],
            }));
            f.blocks.push(bb9);
            // Feed the param from both of 9's predecessors.
            for blk in f.blocks.iter_mut() {
                if let Some(Inst::CondBr {
                    then_target,
                    then_args,
                    ..
                }) = blk.body.last_mut().map(|n| &mut n.inst)
                    && *then_target == b(9)
                {
                    *then_args = vec![v(99)];
                }
            }
        } else {
            link(&mut f, 9, 2, 10, 14, false);
        }
        // 10 is a bool link too (an `Assert`), and is one of the two exits.
        link(&mut f, 10, 23, 11, 30, true);
        // 11 must reach the LATCH, not the header: that is what puts 10 inside
        // `loop_set` and therefore makes it absorbable. With 10 outside the loop
        // set it can never be enqueued at all, the two orders coincide, and a pin
        // written on that CFG is VACUOUS — measured, this exact fixture passed with
        // the Kahn gate mutated out until 11 was repointed here.
        let mut bb11 = Block::new(b(11));
        bb11.body.push(InstrNode::new(Inst::Br {
            target: b(15),
            args: vec![],
        }));
        f.blocks.push(bb11);
        // 14 is the other exit and leads to the LATCH, 15.
        link(&mut f, 14, 24, 15, 30, true);
        let mut bb15 = Block::new(b(15));
        bb15.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(10)],
        }));
        f.blocks.push(bb15);
        let mut bb30 = Block::new(b(30));
        bb30.body.push(InstrNode::new(Inst::Return {
            values: vec![v(10)],
        }));
        f.blocks.push(bb30);
        f
    }

    /// REGRESSION PIN for the candidate ORDER. The recognizer takes the largest
    /// PREFIX of its candidate order that is a closed, forward, two-exit region —
    /// so an order that is not topological cannot offer the right region at all.
    ///
    /// A breadth-first walk of this CFG yields `[6,7,8,10,9]`: `10` is enqueued
    /// from `7` before `9` is reached, and `9 -> 10` then runs BACKWARD in the
    /// order. Every prefix containing `[6,7,8,9]` fails the forward test, the
    /// search settles on `[6,7]`, and the whole collapse is lost — silently,
    /// because a recognizer that declines is indistinguishable from one that never
    /// ran. Measured on `core::str::pattern::TwoWaySearcher::maximal_suffix`; it
    /// cost three rebuild cycles. Kahn's order (append only once ALL predecessors
    /// are in) is what makes `[6,7,8,9]` a prefix.
    #[test]
    fn short_circuit_region_orders_candidates_topologically_not_breadth_first() {
        let f = sc_chain_tir(/*param_on_9=*/ false);
        let loop_set = natural_loop_blocks(&f, b(1), b(15));
        let (region, exits) =
            short_circuit_region(&f, &loop_set, b(1), b(15), b(6), &predecessors_of(&f))
                .expect("the four-link chain must be recognized");
        assert_eq!(
            region,
            vec![b(6), b(7), b(8), b(9)],
            "the region must be the whole condition chain, not the two-block prefix a \
             breadth-first order would leave"
        );
        assert_eq!(
            [exits[0].0, exits[1].0],
            [b(10), b(14)],
            "the exits are the two blocks the chain converges on"
        );
    }

    /// MUTATION CONTROL for the block-param clause, asserted on the RECOGNIZER
    /// ITSELF rather than through the whole model. The previous version of this
    /// test drove `model_back_edge_args` and asserted only that it errored — which
    /// it did, but from the arm walker further downstream, so it would have passed
    /// with the params clause deleted. This one cannot: with a param on link 9 the
    /// region must STOP before it.
    #[test]
    fn short_circuit_region_refuses_an_interior_block_with_params() {
        let f = sc_chain_tir(/*param_on_9=*/ true);
        let loop_set = natural_loop_blocks(&f, b(1), b(15));
        let got = short_circuit_region(&f, &loop_set, b(1), b(15), b(6), &predecessors_of(&f));
        let region = got.map(|(r, _)| r).unwrap_or_default();
        assert!(
            !region.contains(&b(9)),
            "a region block carrying a param must not be absorbed, got region {region:?}"
        );
    }

    /// A tail-diamond LATCH that a condition chain also converges on:
    ///
    ///   bb1(%10,%11)  header, guard -> bb6 / bb30(exit)
    ///   bb6 -> bb7 / bb8       the chain
    ///   bb7 -> bb2 / bb9
    ///   bb8 -> bb2 / bb9
    ///   bb2                    LATCH (no params), condbr -> bb9 / bb1(%11,%10)
    ///   bb9                    br bb1(%11, %10-%11)     reaches the header, NOT the latch
    fn sc_latch_tir(swap_back_args: bool) -> Function {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0));
        bb0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(0), v(1)],
        }));
        f.blocks.push(bb0);
        let mut bb1 = Block::new(b(1))
            .with_param(v(10), Ty::I32)
            .with_param(v(11), Ty::I32);
        bb1.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(99)),
        );
        bb1.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I32,
                lhs: v(11),
                rhs: v(99),
            })
            .with_result(v(3)),
        );
        bb1.body.push(InstrNode::new(Inst::CondBr {
            cond: v(3),
            then_target: b(6),
            then_args: vec![],
            else_target: b(30),
            else_args: vec![],
        }));
        f.blocks.push(bb1);
        link(&mut f, 6, 21, 7, 8, true);
        link(&mut f, 7, 3, 2, 9, false);
        link(&mut f, 8, 3, 2, 9, false);
        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Sgt,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(11),
            })
            .with_result(v(15)),
        );
        bb2.body.push(InstrNode::new(Inst::CondBr {
            cond: v(15),
            then_target: b(9),
            then_args: vec![],
            else_target: b(1),
            // CORRECT: slot0 <- %11 (b), slot1 <- %10 (a). `swap_back_args` routes
            // each into the OTHER slot — the exact misroute this whole VC exists to
            // catch, on the shape this campaign added.
            else_args: if swap_back_args {
                vec![v(10), v(11)]
            } else {
                vec![v(11), v(10)]
            },
        }));
        f.blocks.push(bb2);
        let mut bb9 = Block::new(b(9));
        bb9.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(11),
            })
            .with_result(v(16)),
        );
        bb9.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(11), v(16)],
        }));
        f.blocks.push(bb9);
        let mut bb30 = Block::new(b(30));
        bb30.body.push(InstrNode::new(Inst::Return {
            values: vec![v(10)],
        }));
        f.blocks.push(bb30);
        f
    }

    /// REGRESSION PIN: the region must never swallow the LATCH.
    ///
    /// `natural_loop_blocks` inserts the latch, and a tail-diamond latch ends in a
    /// `CondBr`, so nothing about "is it a link, is it in the loop set" excludes it
    /// — and because the search keeps the LARGEST valid prefix it actively PREFERS
    /// the region that absorbs it (here `[6,7,8]` has exits {2,9} and `[6,7,8,2]`
    /// has exits {9,1}, both exactly two). Absorbing it swallows the very back-edge
    /// under obligation: both exits then classify out-of-loop and the whole loop
    /// fails closed, where before this recognizer existed it modelled fine.
    ///
    /// Also the only pin on the COMPOUND GUARD classification — one exit in-loop,
    /// one not — which is the case that cleared `maximal_suffix`.
    #[test]
    fn short_circuit_region_never_absorbs_the_latch() {
        let f = sc_latch_tir(/*swap_back_args=*/ false);
        let loop_set = natural_loop_blocks(&f, b(1), b(2));
        let (region, exits) =
            short_circuit_region(&f, &loop_set, b(1), b(2), b(6), &predecessors_of(&f))
                .expect("the chain must be recognized");
        assert!(
            !region.contains(&b(2)),
            "the LATCH must never be absorbed into a condition region, got {region:?}"
        );
        assert_eq!(region, vec![b(6), b(7), b(8)]);
        // COMPOUND GUARD: exactly one exit can reach this latch.
        let in_loop: Vec<BlockId> = [exits[0].0, exits[1].0]
            .into_iter()
            .filter(|x| loop_set.contains(x) && *x != b(1))
            .collect();
        assert_eq!(
            in_loop,
            vec![b(2)],
            "exactly one exit reaches this latch, so the region is a GUARD, not a diamond"
        );
        // ... and the whole loop still models, which is what the regression is about.
        let model = model_back_edge_args(
            &f,
            b(1),
            b(2),
            &[(v(10), "a".to_string(), 32), (v(11), "b".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect("a tail-diamond latch behind a condition chain must still model");
        assert_eq!(model.args.len(), 2);
    }

    /// END-TO-END ANTI-SWAP PIN for the short-circuit shape — the property this
    /// whole VC exists for, on the shape this campaign added.
    ///
    /// a35706b1 landed the recognizer with NO `swap_refutes` pin: every such pin in
    /// this file covers a shape that predates it (`ovf_tuple`, `diamond_loop`,
    /// `tail_diamond`, `euclid`). The structural pins assert the recognizer picks
    /// the right region; only this one asserts that a WRONG THREADING through that
    /// region is still caught.
    ///
    /// The REFUTES half is the load-bearing one, and it always runs: a `Refuted` is
    /// a counterexample, never a certification-gap skip. The positive half may skip
    /// on a machine whose Alethe cert store lacks the entry — measured, four
    /// end-to-end pins in this module do exactly that while still printing `ok`.
    #[test]
    fn short_circuit_guard_end_to_end_refines_and_swap_refutes() {
        if !ay_bridge::z3_available() {
            eprintln!("skipping: z3 not available");
            return;
        }
        // The condition chain in front contributes only a path condition, which the
        // impl side deliberately does not record — so the SPEC is exactly the plain
        // tail diamond: cond a > b; b' = select(cond, a-b, a); a' = b.
        let spec = MirBlock {
            stmts: vec![
                MirStmt {
                    dst: "cmp".into(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Gt,
                        ty: MirScalarTy::SInt(Type::I32),
                        lhs: var_i32("l1"),
                        rhs: var_i32("l2"),
                    },
                },
                MirStmt {
                    dst: "then_b".into(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Sub,
                        ty: MirScalarTy::SInt(Type::I32),
                        lhs: var_i32("l1"),
                        rhs: var_i32("l2"),
                    },
                },
                MirStmt {
                    dst: "b_sel".into(),
                    rvalue: MirRvalue::Select {
                        cond: MirOperand::Var {
                            name: "cmp".into(),
                            ty: MirScalarTy::Bool,
                        },
                        ty: MirScalarTy::SInt(Type::I32),
                        then_val: var_i32("then_b"),
                        else_val: var_i32("l1"),
                    },
                },
            ],
            terminator: MirTerminator::Goto {
                target: 0,
                args: vec![var_i32("l2"), var_i32("b_sel")],
            },
        };
        let preconds = vec![
            SmtExpr::var("l2", 32)
                .eq_expr(SmtExpr::bv_const(0, 32))
                .not_expr(),
        ];
        let bindings = [(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)];
        let run = |swap: bool| {
            let f = sc_latch_tir(swap);
            let model = model_back_edge_args(
                &f,
                b(1),
                b(2),
                &bindings,
                &::std::collections::HashSet::new(),
            )
            .expect("a condition chain in front of a tail-diamond latch must model");
            check_back_edge_threading(
                if swap { "sc_swap" } else { "sc_ok" },
                &spec,
                &BridgeEdgeArgs {
                    edge: EdgeKind::Goto,
                    args: model.args,
                },
                &preconds,
                &model.extra_inputs,
                &AYConfig::default(),
            )
            .unwrap()
        };

        match run(false) {
            RefinementOutcome::Refined => {}
            other => {
                if let Some(reason) = crate::formal_gap::refinement_gap_reason(&other) {
                    crate::formal_gap::print_gap_skip(
                        "short_circuit_guard_end_to_end (positive half)",
                        reason,
                    );
                } else {
                    panic!(
                        "the correct threading through a short-circuit guard must refine, got {other:?}"
                    )
                }
            }
        }
        // THE LOAD-BEARING HALF. A cross-slot misroute behind the collapsed
        // condition must still be caught; a `Refuted` is never gap-skipped.
        match run(true) {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!(
                "a swapped back-edge threading behind a short-circuit region MUST refute, got {other:?}"
            ),
        }
    }

    /// The overflow FLAG (result 1) models as the SHARED uninterpreted symbol
    /// `overflow_flag_uf("add", 32, s, 100)` — NOT an opaque input. This is the
    /// load-bearing change: an opaque flag made the flag-carrying loop fail closed.
    #[test]
    fn overflow_flag_result_models_as_uf() {
        let f = ovf_tuple_tir(vec![v(5), v(6)]); // correct: (wrapped, flag)
        let model = model_back_edge_args(
            &f,
            b(1),
            b(2),
            &[(v(10), "s".to_string(), 32), (v(11), "f".to_string(), 1)],
            &::std::collections::HashSet::new(),
        )
        .expect("overflow-tuple loop must model");
        assert_eq!(model.args.len(), 2);
        // Slot 0 (wrapped) is the exact bvadd over the header var + the const.
        assert_eq!(
            model.args[0],
            SmtExpr::var("s", 32).bvadd(SmtExpr::bv_const(100, 32)),
            "wrapped slot must be bvadd(s, 100), got {:?}",
            model.args[0]
        );
        // Slot 1 (flag) is the shared UF — the exact application the SPEC's `_6.1`
        // extract denotes, so the threading VC proves it by congruence.
        let expected_flag = crate::mir_semantics::overflow_flag_uf(
            "add",
            32,
            SmtExpr::var("s", 32),
            SmtExpr::bv_const(100, 32),
        );
        assert_eq!(
            model.args[1], expected_flag,
            "the overflow flag must model as the shared UF, got {:?}",
            model.args[1]
        );
        // The flag is a UF application, NOT a minted opaque input.
        assert!(
            model
                .extra_inputs
                .iter()
                .all(|(n, _)| !n.starts_with("__tir_op")),
            "the overflow flag must be the shared UF, not an opaque input; extra_inputs={:?}",
            model.extra_inputs
        );
    }

    /// END-TO-END (the piece-3 fix): the produced overflow-tuple latch REFINES the
    /// MIR spec built with `CheckedOverflowPacked` + `PackedOverflowField`, and a
    /// STALE-FLAG threading (old `f` re-threaded into the flag slot instead of the
    /// new flag) is REFUTED — the flag UF proves the bridge must thread THIS add's
    /// flag, not a stale one.
    #[test]
    fn ovf_tuple_end_to_end_refines_and_stale_flag_refutes() {
        if !ay_bridge::z3_available() {
            eprintln!("skipping: z3 not available");
            return;
        }
        // SPEC: _6 = AddWithOverflow(s, 100); s = _6.0; f = _6.1; goto header(s, f).
        let spec = MirBlock {
            stmts: vec![
                MirStmt {
                    dst: "_6".into(),
                    rvalue: MirRvalue::CheckedOverflowPacked {
                        op: MirBinOp::Add,
                        ty: MirScalarTy::SInt(Type::I32),
                        lhs: var_i32("s"),
                        rhs: MirOperand::ConstInt {
                            value: 100,
                            ty: MirScalarTy::SInt(Type::I32),
                        },
                    },
                },
                MirStmt {
                    dst: "s".into(),
                    rvalue: MirRvalue::PackedOverflowField {
                        src: "_6".into(),
                        field: 0,
                        value_width: 32,
                    },
                },
                MirStmt {
                    dst: "f".into(),
                    rvalue: MirRvalue::PackedOverflowField {
                        src: "_6".into(),
                        field: 1,
                        value_width: 32,
                    },
                },
            ],
            terminator: MirTerminator::Goto {
                target: 0,
                args: vec![
                    var_i32("s"),
                    MirOperand::Var {
                        name: "f".into(),
                        ty: MirScalarTy::Bool,
                    },
                ],
            },
        };
        // Loop guard `s != 0` over the header param.
        let preconds = vec![
            SmtExpr::var("s", 32)
                .eq_expr(SmtExpr::bv_const(0, 32))
                .not_expr(),
        ];
        let bindings = [(v(10), "s".to_string(), 32), (v(11), "f".to_string(), 1)];

        // POSITIVE: the correct (wrapped, flag) threading refines.
        let f_ok = ovf_tuple_tir(vec![v(5), v(6)]);
        let model = model_back_edge_args(
            &f_ok,
            b(1),
            b(2),
            &bindings,
            &::std::collections::HashSet::new(),
        )
        .expect("overflow-tuple path must model");
        let bridge = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: model.args,
        };
        match back_edge_test_outcome(
            "ovf_ok",
            &spec,
            &bridge,
            &preconds,
            &model.extra_inputs,
            &AYConfig::default(),
        )
        .unwrap()
        {
            RefinementOutcome::Refined => {}
            other => {
                if let Some(reason) = crate::formal_gap::refinement_gap_reason(&other) {
                    crate::formal_gap::print_gap_skip(
                        "ovf_tuple_end_to_end_refines_and_stale_flag_refutes (positive half)",
                        reason,
                    );
                } else {
                    panic!("correct overflow-tuple threading must refine, got {other:?}")
                }
            }
        }

        // NEGATIVE (soundness): threading the STALE old flag (%11) into the flag
        // slot instead of the new flag (%6) must be REFUTED.
        let f_stale = ovf_tuple_tir(vec![v(5), v(11)]);
        let model_stale = model_back_edge_args(
            &f_stale,
            b(1),
            b(2),
            &bindings,
            &::std::collections::HashSet::new(),
        )
        .expect("stale-flag overflow path must still model");
        let bridge_stale = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: model_stale.args,
        };
        match check_back_edge_threading(
            "ovf_stale_flag",
            &spec,
            &bridge_stale,
            &preconds,
            &model_stale.extra_inputs,
            &AYConfig::default(),
        )
        .unwrap()
        {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("stale-flag threading must be refuted, got {other:?}"),
        }
    }

    /// A MALFORMED diamond whose arm IS the latch (so the arm takes the
    /// back-edge to the header) is out of model: Err. Well-formed 2-way diamonds
    /// that reconverge before the latch ARE modeled (see `diamond_loop_*`
    /// below); this shape is rejected because one "arm" branches straight to the
    /// header, which is a nested back-edge, not a reconverging arm.
    #[test]
    fn diamond_arm_taking_back_edge_is_rejected() {
        let mut f = euclid_tir();
        // Repoint the header's ELSE arm (bb3) at the latch bb2: now both header
        // successors are in-loop (a diamond), but the THEN arm bb2 is the latch
        // itself, whose terminator is `Br bb1` (the back-edge).
        {
            let bb3 = f.blocks.iter_mut().find(|blk| blk.id == b(3)).unwrap();
            bb3.body.clear();
            bb3.body.push(InstrNode::new(Inst::Br {
                target: b(2),
                args: vec![],
            }));
        }
        let err = model_back_edge_args(
            &f,
            b(1),
            b(2),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect_err("a diamond arm that takes the back-edge must be rejected");
        assert!(
            err.contains("back to the header") || err.contains("nested back-edge"),
            "got: {err}"
        );
        // The refused arm must BE the latch (bb2): over the natural-loop set an
        // arm that reaches the header has no other way there, and the refusal
        // is minted inside the arm walk, naming that block. This is the theorem
        // behind `allow_header_join=false` for both arms, and the mutation pin
        // for the flag — walking with `true` returns `join == header` instead
        // and the diamond fails later with a "do not reconverge" message that
        // names no arm.
        assert!(
            err.contains("diamond arm BlockId(2)"),
            "the refused arm must be the latch bb2; got: {err}"
        );
    }

    // -----------------------------------------------------------------------
    // 2-WAY DIAMOND inside the loop body (the new coverage). A header that
    // branches on a cond into two straight-line arms reconverging at a join,
    // which then flows to the latch and back-edges. The IMPL-side model merges
    // each join param with `ite(cond, then_arg, else_arg)`.
    // -----------------------------------------------------------------------

    /// A diamond-body loop, as the bridge lowers it (i32, header params
    /// `(a, b)` = (%10, %11)):
    ///
    ///   bb0: br bb1(%0, %1)                       ; preheader
    ///   bb1(%10: i32, %11: i32):                  ; header
    ///       %2 = const 0
    ///       %3 = icmp ne %11, %2                   ; while b != 0
    ///       condbr %3, bb2(), bb5()               ; bb5 = exit
    ///   bb2:                                       ; diamond entry
    ///       %4 = icmp sgt %10, %11                 ; if a > b
    ///       condbr %4, bb3(), bb4()
    ///   bb3:                                       ; THEN arm: t = a - b
    ///       %5 = sub %10, %11
    ///       br bb6(%5)
    ///   bb4:                                       ; ELSE arm: t = b - a
    ///       %6 = sub %11, %10
    ///       br bb6(%6)
    ///   bb6(%7: i32):                              ; JOIN: t = phi(%5, %6)
    ///       br bb1(%11, %7)                        ; back-edge: a'=b, b'=t (latch)
    ///   bb5: return %10
    ///
    /// The latch is the JOIN block bb6 (its `Br bb1` is the back-edge). The
    /// back-edge threads `(a', b') = (old b, select(a>b, a-b, b-a))`.
    fn diamond_tir(swap_join_args: bool) -> Function {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0));
        bb0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(0), v(1)],
        }));
        let mut bb1 = Block::new(b(1))
            .with_param(v(10), Ty::I32)
            .with_param(v(11), Ty::I32);
        bb1.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(2)),
        );
        bb1.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I32,
                lhs: v(11),
                rhs: v(2),
            })
            .with_result(v(3)),
        );
        bb1.body.push(InstrNode::new(Inst::CondBr {
            cond: v(3),
            then_target: b(2),
            then_args: vec![],
            else_target: b(5),
            else_args: vec![],
        }));
        // Diamond entry bb2: if a > b
        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Sgt,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(11),
            })
            .with_result(v(4)),
        );
        bb2.body.push(InstrNode::new(Inst::CondBr {
            cond: v(4),
            then_target: b(3),
            then_args: vec![],
            else_target: b(4),
            else_args: vec![],
        }));
        // THEN arm bb3: t = a - b
        let mut bb3 = Block::new(b(3));
        bb3.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(11),
            })
            .with_result(v(5)),
        );
        bb3.body.push(InstrNode::new(Inst::Br {
            target: b(6),
            args: vec![v(5)],
        }));
        // ELSE arm bb4: t = b - a
        let mut bb4 = Block::new(b(4));
        bb4.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I32,
                lhs: v(11),
                rhs: v(10),
            })
            .with_result(v(6)),
        );
        bb4.body.push(InstrNode::new(Inst::Br {
            target: b(6),
            args: vec![v(6)],
        }));
        // JOIN bb6: t = phi; latch. Back-edge a'=b, b'=t.
        let mut bb6 = Block::new(b(6)).with_param(v(7), Ty::I32);
        let back_args = if swap_join_args {
            vec![v(7), v(11)] // WRONG: a'=t, b'=b (swapped)
        } else {
            vec![v(11), v(7)] // a'=b, b'=t
        };
        bb6.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: back_args,
        }));
        let mut bb5 = Block::new(b(5));
        bb5.body.push(InstrNode::new(Inst::Return {
            values: vec![v(10)],
        }));
        f.blocks = vec![bb0, bb1, bb2, bb3, bb4, bb6, bb5];
        f
    }

    /// The diamond-body loop MODELS: the back-edge args are
    /// `(b, ite(a>b, a-b, b-a))`. Slot 0 is exactly `l2` (old b); slot 1 is the
    /// merged select, mentioning both header vars. The latch is the JOIN bb6.
    #[test]
    fn diamond_loop_models_select_at_join() {
        let f = diamond_tir(false);
        let model = model_back_edge_args(
            &f,
            b(1),
            b(6),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect("diamond loop path must model");
        assert_eq!(model.args.len(), 2);
        // Slot 0 (a') is exactly old b.
        assert_eq!(model.args[0], SmtExpr::var("l2", 32));
        // Slot 1 (b') is the merged select over both header vars.
        let free = model.args[1].free_vars();
        assert!(
            free.contains(&"l1".to_string()) && free.contains(&"l2".to_string()),
            "merged arg must mention both header vars, got free={free:?}"
        );
        // The whole path is encoded — no opaque inputs minted.
        assert!(
            model
                .extra_inputs
                .iter()
                .all(|(n, _)| !n.starts_with("__tir_op")),
            "no opaque should be minted on the fully-encoded diamond path"
        );
    }

    /// END-TO-END diamond: the IMPL model (the merged select) REFINES the MIR
    /// SPEC built with a `MirRvalue::Select` at the join — and a SWAPPED join
    /// back-edge is REFUTED. The spec mirrors `bb6 -> latch`:
    ///   `t = select(a > b, a - b, b - a); back-edge (a', b') = (b, t)`.
    #[test]
    fn diamond_loop_end_to_end_refines_and_swap_refutes() {
        if !ay_bridge::z3_available() {
            eprintln!("skipping: z3 not available");
            return;
        }
        // SPEC: a > b cond, two arms, select-merged t, back-edge (b, t).
        let gt = MirRvalue::BinaryOp {
            op: MirBinOp::Gt,
            ty: MirScalarTy::SInt(Type::I32),
            lhs: var_i32("l1"),
            rhs: var_i32("l2"),
        };
        let spec = MirBlock {
            stmts: vec![
                MirStmt {
                    dst: "cmp".into(),
                    rvalue: gt,
                },
                MirStmt {
                    dst: "then_t".into(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Sub,
                        ty: MirScalarTy::SInt(Type::I32),
                        lhs: var_i32("l1"),
                        rhs: var_i32("l2"),
                    },
                },
                MirStmt {
                    dst: "else_t".into(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Sub,
                        ty: MirScalarTy::SInt(Type::I32),
                        lhs: var_i32("l2"),
                        rhs: var_i32("l1"),
                    },
                },
                MirStmt {
                    dst: "t".into(),
                    rvalue: MirRvalue::Select {
                        cond: MirOperand::Var {
                            name: "cmp".into(),
                            ty: MirScalarTy::Bool,
                        },
                        ty: MirScalarTy::SInt(Type::I32),
                        then_val: var_i32("then_t"),
                        else_val: var_i32("else_t"),
                    },
                },
            ],
            terminator: MirTerminator::Goto {
                target: 0,
                args: vec![var_i32("l2"), var_i32("t")],
            },
        };
        // Loop guard `b != 0` (no division on this path, so just the guard).
        let preconds = vec![
            SmtExpr::var("l2", 32)
                .eq_expr(SmtExpr::bv_const(0, 32))
                .not_expr(),
        ];

        // POSITIVE: correct emitted diamond refines.
        let f = diamond_tir(false);
        let model = model_back_edge_args(
            &f,
            b(1),
            b(6),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect("diamond path must model");
        let bridge = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: model.args,
        };
        match check_back_edge_threading(
            "e2e_diamond",
            &spec,
            &bridge,
            &preconds,
            &model.extra_inputs,
            &AYConfig::default(),
        )
        .unwrap()
        {
            RefinementOutcome::Refined => {}
            other => panic!("correct diamond must refine end-to-end, got {other:?}"),
        }

        // NEGATIVE: a SWAPPED back-edge (a'=t, b'=b) must be refuted.
        let f_swap = diamond_tir(true);
        let model_swap = model_back_edge_args(
            &f_swap,
            b(1),
            b(6),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect("swapped diamond path must still model");
        let bridge_swap = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: model_swap.args,
        };
        match check_back_edge_threading(
            "e2e_diamond_swap",
            &spec,
            &bridge_swap,
            &preconds,
            &model_swap.extra_inputs,
            &AYConfig::default(),
        )
        .unwrap()
        {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("swapped diamond back-edge must be refuted, got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // TAIL DIAMOND at the latch: `for/while { ...; if cond { ... } }`. The latch
    // IS the diamond-condition block; BOTH `CondBr` arms reconverge at the
    // HEADER (one falls through directly, the other does work then Brs to the
    // header). Modeled as `ite(cond, then, else)` per header slot. The tail-arm
    // block is NOT in the natural-loop set of the tail latch (the backward walk
    // stops at the header), so this exercises the `tail_arm_loop_blocks`
    // augmentation.
    // -----------------------------------------------------------------------

    /// A tail-diamond loop (i32, header params `(a, b)` = (%10, %11)):
    ///
    ///   bb0: br bb1(%0, %1)                       ; preheader
    ///   bb1(%10, %11):                            ; HEADER (a, b)
    ///       %2 = const 0
    ///       %3 = icmp ne %11, %2                   ; guard: b != 0
    ///       condbr %3, bb2(), bb5()               ; bb5 = exit
    ///   bb2:                                       ; LATCH (diamond cond block)
    ///       %4 = icmp sgt %10, %11                 ; cond: a > b
    ///       condbr %4, bb3(), bb1(%11, %10)        ; TAIL: then=bb3(work);
    ///                                              ;   else=header (a'=b, b'=a)
    ///   bb3:                                       ; THEN arm (pred: bb2 only)
    ///       %5 = sub %10, %11                       ; a - b
    ///       br bb1(%11, %5)                          ; a'=b, b'=(a-b)
    ///   bb5: return %10
    ///
    /// Two back-edges (bb2->header else edge, bb3->header) so TWO latches. The
    /// tail-diamond VC uses latch=bb2; its natural loop is `{bb1, bb2}` — the
    /// then-arm bb3 is EXCLUDED (only a predecessor of the header), so the
    /// `tail_arm_loop_blocks` widening is required. The back-edge threads
    /// `(a', b') = (b, ite(a>b, a-b, a))`.
    fn tail_diamond_tir(swap_then_args: bool) -> Function {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0));
        bb0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(0), v(1)],
        }));
        let mut bb1 = Block::new(b(1))
            .with_param(v(10), Ty::I32)
            .with_param(v(11), Ty::I32);
        bb1.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(2)),
        );
        bb1.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ne,
                ty: Ty::I32,
                lhs: v(11),
                rhs: v(2),
            })
            .with_result(v(3)),
        );
        bb1.body.push(InstrNode::new(Inst::CondBr {
            cond: v(3),
            then_target: b(2),
            then_args: vec![],
            else_target: b(5),
            else_args: vec![],
        }));
        // LATCH bb2: cond a > b; then=bb3 (work), else=header directly.
        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Sgt,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(11),
            })
            .with_result(v(4)),
        );
        bb2.body.push(InstrNode::new(Inst::CondBr {
            cond: v(4),
            then_target: b(3),
            then_args: vec![],
            // ELSE edge (cond false) threads (a'=b, b'=a) straight to the header.
            else_target: b(1),
            else_args: vec![v(11), v(10)],
        }));
        // THEN arm bb3: b' = a - b; a' = b. Brs to the header.
        let mut bb3 = Block::new(b(3));
        bb3.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Sub,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(11),
            })
            .with_result(v(5)),
        );
        let then_args = if swap_then_args {
            vec![v(5), v(11)] // WRONG: a'=(a-b), b'=b (slots swapped)
        } else {
            vec![v(11), v(5)] // a'=b, b'=(a-b)
        };
        bb3.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: then_args,
        }));
        let mut bb5 = Block::new(b(5));
        bb5.body.push(InstrNode::new(Inst::Return {
            values: vec![v(10)],
        }));
        f.blocks = vec![bb0, bb1, bb2, bb3, bb5];
        f
    }

    /// The tail diamond MODELS at latch=bb2: back-edge args
    /// `(b, ite(a>b, a-b, a))`. Slot 0 (a') collapses to exactly `l2` (both arms
    /// thread old b); slot 1 (b') mentions both header vars. Confirms the
    /// `tail_arm_loop_blocks` widening admits the then-arm bb3 (excluded from the
    /// natural loop of bb2).
    #[test]
    fn tail_diamond_models_ite_at_header() {
        let f = tail_diamond_tir(false);
        let model = model_back_edge_args(
            &f,
            b(1),
            b(2),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect("tail-diamond path must model at latch=bb2");
        assert_eq!(model.args.len(), 2);
        // Slot 0 (a') threads old b on BOTH arms: the value is `ite(cond, b, b)`
        // (z3 collapses it to b in the refine test). Its expression still mentions
        // `l2` (the threaded value) — and, via the ite condition, `l1` — so we only
        // assert it carries old b, not that the cond's vars are absent.
        let free0 = model.args[0].free_vars();
        assert!(
            free0.contains(&"l2".to_string()),
            "slot 0 must thread old b, got free={free0:?}"
        );
        // Slot 1 (b') is the merged ite over both header vars.
        let free1 = model.args[1].free_vars();
        assert!(
            free1.contains(&"l1".to_string()) && free1.contains(&"l2".to_string()),
            "merged slot 1 must mention both header vars, got free={free1:?}"
        );
        assert!(
            model
                .extra_inputs
                .iter()
                .all(|(n, _)| !n.starts_with("__tir_op")),
            "no opaque should be minted on the fully-encoded tail-diamond path"
        );
    }

    /// GATE A (THE soundness gate): the tail-diamond IMPL model REFINES the MIR
    /// SPEC built with a `Select`, AND a back-edge that threads the WRONG SLOT on
    /// the then-arm is z3-REFUTED (fail closed, never admitted). The SPEC mirrors
    /// `bb2 -> header`: `b' = select(a > b, a - b, a); back-edge (a', b') = (b, b')`.
    #[test]
    fn tail_diamond_end_to_end_refines_and_swap_refutes() {
        if !ay_bridge::z3_available() {
            eprintln!("skipping: z3 not available");
            return;
        }
        // SPEC: cond a > b; b' = select(cond, a-b, a); a' = b.
        let spec = MirBlock {
            stmts: vec![
                MirStmt {
                    dst: "cmp".into(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Gt,
                        ty: MirScalarTy::SInt(Type::I32),
                        lhs: var_i32("l1"),
                        rhs: var_i32("l2"),
                    },
                },
                MirStmt {
                    dst: "then_b".into(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Sub,
                        ty: MirScalarTy::SInt(Type::I32),
                        lhs: var_i32("l1"),
                        rhs: var_i32("l2"),
                    },
                },
                MirStmt {
                    dst: "b_sel".into(),
                    rvalue: MirRvalue::Select {
                        cond: MirOperand::Var {
                            name: "cmp".into(),
                            ty: MirScalarTy::Bool,
                        },
                        ty: MirScalarTy::SInt(Type::I32),
                        then_val: var_i32("then_b"),
                        // ELSE value = a (the else edge threads b'=a).
                        else_val: var_i32("l1"),
                    },
                },
            ],
            terminator: MirTerminator::Goto {
                target: 0,
                args: vec![var_i32("l2"), var_i32("b_sel")],
            },
        };
        // Loop guard `b != 0` (no other path condition on the tail diamond).
        let preconds = vec![
            SmtExpr::var("l2", 32)
                .eq_expr(SmtExpr::bv_const(0, 32))
                .not_expr(),
        ];

        // POSITIVE: the correct tail diamond refines.
        let f = tail_diamond_tir(false);
        let model = model_back_edge_args(
            &f,
            b(1),
            b(2),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect("tail-diamond path must model");
        let bridge = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: model.args,
        };
        match back_edge_test_outcome(
            "e2e_tail_diamond",
            &spec,
            &bridge,
            &preconds,
            &model.extra_inputs,
            &AYConfig::default(),
        )
        .unwrap()
        {
            RefinementOutcome::Refined => {}
            other => {
                if let Some(reason) = crate::formal_gap::refinement_gap_reason(&other) {
                    crate::formal_gap::print_gap_skip(
                        "tail_diamond_end_to_end_refines_and_swap_refutes (positive half)",
                        reason,
                    );
                } else {
                    panic!("correct tail diamond must refine end-to-end, got {other:?}")
                }
            }
        }

        // NEGATIVE (THE swap-refute gate): the then-arm threads the WRONG slots
        // (a'=(a-b), b'=b). Under cond=true z3 needs `a-b == b` for ALL inputs -
        // false -> Refuted -> fail closed. A wrong threading is NEVER admitted.
        let f_swap = tail_diamond_tir(true);
        let model_swap = model_back_edge_args(
            &f_swap,
            b(1),
            b(2),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect("swapped tail-diamond path must still model");
        let bridge_swap = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: model_swap.args,
        };
        match check_back_edge_threading(
            "e2e_tail_diamond_swap",
            &spec,
            &bridge_swap,
            &preconds,
            &model_swap.extra_inputs,
            &AYConfig::default(),
        )
        .unwrap()
        {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!(
                "a WRONG-SLOT tail-diamond back-edge MUST be refuted (fail closed), got {other:?}"
            ),
        }
    }

    /// GATE B (the strongest adversary): a bottom-test BREAK loop
    /// `loop { body; if done { break } }` — the latch `CondBr` has ONE edge to
    /// the header (continue) and ONE edge EXITING the loop (break). The exit
    /// block CANNOT reach the header, so `tail_arm_loop_blocks` does NOT add it
    /// and `model_diamond_arm` rejects it: the whole model FAILS CLOSED (never a
    /// wrong value). This locks the tail-diamond-vs-break distinction.
    #[test]
    fn break_loop_latch_condbr_fails_closed() {
        let mut f = empty_fn();
        let mut bb0 = Block::new(b(0));
        bb0.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(0), v(1)],
        }));
        let mut bb1 = Block::new(b(1))
            .with_param(v(10), Ty::I32)
            .with_param(v(11), Ty::I32);
        // body: acc' = a + b
        bb1.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(10),
                rhs: v(11),
            })
            .with_result(v(2)),
        );
        bb1.body.push(InstrNode::new(Inst::Br {
            target: b(2),
            args: vec![],
        }));
        // LATCH bb2: if done { break } -> then=bb5 (EXIT), else=header (continue).
        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Sgt,
                ty: Ty::I32,
                lhs: v(2),
                rhs: v(10),
            })
            .with_result(v(4)),
        );
        bb2.body.push(InstrNode::new(Inst::CondBr {
            cond: v(4),
            then_target: b(5), // break: EXITS the loop
            then_args: vec![],
            else_target: b(1), // continue: back-edge (a'=b, b'=acc)
            else_args: vec![v(11), v(2)],
        }));
        // EXIT bb5: returns (cannot reach the header).
        let mut bb5 = Block::new(b(5));
        bb5.body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        f.blocks = vec![bb0, bb1, bb2, bb5];

        let err = model_back_edge_args(
            &f,
            b(1),
            b(2),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect_err("a break-loop latch CondBr (one arm EXITS) must FAIL CLOSED, not model");
        assert!(
            err.contains("forward in-loop block") || err.contains("out of model"),
            "break-loop must be rejected as an out-of-loop arm, got: {err}"
        );
    }

    /// GATE E (two-VC path): the tail-diamond fixture flags BOTH back-edges
    /// (bb2->header else edge AND bb3->header) as misthreads, producing TWO VCs.
    /// The tail-diamond VC (latch=bb2) and the straight-line-precond VC
    /// (latch=bb3, the cond-true slice) must BOTH refine — neither spuriously
    /// fails closed.
    #[test]
    fn tail_diamond_two_vc_paths_both_refine() {
        if !ay_bridge::z3_available() {
            eprintln!("skipping: z3 not available");
            return;
        }
        let f = tail_diamond_tir(false);
        let bindings = [(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)];
        let guard = vec![
            SmtExpr::var("l2", 32)
                .eq_expr(SmtExpr::bv_const(0, 32))
                .not_expr(),
        ];

        // VC #1 — tail diamond at latch=bb2 (both arms reconverge at header).
        let tail_spec = MirBlock {
            stmts: vec![
                MirStmt {
                    dst: "cmp".into(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Gt,
                        ty: MirScalarTy::SInt(Type::I32),
                        lhs: var_i32("l1"),
                        rhs: var_i32("l2"),
                    },
                },
                MirStmt {
                    dst: "then_b".into(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Sub,
                        ty: MirScalarTy::SInt(Type::I32),
                        lhs: var_i32("l1"),
                        rhs: var_i32("l2"),
                    },
                },
                MirStmt {
                    dst: "b_sel".into(),
                    rvalue: MirRvalue::Select {
                        cond: MirOperand::Var {
                            name: "cmp".into(),
                            ty: MirScalarTy::Bool,
                        },
                        ty: MirScalarTy::SInt(Type::I32),
                        then_val: var_i32("then_b"),
                        else_val: var_i32("l1"),
                    },
                },
            ],
            terminator: MirTerminator::Goto {
                target: 0,
                args: vec![var_i32("l2"), var_i32("b_sel")],
            },
        };
        let tail_model = model_back_edge_args(&f, b(1), b(2), &bindings, &HashSet::new())
            .expect("tail VC (latch=bb2) must model");
        let tail_bridge = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: tail_model.args,
        };
        let tail_outcome = back_edge_test_outcome(
            "two_vc_tail",
            &tail_spec,
            &tail_bridge,
            &guard,
            &tail_model.extra_inputs,
            &AYConfig::default(),
        )
        .unwrap();
        if let Some(reason) = crate::formal_gap::refinement_gap_reason(&tail_outcome) {
            crate::formal_gap::print_gap_skip(
                "tail_diamond_two_vc_paths_both_refine (tail VC)",
                reason,
            );
        } else {
            assert!(
                matches!(tail_outcome, RefinementOutcome::Refined),
                "the tail-diamond VC must refine"
            );
        }

        // VC #2 — straight-line-precond at latch=bb3 (the cond-TRUE slice: the
        // walk takes bb2's then edge under precond `a > b`, reaching bb3's
        // back-edge `(a', b') = (b, a-b)`).
        let sl_spec = MirBlock {
            stmts: vec![MirStmt {
                dst: "sub_ab".into(),
                rvalue: MirRvalue::BinaryOp {
                    op: MirBinOp::Sub,
                    ty: MirScalarTy::SInt(Type::I32),
                    lhs: var_i32("l1"),
                    rhs: var_i32("l2"),
                },
            }],
            terminator: MirTerminator::Goto {
                target: 0,
                args: vec![var_i32("l2"), var_i32("sub_ab")],
            },
        };
        let mut sl_preconds = guard.clone();
        sl_preconds.push(
            SmtExpr::var("l1", 32).bvsgt(SmtExpr::var("l2", 32)), // cond a > b true on this slice
        );
        let sl_model = model_back_edge_args(&f, b(1), b(3), &bindings, &HashSet::new())
            .expect("straight-line VC (latch=bb3) must model");
        let sl_bridge = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: sl_model.args,
        };
        let sl_outcome = back_edge_test_outcome(
            "two_vc_straightline",
            &sl_spec,
            &sl_bridge,
            &sl_preconds,
            &sl_model.extra_inputs,
            &AYConfig::default(),
        )
        .unwrap();
        if let Some(reason) = crate::formal_gap::refinement_gap_reason(&sl_outcome) {
            crate::formal_gap::print_gap_skip(
                "tail_diamond_two_vc_paths_both_refine (straight-line VC)",
                reason,
            );
        } else {
            assert!(
                matches!(sl_outcome, RefinementOutcome::Refined),
                "the straight-line-precond VC must also refine (both VCs of the tail loop hold)"
            );
        }
    }

    /// A diamond-body loop where EACH arm spans TWO blocks: the arm block
    /// (`t = a - b`) branches to a per-arm single-predecessor RETURN block
    /// (`t' = t + 0; br join(t')`) before the join — exactly the `-O0` shape of a
    /// `t = a.wrapping_sub(b)` call (arm block computes into a temp; the call's
    /// return block re-threads it to the join). Exercises the arm walker's HOP
    /// through the single-predecessor chain block.
    ///
    ///   bb3: %5 = sub a,b;  br bb7()          ; THEN arm (1 pred: bb2)
    ///   bb7: %20 = add %5,0; br bb6(%20)       ; then RETURN block (1 pred: bb3)
    ///   bb4: %6 = sub b,a;  br bb8()           ; ELSE arm (1 pred: bb2)
    ///   bb8: %21 = add %6,0; br bb6(%21)       ; else RETURN block (1 pred: bb4)
    ///   bb6(%7): br bb1(b, %7)                 ; JOIN (2 preds: bb7,bb8) = latch
    fn diamond_tir_multiblock(swap_join_args: bool) -> Function {
        let mut f = diamond_tir(false);
        // Re-point the THEN arm bb3 to a new return block bb7, and the ELSE arm
        // bb4 to bb8; each return block re-threads the arm value to the join bb6.
        {
            let bb3 = f.blocks.iter_mut().find(|blk| blk.id == b(3)).unwrap();
            bb3.body.clear();
            bb3.body.push(
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::I32,
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(5)),
            );
            bb3.body.push(InstrNode::new(Inst::Br {
                target: b(7),
                args: vec![],
            }));
        }
        {
            let bb4 = f.blocks.iter_mut().find(|blk| blk.id == b(4)).unwrap();
            bb4.body.clear();
            bb4.body.push(
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::I32,
                    lhs: v(11),
                    rhs: v(10),
                })
                .with_result(v(6)),
            );
            bb4.body.push(InstrNode::new(Inst::Br {
                target: b(8),
                args: vec![],
            }));
        }
        // Swap the join back-edge args in the multiblock variant too, so the
        // NEGATIVE case is the identical misthread (a'=t, b'=b) reached THROUGH
        // the hop. (The join bb6 already exists from `diamond_tir`; overwrite its
        // back-edge if swapping.)
        if swap_join_args {
            let bb6 = f.blocks.iter_mut().find(|blk| blk.id == b(6)).unwrap();
            bb6.body.clear();
            bb6.body.push(InstrNode::new(Inst::Br {
                target: b(1),
                args: vec![v(7), v(11)], // WRONG: a'=t, b'=b (swapped)
            }));
        }
        // THEN return block bb7: %20 = %5 + 0; br bb6(%20).
        let mut bb7 = Block::new(b(7));
        bb7.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(5),
                rhs: v(2), // %2 = const 0, defined in the header (dominates)
            })
            .with_result(v(20)),
        );
        bb7.body.push(InstrNode::new(Inst::Br {
            target: b(6),
            args: vec![v(20)],
        }));
        // ELSE return block bb8: %21 = %6 + 0; br bb6(%21).
        let mut bb8 = Block::new(b(8));
        bb8.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(6),
                rhs: v(2),
            })
            .with_result(v(21)),
        );
        bb8.body.push(InstrNode::new(Inst::Br {
            target: b(6),
            args: vec![v(21)],
        }));
        f.blocks.push(bb7);
        f.blocks.push(bb8);
        f
    }

    /// The multi-block-arm diamond MODELS (the hop through each call-return block
    /// works): the back-edge args are `(b, ite(a>b, a-b, b-a))`, identical to the
    /// single-block diamond — proving the intermediate blocks are traversed.
    #[test]
    fn diamond_loop_multiblock_arm_models_select_at_join() {
        let f = diamond_tir_multiblock(false);
        let model = model_back_edge_args(
            &f,
            b(1),
            b(6),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect("multi-block-arm diamond loop path must model (the hop must succeed)");
        assert_eq!(model.args.len(), 2);
        assert_eq!(model.args[0], SmtExpr::var("l2", 32));
        let free = model.args[1].free_vars();
        assert!(
            free.contains(&"l1".to_string()) && free.contains(&"l2".to_string()),
            "merged arg must mention both header vars, got free={free:?}"
        );
    }

    /// END-TO-END for the CALL-IN-ARM (multi-block) shape: the hopped IMPL model
    /// REFINES the MIR select spec, and a SWAPPED join back-edge reached THROUGH
    /// the hop is REFUTED. This is the soundness bite for the arm-walker hop: a
    /// misthread on the call-in-arm surface cannot be silently admitted.
    #[test]
    fn diamond_loop_multiblock_arm_refines_and_swap_refutes() {
        if !ay_bridge::z3_available() {
            eprintln!("skipping: z3 not available");
            return;
        }
        // SPEC: identical to the single-block end-to-end spec (the return blocks
        // are value-preserving), so a correct hop must refine it.
        let spec = MirBlock {
            stmts: vec![
                MirStmt {
                    dst: "cmp".into(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Gt,
                        ty: MirScalarTy::SInt(Type::I32),
                        lhs: var_i32("l1"),
                        rhs: var_i32("l2"),
                    },
                },
                MirStmt {
                    dst: "then_t".into(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Sub,
                        ty: MirScalarTy::SInt(Type::I32),
                        lhs: var_i32("l1"),
                        rhs: var_i32("l2"),
                    },
                },
                MirStmt {
                    dst: "else_t".into(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Sub,
                        ty: MirScalarTy::SInt(Type::I32),
                        lhs: var_i32("l2"),
                        rhs: var_i32("l1"),
                    },
                },
                MirStmt {
                    dst: "t".into(),
                    rvalue: MirRvalue::Select {
                        cond: MirOperand::Var {
                            name: "cmp".into(),
                            ty: MirScalarTy::Bool,
                        },
                        ty: MirScalarTy::SInt(Type::I32),
                        then_val: var_i32("then_t"),
                        else_val: var_i32("else_t"),
                    },
                },
            ],
            terminator: MirTerminator::Goto {
                target: 0,
                args: vec![var_i32("l2"), var_i32("t")],
            },
        };
        let preconds = vec![
            SmtExpr::var("l2", 32)
                .eq_expr(SmtExpr::bv_const(0, 32))
                .not_expr(),
        ];

        // POSITIVE: the correct multi-block (hopped) diamond refines.
        let f = diamond_tir_multiblock(false);
        let model = model_back_edge_args(
            &f,
            b(1),
            b(6),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect("multi-block diamond path must model");
        let bridge = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: model.args,
        };
        match back_edge_test_outcome(
            "e2e_multiblock_diamond",
            &spec,
            &bridge,
            &preconds,
            &model.extra_inputs,
            &AYConfig::default(),
        )
        .unwrap()
        {
            RefinementOutcome::Refined => {}
            other => {
                if let Some(reason) = crate::formal_gap::refinement_gap_reason(&other) {
                    crate::formal_gap::print_gap_skip(
                        "diamond_loop_multiblock_arm_refines_and_swap_refutes (positive half)",
                        reason,
                    );
                } else {
                    panic!("correct multi-block diamond must refine, got {other:?}")
                }
            }
        }

        // NEGATIVE: a SWAPPED back-edge reached through the hop must be refuted.
        let f_swap = diamond_tir_multiblock(true);
        let model_swap = model_back_edge_args(
            &f_swap,
            b(1),
            b(6),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect("swapped multi-block diamond path must still model");
        let bridge_swap = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: model_swap.args,
        };
        match check_back_edge_threading(
            "e2e_multiblock_diamond_swap",
            &spec,
            &bridge_swap,
            &preconds,
            &model_swap.extra_inputs,
            &AYConfig::default(),
        )
        .unwrap()
        {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!(
                "swapped multi-block diamond back-edge must be refuted (the hop must not \
                 hide a misthread), got {other:?}"
            ),
        }
    }

    // -----------------------------------------------------------------------
    // GUARD ON A DIAMOND ARM (step 7 of the ssa071 widening chain, re-checked
    // on its own). A `CondBr` on an ARM whose two targets split exactly one
    // IN-loop / one OUT-of-loop is a guard — what a MIR `Assert` (a bounds
    // check, an overflow check) lowers to — and `model_diamond_arm` follows the
    // surviving in-loop edge, recording NO path condition. Before these tests
    // nothing exercised that normalization on an arm: measured 2026-09-21 by
    // mutating both `(true, false)` / `(false, true)` arms to `Err`, all 30
    // tests of this module (and the whole `trust-cg-verify` lib) stayed green.
    // -----------------------------------------------------------------------

    /// `diamond_tir` with the THEN arm GUARDED and a TWO-param join, so the
    /// anti-swap half can misroute the guarded arm's own edge args:
    ///
    ///   bb1(%10: a, %11: b):  guard b != 0; condbr -> bb2 / bb5(exit)
    ///   bb2:  %4 = a > b; condbr %4 -> bb3 / bb4          ; diamond entry
    ///   bb3:  %5 = a - b                                  ; THEN arm
    ///         %8 = icmp ne %5, 0                          ;   guard: t != 0
    ///         condbr %8 -> bb6(%5, %11) / bb9             ;   bb9 = OUT of loop
    ///   bb4:  %6 = b - a; br bb6(%6, %11)                 ; ELSE arm
    ///   bb6(%7: t, %12: u): br bb1(%12, %7)               ; JOIN = latch: a'=u, b'=t
    ///   bb9:  return %10                                  ; the panic edge (never reaches bb6)
    ///   bb5:  return %10
    ///
    /// `swap_guarded_args` threads `bb6(%11, %5)` on the GUARDED edge only — the
    /// else arm stays correct, so a refutation witness must come THROUGH the
    /// guard (a > b), which is exactly what the anti-swap half must show.
    fn guarded_arm_diamond_tir(swap_guarded_args: bool) -> Function {
        let mut f = diamond_tir(false);
        {
            let bb3 = f.blocks.iter_mut().find(|blk| blk.id == b(3)).unwrap();
            bb3.body.clear();
            bb3.body.push(
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::I32,
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(5)),
            );
            bb3.body.push(
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ne,
                    ty: Ty::I32,
                    lhs: v(5),
                    rhs: v(2), // %2 = const 0, defined in the header (dominates)
                })
                .with_result(v(8)),
            );
            bb3.body.push(InstrNode::new(Inst::CondBr {
                cond: v(8),
                then_target: b(6),
                then_args: if swap_guarded_args {
                    vec![v(11), v(5)] // WRONG: (u, t) = (b, t) swapped into (t, u)
                } else {
                    vec![v(5), v(11)]
                },
                else_target: b(9),
                else_args: vec![],
            }));
        }
        {
            let bb4 = f.blocks.iter_mut().find(|blk| blk.id == b(4)).unwrap();
            let Some(InstrNode {
                inst: Inst::Br { args, .. },
                ..
            }) = bb4.body.last_mut()
            else {
                panic!("diamond_tir's else arm ends in a Br");
            };
            *args = vec![v(6), v(11)];
        }
        {
            let bb6 = f.blocks.iter_mut().find(|blk| blk.id == b(6)).unwrap();
            bb6.params.push((v(12), Ty::I32));
            bb6.body.clear();
            bb6.body.push(InstrNode::new(Inst::Br {
                target: b(1),
                args: vec![v(12), v(7)],
            }));
        }
        let mut bb9 = Block::new(b(9));
        bb9.body.push(InstrNode::new(Inst::Return {
            values: vec![v(10)],
        }));
        f.blocks.push(bb9);
        f
    }

    /// The guard on the THEN arm is TRANSPARENT to the model: the join param
    /// `t` is exactly the unguarded diamond's `ite(a > b, a - b, b - a)`, with the
    /// then-value `a - b` computed THROUGH the guarded block bb3 (nothing else
    /// defines `%5`), and `u` carries `b` on both arms. No opaque is minted and
    /// the guard's condition is nowhere in the args — it is a path condition the
    /// impl side deliberately does not record.
    ///
    /// MUTATION PIN: with the `(true, false)` / `(false, true)` arms of the
    /// arm-terminator normalization turned into `Err`, `model_back_edge_args`
    /// refuses the whole loop and this `expect` panics (measured 2026-09-21).
    #[test]
    fn guarded_arm_diamond_models_select_through_the_guard() {
        let bindings = [(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)];
        let model = model_back_edge_args(
            &guarded_arm_diamond_tir(false),
            b(1),
            b(6),
            &bindings,
            &::std::collections::HashSet::new(),
        )
        .expect("a guarded THEN arm (one in-loop, one out-of-loop target) must model");
        let plain = model_back_edge_args(
            &diamond_tir(false),
            b(1),
            b(6),
            &bindings,
            &::std::collections::HashSet::new(),
        )
        .expect("the unguarded diamond models");
        assert_eq!(model.args.len(), 2);
        // The EXACT merged term, built by hand: `taken` is the 1-bit `a > b`
        // discriminant compared against 0, exactly as the walk resolves a CondBr.
        let l1 = SmtExpr::var("l1", 32);
        let l2 = SmtExpr::var("l2", 32);
        let taken = SmtExpr::ite(
            l1.clone().bvsgt(l2.clone()),
            SmtExpr::bv_const(1, 1),
            SmtExpr::bv_const(0, 1),
        )
        .eq_expr(SmtExpr::bv_const(0, 1))
        .not_expr();
        assert_eq!(
            model.args[1],
            SmtExpr::ite(
                taken.clone(),
                l1.clone().bvsub(l2.clone()),
                l2.clone().bvsub(l1.clone())
            ),
            "b' must be ite(a > b, a - b, b - a) with the then-value taken THROUGH the guard"
        );
        assert_eq!(
            model.args[1], plain.args[1],
            "the guard must be transparent: same term as the unguarded diamond"
        );
        assert_eq!(
            model.args[0],
            SmtExpr::ite(taken, l2.clone(), l2),
            "a' is the carried b, merged over both arms"
        );
        assert!(
            model
                .extra_inputs
                .iter()
                .all(|(n, _)| !n.starts_with("__tir_op")),
            "no opaque should be minted on the fully-encoded guarded path, got {:?}",
            model.extra_inputs
        );
    }

    /// END-TO-END through the guard: the correct guarded diamond REFINES the
    /// MIR `select` spec (the spec side walks through an `Assert` on an arm and
    /// drops its condition the same way, so the spec is the plain diamond's),
    /// and the GUARDED edge with its two join args SWAPPED is REFUTED — a
    /// misroute that only manifests on the guarded arm (`a > b`), so the
    /// refutation witness passes through the guard. That half never gap-skips.
    #[test]
    fn guarded_arm_diamond_end_to_end_refines_and_swap_refutes() {
        if !ay_bridge::z3_available() {
            eprintln!("skipping: z3 not available");
            return;
        }
        let spec = MirBlock {
            stmts: vec![
                MirStmt {
                    dst: "cmp".into(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Gt,
                        ty: MirScalarTy::SInt(Type::I32),
                        lhs: var_i32("l1"),
                        rhs: var_i32("l2"),
                    },
                },
                MirStmt {
                    dst: "then_t".into(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Sub,
                        ty: MirScalarTy::SInt(Type::I32),
                        lhs: var_i32("l1"),
                        rhs: var_i32("l2"),
                    },
                },
                MirStmt {
                    dst: "else_t".into(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Sub,
                        ty: MirScalarTy::SInt(Type::I32),
                        lhs: var_i32("l2"),
                        rhs: var_i32("l1"),
                    },
                },
                MirStmt {
                    dst: "t".into(),
                    rvalue: MirRvalue::Select {
                        cond: MirOperand::Var {
                            name: "cmp".into(),
                            ty: MirScalarTy::Bool,
                        },
                        ty: MirScalarTy::SInt(Type::I32),
                        then_val: var_i32("then_t"),
                        else_val: var_i32("else_t"),
                    },
                },
            ],
            terminator: MirTerminator::Goto {
                target: 0,
                args: vec![var_i32("l2"), var_i32("t")],
            },
        };
        // Only the loop guard. The arm guard `t != 0` is deliberately NOT a
        // precondition: neither side records it, and the VC must hold on the
        // enlarged space (it does — the guard changes no threaded value).
        let preconds = vec![
            SmtExpr::var("l2", 32)
                .eq_expr(SmtExpr::bv_const(0, 32))
                .not_expr(),
        ];
        let bindings = [(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)];
        let run = |swap: bool| {
            let f = guarded_arm_diamond_tir(swap);
            let model = model_back_edge_args(
                &f,
                b(1),
                b(6),
                &bindings,
                &::std::collections::HashSet::new(),
            )
            .expect("a guarded diamond arm must model (swapped or not)");
            check_back_edge_threading(
                if swap {
                    "guarded_arm_swap"
                } else {
                    "guarded_arm_ok"
                },
                &spec,
                &BridgeEdgeArgs {
                    edge: EdgeKind::Goto,
                    args: model.args,
                },
                &preconds,
                &model.extra_inputs,
                &AYConfig::default(),
            )
            .unwrap()
        };
        match run(false) {
            RefinementOutcome::Refined => {}
            other => {
                if let Some(reason) = crate::formal_gap::refinement_gap_reason(&other) {
                    crate::formal_gap::print_gap_skip(
                        "guarded_arm_diamond_end_to_end (positive half)",
                        reason,
                    );
                } else {
                    panic!("the correct guarded diamond must refine end-to-end, got {other:?}")
                }
            }
        }
        // THE LOAD-BEARING HALF: a swap on the guarded edge's own args MUST be
        // caught; a `Refuted` is never gap-skipped.
        match run(true) {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!(
                "swapped join args on the GUARDED arm must be refuted (the guard must not \
                 hide a misthread), got {other:?}"
            ),
        }
    }

    /// The normalization admits EXACTLY the one-in / one-out split: a `CondBr`
    /// on an arm with BOTH targets in-loop is a nested diamond and stays out of
    /// model, fail closed. Pinned on the same fixture so the only difference
    /// from the admitted shape is where the guard's other edge lands.
    ///
    /// (The `(false, false)` arm is unreachable by construction and is not
    /// pinned: every non-header member of `natural_loop_blocks` — and of the
    /// tail-arm augmentation — was enqueued as a predecessor of a member, so it
    /// has at least one in-set successor; an arm block with NO in-loop
    /// successor is refused at the arm-entry check as "not a forward in-loop
    /// block" before its terminator is ever classified.)
    #[test]
    fn guarded_arm_condbr_with_both_targets_in_loop_is_rejected() {
        let bindings = [(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)];
        // BOTH in-loop: make the "panic" block bb9 reach the join (and so the
        // latch) — it is now inside the natural loop, and bb3's CondBr is a
        // genuine nested diamond.
        let mut both = guarded_arm_diamond_tir(false);
        {
            let bb9 = both.blocks.iter_mut().find(|blk| blk.id == b(9)).unwrap();
            bb9.body.clear();
            bb9.body.push(InstrNode::new(Inst::Br {
                target: b(6),
                args: vec![v(10), v(11)],
            }));
        }
        let err = model_back_edge_args(&both, b(1), b(6), &bindings, &HashSet::new())
            .expect_err("a nested diamond on an arm must be refused");
        assert!(
            err.contains("BOTH targets in-loop"),
            "expected the nested-diamond refusal on bb3, got: {err}"
        );
    }

    /// THE SOUNDNESS QUESTION the ssa071 write-up left open, answered on a
    /// constructed shape: the guard records NO path condition — is there a CFG
    /// where the out-of-loop edge still reaches THIS latch, so that "an execution
    /// taking it never reaches this back-edge" is false?
    ///
    /// The only route an out-of-`loop_set` block has to the latch runs THROUGH
    /// THE HEADER (`natural_loop_blocks` is exactly "reaches the latch without
    /// passing the header"; the augmented tail-arm set only adds blocks that
    /// reach the header). Here the guard's failure edge does exactly that — bb9
    /// re-enters the header (a `continue`-shaped retry), so it DOES reach bb6
    /// again, on the NEXT iteration:
    ///
    ///   bb3: %5 = a - b; %8 = (%5 != 0); condbr %8 -> bb6(%5, %11) / bb9
    ///   bb9: br bb1(%10, %11)                    ; a second back-edge
    ///
    /// That route is a different header entry, so it is a different instance of
    /// the per-iteration obligation "the args this latch threads equal the spec
    /// over the params of the most recent header entry" — and it is a different
    /// BACK-EDGE, with its own latch (bb9) and its own VC. Pinned two ways:
    ///
    /// * the bb6 VC is byte-identical to the one where bb9 exits for good — the
    ///   other route is invisible to this obligation, which is right because it
    ///   passes through the header;
    /// * the bb9 VC models on its own, and its natural loop is `{bb1,bb2,bb3,bb9}`
    ///   — bb3's `CondBr` classifies the OTHER way there (`(false, true)`),
    ///   bb6/bb4 are outside it, and its args are the unchanged `(a, b)`.
    ///
    /// Dropping the guard condition is therefore safe in the one direction it is
    /// used: the VC is `forall inputs. preconds => impl == spec`, the model is a
    /// total extension of the real (partial) back-edge function, and equality on
    /// the larger space implies it on the real domain. What it does NOT claim,
    /// and no path condition would make it claim, is that the guard's condition
    /// itself is the MIR assert's — that is a separate obligation.
    #[test]
    fn guard_exit_re_entering_the_header_is_another_back_edge_not_this_one() {
        let bindings = [(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)];
        let mut f = guarded_arm_diamond_tir(false);
        {
            let bb9 = f.blocks.iter_mut().find(|blk| blk.id == b(9)).unwrap();
            bb9.body.clear();
            bb9.body.push(InstrNode::new(Inst::Br {
                target: b(1),
                args: vec![v(10), v(11)],
            }));
        }
        // bb9 is NOT in this latch's natural loop (it is a predecessor of the
        // header, not of bb6), so bb3's CondBr still classifies as a guard here.
        let set = natural_loop_blocks(&f, b(1), b(6));
        assert!(
            !set.contains(&b(9)) && set.contains(&b(3)) && set.contains(&b(4)),
            "natural loop of (bb1, bb6) must be {{bb1, bb2, bb3, bb4, bb6}}, got {set:?}"
        );
        let this = model_back_edge_args(&f, b(1), b(6), &bindings, &HashSet::new())
            .expect("the bb6 back-edge must model with the guard's exit re-entering the header");
        let exiting = model_back_edge_args(
            &guarded_arm_diamond_tir(false),
            b(1),
            b(6),
            &bindings,
            &HashSet::new(),
        )
        .expect("the exiting variant models");
        assert_eq!(
            this.args, exiting.args,
            "a guard exit that re-enters the header is invisible to THIS latch's obligation"
        );
        // The other route IS a back-edge of its own, and its VC sees bb3's CondBr
        // from the other side: bb9 is in-loop, bb6 is not.
        let other_set = natural_loop_blocks(&f, b(1), b(9));
        assert!(
            other_set.contains(&b(9))
                && other_set.contains(&b(3))
                && !other_set.contains(&b(6))
                && !other_set.contains(&b(4)),
            "natural loop of (bb1, bb9) must be {{bb1, bb2, bb3, bb9}}, got {other_set:?}"
        );
        let other = model_back_edge_args(&f, b(1), b(9), &bindings, &HashSet::new())
            .expect("the bb9 back-edge must model as the guard-failure path");
        assert_eq!(
            other.args,
            vec![SmtExpr::var("l1", 32), SmtExpr::var("l2", 32)],
            "the retry back-edge threads (a, b) unchanged"
        );
    }

    // -----------------------------------------------------------------------
    // END-TO-END: trust-ir symexec (implementation) vs MIR model (spec),
    // discharged through `mir_semantics::check_back_edge_threading` — the
    // exact composition the bridge gate wires up, at the REAL i32 width.
    // -----------------------------------------------------------------------

    use crate::ay_bridge::{self, AYConfig};
    use crate::mir_semantics::{
        BridgeEdgeArgs, EdgeKind, MirBinOp, MirBlock, MirOperand, MirRvalue, MirScalarTy, MirStmt,
        MirTerminator, RefinementOutcome, check_back_edge_threading, discharge_back_edge_threading,
    };
    use trust_cg_lower::types::Type;

    /// [`check_back_edge_threading`] as a guarded test must read it: every
    /// slot is discharged and the verdicts are folded by
    /// `crate::formal_gap::test_outcome`, so a disclosed hole on one slot cannot
    /// stand in for another slot's failure.
    fn back_edge_test_outcome(
        name_prefix: &str,
        latch: &MirBlock,
        bridge_latch: &BridgeEdgeArgs,
        preconditions: &[SmtExpr],
        extra_inputs: &[(String, u32)],
        config: &AYConfig,
    ) -> Result<RefinementOutcome, String> {
        discharge_back_edge_threading(
            name_prefix,
            latch,
            bridge_latch,
            preconditions,
            extra_inputs,
            config,
        )
        .map(|verdicts| crate::formal_gap::test_outcome(name_prefix, &verdicts))
    }

    fn var_i32(name: &str) -> MirOperand {
        MirOperand::Var {
            name: name.to_string(),
            ty: MirScalarTy::SInt(Type::I32),
        }
    }

    /// The euclid SPEC latch, as the bridge derives it from the MIR path
    /// `bb1 (header) -> bb2 -> bb3 -> bb4 (latch)`:
    ///   `t = b; b' = a % b; a' = t;` then `Goto header (a', b')`,
    /// with the source-derived preconditions `b != 0` (divide-by-zero assert /
    /// loop guard) and `!(b == -1 && a == MIN)` (the `%` overflow assert).
    fn euclid_spec() -> (MirBlock, Vec<SmtExpr>) {
        let block = MirBlock {
            stmts: vec![
                MirStmt {
                    dst: "t".into(),
                    rvalue: MirRvalue::Use { src: var_i32("l2") },
                },
                MirStmt {
                    dst: "l2".into(),
                    rvalue: MirRvalue::BinaryOp {
                        op: MirBinOp::Rem,
                        ty: MirScalarTy::SInt(Type::I32),
                        lhs: var_i32("l1"),
                        rhs: var_i32("l2"),
                    },
                },
                MirStmt {
                    dst: "l1".into(),
                    rvalue: MirRvalue::Use { src: var_i32("t") },
                },
            ],
            terminator: MirTerminator::Goto {
                target: 0,
                args: vec![var_i32("l1"), var_i32("l2")],
            },
        };
        let a = SmtExpr::var("l1", 32);
        let b = SmtExpr::var("l2", 32);
        let zero = SmtExpr::bv_const(0, 32);
        let minus1 = SmtExpr::bv_const(u64::MAX, 32);
        let int_min = SmtExpr::bv_const(1 << 31, 32);
        let preconds = vec![
            b.clone().eq_expr(zero).not_expr(),
            b.eq_expr(minus1).and_expr(a.eq_expr(int_min)).not_expr(),
        ];
        (block, preconds)
    }

    /// POSITIVE (the euclid fix): the produced trust-ir rotation, symbolically
    /// executed, REFINES the MIR spec at the real i32 width — including the
    /// raw `SRem` vs trap-sentinel `Rem` difference, which the source-derived
    /// preconditions exclude. This is the exact judgment that turns euclid's
    /// structural false positive into a proven admit.
    #[test]
    fn euclid_end_to_end_rotation_refines() {
        if !ay_bridge::z3_available() {
            eprintln!("skipping: z3 not available");
            return;
        }
        let f = euclid_tir();
        let model = model_back_edge_args(
            &f,
            b(1),
            b(2),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect("euclid path must model");
        let (spec, preconds) = euclid_spec();
        let bridge = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: model.args,
        };
        match back_edge_test_outcome(
            "e2e_euclid",
            &spec,
            &bridge,
            &preconds,
            &model.extra_inputs,
            &AYConfig::default(),
        )
        .unwrap()
        {
            RefinementOutcome::Refined => {}
            other => {
                if let Some(reason) = crate::formal_gap::refinement_gap_reason(&other) {
                    crate::formal_gap::print_gap_skip(
                        "euclid_end_to_end_rotation_refines (positive half)",
                        reason,
                    );
                } else {
                    panic!("euclid rotation must refine end-to-end, got {other:?}")
                }
            }
        }
    }

    /// NEGATIVE (soundness): the SAME pipeline applied to a trust-ir function
    /// whose latch SWAPS the two back-edge args (`br header(%4, %11)` instead
    /// of `br header(%11, %4)`) is REFUTED — the genuine misthread keeps
    /// failing closed end-to-end. Mutation probe: the unswapped function on the
    /// identical spec refines (`euclid_end_to_end_rotation_refines`).
    #[test]
    fn euclid_end_to_end_swapped_latch_is_refuted() {
        if !ay_bridge::z3_available() {
            eprintln!("skipping: z3 not available");
            return;
        }
        let mut f = euclid_tir();
        {
            let bb2 = f.blocks.iter_mut().find(|blk| blk.id == b(2)).unwrap();
            let term = bb2.body.last_mut().unwrap();
            term.inst = Inst::Br {
                target: b(1),
                args: vec![v(4), v(11)], // SWAPPED
            };
        }
        let model = model_back_edge_args(
            &f,
            b(1),
            b(2),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect("swapped euclid path must still model");
        let (spec, preconds) = euclid_spec();
        let bridge = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: model.args,
        };
        match check_back_edge_threading(
            "e2e_swapped",
            &spec,
            &bridge,
            &preconds,
            &model.extra_inputs,
            &AYConfig::default(),
        )
        .unwrap()
        {
            RefinementOutcome::Refuted { counterexample } => {
                assert!(
                    !counterexample.is_empty(),
                    "refutation carries a counterexample"
                );
            }
            other => panic!("swapped latch must be refuted end-to-end, got {other:?}"),
        }
    }

    /// NEGATIVE (the #71 stale-thread): a latch that re-threads the STALE header
    /// `a` (param %10) into slot 0 instead of the rotated old `b` is REFUTED.
    #[test]
    fn euclid_end_to_end_stale_latch_is_refuted() {
        if !ay_bridge::z3_available() {
            eprintln!("skipping: z3 not available");
            return;
        }
        let mut f = euclid_tir();
        {
            let bb2 = f.blocks.iter_mut().find(|blk| blk.id == b(2)).unwrap();
            let term = bb2.body.last_mut().unwrap();
            term.inst = Inst::Br {
                target: b(1),
                args: vec![v(10), v(4)], // STALE a in slot 0
            };
        }
        let model = model_back_edge_args(
            &f,
            b(1),
            b(2),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect("stale euclid path must still model");
        let (spec, preconds) = euclid_spec();
        let bridge = BridgeEdgeArgs {
            edge: EdgeKind::Goto,
            args: model.args,
        };
        match check_back_edge_threading(
            "e2e_stale",
            &spec,
            &bridge,
            &preconds,
            &model.extra_inputs,
            &AYConfig::default(),
        )
        .unwrap()
        {
            RefinementOutcome::Refuted { .. } => {}
            other => panic!("stale latch must be refuted end-to-end, got {other:?}"),
        }
    }

    /// [`diamond_tir`] with the diamond entry's `CondBr` replaced by an
    /// INTEGER-selector `Inst::Switch` — the shape the bridge emits for a
    /// non-bool `SwitchInt` (rustc's inlined `checked_div`/`checked_rem`
    /// zero-guard). Selector = the header param `l2`; `case 0 -> bb4`,
    /// `default -> bb3`. When `extra_successor` is set a third (out-of-loop)
    /// case is added, which must fail closed.
    fn switch_diamond_tir(extra_successor: bool) -> Function {
        let mut f = diamond_tir(false);
        let bb2 = f.blocks.iter_mut().find(|blk| blk.id == b(2)).unwrap();
        bb2.body.clear();
        let mut cases = vec![SwitchCase {
            value: Constant::Int(0),
            target: b(4),
            args: vec![],
        }];
        if extra_successor {
            cases.push(SwitchCase {
                value: Constant::Int(1),
                target: b(5), // the RETURN block: outside the loop
                args: vec![],
            });
        }
        bb2.body.push(InstrNode::new(Inst::Switch {
            value: v(11),
            default: b(3),
            default_args: vec![],
            cases,
            exhaustive_enum_unreachable: false,
        }));
        f
    }

    /// An integer-selector `Inst::Switch` whose two arms are both in-loop and
    /// reconverge is modeled as `ite(no case matches, default_arg, case_arg)` at
    /// the join — the same merge the `CondBr` diamond gets. Before this the
    /// whole non-bool-discriminant class bailed with "multiple distinct in-loop
    /// successors".
    #[test]
    fn switch_diamond_models_ite_at_join() {
        let f = switch_diamond_tir(false);
        let model = model_back_edge_args(
            &f,
            b(1),
            b(6),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect("integer-switch diamond must model");
        assert_eq!(model.args.len(), 2);
        assert_eq!(model.args[0], SmtExpr::var("l2", 32));
        // THEN = the CASE arm (`case 0 -> bb4`, computing b-a), ELSE = the
        // DEFAULT arm (`bb3`, computing a-b) — the same orientation the MIR spec
        // side uses. The predicate is built in the spec's 1-bit carrier domain
        // (`bool1(sel == 0) != 0`) so the two sides can come out term-identical.
        let expected = SmtExpr::ite(
            SmtExpr::ite(
                SmtExpr::var("l2", 32).eq_expr(SmtExpr::bv_const(0, 32)),
                SmtExpr::bv_const(1, 1),
                SmtExpr::bv_const(0, 1),
            )
            .eq_expr(SmtExpr::bv_const(0, 1))
            .not_expr(),
            SmtExpr::var("l2", 32).bvsub(SmtExpr::var("l1", 32)),
            SmtExpr::var("l1", 32).bvsub(SmtExpr::var("l2", 32)),
        );
        assert_eq!(model.args[1], expected, "got {:?}", model.args[1]);
        assert!(
            model
                .extra_inputs
                .iter()
                .all(|(n, _)| !n.starts_with("__tir_")),
            "no opaque should be minted on the fully-encoded switch diamond"
        );
    }

    /// NEGATIVE: a switch with a THIRD distinct successor means some selector
    /// values leave the region here, so a 2-way `ite` is not an exact model of
    /// which edge was taken. Fail closed.
    #[test]
    fn switch_with_three_distinct_successors_fails_closed() {
        let f = switch_diamond_tir(true);
        let err = model_back_edge_args(
            &f,
            b(1),
            b(6),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect_err("a 3-way switch must stay out of model");
        assert!(
            err.contains("distinct successors") || err.contains("in-loop"),
            "unexpected diagnosis: {err}"
        );
    }

    /// STAGE-0 PIN. A value flowing from an UNMODELED instruction (an
    /// unforwardable load) into a back-edge arg is an `Err` — "out of model" —
    /// NOT an expression handed to the solver.
    ///
    /// The pre-Stage-0 contract was the opposite (bind an opaque and let the
    /// obligation refute). That is strictly worse: an opaque can only make the
    /// threading equality SAT, so the operator saw `REFUTED (counterexample …)`,
    /// which reads exactly like a miscompile, for a program the model simply did
    /// not understand. The compile declines either way; this pins WHICH decline.
    /// It is also what makes it safe to widen the modeled control flow, whose
    /// new arms materialize `Option<iN>` through memory.
    #[test]
    fn unmodeled_opaque_in_a_back_edge_arg_is_an_error_not_a_refutation() {
        let mut f = euclid_tir();
        {
            let bb2 = f.blocks.iter_mut().find(|blk| blk.id == b(2)).unwrap();
            bb2.body.clear();
            // A load through a pointer with no store in the window: unforwardable.
            bb2.body.push(
                InstrNode::new(Inst::Load {
                    ty: Ty::I32,
                    ptr: v(12),
                    volatile: false,
                    align: None,
                })
                .with_result(v(4)),
            );
            bb2.body.push(InstrNode::new(Inst::Br {
                target: b(1),
                args: vec![v(11), v(4)],
            }));
        }
        let err = model_back_edge_args(
            &f,
            b(1),
            b(2),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect_err("an unmodeled load feeding the back-edge must be out of model");
        assert!(
            err.contains("unmodeled trust-ir value"),
            "expected an out-of-model diagnosis, got: {err}"
        );
        assert!(
            !err.contains("REFUTED"),
            "an out-of-model shape must never read as a refutation: {err}"
        );
    }

    /// A `Store` followed by a `Load` at the SYNTACTICALLY IDENTICAL address —
    /// including the `PtrToInt` / `+k` / `IntToPtr` round trip the bridge emits
    /// when it materializes an aggregate on the stack — forwards the stored
    /// value instead of minting an opaque. Without this the `Option<iN>` payload
    /// an inlined `checked_div` arm threads is unmodelable.
    #[test]
    fn ptr_roundtrip_and_same_pointer_store_load_forwards() {
        let mut f = euclid_tir();
        {
            let bb2 = f.blocks.iter_mut().find(|blk| blk.id == b(2)).unwrap();
            bb2.body.clear();
            // slot = alloca; p = (slot as int) + 8 as ptr; store p <- l2; t = load p
            bb2.body.push(
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I32,
                    count: None,
                    align: None,
                })
                .with_result(v(20)),
            );
            bb2.body.push(
                InstrNode::new(Inst::Cast {
                    op: CastOp::PtrToInt,
                    src_ty: Ty::Ptr,
                    dst_ty: Ty::I64,
                    operand: v(20),
                })
                .with_result(v(21)),
            );
            bb2.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(8),
                })
                .with_result(v(22)),
            );
            bb2.body.push(
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: v(21),
                    rhs: v(22),
                })
                .with_result(v(23)),
            );
            bb2.body.push(
                InstrNode::new(Inst::Cast {
                    op: CastOp::IntToPtr,
                    src_ty: Ty::I64,
                    dst_ty: Ty::Ptr,
                    operand: v(23),
                })
                .with_result(v(24)),
            );
            bb2.body.push(InstrNode::new(Inst::Store {
                ty: Ty::I32,
                ptr: v(24),
                value: v(11),
                volatile: false,
                align: None,
            }));
            // Re-derive the SAME address independently, then load it.
            bb2.body.push(
                InstrNode::new(Inst::Cast {
                    op: CastOp::PtrToInt,
                    src_ty: Ty::Ptr,
                    dst_ty: Ty::I64,
                    operand: v(20),
                })
                .with_result(v(25)),
            );
            bb2.body.push(
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: v(25),
                    rhs: v(22),
                })
                .with_result(v(26)),
            );
            bb2.body.push(
                InstrNode::new(Inst::Cast {
                    op: CastOp::IntToPtr,
                    src_ty: Ty::I64,
                    dst_ty: Ty::Ptr,
                    operand: v(26),
                })
                .with_result(v(27)),
            );
            bb2.body.push(
                InstrNode::new(Inst::Load {
                    ty: Ty::I32,
                    ptr: v(27),
                    volatile: false,
                    align: None,
                })
                .with_result(v(4)),
            );
            bb2.body.push(InstrNode::new(Inst::Br {
                target: b(1),
                args: vec![v(11), v(4)],
            }));
        }
        let model = model_back_edge_args(
            &f,
            b(1),
            b(2),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect("a same-address store/load window must forward, not go opaque");
        // Slot 1 is the loaded value: it must be `l2`, with no `__tir_*` in it.
        assert_eq!(model.args[1], SmtExpr::var("l2", 32), "{:?}", model.args[1]);
    }

    /// NEGATIVE: an intervening non-identity `Call` can write memory
    /// arbitrarily, so the window is poisoned and the load stays unmodeled
    /// (Stage-0 then declines rather than refuting).
    #[test]
    fn intervening_call_poisons_the_store_map() {
        let mut f = euclid_tir();
        {
            let bb2 = f.blocks.iter_mut().find(|blk| blk.id == b(2)).unwrap();
            bb2.body.clear();
            bb2.body.push(
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I32,
                    count: None,
                    align: None,
                })
                .with_result(v(20)),
            );
            bb2.body.push(InstrNode::new(Inst::Store {
                ty: Ty::I32,
                ptr: v(20),
                value: v(11),
                volatile: false,
                align: None,
            }));
            bb2.body.push(
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(7),
                    args: vec![v(20)],
                })
                .with_result(v(30)),
            );
            bb2.body.push(
                InstrNode::new(Inst::Load {
                    ty: Ty::I32,
                    ptr: v(20),
                    volatile: false,
                    align: None,
                })
                .with_result(v(4)),
            );
            bb2.body.push(InstrNode::new(Inst::Br {
                target: b(1),
                args: vec![v(11), v(4)],
            }));
        }
        let err = model_back_edge_args(
            &f,
            b(1),
            b(2),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect_err("a call between the store and the load must stop forwarding");
        assert!(
            err.contains("unmodeled trust-ir value"),
            "expected an out-of-model diagnosis, got: {err}"
        );
    }

    /// NEGATIVE: a load at a DIFFERENT offset than the store does not forward.
    #[test]
    fn differing_offset_store_does_not_forward() {
        let mut f = euclid_tir();
        {
            let bb2 = f.blocks.iter_mut().find(|blk| blk.id == b(2)).unwrap();
            bb2.body.clear();
            bb2.body.push(
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I32,
                    count: None,
                    align: None,
                })
                .with_result(v(20)),
            );
            bb2.body.push(
                InstrNode::new(Inst::Cast {
                    op: CastOp::PtrToInt,
                    src_ty: Ty::Ptr,
                    dst_ty: Ty::I64,
                    operand: v(20),
                })
                .with_result(v(21)),
            );
            bb2.body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(8),
                })
                .with_result(v(22)),
            );
            bb2.body.push(
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: v(21),
                    rhs: v(22),
                })
                .with_result(v(23)),
            );
            bb2.body.push(
                InstrNode::new(Inst::Cast {
                    op: CastOp::IntToPtr,
                    src_ty: Ty::I64,
                    dst_ty: Ty::Ptr,
                    operand: v(23),
                })
                .with_result(v(24)),
            );
            // store at +8 ...
            bb2.body.push(InstrNode::new(Inst::Store {
                ty: Ty::I32,
                ptr: v(24),
                value: v(11),
                volatile: false,
                align: None,
            }));
            // ... load at +0.
            bb2.body.push(
                InstrNode::new(Inst::Load {
                    ty: Ty::I32,
                    ptr: v(20),
                    volatile: false,
                    align: None,
                })
                .with_result(v(4)),
            );
            bb2.body.push(InstrNode::new(Inst::Br {
                target: b(1),
                args: vec![v(11), v(4)],
            }));
        }
        let err = model_back_edge_args(
            &f,
            b(1),
            b(2),
            &[(v(10), "l1".to_string(), 32), (v(11), "l2".to_string(), 32)],
            &::std::collections::HashSet::new(),
        )
        .expect_err("a differing-offset load must not forward");
        assert!(
            err.contains("unmodeled trust-ir value"),
            "expected an out-of-model diagnosis, got: {err}"
        );
    }
}
