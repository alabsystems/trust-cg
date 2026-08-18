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
//   * The walk REFUSES (returns `Err`, the caller fails the compile closed)
//     any shape it cannot model exactly: a diamond inside the loop (two
//     in-loop successors), a nested back-edge before the latch, a conditional
//     back-edge, a `Switch` with an ambiguous in-loop continuation, a latch
//     that does not end in `Br header(..)`, a width mismatch anywhere.
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
struct Env {
    /// ValueId -> its symbolic value.
    vals: HashMap<ValueId, SmtExpr>,
    /// ValueIds produced by instructions we cannot even WIDTH-type. Resolving
    /// one of these is an error (fail closed), not an opaque.
    untyped: HashSet<ValueId>,
    /// Inputs minted (bindings + opaques), deduped by name.
    inputs: Vec<(String, u32)>,
    opaque_counter: u32,
    /// `FuncId`s of value-IDENTITY calls (`core::hint::black_box`): a `Call` to one
    /// is modeled as `result = arg` rather than left untyped, so a loop whose
    /// bound/inputs are black-boxed can be PROVEN. Restricted by the caller to the
    /// genuine std `black_box` (never a user fn) so this is sound.
    identity_calls: HashSet<FuncId>,
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

    /// Mint a fresh opaque input of the given width.
    fn fresh_opaque(&mut self, width: u32) -> Result<SmtExpr, String> {
        let name = format!("__tir_op{}", self.opaque_counter);
        self.opaque_counter += 1;
        self.declare_input(&name, width)?;
        Ok(SmtExpr::var(name, width))
    }

    /// Bind a ValueId to an opaque input of the given width.
    fn bind_opaque(&mut self, v: ValueId, width: u32) -> Result<(), String> {
        let name = format!("__tir_v{}", v.index());
        self.declare_input(&name, width)?;
        self.vals.insert(v, SmtExpr::var(name, width));
        Ok(())
    }

    /// Resolve a ValueId at an EXPECTED width. A bound value must match the
    /// width exactly; an unbound value becomes a fresh opaque input (a value
    /// defined outside the walked path — sound: opacity can only cause a
    /// fail-closed refutation, never an admission).
    fn resolve(&mut self, v: ValueId, expected_width: u32) -> Result<SmtExpr, String> {
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
                Constant::Bool(bv) if w == 1 => {
                    bind1(env, results, SmtExpr::bv_const(*bv as u64, 1))
                }
                // Wide / float / aggregate constants: opaque (sound).
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
                    let in_range = r.bvult(SmtExpr::bv_const(u64::from(w), w));
                    let opaque = env.fresh_opaque(w)?;
                    SmtExpr::ite(in_range, raw, opaque)
                }
                BinOp::FAdd
                | BinOp::FSub
                | BinOp::FMul
                | BinOp::FDiv
                | BinOp::FRem
                | BinOp::FMin
                | BinOp::FMax => {
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
                | UnOp::CtPop => bind_opaques(env, results, &[w]),
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
                // Everything else (FP converts, pointer casts, ...): opaque.
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
        // Width-typeable but unmodeled value producers: opaque results.
        Inst::Load { ty, .. } | Inst::AtomicLoad { ty, .. } | Inst::AtomicRMW { ty, .. } => {
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
            // into a Refine — never a wrong admit. Width <= 64 + the 3 arithmetic
            // overflow ops only; i128 / unexpected result arity stay opaque (sound).
            Some(w) if w <= 64 && results.len() == 2 => {
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
            // Wide (i128) value, or an unexpected (value, flag) result shape:
            // opaque both, exactly as before (sound — only ever a fail-closed).
            Some(w) => bind_opaques(env, results, &[w, 1]),
            None => {
                for r in results {
                    env.untyped.insert(*r);
                }
                Ok(())
            }
        },
        Inst::Undef { ty } => match ty_bit_width(ty) {
            Some(w) => bind_opaques(env, results, &[w]),
            None => {
                for r in results {
                    env.untyped.insert(*r);
                }
                Ok(())
            }
        },
        Inst::Alloca { .. }
        | Inst::HeapAlloc { .. }
        | Inst::GEP { .. }
        | Inst::PtrData { .. }
        | Inst::GlobalAddr { .. }
        | Inst::NullPtr => bind_opaques(env, results, &vec![64; results.len()]),
        // No results / pure effects: nothing to bind. (Stores and fences do not
        // affect this register-value model; loads are opaque anyway.)
        Inst::Store { .. } | Inst::AtomicStore { .. } | Inst::Fence { .. } => Ok(()),
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
        match &term.inst {
            // A straight-line chain block: thread the incoming edge args into its
            // params, execute its body, then follow its `Br`.
            Inst::Br { target, args } => {
                thread_args_into_params(env, arm_block, &cur_args)?;
                for node in body {
                    exec_inst(env, &node.inst, &node.results)?;
                }
                if *target == header {
                    // A TAIL diamond arm reconverges AT the header (the whole
                    // diamond is the loop tail). Accept it as the join only when
                    // the caller opts in; a MID-loop diamond arm branching to the
                    // header is a nested back-edge, out of model (fail closed).
                    if allow_header_join {
                        return Ok(DiamondArm {
                            join: header,
                            join_args: args.clone(),
                        });
                    }
                    return Err(format!(
                        "diamond arm {cur:?} branches back to the header (nested back-edge \
                         in an arm is out of model)"
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
                    join_args: args.clone(),
                });
            }
            // Any other arm terminator (a nested CondBr/Switch = nested diamond, a
            // Return, an Unreachable) is out of model — fail closed.
            other => {
                return Err(format!(
                    "diamond arm {cur:?} does not end in a single `Br` to the join \
                     (got {other:?}); nested/branching arms are out of model"
                ));
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
#[allow(clippy::too_many_arguments)]
fn model_in_loop_diamond(
    env: &mut Env,
    func: &Function,
    loop_set: &HashSet<BlockId>,
    header: BlockId,
    diamond_entry: BlockId,
    cond: ValueId,
    then_target: BlockId,
    then_args: &[ValueId],
    else_target: BlockId,
    else_args: &[ValueId],
) -> Result<BlockId, String> {
    // The diamond discriminant: a 1-bit value the bridge branches on (`!= 0` is
    // the THEN edge, mirroring `Inst::CondBr`). Resolved over the SAME env as the
    // arms, so the `ite` is over the same free vars as the threading equality.
    let cond_expr = env.resolve(cond, 1)?;

    // The two arms must reconverge at ONE join block, neither being the other
    // (a 2-way diamond, not a triangle that re-enters an arm). An arm whose
    // target IS the other arm is a sequential (non-reconverging) shape.
    if then_target == else_target {
        return Err(format!(
            "diamond at {diamond_entry:?} has both arms targeting the same block \
             {then_target:?} (degenerate; out of model)"
        ));
    }
    // Predecessor counts (computed once) let each arm HOP through its own
    // single-predecessor call-return blocks and stop at the shared join.
    let pred_counts = predecessor_counts(func);
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
    if join_id == header {
        return Err(format!(
            "diamond at {diamond_entry:?} reconverges at the header (out of model)"
        ));
    }
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
        // `ite(cond != 0, then, else)` — the bridge's merge value for this slot.
        let taken = cond_expr
            .clone()
            .eq_expr(SmtExpr::bv_const(0, 1))
            .not_expr();
        let merged = SmtExpr::ite(taken, then_val, else_val);
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
    let loop_set = natural_loop_blocks(func, header, latch);
    let header_block = block_of(func, header)?;

    let mut env = Env {
        vals: HashMap::new(),
        untyped: HashSet::new(),
        inputs: Vec::new(),
        opaque_counter: 0,
        identity_calls: identity_calls.clone(),
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
                        let join = model_in_loop_diamond(
                            &mut env,
                            func,
                            &loop_set,
                            header,
                            cur,
                            *cond,
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
                    (false, false) => {
                        return Err(format!(
                            "block {cur:?} has no in-loop successor toward the latch"
                        ));
                    }
                }
            }
            Inst::Switch {
                default,
                default_args,
                cases,
                ..
            } => {
                if cur == latch {
                    return Err("latch ends in a switch (out of model)".to_string());
                }
                // Collect every in-loop edge (target + args); they must all
                // agree on ONE target with identical args, else out of model.
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
                if candidates
                    .iter()
                    .any(|(t, a)| *t != first_t || *a != first_a)
                {
                    return Err(format!(
                        "block {cur:?} switch has multiple distinct in-loop successors"
                    ));
                }
                (first_t, first_a)
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

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{FuncId, FuncTyId, Function, InstrNode};

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
        match check_back_edge_threading(
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
            other => {
                // Certification-gap guard (crate::formal_gap), MEASURED
                // mechanism: the per-slot walk discharges the VALUE slot
                // first (`s+100 == extract(concat(ovf_flag(s,100), s+100))`
                // — captured live, CORRECTLY unsat), and while the
                // constellation cannot certify that intermediate proof the
                // walk fail-closes to Inconclusive BEFORE reaching the FLAG
                // slot whose stale threading would refute. The refutation
                // lane itself is pinned by the solver-less evaluation run of
                // this same test (it Refutes there). Skip ONLY on the exact
                // gap disclosure — a `Refined` here (a minted false
                // equivalence) still fails hard.
                if let Some(reason) = crate::formal_gap::refinement_gap_reason(&other) {
                    crate::formal_gap::print_gap_skip(
                        "ovf_tuple_end_to_end_refines_and_stale_flag_refutes (negative half; \
                         value-slot VC gap-blocked before the refuting flag slot)",
                        reason,
                    );
                    return;
                }
                panic!("stale-flag threading must be refuted, got {other:?}")
            }
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
        match check_back_edge_threading(
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
        let tail_outcome = check_back_edge_threading(
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
        let sl_outcome = check_back_edge_threading(
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
        match check_back_edge_threading(
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
    // END-TO-END: trust-ir symexec (implementation) vs MIR model (spec),
    // discharged through `mir_semantics::check_back_edge_threading` — the
    // exact composition the bridge gate wires up, at the REAL i32 width.
    // -----------------------------------------------------------------------

    use crate::ay_bridge::{self, AYConfig};
    use crate::mir_semantics::{
        BridgeEdgeArgs, EdgeKind, MirBinOp, MirBlock, MirOperand, MirRvalue, MirScalarTy, MirStmt,
        MirTerminator, RefinementOutcome, check_back_edge_threading,
    };
    use trust_cg_lower::types::Type;

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
        match check_back_edge_threading(
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

    /// A value flowing from an unmodeled instruction (a load) into the
    /// back-edge becomes an OPAQUE input — present in `extra_inputs`.
    #[test]
    fn unmodeled_inst_result_is_opaque() {
        let mut f = euclid_tir();
        {
            let bb2 = f.blocks.iter_mut().find(|blk| blk.id == b(2)).unwrap();
            bb2.body.clear();
            bb2.body.push(
                InstrNode::new(Inst::Load {
                    ty: Ty::I32,
                    ptr: v(10),
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
        .expect("opaque modeling must still succeed");
        assert!(
            model
                .extra_inputs
                .iter()
                .any(|(n, w)| n.starts_with("__tir_") && *w == 32),
            "the load result must be an opaque input: {:?}",
            model.extra_inputs
        );
    }
}
