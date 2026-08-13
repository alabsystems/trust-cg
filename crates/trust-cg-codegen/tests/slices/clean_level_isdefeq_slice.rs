// Real-kernel UNIVERSE-UNIFICATION slice — the production `Level::is_def_eq`
// (clean-kernel/src/level/mod.rs:1026) and its `Level::normalize` (mod.rs:433)
// lowered over the REAL `Level` enum {Zero, Succ, Max, IMax, Param}.
//
// `is_def_eq(l1,l2) = l1==l2 || l1.normalize()==l2.normalize()`.
//
// This CLOSES the universe-logic deferral shared by the verified def_eq (whose
// Sort/Const arms call `level_eq = Level::is_def_eq`) and infer_type (imax). The
// prior def_eq / whnf slices MODELED `Level::is_def_eq` as the structural
// {Zero,Succ,Param} congruence (`l1 == l2`); this slice makes the FULL universe
// arithmetic (Max flatten/sort/dedup/subsume, IMax fold, Succ-offset
// distribution, is_geq subsumption) REAL and JIT-verified.
//
// TRANSCRIPTION NOTE — clean has cfg(kani) and cfg(not(kani)) bodies for several
// of these fns; the kani bodies are the recursion-free / hashbrown-free / env-free
// equivalents that clean's own soundness_harness machine-checks against the
// production bodies. This slice transcribes those cfg(kani) bodies VERBATIM
// (same precedent as the construction/whnf rungs, which transcribed clean's
// cfg(kani) KaniHasher / compute_meta):
//   * PartialEq for Level  -> the kani iterative explicit-stack eq (mod.rs:142).
//   * is_geq_core          -> is_geq_core_iter (kani, Vec worklist, NO hashbrown).
//   * Level::max           -> the kani path (skips the is_geq subsumption that
//                             would re-enter normalize; mod.rs:295-308).
//   * normalize_impl Zero/Param arm -> the kani iterative re-wrap (mod.rs:601).
// All other bodies (normalize_impl IMax/Max arms, normalize_max, push_max_args,
// mk_max_from_args, dedup_max_args, subsume_max_args, is_norm_lt, kind_ord,
// is_explicit, get_offset, add_offset, is_geq, is_geq_leaf, is_zero, is_nonzero,
// imax, succ, zero, is_def_eq, normalize) are IDENTICAL in both cfgs and are
// transcribed VERBATIM.
//
// THE ONE REWRITE (reported): `normalize_max` sorts its flattened Max args with
//   args.sort_by(|a,b| { if is_norm_lt(a,b) {Less} else if is_norm_lt(b,a) {Greater} else {Equal} });
// `sort_by` is generic `core::slice::sort` (driftsort) — its monomorphized body
// is NOT in the user crate, so the MIR collector cannot lower it (confirmed:
// emitting a fn that calls `sort_by` lowers only the comparator closure, not the
// sort). It is rewritten here as an in-module STABLE INSERTION SORT using the
// IDENTICAL `is_norm_lt` total order. `sort_by` is documented stable; insertion
// sort is stable; `is_norm_lt` is a strict weak order, so the resulting canonical
// arg ordering is byte-identical to `sort_by`'s. This is the same class of rewrite
// the prior rungs used for `.iter().zip().all` / index-loop conversions.
//
// MODELED LEAVES (reported honestly):
//   * Name: the real `Name` (name.rs:235) is an interned linked-list of
//     components with a cached_hash and a component-wise `Ord`. Here it is the
//     `Name(u32)` newtype the prior rungs used: PartialEq on the u32 id (faithful
//     for the Param/Param equality in `==`) and Ord on the u32 id (faithful for
//     the `n1 < n2` total order in `is_norm_lt` — distinct params get a
//     deterministic total order; structurally-equal params compare equal, which
//     is all the canonical form depends on).
//   * MVar: the real `Level` enum has NO MVar variant (mod.rs:81-92; the kernel
//     comment at :439 confirms "clean has no MVar"). Nothing to model or defer.
//   * Arc<Level>: LevelArc = Arc<Level> (mod.rs:32, the cfg(not(kani)) form, which
//     the task directs lowering). Arc::new construction + Arc deref are the
//     verified machinery from the Expr rungs. Arc leaks (accepted, same as prior).
//   * stack_safe: production wraps recursive calls in stack_safe(||..) (a
//     recursion-depth trampoline, semantically a pass-through). Here the recursive
//     calls are direct (same as the whnf rung). REPORTED.

#![allow(dead_code)]

use std::sync::Arc;

// ── Name leaf model (the prior rungs' Name(u32); PartialEq + Ord on the id). ──
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(pub u32);

pub type LevelArc = Arc<Level>;

#[inline(always)]
fn level_arc(l: Level) -> LevelArc {
    Arc::new(l)
}

// The real Level enum (mod.rs:81). Variant ORDER is VERBATIM so discriminants
// match the JIT (Zero=0, Succ=1, Max=2, IMax=3, Param=4).
#[derive(Clone, Debug)]
pub enum Level {
    Zero,
    Succ(LevelArc),
    Max(LevelArc, LevelArc),
    IMax(LevelArc, LevelArc),
    Param(Name),
}

// VERBATIM the cfg(kani) iterative explicit-stack PartialEq (mod.rs:142-168).
// Avoids recursive Arc<Level>::eq; iterates a (&Level,&Level) worklist.
impl PartialEq for Level {
    fn eq(&self, other: &Self) -> bool {
        let mut stack: Vec<(&Level, &Level)> = vec![(self, other)];
        while let Some((a, b)) = stack.pop() {
            match (a, b) {
                (Level::Zero, Level::Zero) => {}
                (Level::Succ(la), Level::Succ(lb)) => {
                    stack.push((la, lb));
                }
                (Level::Max(la1, la2), Level::Max(lb1, lb2))
                | (Level::IMax(la1, la2), Level::IMax(lb1, lb2)) => {
                    stack.push((la1, lb1));
                    stack.push((la2, lb2));
                }
                (Level::Param(na), Level::Param(nb)) => {
                    if na != nb {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }
}

impl Eq for Level {}

impl Level {
    // ── smart constructors (mod.rs:259-359) ──

    pub fn zero() -> Self {
        Level::Zero
    }

    pub fn succ(l: Level) -> Self {
        Level::Succ(level_arc(l))
    }

    // VERBATIM the cfg(kani) `max` path: the is_geq subsumption is gated out under
    // kani (mod.rs:295-308) to break the max->is_geq->normalize->imax->max cycle;
    // normalize handles subsumption during canonicalization, so this only yields
    // less-simplified intermediate Max nodes — correctness preserved.
    pub fn max(l1: Level, l2: Level) -> Self {
        if l1 == l2 {
            return l1;
        }
        if l1.is_zero() {
            return l2;
        }
        if l2.is_zero() {
            return l1;
        }
        Level::Max(level_arc(l1), level_arc(l2))
    }

    // VERBATIM `imax` (mod.rs:324-349). Smart constructor: imax(l,0)=0;
    // imax(l,l') = max(l,l') when l' definitely nonzero; imax(0,l)=l; imax(1,l)=l;
    // imax(l,l)=l; else IMax(l1,l2).
    pub fn imax(l1: Level, l2: Level) -> Self {
        if l2.is_zero() {
            return Level::Zero;
        }
        if l2.is_nonzero() {
            return Level::max(l1, l2);
        }
        if l1.is_zero() {
            return l2;
        }
        if l1 == Level::succ(Level::zero()) {
            return l2;
        }
        if l1 == l2 {
            return l1;
        }
        Level::IMax(level_arc(l1), level_arc(l2))
    }

    pub fn param(name: Name) -> Self {
        Level::Param(name)
    }

    // VERBATIM `is_zero` (mod.rs:367-374).
    pub fn is_zero(&self) -> bool {
        match self {
            Level::Zero => true,
            Level::Succ(_) | Level::Param(_) => false,
            Level::Max(l1, l2) => l1.is_zero() && l2.is_zero(),
            Level::IMax(_, l2) => l2.is_zero(),
        }
    }

    // VERBATIM `is_nonzero` (mod.rs:382-389).
    fn is_nonzero(&self) -> bool {
        match self {
            Level::Zero | Level::Param(_) => false,
            Level::Succ(_) => true,
            Level::Max(l1, l2) => l1.is_nonzero() || l2.is_nonzero(),
            Level::IMax(_, l2) => l2.is_nonzero(),
        }
    }

    // VERBATIM `get_offset` (mod.rs:399-408). Iterative Succ-strip.
    fn get_offset(&self) -> (&Level, u32) {
        let mut current = self;
        let mut offset = 0u32;
        while let Level::Succ(inner) = current {
            offset = offset.saturating_add(1);
            current = inner;
        }
        (current, offset)
    }

    // VERBATIM `add_offset` (mod.rs:416-423). The `for _ in 0..n` is written as a
    // counter `while` (same semantics, no Range-iterator into_iter/next externs —
    // the established pattern the whnf rung used to keep the lowering closed).
    fn add_offset(&self, n: u32) -> Level {
        let mut result = self.clone();
        let mut c = 0u32;
        while c < n {
            result = Level::succ(result);
            c += 1;
        }
        result
    }

    // `normalize` (mod.rs:433-435). The production wraps normalize_impl in
    // stack_safe(||..); here the call is direct (trampoline is a depth concern).
    pub fn normalize(&self) -> Level {
        self.normalize_impl()
    }

    // VERBATIM `kind_ord` (mod.rs:441-449). Lean 4 level_kind order.
    fn kind_ord(&self) -> u8 {
        match self {
            Level::Zero => 0,
            Level::Succ(_) => 1,
            Level::Max(_, _) => 2,
            Level::IMax(_, _) => 3,
            Level::Param(_) => 4,
        }
    }

    // VERBATIM the cfg(kani) iterative `is_norm_lt` (mod.rs:459-493). Total order
    // on normalized level exprs (Lean 4 is_norm_lt), iterative tail-call form.
    fn is_norm_lt(a: &Level, b: &Level) -> bool {
        let mut a = a;
        let mut b = b;
        loop {
            if a == b {
                return false;
            }
            let (base1, off1) = a.get_offset();
            let (base2, off2) = b.get_offset();
            if base1 != base2 {
                if base1.kind_ord() != base2.kind_ord() {
                    return base1.kind_ord() < base2.kind_ord();
                }
                match (base1, base2) {
                    (Level::Param(n1), Level::Param(n2)) => return n1 < n2,
                    (Level::Max(a1, b1), Level::Max(a2, b2))
                    | (Level::IMax(a1, b1), Level::IMax(a2, b2)) => {
                        if a1 != a2 {
                            a = a1;
                            b = a2;
                            continue;
                        } else {
                            a = b1;
                            b = b2;
                            continue;
                        }
                    }
                    _ => return false,
                }
            } else {
                return off1 < off2;
            }
        }
    }

    // VERBATIM the cfg(kani) iterative `push_max_args` (mod.rs:530-542). Flatten a
    // Max tree into a buffer of non-Max args via an explicit stack.
    fn push_max_args(l: &Level, buf: &mut Vec<Level>) {
        let mut stack: Vec<&Level> = vec![l];
        while let Some(current) = stack.pop() {
            match current {
                Level::Max(a, b) => {
                    stack.push(b);
                    stack.push(a);
                }
                _ => buf.push(current.clone()),
            }
        }
    }

    // VERBATIM `mk_max_from_args` (mod.rs:558-571). Right-associated Max rebuild.
    fn mk_max_from_args(args: &[Level]) -> Level {
        if args.len() == 1 {
            return args[0].clone();
        }
        let mut r = Level::Max(
            level_arc(args[args.len() - 2].clone()),
            level_arc(args[args.len() - 1].clone()),
        );
        let mut i = args.len() - 2;
        while i > 0 {
            i -= 1;
            r = Level::Max(level_arc(args[i].clone()), level_arc(r));
        }
        r
    }

    // VERBATIM `is_explicit` (mod.rs:577-579).
    fn is_explicit(&self) -> bool {
        matches!(self.get_offset().0, Level::Zero)
    }

    // `normalize_impl` (mod.rs:593-639). VERBATIM control flow; the Zero/Param arm
    // uses the cfg(kani) iterative re-wrap (mod.rs:601-612).
    fn normalize_impl(&self) -> Level {
        let (base, outer_offset) = self.get_offset();

        match base {
            Level::Zero | Level::Param(_) => {
                // The inner `_` arm is DEAD: the outer match guarantees `base` is
                // Zero or Param here. clean's cfg(kani) body writes `unreachable!()`;
                // a panic expands to a `core::panicking` call passing a `&str`/Arguments
                // constant (non-scalar ref) the frontend cannot lower. Replaced with
                // a benign in-domain `Level::Zero` — identical on the reachable domain
                // (same precedent as the construction rung's dead assert! branch).
                let mut result = match base {
                    Level::Zero => Level::Zero,
                    Level::Param(n) => Level::Param(*n),
                    _ => Level::Zero,
                };
                // `for _ in 0..outer_offset` -> counter while (no Range externs).
                let mut c = 0u32;
                while c < outer_offset {
                    result = Level::succ(result);
                    c += 1;
                }
                result
            }
            // DEAD: `get_offset` strips every Succ layer, so `base` is never Succ.
            // clean writes `unreachable!("...")` (non-lowerable &str panic); replaced
            // with a benign self-clone — identical on the reachable domain.
            Level::Succ(_) => base.clone(),

            Level::IMax(l1, l2) => {
                let l1_norm = l1.normalize_impl();
                let l2_norm = l2.normalize_impl();
                let result = Level::imax(l1_norm, l2_norm);
                if matches!(result, Level::Max(_, _)) {
                    result.add_offset(outer_offset).normalize_impl()
                } else {
                    result.add_offset(outer_offset)
                }
            }

            Level::Max(_, _) => Self::normalize_max(base, outer_offset),
        }
    }

    // `normalize_max` (mod.rs:644-690). VERBATIM EXCEPT Step 3 sort: the
    // `args.sort_by(|a,b| ..)` closure-comparator (generic core::slice::sort, not
    // lowerable) is rewritten as a STABLE INSERTION SORT with the IDENTICAL
    // `is_norm_lt` order (see file header).
    fn normalize_max(base: &Level, outer_offset: u32) -> Level {
        // Step 1: flatten.
        let mut todo = Vec::new();
        Self::push_max_args(base, &mut todo);

        // Step 2: normalize each arg, re-flatten.
        let mut args = Vec::new();
        let mut ti = 0;
        while ti < todo.len() {
            let normed = todo[ti].normalize_impl();
            Self::push_max_args(&normed, &mut args);
            ti += 1;
        }

        // Step 3: sort with is_norm_lt — STABLE INSERTION SORT (rewrite of
        // sort_by; identical order). For each i, shift args[i] left past every
        // predecessor that is is_norm_lt-GREATER than it (strictly), preserving
        // the relative order of is_norm_lt-equal elements (stable).
        let mut i = 1;
        while i < args.len() {
            let mut j = i;
            while j > 0 && Self::is_norm_lt(&args[j], &args[j - 1]) {
                args.swap(j, j - 1);
                j -= 1;
            }
            i += 1;
        }

        // Step 4: dedup same-base (keep largest offset) + explicit subsumption.
        let deduped = Self::dedup_max_args(&args);

        // Step 5: semantic subsumption.
        let mut rargs = Self::subsume_max_args(&deduped);

        // Step 6: reapply outer offset.
        if outer_offset > 0 {
            let mut k = 0;
            while k < rargs.len() {
                rargs[k] = rargs[k].add_offset(outer_offset);
                k += 1;
            }
        }

        if rargs.is_empty() {
            Level::Zero
        } else {
            Self::mk_max_from_args(&rargs)
        }
    }

    // `subsume_max_args` (mod.rs:727-770). VERBATIM; the `.iter().filter()` /
    // `.iter().any()` closures are rewritten as explicit index loops with the
    // IDENTICAL predicate (same class as prior rungs' iter->index rewrites).
    fn subsume_max_args(args: &[Level]) -> Vec<Level> {
        if args.len() <= 1 {
            return args.to_vec();
        }
        // is_composite(l) = get_offset base is Max/IMax.
        // composites non-empty?  (fast path: nothing new beyond dedup.)
        let mut any_composite = false;
        {
            let mut c = 0;
            while c < args.len() {
                if matches!(args[c].get_offset().0, Level::Max(_, _) | Level::IMax(_, _)) {
                    any_composite = true;
                    break;
                }
                c += 1;
            }
        }
        if !any_composite {
            return args.to_vec();
        }

        let mut kept: Vec<Level> = Vec::new();
        let mut i = 0;
        while i < args.len() {
            let x = &args[i];
            let x_composite =
                matches!(x.get_offset().0, Level::Max(_, _) | Level::IMax(_, _));

            // dominated by an already-kept (strictly-earlier) arg?
            let mut dominated_by_kept = false;
            {
                let mut ky = 0;
                while ky < kept.len() {
                    let y = &kept[ky];
                    let y_composite =
                        matches!(y.get_offset().0, Level::Max(_, _) | Level::IMax(_, _));
                    if (x_composite || y_composite) && Self::is_geq_core(y, x) {
                        dominated_by_kept = true;
                        break;
                    }
                    ky += 1;
                }
            }
            if dominated_by_kept {
                i += 1;
                continue;
            }

            // dominated by a STRICTLY-later arg (y>=x but not x>=y)?
            let mut dominated_by_later_strict = false;
            {
                let mut ly = i + 1;
                while ly < args.len() {
                    let y = &args[ly];
                    let y_composite =
                        matches!(y.get_offset().0, Level::Max(_, _) | Level::IMax(_, _));
                    if (x_composite || y_composite)
                        && Self::is_geq_core(y, x)
                        && !Self::is_geq_core(x, y)
                    {
                        dominated_by_later_strict = true;
                        break;
                    }
                    ly += 1;
                }
            }
            if dominated_by_later_strict {
                i += 1;
                continue;
            }

            kept.push(x.clone());
            i += 1;
        }
        kept
    }

    // VERBATIM `dedup_max_args` (mod.rs:775-824). Index-loop already (no closures).
    fn dedup_max_args(args: &[Level]) -> Vec<Level> {
        let mut rargs: Vec<Level> = Vec::new();
        let mut i = 0;

        if args[i].is_explicit() {
            while i + 1 < args.len() && args[i + 1].is_explicit() {
                i += 1;
            }
            let k = args[i].get_offset().1;
            let mut j = i + 1;
            while j < args.len() {
                if args[j].get_offset().1 >= k {
                    break;
                }
                j += 1;
            }
            if j < args.len() {
                i += 1;
            }
        }

        if i < args.len() {
            rargs.push(args[i].clone());
            let mut prev_offset = args[i].get_offset();
            i += 1;
            while i < args.len() {
                let curr_offset = args[i].get_offset();
                if prev_offset.0 == curr_offset.0 {
                    if prev_offset.1 < curr_offset.1 {
                        prev_offset = curr_offset;
                        rargs.pop();
                        rargs.push(args[i].clone());
                    }
                } else {
                    prev_offset = curr_offset;
                    rargs.push(args[i].clone());
                }
                i += 1;
            }
        }

        rargs
    }

    // `is_geq` (mod.rs:840-844). Normalizes both sides then is_geq_core.
    fn is_geq(l1: &Level, l2: &Level) -> bool {
        let n1 = l1.normalize();
        let n2 = l2.normalize();
        Self::is_geq_core(&n1, &n2)
    }

    // VERBATIM the cfg(kani) `is_geq_core` = is_geq_core_iter (mod.rs:871-915).
    // Conjunction worklist; NO hashbrown / NO memoization. This is the
    // hashbrown-free equivalent clean's soundness_harness checks against the
    // production cached recursion.
    fn is_geq_core(l1: &Level, l2: &Level) -> bool {
        let mut worklist: Vec<(&Level, &Level)> = vec![(l1, l2)];
        while let Some((l1, l2)) = worklist.pop() {
            if l1 == l2 || l2.is_zero() {
                continue;
            }
            let (base1, offset1) = l1.get_offset();
            if offset1 > 0 && *base1 == *l2 {
                continue;
            }
            if let Level::Max(a, b) = l2 {
                worklist.push((l1, a));
                worklist.push((l1, b));
                continue;
            }
            if let Level::Max(a, b) = l1 {
                if Self::is_geq_leaf(a, l2) || Self::is_geq_leaf(b, l2) {
                    continue;
                }
                return false;
            }
            if let Level::IMax(a, b) = l2 {
                worklist.push((l1, a));
                worklist.push((l1, b));
                continue;
            }
            if let Level::IMax(_, b) = l1 {
                worklist.push((b, l2));
                continue;
            }
            let (base2, offset2) = l2.get_offset();
            if base1 == base2 || base2.is_zero() {
                if offset1 >= offset2 {
                    continue;
                }
                return false;
            }
            if offset1 == offset2 && offset1 > 0 {
                worklist.push((base1, base2));
                continue;
            }
            return false;
        }
        true
    }

    // VERBATIM the cfg(kani) `is_geq_leaf` (mod.rs:920-930).
    fn is_geq_leaf(l1: &Level, l2: &Level) -> bool {
        if l1 == l2 || l2.is_zero() {
            return true;
        }
        let (base1, offset1) = l1.get_offset();
        if offset1 > 0 && *base1 == *l2 {
            return true;
        }
        let (base2, offset2) = l2.get_offset();
        (base1 == base2 || base2.is_zero()) && offset1 >= offset2
    }

    // ── THE TARGET: `is_def_eq` (mod.rs:1026-1033) — VERBATIM. ──
    pub fn is_def_eq(l1: &Level, l2: &Level) -> bool {
        if l1 == l2 {
            return true;
        }
        l1.normalize() == l2.normalize()
    }
}

// Closure entry the driver lowers (`--mir-emit-closure is_def_eq`). Takes two
// thin `&Level` pointers and returns the bool.
pub fn is_def_eq(l1: &Level, l2: &Level) -> bool {
    Level::is_def_eq(l1, l2)
}
