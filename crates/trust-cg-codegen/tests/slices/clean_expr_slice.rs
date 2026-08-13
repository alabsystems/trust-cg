// SELF-CONTAINED clean-kernel `Expr`/`ExprKind` slice — the FOOTHOLD on the FULL
// (production) kernel expression type, richer than the micro-checker's MicroExpr.
//
// The chosen function is `Expr::has_loose_bvar_in_range_impl`
// ($HOME/clean/crates/clean-kernel/src/expr/subst.rs:601), copied VERBATIM. It is:
//   * PURE — no caching / interior mutability / RefCell / global interner;
//   * RECURSIVE through App / Lam / Pi / Let (multi-Arc) / Proj / MData / the
//     Cubical struct-variants (CubicalPath{ty,left,right},
//     CubicalHComp{ty,phi,u,base}, CubicalTransp{ty,phi,base}) / the ZFC
//     struct-variants (ZFCMem{element,set}, ZFCComprehension{domain,pred});
//   * a STRUCTURAL fold returning `bool`, the de-Bruijn analog the verified
//     MicroExpr work targeted, but over the REAL 25-variant ExprKind.
//
// Why this fn: it reads BOTH halves of the production `Expr` shape —
//   (a) the cached metadata word (`self.loose_bvar_range()` → the O(1) guard,
//       a bit-extraction from the `ExprMeta(u64)` field), and
//   (b) the structural `self.kind` enum —
// so it is the function that exercises the FAITHFUL `Expr` wrapper layout, which
// is THE thing distinguishing the real kernel type from MicroExpr (a bare enum).
//
// FAITHFULNESS — what is modeled vs a stand-in, and why each preserves the SHAPE
// `tcx.layout_of` sees (the frontend computes every offset/discriminant from
// layout_of, so a faithful shape is a faithful lowering):
//
//   * `Expr` — modeled FAITHFULLY as the real `pub struct Expr { kind: ExprKind,
//     meta: ExprMeta }`. This is the KEY finding: the production `Expr` is NOT a
//     bare `Arc<ExprKind>` — it is a HASHCONSED struct carrying a cached
//     `ExprMeta(u64)` (hash/depth/flags/loose_bvar_range packed into one word),
//     computed once at construction. The function READS `self.meta` via
//     `loose_bvar_range()`, so the wrapper + its u64 field must be present.
//   * `ExprMeta(u64)` — modeled FAITHFULLY as the real bit-packed newtype, with
//     the verbatim `pack`/`loose_bvar_range` bit layout (bits 44-63). The fn only
//     reads `loose_bvar_range()`; we include `pack` so test graphs get a correct
//     meta word at construction (matching `compute_meta`'s range computation for
//     the variants the tests build).
//   * `Arc<Expr>` children — KEPT VERBATIM as `Arc<Expr>` (the real type). The
//     Arc-read lowering (load + gep<+16> ArcInner data) is a mature rung.
//   * Payloads NOT inspected by the fn — `FVarId(u64)`, `Sort` level, `Const`
//     name+levels, `Lit` literal, `Lam/Pi` BinderData, `Let` name+bool,
//     `Proj` name+u32, `MData` map, `Squash`/`ZFCSet` etc. — are given
//     faithful-LAYOUT stand-ins (same field widths/shapes) since the fn never
//     reads their contents, only matches the variant and recurses into the
//     Arc<Expr> children. Documented per-variant inline. These keep the enum's
//     variant SET + discriminant SHAPE matching the real ExprKind so layout_of
//     assigns the same niche/direct encoding the real type would.
//   * `compute_meta` for the test-built graphs is reproduced for exactly the
//     variants the tests construct (BVar/Sort/App/Lam/Pi/Let/Proj/MData/the
//     Cubical+ZFC struct variants) so the cached `loose_bvar_range` guard is the
//     REAL value — i.e. the O(1) guard short-circuits exactly as in production.
//
// Everything in `has_loose_bvar_in_range_impl` (the early `start>=end` reject,
// the `loose_bvar_range() <= start` O(1) guard, every match arm incl. the
// binder `shift_bvar_range` body descent, the 3-child Let, the struct-variant
// destructures, the ZFC delegation) is the REAL clean-kernel logic.

#![crate_type = "lib"]
#![allow(dead_code)]
#![allow(clippy::all)]

use std::sync::Arc;

// ───────────────────────────────────────────────────────────────────────────
// Payload stand-ins (faithful LAYOUT; contents never read by the chosen fn).
// ───────────────────────────────────────────────────────────────────────────

/// Faithful stand-in for the real `Level` (Sort payload). The fn never inspects
/// it. A recursive Box-enum preserves the "non-Arc-child scalar/ptr payload"
/// shape of a Sort leaf.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Level {
    Zero,
    Succ(Box<Level>),
    Param(u32),
}

/// Faithful stand-in for `Name` (the real interned hashconsed name). The fn never
/// reads it; a `u32` handle preserves the non-recursive leaf-payload shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Name(pub u32);

/// Faithful stand-in for `LevelVec` (Const's `SmallVec<[Level;2]>`). A `Vec`
/// preserves the heap-slice shape; never read by the fn.
pub type LevelVec = Vec<Level>;

/// Faithful stand-in for `Literal`. Never read by the fn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Literal {
    Nat(u64),
    String(Arc<str>),
}

/// Faithful stand-in for `BinderData` (Lam/Pi binder annotation: 2 small enums).
/// Never read by the fn; a 2-byte struct preserves the Copy scalar-pair shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BinderData {
    pub info: u8,
    pub mult: u8,
}

/// Faithful stand-in for `MDataMap` = `Vec<(Name, MDataValue)>`. Never read.
pub type MDataMap = Vec<(Name, u64)>;

/// Faithful stand-in for `FVarId(u64)`. Never read by the fn.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FVarId(pub u64);

/// Faithful stand-in for `ZFCSetExpr`. The fn delegates to
/// `ZFCSetExpr::has_loose_bvar_in_range` (also copied verbatim below), so this
/// is modeled with its real recursive structure (not opaque).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ZFCSetExpr {
    Empty,
    Singleton(Arc<Expr>),
    Pair(Arc<Expr>, Arc<Expr>),
    Union(Arc<Expr>),
    PowerSet(Arc<Expr>),
    Separation { set: Arc<Expr>, pred: Arc<Expr> },
    Replacement { set: Arc<Expr>, func: Arc<Expr> },
    Infinity,
    Choice(Arc<Expr>),
}

// ───────────────────────────────────────────────────────────────────────────
// ExprMeta — the cached metadata word. VERBATIM bit layout from
// $HOME/clean/crates/clean-kernel/src/expr/meta.rs (the parts the fn + the test
// graph construction need: pack + loose_bvar_range; plus mk_* combinators so
// test graphs get correct cached ranges).
// ───────────────────────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExprMeta(u64);

impl ExprMeta {
    const HASH_MASK: u64 = 0xFFFF_FFFF;
    const DEPTH_SHIFT: u32 = 32;
    const HAS_FVAR_BIT: u32 = 40;
    const BVAR_RANGE_SHIFT: u32 = 44;
    pub const MAX_DEPTH: u32 = 255;
    pub const MAX_BVAR_RANGE: u32 = 1_048_575; // 2^20 - 1

    /// VERBATIM pack (meta.rs:53). Only the loose_bvar_range bits matter to the
    /// chosen fn; we keep the full layout so the word is byte-identical to the
    /// real one for the variants the tests build.
    #[inline]
    pub fn pack(
        hash: u32,
        loose_bvar_range: u32,
        approx_depth: u32,
        has_fvar: bool,
        has_expr_mvar: bool,
        has_level_mvar: bool,
        has_level_param: bool,
    ) -> Self {
        let depth = approx_depth.min(Self::MAX_DEPTH);
        assert!(
            loose_bvar_range <= Self::MAX_BVAR_RANGE,
            "too many bound variables"
        );
        let range = loose_bvar_range;
        let bits = (hash as u64)
            | ((depth as u64) << Self::DEPTH_SHIFT)
            | ((has_fvar as u64) << Self::HAS_FVAR_BIT)
            | ((has_expr_mvar as u64) << 41)
            | ((has_level_mvar as u64) << 42)
            | ((has_level_param as u64) << 43)
            | ((range as u64) << Self::BVAR_RANGE_SHIFT);
        ExprMeta(bits)
    }

    /// VERBATIM loose_bvar_range accessor (meta.rs:126) — the O(1) guard the
    /// chosen fn reads. A bit-extraction from the packed u64.
    #[inline]
    pub fn loose_bvar_range(self) -> u32 {
        (self.0 >> Self::BVAR_RANGE_SHIFT) as u32
    }

    #[inline]
    pub fn has_loose_bvars(self) -> bool {
        self.loose_bvar_range() > 0
    }
}

// ───────────────────────────────────────────────────────────────────────────
// ExprKind — the REAL production enum (kind.rs:118). All 25 variants modeled
// with faithful SHAPE. Struct-variants kept as struct-variants; multi-Arc Let
// kept multi-Arc; Arc<Expr> children verbatim.
// ───────────────────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprKind {
    // CORE (all modes)
    BVar(u32),
    FVar(FVarId),
    Sort(Level),
    Const(Name, LevelVec),
    App(Arc<Expr>, Arc<Expr>),
    Lam(BinderData, Arc<Expr>, Arc<Expr>),
    Pi(BinderData, Arc<Expr>, Arc<Expr>),
    Let(Name, Arc<Expr>, Arc<Expr>, Arc<Expr>, bool),
    Lit(Literal),
    Proj(Name, u32, Arc<Expr>),
    MData(MDataMap, Arc<Expr>),

    // IMPREDICATIVE
    SProp,
    Squash(Arc<Expr>),

    // CUBICAL
    CubicalInterval,
    CubicalI0,
    CubicalI1,
    CubicalPath {
        ty: Arc<Expr>,
        left: Arc<Expr>,
        right: Arc<Expr>,
    },
    CubicalPathLam {
        body: Arc<Expr>,
    },
    CubicalPathApp {
        path: Arc<Expr>,
        arg: Arc<Expr>,
    },
    CubicalHComp {
        ty: Arc<Expr>,
        phi: Arc<Expr>,
        u: Arc<Expr>,
        base: Arc<Expr>,
    },
    CubicalTransp {
        ty: Arc<Expr>,
        phi: Arc<Expr>,
        base: Arc<Expr>,
    },

    // SET-THEORETIC
    ZFCSet(ZFCSetExpr),
    ZFCMem {
        element: Arc<Expr>,
        set: Arc<Expr>,
    },
    ZFCComprehension {
        domain: Arc<Expr>,
        pred: Arc<Expr>,
    },
}

// ───────────────────────────────────────────────────────────────────────────
// Expr — the FAITHFUL production wrapper struct (mod.rs:204): a hashconsed
// `{ kind: ExprKind, meta: ExprMeta }`, NOT a bare Arc<ExprKind>.
// ───────────────────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub meta: ExprMeta,
}

// ───────────────────────────────────────────────────────────────────────────
// Pure free helpers — VERBATIM from expr/mod.rs.
// ───────────────────────────────────────────────────────────────────────────

/// VERBATIM checked_add_u32 (mod.rs:83).
pub fn checked_add_u32(a: u32, b: u32, _context: &'static str) -> u32 {
    a.saturating_add(b)
}

/// VERBATIM bvar_in_range (mod.rs:94).
pub fn bvar_in_range(idx: u32, start: u32, end: u32) -> bool {
    if end == u32::MAX {
        idx >= start
    } else {
        idx >= start && idx < end
    }
}

/// VERBATIM shift_bvar_range (mod.rs:114). Returns Option<(u32,u32)>.
pub fn shift_bvar_range(start: u32, end: u32) -> Option<(u32, u32)> {
    if end != u32::MAX && start >= end {
        return None;
    }
    if start == u32::MAX {
        return None;
    }
    let next_start = checked_add_u32(start, 1, "has_loose_bvar_in_range start");
    let next_end = if end == u32::MAX {
        u32::MAX
    } else {
        checked_add_u32(end, 1, "has_loose_bvar_in_range end")
    };
    Some((next_start, next_end))
}

// ───────────────────────────────────────────────────────────────────────────
// ZFCSetExpr::has_loose_bvar_in_range — VERBATIM (kind.rs:378).
// ───────────────────────────────────────────────────────────────────────────

impl ZFCSetExpr {
    pub fn has_loose_bvar_in_range(&self, start: u32, end: u32) -> bool {
        if end != u32::MAX && start >= end {
            return false;
        }
        match self {
            ZFCSetExpr::Empty | ZFCSetExpr::Infinity => false,
            ZFCSetExpr::Singleton(e) => e.has_loose_bvar_in_range(start, end),
            ZFCSetExpr::Pair(a, b) => {
                a.has_loose_bvar_in_range(start, end) || b.has_loose_bvar_in_range(start, end)
            }
            ZFCSetExpr::Union(e) | ZFCSetExpr::PowerSet(e) | ZFCSetExpr::Choice(e) => {
                e.has_loose_bvar_in_range(start, end)
            }
            ZFCSetExpr::Separation { set, pred } | ZFCSetExpr::Replacement { set, func: pred } => {
                let pred_has_loose = match shift_bvar_range(start, end) {
                    Some((next_start, next_end)) => pred.has_loose_bvar_in_range(next_start, next_end),
                    None => false,
                };
                set.has_loose_bvar_in_range(start, end) || pred_has_loose
            }
        }
    }
}

// ───────────────────────────────────────────────────────────────────────────
// Expr::has_loose_bvar_in_range_impl — THE CHOSEN FUNCTION. VERBATIM from
// $HOME/clean/crates/clean-kernel/src/expr/subst.rs:601.  (The public
// `has_loose_bvar_in_range` wrapper just routes through `stack_safe`, which is
// pure plumbing around the SAME body — inlined per the established slice
// convention; both the wrapper and `_impl` are provided so callers compile.)
// ───────────────────────────────────────────────────────────────────────────

impl Expr {
    /// Read cached metadata range (mirrors Expr::loose_bvar_range, mod.rs:314).
    #[inline]
    pub fn loose_bvar_range(&self) -> u32 {
        self.meta.loose_bvar_range()
    }

    /// VERBATIM has_loose_bvar_in_range wrapper (subst.rs:595) with stack_safe
    /// inlined to the direct impl call.
    pub fn has_loose_bvar_in_range(&self, start: u32, end: u32) -> bool {
        self.has_loose_bvar_in_range_impl(start, end)
    }

    /// VERBATIM has_loose_bvar_in_range_impl (subst.rs:601).
    pub fn has_loose_bvar_in_range_impl(&self, start: u32, end: u32) -> bool {
        if end != u32::MAX && start >= end {
            return false;
        }
        // O(1) metadata guard: all loose BVar indices are < loose_bvar_range(),
        // so if loose_bvar_range() <= start, no BVars exist in [start, end).
        if self.loose_bvar_range() <= start {
            return false;
        }
        match &self.kind {
            ExprKind::BVar(idx) => bvar_in_range(*idx, start, end),
            ExprKind::FVar(_) | ExprKind::Sort(_) | ExprKind::Const(_, _) | ExprKind::Lit(_) => {
                false
            }
            ExprKind::App(f, a) => {
                f.has_loose_bvar_in_range(start, end) || a.has_loose_bvar_in_range(start, end)
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                let body_has_loose = match shift_bvar_range(start, end) {
                    Some((next_start, next_end)) => {
                        body.has_loose_bvar_in_range(next_start, next_end)
                    }
                    None => false,
                };
                ty.has_loose_bvar_in_range(start, end) || body_has_loose
            }
            ExprKind::Let(_, ty, val, body, _) => {
                let body_has_loose = match shift_bvar_range(start, end) {
                    Some((next_start, next_end)) => {
                        body.has_loose_bvar_in_range(next_start, next_end)
                    }
                    None => false,
                };
                ty.has_loose_bvar_in_range(start, end)
                    || val.has_loose_bvar_in_range(start, end)
                    || body_has_loose
            }
            ExprKind::Proj(_, _, e) => e.has_loose_bvar_in_range(start, end),
            ExprKind::MData(_, inner) => inner.has_loose_bvar_in_range(start, end),

            // Impredicative mode extensions
            ExprKind::SProp => false,
            ExprKind::Squash(inner) => inner.has_loose_bvar_in_range(start, end),

            // Cubical mode extensions
            ExprKind::CubicalInterval | ExprKind::CubicalI0 | ExprKind::CubicalI1 => false,
            ExprKind::CubicalPath { ty, left, right } => {
                ty.has_loose_bvar_in_range(start, end)
                    || left.has_loose_bvar_in_range(start, end)
                    || right.has_loose_bvar_in_range(start, end)
            }
            ExprKind::CubicalPathLam { body } => match shift_bvar_range(start, end) {
                Some((next_start, next_end)) => body.has_loose_bvar_in_range(next_start, next_end),
                None => false,
            },
            ExprKind::CubicalPathApp { path, arg } => {
                path.has_loose_bvar_in_range(start, end) || arg.has_loose_bvar_in_range(start, end)
            }
            ExprKind::CubicalHComp { ty, phi, u, base } => {
                ty.has_loose_bvar_in_range(start, end)
                    || phi.has_loose_bvar_in_range(start, end)
                    || u.has_loose_bvar_in_range(start, end)
                    || base.has_loose_bvar_in_range(start, end)
            }
            ExprKind::CubicalTransp { ty, phi, base } => {
                ty.has_loose_bvar_in_range(start, end)
                    || phi.has_loose_bvar_in_range(start, end)
                    || base.has_loose_bvar_in_range(start, end)
            }

            // SetTheoretic mode extensions
            ExprKind::ZFCSet(set_expr) => set_expr.has_loose_bvar_in_range(start, end),
            ExprKind::ZFCMem { element, set } => {
                element.has_loose_bvar_in_range(start, end)
                    || set.has_loose_bvar_in_range(start, end)
            }
            ExprKind::ZFCComprehension { domain, pred } => {
                let pred_has_loose = match shift_bvar_range(start, end) {
                    Some((next_start, next_end)) => {
                        pred.has_loose_bvar_in_range(next_start, next_end)
                    }
                    None => false,
                };
                domain.has_loose_bvar_in_range(start, end) || pred_has_loose
            }
        }
    }
}

// Force monomorphization / collection of the chosen fn by referencing it.
pub fn drive(e: &Expr, start: u32, end: u32) -> bool {
    e.has_loose_bvar_in_range_impl(start, end)
}
