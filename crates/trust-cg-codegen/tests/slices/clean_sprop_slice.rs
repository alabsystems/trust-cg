// R15 — THE B5 SProp ARM: strict (definitional) proof irrelevance, LIVE.
//
// Verbatim transcription of clean-kernel's SProp proof-irrelevance disjunct
// (tc/def_eq/proof_irrel.rs:84-87, the `matches!(ty_of_ty_whnf.kind(),
// ExprKind::SProp)` arm at :86 — the arm the R9 slice recorded as
// "structurally absent (B5)") together with the whole proof-irrelevance
// family it composes with, wired into a focused def_eq engine at the
// production hook position (def_eq/mod.rs:358-367), verified native == JIT
// (Clean's CIC kernel through Trust: Rust -> MIR -> trust-ir -> trust-cg ->
// machine code).
//
// THE SOUNDNESS-CRITICAL SEMANTICS (the point of the round):
//   SProp is clean's universe of STRICT propositions with DEFINITIONAL proof
//   irrelevance: any two terms whose TYPE lives in SProp are def-eq
//   unconditionally. In clean, SProp is a DISTINGUISHED ExprKind variant
//   (`ExprKind::SProp`) — NOT a Sort level — and a term is treated as
//   proof-irrelevant iff the type-of-its-type whnf-reduces to `Sort 0` (Prop,
//   proof_irrel.rs:85) OR to `ExprKind::SProp` (proof_irrel.rs:86). The two
//   arms are structurally distinct code paths producing the same verdict.
//
//   A wrong SProp check that treats a NON-SProp type as SProp would conflate
//   distinct values (two distinct elements of a `Type`, two distinct Nats) and
//   make the logic INCONSISTENT (prove `2 = 3` -> False). So the universe
//   check must be sound in BOTH directions: ACCEPT distinct proofs of an
//   SProp; REJECT distinct values of a non-SProp.
//
// PRODUCTION POSITIONS transcribed verbatim (source of truth, read in full):
//   $HOME/clean/crates/clean-kernel/src/tc/def_eq/proof_irrel.rs
//       is_def_eq_proof_irrel (:16-53)            — the Cubical/Directed early
//                                                    out, quick-not-in-Prop
//                                                    pre-filter, the
//                                                    proof-irrelevance verdict.
//       infer_type_quick_or_full (:65-73)         — quick, else infer-only.
//       type_is_proof_irrelevant (:75-88)         — THE Prop|SProp DISJUNCT.
//       type_is_quickly_not_in_prop (:105-115)    — the pure pre-filter.
//       try_infer_type_quick[_inner] (:117-187)   — the quick arms.
//   $HOME/clean/crates/clean-kernel/src/tc/infer_zfc.rs
//       infer_sprop (:156-171)                    — `SProp : Sort 1`, mode-gated.
//   $HOME/clean/crates/clean-kernel/src/tc/infer.rs
//       infer_sort_inner (:765-799)               — the SProp arm at :774
//                                                    (`SProp => Ok(Level::zero())`).
//   $HOME/clean/crates/clean-kernel/src/tc/def_eq/mod.rs:358-367 — the call site.
//   $HOME/clean/crates/clean-kernel/src/mode.rs                  — CleanMode.
//
// THE SOUNDNESS CONTROLS (centerpiece), each a SINGLE gate sharing every other
// line of the engine, so any verdict divergence is 100% attributable:
//   * Verifier.sprop_check == 1 (OVER-EAGER): `sprop_universe_check` returns
//     `true` regardless of the actual universe — i.e. is_sprop dropped its
//     universe check. This ACCEPTS distinct values of a non-SProp `Type`
//     (a =?= b : Foo) and, with the quick pre-filter also dropped, ACCEPTS the
//     literal `2 =?= 3`. Both are UNSOUND. The AWARE engine REJECTS. This is
//     the round soundness proof: the production universe check is EXACTLY what
//     prevents `2 = 3`.
//   * Verifier.sprop_check == 2 (POISON / INVERT): `sprop_universe_check`
//     returns `false` — SProp is never recognized. This REJECTS distinct
//     proofs of an SProp (hp1 =?= hp2 : P), proving the :86 disjunct is
//     load-bearing for the (sound) accept, while leaving the Prop path (:85)
//     UNCHANGED — the two arms are independent.
//   * Verifier.blind_quickfilter drops the type_is_quickly_not_in_prop
//     pre-filter, exposing that Nat is guarded in DEPTH (pre-filter AND
//     universe check).
//   * mode == Cubical exercises the proof_irrel.rs:36-38 early-out (proof
//     irrelevance disabled on the fibrant layer): SProp-typed proofs REJECT.
//
// MODELED BOUNDARIES (documented, inert on the exercised surface):
//   [B5-partial] ExprKind is the production core EXTENDED with `SProp` (this
//             round makes that arm LIVE). Squash/Cubical*/ZFC* ExprKind arms
//             remain structurally ABSENT — the Cubical/Directed def_eq arms,
//             the Squash quick-infer arm (proof_irrel.rs:167-180), and the
//             ZFC arms are NOT modeled. The CleanMode enum IS the full 6
//             variants (so the :36-38 mode early-out transcribes verbatim);
//             only Impredicative and Cubical are exercised.
//   [B-name]  Name modeled as its identity hash `Name{h:u64}` (name_eq = h==h);
//             the proof-irrel path only needs name IDENTITY (Nat/String
//             pre-filter constants + the env's per-decl names). Production
//             Names (murmur/mix chains) are de-modeled in R4/R5/R6/R7.
//   [B-levels] Sort carries a u32 depth; `is_zero()` == (depth == 0); Prop =
//             Sort(0), Type 0 = Sort(1). Full Max/IMax Level is verified in
//             R1/R6. `Level` for infer_sort is the same u32.
//   [B-ctx]   No LocalContext: every scenario term is a Const axiom / literal
//             (never an FVar), so try_infer_type_quick's FVar arm (:147, the
//             context lookup) is modeled `None`, and infer_sort's Pi arm
//             (:775-793, which opens into the context) is a documented stub —
//             dead on all scenario inputs. The R8/R9 context machinery is out
//             of scope here (verified there).
//   [B-env]   The env (`const_type`) is an in-fn match on name identity — the
//             production `env.instantiate_type(name, levels)` collapsed to a
//             per-decl type lookup (axioms: bodyless; B10 no level inst).
//   [B9]      `matches!(..)`-with-guard, `?`-on-Option, and `!(..)?` are
//             transcribed as explicit `match` (evaluation-strategy rewrites,
//             bit-identical verdicts). The quick_infer_cache (:126-141) is
//             elided [C-cache2]; stack_safe + the escaping-BVar debug_assert
//             are B4 pass-throughs.
//   [B-meta]  ExprMeta.hash is a plain in-fn FNV-style mix (NOT the production
//             SipHash — closed in R7). Used only for def_eq's structural fast
//             path and the native==JIT bit-identity of the SProp meta arm.
//
#![allow(clippy::all)]
#![allow(dead_code)]
#![allow(non_snake_case)]
#![allow(unused_variables)]
#![allow(unused_parens)]

use std::sync::Arc;

// ════════════════════════════════════════════════════════════════════════════
// Name — [B-name]: identity hash.
// ════════════════════════════════════════════════════════════════════════════
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Name {
    pub h: u64,
}
pub fn name_eq(a: &Name, b: &Name) -> bool {
    a.h == b.h
}

// The pre-filter constants (proof_irrel.rs:12-13 NAME_NAT / NAME_STRING).
pub fn nat_type_name() -> Name {
    Name { h: 1 }
}
pub fn str_type_name() -> Name {
    Name { h: 2 }
}

// The env's per-decl names.
pub fn nm_P() -> Name {
    Name { h: 10 }
} // P   : SProp
pub fn nm_hp1() -> Name {
    Name { h: 11 }
} // hp1 : P
pub fn nm_hp2() -> Name {
    Name { h: 12 }
} // hp2 : P
pub fn nm_Foo() -> Name {
    Name { h: 20 }
} // Foo : Type 0  (Sort 1)
pub fn nm_a() -> Name {
    Name { h: 21 }
} // a   : Foo
pub fn nm_b() -> Name {
    Name { h: 22 }
} // b   : Foo
pub fn nm_Q() -> Name {
    Name { h: 30 }
} // Q   : Prop   (Sort 0)
pub fn nm_q1() -> Name {
    Name { h: 31 }
} // q1  : Q
pub fn nm_q2() -> Name {
    Name { h: 32 }
} // q2  : Q

// ════════════════════════════════════════════════════════════════════════════
// CleanMode — mode.rs, the full 6 variants (so proof_irrel.rs:36-38 transcribes
// verbatim). Only Impredicative (SProp-valid, proof-irrel active) and Cubical
// (proof-irrel disabled) are exercised. [B5-partial]
// ════════════════════════════════════════════════════════════════════════════
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CleanMode {
    Constructive,
    Impredicative,
    Cubical,
    Directed,
    Classical,
    SetTheoretic,
}

// ════════════════════════════════════════════════════════════════════════════
// TypeError — minimal (infer_sprop's ModeRequired + infer_sort's ExpectedSort).
// ════════════════════════════════════════════════════════════════════════════
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum TypeError {
    ModeRequired,
    ExpectedSort,
    Other,
}

// ════════════════════════════════════════════════════════════════════════════
// Literal — Nat(u64) only (the 2 =?= 3 scenario). String is out of scope
// (de-modeled R3/R4); the proof-irrel path never touches it here. [B-lit]
// ════════════════════════════════════════════════════════════════════════════
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Literal {
    Nat(u64),
}
pub fn lit_eq(a: &Literal, b: &Literal) -> bool {
    match (a, b) {
        (Literal::Nat(x), Literal::Nat(y)) => x == y,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Expr / ExprKind / ExprMeta — the production core EXTENDED with SProp
// [B5-partial]. Sort(u32) depth [B-levels]; Const(Name) [B-name].
// ════════════════════════════════════════════════════════════════════════════
#[derive(Clone, Copy)]
pub struct ExprMeta {
    pub has_fvar: bool,
    pub hash: u64,
}
impl ExprMeta {
    pub fn raw(&self) -> u64 {
        self.hash
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct FVarId(pub u64);

#[derive(Clone)]
pub enum ExprKind {
    BVar(u32),
    FVar(FVarId),
    Sort(u32),
    Const(Name),
    App(Arc<Expr>, Arc<Expr>),
    Lam(Arc<Expr>, Arc<Expr>),
    Pi(Arc<Expr>, Arc<Expr>),
    Let(Arc<Expr>, Arc<Expr>, Arc<Expr>),
    Lit(Literal),
    Proj(Name, u32, Arc<Expr>),
    MData(Arc<Expr>),
    // R15 — the strict-proposition universe (expr/kind.rs:156).
    SProp,
}

#[derive(Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub meta: ExprMeta,
}

fn wmul(a: u64, b: u64) -> u64 {
    a.wrapping_mul(b)
}
fn mix2(a: u64, b: u64) -> u64 {
    wmul(a ^ b, 0x100000001b3)
}

impl ExprKind {
    pub fn compute_meta(&self) -> ExprMeta {
        match self {
            ExprKind::BVar(i) => ExprMeta {
                has_fvar: false,
                hash: mix2(1, *i as u64),
            },
            ExprKind::FVar(id) => ExprMeta {
                has_fvar: true,
                hash: mix2(2, id.0),
            },
            ExprKind::Sort(d) => ExprMeta {
                has_fvar: false,
                hash: mix2(3, *d as u64),
            },
            ExprKind::Const(n) => ExprMeta {
                has_fvar: false,
                hash: mix2(4, n.h),
            },
            ExprKind::App(f, a) => ExprMeta {
                has_fvar: f.meta.has_fvar || a.meta.has_fvar,
                hash: mix2(5, mix2(f.meta.hash, a.meta.hash)),
            },
            ExprKind::Lam(t, b) => ExprMeta {
                has_fvar: t.meta.has_fvar || b.meta.has_fvar,
                hash: mix2(6, mix2(t.meta.hash, b.meta.hash)),
            },
            ExprKind::Pi(t, b) => ExprMeta {
                has_fvar: t.meta.has_fvar || b.meta.has_fvar,
                hash: mix2(7, mix2(t.meta.hash, b.meta.hash)),
            },
            ExprKind::Let(t, v, b) => ExprMeta {
                has_fvar: t.meta.has_fvar || v.meta.has_fvar || b.meta.has_fvar,
                hash: mix2(8, mix2(t.meta.hash, mix2(v.meta.hash, b.meta.hash))),
            },
            ExprKind::Lit(l) => match l {
                Literal::Nat(v) => ExprMeta {
                    has_fvar: false,
                    hash: mix2(9, *v),
                },
            },
            ExprKind::Proj(n, i, e) => ExprMeta {
                has_fvar: e.meta.has_fvar,
                hash: mix2(10, mix2(n.h, mix2(*i as u64, e.meta.hash))),
            },
            ExprKind::MData(e) => ExprMeta {
                has_fvar: e.meta.has_fvar,
                hash: mix2(11, e.meta.hash),
            },
            // R15 — the SProp meta arm (childless, like the production
            // ExprKind::SProp; kind.rs:619 hashes the discriminant).
            ExprKind::SProp => ExprMeta {
                has_fvar: false,
                hash: mix2(12, 0),
            },
        }
    }
}

impl Expr {
    pub fn from_kind(kind: ExprKind) -> Expr {
        let meta = kind.compute_meta();
        Expr { kind, meta }
    }
    pub fn has_fvar_quick(&self) -> bool {
        self.meta.has_fvar
    }
    pub fn cnst(name: Name) -> Expr {
        Expr::from_kind(ExprKind::Const(name))
    }
    pub fn sort(d: u32) -> Expr {
        Expr::from_kind(ExprKind::Sort(d))
    }
    pub fn sprop() -> Expr {
        Expr::from_kind(ExprKind::SProp)
    }
    pub fn fvar(id: u64) -> Expr {
        Expr::from_kind(ExprKind::FVar(FVarId(id)))
    }
    pub fn bvar(i: u32) -> Expr {
        Expr::from_kind(ExprKind::BVar(i))
    }
    pub fn app(f: Expr, a: Expr) -> Expr {
        Expr::from_kind(ExprKind::App(Arc::new(f), Arc::new(a)))
    }
    pub fn lam(ty: Expr, body: Expr) -> Expr {
        Expr::from_kind(ExprKind::Lam(Arc::new(ty), Arc::new(body)))
    }
    pub fn pi(ty: Expr, body: Expr) -> Expr {
        Expr::from_kind(ExprKind::Pi(Arc::new(ty), Arc::new(body)))
    }
    pub fn lit_nat(v: u64) -> Expr {
        Expr::from_kind(ExprKind::Lit(Literal::Nat(v)))
    }
    pub fn mdata(inner: Expr) -> Expr {
        Expr::from_kind(ExprKind::MData(Arc::new(inner)))
    }

    // instantiate — beta-substitution of BVar(0) with `val` (shallow, depth-0).
    // Used by try_infer_type_quick's App arm (Pi-result instantiate) and whnf
    // beta. No scenario term has loose BVars beyond a single bound one. [B9]
    pub fn instantiate(&self, val: &Expr) -> Expr {
        self.inst_at(val, 0)
    }
    fn inst_at(&self, val: &Expr, depth: u32) -> Expr {
        match &self.kind {
            ExprKind::BVar(i) => {
                if *i == depth {
                    val.clone()
                } else {
                    self.clone()
                }
            }
            ExprKind::App(f, a) => Expr::from_kind(ExprKind::App(
                Arc::new(f.inst_at(val, depth)),
                Arc::new(a.inst_at(val, depth)),
            )),
            ExprKind::Lam(t, b) => Expr::from_kind(ExprKind::Lam(
                Arc::new(t.inst_at(val, depth)),
                Arc::new(b.inst_at(val, depth + 1)),
            )),
            ExprKind::Pi(t, b) => Expr::from_kind(ExprKind::Pi(
                Arc::new(t.inst_at(val, depth)),
                Arc::new(b.inst_at(val, depth + 1)),
            )),
            ExprKind::Let(t, v, b) => Expr::from_kind(ExprKind::Let(
                Arc::new(t.inst_at(val, depth)),
                Arc::new(v.inst_at(val, depth)),
                Arc::new(b.inst_at(val, depth + 1)),
            )),
            ExprKind::Proj(n, i, e) => {
                Expr::from_kind(ExprKind::Proj(*n, *i, Arc::new(e.inst_at(val, depth))))
            }
            ExprKind::MData(e) => Expr::from_kind(ExprKind::MData(Arc::new(e.inst_at(val, depth)))),
            _ => self.clone(),
        }
    }
}

// expr_syntactic_eq — production Expr::PartialEq (structural; sees every kind
// incl. SProp). Used as def_eq's P0 syntactic pre-check.
pub fn expr_syntactic_eq(a: &Expr, b: &Expr) -> bool {
    match (&a.kind, &b.kind) {
        (ExprKind::BVar(x), ExprKind::BVar(y)) => x == y,
        (ExprKind::FVar(x), ExprKind::FVar(y)) => x.0 == y.0,
        (ExprKind::Sort(x), ExprKind::Sort(y)) => x == y,
        (ExprKind::Const(x), ExprKind::Const(y)) => name_eq(x, y),
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
            expr_syntactic_eq(f1, f2) && expr_syntactic_eq(a1, a2)
        }
        (ExprKind::Lam(t1, b1), ExprKind::Lam(t2, b2)) => {
            expr_syntactic_eq(t1, t2) && expr_syntactic_eq(b1, b2)
        }
        (ExprKind::Pi(t1, b1), ExprKind::Pi(t2, b2)) => {
            expr_syntactic_eq(t1, t2) && expr_syntactic_eq(b1, b2)
        }
        (ExprKind::Let(t1, v1, b1), ExprKind::Let(t2, v2, b2)) => {
            expr_syntactic_eq(t1, t2) && expr_syntactic_eq(v1, v2) && expr_syntactic_eq(b1, b2)
        }
        (ExprKind::Lit(l1), ExprKind::Lit(l2)) => lit_eq(l1, l2),
        (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
            name_eq(n1, n2) && i1 == i2 && expr_syntactic_eq(e1, e2)
        }
        (ExprKind::MData(e1), ExprKind::MData(e2)) => expr_syntactic_eq(e1, e2),
        (ExprKind::SProp, ExprKind::SProp) => true, // kind.rs:323
        _ => false,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// The Verifier — the mode + the three soundness gates.
// ════════════════════════════════════════════════════════════════════════════
pub struct Verifier {
    pub mode: CleanMode,
    // 0 = AWARE (production `matches!(kind, SProp)`); 1 = OVER-EAGER (universe
    // check dropped -> always true); 2 = POISON (inverted -> never SProp).
    pub sprop_check: u8,
    // true = drop the type_is_quickly_not_in_prop pre-filter (defense removed).
    pub blind_quickfilter: bool,
}

impl Verifier {
    // ── env model [B-env]: a Const's declared type, keyed on name identity
    // (production `env.instantiate_type(name, levels)`; axioms are bodyless,
    // B10 no level instantiation). ──
    fn const_type(&self, name: &Name) -> Option<Expr> {
        if name_eq(name, &nm_P()) {
            return Some(Expr::sprop()); // P : SProp
        }
        if name_eq(name, &nm_hp1()) || name_eq(name, &nm_hp2()) {
            return Some(Expr::cnst(nm_P())); // hp_ : P
        }
        if name_eq(name, &nm_Foo()) {
            return Some(Expr::sort(1)); // Foo : Type 0 (= Sort 1)
        }
        if name_eq(name, &nm_a()) || name_eq(name, &nm_b()) {
            return Some(Expr::cnst(nm_Foo())); // a, b : Foo
        }
        if name_eq(name, &nm_Q()) {
            return Some(Expr::sort(0)); // Q : Prop (= Sort 0)
        }
        if name_eq(name, &nm_q1()) || name_eq(name, &nm_q2()) {
            return Some(Expr::cnst(nm_Q())); // q_ : Q
        }
        if name_eq(name, &nat_type_name()) {
            return Some(Expr::sort(1)); // Nat : Type 0 (= Sort 1)
        }
        None
    }

    // ── env delta model: bodyless axioms -> no unfolding (whnf delta stuck). ──
    fn unfold_definition_model(&self, _name: &Name) -> Option<Expr> {
        None
    }

    // ════════════════════════════════════════════════════════════════════════
    // whnf — a compact faithful whnf_core (beta / delta / zeta), stuck on
    // Sort / SProp / Const-axiom / FVar / Lit. For every scenario type this is
    // near-identity (all types are Const-axiom / Sort / SProp). [B-ctx]: no
    // context zeta (let-FVar) — verified in R9.
    // ════════════════════════════════════════════════════════════════════════
    fn whnf_impl(&self, e: &Expr) -> Expr {
        let mut cur = e.clone();
        loop {
            match &cur.kind {
                // delta — a Const with a body unfolds; our type-consts are
                // bodyless axioms, so this is stuck.
                ExprKind::Const(name) => match self.unfold_definition_model(name) {
                    Some(body) => {
                        cur = body;
                    }
                    None => return cur,
                },
                // beta / spine — App with a Lam head reduces.
                ExprKind::App(f, a) => {
                    let f_whnf = self.whnf_impl(f);
                    match &f_whnf.kind {
                        ExprKind::Lam(_ty, body) => {
                            cur = body.instantiate(a);
                        }
                        _ => {
                            // stuck application: rebuild with reduced head.
                            return Expr::from_kind(ExprKind::App(
                                Arc::new(f_whnf),
                                Arc::new(a.as_ref().clone()),
                            ));
                        }
                    }
                }
                // zeta — let reduces by substituting the value.
                ExprKind::Let(_t, v, b) => {
                    cur = b.instantiate(v);
                }
                // MData is transparent.
                ExprKind::MData(inner) => {
                    cur = inner.as_ref().clone();
                }
                // Sort / SProp / BVar / FVar / Lam / Pi / Lit / Proj — stuck.
                _ => return cur,
            }
        }
    }

    // ════════════════════════════════════════════════════════════════════════
    // THE PROOF-IRRELEVANCE FAMILY — tc/def_eq/proof_irrel.rs, VERBATIM, with
    // the R15 SProp disjunct (:86) LIVE.
    // ════════════════════════════════════════════════════════════════════════

    /// proof_irrel.rs:16-53 — is_def_eq_proof_irrel. The Cubical/Directed
    /// early-out (:36-38) is transcribed verbatim (mode gate). `?`-on-Option
    /// and `!(..)?` -> explicit match [B9]; `is_def_eq_impl(&ty_a, &ty_b)` is
    /// the pillar def_eq.
    fn is_def_eq_proof_irrel(&self, a: &Expr, b: &Expr) -> Option<bool> {
        // :36-38 — the fibrant (Cubical/Directed) layer must NOT use
        // definitional proof irrelevance (UIP is inconsistent with
        // univalence). Returning None only makes def-eq more conservative.
        // `self.mode == Cubical || self.mode == Directed` -> match [B9]
        // (avoids derived PartialEq on the enum; verdict-identical).
        match self.mode {
            CleanMode::Cubical => return None,
            CleanMode::Directed => return None,
            _ => {}
        }
        let ty_a = match self.infer_type_quick_or_full(a) {
            Some(t) => t,
            None => return None,
        };
        // :39-47 fast path — if ty_a is quickly known to NOT be in Prop, skip
        // the expensive type_is_proof_irrelevant check entirely.
        if self.type_is_quickly_not_in_prop(&ty_a) {
            return None;
        }
        match self.type_is_proof_irrelevant(&ty_a) {
            Some(true) => {}
            Some(false) => return None,
            None => return None,
        }
        let ty_b = match self.infer_type_quick_or_full(b) {
            Some(t) => t,
            None => return None,
        };
        Some(self.def_eq_impl(&ty_a, &ty_b))
    }

    /// proof_irrel.rs:65-73 — quick inference, else the FULL infer-only
    /// fallback (:72, `infer_type_infer_only`); `.ok()` -> match [B9]. The
    /// PROOF_IRREL_FALLBACK_INFER_COUNT test hook (:69-71) is elided.
    fn infer_type_quick_or_full(&self, e: &Expr) -> Option<Expr> {
        match self.try_infer_type_quick(e) {
            Some(ty) => Some(ty),
            None => match self.infer_type_infer_only_core(e) {
                Ok(t) => Some(t),
                Err(_) => None,
            },
        }
    }

    /// proof_irrel.rs:75-88 — type_is_proof_irrelevant: whnf the type; a Sort
    /// is QUICK-REJECTED (its type is Sort(succ) — never Prop); else the
    /// type-of-type must whnf to `Sort 0` (Prop, :85) OR to `ExprKind::SProp`
    /// (the R15 SProp disjunct, :86). The two disjuncts are routed so the
    /// controls can drop/invert JUST the SProp universe test.
    fn type_is_proof_irrelevant(&self, ty: &Expr) -> Option<bool> {
        let ty_whnf = self.whnf_impl(ty);
        // :77-81 — quick rejection: `ty : Sort` has type `Sort(succ(l))`,
        // never Sort(0)/Prop/SProp. Skip the expensive infer chain.
        match &ty_whnf.kind {
            ExprKind::Sort(_) => return Some(false),
            _ => {}
        }
        let ty_of_ty = match self.infer_type_quick_or_full(&ty_whnf) {
            Some(t) => t,
            None => return None,
        };
        let ty_of_ty_whnf = self.whnf_impl(&ty_of_ty);
        // :84-87 VERBATIM (the `matches!(.. Sort(l) if l.is_zero()) ||
        // matches!(.. SProp)`, split to an explicit match for the guard [B9]):
        //   the Prop disjunct (:85)  OR  the SProp disjunct (:86).
        let prop_disjunct = match &ty_of_ty_whnf.kind {
            ExprKind::Sort(d) => *d == 0, // Level::is_zero()
            _ => false,
        };
        Some(prop_disjunct || self.sprop_universe_check(&ty_of_ty_whnf))
    }

    /// proof_irrel.rs:86 — `matches!(ty_of_ty_whnf.kind(), ExprKind::SProp)`.
    /// AWARE (sprop_check==0) is the production universe check. The OVER-EAGER
    /// (==1) and POISON (==2) arms are the R15 soundness controls; they share
    /// EVERY other line of the engine.
    fn sprop_universe_check(&self, ty_of_ty_whnf: &Expr) -> bool {
        if self.sprop_check == 1 {
            // OVER-EAGER: universe check dropped — is_sprop returns true for
            // ANY type. UNSOUND: conflates distinct values of a non-SProp type.
            return true;
        }
        if self.sprop_check == 2 {
            // POISON: SProp never recognized — REJECTS distinct proofs of an
            // SProp (the :86 disjunct is load-bearing for the sound accept).
            return false;
        }
        // AWARE — the production `matches!(kind, ExprKind::SProp)`.
        match &ty_of_ty_whnf.kind {
            ExprKind::SProp => true,
            _ => false,
        }
    }

    /// proof_irrel.rs:105-115 — the pure pre-filter. Const arm's
    /// `levels.is_empty()` is trivially true in the monomorphic Const model
    /// [B-levels]; the `*name == *NAME_NAT || *name == *NAME_STRING` is
    /// name_eq against the same pre-filter constants. blind_quickfilter drops
    /// the whole filter (control): returning false is always SAFE (means "do
    /// the full check").
    fn type_is_quickly_not_in_prop(&self, ty: &Expr) -> bool {
        if self.blind_quickfilter {
            return false;
        }
        match &ty.kind {
            // Sort(l) : Sort(succ(l)) — always in a Sort above Prop.
            ExprKind::Sort(_) => true,
            // Literal types: Nat and String are both in Type 0, not Prop.
            ExprKind::Const(name) => {
                name_eq(name, &nat_type_name()) || name_eq(name, &str_type_name())
            }
            _ => false,
        }
    }

    /// proof_irrel.rs:117-143 wrapper (cache elided [C-cache2], stack_safe +
    /// debug_assert B4) over :145-187 try_infer_type_quick_inner — the quick
    /// arms VERBATIM on the extended core.
    fn try_infer_type_quick(&self, e: &Expr) -> Option<Expr> {
        self.try_infer_type_quick_inner(e)
    }
    fn try_infer_type_quick_inner(&self, e: &Expr) -> Option<Expr> {
        match &e.kind {
            // :147 — the FVar TYPE comes from the context. [B-ctx]: no
            // LocalContext modeled (no scenario term is an FVar) -> None.
            ExprKind::FVar(_id) => None,
            // :148 — `self.env.instantiate_type(name, levels)`. [B-env].
            ExprKind::Const(name) => self.const_type(name),
            // :149.
            ExprKind::Sort(l) => Some(Expr::sort(l + 1)),
            // :150-157 — quick fn type, whnf, Pi-result instantiate.
            ExprKind::App(f, a) => {
                let f_type = match self.try_infer_type_quick(f) {
                    Some(t) => t,
                    None => return None,
                };
                let f_type_whnf = self.whnf_impl(&f_type);
                match &f_type_whnf.kind {
                    ExprKind::Pi(_ty, result_type) => Some(result_type.instantiate(a)),
                    _ => None,
                }
            }
            // :158-161 — quick body type wrapped in Pi.
            ExprKind::Lam(ty, body) => {
                let body_type = match self.try_infer_type_quick(body) {
                    Some(t) => t,
                    None => return None,
                };
                Some(Expr::pi(ty.as_ref().clone(), body_type))
            }
            // :162-165 — literal types (B-name constants).
            ExprKind::Lit(lit) => Some(match lit {
                Literal::Nat(_) => Expr::cnst(nat_type_name()),
            }),
            // :166.
            ExprKind::MData(inner) => self.try_infer_type_quick(inner),
            // :181-184 Proj — [C-proj-quick] production consults
            // infer_proj_type_from_quick; None here (no live Proj on the quick
            // path this round). :167-180 Squash quick arm ABSENT [B5-partial].
            ExprKind::Proj(_, _, _) => None,
            // :185 — the production catch-all (BVar, Pi, Let, SProp, ...).
            _ => None,
        }
    }

    /// tc/infer.rs infer_type_infer_only — the proof-irrel FULL fallback.
    /// Transcribed as the arms needed on the exercised surface (the
    /// `if !self.infer_only.get()` check blocks are statically OFF
    /// [C-inferonly]): Const/Sort/Lit/MData mirror the quick arms; SProp
    /// routes to infer_sprop (the ONLY arm the quick path lacks); everything
    /// else is a documented boundary (Err) — dead on all scenario inputs.
    fn infer_type_infer_only_core(&self, e: &Expr) -> Result<Expr, TypeError> {
        match &e.kind {
            ExprKind::Const(name) => match self.const_type(name) {
                Some(t) => Ok(t),
                None => Err(TypeError::Other),
            },
            ExprKind::Sort(l) => Ok(Expr::sort(l + 1)),
            ExprKind::Lit(lit) => Ok(match lit {
                Literal::Nat(_) => Expr::cnst(nat_type_name()),
            }),
            ExprKind::MData(inner) => self.infer_type_infer_only_core(inner),
            // infer.rs:645 — `ExprKind::SProp => self.infer_sprop()`.
            ExprKind::SProp => self.infer_sprop(),
            _ => Err(TypeError::Other),
        }
    }

    /// infer_zfc.rs:156-171 — `infer_sprop`: SProp : Sort 1 (= Type 0),
    /// mode-gated to Impredicative / Classical / SetTheoretic. VERBATIM.
    fn infer_sprop(&self) -> Result<Expr, TypeError> {
        // `mode != Impredicative && != Classical && != SetTheoretic` -> match
        // [B9] (avoids derived PartialEq on the enum; verdict-identical).
        match self.mode {
            CleanMode::Impredicative => {}
            CleanMode::Classical => {}
            CleanMode::SetTheoretic => {}
            _ => return Err(TypeError::ModeRequired),
        }
        // SProp is a sort like Prop, so SProp : Type 1 (Sort(succ(zero))).
        Ok(Expr::sort(1))
    }

    // ════════════════════════════════════════════════════════════════════════
    // infer_sort — infer.rs:735-799. The SProp arm (:774) LIVE. The Pi arm
    // (:775-793, opens into the context) is a documented [B-ctx] stub — dead
    // on all scenario inputs (P/Q/Foo/SProp are never Pi-typed).
    // ════════════════════════════════════════════════════════════════════════
    fn infer_sort(&self, e: &Expr) -> Result<u32, TypeError> {
        self.infer_sort_inner(e, 0)
    }
    fn infer_sort_inner(&self, e: &Expr, depth: u32) -> Result<u32, TypeError> {
        let ty = match self.infer_type_infer_only_core(e) {
            Ok(t) => t,
            Err(err) => return Err(err),
        };
        let ty_whnf = self.whnf_impl(&ty);
        match &ty_whnf.kind {
            ExprKind::Sort(l) => Ok(*l),
            // :774 — `ExprKind::SProp => Ok(Level::zero())`.
            ExprKind::SProp => Ok(0),
            // :775-793 Pi — opens into the LocalContext. [B-ctx] stub (dead).
            ExprKind::Pi(_ty, _body) => Err(TypeError::Other),
            _ => Err(TypeError::ExpectedSort),
        }
    }

    // ════════════════════════════════════════════════════════════════════════
    // THE def_eq ENGINE — a focused transcription of def_eq/mod.rs's phase
    // ordering: P0 syntactic (:300-ish quick / :341 equal-after-whnf), the
    // proof-irrelevance consult at the PRODUCTION position (:358-367), then
    // structural congruence (the remaining phases: Const/App/Sort/... eta).
    // The lazy-delta / cache / reducer phases (R11-R14) are elided here — this
    // is the R13/R14-style FOCUSED slice; the full-engine gate is verified
    // R9-R14. reduce_nat is NOT modeled (so `2 =?= 3` rejects structurally, the
    // correct verdict; the quick pre-filter + universe check are what the
    // controls target).
    // ════════════════════════════════════════════════════════════════════════
    fn is_def_eq(&self, a: &Expr, b: &Expr) -> bool {
        self.def_eq_inner(a, b)
    }
    fn def_eq_impl(&self, a: &Expr, b: &Expr) -> bool {
        self.def_eq_inner(a, b)
    }
    fn def_eq_inner(&self, a: &Expr, b: &Expr) -> bool {
        // P0 syntactic (before any reduction) — reflexivity fast path.
        if a.meta.raw() == b.meta.raw() && expr_syntactic_eq(a, b) {
            return true;
        }
        let a_whnf = self.whnf_impl(a);
        let b_whnf = self.whnf_impl(b);
        // equal after whnf (def_eq/mod.rs:341).
        if a_whnf.meta.raw() == b_whnf.meta.raw() && expr_syntactic_eq(&a_whnf, &b_whnf) {
            return true;
        }
        // ── def_eq/mod.rs:358-367 VERBATIM at the production POSITION: after
        // reduction + the equality fast path, before the congruence phases.
        // ONLY Some(true) short-circuits; Some(false) / None fall through. ──
        let proof_irrel = self.is_def_eq_proof_irrel(&a_whnf, &b_whnf);
        match proof_irrel {
            Some(true) => return true,
            _ => {}
        }
        // structural congruence (P6-ish), incl. SProp == SProp.
        let matched = match (&a_whnf.kind, &b_whnf.kind) {
            (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
            (ExprKind::FVar(i), ExprKind::FVar(j)) => i.0 == j.0,
            (ExprKind::Sort(l1), ExprKind::Sort(l2)) => l1 == l2,
            (ExprKind::Const(n1), ExprKind::Const(n2)) => name_eq(n1, n2),
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                self.def_eq_impl(f1, f2) && self.def_eq_impl(a1, a2)
            }
            (ExprKind::Lam(t1, b1), ExprKind::Lam(t2, b2)) => {
                self.def_eq_impl(t1, t2) && self.def_eq_impl(b1, b2)
            }
            (ExprKind::Pi(t1, b1), ExprKind::Pi(t2, b2)) => {
                self.def_eq_impl(t1, t2) && self.def_eq_impl(b1, b2)
            }
            (ExprKind::Let(t1, v1, b1), ExprKind::Let(t2, v2, b2)) => {
                self.def_eq_impl(t1, t2) && self.def_eq_impl(v1, v2) && self.def_eq_impl(b1, b2)
            }
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => lit_eq(l1, l2),
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
                name_eq(n1, n2) && i1 == i2 && self.def_eq_impl(e1, e2)
            }
            (ExprKind::MData(in1), ExprKind::MData(in2)) => self.def_eq_impl(in1, in2),
            (ExprKind::SProp, ExprKind::SProp) => true,
            _ => false,
        };
        matched
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Scenario construction.
// ════════════════════════════════════════════════════════════════════════════
fn build_defeq_scenario(scenario: u64) -> (Expr, Expr) {
    if scenario == 0 {
        // (a) hp1 =?= hp2 : P where P : SProp. DISTINCT proofs of a strict
        //     proposition — ACCEPTED by strict irrelevance (via the :86 SProp
        //     disjunct). Structural congruence would REJECT (distinct names).
        (Expr::cnst(nm_hp1()), Expr::cnst(nm_hp2()))
    } else if scenario == 1 {
        // (b) a =?= b : Foo where Foo : Type 0 (Sort 1). DISTINCT values of a
        //     NON-SProp type — must be REJECTED (strict irrelevance must NOT
        //     fire). THE CENTERPIECE: the over-eager control ACCEPTS this.
        (Expr::cnst(nm_a()), Expr::cnst(nm_b()))
    } else if scenario == 2 {
        // (c) q1 =?= q2 : Q where Q : Prop (Sort 0). DISTINCT proofs of a Prop
        //     — ACCEPTED via the Prop disjunct (:85), a DIFFERENT code path
        //     from SProp (:86). Shows the two arms are distinct.
        (Expr::cnst(nm_q1()), Expr::cnst(nm_q2()))
    } else if scenario == 3 {
        // (d) 2 =?= 3 : Nat. DISTINCT nat literals — REJECT (correct). Guarded
        //     in DEPTH: the quick pre-filter (Nat) short-circuits before the
        //     universe check. With blind_quickfilter set, the over-eager
        //     control reaches the universe check and ACCEPTS (unsound 2=?=3).
        (Expr::lit_nat(2), Expr::lit_nat(3))
    } else if scenario == 4 {
        // trivial reflexivity control: hp1 =?= hp1 : P — ACCEPT by P0
        // syntactic (NOT proof irrelevance).
        (Expr::cnst(nm_hp1()), Expr::cnst(nm_hp1()))
    } else if scenario == 5 {
        // trivial reflexivity control: a =?= a : Foo — ACCEPT by P0.
        (Expr::cnst(nm_a()), Expr::cnst(nm_a()))
    } else {
        // default: Sort 0 =?= Sort 0 — ACCEPT.
        (Expr::sort(0), Expr::sort(0))
    }
}

// ════════════════════════════════════════════════════════════════════════════
// ROOTS — mono #[cfg_attr(not(test), no_mangle)] entries (standalone re-emit).
// ════════════════════════════════════════════════════════════════════════════

// def_eq differential dispatcher. idx encodes:
//   bits 0-7  : scenario id
//   bits 8-9  : sprop_check (0 aware / 1 over-eager / 2 poison)
//   bit  10   : blind_quickfilter
//   bit  11   : cubical_mode (mode = Cubical if set, else Impredicative)
// Returns 1 (accept) / 0 (reject).
#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn sprop_defeq_root(idx: u64) -> u64 {
    let scenario = idx & 0xff;
    let sprop_check = ((idx >> 8) & 0x3) as u8;
    let blind_quickfilter = (idx & 0x400) != 0;
    let cubical_mode = (idx & 0x800) != 0;
    let mode = if cubical_mode {
        CleanMode::Cubical
    } else {
        CleanMode::Impredicative
    };
    let v = Verifier {
        mode,
        sprop_check,
        blind_quickfilter,
    };
    let (a, b) = build_defeq_scenario(scenario);
    if v.is_def_eq(&a, &b) { 1 } else { 0 }
}

// infer_sort gate dispatcher — exercises the SProp arm (infer.rs:774) and
// infer_sprop's mode gate (infer_zfc.rs:160-168). idx encodes:
//   bits 0-7 : term id (0 P / 1 Q / 2 Foo / 3 SProp)
//   bit  8   : constructive_mode (mode = Constructive if set, else Impredicative)
// Returns the sort level, or u64::MAX on TypeError.
#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn sprop_infer_sort_root(idx: u64) -> u64 {
    let term_id = idx & 0xff;
    let constructive_mode = (idx & 0x100) != 0;
    let mode = if constructive_mode {
        CleanMode::Constructive
    } else {
        CleanMode::Impredicative
    };
    let v = Verifier {
        mode,
        sprop_check: 0,
        blind_quickfilter: false,
    };
    let e = if term_id == 0 {
        Expr::cnst(nm_P()) // P : SProp  -> infer_sort peels to the SProp arm.
    } else if term_id == 1 {
        Expr::cnst(nm_Q()) // Q : Prop   -> Sort 0.
    } else if term_id == 2 {
        Expr::cnst(nm_Foo()) // Foo : Type 0 -> Sort 1.
    } else {
        Expr::sprop() // SProp itself -> infer_sprop (mode gate) -> Sort 1.
    };
    match v.infer_sort(&e) {
        Ok(level) => level as u64,
        Err(_) => u64::MAX,
    }
}
