// R14 — THE DEF-EQ CACHE LAYER. Verbatim transcription of clean-kernel's
// definitional-equality CACHE surface (tc/def_eq/mod.rs is_def_eq / is_def_eq_impl
// / is_def_eq_inner — the DefEqCacheKey routing + the #1773/#38 negative-cache
// SOUNDNESS guard `all_fvars_in_context`; tc/equiv_manager.rs — the union-find
// equivalence manager; tc/branch_sharing.rs — the #3402 verified-pair memo),
// wired at their PRODUCTION positions around is_def_eq_core, verified
// native == JIT (Clean's CIC kernel through Trust: Rust -> MIR -> trust-ir ->
// trust-cg -> machine code).
//
// The point of the round is SOUNDNESS: a def_eq cache must be transparent
// (hit == miss on every verdict — it changes nothing but a hit counter), and a
// NEGATIVE (not-def-eq) verdict is CONTEXT-DEPENDENT when the compared terms
// carry FVars whose meaning comes from the LocalContext. Caching such a negative
// across a DIFFERENT context (where those fvars are gone / rebound) and trusting
// it blindly returns a STALE WRONG answer. The #1773 guard (`all_fvars_in_context`
// + the `out_of_context` read gate at mod.rs:250-255) forces a RECOMPUTE when a
// cached negative mentions a fvar not in the current context. A cache WITHOUT
// this guard is UNSOUND.
//
// PRODUCTION POSITIONS transcribed verbatim (tc/def_eq/mod.rs):
//   is_def_eq          (:176-189) — public entry; post-result add_equiv on TRUE.
//   is_def_eq_impl     (:195-197) — the recursive entry (cache lives here).
//   is_def_eq_inner    (:200-270) — equiv consult (:210), structural fast-path
//                       (:218), DefEqCacheKey::new (:225), cache get (:231), the
//                       #1773 out_of_context negative-cache guard (:250-255),
//                       is_def_eq_core recompute (:259), cache insert (:263-267).
//   DefEqCacheKey      (:88-165) — unordered {a,b}+transparency key; hash-based
//                       canonical ordering (:113-132, smaller hash in `a`);
//                       commutative min/max Hash (:157-164); unordered Eq
//                       (:137-141). #957/#968/#1774/#1636.
//   all_fvars_in_context (:535-603) — the #1773 recursive in-context walk.
//   quick_is_def_eq    (:493-525) — the equiv consult (:495) + reachable arms.
// tc/equiv_manager.rs: EquivManager union-find — add_equiv (:67-71), is_equiv /
//   is_equiv_core (:62-348), find (:97-110, path compression), merge (:113-128,
//   union by rank), get_or_insert_node (:131-138).
// tc/branch_sharing.rs: try_branch_sharing_def_eq (:442-497, recursor-congruence
//   fast path — NEVER Some(false), only Some(true)/None), branch_sharing_compare
//   (:283-311, verified-pair O(1) check + record-on-success), is_verified_pair /
//   record_verified_pair (:67-89, canonical smaller-hash-first key).
//
// THE CONFIG KNOBS (the falsifiability construction):
//   Verifier.cache_mode : 0 = NOCACHE  (the R13/R12 def_eq engine — no def_eq
//                                        cache; the TRANSPARENCY BASELINE),
//                         1 = AWARE    (cache ON + the #1773 guard, = production),
//                         2 = BLIND    (cache ON, guard REMOVED — trusts a cached
//                                        NEGATIVE unconditionally; the UNSOUND
//                                        control).
//   Verifier.equiv_off  : skip the equiv_manager consult (to isolate the def_eq
//                         cache hit path from the union-find short-circuit).
// AWARE and BLIND share EVERY other line; the ONLY divergence is the guard, so
// any verdict divergence is 100% attributable to the #1773 guard — the sharpest
// falsifiability construction (identical to R13's blind_nat).
//
// MODELED BOUNDARIES (documented, stated precisely per DISCIPLINE):
//   [C-cache]  The real def_eq_cache is a SlidingCache<DefEqCacheKey, bool>
//              (double-buffer generational hashbrown over a KaniHasher/ahash
//              bucketing of the commutative min/max key hash). Here it is an
//              append-only Vec<DefEqEntry> SCANNED with the REAL DefEqCacheKey
//              PartialEq (unordered {a,b} + transparency, via expr_syntactic_eq),
//              exactly as the R2 whnf-cache routing modeled SlidingCache
//              (tests/slices/clean_tc_stitch_slice.rs [C3]). What is VERIFIED is
//              the ROUTING + KEY DISCIPLINE: the canonical hash ordering
//              (DefEqCacheKey::new picks smaller-hash-first), the unordered
//              structural key equality, the transparency tag in the key (#1636),
//              the out_of_context read gate, and the record. The hashbrown
//              BUCKETING, the SlidingCache generational trim/promote, and
//              max_cache_entries eviction are modeled out (pure performance; no
//              verdict effect). KEY CONSTRUCTION is precise: DefEqCacheKey hashes
//              NOTHING beyond Expr::hash_cached() (the O(1) cached ExprMeta.hash),
//              which I DO model (compute_meta below); the min/max of the two
//              cached hashes is the commutative combine; there is no separate
//              key-payload hash to model.
//   [C-equiv]  EquivManager's `nodes: Vec<Node>` + `to_node: HashMap<Expr,NodeRef>`
//              is flattened to `equiv_nodes: Vec<EquivNode>` + `equiv_keys:
//              Vec<Expr>` with node index == insertion order (get_or_insert_node
//              scans equiv_keys with expr_syntactic_eq). find (path compression)
//              and merge (union by rank) are VERBATIM. The SlidingEquivManager
//              double-buffer + trim is modeled out (pure perf). The union-find
//              algebra — the soundness-relevant part — is exact.
//   [C-branch] branch_sharing's verified_pairs: HashMap<(Expr,Expr),()> ->
//              Vec<(Expr,Expr)> slice-scan with the REAL canonical smaller-hash
//              key + record-on-success. The whnf-prefix memo (`entries`) is a
//              pure performance cache (recomputes the same whnf) — modeled out
//              [C-bs-whnf]; branch_sharing_whnf calls whnf_core_no_delta directly.
//              The verified-pair KEY DISCIPLINE (canonical order, record only on
//              a proven-equal comparison) is the soundness-relevant part, exact.
//   [B-name]   Name = identity hash Name{h:u64} (name_eq = h==h). Production
//              murmur/mix Names de-modeled R4/R5/R6; the cache only needs Name
//              identity (through expr_syntactic_eq / compute_meta).
//   [B-levels] Const is monomorphic (implicit empty level list); Sort a u32
//              depth. try_branch_sharing's `levels` compare is over empty lists.
//   [B-meta]   ExprMeta.hash is the same in-fn FNV mix as R13 (wrapping_mul by
//              const 1099511628211) — used for the native==JIT bit-identity AND
//              as the O(1) cached hash the DefEqCacheKey canonical ordering /
//              equiv hash pre-filter consume. Not the production SipHash13 (that
//              is closed in R7); both sides compute the SAME mix, and the ordering
//              is verdict-inert (the scan is structural), so this is faithful to
//              the cache-key DISCIPLINE. has_fvar IS faithful (drives the #1773
//              guard's `has_fvar_quick()` pre-test at mod.rs:251).
//   [B-engine] The thing being CACHED is a compact but faithful is_def_eq_core:
//              P0 syntactic, quick (Sort/Lit + equiv consult), P1 no-delta whnf
//              (beta/zeta/MData) + re-quick, branch-sharing hook (#3402 position),
//              P2 lazy delta (delta step, height ordering), P3 Const/FVar head,
//              P6 structural congruence. Proof-irrel / struct-eta / string-lit /
//              unit-like / the nat/native/monad reducers are registry-empty /
//              out of scope (verified R9..R13); they are inert on every scenario
//              here. This mirrors R13's FOCUSED-slice discipline (the full
//              P0-P8 engine was verified R9-R12).
//   [B-proj]   No Proj/struct-eta ExprKind (no scenario needs it; verified R2/R12).
//   [C-ptreq]  is_def_eq_inner's `std::ptr::eq(a,b)` micro-opt (:202) is omitted
//              (unobservable — the structural fast-path at :218 subsumes it).
//   [C-leak]   THE #38 LEAK, modeled explicitly for the guard scenario: production
//              clears the def_eq/whnf caches on `local_context_mut()` push/pop
//              (tc/tests/defeq.rs:938 contract), so within the monotonic-FVarId
//              invariant a cache entry cannot leak across a context change. The
//              #1773 guard is the LAST-LINE defense against the elaborator/tactic
//              path (#38) that hands the kernel a term carrying a FVar that is NOT
//              a current context decl (a sibling subgoal's binder leaked through
//              a metavariable's stored type) WITHOUT going through the clearing
//              path. The guard scenario models exactly this: the cache PERSISTS
//              across a context mutation (the leak), the leaked FVar `x` is out of
//              the later context (tripping `all_fvars_in_context`), and a genuine
//              refinement of the in-context FVar `y` (an mvar assignment — clean
//              has no MVar ExprKind, so modeled as a LocalContext value change)
//              makes the CORRECT verdict flip to accept. The guard recomputes and
//              gets it right; the blind cache returns the stale wrong reject.
//
// Source of truth (read in full):
//   $HOME/clean/crates/clean-kernel/src/tc/def_eq/mod.rs        (cache routing + guard)
//   $HOME/clean/crates/clean-kernel/src/tc/equiv_manager.rs     (union-find)
//   $HOME/clean/crates/clean-kernel/src/tc/branch_sharing.rs    (#3402 verified pairs)
//   $HOME/clean/crates/clean-kernel/src/tc/sliding_cache.rs     ([C-cache] SlidingCache)
//   $HOME/clean/crates/clean-kernel/src/tc/mod.rs:274-590        (TypeChecker fields)
//   $HOME/clean/crates/clean-kernel/src/tc/local_context.rs      (LocalContext)

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
pub fn nm_foo() -> Name {
    Name { h: 3001 }
}
pub fn nm_bar() -> Name {
    Name { h: 3002 }
}
pub fn nm_dfn() -> Name {
    Name { h: 3003 }
} // a def whose body is `foo` (delta)
pub fn nm_baz() -> Name {
    Name { h: 3005 }
}
pub fn nm_g() -> Name {
    Name { h: 3004 }
}
pub fn nm_x() -> Name {
    Name { h: 4001 }
} // the leaked fvar's user name
pub fn nm_y() -> Name {
    Name { h: 4002 }
} // the in-context fvar's user name
pub fn nm_motive() -> Name {
    Name { h: 5001 }
}
pub fn nm_maj() -> Name {
    Name { h: 5002 }
}
pub fn bool_rec_name() -> Name {
    Name { h: 5000 }
} // the recursor head

// ════════════════════════════════════════════════════════════════════════════
// Expr / ExprKind / ExprMeta — [B-levels] Sort(u32), Const(Name); [B-proj] no
// Proj; [B-lit] Lit(u64) small nat.
// ════════════════════════════════════════════════════════════════════════════
#[derive(Clone, Copy)]
pub struct ExprMeta {
    pub has_fvar: bool,
    pub hash: u64,
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
    Lit(u64),
    MData(Arc<Expr>),
}

#[derive(Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub meta: ExprMeta,
}

// wrapping_mul leaf (shim); FNV-style mix with the const 1099511628211 (the
// armed-golden corruption target, identical to R13).
fn wmul(a: u64, b: u64) -> u64 {
    a.wrapping_mul(b)
}
fn mix2(a: u64, b: u64) -> u64 {
    wmul(a ^ b, 1099511628211)
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
            ExprKind::Lit(v) => ExprMeta {
                has_fvar: false,
                hash: mix2(9, *v),
            },
            ExprKind::MData(e) => ExprMeta {
                has_fvar: e.meta.has_fvar,
                hash: mix2(11, e.meta.hash),
            },
        }
    }
}

impl Expr {
    pub fn from_kind(kind: ExprKind) -> Expr {
        let meta = kind.compute_meta();
        Expr { kind, meta }
    }
    // Expr::hash_cached() (O(1) cached ExprMeta.hash) — the value DefEqCacheKey /
    // the equiv hash pre-filter consume.
    pub fn hash_cached(&self) -> u64 {
        self.meta.hash
    }
    // Expr::has_fvar_quick() (meta bit) — the #1773 guard's pre-test.
    pub fn has_fvar_quick(&self) -> bool {
        self.meta.has_fvar
    }
    pub fn cnst(name: Name) -> Expr {
        Expr::from_kind(ExprKind::Const(name))
    }
    pub fn app(f: Expr, a: Expr) -> Expr {
        Expr::from_kind(ExprKind::App(Arc::new(f), Arc::new(a)))
    }
    pub fn sort(d: u32) -> Expr {
        Expr::from_kind(ExprKind::Sort(d))
    }
    pub fn fvar(id: u64) -> Expr {
        Expr::from_kind(ExprKind::FVar(FVarId(id)))
    }
    pub fn bvar(i: u32) -> Expr {
        Expr::from_kind(ExprKind::BVar(i))
    }
    pub fn lam(ty: Expr, body: Expr) -> Expr {
        Expr::from_kind(ExprKind::Lam(Arc::new(ty), Arc::new(body)))
    }
    pub fn lit(v: u64) -> Expr {
        Expr::from_kind(ExprKind::Lit(v))
    }
    pub fn mdata(inner: Expr) -> Expr {
        Expr::from_kind(ExprKind::MData(Arc::new(inner)))
    }

    // get_app_fn — walk the App spine to the head.
    pub fn get_app_fn(&self) -> &Expr {
        let mut cur = self;
        loop {
            match &cur.kind {
                ExprKind::App(f, _) => cur = f,
                _ => return cur,
            }
        }
    }
    pub fn get_app_num_args(&self) -> usize {
        let mut n = 0usize;
        let mut cur = self;
        loop {
            match &cur.kind {
                ExprKind::App(f, _) => {
                    n += 1;
                    cur = f;
                }
                _ => return n,
            }
        }
    }
    // get_app_args — collect spine args left-to-right ([B9] Vec, not AppArgs).
    pub fn get_app_args(&self) -> Vec<Expr> {
        let mut rev: Vec<Expr> = Vec::new();
        let mut cur = self;
        loop {
            match &cur.kind {
                ExprKind::App(f, a) => {
                    rev.push(a.as_ref().clone());
                    cur = f;
                }
                _ => break,
            }
        }
        // reverse in place.
        let mut out: Vec<Expr> = Vec::new();
        let mut i = rev.len();
        while i > 0 {
            i -= 1;
            out.push(rev[i].clone());
        }
        out
    }

    // instantiate — beta substitution of BVar(0) with `val` at depth 0.
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
            ExprKind::MData(e) => Expr::from_kind(ExprKind::MData(Arc::new(e.inst_at(val, depth)))),
            _ => self.clone(),
        }
    }
}

// expr_syntactic_eq — production Expr::PartialEq (structural, every kind). This
// is the relation the DefEqCacheKey PartialEq, the equiv structural fallback,
// and the verified-pair keys all evaluate.
pub fn expr_syntactic_eq(a: &Expr, b: &Expr) -> bool {
    // ExprMeta hash pre-filter (production Expr::eq metadata pre-check).
    if a.meta.hash != b.meta.hash {
        return false;
    }
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
        (ExprKind::Lit(x), ExprKind::Lit(y)) => x == y,
        (ExprKind::MData(e1), ExprKind::MData(e2)) => expr_syntactic_eq(e1, e2),
        _ => false,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// LocalContext — tc/local_context.rs (push / push_let / pop / get, VERBATIM
// shape). set_value models the elaborator refining an in-context binder's value
// ([C-leak] — the mvar-assignment stand-in; clean has no MVar ExprKind).
// ════════════════════════════════════════════════════════════════════════════
#[derive(Clone)]
pub struct LocalDecl {
    pub id: FVarId,
    pub name: Name,
    pub type_: Expr,
    pub value: Option<Expr>,
}

pub struct LocalContext {
    pub decls: Vec<LocalDecl>,
    pub next_id: u64,
}

impl LocalContext {
    pub fn new() -> LocalContext {
        LocalContext {
            decls: Vec::new(),
            next_id: 0,
        }
    }
    // push (:79-99) — mint fresh id, append plain decl (value None).
    pub fn push(&mut self, name: Name, type_: Expr) -> FVarId {
        let id = FVarId(self.next_id);
        self.next_id += 1;
        self.decls.push(LocalDecl {
            id,
            name,
            type_,
            value: None,
        });
        id
    }
    // push_let (:109-129) — append let decl (value Some).
    pub fn push_let(&mut self, name: Name, type_: Expr, value: Expr) -> FVarId {
        let id = FVarId(self.next_id);
        self.next_id += 1;
        self.decls.push(LocalDecl {
            id,
            name,
            type_,
            value: Some(value),
        });
        id
    }
    // pop (:189-193) — drop the last decl; ids never re-minted (next_id monotone).
    pub fn pop(&mut self) {
        let _d = self.decls.pop();
    }
    // get (:201-204) — BACKWARD scan (latest pushed position wins).
    pub fn get(&self, id: FVarId) -> Option<LocalDecl> {
        let mut i = self.decls.len();
        while i > 0 {
            i -= 1;
            if self.decls[i].id == id {
                return Some(self.decls[i].clone());
            }
        }
        None
    }
    pub fn len(&self) -> usize {
        self.decls.len()
    }
    // [C-leak] set the value of an existing decl (elaborator refinement model).
    pub fn set_value(&mut self, id: FVarId, value: Expr) {
        let mut i = self.decls.len();
        while i > 0 {
            i -= 1;
            if self.decls[i].id == id {
                self.decls[i].value = Some(value);
                return;
            }
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Reducibility — def_eq/delta.rs ordering (Reducible > Regular(h) > Irreducible
// > Opaque; taller Regular first).
// ════════════════════════════════════════════════════════════════════════════
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Reducibility {
    Reducible,
    Regular(u32),
    Irreducible,
    Opaque,
}
impl Reducibility {
    pub fn rank(&self) -> u32 {
        match self {
            Reducibility::Reducible => 3,
            Reducibility::Regular(_) => 2,
            Reducibility::Irreducible => 1,
            Reducibility::Opaque => 0,
        }
    }
    pub fn compare(&self, other: &Reducibility) -> i32 {
        let ra = self.rank();
        let rb = other.rank();
        if ra != rb {
            if ra < rb {
                return -1;
            } else {
                return 1;
            }
        }
        match (self, other) {
            (Reducibility::Regular(ha), Reducibility::Regular(hb)) => {
                if ha < hb {
                    -1
                } else if ha > hb {
                    1
                } else {
                    0
                }
            }
            _ => 0,
        }
    }
    pub fn is_regular(&self) -> bool {
        match self {
            Reducibility::Regular(_) => true,
            _ => false,
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// RecInfo — the minimal recursor metadata env.get_recursor returns (used by
// branch_sharing's as_recursor_app). MajorAfterMotive Bool.rec model.
// ════════════════════════════════════════════════════════════════════════════
#[derive(Clone, Copy)]
pub struct RecInfo {
    pub num_params: usize,
    pub num_motives: usize,
    pub num_indices: usize,
    pub num_minors: usize,
}

// ════════════════════════════════════════════════════════════════════════════
// EquivNode — equiv_manager.rs Node (parent, rank), flattened [C-equiv].
// ════════════════════════════════════════════════════════════════════════════
#[derive(Clone, Copy)]
pub struct EquivNode {
    pub parent: u32,
    pub rank: u32,
}

// DefEqEntry — one def_eq_cache row [C-cache]. (a,b) stored in canonical
// smaller-hash-first order by DefEqCacheKey::new; tm = transparency tag; v =
// verdict (0/1). Scanned with the REAL DefEqCacheKey PartialEq.
#[derive(Clone)]
pub struct DefEqEntry {
    pub a: Expr,
    pub b: Expr,
    pub tm: u64,
    pub v: u64,
}

// ════════════════════════════════════════════════════════════════════════════
// CacheCtx — the mutable TypeChecker cache state, threaded &mut (production:
// the RefCell<SlidingCache*> fields). Flattened per [C-cache]/[C-equiv]/[C-branch].
// ════════════════════════════════════════════════════════════════════════════
pub struct CacheCtx {
    // def_eq_cache (tc/mod.rs:370).
    pub cache: Vec<DefEqEntry>,
    pub cache_hits: u64, // observable: def_eq cache reads that HIT.
    pub cache_miss: u64,
    pub recomputes: u64, // the #1773 guard fell through (out_of_context) and recomputed.
    // equiv_manager (tc/mod.rs:514).
    pub equiv_nodes: Vec<EquivNode>,
    pub equiv_keys: Vec<Expr>,
    pub equiv_hits: u64, // observable: equiv consults that returned true.
    // branch_sharing verified_pairs (branch_sharing.rs:37).
    pub verified: Vec<(Expr, Expr)>,
}

pub fn cachectx_new() -> CacheCtx {
    CacheCtx {
        cache: Vec::new(),
        cache_hits: 0,
        cache_miss: 0,
        recomputes: 0,
        equiv_nodes: Vec::new(),
        equiv_keys: Vec::new(),
        equiv_hits: 0,
        verified: Vec::new(),
    }
}

fn umin(a: u64, b: u64) -> u64 {
    if a <= b { a } else { b }
}
fn umax(a: u64, b: u64) -> u64 {
    if a >= b { a } else { b }
}

// ─────────────── DefEqCacheKey routing [C-cache] ─────────────────────────────
// DefEqCacheKey::new (:113-132): canonical ordering — smaller cached hash in `a`.
// Returns the (a, b) pair in canonical order. (transparency carried separately.)
fn defeqkey_canonical(a: &Expr, b: &Expr) -> (Expr, Expr) {
    let a_hash = a.hash_cached();
    let b_hash = b.hash_cached();
    if a_hash <= b_hash {
        (a.clone(), b.clone())
    } else {
        (b.clone(), a.clone())
    }
}
// DefEqCacheKey PartialEq (:137-141): unordered {a,b} + transparency.
fn defeqkey_eq(qa: &Expr, qb: &Expr, qtm: u64, ea: &Expr, eb: &Expr, etm: u64) -> bool {
    qtm == etm
        && ((expr_syntactic_eq(qa, ea) && expr_syntactic_eq(qb, eb))
            || (expr_syntactic_eq(qa, eb) && expr_syntactic_eq(qb, ea)))
}
// SlidingCache::get modeled as a scan; the commutative min/max hash Hash
// (:157-164) is subsumed by the scan (a linear probe visits every bucket).
fn cache_get(cx: &CacheCtx, qa: &Expr, qb: &Expr, qtm: u64) -> Option<u64> {
    let mut i = 0usize;
    let n = cx.cache.len();
    while i < n {
        // hash pre-filter using the commutative min/max key hash (:161-162).
        let e = &cx.cache[i];
        let qmin = umin(qa.hash_cached(), qb.hash_cached());
        let qmax = umax(qa.hash_cached(), qb.hash_cached());
        let emin = umin(e.a.hash_cached(), e.b.hash_cached());
        let emax = umax(e.a.hash_cached(), e.b.hash_cached());
        if qmin == emin && qmax == emax && defeqkey_eq(qa, qb, qtm, &e.a, &e.b, e.tm) {
            return Some(e.v);
        }
        i += 1;
    }
    None
}
fn cache_insert(cx: &mut CacheCtx, qa: &Expr, qb: &Expr, qtm: u64, v: u64) {
    let (ka, kb) = defeqkey_canonical(qa, qb);
    cx.cache.push(DefEqEntry {
        a: ka,
        b: kb,
        tm: qtm,
        v,
    });
}

// ════════════════════════════════════════════════════════════════════════════
// EquivManager — union-find (equiv_manager.rs), flattened [C-equiv].
// ════════════════════════════════════════════════════════════════════════════
// get_or_insert_node (:131-138): scan to_node (equiv_keys) structurally; else
// mk_node.
fn equiv_get_or_insert(cx: &mut CacheCtx, e: &Expr) -> u32 {
    let mut i = 0usize;
    let n = cx.equiv_keys.len();
    while i < n {
        if expr_syntactic_eq(&cx.equiv_keys[i], e) {
            return i as u32;
        }
        i += 1;
    }
    let r = cx.equiv_nodes.len() as u32;
    cx.equiv_nodes.push(EquivNode { parent: r, rank: 0 });
    cx.equiv_keys.push(e.clone());
    r
}
// find (:97-110) — path compression.
fn equiv_find(cx: &mut CacheCtx, n0: u32) -> u32 {
    let mut root = n0;
    while cx.equiv_nodes[root as usize].parent != root {
        root = cx.equiv_nodes[root as usize].parent;
    }
    let mut n = n0;
    while cx.equiv_nodes[n as usize].parent != root {
        let next = cx.equiv_nodes[n as usize].parent;
        cx.equiv_nodes[n as usize].parent = root;
        n = next;
    }
    root
}
// merge (:113-128) — union by rank.
fn equiv_merge(cx: &mut CacheCtx, n1: u32, n2: u32) {
    let r1 = equiv_find(cx, n1);
    let r2 = equiv_find(cx, n2);
    if r1 != r2 {
        let rank1 = cx.equiv_nodes[r1 as usize].rank;
        let rank2 = cx.equiv_nodes[r2 as usize].rank;
        if rank1 < rank2 {
            cx.equiv_nodes[r1 as usize].parent = r2;
        } else if rank1 > rank2 {
            cx.equiv_nodes[r2 as usize].parent = r1;
        } else {
            cx.equiv_nodes[r2 as usize].parent = r1;
            cx.equiv_nodes[r1 as usize].rank += 1;
        }
    }
}
// add_equiv (:67-71) — record a proven equality.
fn equiv_add(cx: &mut CacheCtx, a: &Expr, b: &Expr) {
    let r1 = equiv_get_or_insert(cx, a);
    let r2 = equiv_get_or_insert(cx, b);
    equiv_merge(cx, r1, r2);
}
// is_equiv_core (:142-348): union-find lookup (roots equal) + hash pre-filter +
// structural fallback by kind with merge-on-success. Returns true if known /
// provably-equal. (BVar fast path :147-149 folded in.)
fn equiv_is_equiv(cx: &mut CacheCtx, a: &Expr, b: &Expr) -> bool {
    // BVar fast path (:147-149).
    if let (ExprKind::BVar(i), ExprKind::BVar(j)) = (&a.kind, &b.kind) {
        return i == j;
    }
    // step 3: existing union-find knowledge wins even when hashes differ.
    let ta = equiv_lookup(cx, a);
    let tb = equiv_lookup(cx, b);
    let tracked = match (ta, tb) {
        (Some(na), Some(nb)) => {
            let r1 = equiv_find(cx, na);
            let r2 = equiv_find(cx, nb);
            if r1 == r2 {
                return true;
            }
            Some((r1, r2))
        }
        _ => None,
    };
    // step 4: hash pre-filter.
    if a.hash_cached() != b.hash_cached() {
        return false;
    }
    // step 5: union-find lookup (reuse tracked roots or insert).
    let (r1, r2) = match tracked {
        Some(roots) => roots,
        None => {
            let n1 = equiv_get_or_insert(cx, a);
            let n2 = equiv_get_or_insert(cx, b);
            (equiv_find(cx, n1), equiv_find(cx, n2))
        }
    };
    if r1 == r2 {
        return true;
    }
    // step 6: structural comparison fallback by kind.
    let result = match (&a.kind, &b.kind) {
        (ExprKind::FVar(id1), ExprKind::FVar(id2)) => id1.0 == id2.0,
        (ExprKind::Sort(l1), ExprKind::Sort(l2)) => l1 == l2,
        (ExprKind::Const(n1), ExprKind::Const(n2)) => name_eq(n1, n2),
        (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
        (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
            equiv_is_equiv(cx, f1, f2) && equiv_is_equiv(cx, a1, a2)
        }
        (ExprKind::Lam(t1, b1), ExprKind::Lam(t2, b2)) => {
            equiv_is_equiv(cx, t1, t2) && equiv_is_equiv(cx, b1, b2)
        }
        (ExprKind::Pi(t1, b1), ExprKind::Pi(t2, b2)) => {
            equiv_is_equiv(cx, t1, t2) && equiv_is_equiv(cx, b1, b2)
        }
        (ExprKind::Let(t1, v1, b1), ExprKind::Let(t2, v2, b2)) => {
            equiv_is_equiv(cx, t1, t2) && equiv_is_equiv(cx, v1, v2) && equiv_is_equiv(cx, b1, b2)
        }
        (ExprKind::MData(e1), ExprKind::MData(e2)) => equiv_is_equiv(cx, e1, e2),
        _ => false,
    };
    if result {
        equiv_merge(cx, r1, r2);
    }
    result
}
// to_node.get(e) — scan without inserting.
fn equiv_lookup(cx: &CacheCtx, e: &Expr) -> Option<u32> {
    let mut i = 0usize;
    let n = cx.equiv_keys.len();
    while i < n {
        if expr_syntactic_eq(&cx.equiv_keys[i], e) {
            return Some(i as u32);
        }
        i += 1;
    }
    None
}

// ════════════════════════════════════════════════════════════════════════════
// branch_sharing verified_pairs [C-branch] — canonical smaller-hash key,
// record-on-success (branch_sharing.rs:67-89).
// ════════════════════════════════════════════════════════════════════════════
fn is_verified_pair(cx: &CacheCtx, a: &Expr, b: &Expr) -> bool {
    let (ka, kb) = if a.hash_cached() <= b.hash_cached() {
        (a, b)
    } else {
        (b, a)
    };
    let mut i = 0usize;
    let n = cx.verified.len();
    while i < n {
        let e = &cx.verified[i];
        if expr_syntactic_eq(&e.0, ka) && expr_syntactic_eq(&e.1, kb) {
            return true;
        }
        i += 1;
    }
    false
}
fn record_verified_pair(cx: &mut CacheCtx, a: &Expr, b: &Expr) {
    let (ka, kb) = if a.hash_cached() <= b.hash_cached() {
        (a.clone(), b.clone())
    } else {
        (b.clone(), a.clone())
    };
    cx.verified.push((ka, kb));
}

// ════════════════════════════════════════════════════════════════════════════
// The Verifier + engine.
// ════════════════════════════════════════════════════════════════════════════
pub struct Verifier {
    pub cache_mode: u64,   // 0 NOCACHE, 1 AWARE (guard), 2 BLIND (guard removed).
    pub equiv_off: bool,   // skip the equiv consult (isolate the def_eq cache).
    pub transparency: u64, // the TransparencyMode tag in the key (#1636).
}

impl Verifier {
    // ── env model [B-env]: dfn := foo (delta witness); Reducibility Regular(1)
    // for the def, Irreducible for bodyless consts. ──
    fn unfold_definition_model(&self, name: &Name) -> Option<Expr> {
        if name_eq(name, &nm_dfn()) {
            Some(Expr::cnst(nm_foo()))
        } else {
            None
        }
    }
    fn get_reducibility(&self, name: &Name) -> Reducibility {
        if name_eq(name, &nm_dfn()) {
            Reducibility::Regular(1)
        } else {
            Reducibility::Irreducible
        }
    }
    // env.get_recursor — only Bool.rec is a recursor (MajorAfterMotive; 1 motive,
    // 2 minors, 0 params/indices).
    fn get_recursor(&self, name: &Name) -> Option<RecInfo> {
        if name_eq(name, &bool_rec_name()) {
            Some(RecInfo {
                num_params: 0,
                num_motives: 1,
                num_indices: 0,
                num_minors: 2,
            })
        } else {
            None
        }
    }
    // registry-empty reducers (verified R13).
    fn reduce_nat(&self, _e: &Expr) -> Option<Expr> {
        None
    }
    fn reduce_native(&self, _e: &Expr) -> Option<Expr> {
        None
    }
    fn try_iota_reduction(&self, _e: &Expr) -> Option<Expr> {
        None
    }

    // ── whnf_core_no_delta (whnf.rs:341-465): beta / Let-zeta / FVar-zeta (via
    // ctx) / MData; Const STUCK (no delta). The FVar-zeta arm (:455-461) is the
    // context-aware reduction the #1773 guard scenario turns on. ──
    pub fn whnf_core_no_delta(&self, e: &Expr, ctx: &LocalContext) -> Expr {
        match &e.kind {
            ExprKind::App(f, a) => {
                let f0 = e.get_app_fn();
                if let ExprKind::Const(_) = &f0.kind {
                    if let Some(reduced) = self.reduce_nat(e) {
                        return self.whnf_core_no_delta(&reduced, ctx);
                    }
                    if let Some(reduced) = self.reduce_native(e) {
                        return self.whnf_core_no_delta(&reduced, ctx);
                    }
                }
                let f_whnf = self.whnf_core_no_delta(f, ctx);
                match &f_whnf.kind {
                    ExprKind::Lam(_, body) => {
                        let reduced = body.instantiate(a);
                        self.whnf_core_no_delta(&reduced, ctx)
                    }
                    _ => {
                        let app = Expr::from_kind(ExprKind::App(Arc::new(f_whnf), a.clone()));
                        if let Some(reduced) = self.try_iota_reduction(&app) {
                            return self.whnf_core_no_delta(&reduced, ctx);
                        }
                        if let Some(reduced) = self.reduce_nat(&app) {
                            return self.whnf_core_no_delta(&reduced, ctx);
                        }
                        app
                    }
                }
            }
            // Let zeta (:432-434).
            ExprKind::Let(_, val, body) => {
                let reduced = body.instantiate(val);
                self.whnf_core_no_delta(&reduced, ctx)
            }
            // Const STUCK in NoDelta (:439-442).
            ExprKind::Const(_) => e.clone(),
            // FVar zeta (:455-461) — context value lookup; missing/plain stuck.
            ExprKind::FVar(id) => {
                let val_opt: Option<Expr> = match ctx.get(*id) {
                    Some(d) => d.value,
                    None => None,
                };
                match val_opt {
                    Some(val) => self.whnf_core_no_delta(&val, ctx),
                    None => e.clone(),
                }
            }
            // MData strips (:465).
            ExprKind::MData(inner) => self.whnf_core_no_delta(inner, ctx),
            _ => e.clone(),
        }
    }

    // ════════════════════════════════════════════════════════════════════════
    // is_def_eq / is_def_eq_impl / is_def_eq_inner — THE CACHE ROUTING.
    // ════════════════════════════════════════════════════════════════════════
    // is_def_eq (:176-189) — public entry; post-result add_equiv on TRUE.
    pub fn is_def_eq(&self, a: &Expr, b: &Expr, ctx: &LocalContext, cx: &mut CacheCtx) -> bool {
        let result = self.is_def_eq_impl(a, b, ctx, cx);
        // Record positive results in the equiv_manager (:183-187).
        if result && !self.equiv_off {
            equiv_add(cx, a, b);
        }
        result
    }
    // is_def_eq_impl (:195-197) — the recursive entry.
    pub fn is_def_eq_impl(
        &self,
        a: &Expr,
        b: &Expr,
        ctx: &LocalContext,
        cx: &mut CacheCtx,
    ) -> bool {
        self.is_def_eq_inner(a, b, ctx, cx)
    }
    // is_def_eq_inner (:200-270) — [C-ptreq] ptr::eq omitted; equiv consult
    // (:210); structural fast-path (:218); DefEqCacheKey routing (:225-267) with
    // the #1773 out_of_context guard (:250-255).
    fn is_def_eq_inner(&self, a: &Expr, b: &Expr, ctx: &LocalContext, cx: &mut CacheCtx) -> bool {
        // Check equiv_manager for cross-call accumulated knowledge (:210).
        if !self.equiv_off {
            if equiv_is_equiv(cx, a, b) {
                cx.equiv_hits += 1;
                return true;
            }
        }
        // Fast-path structural equality (:218).
        if expr_syntactic_eq(a, b) {
            return true;
        }
        // NOCACHE baseline (the R13/R12 config): no def_eq cache at all.
        if self.cache_mode == 0 {
            return self.is_def_eq_core(a, b, ctx, cx);
        }
        // Check def_eq cache (:225-256). DefEqCacheKey::new picks the canonical
        // ordering; the scan applies the unordered structural key eq.
        let cached_opt = cache_get(cx, a, b, self.transparency);
        match cached_opt {
            Some(cached) => {
                cx.cache_hits += 1;
                if self.cache_mode == 1 {
                    // AWARE — the #1773/#38 guard (:250-255). A negative is only
                    // trustworthy if BOTH sides are fully in-context; a cached
                    // POSITIVE stays trusted (def-eq is monotone).
                    let cached_bool = cached != 0;
                    let out_of_context = !cached_bool
                        && ((a.has_fvar_quick() && !self.all_fvars_in_context(a, ctx))
                            || (b.has_fvar_quick() && !self.all_fvars_in_context(b, ctx)));
                    if !out_of_context {
                        return cached_bool;
                    }
                    // guard tripped: fall through and RECOMPUTE (never trust the
                    // stale negative, never panic).
                    cx.recomputes += 1;
                } else {
                    // BLIND (cache_mode == 2) — guard REMOVED: trust the cached
                    // verdict unconditionally (the UNSOUND control).
                    return cached != 0;
                }
            }
            None => {
                cx.cache_miss += 1;
            }
        }
        // Compute the result (:259).
        let result = self.is_def_eq_core(a, b, ctx, cx);
        // Cache the result under the canonical key (:263-267).
        cache_insert(cx, a, b, self.transparency, if result { 1 } else { 0 });
        result
    }

    // all_fvars_in_context (:535-603) — VERBATIM recursive in-context walk (the
    // reachable ExprKinds; cubical/ZFC arms absent [B-proj]).
    fn all_fvars_in_context(&self, e: &Expr, ctx: &LocalContext) -> bool {
        match &e.kind {
            ExprKind::FVar(id) => ctx.get(*id).is_some(),
            ExprKind::App(f, a) => {
                self.all_fvars_in_context(f, ctx) && self.all_fvars_in_context(a, ctx)
            }
            ExprKind::Lam(ty, body) | ExprKind::Pi(ty, body) => {
                self.all_fvars_in_context(ty, ctx) && self.all_fvars_in_context(body, ctx)
            }
            ExprKind::Let(ty, val, body) => {
                self.all_fvars_in_context(ty, ctx)
                    && self.all_fvars_in_context(val, ctx)
                    && self.all_fvars_in_context(body, ctx)
            }
            ExprKind::MData(inner) => self.all_fvars_in_context(inner, ctx),
            // Leaf nodes without FVars.
            ExprKind::BVar(_) | ExprKind::Sort(_) | ExprKind::Const(_) | ExprKind::Lit(_) => true,
        }
    }

    // is_def_eq_core (:273-481) — quick, P1 whnf + re-quick, branch-sharing hook
    // (#3402), P2 lazy delta, P3 Const/FVar, P6 structural. (proof-irrel /
    // struct-eta / string-lit / unit-like / Bool.true reflection out of scope
    // here, verified R9..R12 — inert on these scenarios [B-engine].)
    fn is_def_eq_core(&self, a: &Expr, b: &Expr, ctx: &LocalContext, cx: &mut CacheCtx) -> bool {
        match self.quick_is_def_eq(a, b, cx) {
            Some(v) => return v,
            None => {}
        }
        // P1 — no-delta cheap whnf both sides.
        let t = self.whnf_core_no_delta(a, ctx);
        let s = self.whnf_core_no_delta(b, ctx);
        if !expr_syntactic_eq(&t, a) || !expr_syntactic_eq(&s, b) {
            if expr_syntactic_eq(&t, &s) {
                return true;
            }
            match self.quick_is_def_eq(&t, &s, cx) {
                Some(v) => return v,
                None => {}
            }
        }
        // Branch-sharing recursor congruence (#3402), fires before lazy delta.
        match self.try_branch_sharing_def_eq(&t, &s, ctx, cx) {
            Some(v) => return v,
            None => {}
        }
        // P2 — lazy delta.
        match self.lazy_delta_reduction(&t, &s, ctx, cx) {
            Ok(v) => return v,
            Err((t2, s2)) => {
                // P3 — Const/FVar head after delta.
                if let (ExprKind::Const(n1), ExprKind::Const(n2)) = (&t2.kind, &s2.kind) {
                    if name_eq(n1, n2) {
                        return true;
                    }
                }
                if let (ExprKind::FVar(i), ExprKind::FVar(j)) = (&t2.kind, &s2.kind) {
                    if i.0 == j.0 {
                        return true;
                    }
                }
                // P6 — structural congruence.
                self.is_def_eq_structural(&t2, &s2, ctx, cx)
            }
        }
    }

    // quick_is_def_eq (:493-525) — equiv consult (:495) + Sort/Lit reachable arms.
    fn quick_is_def_eq(&self, a: &Expr, b: &Expr, cx: &mut CacheCtx) -> Option<bool> {
        if !self.equiv_off {
            if equiv_is_equiv(cx, a, b) {
                cx.equiv_hits += 1;
                return Some(true);
            }
        }
        match (&a.kind, &b.kind) {
            (ExprKind::Sort(x), ExprKind::Sort(y)) => Some(x == y),
            (ExprKind::Lit(x), ExprKind::Lit(y)) => Some(x == y),
            _ => None,
        }
    }

    // ── lazy delta (def_eq/delta.rs) — delta step with height ordering; the
    // registry-empty nat/native/monad/offset hooks return None [B-engine]. ──
    fn get_delta_const(&self, e: &Expr) -> Option<(Name, Reducibility)> {
        let head = e.get_app_fn();
        if let ExprKind::Const(name) = &head.kind {
            if self.unfold_definition_model(name).is_some() {
                let red = self.get_reducibility(name);
                match red {
                    Reducibility::Opaque => None,
                    _ => Some((*name, red)),
                }
            } else {
                None
            }
        } else {
            None
        }
    }
    fn try_unfold_const_in_place(&self, e: &mut Expr, name: &Name) -> bool {
        match self.unfold_definition_model(name) {
            Some(body) => {
                *e = self.replace_head(e, &body);
                true
            }
            None => false,
        }
    }
    fn replace_head(&self, e: &Expr, new_head: &Expr) -> Expr {
        match &e.kind {
            ExprKind::App(f, a) => {
                let nf = self.replace_head(f, new_head);
                Expr::from_kind(ExprKind::App(Arc::new(nf), a.clone()))
            }
            ExprKind::Const(_) => new_head.clone(),
            _ => e.clone(),
        }
    }
    pub fn lazy_delta_reduction(
        &self,
        a: &Expr,
        b: &Expr,
        ctx: &LocalContext,
        cx: &mut CacheCtx,
    ) -> Result<bool, (Expr, Expr)> {
        let max_iters: u32 = 10_000;
        let mut t = a.clone();
        let mut s = b.clone();
        let mut iters = 0u32;
        loop {
            iters += 1;
            if iters > max_iters {
                return Ok(false); // #1773 conservative cap.
            }
            match self.lazy_delta_step(&mut t, &mut s, ctx, cx) {
                LdStatus::Continue => {}
                LdStatus::DefEqual => return Ok(true),
                LdStatus::DefUnknown => return Err((t, s)),
                LdStatus::DefDiff => return Ok(false),
            }
        }
    }
    fn lazy_delta_step(
        &self,
        t: &mut Expr,
        s: &mut Expr,
        ctx: &LocalContext,
        cx: &mut CacheCtx,
    ) -> LdStatus {
        let dt = self.get_delta_const(t);
        let ds = self.get_delta_const(s);
        let status = match (dt, ds) {
            (Some((tn, tr)), Some((sn, sr))) => {
                let ord = tr.compare(&sr);
                if ord < 0 {
                    if self.try_unfold_const_in_place(t, &tn)
                        || self.try_unfold_const_in_place(s, &sn)
                    {
                        LdStatus::Continue
                    } else {
                        LdStatus::DefUnknown
                    }
                } else if ord > 0 {
                    if self.try_unfold_const_in_place(s, &sn)
                        || self.try_unfold_const_in_place(t, &tn)
                    {
                        LdStatus::Continue
                    } else {
                        LdStatus::DefUnknown
                    }
                } else {
                    if name_eq(&tn, &sn) && tr.is_regular() {
                        if self.is_def_eq_args_only(t, s, ctx, cx) {
                            return LdStatus::DefEqual;
                        }
                    }
                    let tc = self.try_unfold_const_in_place(t, &tn);
                    let sc = self.try_unfold_const_in_place(s, &sn);
                    if tc || sc {
                        LdStatus::Continue
                    } else {
                        LdStatus::DefUnknown
                    }
                }
            }
            (Some((tn, _tr)), None) => {
                if self.try_unfold_const_in_place(t, &tn) {
                    LdStatus::Continue
                } else {
                    LdStatus::DefUnknown
                }
            }
            (None, Some((sn, _sr))) => {
                if self.try_unfold_const_in_place(s, &sn) {
                    LdStatus::Continue
                } else {
                    LdStatus::DefUnknown
                }
            }
            (None, None) => LdStatus::DefUnknown,
        };
        match status {
            LdStatus::Continue => self.finish_delta_step(t, s, cx),
            _ => status,
        }
    }
    fn finish_delta_step(&self, t: &Expr, s: &Expr, cx: &mut CacheCtx) -> LdStatus {
        if expr_syntactic_eq(t, s) {
            return LdStatus::DefEqual;
        }
        match self.quick_is_def_eq(t, s, cx) {
            Some(true) => LdStatus::DefEqual,
            Some(false) => LdStatus::DefDiff,
            None => LdStatus::Continue,
        }
    }
    fn is_def_eq_args_only(
        &self,
        t: &Expr,
        s: &Expr,
        ctx: &LocalContext,
        cx: &mut CacheCtx,
    ) -> bool {
        match (&t.kind, &s.kind) {
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                self.is_def_eq_args_only(f1, f2, ctx, cx) && self.is_def_eq_impl(a1, a2, ctx, cx)
            }
            (ExprKind::Const(_), ExprKind::Const(_)) => true,
            _ => expr_syntactic_eq(t, s),
        }
    }

    // P6 structural congruence.
    fn is_def_eq_structural(
        &self,
        a: &Expr,
        b: &Expr,
        ctx: &LocalContext,
        cx: &mut CacheCtx,
    ) -> bool {
        match (&a.kind, &b.kind) {
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                self.is_def_eq_impl(f1, f2, ctx, cx) && self.is_def_eq_impl(a1, a2, ctx, cx)
            }
            (ExprKind::Lam(t1, b1), ExprKind::Lam(t2, b2)) => {
                self.is_def_eq_impl(t1, t2, ctx, cx) && self.is_def_eq_impl(b1, b2, ctx, cx)
            }
            (ExprKind::Pi(t1, b1), ExprKind::Pi(t2, b2)) => {
                self.is_def_eq_impl(t1, t2, ctx, cx) && self.is_def_eq_impl(b1, b2, ctx, cx)
            }
            (ExprKind::Sort(x), ExprKind::Sort(y)) => x == y,
            (ExprKind::Const(x), ExprKind::Const(y)) => name_eq(x, y),
            (ExprKind::FVar(x), ExprKind::FVar(y)) => x.0 == y.0,
            (ExprKind::BVar(x), ExprKind::BVar(y)) => x == y,
            (ExprKind::Lit(x), ExprKind::Lit(y)) => x == y,
            (ExprKind::MData(e1), _) => self.is_def_eq_impl(e1, b, ctx, cx),
            (_, ExprKind::MData(e2)) => self.is_def_eq_impl(a, e2, ctx, cx),
            _ => false,
        }
    }

    // ════════════════════════════════════════════════════════════════════════
    // branch_sharing (#3402) — try_branch_sharing_def_eq + branch_sharing_compare.
    // ════════════════════════════════════════════════════════════════════════
    // branch_sharing_compare (:283-311) — verified-pair O(1) check + [C-bs-whnf]
    // direct whnf (the prefix memo modeled out) + record-on-success.
    fn branch_sharing_compare(
        &self,
        a: &Expr,
        b: &Expr,
        ctx: &LocalContext,
        cx: &mut CacheCtx,
    ) -> bool {
        if is_verified_pair(cx, a, b) {
            return true;
        }
        let a_n = self.whnf_core_no_delta(a, ctx);
        let b_n = self.whnf_core_no_delta(b, ctx);
        let result = if expr_syntactic_eq(&a_n, &b_n) {
            true
        } else {
            self.is_def_eq_impl(&a_n, &b_n, ctx, cx)
        };
        if result {
            record_verified_pair(cx, a, b);
        }
        result
    }
    // as_recursor_app (:387-403) — head Const is a recursor with >= required args.
    fn recursor_args_before_major(&self, r: &RecInfo) -> usize {
        // MajorAfterMotive: params + motives + indices.
        r.num_params + r.num_motives + r.num_indices
    }
    fn recursor_required_args(&self, r: &RecInfo) -> usize {
        // MajorAfterMotive: args_before_major + 1 + num_minors.
        self.recursor_args_before_major(r) + 1 + r.num_minors
    }
    // try_branch_sharing_def_eq (:442-497) — recursor congruence; NEVER
    // Some(false) (only Some(true) / None), so it can only ADD completeness.
    fn try_branch_sharing_def_eq(
        &self,
        a: &Expr,
        b: &Expr,
        ctx: &LocalContext,
        cx: &mut CacheCtx,
    ) -> Option<bool> {
        let a_head = a.get_app_fn();
        let b_head = b.get_app_fn();
        let a_name = match &a_head.kind {
            ExprKind::Const(n) => *n,
            _ => return None,
        };
        let b_name = match &b_head.kind {
            ExprKind::Const(n) => *n,
            _ => return None,
        };
        let ra = match self.get_recursor(&a_name) {
            Some(r) => r,
            None => return None,
        };
        let rb = match self.get_recursor(&b_name) {
            Some(r) => r,
            None => return None,
        };
        let a_args = a.get_app_args();
        let b_args = b.get_app_args();
        if a_args.len() < self.recursor_required_args(&ra) {
            return None;
        }
        if b_args.len() < self.recursor_required_args(&rb) {
            return None;
        }
        if !name_eq(&a_name, &b_name) {
            return None;
        }
        if a_args.len() != b_args.len() {
            return None;
        }
        // [B-levels] levels are empty on both sides (Const monomorphic) — trivially equal.
        let motives_end = ra.num_params + ra.num_motives;
        // shared prefix (params + motives).
        if !self.compare_arg_range(&a_args, &b_args, 0, motives_end, ctx, cx) {
            return None;
        }
        // indices (MajorAfterMotive: motives_end .. + num_indices).
        if !self.compare_arg_range(
            &a_args,
            &b_args,
            motives_end,
            motives_end + ra.num_indices,
            ctx,
            cx,
        ) {
            return None;
        }
        // major (index args_before_major).
        let major_idx = self.recursor_args_before_major(&ra);
        if !self.branch_sharing_compare(&a_args[major_idx], &b_args[major_idx], ctx, cx) {
            return None;
        }
        // minors (major_idx+1 .. + num_minors).
        let minors_start = major_idx + 1;
        if !self.compare_arg_range(
            &a_args,
            &b_args,
            minors_start,
            minors_start + ra.num_minors,
            ctx,
            cx,
        ) {
            return None;
        }
        // extras (minors_end .. len).
        if !self.compare_arg_range(
            &a_args,
            &b_args,
            minors_start + ra.num_minors,
            a_args.len(),
            ctx,
            cx,
        ) {
            return None;
        }
        Some(true)
    }
    fn compare_arg_range(
        &self,
        a_args: &Vec<Expr>,
        b_args: &Vec<Expr>,
        lo: usize,
        hi: usize,
        ctx: &LocalContext,
        cx: &mut CacheCtx,
    ) -> bool {
        let mut i = lo;
        while i < hi {
            if !self.branch_sharing_compare(&a_args[i], &b_args[i], ctx, cx) {
                return false;
            }
            i += 1;
        }
        true
    }
}

enum LdStatus {
    Continue,
    DefEqual,
    DefUnknown,
    DefDiff,
}

// ════════════════════════════════════════════════════════════════════════════
// ROOTS — one mono entry point that dispatches every scenario. idx layout:
//   cat = idx >> 16 ; lo = idx & 0xffff.
// Return is a packed u64 (per-category bit layout documented at each arm and
// mirrored in the e2e test).
// ════════════════════════════════════════════════════════════════════════════
fn bit(c: bool) -> u64 {
    if c { 1 } else { 0 }
}
fn sort0() -> Expr {
    Expr::sort(0)
}

// Build the (a,b) pair for the transparency / equiv / poison scenarios (context-
// free — no fvars).
fn build_simple_pair(sc: u64) -> (Expr, Expr) {
    if sc == 0 {
        // dfn =?= bar : NEGATIVE (dfn delta-> foo; foo != bar). A guard-free
        // negative (no fvars) — the warm run hits the def_eq cache.
        (Expr::cnst(nm_dfn()), Expr::cnst(nm_bar()))
    } else if sc == 1 {
        // dfn =?= foo : POSITIVE via delta.
        (Expr::cnst(nm_dfn()), Expr::cnst(nm_foo()))
    } else if sc == 2 {
        // g dfn =?= g foo : POSITIVE via App congruence over delta.
        (
            Expr::app(Expr::cnst(nm_g()), Expr::cnst(nm_dfn())),
            Expr::app(Expr::cnst(nm_g()), Expr::cnst(nm_foo())),
        )
    } else {
        // foo =?= bar : NEGATIVE.
        (Expr::cnst(nm_foo()), Expr::cnst(nm_bar()))
    }
}

// A Bool.rec application: Bool.rec motive major minor0 minor1  (MajorAfterMotive).
fn bool_rec_app(minor0: Expr, minor1: Expr) -> Expr {
    let m = Expr::cnst(nm_motive());
    let maj = Expr::cnst(nm_maj());
    // App spine: (((Bool.rec m) maj) minor0) minor1.
    let e0 = Expr::app(Expr::cnst(bool_rec_name()), m);
    let e1 = Expr::app(e0, maj);
    let e2 = Expr::app(e1, minor0);
    Expr::app(e2, minor1)
}

#[cfg_attr(not(test), no_mangle)]
pub extern "C" fn defeq_cache_root(idx: u64) -> u64 {
    let cat = idx >> 16;
    let lo = idx & 0xffff;
    if cat == 0 {
        run_transparency(lo)
    } else if cat == 1 {
        run_guard(lo)
    } else if cat == 2 {
        run_equiv(lo)
    } else if cat == 3 {
        run_branch(lo)
    } else if cat == 4 {
        run_poison_cache(lo)
    } else if cat == 5 {
        run_meta_probe(lo)
    } else {
        0
    }
}

// cat 0 — TRANSPARENCY. lo selects (scenario, equiv_off):
//   0 = negative pair (dfn=?=bar), equiv on   — warm hits the DEF_EQ cache.
//   1 = positive pair (dfn=?=foo), equiv OFF  — warm hits the DEF_EQ cache.
//   2 = positive pair (dfn=?=foo), equiv ON   — warm hits the EQUIV manager.
//   3 = positive App-congruence (g dfn=?=g foo), equiv OFF.
// Returns: bit0 cold verdict, bit1 warm verdict, bit2 cold==warm,
//   bit3 def_eq-cache hit advanced, bit4 equiv hit advanced.
fn run_transparency(lo: u64) -> u64 {
    let (sc, equiv_off) = if lo == 0 {
        (0u64, false)
    } else if lo == 1 {
        (1u64, true)
    } else if lo == 2 {
        (1u64, false)
    } else {
        (2u64, true)
    };
    let v = Verifier {
        cache_mode: 1,
        equiv_off,
        transparency: 0,
    };
    let ctx = LocalContext::new();
    let mut cx = cachectx_new();
    let (a, b) = build_simple_pair(sc);
    let cold = v.is_def_eq(&a, &b, &ctx, &mut cx);
    let ch0 = cx.cache_hits;
    let eh0 = cx.equiv_hits;
    let warm = v.is_def_eq(&a, &b, &ctx, &mut cx);
    let cache_adv = cx.cache_hits > ch0;
    let equiv_adv = cx.equiv_hits > eh0;
    bit(cold)
        | (bit(warm) << 1)
        | (bit(cold == warm) << 2)
        | (bit(cache_adv) << 3)
        | (bit(equiv_adv) << 4)
}

// cat 1 — THE GUARD (centerpiece). lo = cache_mode (0 NOCACHE, 1 AWARE, 2 BLIND).
// Scenario: a = (λ_:Sort0. FVar y) (FVar x) ; b = foo. The beta DISCARDS x, so
// the verdict depends only on y. Context A: x present (plain), y let-bound to
// bar -> a whnf's to bar != foo -> NEGATIVE (cached). Then the leak: pop x (out
// of the later context; cache NOT cleared) and refine y := foo. Context B: a
// whnf's to foo == foo -> the CORRECT verdict is ACCEPT.
//   AWARE: x out of ctx B trips all_fvars_in_context -> recompute -> ACCEPT (SOUND).
//   BLIND: stale cache hit -> REJECT (UNSOUND).
//   NOCACHE: recompute both -> A reject, B accept (the ground truth).
// Returns: bit0 vA, bit1 vB, bit2 out_of_context tripped (recomputes>0),
//   bit3 cache hit happened in ctx B.
fn run_guard(mode: u64) -> u64 {
    let v = Verifier {
        cache_mode: mode,
        equiv_off: true,
        transparency: 0,
    };
    let mut ctx = LocalContext::new();
    let mut cx = cachectx_new();
    // Context A.
    let yid = ctx.push_let(nm_y(), sort0(), Expr::cnst(nm_bar())); // id 0, y := bar
    let xid = ctx.push(nm_x(), sort0()); // id 1, x plain
    let a = Expr::app(Expr::lam(sort0(), Expr::fvar(yid.0)), Expr::fvar(xid.0));
    let b = Expr::cnst(nm_foo());
    let va = v.is_def_eq(&a, &b, &ctx, &mut cx); // ctx A -> reject (caches negative)
    let ch_after_a = cx.cache_hits;
    // The #38 leak: pop x (out of the later context), refine y := foo. The
    // def_eq cache is NOT cleared (models the tactic path bypassing
    // local_context_mut's clear).
    ctx.pop(); // x (id 1) gone
    ctx.set_value(yid, Expr::cnst(nm_foo())); // y := foo (elaborator refinement)
    let vb = v.is_def_eq(&a, &b, &ctx, &mut cx); // ctx B
    let cache_hit_in_b = cx.cache_hits > ch_after_a;
    bit(va) | (bit(vb) << 1) | (bit(cx.recomputes > 0) << 2) | (bit(cache_hit_in_b) << 3)
}

// cat 2 — EQUIV manager. lo:
//   0 = transparency: is_def_eq(dfn,foo) twice; 2nd short-circuits via the
//       union-find. Returns bit0 v1, bit1 v2, bit2 equiv hit advanced.
//   1 = POISON: pre-seed a WRONG equiv (foo == bar); is_def_eq(foo,bar) -> the
//       union-find returns true -> ACCEPT (WRONG). bit0 verdict.
//   2 = CLEAN: no seed; is_def_eq(foo,bar) -> REJECT. bit0 verdict.
fn run_equiv(lo: u64) -> u64 {
    if lo == 0 {
        let v = Verifier {
            cache_mode: 1,
            equiv_off: false,
            transparency: 0,
        };
        let ctx = LocalContext::new();
        let mut cx = cachectx_new();
        let a = Expr::cnst(nm_dfn());
        let b = Expr::cnst(nm_foo());
        let v1 = v.is_def_eq(&a, &b, &ctx, &mut cx); // accept via delta; add_equiv(dfn,foo)
        let eh0 = cx.equiv_hits;
        let v2 = v.is_def_eq(&a, &b, &ctx, &mut cx); // accept via union-find short-circuit
        let equiv_adv = cx.equiv_hits > eh0;
        bit(v1) | (bit(v2) << 1) | (bit(equiv_adv) << 2)
    } else {
        let v = Verifier {
            cache_mode: 1,
            equiv_off: false,
            transparency: 0,
        };
        let ctx = LocalContext::new();
        let mut cx = cachectx_new();
        let foo = Expr::cnst(nm_foo());
        let bar = Expr::cnst(nm_bar());
        if lo == 1 {
            // POISON: inject a WRONG proven-equality into the union-find.
            equiv_add(&mut cx, &foo, &bar);
        }
        let verdict = v.is_def_eq(&foo, &bar, &ctx, &mut cx);
        bit(verdict)
    }
}

// cat 3 — branch_sharing (#3402). lo:
//   0 = congruent accept: Bool.rec m maj dfn f  =?=  Bool.rec m maj foo f. The
//       minors differ syntactically (dfn vs foo) but are delta-equal; branch
//       sharing decides via branch_sharing_compare. bit0 verdict, bit1
//       verified_pairs advanced.
//   1 = CLEAN reject: Bool.rec m maj bar f =?= Bool.rec m maj baz f (bar!=baz,
//       not def-eq) -> REJECT. bit0 verdict.
//   2 = POISON: pre-record a WRONG verified-pair (bar,baz); the same recursor
//       pair now branch-shares to ACCEPT (WRONG). bit0 verdict.
fn run_branch(lo: u64) -> u64 {
    let v = Verifier {
        cache_mode: 1,
        equiv_off: true,
        transparency: 0,
    };
    let ctx = LocalContext::new();
    let mut cx = cachectx_new();
    let f = Expr::cnst(nm_g()); // a shared second minor
    if lo == 0 {
        let r1 = bool_rec_app(Expr::cnst(nm_dfn()), f.clone());
        let r2 = bool_rec_app(Expr::cnst(nm_foo()), f);
        let verdict = v.is_def_eq(&r1, &r2, &ctx, &mut cx);
        let vp_adv = cx.verified.len() > 0;
        bit(verdict) | (bit(vp_adv) << 1)
    } else {
        let bar = Expr::cnst(nm_bar());
        let baz = Expr::cnst(nm_baz());
        if lo == 2 {
            // POISON: record (bar,baz) as a verified pair despite bar != baz.
            record_verified_pair(&mut cx, &bar, &baz);
        }
        let r1 = bool_rec_app(bar, f.clone());
        let r2 = bool_rec_app(baz, f);
        let verdict = v.is_def_eq(&r1, &r2, &ctx, &mut cx);
        bit(verdict)
    }
}

// cat 4 — POISONED-CACHE-VALUE control. lo:
//   0 = clean: foo =?= bar -> REJECT. bit0 verdict.
//   1 = poison: inject a WRONG cache verdict {foo,bar}=true, then foo=?=bar ->
//       the cache VALUE is consulted -> ACCEPT (WRONG). bit0 verdict.
fn run_poison_cache(lo: u64) -> u64 {
    let v = Verifier {
        cache_mode: 1,
        equiv_off: true,
        transparency: 0,
    };
    let ctx = LocalContext::new();
    let mut cx = cachectx_new();
    let foo = Expr::cnst(nm_foo());
    let bar = Expr::cnst(nm_bar());
    if lo == 1 {
        cache_insert(&mut cx, &foo, &bar, 0, 1); // WRONG: {foo,bar} = true
    }
    let verdict = v.is_def_eq(&foo, &bar, &ctx, &mut cx);
    bit(verdict)
}

// cat 5 — META PROBE. Returns the ExprMeta.hash of a canonical constructed term
// (for the armed-golden FNV-corruption differential — value-preserving elsewhere,
// hash-diverging here).
fn run_meta_probe(lo: u64) -> u64 {
    let t = if lo == 0 {
        Expr::app(Expr::cnst(nm_g()), Expr::cnst(nm_foo()))
    } else {
        Expr::cnst(nm_dfn())
    };
    t.meta.hash
}
