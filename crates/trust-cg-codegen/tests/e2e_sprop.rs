// R15 — THE B5 SProp ARM: strict (definitional) proof irrelevance, native == JIT
// over Clean's SProp proof-irrelevance disjunct (tc/def_eq/proof_irrel.rs:86 —
// `matches!(ty_of_ty_whnf.kind(), ExprKind::SProp)`, the arm R9 recorded as
// "structurally absent (B5)") compiled through Trust (Rust -> MIR -> trust-ir
// -> trust-cg -> machine code).
//
// SOUNDNESS-CRITICAL: any two terms whose TYPE lives in SProp are def-eq
// unconditionally (definitional proof irrelevance). A wrong universe check that
// treats a NON-SProp type as SProp conflates distinct values (2 = 3) and proves
// False. The check must be sound in BOTH directions: ACCEPT distinct proofs of
// an SProp; REJECT distinct values of a non-SProp.
//
// THE ROUND SOUNDNESS PROOF (native == JIT, both ways):
//   * The AWARE (production) engine REJECTS `a =?= b : Foo` (distinct values of
//     a Type-level type). The OVER-EAGER control (universe check dropped)
//     ACCEPTS it — UNSOUND. The production universe check is EXACTLY what
//     prevents `2 = 3`. Both native and JIT agree on aware AND on blind.
//   * The POISON control (universe check inverted) REJECTS distinct proofs of
//     an SProp — the :86 disjunct is load-bearing — while leaving the Prop path
//     (:85) UNCHANGED (the two arms are independent code paths).
//   * The armed golden corruption flips the SProp discriminant (11) in the
//     module text; the corrupted JIT REJECTS the SProp accept while native
//     (pristine) ACCEPTS — proving the machine code genuinely runs the switch.
//
// Slice: crates/trust-cg-codegen/tests/slices/clean_sprop_slice.rs.
// Emit recipe (per root): trust_ir_mir --mir-emit-closure <root> <out.tir>
//   roots: sprop_defeq_root, sprop_infer_sort_root.
//
// Per-process under `perl -e 'alarm 600; exec @ARGV' -- <bin> --test-threads=1`.
#![allow(clippy::all)]
#![allow(dead_code)]
#![allow(non_snake_case)]
#![allow(unused_imports)]

use std::collections::HashMap;
use std::sync::Arc;
use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

// The native oracle: the slice compiled as a Rust module.
#[path = "slices/clean_sprop_slice.rs"]
pub mod rn;

// The VERBATIM MIR-emitted trust-ir closures, embedded from the in-repo
// regeneration artifacts (emit recipe in the header). Each is validate_module=0.
const DEFEQ_TIR: &str = include_str!("clean_sprop_defeq.tir");
const INFER_TIR: &str = include_str!("clean_sprop_infer_sort.tir");
fn tir(root: &str) -> String {
    match root {
        "sprop_defeq_root" => DEFEQ_TIR.to_string(),
        "sprop_infer_sort_root" => INFER_TIR.to_string(),
        _ => panic!("unknown root {root}"),
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Shims — the 6 bodyless externs the closure leaves (read off the emitted
// functys; identical mangled names in both roots' union).
// ════════════════════════════════════════════════════════════════════════════

// Allocator leaves: `Arc::new` lowers to the trust-cg `heap_alloc` intrinsic,
// which the JIT resolves to `__rust_alloc` at runtime. (No Arc is constructed on
// the decisive-scenario runtime paths — all leaf terms — but the whnf/instantiate
// Arc-rebuild arms are compiled, so the symbol must resolve.)
extern "C" fn s_alloc(size: usize, align: usize) -> *mut u8 {
    unsafe { std::alloc::alloc(std::alloc::Layout::from_size_align(size, align).unwrap()) }
}
extern "C" fn s_dealloc(ptr: *mut u8, size: usize, align: usize) {
    unsafe {
        std::alloc::dealloc(
            ptr,
            std::alloc::Layout::from_size_align(size, align).unwrap(),
        )
    }
}
extern "C" fn s_realloc(ptr: *mut u8, size: usize, align: usize, new_size: usize) -> *mut u8 {
    unsafe {
        std::alloc::realloc(
            ptr,
            std::alloc::Layout::from_size_align(size, align).unwrap(),
            new_size,
        )
    }
}

// `<&u64 as PartialEq>::eq` — receiver is `&&u64` (DOUBLE ptr): the call passes
// a slot holding the `&u64`. Used by lit_eq (`x == y`, x,y : &u64).
extern "C" fn s_ref_u64_eq(a: *const *const u64, b: *const *const u64) -> bool {
    unsafe { (**a) == (**b) }
}
// `<&u32 as PartialEq>::eq` — DOUBLE ptr. Used by Sort-depth eq (`l1 == l2`).
extern "C" fn s_ref_u32_eq(a: *const *const u32, b: *const *const u32) -> bool {
    unsafe { (**a) == (**b) }
}
// `<&u32 as Add<u32>>::add` — self : &u32 (single ptr), rhs : u32. Used by
// `Expr::sort(l + 1)` (the try_infer_type_quick Sort arm and infer_only Sort).
extern "C" fn s_ref_u32_add(self_: *const u32, rhs: u32) -> u32 {
    unsafe { (*self_) + rhs }
}
// `u64::wrapping_mul` — the compute_meta FNV mix (wmul).
extern "C" fn s_wrap_mul(a: u64, b: u64) -> u64 {
    a.wrapping_mul(b)
}
// `Arc<Expr>::clone` (sret, this).
extern "C" fn s_arc_expr_clone(sret: *mut Arc<rn::Expr>, this: *const Arc<rn::Expr>) {
    unsafe {
        std::ptr::write(sret, Arc::clone(&*this));
    }
}
// `Arc<Expr>::as_ref` — skip the 16-byte ArcInner header (2× usize refcounts)
// to the Expr payload. Arg is `&Arc<Expr>` = *const *const u8 (double).
extern "C" fn s_arc_expr_as_ref(arc_ref: *const *const u8) -> *const rn::Expr {
    unsafe { (*arc_ref).add(16) as *const rn::Expr }
}

// Exact mangled names (captured from the emitted .tir; the crate disambiguator
// `Csbl3Kp9dptzX_` is stable per crate name+content).
const SYM_U64_EQ: &str = "_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRmNtB7_9PartialEq2eqCsbl3Kp9dptzX_17clean_sprop_slice";
const SYM_U32_EQ: &str = "_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRyNtB7_9PartialEq2eqCsbl3Kp9dptzX_17clean_sprop_slice";
const SYM_U32_ADD: &str =
    "_RNvXsn_NtNtCs2EYQwhfuABO_4core3ops5arithRmINtB5_3AddmE3addCsbl3Kp9dptzX_17clean_sprop_slice";
const SYM_WRAP_MUL: &str = "_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_mul";
const SYM_ARC_CLONE: &str = "_RNvXsu_NtCskTzINo8ZBH9_5alloc4syncINtB5_3ArcNtCsbl3Kp9dptzX_17clean_sprop_slice4ExprENtNtCs2EYQwhfuABO_4core5clone5Clone5cloneBI_";
const SYM_ARC_AS_REF: &str = "_RNvXs1j_NtCskTzINo8ZBH9_5alloc4syncINtB6_3ArcNtCsbl3Kp9dptzX_17clean_sprop_slice4ExprEINtNtCs2EYQwhfuABO_4core7convert5AsRefBH_E6as_refBJ_";

fn externs() -> HashMap<String, *const u8> {
    let mut e: HashMap<String, *const u8> = HashMap::new();
    e.insert("__rust_alloc".to_string(), s_alloc as *const u8);
    e.insert("__rust_dealloc".to_string(), s_dealloc as *const u8);
    e.insert("__rust_realloc".to_string(), s_realloc as *const u8);
    e.insert(SYM_U64_EQ.to_string(), s_ref_u64_eq as *const u8);
    e.insert(SYM_U32_EQ.to_string(), s_ref_u32_eq as *const u8);
    e.insert(SYM_U32_ADD.to_string(), s_ref_u32_add as *const u8);
    e.insert(SYM_WRAP_MUL.to_string(), s_wrap_mul as *const u8);
    e.insert(SYM_ARC_CLONE.to_string(), s_arc_expr_clone as *const u8);
    e.insert(SYM_ARC_AS_REF.to_string(), s_arc_expr_as_ref as *const u8);
    e
}

fn parse_validate(text: &str, what: &str) -> trust_ir::Module {
    let m = trust_ir::parser::parse_module(text).unwrap_or_else(|e| panic!("{what} parse: {e:?}"));
    let errs = trust_ir_build::validate_module(&m);
    assert!(errs.is_empty(), "{what} validate: {errs:?}");
    m
}

fn jit_with_externs(
    text: &str,
    what: &str,
    ext: &HashMap<String, *const u8>,
) -> trust_cg_codegen::jit::ExecutableBuffer {
    let module = parse_validate(text, what);
    for f in &module.functions {
        if f.blocks.is_empty() {
            assert!(
                ext.contains_key(&f.name),
                "unbound extern `{}` in {what}",
                f.name
            );
        }
    }
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(&module, ext)
        .unwrap_or_else(|e| panic!("JIT compile {what} failed: {e:?}"))
        .buffer
}

fn jit(text: &str, what: &str) -> trust_cg_codegen::jit::ExecutableBuffer {
    jit_with_externs(text, what, &externs())
}

fn bind(buf: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buf.get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("sym {sym} not found"))
        .as_ptr()
}

type U64Fn = extern "C" fn(u64) -> u64;

// idx encoding for sprop_defeq_root.
const AWARE: u64 = 0;
const OVER_EAGER: u64 = 1 << 8;
const POISON: u64 = 2 << 8;
const BLIND_QF: u64 = 1 << 10;
const CUBICAL: u64 = 1 << 11;

fn native_defeq(idx: u64) -> u64 {
    rn::sprop_defeq_root(idx)
}
fn jit_defeq(f: U64Fn, idx: u64) -> u64 {
    f(idx)
}

fn native_infer(idx: u64) -> u64 {
    rn::sprop_infer_sort_root(idx)
}
fn jit_infer(f: U64Fn, idx: u64) -> u64 {
    f(idx)
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 1 — module sanity: the proof-irrelevance family is LIVE (bodied), def_eq
// genuinely Calls it, and the SProp universe switch is present in machine code.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn sprop_module_sanity_and_wiring() {
    for root in ["sprop_defeq_root", "sprop_infer_sort_root"] {
        let text = tir(root);
        let _ = parse_validate(&text, root);
    }
    let text = tir("sprop_defeq_root");
    let m = parse_validate(&text, "sprop_defeq_root");
    let bodied = |sym: &str| {
        m.functions
            .iter()
            .any(|f| f.name == sym && !f.blocks.is_empty())
    };
    // The whole proof-irrel family must be LIVE (bodied), not stubbed.
    assert!(
        bodied("Verifier__is_def_eq_proof_irrel"),
        "is_def_eq_proof_irrel must be bodied"
    );
    assert!(
        bodied("Verifier__type_is_proof_irrelevant"),
        "type_is_proof_irrelevant must be bodied"
    );
    assert!(
        bodied("Verifier__sprop_universe_check"),
        "sprop_universe_check must be bodied"
    );
    assert!(
        bodied("Verifier__type_is_quickly_not_in_prop"),
        "type_is_quickly_not_in_prop must be bodied"
    );
    assert!(
        bodied("Verifier__try_infer_type_quick_inner"),
        "try_infer_type_quick_inner must be bodied"
    );

    // def_eq_inner must genuinely Call is_def_eq_proof_irrel (the production
    // hook edge at def_eq/mod.rs:360 must RUN in machine code).
    let idx_exact = |sym: &str| {
        m.functions
            .iter()
            .position(|f| f.name == sym)
            .unwrap_or_else(|| panic!("{sym} not in module"))
    };
    let pii = idx_exact("Verifier__is_def_eq_proof_irrel");
    let body = |name: &str| -> String {
        let start = text.find(&format!("fn @{name}(")).unwrap();
        let after = &text[start + 1..];
        let end = after
            .find("\nfn @")
            .map(|k| start + 1 + k)
            .unwrap_or(text.len());
        text[start..end].to_string()
    };
    assert!(
        body("Verifier__def_eq_inner").contains(&format!("@func.{pii}(")),
        "def_eq_inner must Call is_def_eq_proof_irrel (the :360 hook)"
    );
    // The SProp universe switch (discriminant 11) must be present verbatim in
    // sprop_universe_check's machine code.
    assert!(
        body("Verifier__sprop_universe_check").contains("switch %19 [ 11: bb6 default: bb5 ]"),
        "the aware SProp discriminant switch (11) must be in sprop_universe_check"
    );
    eprintln!(
        "sanity: proof-irrel family LIVE; def_eq Calls it at func.{pii}; SProp switch present"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 2 — the DECISIVE scenarios: native == JIT AND the aware verdicts.
//   (a) hp1 =?= hp2 : P (P : SProp)  -> ACCEPT (strict irrelevance, :86).
//   (b) a   =?= b   : Foo (Foo:Type) -> REJECT (distinct values, non-SProp).
//   (c) q1  =?= q2  : Q (Q : Prop)   -> ACCEPT (Prop irrelevance, :85 — a
//       DISTINCT code path from SProp).
//   (d) 2   =?= 3   : Nat            -> REJECT (distinct literals).
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn sprop_defeq_decisive_native_jit() {
    let text = tir("sprop_defeq_root");
    let buf = jit(&text, "sprop_defeq_root");
    let f: U64Fn = unsafe { std::mem::transmute(bind(&buf, "sprop_defeq_root")) };
    let agree = |idx: u64| -> u64 {
        let n = native_defeq(idx);
        let j = jit_defeq(f, idx);
        assert_eq!(n, j, "idx {idx:#x}: native {n} != JIT {j}");
        j
    };

    // AWARE (production) verdicts.
    assert_eq!(
        agree(0 | AWARE),
        1,
        "(a) hp1=?=hp2 : SProp must ACCEPT (strict proof irrelevance)"
    );
    assert_eq!(
        agree(1 | AWARE),
        0,
        "(b) a=?=b : Foo(Type) must REJECT (distinct values of a non-SProp)"
    );
    assert_eq!(
        agree(2 | AWARE),
        1,
        "(c) q1=?=q2 : Prop must ACCEPT (Prop irrelevance, the :85 path)"
    );
    assert_eq!(
        agree(3 | AWARE),
        0,
        "(d) 2=?=3 : Nat must REJECT (distinct literals)"
    );
    // reflexivity controls (accept via P0 syntactic, NOT proof irrelevance).
    assert_eq!(agree(4 | AWARE), 1, "hp1=?=hp1 reflexivity ACCEPT");
    assert_eq!(agree(5 | AWARE), 1, "a=?=a reflexivity ACCEPT");

    eprintln!(
        "decisive: (a) SProp accept, (b) non-SProp reject, (c) Prop accept, (d) Nat reject — native==JIT"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 3 — THE UNSOUNDNESS CENTERPIECE: the over-eager `is_sprop` (universe
// check dropped) ACCEPTS distinct values of a non-SProp type — UNSOUND — while
// the AWARE engine REJECTS. native == JIT for BOTH configs, so the machine code
// genuinely runs the universe check; the divergence is 100% attributable to it.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn sprop_over_eager_unsoundness_centerpiece() {
    let text = tir("sprop_defeq_root");
    let buf = jit(&text, "sprop_defeq_root");
    let f: U64Fn = unsafe { std::mem::transmute(bind(&buf, "sprop_defeq_root")) };
    let agree = |idx: u64| -> u64 {
        let n = native_defeq(idx);
        let j = jit_defeq(f, idx);
        assert_eq!(n, j, "idx {idx:#x}: native {n} != JIT {j}");
        j
    };

    // (b) a =?= b : Foo (Type-level). THE decisive pair.
    assert_eq!(agree(1 | AWARE), 0, "AWARE must REJECT a=?=b : Foo (SOUND)");
    assert_eq!(
        agree(1 | OVER_EAGER),
        1,
        "OVER-EAGER must ACCEPT a=?=b : Foo (UNSOUND — universe check dropped conflates distinct values)"
    );
    // The divergence is EXACTLY the soundness gap and appears identically in JIT.
    assert_ne!(
        native_defeq(1 | AWARE),
        native_defeq(1 | OVER_EAGER),
        "the over-eager universe drop MUST diverge from aware on Foo"
    );

    // Nat is guarded in DEPTH: the quick pre-filter short-circuits before the
    // universe check, so over-eager ALONE still REJECTS 2=?=3 ...
    assert_eq!(agree(3 | AWARE), 0, "AWARE rejects 2=?=3");
    assert_eq!(
        agree(3 | OVER_EAGER),
        0,
        "over-eager ALONE still rejects 2=?=3 (quick pre-filter guards Nat)"
    );
    // ... but with the pre-filter ALSO dropped, the over-eager universe check
    // ACCEPTS the literal 2 =?= 3 — the task-literal unsound conflation.
    assert_eq!(
        agree(3 | OVER_EAGER | BLIND_QF),
        1,
        "over-eager + no-quickfilter ACCEPTS 2=?=3 (UNSOUND — proves 2=3=False)"
    );

    // The Prop and SProp accepts are unchanged under over-eager (already accept).
    assert_eq!(
        agree(0 | OVER_EAGER),
        1,
        "SProp accept unchanged under over-eager"
    );
    assert_eq!(
        agree(2 | OVER_EAGER),
        1,
        "Prop accept unchanged under over-eager"
    );

    eprintln!(
        "CENTERPIECE: over-eager is_sprop ACCEPTS a=?=b:Foo and 2=?=3 (UNSOUND); aware REJECTS; native==JIT both"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 4 — THE POISONED is_sprop ORACLE: inverting the universe check (SProp
// never recognized) REJECTS distinct proofs of an SProp — the :86 disjunct is
// load-bearing for the sound accept — while leaving the Prop path (:85)
// UNCHANGED. The two arms are independent. Verdicts flip identically native==JIT.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn sprop_poisoned_oracle_and_prop_independence() {
    let text = tir("sprop_defeq_root");
    let buf = jit(&text, "sprop_defeq_root");
    let f: U64Fn = unsafe { std::mem::transmute(bind(&buf, "sprop_defeq_root")) };
    let agree = |idx: u64| -> u64 {
        let n = native_defeq(idx);
        let j = jit_defeq(f, idx);
        assert_eq!(n, j, "idx {idx:#x}: native {n} != JIT {j}");
        j
    };

    // (a) hp1 =?= hp2 : P (SProp). Aware ACCEPTs; POISON REJECTs — the :86
    //     disjunct is load-bearing.
    assert_eq!(agree(0 | AWARE), 1, "aware ACCEPTs SProp proofs");
    assert_eq!(
        agree(0 | POISON),
        0,
        "POISON REJECTs SProp proofs (:86 disjunct is load-bearing)"
    );
    assert_ne!(
        native_defeq(0 | AWARE),
        native_defeq(0 | POISON),
        "poison must flip the SProp verdict"
    );

    // (c) q1 =?= q2 : Q (Prop). Poisoning the SProp arm must NOT touch the Prop
    //     path — it still ACCEPTs. The two disjuncts are INDEPENDENT.
    assert_eq!(agree(2 | AWARE), 1, "aware ACCEPTs Prop proofs (:85)");
    assert_eq!(
        agree(2 | POISON),
        1,
        "POISON leaves the Prop path UNCHANGED (Prop != SProp code path)"
    );

    // (b) Foo: already rejects; poison keeps rejecting.
    assert_eq!(
        agree(1 | POISON),
        0,
        "poison keeps rejecting distinct Foo values"
    );

    eprintln!(
        "poison: SProp verdict flips (:86 load-bearing); Prop verdict UNCHANGED (:85 independent); native==JIT"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 5 — the CleanMode gate (proof_irrel.rs:36-38): the fibrant Cubical layer
// must NOT use definitional proof irrelevance (UIP inconsistent with
// univalence). In Cubical mode BOTH the SProp and Prop proofs REJECT. native==JIT.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn sprop_cubical_mode_disables_proof_irrel() {
    let text = tir("sprop_defeq_root");
    let buf = jit(&text, "sprop_defeq_root");
    let f: U64Fn = unsafe { std::mem::transmute(bind(&buf, "sprop_defeq_root")) };
    let agree = |idx: u64| -> u64 {
        let n = native_defeq(idx);
        let j = jit_defeq(f, idx);
        assert_eq!(n, j, "idx {idx:#x}: native {n} != JIT {j}");
        j
    };

    // Impredicative: proof irrel active (baseline).
    assert_eq!(agree(0 | AWARE), 1, "Impredicative: SProp proofs ACCEPT");
    assert_eq!(agree(2 | AWARE), 1, "Impredicative: Prop proofs ACCEPT");
    // Cubical: the :36-38 early-out disables ALL proof irrelevance.
    assert_eq!(
        agree(0 | CUBICAL),
        0,
        "Cubical: SProp proofs REJECT (proof irrel disabled on the fibrant layer)"
    );
    assert_eq!(
        agree(2 | CUBICAL),
        0,
        "Cubical: Prop proofs REJECT (proof irrel disabled)"
    );
    // reflexivity is unaffected by the mode gate (P0 syntactic).
    assert_eq!(
        agree(4 | CUBICAL),
        1,
        "Cubical: reflexivity still ACCEPTs (P0, not proof irrel)"
    );

    eprintln!("mode gate: Cubical disables proof irrelevance for BOTH Prop and SProp; native==JIT");
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 6 — infer_sort's SProp arm (infer.rs:774, `SProp => Ok(Level::zero())`)
// and infer_sprop's MODE gate (infer_zfc.rs:160-168): native == JIT.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn sprop_infer_sort_native_jit() {
    let text = tir("sprop_infer_sort_root");
    let buf = jit(&text, "sprop_infer_sort_root");
    let f: U64Fn = unsafe { std::mem::transmute(bind(&buf, "sprop_infer_sort_root")) };
    let agree = |idx: u64| -> u64 {
        let n = native_infer(idx);
        let j = jit_infer(f, idx);
        assert_eq!(n, j, "infer idx {idx:#x}: native {n} != JIT {j}");
        j
    };
    const CONSTRUCTIVE: u64 = 1 << 8;

    // Impredicative: the SProp arm at infer.rs:774 treats an SProp-typed prop as
    // level 0 (like Prop).
    assert_eq!(
        agree(0),
        0,
        "infer_sort(P : SProp) = 0 (the SProp arm, :774)"
    );
    assert_eq!(agree(1), 0, "infer_sort(Q : Prop) = 0");
    assert_eq!(agree(2), 1, "infer_sort(Foo : Type 0) = 1");
    assert_eq!(
        agree(3),
        1,
        "infer_sort(SProp) = 1 (infer_sprop -> Sort 1 in Impredicative)"
    );
    // The mode gate: infer_sprop errors outside Impredicative/Classical/SetTheoretic.
    assert_eq!(
        agree(3 | CONSTRUCTIVE),
        u64::MAX,
        "infer_sort(SProp) in Constructive is a mode error"
    );
    // P's type is SProp regardless of mode (const_type is not mode-gated), so
    // infer_sort(P) stays 0 even in Constructive.
    assert_eq!(
        agree(0 | CONSTRUCTIVE),
        0,
        "infer_sort(P) in Constructive still 0 (const_type not mode-gated)"
    );

    eprintln!(
        "infer_sort: SProp arm (:774) live -> level 0; infer_sprop mode gate errors in Constructive; native==JIT"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 7 — ARMED golden corruption: flip the SProp discriminant (11) in the
// module text. The corrupted JIT's aware universe check now matches discriminant
// 10 (MData) instead of SProp, so `hp1 =?= hp2 : P` REJECTs, while native (the
// pristine slice) ACCEPTs. The differential CATCHES it — proving the embedded
// .tir is genuinely compiled & executed and the SProp switch is load-bearing.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn sprop_armed_golden_corruption() {
    let base = tir("sprop_defeq_root");
    let n_accept = native_defeq(0 | AWARE); // pristine native: SProp proofs ACCEPT
    assert_eq!(n_accept, 1, "native aware must ACCEPT the SProp pair");

    // baseline: uncorrupted JIT matches native (ACCEPT).
    {
        let buf = jit(&base, "sprop_defeq_root");
        let f: U64Fn = unsafe { std::mem::transmute(bind(&buf, "sprop_defeq_root")) };
        assert_eq!(
            jit_defeq(f, 0 | AWARE),
            1,
            "baseline JIT must ACCEPT the SProp pair (matches native)"
        );
    }

    // ARMED corruption: SProp discriminant 11 -> 10 in the aware universe switch.
    let target = "switch %19 [ 11: bb6 default: bb5 ]";
    assert_eq!(
        base.matches(target).count(),
        1,
        "the SProp switch must be a unique corruption target"
    );
    let corrupted = base.replace(target, "switch %19 [ 10: bb6 default: bb5 ]");
    assert!(corrupted != base, "corruption must change the text");

    let buf = jit(&corrupted, "sprop_defeq_root(SProp-disc-corrupted)");
    let f: U64Fn = unsafe { std::mem::transmute(bind(&buf, "sprop_defeq_root")) };
    let j_corrupt = jit_defeq(f, 0 | AWARE);
    assert_eq!(
        j_corrupt, 0,
        "corrupted JIT (SProp disc 11->10) must REJECT the SProp pair (the switch is load-bearing)"
    );
    assert_ne!(
        n_accept, j_corrupt,
        "armed control: pristine native ACCEPTs but corrupted JIT REJECTs — the differential is genuinely load-bearing"
    );
    // The corruption must NOT touch the Prop path (:85) — scenario 2 unaffected.
    assert_eq!(
        jit_defeq(f, 2 | AWARE),
        1,
        "corrupting the SProp switch leaves the Prop accept UNCHANGED"
    );

    eprintln!(
        "armed: SProp disc 11->10 flips the SProp accept to reject in JIT (native still accepts); Prop path unaffected"
    );
}
