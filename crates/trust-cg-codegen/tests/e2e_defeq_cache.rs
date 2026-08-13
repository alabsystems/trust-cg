// R14 — THE DEF-EQ CACHE LAYER: native == JIT over Clean's definitional-equality
// cache surface (the DefEqCacheKey routing + the #1773/#38 negative-cache
// SOUNDNESS guard, the equiv_manager union-find, the #3402 verified-pair memo)
// compiled through Trust (Rust -> MIR -> trust-ir -> trust-cg -> machine code).
//
// THE POINT: a def_eq cache must be TRANSPARENT (hit == miss on every verdict —
// it changes nothing but a hit counter), and a NEGATIVE verdict is
// CONTEXT-DEPENDENT when the compared terms carry FVars from the LocalContext.
// The #1773 guard (`all_fvars_in_context`) forces a RECOMPUTE when a cached
// negative mentions a fvar out of the current context; a cache WITHOUT the guard
// is UNSOUND (the BLIND control returns a stale wrong reject where the guarded
// and the uncached both correctly accept).
//
// Slice: crates/trust-cg-codegen/tests/slices/clean_defeq_cache_slice.rs.
// Emit recipe (single root): trust_ir_mir --mir-emit-closure defeq_cache_root
//   crates/trust-cg-codegen/tests/clean_defeq_cache.tir  (validate_module = 0).
//
// Per-process under `perl -e 'alarm 600; exec @ARGV' -- <bin> --test-threads=1`.
#![allow(clippy::all)]
#![allow(dead_code)]
#![allow(non_snake_case)]
#![allow(unused_imports)]

#[cfg(kernel_fixture_layout_unknown)]
compile_error!(
    "kernel JIT fixtures require exact Rust 1.95.0, Rust 1.97.1, or the certified Trust compiler"
);

use std::collections::HashMap;
use std::sync::Arc;
use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

// The native oracle: the slice compiled as a Rust module.
#[path = "slices/clean_defeq_cache_slice.rs"]
pub mod rn;

// The VERBATIM MIR-emitted trust-ir closure of defeq_cache_root. Two frozen
// snapshots, selected by the exact fixture-compiler identity (see build.rs):
//   * Rust 1.95 (`clean_defeq_cache.tir`)      — baked by the fixtures' 1.95
//     generation toolchain (repr(Rust) niche/discriminant layout of that build,
//     and the older sret ABI for `<Arc<Expr> as Clone>::clone`).
//   * Rust 1.97 (`clean_defeq_cache.trust.tir`) — re-emitted by the current
//     self-hosted frontend (prerelease rustc-master layout + register-return
//     clone ABI). Each pairs with its matching `s_arc_clone` shim below.
// Both certified fixture lanes run all tests; nothing is ignored.
#[cfg(kernel_fixture_layout_matches)]
const TIR: &str = include_str!("clean_defeq_cache.tir");
#[cfg(not(kernel_fixture_layout_matches))]
const TIR: &str = include_str!("clean_defeq_cache.trust.tir");

type Pair = (rn::Expr, rn::Expr);

// ── Vec / Arc / Option / cmp shims (all element structs use the by-pointer ABI,
//    read off the emitted functys: new (sret), push (v, *const T), len (v)->u64,
//    index/index_mut (v, u64)->ptr, pop (sret Option<T>, v)). ──

macro_rules! vec_new {
    ($n:ident, $t:ty) => {
        extern "C" fn $n(sret: *mut Vec<$t>) {
            unsafe {
                std::ptr::write(sret, Vec::new());
            }
        }
    };
}
macro_rules! vec_push {
    ($n:ident, $t:ty) => {
        extern "C" fn $n(v: *mut Vec<$t>, val: *const $t) {
            unsafe {
                let e = std::ptr::read(val);
                (*v).push(e);
            }
        }
    };
}
macro_rules! vec_len {
    ($n:ident, $t:ty) => {
        extern "C" fn $n(v: *const Vec<$t>) -> u64 {
            unsafe { (*v).len() as u64 }
        }
    };
}
macro_rules! vec_index {
    ($n:ident, $t:ty) => {
        extern "C" fn $n(v: *const Vec<$t>, idx: u64) -> *const $t {
            unsafe {
                let s: &[$t] = (*v).as_slice();
                assert!((idx as usize) < s.len(), "vec index oob");
                s.as_ptr().add(idx as usize)
            }
        }
    };
}
macro_rules! vec_index_mut {
    ($n:ident, $t:ty) => {
        extern "C" fn $n(v: *mut Vec<$t>, idx: u64) -> *mut $t {
            unsafe {
                let s: &mut [$t] = (*v).as_mut_slice();
                assert!((idx as usize) < s.len(), "vec index_mut oob");
                s.as_mut_ptr().add(idx as usize)
            }
        }
    };
}

vec_new!(v_new_expr, rn::Expr);
vec_new!(v_new_decl, rn::LocalDecl);
vec_new!(v_new_entry, rn::DefEqEntry);
vec_new!(v_new_node, rn::EquivNode);
vec_new!(v_new_pair, Pair);

vec_push!(v_push_expr, rn::Expr);
vec_push!(v_push_decl, rn::LocalDecl);
vec_push!(v_push_entry, rn::DefEqEntry);
vec_push!(v_push_node, rn::EquivNode);
vec_push!(v_push_pair, Pair);

vec_len!(v_len_expr, rn::Expr);
vec_len!(v_len_decl, rn::LocalDecl);
vec_len!(v_len_entry, rn::DefEqEntry);
vec_len!(v_len_node, rn::EquivNode);
vec_len!(v_len_pair, Pair);

vec_index!(v_idx_expr, rn::Expr);
vec_index!(v_idx_decl, rn::LocalDecl);
vec_index!(v_idx_entry, rn::DefEqEntry);
vec_index!(v_idx_node, rn::EquivNode);
vec_index!(v_idx_pair, Pair);

vec_index_mut!(v_idxmut_decl, rn::LocalDecl);
vec_index_mut!(v_idxmut_node, rn::EquivNode);

extern "C" fn v_pop_decl(sret: *mut Option<rn::LocalDecl>, v: *mut Vec<rn::LocalDecl>) {
    unsafe {
        std::ptr::write(sret, (*v).pop());
    }
}

// Arc<Expr> clone / as_ref (ArcInner data @ +16, align 8).
//
// The emitted functy for `<Arc<Expr> as Clone>::clone` is `(ptr) -> (ptr)`: `this`
// (a `&Arc<Expr>`) comes in x0 and the cloned `Arc<Expr>` is RETURNED by value in
// the register — `Arc<Expr>` is pointer-sized (8 bytes = `NonNull<ArcInner>`), so
// the AArch64 ABI returns it in a register, NOT via an sret out-pointer. The old
// shim used the sret ABI `(sret, this)`; against the register-return functy that
// makes the JIT-supplied `this` land in x0 while the shim reads a stale x1, so
// `Arc::clone` dereferences garbage. The raw Arc value is the ArcInner base
// (= data_ptr - 16, matching the +16 convention in `s_arc_as_ref`); `into_raw`
// keeps the strong count this clone just incremented.
// Stable fixture: older frontend emitted the clone with the sret ABI
// `(sret, this) -> ()`. Trust fixture: current frontend emits register-return
// `(this) -> ptr`. The shim ABI must match whichever `.tir` is compiled.
#[cfg(kernel_fixture_layout_matches)]
extern "C" fn s_arc_clone(sret: *mut Arc<rn::Expr>, this: *const Arc<rn::Expr>) {
    unsafe {
        std::ptr::write(sret, Arc::clone(&*this));
    }
}
#[cfg(not(kernel_fixture_layout_matches))]
extern "C" fn s_arc_clone(this: *const Arc<rn::Expr>) -> *const rn::Expr {
    unsafe {
        let data = Arc::into_raw(Arc::clone(&*this)) as *const u8;
        data.sub(16) as *const rn::Expr
    }
}
extern "C" fn s_arc_as_ref(arc_ref: *const *const u8) -> *const rn::Expr {
    unsafe { (*arc_ref).add(16) as *const rn::Expr }
}

// Option<Expr>::clone / is_some ; Option<LocalDecl>::is_some.
extern "C" fn s_opt_expr_clone(sret: *mut Option<rn::Expr>, this: *const Option<rn::Expr>) {
    unsafe {
        std::ptr::write(sret, (*this).clone());
    }
}
extern "C" fn s_opt_expr_is_some(this: *const Option<rn::Expr>) -> bool {
    unsafe { (*this).is_some() }
}
extern "C" fn s_opt_decl_is_some(this: *const Option<rn::LocalDecl>) -> bool {
    unsafe { (*this).is_some() }
}

// <&T as PartialEq/PartialOrd> — receiver is &&T (double pointer).
extern "C" fn s_ref_u64_eq(a: *const *const u64, b: *const *const u64) -> bool {
    unsafe { **a == **b }
}
extern "C" fn s_ref_u32_eq(a: *const *const u32, b: *const *const u32) -> bool {
    unsafe { **a == **b }
}
extern "C" fn s_ref_u32_lt(a: *const *const u32, b: *const *const u32) -> bool {
    unsafe { **a < **b }
}
extern "C" fn s_ref_u32_gt(a: *const *const u32, b: *const *const u32) -> bool {
    unsafe { **a > **b }
}

// core::num::<u64>::wrapping_mul.
extern "C" fn s_wrap_mul(a: u64, b: u64) -> u64 {
    a.wrapping_mul(b)
}

// ── mangled-name bindings (read off the emitted .tir bodyless functions) ──
const M_VNEW_EXPR: &str = "_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCseaynGAz3kP1_23clean_defeq_cache_slice4ExprE3newBE_";
const M_VNEW_DECL: &str = "_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCseaynGAz3kP1_23clean_defeq_cache_slice9LocalDeclE3newBE_";
const M_VNEW_ENTRY: &str = "_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCseaynGAz3kP1_23clean_defeq_cache_slice10DefEqEntryE3newBE_";
const M_VNEW_NODE: &str = "_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecNtCseaynGAz3kP1_23clean_defeq_cache_slice9EquivNodeE3newBE_";
const M_VNEW_PAIR: &str = "_RNvMNtCskTzINo8ZBH9_5alloc3vecINtB2_3VecTNtCseaynGAz3kP1_23clean_defeq_cache_slice4ExprBD_EE3newBF_";

const M_VPUSH_EXPR: &str = "_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCseaynGAz3kP1_23clean_defeq_cache_slice4ExprE4pushBH_";
const M_VPUSH_DECL: &str = "_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCseaynGAz3kP1_23clean_defeq_cache_slice9LocalDeclE4pushBH_";
const M_VPUSH_ENTRY: &str = "_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCseaynGAz3kP1_23clean_defeq_cache_slice10DefEqEntryE4pushBH_";
const M_VPUSH_NODE: &str = "_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCseaynGAz3kP1_23clean_defeq_cache_slice9EquivNodeE4pushBH_";
const M_VPUSH_PAIR: &str = "_RNvMsF_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecTNtCseaynGAz3kP1_23clean_defeq_cache_slice4ExprBG_EE4pushBI_";

const M_VLEN_EXPR: &str = "_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCseaynGAz3kP1_23clean_defeq_cache_slice4ExprE3lenBG_";
const M_VLEN_DECL: &str = "_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCseaynGAz3kP1_23clean_defeq_cache_slice9LocalDeclE3lenBG_";
const M_VLEN_ENTRY: &str = "_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCseaynGAz3kP1_23clean_defeq_cache_slice10DefEqEntryE3lenBG_";
const M_VLEN_NODE: &str = "_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCseaynGAz3kP1_23clean_defeq_cache_slice9EquivNodeE3lenBG_";
const M_VLEN_PAIR: &str = "_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecTNtCseaynGAz3kP1_23clean_defeq_cache_slice4ExprBF_EE3lenBH_";

const M_VIDX_EXPR: &str = "_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCseaynGAz3kP1_23clean_defeq_cache_slice4ExprEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_";
const M_VIDX_DECL: &str = "_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCseaynGAz3kP1_23clean_defeq_cache_slice9LocalDeclEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_";
const M_VIDX_ENTRY: &str = "_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCseaynGAz3kP1_23clean_defeq_cache_slice10DefEqEntryEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_";
const M_VIDX_NODE: &str = "_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCseaynGAz3kP1_23clean_defeq_cache_slice9EquivNodeEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBH_";
const M_VIDX_PAIR: &str = "_RNvXsc_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecTNtCseaynGAz3kP1_23clean_defeq_cache_slice4ExprBG_EEINtNtNtCs2EYQwhfuABO_4core3ops5index5IndexjE5indexBI_";

const M_VIDXMUT_DECL: &str = "_RNvXsd_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCseaynGAz3kP1_23clean_defeq_cache_slice9LocalDeclEINtNtNtCs2EYQwhfuABO_4core3ops5index8IndexMutjE9index_mutBH_";
const M_VIDXMUT_NODE: &str = "_RNvXsd_NtCskTzINo8ZBH9_5alloc3vecINtB5_3VecNtCseaynGAz3kP1_23clean_defeq_cache_slice9EquivNodeEINtNtNtCs2EYQwhfuABO_4core3ops5index8IndexMutjE9index_mutBH_";

const M_VPOP_DECL: &str = "_RNvMs_NtCskTzINo8ZBH9_5alloc3vecINtB4_3VecNtCseaynGAz3kP1_23clean_defeq_cache_slice9LocalDeclE3popBG_";

const M_ARC_CLONE: &str = "_RNvXsu_NtCskTzINo8ZBH9_5alloc4syncINtB5_3ArcNtCseaynGAz3kP1_23clean_defeq_cache_slice4ExprENtNtCs2EYQwhfuABO_4core5clone5Clone5cloneBI_";
const M_ARC_ASREF: &str = "_RNvXs1j_NtCskTzINo8ZBH9_5alloc4syncINtB6_3ArcNtCseaynGAz3kP1_23clean_defeq_cache_slice4ExprEINtNtCs2EYQwhfuABO_4core7convert5AsRefBH_E6as_refBJ_";

const M_OPT_EXPR_CLONE: &str = "_RNvXs4_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionNtCseaynGAz3kP1_23clean_defeq_cache_slice4ExprENtNtB7_5clone5Clone5cloneBM_";
const M_OPT_EXPR_ISSOME: &str = "_RNvMNtCs2EYQwhfuABO_4core6optionINtB2_6OptionNtCseaynGAz3kP1_23clean_defeq_cache_slice4ExprE7is_someBJ_";
const M_OPT_DECL_ISSOME: &str = "_RNvMNtCs2EYQwhfuABO_4core6optionINtB2_6OptionNtCseaynGAz3kP1_23clean_defeq_cache_slice9LocalDeclE7is_someBJ_";

const M_REF_U64_EQ: &str = "_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRyNtB7_9PartialEq2eqCseaynGAz3kP1_23clean_defeq_cache_slice";
const M_REF_U32_EQ: &str = "_RNvXs7_NtNtCs2EYQwhfuABO_4core3cmp5implsRmNtB7_9PartialEq2eqCseaynGAz3kP1_23clean_defeq_cache_slice";
const M_REF_U32_LT: &str = "_RNvXs8_NtNtCs2EYQwhfuABO_4core3cmp5implsRmNtB7_10PartialOrd2ltCseaynGAz3kP1_23clean_defeq_cache_slice";
const M_REF_U32_GT: &str = "_RNvXs8_NtNtCs2EYQwhfuABO_4core3cmp5implsRmNtB7_10PartialOrd2gtCseaynGAz3kP1_23clean_defeq_cache_slice";

const M_WRAP_MUL: &str = "_RNvMs7_NtCs2EYQwhfuABO_4core3numy12wrapping_mul";

fn externs() -> HashMap<String, *const u8> {
    let mut e: HashMap<String, *const u8> = HashMap::new();
    let mut ins = |k: &str, v: *const u8| {
        e.insert(k.to_string(), v);
    };
    // __rust_alloc/dealloc/realloc (heap for the Arc/Vec growth).
    ins("__rust_alloc", s_alloc as *const u8);
    ins("__rust_dealloc", s_dealloc as *const u8);
    ins("__rust_realloc", s_realloc as *const u8);
    ins(M_VNEW_EXPR, v_new_expr as *const u8);
    ins(M_VNEW_DECL, v_new_decl as *const u8);
    ins(M_VNEW_ENTRY, v_new_entry as *const u8);
    ins(M_VNEW_NODE, v_new_node as *const u8);
    ins(M_VNEW_PAIR, v_new_pair as *const u8);
    ins(M_VPUSH_EXPR, v_push_expr as *const u8);
    ins(M_VPUSH_DECL, v_push_decl as *const u8);
    ins(M_VPUSH_ENTRY, v_push_entry as *const u8);
    ins(M_VPUSH_NODE, v_push_node as *const u8);
    ins(M_VPUSH_PAIR, v_push_pair as *const u8);
    ins(M_VLEN_EXPR, v_len_expr as *const u8);
    ins(M_VLEN_DECL, v_len_decl as *const u8);
    ins(M_VLEN_ENTRY, v_len_entry as *const u8);
    ins(M_VLEN_NODE, v_len_node as *const u8);
    ins(M_VLEN_PAIR, v_len_pair as *const u8);
    ins(M_VIDX_EXPR, v_idx_expr as *const u8);
    ins(M_VIDX_DECL, v_idx_decl as *const u8);
    ins(M_VIDX_ENTRY, v_idx_entry as *const u8);
    ins(M_VIDX_NODE, v_idx_node as *const u8);
    ins(M_VIDX_PAIR, v_idx_pair as *const u8);
    ins(M_VIDXMUT_DECL, v_idxmut_decl as *const u8);
    ins(M_VIDXMUT_NODE, v_idxmut_node as *const u8);
    ins(M_VPOP_DECL, v_pop_decl as *const u8);
    ins(M_ARC_CLONE, s_arc_clone as *const u8);
    ins(M_ARC_ASREF, s_arc_as_ref as *const u8);
    ins(M_OPT_EXPR_CLONE, s_opt_expr_clone as *const u8);
    ins(M_OPT_EXPR_ISSOME, s_opt_expr_is_some as *const u8);
    ins(M_OPT_DECL_ISSOME, s_opt_decl_is_some as *const u8);
    ins(M_REF_U64_EQ, s_ref_u64_eq as *const u8);
    ins(M_REF_U32_EQ, s_ref_u32_eq as *const u8);
    ins(M_REF_U32_LT, s_ref_u32_lt as *const u8);
    ins(M_REF_U32_GT, s_ref_u32_gt as *const u8);
    ins(M_WRAP_MUL, s_wrap_mul as *const u8);
    e
}

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

fn parse_validate(text: &str, what: &str) -> trust_ir::Module {
    let m = trust_ir::parser::parse_module(text).unwrap_or_else(|e| panic!("{what} parse: {e:?}"));
    let errs = trust_ir_build::validate_module(&m);
    assert!(errs.is_empty(), "{what} validate: {errs:?}");
    m
}

extern "C" fn s_noop_drop() {}
extern "C" fn s_abort_panic() {
    std::process::abort();
}

// Normalize a Rust v0-mangled symbol so drifting disambiguators (the
// `Cs<base62>_` crate-disambiguator and `s<base62>_` impl-disambiguators, plus
// backref tokens) are neutralized while every length-prefixed <count><identifier>
// run is copied VERBATIM (read the count, copy exactly that many bytes). A misparse
// panics loudly — never a silent wrong-bind.
fn norm_extern(name: &str) -> String {
    let b = name.as_bytes();
    let mut i = 0usize;
    let mut out = String::new();
    while i < b.len() {
        let c = b[i];
        if c.is_ascii_digit() {
            // length-prefixed identifier <decimaldigits><identifier>: copy verbatim.
            let mut j = i;
            let mut n: usize = 0;
            while j < b.len() && b[j].is_ascii_digit() {
                n = n
                    .checked_mul(10)
                    .and_then(|x| x.checked_add((b[j] - b'0') as usize))
                    .unwrap_or_else(|| panic!("norm_extern length overflow in `{name}`"));
                j += 1;
            }
            let end = j
                .checked_add(n)
                .filter(|&e| e <= b.len())
                .unwrap_or_else(|| {
                    panic!("norm_extern misparse: identifier length {n} at {i} overruns `{name}`")
                });
            out.push_str(&name[i..end]);
            i = end;
        } else if c == b'B' {
            // backref B<base62>_ : copy verbatim (never a length prefix).
            let mut j = i + 1;
            while j < b.len() && b[j].is_ascii_alphanumeric() {
                j += 1;
            }
            if j < b.len() && b[j] == b'_' {
                j += 1;
            }
            out.push_str(&name[i..j]);
            i = j;
        } else if c == b's' {
            // possible disambiguator s<base62>_ : strip if it closes with `_`.
            let mut j = i + 1;
            while j < b.len() && b[j].is_ascii_alphanumeric() {
                j += 1;
            }
            if j < b.len() && b[j] == b'_' {
                i = j + 1; // drop the whole s...._ token
            } else {
                out.push('s');
                i += 1;
            }
        } else {
            out.push(c as char);
            i += 1;
        }
    }
    out
}

fn jit_with(
    text: &str,
    what: &str,
    ext: &HashMap<String, *const u8>,
) -> trust_cg_codegen::jit::ExecutableBuffer {
    let module = parse_validate(text, what);
    // Build a normalized index of the shim table.
    let mut norm_index: HashMap<String, *const u8> = HashMap::new();
    for (k, &v) in ext {
        let nk = norm_extern(k);
        if let Some(&prev) = norm_index.get(&nk) {
            assert!(
                prev == v,
                "norm_extern shim collision: `{k}` -> `{nk}` maps to two pointers"
            );
        }
        norm_index.insert(nk, v);
    }
    // Seed with the raw shim table so runtime symbols (e.g. __rust_alloc) and any
    // already-exact-matching mangled names stay bound; overlay robust bindings below.
    let mut resolved: HashMap<String, *const u8> = ext.clone();
    // Resolve each empty-body (extern) function robustly by normalized name.
    for f in &module.functions {
        if !f.blocks.is_empty() {
            continue;
        }
        let nn = norm_extern(&f.name);
        let ptr: *const u8 = if nn.contains("drop_glue") || nn.contains("rust_eh_personality") {
            s_noop_drop as *const u8
        } else if nn.contains("panic") {
            s_abort_panic as *const u8
        } else if let Some(&p) = norm_index.get(&nn) {
            p
        } else {
            panic!(
                "unbound extern `{}` (normalized `{}`) in {what}",
                f.name, nn
            );
        };
        resolved.insert(f.name.clone(), ptr);
    }
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(&module, &resolved)
        .unwrap_or_else(|e| panic!("JIT compile {what} failed: {e:?}"))
        .buffer
}
fn jit(text: &str, what: &str) -> trust_cg_codegen::jit::ExecutableBuffer {
    jit_with(text, what, &externs())
}
fn bind(buf: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buf.get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("sym {sym} not found"))
        .as_ptr()
}

type RootFn = extern "C" fn(u64) -> u64;

// idx encoding: cat = idx>>16 ; lo = idx&0xffff.
fn idx(cat: u64, lo: u64) -> u64 {
    (cat << 16) | lo
}
fn native(i: u64) -> u64 {
    rn::defeq_cache_root(i)
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 1 — module sanity + the cache-routing wiring.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn cache_module_sanity_and_wiring() {
    let m = parse_validate(TIR, "defeq_cache_root");
    let bodied = |sym: &str| {
        m.functions
            .iter()
            .any(|f| f.name == sym && !f.blocks.is_empty())
    };
    // The cache surface must be LIVE (bodied) in-module.
    assert!(
        bodied("Verifier__is_def_eq_inner"),
        "is_def_eq_inner must be bodied"
    );
    assert!(
        bodied("Verifier__is_def_eq_core"),
        "is_def_eq_core must be bodied"
    );
    assert!(
        bodied("Verifier__all_fvars_in_context"),
        "all_fvars_in_context (#1773) must be bodied"
    );
    assert!(bodied("cache_get"), "cache_get must be bodied");
    assert!(bodied("cache_insert"), "cache_insert must be bodied");
    assert!(
        bodied("equiv_is_equiv"),
        "equiv_is_equiv (union-find) must be bodied"
    );
    assert!(bodied("equiv_add"), "equiv_add must be bodied");
    assert!(
        bodied("Verifier__try_branch_sharing_def_eq"),
        "try_branch_sharing_def_eq (#3402) must be bodied"
    );
    assert!(
        bodied("is_verified_pair"),
        "is_verified_pair must be bodied"
    );

    // The #1773 guard edge must genuinely RUN: is_def_eq_inner Calls
    // all_fvars_in_context and cache_get.
    let idx_of = |sym: &str| {
        m.functions
            .iter()
            .position(|f| f.name == sym)
            .unwrap_or_else(|| panic!("{sym} not in module"))
    };
    let inner = idx_of("Verifier__is_def_eq_inner");
    let afic = idx_of("Verifier__all_fvars_in_context");
    let cget = idx_of("cache_get");
    let body = |i: usize| -> String {
        let name = &m.functions[i].name;
        let start = TIR.find(&format!("fn @{name}(")).unwrap();
        let after = &TIR[start + 1..];
        let end = after
            .find("\nfn @")
            .map(|k| start + 1 + k)
            .unwrap_or(TIR.len());
        TIR[start..end].to_string()
    };
    let inner_body = body(inner);
    assert!(
        inner_body.contains(&format!("@func.{afic}(")),
        "is_def_eq_inner must Call all_fvars_in_context (#1773 guard)"
    );
    assert!(
        inner_body.contains(&format!("@func.{cget}(")),
        "is_def_eq_inner must Call cache_get (the cache routing)"
    );
    eprintln!(
        "sanity: cache surface live and wired (is_def_eq_inner -> all_fvars_in_context func.{afic}, cache_get func.{cget})"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 2 — TRANSPARENCY: hit == miss. Cold-then-warm on every scenario; the
// cached verdict EQUALS the recomputed verdict (bit2), and the hit counter
// genuinely advances (bit3 def_eq cache, bit4 equiv). native == JIT.
// Bit layout: bit0 cold, bit1 warm, bit2 cold==warm, bit3 cache-hit-adv,
// bit4 equiv-hit-adv.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn cache_transparency_hit_equals_miss() {
    let buf = jit(TIR, "defeq_cache_root");
    let f: RootFn = unsafe { std::mem::transmute(bind(&buf, "defeq_cache_root")) };

    // (lo, expect_cold, want_cache_adv, want_equiv_adv)
    let cases: &[(u64, u64, bool, bool)] = &[
        (0, 0, true, false), // dfn=?=bar NEGATIVE, equiv on -> warm hits DEF_EQ cache.
        (1, 1, true, false), // dfn=?=foo POSITIVE, equiv OFF -> warm hits DEF_EQ cache.
        (2, 1, false, true), // dfn=?=foo POSITIVE, equiv ON  -> warm hits EQUIV manager.
        (3, 1, true, false), // g dfn=?=g foo POSITIVE, equiv OFF -> warm hits DEF_EQ cache.
    ];
    for &(lo, exp_cold, want_cache, want_equiv) in cases {
        let i = idx(0, lo);
        let n = native(i);
        let j = f(i);
        assert_eq!(
            n, j,
            "transparency lo={lo}: native {n:#07b} != JIT {j:#07b}"
        );
        let cold = n & 1;
        let warm = (n >> 1) & 1;
        let eq = (n >> 2) & 1;
        let cache_adv = (n >> 3) & 1;
        let equiv_adv = (n >> 4) & 1;
        assert_eq!(cold, exp_cold, "lo={lo}: cold verdict");
        assert_eq!(
            warm, cold,
            "lo={lo}: WARM (cached) verdict must EQUAL COLD (recomputed) — hit==miss"
        );
        assert_eq!(eq, 1, "lo={lo}: cold==warm bit");
        assert_eq!(
            cache_adv == 1,
            want_cache,
            "lo={lo}: def_eq cache hit advance"
        );
        assert_eq!(equiv_adv == 1, want_equiv, "lo={lo}: equiv hit advance");
    }
    // Batch with repeats: determinism + native==JIT over a repeated stream.
    let stream = [0u64, 1, 2, 3, 0, 2, 1, 3, 3, 0];
    for &lo in &stream {
        let i = idx(0, lo);
        assert_eq!(native(i), f(i), "batch-repeat lo={lo}: native != JIT");
    }
    eprintln!(
        "transparency: hit==miss on every scenario, native==JIT; def_eq-cache AND equiv hit counters advance"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 3 — THE #1773 GUARD (centerpiece): a context-dependent NEGATIVE. Context A
// caches `(λ_.y) x =?= foo` = REJECT (y:=bar). The leak: pop x (out of the later
// context), refine y:=foo. Context B's CORRECT verdict is ACCEPT.
//   AWARE (guard):   x out of ctx B -> recompute -> ACCEPT (SOUND).
//   BLIND (no guard): stale cache hit -> REJECT (UNSOUND).
//   NOCACHE (base):   recompute both -> ACCEPT (the ground truth).
// Bit layout: bit0 vA, bit1 vB, bit2 recompute-guard tripped, bit3 cache-hit-in-B.
// ════════════════════════════════════════════════════════════════════════════
const NOCACHE: u64 = 0;
const AWARE: u64 = 1;
const BLIND: u64 = 2;

#[test]
fn cache_guard_1773_soundness_centerpiece() {
    let buf = jit(TIR, "defeq_cache_root");
    let f: RootFn = unsafe { std::mem::transmute(bind(&buf, "defeq_cache_root")) };

    let run = |mode: u64| -> u64 {
        let i = idx(1, mode);
        let n = native(i);
        let j = f(i);
        assert_eq!(n, j, "guard mode={mode}: native {n:#06b} != JIT {j:#06b}");
        j
    };
    let nocache = run(NOCACHE);
    let aware = run(AWARE);
    let blind = run(BLIND);

    let va = |r: u64| r & 1;
    let vb = |r: u64| (r >> 1) & 1;
    let recompute = |r: u64| (r >> 2) & 1;
    let hit_in_b = |r: u64| (r >> 3) & 1;

    // Context A always rejects (y:=bar; whnf-> bar != foo).
    assert_eq!(va(nocache), 0, "ctx A must REJECT (nocache)");
    assert_eq!(va(aware), 0, "ctx A must REJECT (aware)");
    assert_eq!(va(blind), 0, "ctx A must REJECT (blind)");

    // GROUND TRUTH: context B correctly ACCEPTS (y:=foo, x discarded).
    assert_eq!(vb(nocache), 1, "NOCACHE ctx B is the ground truth: ACCEPT");

    // AWARE: the #1773 guard recomputes (x out of ctx B) -> ACCEPT (SOUND).
    assert_eq!(
        vb(aware),
        1,
        "AWARE ctx B must ACCEPT — the #1773 guard recomputes, verdict is SOUND"
    );
    assert_eq!(
        recompute(aware),
        1,
        "AWARE must have tripped the out_of_context guard (recompute)"
    );
    assert_eq!(
        hit_in_b(aware),
        1,
        "AWARE must have hit the cache in ctx B (the stale entry was consulted)"
    );

    // BLIND: the guard is REMOVED -> trusts the stale negative -> REJECT (UNSOUND).
    assert_eq!(
        vb(blind),
        0,
        "BLIND ctx B REJECTS — the stale negative is trusted (UNSOUND)"
    );
    assert_eq!(
        hit_in_b(blind),
        1,
        "BLIND must have hit the cache in ctx B (same stale entry)"
    );
    assert_eq!(
        recompute(blind),
        0,
        "BLIND must NOT recompute (the guard is gone)"
    );

    // THE DECISIVE DIVERGENCE: AWARE accepts where BLIND rejects, native==JIT both.
    assert_ne!(
        vb(aware),
        vb(blind),
        "the #1773 guard must FLIP the ctx-B verdict vs the guard-removed blind control — this is the whole point"
    );
    assert_eq!(
        vb(aware),
        vb(nocache),
        "the guarded verdict must equal the uncached ground truth (both SOUND)"
    );
    eprintln!(
        "centerpiece: ctx A reject; ctx B AWARE=ACCEPT (guard recomputes, SOUND) vs BLIND=REJECT (stale, UNSOUND); NOCACHE=ACCEPT ground truth; native==JIT"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 4 — the equiv_manager union-find: add_equiv records a proven equality and
// a later identical query short-circuits via the union-find; a POISONED equiv
// (a WRONG entry) flips a verdict, proving the union-find is consulted (and why
// only PROVEN equivs may be added).
// lo0 bit layout: bit0 v1, bit1 v2, bit2 equiv-hit-adv. lo1/lo2: bit0 verdict.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn cache_equiv_manager_union_find() {
    let buf = jit(TIR, "defeq_cache_root");
    let f: RootFn = unsafe { std::mem::transmute(bind(&buf, "defeq_cache_root")) };

    let run = |lo: u64| -> u64 {
        let i = idx(2, lo);
        let n = native(i);
        let j = f(i);
        assert_eq!(n, j, "equiv lo={lo}: native {n:#05b} != JIT {j:#05b}");
        j
    };
    // lo0: transparency — 2nd query short-circuits via the union-find.
    let t = run(0);
    assert_eq!(t & 1, 1, "equiv lo0: v1 (delta) ACCEPT");
    assert_eq!(
        (t >> 1) & 1,
        1,
        "equiv lo0: v2 ACCEPT (union-find short-circuit)"
    );
    assert_eq!((t >> 1) & 1, t & 1, "equiv lo0: hit==miss verdict");
    assert_eq!(
        (t >> 2) & 1,
        1,
        "equiv lo0: equiv hit counter advanced (union-find consulted)"
    );
    // lo1 POISON vs lo2 CLEAN — the wrong equiv entry FLIPS foo=?=bar.
    let poison = run(1);
    let clean = run(2);
    assert_eq!(clean & 1, 0, "equiv lo2 CLEAN: foo=?=bar REJECT");
    assert_eq!(
        poison & 1,
        1,
        "equiv lo1 POISON: foo=?=bar ACCEPT (WRONG) — proves the union-find is consulted"
    );
    assert_ne!(
        poison & 1,
        clean & 1,
        "the poisoned equiv MUST flip the verdict"
    );
    eprintln!(
        "equiv: add_equiv short-circuit (hit==miss), poisoned-equiv flips foo=?=bar accept<->reject; native==JIT"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 5 — branch-sharing (#3402): recursor congruence via branch_sharing_compare,
// the verified-pair memo, and a POISONED verified-pair that flips a verdict.
// lo0 bit layout: bit0 verdict, bit1 verified-pairs advanced. lo1/lo2: bit0 verdict.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn cache_branch_sharing_3402() {
    let buf = jit(TIR, "defeq_cache_root");
    let f: RootFn = unsafe { std::mem::transmute(bind(&buf, "defeq_cache_root")) };

    let run = |lo: u64| -> u64 {
        let i = idx(3, lo);
        let n = native(i);
        let j = f(i);
        assert_eq!(n, j, "branch lo={lo}: native {n:#04b} != JIT {j:#04b}");
        j
    };
    let congruent = run(0);
    assert_eq!(
        congruent & 1,
        1,
        "branch lo0: Bool.rec .. dfn .. =?= Bool.rec .. foo .. ACCEPT (congruence over delta)"
    );
    assert_eq!(
        (congruent >> 1) & 1,
        1,
        "branch lo0: verified_pairs populated (the memo was exercised)"
    );
    let clean = run(1);
    let poison = run(2);
    assert_eq!(clean & 1, 0, "branch lo1 CLEAN: bar/baz minors -> REJECT");
    assert_eq!(
        poison & 1,
        1,
        "branch lo2 POISON: pre-recorded (bar,baz) verified-pair -> ACCEPT (WRONG)"
    );
    assert_ne!(
        clean & 1,
        poison & 1,
        "the poisoned verified-pair MUST flip the verdict (the memo is consulted)"
    );
    eprintln!(
        "branch-sharing: recursor congruence accept + verified-pair memo; poisoned verified-pair flips; native==JIT"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 6 — poisoned-cache-VALUE control: inject a WRONG verdict into the def_eq
// cache and observe the JIT return it (the cache VALUE is genuinely consulted).
// lo0 clean -> REJECT ; lo1 poison {foo,bar}=true -> ACCEPT.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn cache_poisoned_value_control() {
    let buf = jit(TIR, "defeq_cache_root");
    let f: RootFn = unsafe { std::mem::transmute(bind(&buf, "defeq_cache_root")) };
    let run = |lo: u64| -> u64 {
        let i = idx(4, lo);
        let n = native(i);
        let j = f(i);
        assert_eq!(n, j, "poison-cache lo={lo}: native != JIT");
        j
    };
    let clean = run(0);
    let poison = run(1);
    assert_eq!(clean, 0, "clean foo=?=bar REJECT");
    assert_eq!(
        poison, 1,
        "poisoned cache {{foo,bar}}=true -> ACCEPT (the JIT reads the stored verdict)"
    );
    assert_ne!(
        clean, poison,
        "the poisoned cache value MUST flip the verdict"
    );
    eprintln!(
        "poisoned-cache-value: the JIT genuinely consults the stored verdict (clean reject vs poison accept)"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 7 — ARMED golden corruption: flip compute_meta's FNV mix constant in the
// module text. The ExprMeta.hash (cat 5 meta probe) must DIVERGE, while every
// VERDICT (cats 1-4) stays IDENTICAL — the def_eq cache is verdict-transparent
// under hash perturbation (the scan is structural), and the differential is
// genuinely load-bearing on the hash path.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn cache_armed_fnv_corruption_control() {
    // baseline JIT.
    let buf = jit(TIR, "defeq_cache_root");
    let f: RootFn = unsafe { std::mem::transmute(bind(&buf, "defeq_cache_root")) };

    // native meta hashes.
    let native_h0 = native(idx(5, 0));
    let native_h1 = native(idx(5, 1));
    assert_eq!(f(idx(5, 0)), native_h0, "baseline meta hash0 native==JIT");
    assert_eq!(f(idx(5, 1)), native_h1, "baseline meta hash1 native==JIT");

    // ARMED: flip the FNV mix constant in the module text.
    let corrupted = TIR.replace("const u64 1099511628211", "const u64 1099511628213");
    assert!(corrupted != TIR, "corruption must change the text");
    let cbuf = jit(&corrupted, "defeq_cache_root(FNV-corrupted)");
    let cf: RootFn = unsafe { std::mem::transmute(bind(&cbuf, "defeq_cache_root")) };

    // (1) the meta hash MUST diverge (the differential is load-bearing).
    let ch0 = cf(idx(5, 0));
    let ch1 = cf(idx(5, 1));
    assert!(
        native_h0 != ch0,
        "FNV corruption MUST change meta hash0: {native_h0:#x} == {ch0:#x} (NOT load-bearing!)"
    );
    assert!(
        native_h1 != ch1,
        "FNV corruption MUST change meta hash1: {native_h1:#x} == {ch1:#x}"
    );

    // (2) every VERDICT is UNCHANGED (cache is verdict-transparent under hash perturbation).
    let verdict_idxs = [
        idx(1, AWARE),
        idx(1, BLIND),
        idx(1, NOCACHE),
        idx(2, 0),
        idx(2, 1),
        idx(2, 2),
        idx(3, 0),
        idx(3, 1),
        idx(3, 2),
        idx(4, 0),
        idx(4, 1),
        idx(0, 0),
        idx(0, 1),
        idx(0, 2),
        idx(0, 3),
    ];
    for &i in &verdict_idxs {
        assert_eq!(
            cf(i),
            f(i),
            "FNV corruption must NOT change verdict at idx={i:#x} (structural scan is hash-independent)"
        );
    }
    eprintln!(
        "armed(FNV): meta hash diverges {native_h0:#x} != {ch0:#x} (load-bearing) while EVERY verdict is unchanged (cache verdict-transparent under hash perturbation)"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 8 — the full native==JIT sweep over every (cat, lo) plus a repeated
// stream, plus a POISONED PUSH shim showing the JIT genuinely runs the cache
// store (a corrupt DefEqEntry push flips a would-be transparent verdict).
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn cache_full_native_jit_sweep_and_poison_push() {
    let buf = jit(TIR, "defeq_cache_root");
    let f: RootFn = unsafe { std::mem::transmute(bind(&buf, "defeq_cache_root")) };

    let mut n = 0u64;
    let cats: &[(u64, u64)] = &[(0, 4), (1, 3), (2, 3), (3, 3), (4, 2), (5, 2)];
    for &(cat, hi) in cats {
        for lo in 0..hi {
            let i = idx(cat, lo);
            assert_eq!(native(i), f(i), "sweep cat={cat} lo={lo}: native != JIT");
            n += 1;
        }
    }
    assert!(n >= 17, "sweep too small: {n}");

    // POISONED-CACHE-store control: a DefEqEntry push shim that flips the stored
    // verdict bit. On the transparency negative pair (cat0 lo0), the WARM read of
    // the poisoned store returns the flipped (accept) verdict — proving the JIT
    // machine code genuinely WRITES to and READS from the cache store.
    extern "C" fn v_push_entry_POISON(v: *mut Vec<rn::DefEqEntry>, val: *const rn::DefEqEntry) {
        unsafe {
            let mut e = std::ptr::read(val);
            e.v = if e.v == 0 { 1 } else { 0 }; // flip the stored verdict
            (*v).push(e);
        }
    }
    let mut ext = externs();
    ext.insert(M_VPUSH_ENTRY.to_string(), v_push_entry_POISON as *const u8);
    let pbuf = jit_with(TIR, "defeq_cache_root(poison-store)", &ext);
    let pf: RootFn = unsafe { std::mem::transmute(bind(&pbuf, "defeq_cache_root")) };

    // cat0 lo0 = dfn=?=bar (cold REJECT, cached). With the poisoned store the
    // WARM read returns the flipped ACCEPT -> warm != cold (transparency broken
    // by the poison, proving the store is genuinely consulted).
    let clean0 = f(idx(0, 0));
    let poison0 = pf(idx(0, 0));
    let clean_warm = (clean0 >> 1) & 1;
    let poison_warm = (poison0 >> 1) & 1;
    assert_eq!(clean_warm, clean0 & 1, "clean: warm==cold (transparent)");
    assert_ne!(
        poison_warm, clean_warm,
        "poisoned DefEqEntry store MUST flip the WARM verdict — proves the JIT writes+reads the cache store"
    );
    eprintln!(
        "sweep: {n} (cat,lo) native==JIT; poisoned-store flips the warm verdict (store genuinely consulted)"
    );
}
