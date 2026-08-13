// R18 — THE QUOTIENT MACHINERY, native == JIT over Clean's second soundness-
// critical trusted surface (the companion to R17's inductive-soundness gate),
// re-composed on the full modern stack (real Names + full Level + production
// compute_meta) and compiled through Trust (Rust -> MIR -> trust-ir -> trust-cg
// -> machine code).
//
// TWO SURFACES:
//   (b) THE 5 AXIOM TYPES the kernel ASSERTS as quotient axioms (a wrong type is
//       a LIE — a route to False): quot_type / quot_mk_type / quot_lift_type /
//       quot_ind_type / quot_sound_type — each built BIT-IDENTICAL native == JIT
//       (deep structural deep_eq + ExprMeta word), real-Name cached_hashes
//       pinned to the R4-R7 murmur-chain goldens.
//   (a) THE IOTA REDUCTION: `Quot.lift f h (Quot.mk r a)` reduces to `f a`
//       (payload-deep) + a stuck non-redex, native == JIT.
//   THE LOAD-BEARING SOUNDNESS PROOF (centerpiece): a corrupted axiom type (the
//       EXACT latent off-by-one the quot.rs SOUNDNESS comments warn about for
//       quot_lift_type; a swapped-argument corruption of quot_sound_type)
//       DIVERGES from the correct type native == JIT; and a POISONED iota oracle
//       (a reduce that returns the wrong term) DIVERGES from the correct
//       reduction native == JIT.
//
// Slice: crates/trust-cg-codegen/tests/slices/clean_quotient_slice.rs
// Emit (per root; trust-ir main; NO frontend changes):
//   trust_ir_mir --mir-emit-closure <root> <out.tir>
//   roots: quot_axiom_root | quot_iota_root | quot_names_probe_root
//
// Per-process under `perl -e 'alarm 600; exec @ARGV' -- <bin> --test-threads=1`.
#![allow(clippy::all)]
#![allow(dead_code)]
#![allow(non_snake_case)]
#![allow(unused_imports)]

use std::collections::HashMap;
use std::mem::MaybeUninit;
use std::sync::Arc;
use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

// The native oracle: the slice compiled as a Rust module.
#[path = "slices/clean_quotient_slice.rs"]
pub mod rn;

// The VERBATIM MIR-emitted trust-ir closures (validate_module = 0 each).
const AXIOM_TIR: &str = include_str!("clean_quot_axiom.tir");
const IOTA_TIR: &str = include_str!("clean_quot_iota.tir");
const NAMES_TIR: &str = include_str!("clean_quot_names.tir");

fn tir(root: &str) -> &'static str {
    match root {
        "quot_axiom_root" => AXIOM_TIR,
        "quot_iota_root" => IOTA_TIR,
        "quot_names_probe_root" => NAMES_TIR,
        _ => panic!("unknown root {root}"),
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
struct FatPair {
    ptr: *const u8,
    len: u64,
}

// ════════════════════════════════════════════════════════════════════════════
// Shims — the bodyless extern leaves. The R8/R17 shim set (retyped onto this
// slice's `rn` types), trimmed to the Expr/Level/Name/Literal families this
// module reaches, plus the two ptr::write<Expr>/<Name> leaves the roots use.
// ════════════════════════════════════════════════════════════════════════════

// allocator
extern "C" fn is_rust_alloc(size: usize, align: usize) -> *mut u8 {
    unsafe { std::alloc::alloc(std::alloc::Layout::from_size_align(size, align).expect("layout")) }
}
extern "C" fn is_rust_dealloc(ptr: *mut u8, size: usize, align: usize) {
    unsafe {
        std::alloc::dealloc(
            ptr,
            std::alloc::Layout::from_size_align(size, align).expect("layout"),
        );
    }
}
extern "C" fn is_rust_realloc(ptr: *mut u8, size: usize, align: usize, new_size: usize) -> *mut u8 {
    unsafe {
        std::alloc::realloc(
            ptr,
            std::alloc::Layout::from_size_align(size, align).expect("layout"),
            new_size,
        )
    }
}

// num / cmp primitives
extern "C" fn is_sat_add(a: u32, b: u32) -> u32 {
    a.saturating_add(b)
}
extern "C" fn is_sat_sub(a: u32, b: u32) -> u32 {
    a.saturating_sub(b)
}
extern "C" fn is_wrap_mul_u64(a: u64, b: u64) -> u64 {
    a.wrapping_mul(b)
}
extern "C" fn is_wrap_mul_usize(a: usize, b: usize) -> usize {
    a.wrapping_mul(b)
}
extern "C" fn is_max_u8(a: u8, b: u8) -> u8 {
    a.max(b)
}
extern "C" fn is_max_u32(a: u32, b: u32) -> u32 {
    a.max(b)
}
extern "C" fn is_min_u32(a: u32, b: u32) -> u32 {
    a.min(b)
}

// Arc leaves
extern "C" fn is_arc_expr_clone(sret: *mut Arc<rn::Expr>, this: *const Arc<rn::Expr>) {
    unsafe {
        std::ptr::write(sret, Arc::clone(&*this));
    }
}
extern "C" fn is_arc_lvl_clone(sret: *mut Arc<rn::Level>, this: *const Arc<rn::Level>) {
    unsafe {
        std::ptr::write(sret, Arc::clone(&*this));
    }
}
extern "C" fn is_arc_name_clone(sret: *mut Arc<rn::Name>, this: *const Arc<rn::Name>) {
    unsafe {
        std::ptr::write(sret, Arc::clone(&*this));
    }
}
extern "C" fn is_arc_expr_as_ref(arc_ref: *const *const u8) -> *const rn::Expr {
    unsafe { (*arc_ref).add(16) as *const rn::Expr }
}
extern "C" fn is_arc_str_from(sret: *mut u8, pair: *const FatPair) {
    unsafe {
        let p = *pair;
        let s = std::str::from_utf8(std::slice::from_raw_parts(p.ptr, p.len as usize))
            .expect("Arc::<str>::from shim received non-UTF8 bytes");
        let a: Arc<str> = Arc::from(s);
        std::ptr::write(sret as *mut Arc<str>, a);
    }
}
extern "C" fn is_arc_str_deref(sret: *mut FatPair, arc_slot: *const Arc<str>) {
    unsafe {
        let a: &Arc<str> = &*arc_slot;
        let s: &str = &**a;
        *sret = FatPair {
            ptr: s.as_ptr(),
            len: s.len() as u64,
        };
    }
}
extern "C" fn is_arc_str_clone(sret: *mut Arc<str>, this: *const Arc<str>) {
    unsafe {
        std::ptr::write(sret, Arc::clone(&*this));
    }
}

// clones
extern "C" fn is_opt_expr_clone(sret: *mut Option<rn::Expr>, this: *const Option<rn::Expr>) {
    unsafe {
        std::ptr::write(sret, (*this).clone());
    }
}
extern "C" fn is_vec_lvl_clone(sret: *mut Vec<rn::Level>, this: *const Vec<rn::Level>) {
    unsafe {
        std::ptr::write(sret, (*this).clone());
    }
}

// ptr::write leaves (the roots write Expr / Name through the sret pointer)
extern "C" fn is_ptr_write_expr(dst: *mut rn::Expr, val: *const rn::Expr) {
    unsafe {
        std::ptr::write(dst, std::ptr::read(val));
    }
}
extern "C" fn is_ptr_write_name(dst: *mut rn::Name, val: *const rn::Name) {
    unsafe {
        std::ptr::write(dst, std::ptr::read(val));
    }
}

// Vec<T> op families (owned, big payload passed by pointer)
macro_rules! is_vec_shims {
    ($new:ident, $push:ident, $pop:ident, $len:ident, $index:ident, $deref:ident, $ty:ty) => {
        #[allow(dead_code)]
        extern "C" fn $new(sret: *mut Vec<$ty>) {
            unsafe {
                std::ptr::write(sret, Vec::new());
            }
        }
        #[allow(dead_code)]
        extern "C" fn $push(vec: *mut Vec<$ty>, value: *const $ty) {
            unsafe {
                let v = std::ptr::read(value);
                (*vec).push(v);
            }
        }
        #[allow(dead_code)]
        extern "C" fn $pop(sret: *mut Option<$ty>, vec: *mut Vec<$ty>) {
            unsafe {
                std::ptr::write(sret, (*vec).pop());
            }
        }
        #[allow(dead_code)]
        extern "C" fn $len(vec: *const Vec<$ty>) -> u64 {
            unsafe { (*vec).len() as u64 }
        }
        #[allow(dead_code)]
        extern "C" fn $index(vec: *const Vec<$ty>, idx: u64) -> *const $ty {
            unsafe {
                let s: &[$ty] = (*vec).as_slice();
                assert!((idx as usize) < s.len(), "vec index oob");
                s.as_ptr().add(idx as usize)
            }
        }
        #[allow(dead_code)]
        extern "C" fn $deref(sret: *mut (*const $ty, usize), vec: *const Vec<$ty>) {
            unsafe {
                let s: &[$ty] = (*vec).as_slice();
                std::ptr::write(sret, (s.as_ptr(), s.len()));
            }
        }
    };
}
is_vec_shims!(
    iv_env_new,
    iv_env_push,
    iv_env_pop,
    iv_env_len,
    iv_env_index,
    iv_env_deref,
    (rn::Name, Option<rn::Expr>)
);
is_vec_shims!(
    iv_ctors_new,
    iv_ctors_push,
    iv_ctors_pop,
    iv_ctors_len,
    iv_ctors_index,
    iv_ctors_deref,
    (rn::Name, u32)
);
is_vec_shims!(
    iv_lvl_new,
    iv_lvl_push,
    iv_lvl_pop,
    iv_lvl_len,
    iv_lvl_index,
    iv_lvl_deref,
    rn::Level
);
is_vec_shims!(
    iv_expr_new,
    iv_expr_push,
    iv_expr_pop,
    iv_expr_len,
    iv_expr_index,
    iv_expr_deref,
    rn::Expr
);

// Vec<Expr> mut-slice access + slice reverse (get_app_args builds+reverses)
extern "C" fn iv_expr_deref_mut(sret: *mut (*mut rn::Expr, usize), v: *mut Vec<rn::Expr>) {
    unsafe {
        let s: &mut [rn::Expr] = (*v).as_mut_slice();
        std::ptr::write(sret, (s.as_mut_ptr(), s.len()));
    }
}
extern "C" fn is_expr_slice_reverse(slice_ref: *const (*mut rn::Expr, usize)) {
    unsafe {
        let (ptr, len) = *slice_ref;
        let s: &mut [rn::Expr] = std::slice::from_raw_parts_mut(ptr, len);
        s.reverse();
    }
}

// KaniHasher hash leaves (single u64 state word) + discriminant
const IS_KANI_MAGIC: u64 = 0x517cc1b727220a95;
extern "C" fn is_hash_u32(value: *const u32, state: *mut u64) {
    unsafe {
        let i = *value as u64;
        let s = (*state) ^ i;
        *state = s.wrapping_mul(IS_KANI_MAGIC);
    }
}
extern "C" fn is_hash_u64(value: *const u64, state: *mut u64) {
    unsafe {
        let i = *value;
        let s = (*state) ^ i;
        *state = s.wrapping_mul(IS_KANI_MAGIC);
    }
}
extern "C" fn is_hash_isize(value: *const isize, state: *mut u64) {
    unsafe {
        let i = *value as u64;
        let s = (*state) ^ i;
        *state = s.wrapping_mul(IS_KANI_MAGIC);
    }
}
extern "C" fn is_discriminant_level(
    sret: *mut std::mem::Discriminant<rn::Level>,
    this: *const rn::Level,
) {
    unsafe {
        std::ptr::write(sret, std::mem::discriminant(&*this));
    }
}
struct IsKani {
    state: u64,
}
impl std::hash::Hasher for IsKani {
    fn finish(&self) -> u64 {
        self.state
    }
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.state = self.state.wrapping_mul(31).wrapping_add(b as u64);
        }
    }
    fn write_u8(&mut self, i: u8) {
        self.state ^= i as u64;
        self.state = self.state.wrapping_mul(IS_KANI_MAGIC);
    }
    fn write_u16(&mut self, i: u16) {
        self.state ^= i as u64;
        self.state = self.state.wrapping_mul(IS_KANI_MAGIC);
    }
    fn write_u32(&mut self, i: u32) {
        self.state ^= i as u64;
        self.state = self.state.wrapping_mul(IS_KANI_MAGIC);
    }
    fn write_u64(&mut self, i: u64) {
        self.state ^= i;
        self.state = self.state.wrapping_mul(IS_KANI_MAGIC);
    }
    fn write_u128(&mut self, i: u128) {
        self.write_u64(i as u64);
        self.write_u64((i >> 64) as u64);
    }
    fn write_usize(&mut self, i: usize) {
        self.write_u64(i as u64);
    }
}
extern "C" fn is_hash_discriminant_level(
    value: *const std::mem::Discriminant<rn::Level>,
    state: *mut u64,
) {
    use std::hash::{Hash, Hasher};
    unsafe {
        let mut h = IsKani { state: *state };
        (*value).hash(&mut h);
        *state = h.finish();
    }
}
extern "C" fn is_hash_arc_level(arcptr: *const Arc<rn::Level>, state: *mut u64) {
    use std::hash::{Hash, Hasher};
    unsafe {
        let lvl: &rn::Level = &*(*arcptr);
        let mut h = IsKani { state: *state };
        lvl.hash(&mut h);
        *state = h.finish();
    }
}

// ════════════════════════════════════════════════════════════════════════════
// The hash-independent structural classifier (R17 order/discipline).
// ════════════════════════════════════════════════════════════════════════════
fn shim_for(n: &str) -> Option<*const u8> {
    let has = |s: &str| n.contains(s);
    // primitives
    if has("3numm14saturating_add") {
        return Some(is_sat_add as *const u8);
    }
    if has("3numm14saturating_sub") {
        return Some(is_sat_sub as *const u8);
    }
    if has("3numy12wrapping_mul") {
        return Some(is_wrap_mul_u64 as *const u8);
    }
    if has("3numj12wrapping_mul") {
        return Some(is_wrap_mul_usize as *const u8);
    }
    if has("3cmp3Ord3max") {
        return Some(if has("_RNvYh") {
            is_max_u8 as *const u8
        } else {
            is_max_u32 as *const u8
        });
    }
    if has("3cmp3Ord3min") {
        return Some(is_min_u32 as *const u8);
    }

    // hash + discriminant
    if has("hash5implsmNt") && has("4Hash4hash") {
        return Some(is_hash_u32 as *const u8);
    }
    if has("hash5implsyNt") && has("4Hash4hash") {
        return Some(is_hash_u64 as *const u8);
    }
    if has("hash5implsiNt") && has("4Hash4hash") {
        return Some(is_hash_isize as *const u8);
    }
    if has("12Discriminant") && has("4hash4Hash4hash") {
        return Some(is_hash_discriminant_level as *const u8);
    }
    if has("3Arc") && has("5Level") && has("4hash4Hash4hash") {
        return Some(is_hash_arc_level as *const u8);
    }
    if has("3mem12discriminant") && has("5Level") && !has("4Hash") {
        return Some(is_discriminant_level as *const u8);
    }

    // ptr::write (the sret roots) — Expr / Name
    if has("3ptr5write") {
        if has("4ExprE") {
            return Some(is_ptr_write_expr as *const u8);
        }
        if has("4NameE") {
            return Some(is_ptr_write_name as *const u8);
        }
    }

    // clones
    if has("5clone5Clone5clone") {
        if has("6Option") && has("4Expr") {
            return Some(is_opt_expr_clone as *const u8);
        }
        if has("3vec") && has("5Level") {
            return Some(is_vec_lvl_clone as *const u8);
        }
        if has("3Arc") {
            if has("3ArceE") {
                return Some(is_arc_str_clone as *const u8);
            }
            if has("4ExprE") {
                return Some(is_arc_expr_clone as *const u8);
            }
            if has("4NameE") {
                return Some(is_arc_name_clone as *const u8);
            }
            if has("5LevelE") {
                return Some(is_arc_lvl_clone as *const u8);
            }
        }
    }
    // Arc other
    if has("3Arc") && has("4ExprE") && has("6as_ref") {
        return Some(is_arc_expr_as_ref as *const u8);
    }
    if has("3Arce") && has("4from") {
        return Some(is_arc_str_from as *const u8);
    }
    if has("3Arce") && has("5deref5Deref5deref") {
        return Some(is_arc_str_deref as *const u8);
    }

    // slice ops
    if has("5sliceS") {
        if has("4Expr") && has("7reverse") {
            return Some(is_expr_slice_reverse as *const u8);
        }
    }

    // Vec<tuple> (env / ctors)
    if has("3VecT") {
        if has("4Name") && has("6Option") {
            if has("3new") {
                return Some(iv_env_new as *const u8);
            }
            if has("4push") {
                return Some(iv_env_push as *const u8);
            }
            if has("5deref5Deref5deref") {
                return Some(iv_env_deref as *const u8);
            }
        }
        if has("4Namem") {
            if has("3new") {
                return Some(iv_ctors_new as *const u8);
            }
            if has("4push") {
                return Some(iv_ctors_push as *const u8);
            }
            if has("5deref5Deref5deref") {
                return Some(iv_ctors_deref as *const u8);
            }
        }
    }

    // Vec<T> owned
    if has("3VecNt") {
        if has("4ExprE") {
            if has("3new") {
                return Some(iv_expr_new as *const u8);
            }
            if has("4push") {
                return Some(iv_expr_push as *const u8);
            }
            if has("3pop") {
                return Some(iv_expr_pop as *const u8);
            }
            if has("3len") {
                return Some(iv_expr_len as *const u8);
            }
            if has("9deref_mut") {
                return Some(iv_expr_deref_mut as *const u8);
            }
            if has("5deref5Deref5deref") {
                return Some(iv_expr_deref as *const u8);
            }
            if has("5index5Index") {
                return Some(iv_expr_index as *const u8);
            }
        }
        if has("5LevelE") {
            if has("3new") {
                return Some(iv_lvl_new as *const u8);
            }
            if has("4push") {
                return Some(iv_lvl_push as *const u8);
            }
            if has("3pop") {
                return Some(iv_lvl_pop as *const u8);
            }
            if has("3len") {
                return Some(iv_lvl_len as *const u8);
            }
            if has("5deref5Deref5deref") {
                return Some(iv_lvl_deref as *const u8);
            }
            if has("5index5Index") {
                return Some(iv_lvl_index as *const u8);
            }
        }
    }

    None
}

// ════════════════════════════════════════════════════════════════════════════
// JIT plumbing.
// ════════════════════════════════════════════════════════════════════════════
fn parse_validate(text: &str, what: &str) -> trust_ir::Module {
    let m = trust_ir::parser::parse_module(text).unwrap_or_else(|e| panic!("{what} parse: {e:?}"));
    let errs = trust_ir_build::validate_module(&m);
    assert!(errs.is_empty(), "{what} validate: {errs:?}");
    m
}

fn jit(text: &str, what: &str) -> trust_cg_codegen::jit::ExecutableBuffer {
    let module = parse_validate(text, what);
    let mut externs: HashMap<String, *const u8> = HashMap::new();
    externs.insert("__rust_alloc".to_string(), is_rust_alloc as *const u8);
    externs.insert("__rust_dealloc".to_string(), is_rust_dealloc as *const u8);
    externs.insert("__rust_realloc".to_string(), is_rust_realloc as *const u8);
    for f in &module.functions {
        if f.blocks.is_empty() {
            let shim = shim_for(&f.name)
                .unwrap_or_else(|| panic!("unclassified extern leaf `{}` in {what}", f.name));
            externs.insert(f.name.clone(), shim);
        }
    }
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(&module, &externs)
        .unwrap_or_else(|e| panic!("JIT compile {what} failed: {e:?}"))
        .buffer
}

fn bind(buf: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buf.get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("sym {sym} not found"))
        .as_ptr()
}

type AxiomFn = extern "C" fn(*mut rn::Expr, u64, u64);
type NameFn = extern "C" fn(*mut rn::Name, u64);

// ── native oracle wrappers (call the slice roots directly) ──
fn native_axiom(kind: u64, blind: u64) -> rn::Expr {
    let mut s = MaybeUninit::<rn::Expr>::uninit();
    unsafe {
        rn::quot_axiom_root(s.as_mut_ptr(), kind, blind);
        s.assume_init()
    }
}
fn native_iota(case: u64, poison: u64) -> rn::Expr {
    let mut s = MaybeUninit::<rn::Expr>::uninit();
    unsafe {
        rn::quot_iota_root(s.as_mut_ptr(), case, poison);
        s.assume_init()
    }
}
fn native_name(idx: u64) -> rn::Name {
    let mut s = MaybeUninit::<rn::Name>::uninit();
    unsafe {
        rn::quot_names_probe_root(s.as_mut_ptr(), idx);
        s.assume_init()
    }
}
fn jit_axiom(f: AxiomFn, kind: u64, blind: u64) -> rn::Expr {
    let mut s = MaybeUninit::<rn::Expr>::uninit();
    unsafe {
        f(s.as_mut_ptr(), kind, blind);
        s.assume_init()
    }
}
fn jit_iota(f: AxiomFn, case: u64, poison: u64) -> rn::Expr {
    let mut s = MaybeUninit::<rn::Expr>::uninit();
    unsafe {
        f(s.as_mut_ptr(), case, poison);
        s.assume_init()
    }
}
fn jit_name(f: NameFn, idx: u64) -> rn::Name {
    let mut s = MaybeUninit::<rn::Name>::uninit();
    unsafe {
        f(s.as_mut_ptr(), idx);
        s.assume_init()
    }
}

// ── payload-deep structural equality over rn::Expr (deref-ing JIT-built Arcs) ──
fn deep_eq(a: &rn::Expr, b: &rn::Expr) -> bool {
    use rn::ExprKind::*;
    if a.meta.raw() != b.meta.raw() {
        return false;
    }
    match (&a.kind, &b.kind) {
        (BVar(x), BVar(y)) => x == y,
        (FVar(x), FVar(y)) => x == y,
        (Sort(x), Sort(y)) => x == y,
        (Const(n1, l1), Const(n2, l2)) => rn::name_eq(n1, n2) && l1 == l2,
        (Lit(x), Lit(y)) => x == y,
        (App(f1, a1), App(f2, a2)) => deep_eq(f1, f2) && deep_eq(a1, a2),
        (Lam(b1, t1, y1), Lam(b2, t2, y2)) => b1 == b2 && deep_eq(t1, t2) && deep_eq(y1, y2),
        (Pi(b1, t1, y1), Pi(b2, t2, y2)) => b1 == b2 && deep_eq(t1, t2) && deep_eq(y1, y2),
        (Proj(n1, i1, e1), Proj(n2, i2, e2)) => rn::name_eq(n1, n2) && i1 == i2 && deep_eq(e1, e2),
        (MData(t1, e1), MData(t2, e2)) => t1 == t2 && deep_eq(e1, e2),
        _ => false,
    }
}

// walk the App spine to the head; true iff it is Const == Quot.lift.
fn head_is_quot_lift(e: &rn::Expr) -> bool {
    let mut cur = e;
    loop {
        match &cur.kind {
            rn::ExprKind::App(f, _) => cur = f,
            rn::ExprKind::Const(nm, _) => return rn::name_eq(nm, &rn::nm_quot_lift()),
            _ => return false,
        }
    }
}

// ── GOLDEN real-Name cached_hashes (the R4-R7-verified production murmur chain;
// slice construction == independent chunks_exact oracle == these) ──
const G_QUOT: u64 = 0xc8a0636f74fa7f5b;
const G_QUOT_MK: u64 = 0xf83a8452528971ff;
const G_QUOT_LIFT: u64 = 0x50c9c8de22267d5b;
const G_QUOT_IND: u64 = 0x3c891b6d9879d596;
const G_QUOT_SOUND: u64 = 0x1cc74f2845e6ffff;
const G_EQ: u64 = 0xdfbff609f865258f;
const G_U: u64 = 0xae572a66f1f7b2e8;
const G_V: u64 = 0x486e7075aebc6ca6;
const GOLDENS: [(u64, u64, &str); 8] = [
    (0, G_QUOT, "Quot"),
    (1, G_QUOT_MK, "Quot.mk"),
    (2, G_QUOT_LIFT, "Quot.lift"),
    (3, G_QUOT_IND, "Quot.ind"),
    (4, G_QUOT_SOUND, "Quot.sound"),
    (5, G_EQ, "Eq"),
    (6, G_U, "u"),
    (7, G_V, "v"),
];

// Independent murmur/mix oracle (chunks_exact form; distinct from the slice's
// index-loop) — a SECOND implementation of the production hash chain.
fn native_mix_hash(h: u64, k: u64) -> u64 {
    const M: u64 = 0xc6a4_a793_5bd1_e995;
    const R: u32 = 47;
    let mut k = k.wrapping_mul(M);
    k ^= k >> R;
    k ^= M;
    let h = h ^ k;
    h.wrapping_mul(M)
}
fn native_murmur(data: &[u8], seed: u64) -> u64 {
    const M: u64 = 0xc6a4_a793_5bd1_e995;
    const R: u32 = 47;
    let len = data.len();
    let mut h: u64 = seed ^ (len as u64).wrapping_mul(M);
    let mut chunks = data.chunks_exact(8);
    for block in &mut chunks {
        let mut k = u64::from_le_bytes(block.try_into().unwrap());
        k = k.wrapping_mul(M);
        k ^= k >> (R & 63);
        k = k.wrapping_mul(M);
        h ^= k;
        h = h.wrapping_mul(M);
    }
    let tail = chunks.remainder();
    for (i, &b) in tail.iter().enumerate() {
        h ^= (b as u64) << (i.wrapping_mul(8) & 63);
    }
    if !tail.is_empty() {
        h = h.wrapping_mul(M);
    }
    h ^= h >> (R & 63);
    h = h.wrapping_mul(M);
    h ^= h >> (R & 63);
    h
}
fn name_hash_dotted(s: &str) -> u64 {
    let mut h = 1723u64;
    for part in s.split('.') {
        if let Ok(nn) = part.parse::<u64>() {
            h = native_mix_hash(h, nn);
        } else {
            h = native_mix_hash(h, native_murmur(part.as_bytes(), 11));
        }
    }
    h
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 0 — golden cross-check: the real-Name murmur chain is three-way bit-
// identical (independent oracle == native slice construction == the pins).
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r18_golden_name_hashes() {
    for (idx, g, s) in GOLDENS {
        assert_eq!(name_hash_dotted(s), g, "independent murmur({s}) != pin");
        assert_eq!(
            native_name(idx).cached_hash,
            g,
            "native slice cached_hash({s}) != pin"
        );
    }
    eprintln!("golden: 8 quot names, three-way agree (independent oracle == slice == pin)");
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 1 — the 5 axiom types built BIT-IDENTICAL native == JIT (deep structural
// deep_eq + ExprMeta word), and their embedded real Names cached_hash-pinned.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r18_axiom_types_native_jit() {
    let buf = jit(tir("quot_axiom_root"), "quot_axiom_root");
    let f: AxiomFn = unsafe { std::mem::transmute(bind(&buf, "quot_axiom_root")) };
    let labels = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind", "Quot.sound"];
    for kind in 0u64..5 {
        let nv = native_axiom(kind, 0);
        let jv = jit_axiom(f, kind, 0);
        assert!(
            deep_eq(&nv, &jv),
            "{}: native != JIT (structure)",
            labels[kind as usize]
        );
        assert_eq!(
            nv.meta.raw(),
            jv.meta.raw(),
            "{}: meta word disagrees",
            labels[kind as usize]
        );
        eprintln!(
            "{}: native==JIT meta={:#018x}",
            labels[kind as usize],
            jv.meta.raw()
        );
    }
    // real-Name cached_hashes (via the probe root), native == JIT == golden.
    let nbuf = jit(tir("quot_names_probe_root"), "quot_names_probe_root");
    let nf: NameFn = unsafe { std::mem::transmute(bind(&nbuf, "quot_names_probe_root")) };
    for (idx, g, s) in GOLDENS {
        let nv = native_name(idx).cached_hash;
        let jv = jit_name(nf, idx).cached_hash;
        assert_eq!(nv, jv, "{s}: native cached_hash != JIT");
        assert_eq!(jv, g, "{s}: JIT cached_hash != golden");
    }
    eprintln!("axiom types: 5/5 bit-identical native==JIT; 8 real-Name cached_hashes pinned");
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 2 — CENTERPIECE (i): quot_lift_type corrupted with the EXACT latent
// off-by-one the source SOUNDNESS comment warns about (result BVar(3)=β ->
// BVar(2)=f) DIVERGES from the correct type, native == JIT for both configs.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r18_quot_lift_corruption_diverges() {
    let buf = jit(tir("quot_axiom_root"), "quot_axiom_root");
    let f: AxiomFn = unsafe { std::mem::transmute(bind(&buf, "quot_axiom_root")) };
    // correct (blind=0) and corrupted (blind=1), native == JIT on BOTH.
    let n_ok = native_axiom(2, 0);
    let j_ok = jit_axiom(f, 2, 0);
    let n_bad = native_axiom(2, 1);
    let j_bad = jit_axiom(f, 2, 1);
    assert!(deep_eq(&n_ok, &j_ok), "lift correct: native != JIT");
    assert!(deep_eq(&n_bad, &j_bad), "lift corrupted: native != JIT");
    // the corruption is OBSERVABLE: corrupt != correct, in machine code.
    assert!(
        !deep_eq(&j_ok, &j_bad),
        "JIT: corrupted lift type must DIVERGE from correct (soundness-critical)"
    );
    assert_ne!(
        j_ok.meta.raw(),
        j_bad.meta.raw(),
        "corrupted lift meta must differ"
    );
    // and the divergence is the SAME native and JIT (attribution).
    assert_eq!(
        deep_eq(&n_ok, &n_bad),
        deep_eq(&j_ok, &j_bad),
        "aware/blind divergence must agree native==JIT"
    );
    eprintln!(
        "quot_lift: the result-BVar off-by-one (β->f, the source-warned latent bug) DIVERGES native==JIT — a wrong axiom type is a LIE"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 3 — CENTERPIECE (ii): quot_sound_type (the soundness axiom) corrupted by
// a swapped hypothesis argument (r a b -> r b a) DIVERGES, native == JIT.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r18_quot_sound_corruption_diverges() {
    let buf = jit(tir("quot_axiom_root"), "quot_axiom_root");
    let f: AxiomFn = unsafe { std::mem::transmute(bind(&buf, "quot_axiom_root")) };
    let n_ok = native_axiom(4, 0);
    let j_ok = jit_axiom(f, 4, 0);
    let n_bad = native_axiom(4, 1);
    let j_bad = jit_axiom(f, 4, 1);
    assert!(deep_eq(&n_ok, &j_ok), "sound correct: native != JIT");
    assert!(deep_eq(&n_bad, &j_bad), "sound corrupted: native != JIT");
    assert!(
        !deep_eq(&j_ok, &j_bad),
        "JIT: corrupted sound type must DIVERGE from correct (soundness axiom is a LIE if wrong)"
    );
    assert_ne!(
        j_ok.meta.raw(),
        j_bad.meta.raw(),
        "corrupted sound meta must differ"
    );
    // the correct quot_lift blind must NOT accidentally equal quot_sound (sanity).
    eprintln!(
        "quot_sound: the swapped-argument hypothesis corruption (r a b -> r b a) DIVERGES native==JIT — the soundness axiom's type is soundness-critical"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 4 — THE IOTA REDUCTION: Quot.lift f h (Quot.mk r a) -> f a (payload-deep)
// + extra-arg reapplication + Quot.ind reduction + a STUCK non-redex, native ==
// JIT.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r18_iota_reduction_native_jit() {
    let buf = jit(tir("quot_iota_root"), "quot_iota_root");
    let f: AxiomFn = unsafe { std::mem::transmute(bind(&buf, "quot_iota_root")) };
    let agree = |case: u64, poison: u64| -> rn::Expr {
        let nv = native_iota(case, poison);
        let jv = jit_iota(f, case, poison);
        assert!(
            deep_eq(&nv, &jv),
            "iota case {case} poison {poison}: native != JIT"
        );
        assert_eq!(
            nv.meta.raw(),
            jv.meta.raw(),
            "iota case {case} poison {poison}: meta disagrees"
        );
        jv
    };
    // case 0: the redex reduces (head no longer Quot.lift).
    let r0 = agree(0, 0);
    assert!(
        !head_is_quot_lift(&r0),
        "case 0: Quot.lift-of-Quot.mk must REDUCE (head is f, not Quot.lift)"
    );
    // case 3: Quot.ind reduces to the SAME f a.
    let r3 = agree(3, 0);
    assert!(
        deep_eq(&r0, &r3),
        "Quot.lift and Quot.ind reductions must both give f a"
    );
    // case 1: the non-redex (major not Quot.mk) is left STUCK.
    let r1 = agree(1, 0);
    assert!(
        head_is_quot_lift(&r1),
        "case 1: non-redex (major not Quot.mk) must stay STUCK (head still Quot.lift)"
    );
    assert!(
        !deep_eq(&r0, &r1),
        "the stuck non-redex must differ from the reduced redex"
    );
    // case 2: redex + one extra arg -> (f a) extra (reduced, extra reapplied).
    let r2 = agree(2, 0);
    assert!(!head_is_quot_lift(&r2), "case 2: must reduce");
    assert!(
        !deep_eq(&r0, &r2),
        "case 2 (extra arg reapplied) must differ from case 0"
    );
    eprintln!(
        "iota: Quot.lift/Quot.ind-of-Quot.mk REDUCE to f a (payload-deep); the non-redex stays STUCK; native==JIT"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 5 — POISONED IOTA ORACLE: a reduce that extracts the wrong quoted value
// (major_args[1]=r instead of [2]=a) returns the WRONG term — it DIVERGES from
// the correct reduction, native == JIT for both configs.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r18_poisoned_iota_diverges() {
    let buf = jit(tir("quot_iota_root"), "quot_iota_root");
    let f: AxiomFn = unsafe { std::mem::transmute(bind(&buf, "quot_iota_root")) };
    let n_ok = native_iota(0, 0);
    let j_ok = jit_iota(f, 0, 0);
    let n_bad = native_iota(0, 1);
    let j_bad = jit_iota(f, 0, 1);
    assert!(deep_eq(&n_ok, &j_ok), "pristine iota: native != JIT");
    assert!(deep_eq(&n_bad, &j_bad), "poisoned iota: native != JIT");
    assert!(
        !deep_eq(&j_ok, &j_bad),
        "poisoned reduce must return a DIFFERENT term (the reduction is load-bearing in machine code)"
    );
    assert_ne!(
        j_ok.meta.raw(),
        j_bad.meta.raw(),
        "poisoned iota meta must differ"
    );
    eprintln!(
        "iota oracle: poisoning the quoted-value extraction (r not a) DIVERGES native==JIT — the machine code genuinely runs the ι-rule"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 6 — ARMED golden corruption: bump the anon seed (1723 -> 1724) in the
// names module text, re-JIT, and prove EVERY probed cached_hash diverges from
// its golden (native still matches) — the .tir is genuinely compiled+executed
// and the real-Name murmur/mix chain is load-bearing.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r18_armed_anon_seed_corruption() {
    let base = tir("quot_names_probe_root");
    // pristine JIT matches native + golden.
    {
        let buf = jit(base, "quot_names_probe_root");
        let nf: NameFn = unsafe { std::mem::transmute(bind(&buf, "quot_names_probe_root")) };
        for (idx, g, s) in GOLDENS {
            assert_eq!(
                jit_name(nf, idx).cached_hash,
                g,
                "pristine JIT cached_hash({s}) != golden"
            );
        }
    }
    // corrupt the unique anon seed constant.
    assert_eq!(
        base.matches("const u64 1723").count(),
        1,
        "anon seed 1723 must be unique in name_anon"
    );
    let corrupted = base.replace("const u64 1723", "const u64 1724");
    assert!(corrupted != base, "corruption must change the text");
    let buf = jit(&corrupted, "quot_names_probe_root(anon-seed-corrupted)");
    let nf: NameFn = unsafe { std::mem::transmute(bind(&buf, "quot_names_probe_root")) };
    for (idx, g, s) in GOLDENS {
        let jc = jit_name(nf, idx).cached_hash;
        assert_ne!(
            jc, g,
            "corrupted JIT cached_hash({s}) must DIVERGE from golden (chain is load-bearing)"
        );
        assert_eq!(
            native_name(idx).cached_hash,
            g,
            "native cached_hash({s}) unchanged (still golden)"
        );
    }
    eprintln!(
        "armed: bumping the anon seed 1723->1724 diverges ALL 8 cached_hashes (native still golden) — .tir genuinely compiled+executed"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 7 — module sanity + wiring: the axiom builders and the iota reduction are
// LIVE (bodied) in the compiled modules.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r18_module_sanity_and_wiring() {
    let axiom = parse_validate(tir("quot_axiom_root"), "quot_axiom_root");
    let ab = |sym: &str| {
        axiom
            .functions
            .iter()
            .any(|f| f.name == sym && !f.blocks.is_empty())
    };
    for sym in [
        "quot_type",
        "quot_mk_type",
        "quot_lift_type",
        "build_lift_proof_type",
        "make_eq_type",
        "quot_ind_type",
        "build_ind_hyp_type",
        "quot_sound_type",
    ] {
        assert!(ab(sym), "{sym} must be bodied in the axiom module");
    }
    let iota = parse_validate(tir("quot_iota_root"), "quot_iota_root");
    let ib = |sym: &str| {
        iota.functions
            .iter()
            .any(|f| f.name.contains(sym) && !f.blocks.is_empty())
    };
    for sym in [
        "try_quot_reduction",
        "try_quot_lift_reduction",
        "try_quot_ind_reduction",
        "whnf_inner",
        "name_eq",
    ] {
        assert!(ib(sym), "{sym} must be bodied in the iota module");
    }
    eprintln!(
        "sanity: 8 axiom builders + the iota reduction (lift/ind dispatch, name_eq, whnf) all LIVE (bodied)"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 8 — ARMED corruption of the AXIOM module: bump the anon seed (1723 ->
// 1724) in the axiom module text, re-JIT, and prove the JIT-built axiom type
// DIVERGES from the pristine native one (the embedded Const/Param real-Name
// hashes shift -> the whole ExprMeta tree shifts) — the axiom .tir is genuinely
// compiled+executed (not native-shadowed), and the real-Name construction is
// load-bearing inside the axiom TYPE.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r18_armed_axiom_module_corruption() {
    let base = tir("quot_axiom_root");
    // pristine JIT == native for all 5 kinds.
    {
        let buf = jit(base, "quot_axiom_root");
        let f: AxiomFn = unsafe { std::mem::transmute(bind(&buf, "quot_axiom_root")) };
        for kind in 0u64..5 {
            assert!(
                deep_eq(&native_axiom(kind, 0), &jit_axiom(f, kind, 0)),
                "pristine axiom {kind}: native != JIT"
            );
        }
    }
    assert_eq!(
        base.matches("const u64 1723").count(),
        1,
        "anon seed 1723 must be unique in the axiom module"
    );
    let corrupted = base.replace("const u64 1723", "const u64 1724");
    assert!(corrupted != base, "corruption must change the text");
    let buf = jit(&corrupted, "quot_axiom_root(anon-seed-corrupted)");
    let f: AxiomFn = unsafe { std::mem::transmute(bind(&buf, "quot_axiom_root")) };
    // every axiom kind's JIT-built type now diverges from the pristine native type.
    for kind in 0u64..5 {
        let nv = native_axiom(kind, 0);
        let jv = jit_axiom(f, kind, 0);
        assert!(
            !deep_eq(&nv, &jv),
            "corrupted axiom {kind}: JIT must DIVERGE from pristine native (name/meta chain load-bearing)"
        );
        assert_ne!(
            nv.meta.raw(),
            jv.meta.raw(),
            "corrupted axiom {kind}: meta must differ"
        );
    }
    eprintln!(
        "armed: bumping the anon seed in the AXIOM module shifts every axiom type's meta tree (native unchanged) — the axiom .tir is genuinely compiled+executed"
    );
}
