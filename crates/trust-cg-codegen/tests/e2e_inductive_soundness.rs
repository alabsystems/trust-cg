// R17 — THE INDUCTIVE-SOUNDNESS GATE, native == JIT over Clean's three
// soundness-critical inductive checks, re-composed on the full modern stack
// (real Names + full Level + production compute_meta + FVar LocalContext +
// pillar def_eq/whnf/infer), compiled through Trust (Rust -> MIR -> trust-ir ->
// trust-cg -> machine code).
//
// The three checks whose correctness IS the consistency of the logic for
// inductive types:
//   1. STRICT POSITIVITY          (inductive/mod.rs:409/451/490/661/698)
//   2. LARGE-ELIM-FROM-PROP       (env/elim_analysis.rs:38 + tc/infer.rs:808)
//   3. CTOR-RETURN (lean4#2125)   (inductive/mod.rs:854/752/710)
//
// THE LOAD-BEARING PROOF (centerpiece): for EACH check, a BLIND control that
// DROPS the soundness-critical sub-check ACCEPTS the corresponding unsound
// declaration where the AWARE (production) gate REJECTS — proven native == JIT
// for both configs, so each check is soundness-critical in compiled machine
// code (dropping it admits an inconsistency).
//
// Slice: crates/trust-cg-codegen/tests/slices/clean_inductive_soundness_slice.rs
// Emit (per root; trust-ir main; NO frontend changes):
//   trust_ir_mir --mir-emit-closure <root> <out.tir>
//   roots: positivity_root | ctor_return_root | elim_root
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
#[path = "slices/clean_inductive_soundness_slice.rs"]
pub mod rn;

// The VERBATIM MIR-emitted trust-ir closures (validate_module = 0 each).
const POSITIVITY_TIR: &str = include_str!("clean_inductive_positivity.tir");
const CTOR_RETURN_TIR: &str = include_str!("clean_inductive_ctor_return.tir");
const ELIM_TIR: &str = include_str!("clean_inductive_elim.tir");

fn tir(root: &str) -> &'static str {
    match root {
        "positivity_root" => POSITIVITY_TIR,
        "ctor_return_root" => CTOR_RETURN_TIR,
        "elim_root" => ELIM_TIR,
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
// Shims — the bodyless extern leaves the emit-closure leaves. Bodies are the R8
// (clean_fvar_opening_slice) shim set, retyped onto this slice's `rn` types,
// plus the R17-new leaves (CheckResult write; Vec<Constructor>/<InductiveType>/
// <usize>/<&Expr>; Result<(),InductiveError> Try). Bound to symbols by a
// hash-independent structural classifier (`shim_for`); jit_module fail-louds if
// any emitted extern is unresolved.
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
extern "C" fn is_arc_lvl_ne(a: *const Arc<rn::Level>, b: *const Arc<rn::Level>) -> bool {
    unsafe { !(*(*a) == *(*b)) }
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

// ptr::write leaves
extern "C" fn is_ptr_write_checkresult(dst: *mut rn::CheckResult, val: *const rn::CheckResult) {
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
    iv_name_new,
    iv_name_push,
    iv_name_pop,
    iv_name_len,
    iv_name_index,
    iv_name_deref,
    rn::Name
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
is_vec_shims!(
    iv_ld_new,
    iv_ld_push,
    iv_ld_pop,
    iv_ld_len,
    iv_ld_index,
    iv_ld_deref,
    rn::LocalDecl
);
is_vec_shims!(
    iv_ctor_new,
    iv_ctor_push,
    iv_ctor_pop,
    iv_ctor_len,
    iv_ctor_index,
    iv_ctor_deref,
    rn::Constructor
);
is_vec_shims!(
    iv_indty_new,
    iv_indty_push,
    iv_indty_pop,
    iv_indty_len,
    iv_indty_index,
    iv_indty_deref,
    rn::InductiveType
);

// Vec<usize>: usize is a SCALAR (8 bytes) — the ABI-faithful lowering passes the
// pushed element BY VALUE (emitted functy `(ptr, u64) -> ()`), not by pointer.
extern "C" fn iv_usize_new(sret: *mut Vec<usize>) {
    unsafe {
        std::ptr::write(sret, Vec::new());
    }
}
extern "C" fn iv_usize_push(vec: *mut Vec<usize>, value: usize) {
    unsafe {
        (*vec).push(value);
    }
}
extern "C" fn iv_usize_len(vec: *const Vec<usize>) -> u64 {
    unsafe { (*vec).len() as u64 }
}
extern "C" fn iv_usize_index(vec: *const Vec<usize>, idx: u64) -> *const usize {
    unsafe {
        let s: &[usize] = (*vec).as_slice();
        assert!((idx as usize) < s.len(), "usize vec idx oob");
        s.as_ptr().add(idx as usize)
    }
}
extern "C" fn iv_usize_is_empty(vec: *const Vec<usize>) -> bool {
    unsafe { (*vec).is_empty() }
}

// Vec<FVarId> (scalar element passed BY VALUE — the ABI-faithful lowering)
extern "C" fn iv_fid_new(sret: *mut Vec<rn::FVarId>) {
    unsafe {
        std::ptr::write(sret, Vec::new());
    }
}
extern "C" fn iv_fid_push(vec: *mut Vec<rn::FVarId>, value: u64) {
    unsafe {
        (*vec).push(rn::FVarId(value));
    }
}
extern "C" fn iv_fid_len(vec: *const Vec<rn::FVarId>) -> u64 {
    unsafe { (*vec).len() as u64 }
}
extern "C" fn iv_fid_index(vec: *const Vec<rn::FVarId>, idx: u64) -> *const rn::FVarId {
    unsafe {
        let s: &[rn::FVarId] = (*vec).as_slice();
        assert!((idx as usize) < s.len(), "vec_fid oob");
        s.as_ptr().add(idx as usize)
    }
}

// Vec<Level> mut-slice access + slice ops
extern "C" fn iv_lvl_index_mut(v: *mut Vec<rn::Level>, idx: u64) -> *mut rn::Level {
    unsafe {
        let s: &mut [rn::Level] = (*v).as_mut_slice();
        assert!((idx as usize) < s.len(), "lvl_index_mut oob");
        s.as_mut_ptr().add(idx as usize)
    }
}
extern "C" fn iv_lvl_deref_mut(sret: *mut (*mut rn::Level, usize), v: *mut Vec<rn::Level>) {
    unsafe {
        let s: &mut [rn::Level] = (*v).as_mut_slice();
        std::ptr::write(sret, (s.as_mut_ptr(), s.len()));
    }
}
extern "C" fn iv_lvl_is_empty(v: *const Vec<rn::Level>) -> bool {
    unsafe { (*v).is_empty() }
}
extern "C" fn is_lvl_slice_swap(fat: *const (*mut rn::Level, usize), i: u64, j: u64) {
    unsafe {
        let (data, _len) = *fat;
        std::ptr::swap(data.add(i as usize), data.add(j as usize));
    }
}
extern "C" fn is_lvl_slice_to_vec(
    sret: *mut Vec<rn::Level>,
    src: *const (*const rn::Level, usize),
) {
    unsafe {
        let (p, n) = *src;
        let s = std::slice::from_raw_parts(p, n);
        std::ptr::write(sret, s.to_vec());
    }
}
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
extern "C" fn is_constructor_slice_is_empty(fat: *const (*const rn::Constructor, usize)) -> bool {
    unsafe {
        let (_p, n) = *fat;
        n == 0
    }
}

// Vec<&Expr> / Vec<&Name> / Vec<&Level> / Vec<(&Level,&Level)> worklists
extern "C" fn iv_expr_ref_new(sret: *mut Vec<&'static rn::Expr>) {
    unsafe {
        std::ptr::write(sret, Vec::new());
    }
}
extern "C" fn iv_expr_ref_push(v: *mut Vec<&'static rn::Expr>, val: *const rn::Expr) {
    unsafe {
        (*v).push(&*val);
    }
}
extern "C" fn iv_expr_ref_pop(
    sret: *mut Option<&'static rn::Expr>,
    v: *mut Vec<&'static rn::Expr>,
) {
    unsafe {
        std::ptr::write(sret, (*v).pop());
    }
}
extern "C" fn iv_expr_ref_len(v: *const Vec<&'static rn::Expr>) -> u64 {
    unsafe { (*v).len() as u64 }
}
extern "C" fn iv_expr_ref_index(
    v: *const Vec<&'static rn::Expr>,
    idx: u64,
) -> *const &'static rn::Expr {
    unsafe {
        let s: &[&rn::Expr] = (*v).as_slice();
        assert!((idx as usize) < s.len(), "expr_ref idx oob");
        s.as_ptr().add(idx as usize)
    }
}
extern "C" fn iv_expr_ref_deref_mut(
    sret: *mut (*mut &'static rn::Expr, usize),
    v: *mut Vec<&'static rn::Expr>,
) {
    unsafe {
        let s: &mut [&rn::Expr] = (*v).as_mut_slice();
        std::ptr::write(sret, (s.as_mut_ptr(), s.len()));
    }
}
extern "C" fn is_expr_ref_slice_reverse(slice_ref: *const (*mut &'static rn::Expr, usize)) {
    unsafe {
        let (ptr, len) = *slice_ref;
        let s: &mut [&rn::Expr] = std::slice::from_raw_parts_mut(ptr, len);
        s.reverse();
    }
}
extern "C" fn iv_lvl_ref_push(v: *mut Vec<&'static rn::Level>, val: *const rn::Level) {
    unsafe {
        (*v).push(&*val);
    }
}
extern "C" fn iv_lvl_ref_pop(
    sret: *mut Option<&'static rn::Level>,
    v: *mut Vec<&'static rn::Level>,
) {
    unsafe {
        std::ptr::write(sret, (*v).pop());
    }
}
extern "C" fn iv_lvl_pair_push(
    v: *mut Vec<(&'static rn::Level, &'static rn::Level)>,
    val: *const (&'static rn::Level, &'static rn::Level),
) {
    unsafe {
        (*v).push(std::ptr::read(val));
    }
}
extern "C" fn iv_lvl_pair_pop(
    sret: *mut Option<(&'static rn::Level, &'static rn::Level)>,
    v: *mut Vec<(&'static rn::Level, &'static rn::Level)>,
) {
    unsafe {
        std::ptr::write(sret, (*v).pop());
    }
}
extern "C" fn iv_name_ref_new(sret: *mut Vec<&'static rn::Name>) {
    unsafe {
        std::ptr::write(sret, Vec::new());
    }
}
extern "C" fn iv_name_ref_push(v: *mut Vec<&'static rn::Name>, val: *const rn::Name) {
    unsafe {
        (*v).push(&*val);
    }
}
extern "C" fn iv_name_ref_pop(
    sret: *mut Option<&'static rn::Name>,
    v: *mut Vec<&'static rn::Name>,
) {
    unsafe {
        std::ptr::write(sret, (*v).pop());
    }
}

// `?` leaves: Try::branch / FromResidual::from_residual
extern "C" fn is_result_expr_branch(
    sret: *mut std::ops::ControlFlow<Result<std::convert::Infallible, rn::TypeError>, rn::Expr>,
    this: *const Result<rn::Expr, rn::TypeError>,
) {
    unsafe {
        let cf = match std::ptr::read(this) {
            Ok(v) => std::ops::ControlFlow::Continue(v),
            Err(e) => std::ops::ControlFlow::Break(Err(e)),
        };
        std::ptr::write(sret, cf);
    }
}
extern "C" fn is_result_expr_from_residual(
    sret: *mut Result<rn::Expr, rn::TypeError>,
    residual: *const Result<std::convert::Infallible, rn::TypeError>,
) {
    unsafe {
        let err = match std::ptr::read(residual) {
            Ok(_) => unreachable!(),
            Err(e) => e,
        };
        std::ptr::write(sret, Err(err));
    }
}
extern "C" fn is_result_lvl_branch(
    sret: *mut std::ops::ControlFlow<Result<std::convert::Infallible, rn::TypeError>, rn::Level>,
    this: *const Result<rn::Level, rn::TypeError>,
) {
    unsafe {
        let cf = match std::ptr::read(this) {
            Ok(v) => std::ops::ControlFlow::Continue(v),
            Err(e) => std::ops::ControlFlow::Break(Err(e)),
        };
        std::ptr::write(sret, cf);
    }
}
extern "C" fn is_result_lvl_from_residual(
    sret: *mut Result<rn::Level, rn::TypeError>,
    residual: *const Result<std::convert::Infallible, rn::TypeError>,
) {
    unsafe {
        let err = match std::ptr::read(residual) {
            Ok(_) => unreachable!(),
            Err(e) => e,
        };
        std::ptr::write(sret, Err(err));
    }
}
// Result<(), InductiveError> — the positivity / ctor_return `?` operator.
extern "C" fn is_result_unit_inderr_branch(
    sret: *mut std::ops::ControlFlow<Result<std::convert::Infallible, rn::InductiveError>, ()>,
    this: *const Result<(), rn::InductiveError>,
) {
    unsafe {
        let cf = match std::ptr::read(this) {
            Ok(v) => std::ops::ControlFlow::Continue(v),
            Err(e) => std::ops::ControlFlow::Break(Err(e)),
        };
        std::ptr::write(sret, cf);
    }
}
extern "C" fn is_result_unit_inderr_from_residual(
    sret: *mut Result<(), rn::InductiveError>,
    residual: *const Result<std::convert::Infallible, rn::InductiveError>,
) {
    unsafe {
        let err = match std::ptr::read(residual) {
            Ok(_) => unreachable!(),
            Err(e) => e,
        };
        std::ptr::write(sret, Err(err));
    }
}

// ref-to-ref PartialEq wrappers (core::cmp::impls, double-ptr receiver)
extern "C" fn is_lvl_ref_eq(a: *const *const rn::Level, b: *const *const rn::Level) -> bool {
    unsafe { (**a) == (**b) }
}
extern "C" fn is_lvl_ref_ne(a: *const *const rn::Level, b: *const *const rn::Level) -> bool {
    unsafe { (**a) != (**b) }
}
extern "C" fn is_lit_ref_eq(a: *const *const rn::Literal, b: *const *const rn::Literal) -> bool {
    unsafe { (**a) == (**b) }
}
extern "C" fn is_fvarid_ref_eq(a: *const *const rn::FVarId, b: *const *const rn::FVarId) -> bool {
    unsafe { (**a) == (**b) }
}
extern "C" fn is_u32_ref_eq(a: *const *const u32, b: *const *const u32) -> bool {
    unsafe { (**a) == (**b) }
}

// KaniHasher hash leaves (single u64 state word)
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
// The hash-independent structural classifier: maps a bodyless mangled symbol to
// its shim by demangled-meaning substrings (crate disambiguator ignored). Order
// matters: most-specific tokens first.
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

    // ptr::write
    if has("3ptr5write") && has("11CheckResult") {
        return Some(is_ptr_write_checkresult as *const u8);
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
    if has("3cmp5implsRINt") && has("3Arc") && has("5Level") && has("2ne") {
        return Some(is_arc_lvl_ne as *const u8);
    }

    // ref-to-ref PartialEq
    if has("3cmp5implsRm") && has("2eq") {
        return Some(is_u32_ref_eq as *const u8);
    }
    if has("3cmp5implsRNt") {
        if has("5Level") && has("2eq") {
            return Some(is_lvl_ref_eq as *const u8);
        }
        if has("5Level") && has("2ne") {
            return Some(is_lvl_ref_ne as *const u8);
        }
        if has("6FVarId") && has("2eq") {
            return Some(is_fvarid_ref_eq as *const u8);
        }
        if has("7Literal") && has("2eq") {
            return Some(is_lit_ref_eq as *const u8);
        }
    }

    // slice ops
    if has("5sliceS") {
        if has("11Constructor") && has("8is_empty") {
            return Some(is_constructor_slice_is_empty as *const u8);
        }
        if has("5Level") && has("4swap") {
            return Some(is_lvl_slice_swap as *const u8);
        }
        if has("5Level") && has("6to_vec") {
            return Some(is_lvl_slice_to_vec as *const u8);
        }
        if has("4Expr") && has("7reverse") {
            return Some(if has("5sliceSR") {
                is_expr_ref_slice_reverse as *const u8
            } else {
                is_expr_slice_reverse as *const u8
            });
        }
    }

    // Result Try/from_residual
    if has("6result") {
        let from_res = has("13from_residual");
        let branch = has("6branch");
        if has("14InductiveError") {
            if branch {
                return Some(is_result_unit_inderr_branch as *const u8);
            }
            if from_res {
                return Some(is_result_unit_inderr_from_residual as *const u8);
            }
        }
        if has("4Expr") && has("9TypeError") {
            if branch {
                return Some(is_result_expr_branch as *const u8);
            }
            if from_res {
                return Some(is_result_expr_from_residual as *const u8);
            }
        }
        if has("5Level") && has("9TypeError") {
            if branch {
                return Some(is_result_lvl_branch as *const u8);
            }
            if from_res {
                return Some(is_result_lvl_from_residual as *const u8);
            }
        }
    }

    // Vec<usize>
    if has("3VecjE") {
        if has("3new") {
            return Some(iv_usize_new as *const u8);
        }
        if has("4push") {
            return Some(iv_usize_push as *const u8);
        }
        if has("3len") {
            return Some(iv_usize_len as *const u8);
        }
        if has("8is_empty") {
            return Some(iv_usize_is_empty as *const u8);
        }
        if has("5index") {
            return Some(iv_usize_index as *const u8);
        }
    }

    // Vec<&T> (reference element)
    if has("3VecR") {
        if has("4ExprE") {
            if has("3new") {
                return Some(iv_expr_ref_new as *const u8);
            }
            if has("4push") {
                return Some(iv_expr_ref_push as *const u8);
            }
            if has("3pop") {
                return Some(iv_expr_ref_pop as *const u8);
            }
            if has("3len") {
                return Some(iv_expr_ref_len as *const u8);
            }
            if has("9deref_mut") {
                return Some(iv_expr_ref_deref_mut as *const u8);
            }
            if has("5index") {
                return Some(iv_expr_ref_index as *const u8);
            }
        }
        if has("4NameE") {
            if has("3new") {
                return Some(iv_name_ref_new as *const u8);
            }
            if has("4push") {
                return Some(iv_name_ref_push as *const u8);
            }
            if has("3pop") {
                return Some(iv_name_ref_pop as *const u8);
            }
        }
        if has("5LevelE") {
            if has("4push") {
                return Some(iv_lvl_ref_push as *const u8);
            }
            if has("3pop") {
                return Some(iv_lvl_ref_pop as *const u8);
            }
        }
    }

    // Vec<tuple>
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
            if has("5deref5Deref5deref") {
                return Some(iv_ctors_deref as *const u8);
            }
        }
        if has("3VecTR") && has("5Level") {
            if has("4push") {
                return Some(iv_lvl_pair_push as *const u8);
            }
            if has("3pop") {
                return Some(iv_lvl_pair_pop as *const u8);
            }
        }
    }

    // Vec<T> owned
    if has("3VecNt") {
        // deref_mut vs deref vs index vs index_mut vs len vs pop vs push vs new
        if has("4ExprE") {
            if has("3new") {
                return Some(iv_expr_new as *const u8);
            }
            if has("4push") {
                return Some(iv_expr_push as *const u8);
            }
            if has("3len") {
                return Some(iv_expr_len as *const u8);
            }
            if has("9deref_mut") {
                return Some(iv_expr_deref_mut as *const u8);
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
            if has("8is_empty") {
                return Some(iv_lvl_is_empty as *const u8);
            }
            if has("9index_mut") {
                return Some(iv_lvl_index_mut as *const u8);
            }
            if has("9deref_mut") {
                return Some(iv_lvl_deref_mut as *const u8);
            }
            if has("5index5Index") {
                return Some(iv_lvl_index as *const u8);
            }
            if has("5deref5Deref5deref") {
                return Some(iv_lvl_deref as *const u8);
            }
        }
        if has("6FVarIdE") {
            if has("3new") {
                return Some(iv_fid_new as *const u8);
            }
            if has("4push") {
                return Some(iv_fid_push as *const u8);
            }
            if has("3len") {
                return Some(iv_fid_len as *const u8);
            }
            if has("5index") {
                return Some(iv_fid_index as *const u8);
            }
        }
        if has("9LocalDeclE") {
            if has("3new") {
                return Some(iv_ld_new as *const u8);
            }
            if has("4push") {
                return Some(iv_ld_push as *const u8);
            }
            if has("3pop") {
                return Some(iv_ld_pop as *const u8);
            }
            if has("3len") {
                return Some(iv_ld_len as *const u8);
            }
            if has("5index") {
                return Some(iv_ld_index as *const u8);
            }
        }
        if has("11ConstructorE") {
            if has("3new") {
                return Some(iv_ctor_new as *const u8);
            }
            if has("4push") {
                return Some(iv_ctor_push as *const u8);
            }
            if has("3len") {
                return Some(iv_ctor_len as *const u8);
            }
            if has("5deref5Deref5deref") {
                return Some(iv_ctor_deref as *const u8);
            }
            if has("5index") {
                return Some(iv_ctor_index as *const u8);
            }
        }
        if has("13InductiveTypeE") {
            if has("3new") {
                return Some(iv_indty_new as *const u8);
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

type CheckFn = extern "C" fn(*mut rn::CheckResult, u64, u64);

fn native_call(root: u8, case: u64, blind: u64) -> (u64, u64, u64) {
    let mut cr = MaybeUninit::<rn::CheckResult>::uninit();
    let cr = unsafe {
        match root {
            0 => rn::positivity_root(cr.as_mut_ptr(), case, blind),
            1 => rn::ctor_return_root(cr.as_mut_ptr(), case, blind),
            _ => rn::elim_root(cr.as_mut_ptr(), case, blind),
        };
        cr.assume_init()
    };
    (cr.code, cr.name_hash, cr.ctor_meta)
}

fn jit_call(f: CheckFn, case: u64, blind: u64) -> (u64, u64, u64) {
    let mut cr = MaybeUninit::<rn::CheckResult>::uninit();
    let cr = unsafe {
        f(cr.as_mut_ptr(), case, blind);
        cr.assume_init()
    };
    (cr.code, cr.name_hash, cr.ctor_meta)
}

// GOLDEN real-Name cached_hashes (murmur chain == the R4-R7-verified production
// chain; native == JIT re-proves the JIT matches).
const GOLDEN_I: u64 = 0x7438329c63f700f5;
const GOLDEN_FOREST: u64 = 0x67467aab1408ef94;

// Independent murmur oracle (R8 e2e's, VERBATIM) — cross-checks GOLDEN_I/FOREST
// against a SECOND implementation of the production hash chain.
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
fn name_hash_of(s: &str) -> u64 {
    // single-component (no '.') from_string_uncached: anon(1723) -> str-part.
    native_mix_hash(1723, native_murmur(s.as_bytes(), 11))
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 0 — golden cross-check: the real-Name murmur chain is bit-identical
// across the slice's construction, the independent oracle, and the pins.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r17_golden_name_hashes() {
    assert_eq!(
        name_hash_of("I"),
        GOLDEN_I,
        "independent murmur('I') != pin"
    );
    assert_eq!(
        name_hash_of("Forest"),
        GOLDEN_FOREST,
        "independent murmur('Forest') != pin"
    );
    // and the native slice roots return exactly these (accept -> ind name I;
    // Forest-sibling rejection -> Forest).
    assert_eq!(
        native_call(0, 0, 0).1,
        GOLDEN_I,
        "positivity accept name_hash != GOLDEN_I"
    );
    assert_eq!(
        native_call(0, 4, 0).1,
        GOLDEN_FOREST,
        "positivity Forest-reject name_hash != GOLDEN_FOREST"
    );
    eprintln!(
        "golden: I={GOLDEN_I:#018x} Forest={GOLDEN_FOREST:#018x} (murmur chain, three-way agree)"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 1 — STRICT POSITIVITY (the Reynolds guard): native == JIT verdicts +
// error identity + ExprMeta; AND the load-bearing blind divergence.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r17_positivity_native_jit_and_blind() {
    let buf = jit(tir("positivity_root"), "positivity_root");
    let f: CheckFn = unsafe { std::mem::transmute(bind(&buf, "positivity_root")) };
    let agree = |case: u64, blind: u64| -> (u64, u64, u64) {
        let nv = native_call(0, case, blind);
        let jv = jit_call(f, case, blind);
        assert_eq!(
            nv, jv,
            "positivity case {case} blind {blind}: native {nv:?} != JIT {jv:?}"
        );
        jv
    };
    // AWARE verdicts (code 0 accept; 1 NonPositive).
    assert_eq!(agree(0, 0).0, 0, "I -> I  (direct recursive) ACCEPT");
    assert_eq!(
        agree(1, 0).0,
        0,
        "(A -> I) -> I  (W-type strictly-positive) ACCEPT"
    );
    assert_eq!(agree(3, 0).0, 0, "Bool -> I -> I  ACCEPT");
    let reynolds = agree(2, 0);
    assert_eq!(
        reynolds.0, 1,
        "(I -> Bool) -> I  (Reynolds) must REJECT NonPositive"
    );
    assert_eq!(
        reynolds.1, GOLDEN_I,
        "NonPositive carries the real Name I (cached_hash)"
    );
    let sibling = agree(4, 0);
    assert_eq!(
        sibling.0, 1,
        "(Forest -> Bool) -> I  (Wave 107 sibling) must REJECT"
    );
    assert_eq!(
        sibling.1, GOLDEN_FOREST,
        "sibling NonPositive carries the real Name Forest"
    );

    // THE LOAD-BEARING PROOF: blind (Pi-domain guard dropped) ACCEPTS the
    // Reynolds ctor and the sibling ctor — native == JIT on BOTH configs.
    assert_eq!(
        agree(2, 1).0,
        0,
        "BLIND accepts (I -> Bool) -> I (positivity dropped -> Reynolds admitted, UNSOUND)"
    );
    assert_eq!(agree(4, 1).0, 0, "BLIND accepts (Forest -> Bool) -> I");
    assert_ne!(
        native_call(0, 2, 0).0,
        native_call(0, 2, 1).0,
        "aware != blind on Reynolds (check is load-bearing)"
    );
    // and the well-formed accepts are unchanged blind (no false divergence).
    assert_eq!(
        agree(0, 1).0,
        0,
        "blind still accepts the well-formed I -> I"
    );
    assert_eq!(agree(1, 1).0, 0, "blind still accepts the W-type");
    eprintln!(
        "positivity: aware REJECTS Reynolds+sibling (real Name identity); blind ADMITS them; native==JIT"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 2 — CTOR-RETURN (is_valid_ind_app, incl. lean4#2125): native == JIT +
// the blind divergence over head / param / index rejections.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r17_ctor_return_native_jit_and_blind() {
    let buf = jit(tir("ctor_return_root"), "ctor_return_root");
    let f: CheckFn = unsafe { std::mem::transmute(bind(&buf, "ctor_return_root")) };
    let agree = |case: u64, blind: u64| -> (u64, u64, u64) {
        let nv = native_call(1, case, blind);
        let jv = jit_call(f, case, blind);
        assert_eq!(
            nv, jv,
            "ctor_return case {case} blind {blind}: native {nv:?} != JIT {jv:?}"
        );
        jv
    };
    // AWARE: 0 accept; 2 head; 3 param(idx 0); 4 index(pos 0). (payload folded
    // into bits 8..16 for param/index.)
    assert_eq!(agree(0, 0).0, 0, "Nat -> I  ACCEPT");
    assert_eq!(agree(1, 0).0, 0, "(A) -> I (BVar0)  ACCEPT");
    assert_eq!(agree(2, 0).0, 2, "Nat -> Nat  REJECT wrong head");
    assert_eq!(
        agree(3, 0).0,
        3 | (0 << 8),
        "(A) -> I Nat  REJECT param mismatch (idx 0)"
    );
    let idx2125 = agree(4, 0);
    assert_eq!(
        idx2125.0,
        4 | (0 << 8),
        "(A) -> I (BVar0) (List I)  REJECT index mentions I (lean4#2125, pos 0)"
    );
    assert_eq!(
        idx2125.1, GOLDEN_I,
        "index rejection carries the mentioned real Name I"
    );

    // THE LOAD-BEARING PROOF: blind drops all three rejects -> accepts every bad
    // ctor return, native == JIT.
    for &c in &[2u64, 3, 4] {
        assert_eq!(
            agree(c, 1).0,
            0,
            "BLIND accepts bad ctor return case {c} (ctor-return check dropped, UNSOUND)"
        );
        assert_ne!(
            native_call(1, c, 0).0,
            native_call(1, c, 1).0,
            "aware != blind on ctor case {c}"
        );
    }
    assert_eq!(
        agree(0, 1).0,
        0,
        "blind still accepts the well-formed Nat -> I"
    );
    eprintln!(
        "ctor-return: aware REJECTS wrong-head/param/index(#2125); blind ADMITS all three; native==JIT"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 3 — LARGE-ELIM-FROM-PROP: native == JIT verdicts (through the FVar-
// threaded infer_sort + full-Level is_nonzero gate) + the blind divergence on
// the Nonempty-like proposition.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r17_elim_native_jit_and_blind() {
    let buf = jit(tir("elim_root"), "elim_root");
    let f: CheckFn = unsafe { std::mem::transmute(bind(&buf, "elim_root")) };
    let agree = |case: u64, blind: u64| -> (u64, u64, u64) {
        let nv = native_call(2, case, blind);
        let jv = jit_call(f, case, blind);
        assert_eq!(
            nv, jv,
            "elim case {case} blind {blind}: native {nv:?} != JIT {jv:?}"
        );
        jv
    };
    // AWARE: 10 = large-elim allowed; 11 = Prop-only (restricted).
    assert_eq!(
        agree(0, 0).0,
        10,
        "False-like (0 ctors, Prop) -> large elim"
    );
    assert_eq!(agree(1, 0).0, 11, "Or-like (2 ctors, Prop) -> Prop-only");
    assert_eq!(
        agree(2, 0).0,
        11,
        "Mutual Prop (num_types 2) -> Prop-only (#3238)"
    );
    assert_eq!(
        agree(3, 0).0,
        10,
        "Type-valued (Sort 1) -> large elim (is_nonzero gate, full Level)"
    );
    assert_eq!(
        agree(4, 0).0,
        10,
        "And-like (2 Prop fields) -> large elim (subsingleton)"
    );
    let nonempty = agree(5, 0);
    assert_eq!(
        nonempty.0, 11,
        "Nonempty-like (1 non-Prop non-index field) -> Prop-only"
    );

    // THE LOAD-BEARING PROOF: blind (field-not-index restriction dropped) GRANTS
    // large elim to the Nonempty-like Prop — extracting the datum from a proof,
    // UNSOUND — native == JIT for both configs.
    assert_eq!(
        agree(5, 1).0,
        10,
        "BLIND grants large elim to Nonempty (large-elim-from-Prop, UNSOUND)"
    );
    assert_ne!(
        native_call(2, 5, 0).0,
        native_call(2, 5, 1).0,
        "aware != blind on Nonempty (elim check load-bearing)"
    );
    // the sound verdicts are unchanged blind (attribution is exactly the field
    // restriction).
    for &c in &[0u64, 1, 2, 3, 4] {
        assert_eq!(
            native_call(2, c, 0).0,
            native_call(2, c, 1).0,
            "blind leaves the non-Nonempty verdict unchanged (case {c})"
        );
    }
    eprintln!(
        "large-elim: aware RESTRICTS Nonempty to Prop-only; blind GRANTS large elim (UNSOUND); native==JIT"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 4 — THE CENTERPIECE (all three at once): dropping each check admits the
// corresponding classic inconsistency, in compiled machine code, native == JIT.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r17_soundness_centerpiece_all_three() {
    let pos = jit(tir("positivity_root"), "positivity_root");
    let ctor = jit(tir("ctor_return_root"), "ctor_return_root");
    let elim = jit(tir("elim_root"), "elim_root");
    let pf: CheckFn = unsafe { std::mem::transmute(bind(&pos, "positivity_root")) };
    let cf: CheckFn = unsafe { std::mem::transmute(bind(&ctor, "ctor_return_root")) };
    let ef: CheckFn = unsafe { std::mem::transmute(bind(&elim, "elim_root")) };

    // (1) positivity — the Reynolds ctor (I -> Bool) -> I.
    let p_aware = jit_call(pf, 2, 0);
    let p_blind = jit_call(pf, 2, 1);
    assert_eq!(
        (native_call(0, 2, 0), native_call(0, 2, 1)),
        (p_aware, p_blind),
        "positivity native==JIT"
    );
    assert_eq!(p_aware.0, 1, "AWARE positivity REJECTS Reynolds");
    assert_eq!(p_blind.0, 0, "BLIND positivity ACCEPTS Reynolds (unsound)");

    // (2) large-elim — the Nonempty-like Prop.
    let e_aware = jit_call(ef, 5, 0);
    let e_blind = jit_call(ef, 5, 1);
    assert_eq!(
        (native_call(2, 5, 0), native_call(2, 5, 1)),
        (e_aware, e_blind),
        "elim native==JIT"
    );
    assert_eq!(e_aware.0, 11, "AWARE large-elim RESTRICTS Nonempty");
    assert_eq!(
        e_blind.0, 10,
        "BLIND large-elim GRANTS large elim (unsound)"
    );

    // (3) ctor-return — the lean4#2125 index ctor (A) -> I (BVar0) (List I).
    let c_aware = jit_call(cf, 4, 0);
    let c_blind = jit_call(cf, 4, 1);
    assert_eq!(
        (native_call(1, 4, 0), native_call(1, 4, 1)),
        (c_aware, c_blind),
        "ctor-return native==JIT"
    );
    assert_eq!(c_aware.0 & 0xff, 4, "AWARE ctor-return REJECTS #2125 index");
    assert_eq!(
        c_blind.0, 0,
        "BLIND ctor-return ACCEPTS #2125 index (unsound)"
    );

    eprintln!(
        "CENTERPIECE: dropping each of positivity / large-elim / ctor-return ADMITS the classic inconsistency; aware REJECTS; native==JIT for all three"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 5 — ARMED golden corruption: flip the ExprKind::Const discriminant match
// in mentions_name's machine code so the index check no longer sees `I`, and
// prove the differential CATCHES it (corrupted JIT stops rejecting the #2125
// index while native still rejects) — proving the embedded .tir is genuinely
// compiled and executed and the Const-occurrence scan is load-bearing.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r17_armed_golden_corruption() {
    let base = tir("ctor_return_root");
    // native pristine: #2125 index REJECTS (code low byte 4).
    let n = native_call(1, 4, 0);
    assert_eq!(n.0 & 0xff, 4, "native must reject the #2125 index ctor");

    // baseline JIT matches native.
    {
        let buf = jit(base, "ctor_return_root");
        let f: CheckFn = unsafe { std::mem::transmute(bind(&buf, "ctor_return_root")) };
        assert_eq!(jit_call(f, 4, 0), n, "baseline JIT must match native");
    }

    // Corrupt mentions_name's Const arm: it matches ExprKind::Const via a switch
    // on the discriminant. Const is discriminant 3 in this ExprKind
    // (BVar0,FVar1,Sort2,Const3,...). Find a `switch %N [ 3: bbX default: bbY ]`
    // inside the mentions_name body and redirect the Const arm to `default`
    // (never taken), so `List I` no longer registers as mentioning I.
    let fn_body = |name: &str| -> (usize, usize) {
        let start = base
            .find(&format!("fn @{name}("))
            .unwrap_or_else(|| panic!("no fn {name}"));
        let after = &base[start + 1..];
        let end = after
            .find("\nfn @")
            .map(|k| start + 1 + k)
            .unwrap_or(base.len());
        (start, end)
    };
    let (s, e) = fn_body("mentions_name");
    let body = &base[s..e];
    // mentions_name matches ExprKind via a `switch` on the discriminant: Const is
    // 3 (BVar0,FVar1,Sort2,Const3,...App4,...Lit8,...). The leaves
    // BVar/FVar/Sort/Lit dispatch to a shared `false`-returning block (the `0:`
    // target); Const dispatches to the `name_eq` block. SWAP the Const(3) and
    // Lit(8) targets — Const now takes the false-leaf (so a Const NEVER registers
    // as a mention) and Lit takes the name_eq block. Both blocks stay reachable
    // (no orphaned block -> the module still validates), and Lit(8) is never hit
    // in the #2125 scenario (the index arg `List I` is App/Const, no Lit), so the
    // only observable change is `mentions_name(List I, I) -> false`.
    let sw_start = body.find("switch ").expect("a switch in mentions_name");
    let sw_line_end = body[sw_start..].find(']').expect("switch close") + sw_start + 1;
    let sw_line = &body[sw_start..sw_line_end];
    let field = |lbl: &str| -> String {
        let p = sw_line
            .find(lbl)
            .unwrap_or_else(|| panic!("no `{lbl}` in switch: {sw_line}"))
            + lbl.len();
        let rest = &sw_line[p..];
        let endw = rest.find(|c: char| c == ' ' || c == ']').unwrap();
        rest[..endw].to_string()
    };
    let tgt_const = field("3: "); // the name_eq block, e.g. bb9(%1)
    let tgt_false = field("8: "); // the Lit false-leaf block, e.g. bb8
    assert_ne!(
        tgt_const, tgt_false,
        "Const arm and the Lit false-leaf must differ"
    );
    assert_eq!(
        tgt_false,
        field("0: "),
        "Lit and BVar must share the false-leaf block"
    );
    assert!(
        tgt_const.contains('('),
        "the Const arm should carry the name-payload arg"
    );
    // swap 3<->8 targets (order matters: rewrite `3: <name_eq>` first, then the
    // still-present `8: <false>`).
    let corrupted_sw = sw_line
        .replacen(&format!("3: {tgt_const}"), &format!("3: {tgt_false}"), 1)
        .replacen(&format!("8: {tgt_false}"), &format!("8: {tgt_const}"), 1);
    let corrupted_body = body.replacen(sw_line, &corrupted_sw, 1);
    let corrupted = format!("{}{}{}", &base[..s], corrupted_body, &base[e..]);
    assert!(corrupted != base, "corruption must change the text");

    let buf = jit(
        &corrupted,
        "ctor_return_root(mentions_name-Const-corrupted)",
    );
    let f: CheckFn = unsafe { std::mem::transmute(bind(&buf, "ctor_return_root")) };
    let jc = jit_call(f, 4, 0);
    // With the Const arm disabled, mentions_name(List I, I) no longer sees the
    // Const I -> the #2125 index check passes -> the ctor is ACCEPTED (code 0).
    assert_ne!(
        jc.0, n.0,
        "corrupted JIT must diverge from pristine native (Const scan is load-bearing)"
    );
    assert_eq!(
        jc.0, 0,
        "corrupted (Const arm dead) ACCEPTS the #2125 index ctor"
    );
    eprintln!(
        "armed: disabling mentions_name's Const arm makes the JIT stop rejecting the #2125 index (native still rejects) — .tir genuinely compiled+executed"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 6 — module sanity + wiring: the three checks are LIVE (bodied) and the
// gates genuinely Call their soundness sub-checks in machine code.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r17_module_sanity_and_wiring() {
    for root in ["positivity_root", "ctor_return_root", "elim_root"] {
        let m = parse_validate(tir(root), root);
        let bodied = |sym: &str| {
            m.functions
                .iter()
                .any(|f| f.name == sym && !f.blocks.is_empty())
        };
        match root {
            "positivity_root" => {
                assert!(
                    bodied("check_strictly_positive_impl"),
                    "check_strictly_positive_impl must be bodied"
                );
                assert!(
                    bodied("check_no_negative_occurrence"),
                    "check_no_negative_occurrence must be bodied"
                );
                assert!(bodied("mentions_name"), "mentions_name must be bodied");
            }
            "ctor_return_root" => {
                assert!(
                    bodied("validate_ctor_return_type"),
                    "validate_ctor_return_type must be bodied"
                );
                assert!(bodied("mentions_name"), "mentions_name must be bodied");
                assert!(bodied("count_pi_args"), "count_pi_args must be bodied");
            }
            _ => {
                assert!(
                    bodied("elim_only_at_universe_zero"),
                    "elim_only_at_universe_zero must be bodied"
                );
                assert!(
                    bodied("Verifier____env___ctor_field_sort_levels"),
                    "ctor_field_sort_levels must be bodied"
                );
                assert!(
                    bodied("Verifier____env___infer_sort_inner"),
                    "infer_sort_inner must be bodied"
                );
            }
        }
    }
    eprintln!(
        "sanity: positivity / ctor-return / large-elim checks all LIVE (bodied) across the three modules"
    );
}
