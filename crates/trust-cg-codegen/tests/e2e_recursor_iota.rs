// R19 — THE RECURSOR IOTA REDUCTION, native == JIT over Clean's inductive
// COMPUTATION rule (the companion to R17's well-formedness CHECKS and R5's
// recursor TYPE), re-composed on the full modern stack (real Names + full Level
// + production compute_meta) and compiled through Trust (Rust -> MIR -> trust-ir
// -> trust-cg -> machine code).
//
// The iota rule is factored as build_recursor_rule_rhs (where MINOR SELECTION +
// the RECURSIVE IH live) + try_iota_reduction (the applier), wired at whnf's
// App-arm; a full-normalize driver reduces multi-step so the IH re-fires the
// recursor recursively. Two REAL families: Nat (zero/succ) and Tree
// (leaf : Nat -> Tree / node : Tree -> Tree -> Tree).
//
// SOUNDNESS PROOF (centerpiece): a POISONED iota — (1) the WRONG minor premise,
// or (2) the DROPPED recursive IH — reduces to a DIFFERENT term, native == JIT
// (structural deep_eq + meta). A STUCK non-redex (recursor on a variable) is left
// unchanged. Armed golden corruption (anon seed) proves the .tir is genuinely
// compiled+executed.
//
// Slice: crates/trust-cg-codegen/tests/slices/clean_recursor_iota_slice.rs
// Emit (per root; trust-ir main; NO frontend changes):
//   trust_ir_mir --mir-emit-closure <root> <out.tir>
//   roots: iota_reduce_root | iota_names_probe_root
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
#[path = "slices/clean_recursor_iota_slice.rs"]
pub mod rn;

// The VERBATIM MIR-emitted trust-ir closures (validate_module = 0 each).
const REDUCE_TIR: &str = include_str!("clean_ri_reduce.tir");
const NAMES_TIR: &str = include_str!("clean_ri_names.tir");

fn tir(root: &str) -> &'static str {
    match root {
        "iota_reduce_root" => REDUCE_TIR,
        "iota_names_probe_root" => NAMES_TIR,
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
// Shims — the bodyless extern leaves (the R18/R5 set retyped onto this slice's
// `rn` types; Arc/Vec ops LEAK, the landed model).
// ════════════════════════════════════════════════════════════════════════════

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

// usize_to_u32 = u32::try_from(v).unwrap_or(MAX)
extern "C" fn is_try_from_u32(sret: *mut Result<u32, std::num::TryFromIntError>, v: u64) {
    unsafe {
        std::ptr::write(sret, u32::try_from(v));
    }
}
extern "C" fn is_result_unwrap_or(
    res: *const Result<u32, std::num::TryFromIntError>,
    default: u32,
) -> u32 {
    unsafe { (*res).clone().unwrap_or(default) }
}

// ptr::write leaves
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
extern "C" fn is_arc_str_clone(sret: *mut Arc<str>, this: *const Arc<str>) {
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

// slice ops
extern "C" fn is_slice_expr_get<'a>(
    sret: *mut Option<&'a rn::Expr>,
    slice_ref: *const (*const rn::Expr, usize),
    idx: u64,
) {
    unsafe {
        let (data, len) = *slice_ref;
        if (idx as usize) < len {
            std::ptr::write(sret, Some(&*data.add(idx as usize)));
        } else {
            std::ptr::write(sret, None);
        }
    }
}
extern "C" fn is_slice_rule_get<'a>(
    sret: *mut Option<&'a rn::RecursorRule>,
    slice_ref: *const (*const rn::RecursorRule, usize),
    idx: u64,
) {
    unsafe {
        let (data, len) = *slice_ref;
        if (idx as usize) < len {
            std::ptr::write(sret, Some(&*data.add(idx as usize)));
        } else {
            std::ptr::write(sret, None);
        }
    }
}
extern "C" fn is_slice_expr_reverse(slice_ref: *const (*mut rn::Expr, usize)) {
    unsafe {
        let (ptr, len) = *slice_ref;
        let s: &mut [rn::Expr] = std::slice::from_raw_parts_mut(ptr, len);
        s.reverse();
    }
}
extern "C" fn is_slice_name_is_empty(slice_ref: *const (*const rn::Name, usize)) -> bool {
    unsafe { (*slice_ref).1 == 0 }
}

// KaniHasher leaves + discriminant
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

// Vec<T> op families (owned; big payload passed by pointer).
macro_rules! vec_shims {
    ($new:ident, $push:ident, $len:ident, $index:ident, $deref:ident, $clone:ident, $ty:ty) => {
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
        #[allow(dead_code)]
        extern "C" fn $clone(sret: *mut Vec<$ty>, this: *const Vec<$ty>) {
            unsafe {
                std::ptr::write(sret, (*this).clone());
            }
        }
    };
}
vec_shims!(
    v_name_new,
    v_name_push,
    v_name_len,
    v_name_index,
    v_name_deref,
    v_name_clone,
    rn::Name
);
vec_shims!(
    v_ind_new,
    v_ind_push,
    v_ind_len,
    v_ind_index,
    v_ind_deref,
    v_ind_clone,
    rn::InductiveType
);
vec_shims!(
    v_ctor_new,
    v_ctor_push,
    v_ctor_len,
    v_ctor_index,
    v_ctor_deref,
    v_ctor_clone,
    rn::Ctor
);
vec_shims!(
    v_rule_new,
    v_rule_push,
    v_rule_len,
    v_rule_index,
    v_rule_deref,
    v_rule_clone,
    rn::RecursorRule
);
vec_shims!(
    v_cval_new,
    v_cval_push,
    v_cval_len,
    v_cval_index,
    v_cval_deref,
    v_cval_clone,
    rn::ConstructorVal
);
vec_shims!(
    v_rval_new,
    v_rval_push,
    v_rval_len,
    v_rval_index,
    v_rval_deref,
    v_rval_clone,
    rn::RecursorVal
);
vec_shims!(
    v_lvl_new,
    v_lvl_push,
    v_lvl_len,
    v_lvl_index,
    v_lvl_deref,
    v_lvl_clone,
    rn::Level
);
vec_shims!(
    v_expr_new,
    v_expr_push,
    v_expr_len,
    v_expr_index,
    v_expr_deref,
    v_expr_clone,
    rn::Expr
);
vec_shims!(
    v_bdexpr_new,
    v_bdexpr_push,
    v_bdexpr_len,
    v_bdexpr_index,
    v_bdexpr_deref,
    v_bdexpr_clone,
    (rn::BinderData, rn::Expr)
);

// Vec<bool>: push BY VALUE; deref.
extern "C" fn v_bool_new(sret: *mut Vec<bool>) {
    unsafe {
        std::ptr::write(sret, Vec::new());
    }
}
extern "C" fn v_bool_push(vec: *mut Vec<bool>, value: bool) {
    unsafe {
        (*vec).push(value);
    }
}
extern "C" fn v_bool_len(vec: *const Vec<bool>) -> u64 {
    unsafe { (*vec).len() as u64 }
}
extern "C" fn v_bool_index(vec: *const Vec<bool>, idx: u64) -> *const bool {
    unsafe {
        let s: &[bool] = (*vec).as_slice();
        assert!((idx as usize) < s.len(), "bool oob");
        s.as_ptr().add(idx as usize)
    }
}
extern "C" fn v_bool_deref(sret: *mut (*const bool, usize), vec: *const Vec<bool>) {
    unsafe {
        let s: &[bool] = (*vec).as_slice();
        std::ptr::write(sret, (s.as_ptr(), s.len()));
    }
}

// Vec<Expr> mut-slice access (get_app_args builds then reverses).
extern "C" fn v_expr_deref_mut(sret: *mut (*mut rn::Expr, usize), v: *mut Vec<rn::Expr>) {
    unsafe {
        let s: &mut [rn::Expr] = (*v).as_mut_slice();
        std::ptr::write(sret, (s.as_mut_ptr(), s.len()));
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Structural extern-leaf classifier (crate-tag independent; R18 discipline).
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
    if has("ptr_try_from_impls") {
        return Some(is_try_from_u32 as *const u8);
    }
    if has("6Result") && has("9unwrap_or") {
        return Some(is_result_unwrap_or as *const u8);
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
    if has("3ptr5write") {
        if has("4ExprE") {
            return Some(is_ptr_write_expr as *const u8);
        }
        if has("4NameE") {
            return Some(is_ptr_write_name as *const u8);
        }
    }

    // slice ops
    if has("5sliceS") {
        if has("4Expr3get") {
            return Some(is_slice_expr_get as *const u8);
        }
        if has("12RecursorRule3get") {
            return Some(is_slice_rule_get as *const u8);
        }
        if has("4Expr7reverse") {
            return Some(is_slice_expr_reverse as *const u8);
        }
        if has("4Name8is_empty") {
            return Some(is_slice_name_is_empty as *const u8);
        }
    }

    // Arc other (as_ref / from / deref) before clones
    if has("3Arc") && has("4ExprE") && has("6as_ref") {
        return Some(is_arc_expr_as_ref as *const u8);
    }
    if has("3Arce") && has("4from") {
        return Some(is_arc_str_from as *const u8);
    }
    if has("3Arce") && has("5deref5Deref5deref") {
        return Some(is_arc_str_deref as *const u8);
    }

    // clones (Vec vs Arc)
    if has("5clone5Clone5clone") {
        if has("3Vec") {
            if has("4ExprE") {
                return Some(v_expr_clone as *const u8);
            }
            if has("5LevelE") {
                return Some(v_lvl_clone as *const u8);
            }
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

    // Vec<bool>
    if has("3Vecb") {
        if has("3new") {
            return Some(v_bool_new as *const u8);
        }
        if has("4push") {
            return Some(v_bool_push as *const u8);
        }
        if has("3len") {
            return Some(v_bool_len as *const u8);
        }
        if has("5index5Index") {
            return Some(v_bool_index as *const u8);
        }
        if has("5deref5Deref5deref") {
            return Some(v_bool_deref as *const u8);
        }
    }

    // Vec<(BinderData, Expr)>
    if has("3Vec") && has("10BinderData") {
        if has("3new") {
            return Some(v_bdexpr_new as *const u8);
        }
        if has("4push") {
            return Some(v_bdexpr_push as *const u8);
        }
        if has("3len") {
            return Some(v_bdexpr_len as *const u8);
        }
        if has("5index5Index") {
            return Some(v_bdexpr_index as *const u8);
        }
        if has("5deref5Deref5deref") {
            return Some(v_bdexpr_deref as *const u8);
        }
    }

    // Vec<T> owned (single element type). Discriminate by type marker, then method.
    if has("3Vec") {
        // deref_mut is Expr-only (get_app_args)
        if has("4ExprE") && has("8DerefMut9deref_mut") {
            return Some(v_expr_deref_mut as *const u8);
        }
        let ty_expr = has("4ExprE");
        let ty_name = has("4NameE");
        let ty_lvl = has("5LevelE");
        let ty_ind = has("13InductiveType");
        let ty_ctor = has("4CtorE");
        let ty_rule = has("12RecursorRule");
        let ty_cval = has("14ConstructorVal");
        let ty_rval = has("11RecursorVal");
        let pick = |e, na, l, i, c, r, cv, rv| -> Option<*const u8> {
            if ty_expr {
                Some(e)
            } else if ty_name {
                Some(na)
            } else if ty_lvl {
                Some(l)
            } else if ty_ind {
                Some(i)
            } else if ty_ctor {
                Some(c)
            } else if ty_rule {
                Some(r)
            } else if ty_cval {
                Some(cv)
            } else if ty_rval {
                Some(rv)
            } else {
                None
            }
        };
        if has("3new") {
            return pick(
                v_expr_new as *const u8,
                v_name_new as *const u8,
                v_lvl_new as *const u8,
                v_ind_new as *const u8,
                v_ctor_new as *const u8,
                v_rule_new as *const u8,
                v_cval_new as *const u8,
                v_rval_new as *const u8,
            );
        }
        if has("4push") {
            return pick(
                v_expr_push as *const u8,
                v_name_push as *const u8,
                v_lvl_push as *const u8,
                v_ind_push as *const u8,
                v_ctor_push as *const u8,
                v_rule_push as *const u8,
                v_cval_push as *const u8,
                v_rval_push as *const u8,
            );
        }
        if has("3len") {
            return pick(
                v_expr_len as *const u8,
                v_name_len as *const u8,
                v_lvl_len as *const u8,
                v_ind_len as *const u8,
                v_ctor_len as *const u8,
                v_rule_len as *const u8,
                v_cval_len as *const u8,
                v_rval_len as *const u8,
            );
        }
        if has("5index5Index") {
            return pick(
                v_expr_index as *const u8,
                v_name_index as *const u8,
                v_lvl_index as *const u8,
                v_ind_index as *const u8,
                v_ctor_index as *const u8,
                v_rule_index as *const u8,
                v_cval_index as *const u8,
                v_rval_index as *const u8,
            );
        }
        if has("5deref5Deref5deref") {
            return pick(
                v_expr_deref as *const u8,
                v_name_deref as *const u8,
                v_lvl_deref as *const u8,
                v_ind_deref as *const u8,
                v_ctor_deref as *const u8,
                v_rule_deref as *const u8,
                v_cval_deref as *const u8,
                v_rval_deref as *const u8,
            );
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

type ReduceFn = extern "C" fn(*mut rn::Expr, u64, u64);
type NameFn = extern "C" fn(*mut rn::Name, u64);

// ── native oracle wrappers (call the slice roots directly) ──
fn native_reduce(scenario: u64, poison: u64) -> rn::Expr {
    let mut s = MaybeUninit::<rn::Expr>::uninit();
    unsafe {
        rn::iota_reduce_root(s.as_mut_ptr(), scenario, poison);
        s.assume_init()
    }
}
fn native_name(idx: u64) -> rn::Name {
    let mut s = MaybeUninit::<rn::Name>::uninit();
    unsafe {
        rn::iota_names_probe_root(s.as_mut_ptr(), idx);
        s.assume_init()
    }
}
fn jit_reduce(f: ReduceFn, scenario: u64, poison: u64) -> rn::Expr {
    let mut s = MaybeUninit::<rn::Expr>::uninit();
    unsafe {
        f(s.as_mut_ptr(), scenario, poison);
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

// META-INDEPENDENT structural equality (ignores ExprMeta) — proves a divergence
// is a genuine tree-shape difference, not a meta-hash artifact.
fn struct_eq(a: &rn::Expr, b: &rn::Expr) -> bool {
    use rn::ExprKind::*;
    match (&a.kind, &b.kind) {
        (BVar(x), BVar(y)) => x == y,
        (FVar(x), FVar(y)) => x == y,
        (Sort(x), Sort(y)) => x == y,
        (Const(n1, l1), Const(n2, l2)) => rn::name_eq(n1, n2) && l1 == l2,
        (Lit(x), Lit(y)) => x == y,
        (App(f1, a1), App(f2, a2)) => struct_eq(f1, f2) && struct_eq(a1, a2),
        (Lam(b1, t1, y1), Lam(b2, t2, y2)) => b1 == b2 && struct_eq(t1, t2) && struct_eq(y1, y2),
        (Pi(b1, t1, y1), Pi(b2, t2, y2)) => b1 == b2 && struct_eq(t1, t2) && struct_eq(y1, y2),
        (Proj(n1, i1, e1), Proj(n2, i2, e2)) => {
            rn::name_eq(n1, n2) && i1 == i2 && struct_eq(e1, e2)
        }
        (MData(t1, e1), MData(t2, e2)) => t1 == t2 && struct_eq(e1, e2),
        _ => false,
    }
}

// walk the App spine to the head Const name (via rn's pub Names).
fn head_name(e: &rn::Expr) -> Option<rn::Name> {
    let mut cur = e;
    loop {
        match &cur.kind {
            rn::ExprKind::App(f, _) => cur = f,
            rn::ExprKind::Const(nm, _) => return Some(nm.clone()),
            _ => return None,
        }
    }
}
fn head_is(e: &rn::Expr, nm: &rn::Name) -> bool {
    match head_name(e) {
        Some(h) => rn::name_eq(&h, nm),
        None => false,
    }
}

// ── test-side term builders (rn PUB api; independent of the slice's private
//    scenario helpers) — the EXPECTED reduced terms ──
fn e_nm1(s: &str) -> rn::Name {
    rn::fold_step(rn::name_anon(), s)
}
fn e_nm2(a: &str, b: &str) -> rn::Name {
    rn::fold_step(rn::fold_step(rn::name_anon(), a), b)
}
fn e_cnst(s: &str) -> rn::Expr {
    rn::Expr::cnst(e_nm1(s))
}
fn e_app(f: rn::Expr, a: rn::Expr) -> rn::Expr {
    rn::Expr::app(f, a)
}
fn e_num(k: u64) -> rn::Expr {
    let mut e = rn::Expr::const_(e_nm2("Nat", "zero"), Vec::new());
    let mut i = 0u64;
    while i < k {
        e = rn::Expr::app(rn::Expr::const_(e_nm2("Nat", "succ"), Vec::new()), e);
        i += 1;
    }
    e
}
fn e_leaf(x: rn::Expr) -> rn::Expr {
    rn::Expr::app(rn::Expr::const_(e_nm2("Tree", "leaf"), Vec::new()), x)
}

// GOLDEN real-Name cached_hashes (R4-R7-verified production murmur chain; the
// native slice construction == independent chunks_exact oracle == these; Tree.rec
// and u are anchored to the R4/R18 pins).
const G_NAT: u64 = 0x9ecc0d3a68dfdd9b;
const G_NAT_ZERO: u64 = 0xba5a9c475ea35133;
const G_NAT_SUCC: u64 = 0xdf9c287df649a55d;
const G_NAT_REC: u64 = 0x4d9af511f20f49b2;
const G_TREE: u64 = 0x799c131f2f585927;
const G_TREE_LEAF: u64 = 0xbde19090ef9df6dc;
const G_TREE_NODE: u64 = 0x03b4a4808874f36c;
const G_TREE_REC: u64 = 0x293412c406e2a88e; // == round-4 pin (anchor)
const G_U: u64 = 0xae572a66f1f7b2e8; // == R18 pin (anchor)
const GOLDENS: [(u64, u64, &str); 9] = [
    (0, G_NAT, "Nat"),
    (1, G_NAT_ZERO, "Nat.zero"),
    (2, G_NAT_SUCC, "Nat.succ"),
    (3, G_NAT_REC, "Nat.rec"),
    (4, G_TREE, "Tree"),
    (5, G_TREE_LEAF, "Tree.leaf"),
    (6, G_TREE_NODE, "Tree.node"),
    (7, G_TREE_REC, "Tree.rec"),
    (8, G_U, "u"),
];

// Independent murmur/mix oracle (chunks_exact; distinct from the slice index-loop).
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
fn r19_golden_name_hashes() {
    for (idx, g, s) in GOLDENS {
        assert_eq!(name_hash_dotted(s), g, "independent murmur({s}) != pin");
        assert_eq!(
            native_name(idx).cached_hash,
            g,
            "native slice cached_hash({s}) != pin"
        );
    }
    eprintln!(
        "golden: 9 family names three-way agree (independent oracle == slice == pin); Tree.rec/u anchored to R4/R18"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 1 — all 8 scenarios reduce BIT-IDENTICAL native == JIT (deep structural +
// ExprMeta word), and the family Names cached_hash-pinned native == JIT == golden.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r19_scenarios_native_jit() {
    let buf = jit(tir("iota_reduce_root"), "iota_reduce_root");
    let f: ReduceFn = unsafe { std::mem::transmute(bind(&buf, "iota_reduce_root")) };
    let labels = [
        "Nat.base",
        "Nat.succ-1step",
        "Nat.succ^2-nf",
        "Nat.succ^3-nf",
        "Tree.node-nf",
        "Nat.stuck",
        "Nat.lit-nf",
        "Nat.extras",
    ];
    for scenario in 0u64..8 {
        let nv = native_reduce(scenario, 0);
        let jv = jit_reduce(f, scenario, 0);
        assert!(
            deep_eq(&nv, &jv),
            "scenario {scenario} ({}): native != JIT (structure)",
            labels[scenario as usize]
        );
        assert_eq!(
            nv.meta.raw(),
            jv.meta.raw(),
            "scenario {scenario}: meta word disagrees"
        );
        eprintln!(
            "{}: native==JIT meta={:#018x}",
            labels[scenario as usize],
            jv.meta.raw()
        );
    }
    let nbuf = jit(tir("iota_names_probe_root"), "iota_names_probe_root");
    let nf: NameFn = unsafe { std::mem::transmute(bind(&nbuf, "iota_names_probe_root")) };
    for (idx, g, s) in GOLDENS {
        assert_eq!(
            native_name(idx).cached_hash,
            jit_name(nf, idx).cached_hash,
            "{s}: native cached_hash != JIT"
        );
        assert_eq!(
            jit_name(nf, idx).cached_hash,
            g,
            "{s}: JIT cached_hash != golden"
        );
    }
    eprintln!("scenarios: 8/8 bit-identical native==JIT; 9 real-Name cached_hashes pinned");
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 2 — CORRECTNESS: the iota rule computes the RIGHT values (minor selection
// + recursive IH), verified against independently-built expected terms, native ==
// JIT.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r19_iota_correctness_native_jit() {
    let buf = jit(tir("iota_reduce_root"), "iota_reduce_root");
    let f: ReduceFn = unsafe { std::mem::transmute(bind(&buf, "iota_reduce_root")) };
    let agree = |scenario: u64, poison: u64| -> rn::Expr {
        let nv = native_reduce(scenario, poison);
        let jv = jit_reduce(f, scenario, poison);
        assert!(
            deep_eq(&nv, &jv),
            "scenario {scenario} poison {poison}: native != JIT"
        );
        assert_eq!(
            nv.meta.raw(),
            jv.meta.raw(),
            "scenario {scenario} poison {poison}: meta disagrees"
        );
        jv
    };
    // base: Nat.rec C z s zero -> z
    let base = agree(0, 0);
    assert!(
        deep_eq(&base, &e_cnst("z")),
        "base iota must reduce to z (the base minor)"
    );
    // succ^2: -> s (succ zero) (s zero z)  [minor selection s + IH exercised recursively]
    let exp2 = e_app(
        e_app(e_cnst("s"), e_num(1)),
        e_app(e_app(e_cnst("s"), e_num(0)), e_cnst("z")),
    );
    assert!(
        deep_eq(&agree(2, 0), &exp2),
        "succ^2 multi-step must be s (succ zero) (s zero z)"
    );
    // succ^3: -> s (succ^2 zero) (s (succ zero) (s zero z))
    let exp3 = e_app(
        e_app(e_cnst("s"), e_num(2)),
        e_app(
            e_app(e_cnst("s"), e_num(1)),
            e_app(e_app(e_cnst("s"), e_num(0)), e_cnst("z")),
        ),
    );
    assert!(deep_eq(&agree(3, 0), &exp3), "succ^3 must fully reduce");
    // Tree: -> mn (leaf a) (leaf b) (ml a) (ml b)  [minor selection + non-rec field + 2 IHs IN ORDER]
    let exp4 = e_app(
        e_app(
            e_app(
                e_app(e_cnst("mn"), e_leaf(e_cnst("a"))),
                e_leaf(e_cnst("b")),
            ),
            e_app(e_cnst("ml"), e_cnst("a")),
        ),
        e_app(e_cnst("ml"), e_cnst("b")),
    );
    assert!(
        deep_eq(&agree(4, 0), &exp4),
        "Tree: minor selection + non-rec field + 2 IHs in order"
    );
    // Nat literal major (nat_lit_to_constructor feeds iota): -> s (Lit 1) (s (Lit 0) z)
    let lit = |k: u64| rn::Expr::from_kind(rn::ExprKind::Lit(rn::Literal::Nat(k)));
    let exp6 = e_app(
        e_app(e_cnst("s"), lit(1)),
        e_app(e_app(e_cnst("s"), lit(0)), e_cnst("z")),
    );
    assert!(
        deep_eq(&agree(6, 0), &exp6),
        "Nat-literal major: lit->ctor feeds iota"
    );
    eprintln!(
        "correctness: base->z, succ^2/succ^3 recursive-IH, Tree minor+2-IH-order, lit->ctor — all native==JIT against independent expected terms"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 3 — CENTERPIECE (i): the POISONED MINOR SELECTION (wrong minor premise)
// reduces to a DIFFERENT term, native == JIT for both configs — a wrong minor is
// a wrong computation, proven in machine code.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r19_poison_minor_diverges() {
    let buf = jit(tir("iota_reduce_root"), "iota_reduce_root");
    let f: ReduceFn = unsafe { std::mem::transmute(bind(&buf, "iota_reduce_root")) };
    for scenario in [2u64, 4u64] {
        let n_ok = native_reduce(scenario, 0);
        let j_ok = jit_reduce(f, scenario, 0);
        let n_bad = native_reduce(scenario, 1);
        let j_bad = jit_reduce(f, scenario, 1);
        assert!(
            deep_eq(&n_ok, &j_ok),
            "scenario {scenario} correct: native != JIT"
        );
        assert!(
            deep_eq(&n_bad, &j_bad),
            "scenario {scenario} poison_minor: native != JIT"
        );
        assert!(
            !deep_eq(&j_ok, &j_bad),
            "scenario {scenario}: poisoned MINOR must DIVERGE from correct (soundness-critical)"
        );
        assert!(
            !struct_eq(&j_ok, &j_bad),
            "scenario {scenario}: poisoned-minor divergence must be STRUCTURAL (tree-shape, meta-independent)"
        );
        assert_ne!(
            j_ok.meta.raw(),
            j_bad.meta.raw(),
            "scenario {scenario}: poisoned-minor meta must differ"
        );
        // attribution: the divergence is the SAME native and JIT.
        assert_eq!(
            deep_eq(&n_ok, &n_bad),
            deep_eq(&j_ok, &j_bad),
            "scenario {scenario}: divergence must agree native==JIT"
        );
    }
    eprintln!(
        "poison MINOR: selecting the wrong minor premise DIVERGES native==JIT (Nat succ->zero-minor, Tree node->leaf-minor) — a wrong minor is a wrong computation"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 4 — CENTERPIECE (ii): the DROPPED RECURSIVE IH reduces to a DIFFERENT
// term (missing the recursive result), native == JIT for both configs.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r19_poison_ih_diverges() {
    let buf = jit(tir("iota_reduce_root"), "iota_reduce_root");
    let f: ReduceFn = unsafe { std::mem::transmute(bind(&buf, "iota_reduce_root")) };
    for scenario in [2u64, 4u64] {
        let n_ok = native_reduce(scenario, 0);
        let j_ok = jit_reduce(f, scenario, 0);
        let n_bad = native_reduce(scenario, 2);
        let j_bad = jit_reduce(f, scenario, 2);
        assert!(
            deep_eq(&n_ok, &j_ok),
            "scenario {scenario} correct: native != JIT"
        );
        assert!(
            deep_eq(&n_bad, &j_bad),
            "scenario {scenario} poison_ih: native != JIT"
        );
        assert!(
            !deep_eq(&j_ok, &j_bad),
            "scenario {scenario}: dropped IH must DIVERGE from correct (a non-computing recursor)"
        );
        assert!(
            !struct_eq(&j_ok, &j_bad),
            "scenario {scenario}: dropped-IH divergence must be STRUCTURAL (tree-shape, meta-independent)"
        );
        assert_ne!(
            j_ok.meta.raw(),
            j_bad.meta.raw(),
            "scenario {scenario}: dropped-IH meta must differ"
        );
    }
    // and the two poisons are distinct corruptions (minor != ih).
    assert!(
        !deep_eq(&native_reduce(2, 1), &native_reduce(2, 2)),
        "poison_minor and poison_ih must be distinct corruptions"
    );
    eprintln!(
        "poison IH: dropping the recursive induction hypothesis DIVERGES native==JIT (Nat succ k -> s k, Tree node -> arity 4->2) — a dropped IH is a non-computing recursor"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 5 — the STUCK non-redex: a recursor applied to a VARIABLE (not a ctor
// application) is left correctly UNCHANGED (head still Nat.rec), native == JIT.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r19_stuck_non_redex_native_jit() {
    let buf = jit(tir("iota_reduce_root"), "iota_reduce_root");
    let f: ReduceFn = unsafe { std::mem::transmute(bind(&buf, "iota_reduce_root")) };
    let n = native_reduce(5, 0);
    let j = jit_reduce(f, 5, 0);
    assert!(deep_eq(&n, &j), "stuck: native != JIT");
    // head is still Nat.rec (the recursor did NOT fire on a non-ctor major).
    let nat_rec = rn::name_append_rec(&e_nm1("Nat"));
    assert!(
        head_is(&j, &nat_rec),
        "stuck non-redex must keep head Nat.rec (recursor must NOT reduce on a variable)"
    );
    // a redex on the SAME family (base) does reduce away from Nat.rec.
    assert!(
        !head_is(&native_reduce(0, 0), &nat_rec),
        "the base redex must reduce (head no longer Nat.rec)"
    );
    eprintln!(
        "stuck: Nat.rec applied to a variable is left correctly STUCK (head still Nat.rec); the base redex reduces — native==JIT"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 6 — ARMED golden corruption: bump the anon seed (1723 -> 1724) in the
// names module text, re-JIT, and prove EVERY probed cached_hash diverges from its
// golden (native still matches) — the .tir is genuinely compiled+executed and the
// real-Name murmur/mix chain is load-bearing.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r19_armed_anon_seed_corruption() {
    let base = tir("iota_names_probe_root");
    {
        let buf = jit(base, "iota_names_probe_root");
        let nf: NameFn = unsafe { std::mem::transmute(bind(&buf, "iota_names_probe_root")) };
        for (idx, g, s) in GOLDENS {
            assert_eq!(
                jit_name(nf, idx).cached_hash,
                g,
                "pristine JIT cached_hash({s}) != golden"
            );
        }
    }
    assert_eq!(
        base.matches("const u64 1723").count(),
        1,
        "anon seed 1723 must be unique in name_anon"
    );
    let corrupted = base.replace("const u64 1723", "const u64 1724");
    assert!(corrupted != base, "corruption must change the text");
    let buf = jit(&corrupted, "iota_names_probe_root(anon-seed-corrupted)");
    let nf: NameFn = unsafe { std::mem::transmute(bind(&buf, "iota_names_probe_root")) };
    for (idx, g, s) in GOLDENS {
        assert_ne!(
            jit_name(nf, idx).cached_hash,
            g,
            "corrupted JIT cached_hash({s}) must DIVERGE from golden"
        );
        assert_eq!(
            native_name(idx).cached_hash,
            g,
            "native cached_hash({s}) unchanged (still golden)"
        );
    }
    eprintln!(
        "armed: bumping the anon seed 1723->1724 diverges ALL 9 cached_hashes (native still golden) — .tir genuinely compiled+executed"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 7 — module sanity + wiring: the RHS builder, the iota reduction, and the
// whnf are LIVE (bodied) in the compiled reduce module.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r19_module_sanity_and_wiring() {
    let reduce = parse_validate(tir("iota_reduce_root"), "iota_reduce_root");
    let bodied = |sym: &str| {
        reduce
            .functions
            .iter()
            .any(|f| f.name.contains(sym) && !f.blocks.is_empty())
    };
    for sym in [
        "build_recursor_rule_rhs",
        "try_iota_reduction",
        "whnf_inner",
        "whnf_impl",
        "instantiate_level_params_direct",
        "name_eq",
        "build_rec_env",
        "run_scenario",
        "get_recursive_field_flags",
    ] {
        assert!(bodied(sym), "{sym} must be bodied in the reduce module");
    }
    // the extern-leaf set is fully classified (jit() would panic otherwise).
    let _ = jit(tir("iota_reduce_root"), "iota_reduce_root");
    eprintln!(
        "sanity: build_recursor_rule_rhs + try_iota_reduction + whnf + instantiate_level_params + name_eq all LIVE (bodied); every extern leaf classified"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 8 — ARMED corruption of the REDUCE module: bump the anon seed (1723 ->
// 1724), re-JIT, and prove the reduced term DIVERGES from the pristine native one
// (every embedded real-Name hash shifts -> the whole ExprMeta tree shifts) — the
// reduce .tir is genuinely compiled+executed (not native-shadowed).
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn r19_armed_reduce_module_corruption() {
    let base = tir("iota_reduce_root");
    {
        let buf = jit(base, "iota_reduce_root");
        let f: ReduceFn = unsafe { std::mem::transmute(bind(&buf, "iota_reduce_root")) };
        for scenario in 0u64..8 {
            assert!(
                deep_eq(&native_reduce(scenario, 0), &jit_reduce(f, scenario, 0)),
                "pristine reduce {scenario}: native != JIT"
            );
        }
    }
    assert_eq!(
        base.matches("const u64 1723").count(),
        1,
        "anon seed 1723 must be unique in the reduce module"
    );
    let corrupted = base.replace("const u64 1723", "const u64 1724");
    assert!(corrupted != base, "corruption must change the text");
    let buf = jit(&corrupted, "iota_reduce_root(anon-seed-corrupted)");
    let f: ReduceFn = unsafe { std::mem::transmute(bind(&buf, "iota_reduce_root")) };
    // at least one scenario's reduced term must diverge (the base result z carries
    // no real family Name, so probe the Tree result which embeds Tree.leaf/node).
    let n_tree = native_reduce(4, 0);
    let j_tree = jit_reduce(f, 4, 0);
    assert!(
        !deep_eq(&n_tree, &j_tree),
        "corrupted reduce Tree result must DIVERGE from pristine native (real-Name hashes are load-bearing in the reduction)"
    );
    eprintln!(
        "armed: corrupting the anon seed in the REDUCE module diverges the Tree reduction (embedded real-Name hashes shift) — the reduce .tir is genuinely executed"
    );
}
