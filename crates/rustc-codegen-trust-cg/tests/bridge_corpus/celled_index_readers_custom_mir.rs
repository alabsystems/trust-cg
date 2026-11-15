// CORPUS FIXTURE — a CELLED index local read by EVERY `Index(local)` reader.
// An entry argument whose address is taken (`&raw const i`) is CELLED
// (`compute_scalar_cell_locals`): every later write (`i = K`) lands in the cell
// and never rebinds the SSA value. The readers of an `Index(i)` projection
// operand — `resolve_index_value` (an array through a reference, a memory-backed
// local array, a slice-element store), `lower_memory_slice_place_read` /
// `lower_slice_deref_element_load` (a slice read, a const-slice read),
// `lower_dyn_slice_element_use` (a `&[&dyn Tr]` element) and the slice-element
// borrow in `lower_scalar_ref` — read the index through the SSA binding, whose
// entry-arg fallback is the INCOMING parameter: each function below read the
// STALE index (a silent wrong value; the checksum was 198 at O0/O2/O3 at trust-cg
// 874c4b3ef). Custom MIR because rustc's own MIR copies an index into a fresh
// temporary first, so this shape is reachable today only through custom MIR —
// and through any lowering that cells a loop-carried index (the [TCG-SSA-071]
// cell retry). Order-sensitive checksum; correct exit = LLVM oracle (19 at O0/O2/O3).
#![no_std]
#![no_main]
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
use core::hint::black_box;
use core::intrinsics::mir::*;
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }

pub trait Tr { fn get(&self) -> u64; }
impl Tr for u64 { #[inline(never)] fn get(&self) -> u64 { *self * 2 } }
const T: &[u64] = &[3, 5, 7, 11, 13, 17, 19, 23];

// `(*a)[i]`, `a: &[u64; 8]` — the runtime-address walker (`resolve_index_value`).
#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
fn f_arr(a: &[u64; 8], i: usize) -> u64 {
    mir! {
        let p: *const usize;
        {
            p = &raw const i;
            i = 5;
            RET = (*a)[i];
            Return()
        }
    }
}

// `(*s)[i]`, `s: &[u64]` — a slice element read.
#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
fn f_slice(s: &[u64], i: usize) -> u64 {
    mir! {
        let p: *const usize;
        {
            p = &raw const i;
            i = 6;
            RET = (*s)[i];
            Return()
        }
    }
}

// `(*s)[i] = 99` — a slice element STORE (read back through an SSA index).
#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
fn f_store(s: &mut [u64], i: usize) -> u64 {
    mir! {
        let p: *const usize;
        let k: usize;
        {
            p = &raw const i;
            i = 2;
            (*s)[i] = 99;
            k = 2;
            RET = (*s)[k];
            Return()
        }
    }
}

// `r = &(*s)[i]; *r` — the slice-element borrow in `lower_scalar_ref`.
#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
fn f_borrow(s: &[u64], i: usize) -> u64 {
    mir! {
        let p: *const usize;
        let r: &u64;
        {
            p = &raw const i;
            i = 7;
            r = &(*s)[i];
            RET = *r;
            Return()
        }
    }
}

// `arr[i]` over a memory-backed LOCAL array (runtime index => memory slot).
#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
fn f_local(i: usize, x: u64, j: usize) -> u64 {
    mir! {
        let p: *const usize;
        let arr: [u64; 4];
        let x1: u64;
        let x2: u64;
        let x3: u64;
        {
            x1 = x + 1;
            x2 = x + 2;
            x3 = x + 3;
            arr = [x, x1, x2, x3];
            p = &raw const i;
            i = j;
            RET = arr[i];
            Return()
        }
    }
}

// `d = (*s)[i]`, `s: &[&dyn Tr]` — `lower_dyn_slice_element_use`.
#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
fn f_dyn(s: &[&dyn Tr], i: usize) -> u64 {
    mir! {
        let p: *const usize;
        let d: &dyn Tr;
        {
            p = &raw const i;
            i = 2;
            d = (*s)[i];
            Call(RET = Tr::get(d), ReturnTo(bb1), UnwindUnreachable())
        }
        bb1 = {
            Return()
        }
    }
}

// `(*s)[i]` over a CONST slice (a bound data pointer).
#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
fn f_const(i: usize) -> u64 {
    mir! {
        let p: *const usize;
        let s: &[u64];
        {
            s = T;
            p = &raw const i;
            i = 4;
            RET = (*s)[i];
            Return()
        }
    }
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a = black_box([3u64, 5, 7, 11, 13, 17, 19, 23]);
    let mut m = black_box([3u64, 5, 7, 11, 13, 17, 19, 23]);
    let (x, y, z) = (black_box(5u64), black_box(7u64), black_box(11u64));
    let v: [&dyn Tr; 3] = [&x, &y, &z];
    let rs = [
        f_arr(&a, black_box(1)),
        f_slice(black_box(&a[..]), black_box(1)),
        f_store(black_box(&mut m[..]), black_box(1)),
        f_borrow(black_box(&a[..]), black_box(1)),
        f_local(black_box(1), black_box(40), black_box(3)),
        f_dyn(black_box(&v[..]), black_box(0)),
        f_const(black_box(1)),
        m[1],
        m[2],
    ];
    let mut s: u64 = 0;
    let mut k = 0;
    while k < rs.len() {
        s = s.wrapping_mul(131).wrapping_add(rs[k]);
        k += 1;
    }
    (s % 251) as i32
}
