// wasm32 execution-differential corpus: closure `fn` pointers, 16-byte slice
// swaps and slice-tailed `Cell` pointers.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// * `cf_*`: non-capturing closures coerced to `fn(..)` pointers and called
//   through them — stored in a static table, a static scalar and a struct
//   field, held in a `const` value and a `const` slice, produced at run time
//   (a local and an argument) and reached through a `&dyn Fn` vtable. The
//   address rustc stores is the closure's `FnOnce::call_once` shim, whose
//   `rust-call` ABI untuples the arguments; the entry must accept exactly the
//   pointer's `fn(A, B, ..)` parameter list. `cf_const_plain` holds a plain
//   function in a `const` value, whose operand must be the code address.
// * `dy_*`: `&dyn Fn` / `&mut dyn FnMut` over a `fn(..)` pointer and a fn
//   item. A dynamic call passes the receiver and the spread arguments, so the
//   vtable slot must accept exactly that list.
// * `sw_*`: `<[T]>::swap` over 16-byte, 8-or-more-aligned elements (`i128`,
//   `u128`, `(u64, u64)`), whose alignment differs between wasm32 and 64-bit
//   hosts.
// * `ce_*`: `Cell::from_mut(&mut [T]).as_slice_of_cells()`, a fat pointer to
//   the slice-tailed `Cell<[T]>`, which is two 4-byte words on wasm32.
//
// wasm32-differential-flags: -Copt-level=2

#![no_std]
#![allow(dead_code)]

use core::cell::Cell;
use core::hint::black_box;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

fn add(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

fn sub(a: u32, b: u32) -> u32 {
    a.wrapping_sub(b)
}

// ---- closure `fn` pointers ----------------------------------------------------

static OPS: [fn(u32, u32) -> u32; 3] = [add, sub, |a, b| a ^ b.wrapping_mul(3)];
static ONE: fn(u64, u32) -> u64 = |a, b| a.rotate_left(b) ^ 7;
static NULLARY: fn() -> u32 = || 0x5eed;
static RD: fn(&u32) -> u32 = |r| r.wrapping_mul(5) ^ 1;
static FH: fn(f64, f64) -> f64 = |a, b| a * 1.5 - b;

struct Entry {
    name: &'static str,
    f: fn(u64) -> u64,
    w: u8,
}

static TABLE: [Entry; 2] = [
    Entry {
        name: "square",
        f: |x| x.wrapping_mul(x),
        w: 3,
    },
    Entry {
        name: "mix",
        f: |x| x ^ (x >> 7),
        w: 5,
    },
];

const CREF: &[fn(u32, u32) -> u32] = &[add, |a, b| a.wrapping_sub(b) ^ 0x55];
const CVAL: fn(u32, u32) -> u32 = |a, b| a.wrapping_mul(b) ^ 0x1234;
const CPLAIN: fn(u32, u32) -> u32 = sub;

#[inline(never)]
fn apply(f: fn(u32, u32) -> u32, a: u32, b: u32) -> u32 {
    f(a, b)
}

#[no_mangle]
pub extern "C" fn cf_static_ops(k: u32, x: u32) -> u32 {
    OPS[(k % 3) as usize](x, k)
}

#[no_mangle]
pub extern "C" fn cf_static_scalars(k: u32, x: u32) -> u64 {
    let r = RD(&x) ^ NULLARY();
    ONE(u64::from(x) | u64::from(k) << 32, k) ^ u64::from(r)
}

#[no_mangle]
pub extern "C" fn cf_static_float(a: f64, b: f64) -> f64 {
    FH(a, b)
}

#[no_mangle]
pub extern "C" fn cf_struct_field(k: u32, x: u64) -> u64 {
    let e = &TABLE[(k % 2) as usize];
    (e.f)(x) ^ (e.name.len() as u64) << 40 ^ u64::from(e.w)
}

#[no_mangle]
pub extern "C" fn cf_const_ref(k: u32, x: u32) -> u32 {
    CREF[(k % 2) as usize](x, k)
}

#[no_mangle]
pub extern "C" fn cf_const_value(k: u32, x: u32) -> u32 {
    black_box(CVAL)(x, k)
}

#[no_mangle]
pub extern "C" fn cf_const_plain(k: u32, x: u32) -> u32 {
    let f = if k & 1 == 0 { CPLAIN } else { add };
    black_box(f)(x, k)
}

#[no_mangle]
pub extern "C" fn cf_local(k: u32, x: u32) -> u32 {
    let f: fn(u32, u32) -> u32 = if k & 1 == 0 {
        |a, b| a.rotate_left(b)
    } else {
        |a, b| a.wrapping_mul(b | 1)
    };
    black_box(f)(x, k)
}

#[no_mangle]
pub extern "C" fn cf_arg(k: u32, x: u32) -> u32 {
    apply(|a, b| a.wrapping_add(b.wrapping_mul(3)), x, k) ^ apply(|a, b| a & !b, k, x)
}

fn mix(a: u32, b: u32) -> u32 {
    a.rotate_left(b & 31) ^ b.wrapping_mul(7)
}

#[inline(never)]
fn call_dyn_mut(f: &mut dyn FnMut(u32, u32) -> u32, a: u32, b: u32) -> u32 {
    f(a, b) ^ f(b, a)
}

#[no_mangle]
pub extern "C" fn dy_fn_pointer(k: u32, x: u32) -> u32 {
    let f: fn(u32, u32) -> u32 = mix;
    let d: &dyn Fn(u32, u32) -> u32 = black_box(&f);
    d(x, k)
}

#[no_mangle]
pub extern "C" fn dy_fn_item(k: u32, x: u32) -> u32 {
    let item = black_box(mix);
    let d: &dyn Fn(u32, u32) -> u32 = &item;
    let mut g: [fn(u32, u32) -> u32; 2] = [sub, add];
    d(x, k) ^ call_dyn_mut(&mut g[(k & 1) as usize], k, x)
}

#[no_mangle]
pub extern "C" fn dy_fn_unary(k: u32, x: u64) -> u64 {
    let f: fn(u64) -> u64 = |v| v.wrapping_mul(0x9e37_79b9_7f4a_7c15);
    let d: &dyn Fn(u64) -> u64 = black_box(&f);
    d(x) ^ u64::from(k)
}

#[no_mangle]
pub extern "C" fn cf_dyn(k: u32, x: u32) -> u32 {
    let f: fn(u32, u32) -> u32 = |a, b| a ^ b.rotate_right(3);
    let d: &dyn Fn(u32, u32) -> u32 = black_box(&f);
    d(x, k)
}

// ---- `<[T]>::swap` over 16-byte elements ----------------------------------------

#[no_mangle]
pub extern "C" fn sw_i128(a: i64, b: u32) -> i64 {
    let mut v = [a as i128, -(a as i128), (a as i128) << 70];
    v.swap((b % 3) as usize, ((b / 3) % 3) as usize);
    (v[0] ^ (v[1] >> 64) ^ (v[2] >> 7)) as i64
}

#[inline(never)]
fn sort_u128(v: &mut [u128]) {
    let mut i = 0;
    while i < v.len() {
        let mut j = 0;
        while j + 1 < v.len() - i {
            if v[j] > v[j + 1] {
                v.swap(j, j + 1);
            }
            j += 1;
        }
        i += 1;
    }
}

#[no_mangle]
pub extern "C" fn sw_sort_u128(a: u64, b: u64) -> u64 {
    let x = u128::from(a) << 64 | u128::from(b);
    let mut v = [x, x.rotate_left(17), !x, x.wrapping_mul(3), u128::from(b)];
    sort_u128(&mut v);
    let mut h = 0u64;
    let mut i = 0;
    while i < v.len() {
        h = h.rotate_left(9) ^ (v[i] >> 64) as u64 ^ v[i] as u64;
        i += 1;
    }
    h
}

#[no_mangle]
pub extern "C" fn sw_pair(a: u64, k: u32) -> u64 {
    let mut v = [(a, !a), (a >> 3, a << 5), (7, a ^ 0x55)];
    let i = (k % 3) as usize;
    let j = ((k >> 2) % 3) as usize;
    v.swap(i, j);
    v[0].0 ^ v[0].1.rotate_left(1) ^ v[1].0.rotate_left(2) ^ v[1].1.rotate_left(3) ^ v[2].0 ^ v[2].1
}

// ---- `Cell<[T]>` fat pointers ------------------------------------------------------

#[no_mangle]
pub extern "C" fn ce_cell_slice(x: u32, n: u32) -> u32 {
    let mut a = [x, x ^ 1, x ^ 2, x ^ 3, x ^ 4];
    let cs: &[Cell<u32>] = Cell::from_mut(&mut a[..]).as_slice_of_cells();
    let n = (n % 5) as usize;
    let mut i = 0;
    while i < n {
        cs[i].set(cs[i].get().wrapping_add(cs[4 - i].get()));
        i += 1;
    }
    a[0] ^ a[1].rotate_left(1) ^ a[2].rotate_left(2) ^ a[3].rotate_left(3) ^ a[4].rotate_left(4)
}

#[inline(never)]
fn rotate_cells(cs: &Cell<[u64]>, k: usize) -> u64 {
    let cells = cs.as_slice_of_cells();
    let len = cells.len();
    let mut i = 0;
    while i < len {
        let j = (i + k) % len;
        let t = cells[j].replace(cells[i].get());
        cells[i].set(t);
        i += 1;
    }
    let mut h = len as u64;
    let mut i = 0;
    while i < len {
        h = h.rotate_left(7) ^ cells[i].get();
        i += 1;
    }
    h
}

#[no_mangle]
pub extern "C" fn ce_cell_u64(x: u64, k: u32) -> u64 {
    let mut a = [x, !x, x >> 9, x.rotate_left(33)];
    let len = 1 + (k % 4) as usize;
    rotate_cells(Cell::from_mut(&mut a[..len]), (k >> 2) as usize % 4) ^ a[0]
}
