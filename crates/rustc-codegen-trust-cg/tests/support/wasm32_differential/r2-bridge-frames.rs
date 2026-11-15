// wasm32 execution-differential corpus: stack frames and address identity of
// the rustc bridge's MIR lowering.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Two properties of the frames the bridge emits, both shared by every target:
// * ONE SLOT PER ALLOCA SITE. The bridge's use-site temporaries (a `&dyn` or
//   `&T` borrow of a register-held local, a by-value aggregate argument, a
//   constant iterator image, iterator scratch, a closure's argument tuple) live
//   in the entry block. trust-ir gives every execution of an `Alloca` fresh
//   storage, so one left in a loop body grows the frame per iteration; the
//   `*_loop` exports run more than 65,536 iterations (140,000 or more), which
//   exhausts the 1 MiB wasm32 shadow stack when a temporary is carved per
//   iteration.
// * ONE ADDRESS PER LIVE LOCAL. Two borrows of the same local compare equal
//   (`ptr::eq`, `as usize`) whether they are passed to calls, unsized to
//   `&dyn`, stored in a struct or taken `&mut` then `&`; borrows of two fields
//   of one local are exactly their layout offset apart; a reference joined
//   from two locals (whole locals, fields or elements, of mixed kinds) equals
//   the direct borrow of the one it selected. The two locals a join selects
//   between are distinct objects, so borrowing each of them directly as well
//   is accepted (`fr_join_*_separately`).
//
// The optimized configurations cover the same shapes after MIR inlining.
//
// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=3

#![no_std]
#![allow(dead_code)]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

/// Every long loop runs at least this many iterations.
const LONG: u32 = 140_000;

#[derive(Clone, Copy)]
pub struct P {
    a: u32,
    b: u32,
}

#[derive(Clone, Copy)]
pub struct Big {
    a: u64,
    b: u64,
    c: u64,
    d: u32,
}

#[derive(Clone, Copy)]
pub struct Q {
    x: u64,
    y: u16,
    z: u8,
}

#[derive(Clone, Copy)]
pub struct Y(u32);

pub struct N {
    p: P,
    c: u32,
}

pub struct Holder<'a> {
    r: &'a u32,
    k: u32,
}

pub struct R<'a> {
    r: &'a u32,
    k: u32,
}

pub struct A {
    x: u64,
}

trait Tr {
    fn g(&self) -> u32;
}

impl Tr for P {
    fn g(&self) -> u32 {
        self.a ^ self.b
    }
}

impl Tr for Y {
    fn g(&self) -> u32 {
        self.0
    }
}

impl Tr for u32 {
    fn g(&self) -> u32 {
        *self
    }
}

trait Tr64 {
    fn f(&self, k: u64) -> u64;
}

impl Tr64 for A {
    fn f(&self, k: u64) -> u64 {
        self.x.wrapping_mul(3) ^ k
    }
}

struct X3(u32);
struct Y3(u32);

impl Tr for X3 {
    fn g(&self) -> u32 {
        self.0.wrapping_mul(3)
    }
}

impl Tr for Y3 {
    fn g(&self) -> u32 {
        self.0 ^ 0x55
    }
}

#[inline(never)]
fn same<T>(a: &T, b: &T) -> u32 {
    core::ptr::eq(a, b) as u32
}

#[inline(never)]
fn addr<T>(a: &T) -> usize {
    a as *const T as usize
}

#[inline(never)]
fn addr_mut<T>(a: &mut T) -> usize {
    a as *mut T as usize
}

#[inline(never)]
fn dyn_addr(d: &dyn Tr) -> usize {
    d as *const dyn Tr as *const u8 as usize
}

#[inline(never)]
fn holder_same(h: &Holder, r: &u32) -> u32 {
    core::ptr::eq(h.r, r) as u32 + h.k
}

#[inline(never)]
fn triple(a: &u32) -> u32 {
    a.wrapping_mul(3)
}

#[inline(never)]
fn bump(a: &mut u32) {
    *a = a.wrapping_add(3);
}

#[inline(never)]
fn bump_p(p: &mut P) {
    p.a = p.a.wrapping_add(1);
    p.b ^= 7;
}

#[inline(never)]
fn sum_p(p: &P) -> u32 {
    p.a.wrapping_add(p.b)
}

#[inline(never)]
fn by_val(p: P) -> u32 {
    p.a ^ p.b.rotate_left(3)
}

#[inline(never)]
fn by_val_big(p: Big) -> u64 {
    p.a ^ p.b ^ p.c ^ p.d as u64
}

#[inline(never)]
fn apply<F: Fn(u32, u32) -> u32>(f: &F, x: u32, y: u32) -> u32 {
    f(x, y)
}

#[inline(never)]
fn call_dyn(d: &dyn Tr64, k: u64) -> u64 {
    d.f(k)
}

#[inline(never)]
fn probe(arr: &[&dyn Tr; 3], y: &Y3) -> u32 {
    let p = arr as *const [&dyn Tr; 3] as *const u32;
    let w = unsafe { core::ptr::read(p.add(2)) };
    (w == (y as *const Y3 as usize as u32)) as u32
}

// ---- one slot per alloca site: loops longer than 65,536 iterations ----

/// A `&dyn` borrow of a register-held aggregate built in the loop body.
#[no_mangle]
pub extern "C" fn fr_dyn_loop(x: u64) -> u64 {
    let n = LONG as u64 + (x & 0x3ff);
    let mut acc = 0u64;
    let mut i = 0u64;
    while i < n {
        let a = A { x: x ^ i };
        acc = acc.wrapping_add(call_dyn(&a, i));
        i += 1;
    }
    acc
}

/// A slice iterator over an array built in the loop body.
#[no_mangle]
pub extern "C" fn fr_arr_sum_loop(x: u64) -> u64 {
    let n = LONG as u64 + (x & 0x3ff);
    let mut acc = 0u64;
    let mut i = 0u64;
    while i < n {
        let arr = [i, x, i ^ x, 3];
        acc = acc.wrapping_add(arr.iter().fold(0u64, |s, v| s.wrapping_add(*v)));
        i += 1;
    }
    acc
}

/// A `&T` of an outer scalar in every iteration: one address throughout.
#[no_mangle]
pub extern "C" fn fr_scalar_ref_loop(v: u32) -> u32 {
    let n = LONG + (v & 0x3ff);
    let y = v ^ 3;
    let first = addr(&y);
    let mut ok = 1u32;
    let mut i = 0;
    while i < n {
        if addr(&y) != first {
            ok = 0;
        }
        i += 1;
    }
    ok + (y & 4)
}

#[no_mangle]
pub extern "C" fn fr_agg_ref_loop(v: u32) -> u32 {
    let n = LONG + (v & 0x3ff);
    let mut acc = 0u32;
    let mut i = 0u32;
    while i < n {
        let p = P { a: v ^ i, b: i };
        acc = acc.wrapping_add(sum_p(&p));
        i += 1;
    }
    acc
}

#[no_mangle]
pub extern "C" fn fr_mut_agg_loop(v: u32) -> u32 {
    let n = LONG + (v & 0x3ff);
    let mut p = P { a: v, b: 1 };
    let mut i = 0u32;
    while i < n {
        bump_p(&mut p);
        i += 1;
    }
    p.a ^ p.b
}

#[no_mangle]
pub extern "C" fn fr_dyn_scalar_loop(v: u32) -> u32 {
    let n = LONG + (v & 0x3ff);
    let mut acc = 0u32;
    let mut i = 0u32;
    while i < n {
        let y = v ^ i;
        let d: &dyn Tr = &y;
        acc = acc.wrapping_add(d.g());
        i += 1;
    }
    acc
}

#[no_mangle]
pub extern "C" fn fr_byval_loop(v: u32) -> u32 {
    let n = LONG + (v & 0x3ff);
    let mut acc = 0u32;
    let mut i = 0u32;
    while i < n {
        acc = acc.wrapping_add(by_val(P { a: v ^ i, b: i }));
        i += 1;
    }
    acc
}

#[no_mangle]
pub extern "C" fn fr_byval_big_loop(v: u64) -> u64 {
    let n = LONG as u64 + (v & 0x3ff);
    let mut acc = 0u64;
    let mut i = 0u64;
    while i < n {
        acc = acc.wrapping_add(by_val_big(Big {
            a: v,
            b: i,
            c: v ^ i,
            d: i as u32,
        }));
        i += 1;
    }
    acc
}

/// A constant `Range` driven through `map` + `sum` in every iteration.
#[no_mangle]
pub extern "C" fn fr_range_sum_loop(v: u32) -> u32 {
    let n = LONG + (v & 0x3ff);
    let mut acc = 0u32;
    let mut i = 0u32;
    while i < n {
        acc = acc.wrapping_add((0..8u32).map(|k| k ^ v).sum::<u32>());
        i += 1;
    }
    acc
}

#[no_mangle]
pub extern "C" fn fr_filter_count_loop(v: u32) -> u32 {
    let n = LONG + (v & 0x3ff);
    let mut acc = 0u32;
    let mut i = 0u32;
    while i < n {
        acc = acc.wrapping_add((0..6u32).filter(|k| (k ^ v) & 1 == 0).count() as u32);
        i += 1;
    }
    acc
}

#[no_mangle]
pub extern "C" fn fr_closure_loop(v: u32) -> u32 {
    let n = LONG + (v & 0x3ff);
    let mut acc = 0u32;
    let mut i = 0u32;
    let k = v | 1;
    let f = |x: u32, y: u32| x.wrapping_mul(k) ^ y;
    while i < n {
        acc = acc.wrapping_add(apply(&f, i, v));
        i += 1;
    }
    acc
}

#[no_mangle]
pub extern "C" fn fr_slice_filter_fold_loop(v: u32) -> u32 {
    let n = LONG + (v & 0x3ff);
    let mut acc = 0u32;
    let mut i = 0u32;
    while i < n {
        let arr = [i, v, i ^ v, 3];
        acc = acc.wrapping_add(
            arr.iter()
                .filter(|x| **x & 1 == 1)
                .fold(0u32, |s, x| s.wrapping_add(*x)),
        );
        i += 1;
    }
    acc
}

// ---- one address per live local ----

/// A `&dyn` array element and a `&T` of the same local share its address.
#[no_mangle]
pub extern "C" fn fr_dyn_array_layout(v: u32) -> u32 {
    let x = X3(v);
    let y = Y3(v ^ 1);
    let z = X3(v ^ 2);
    let arr: [&dyn Tr; 3] = [&x, &y, &z];
    probe(&arr, &y) + 2 * ((core::mem::size_of::<[&dyn Tr; 3]>() == 24) as u32)
}

#[no_mangle]
pub extern "C" fn fr_ptr_eq_two_borrows(v: u32) -> u32 {
    let y = v ^ 7;
    same(&y, &y) * 10 + y % 7
}

#[no_mangle]
pub extern "C" fn fr_raw_addr_compare(v: u32) -> u32 {
    let y = v ^ 3;
    let p = &y as *const u32 as usize;
    let q = &y as *const u32 as usize;
    (p == q) as u32 + (y & 1)
}

#[no_mangle]
pub extern "C" fn fr_two_calls(v: u32) -> u32 {
    let y = v.wrapping_mul(5);
    (addr(&y) == addr(&y)) as u32 + (y & 2)
}

#[no_mangle]
pub extern "C" fn fr_struct_held_borrow(v: u32) -> u32 {
    let y = v | 1;
    let h = Holder { r: &y, k: v & 4 };
    holder_same(&h, &y)
}

#[no_mangle]
pub extern "C" fn fr_mut_then_shared(v: u32) -> u32 {
    let mut y = v;
    let a = addr_mut(&mut y);
    y = y.wrapping_add(1);
    let b = addr(&y);
    (a == b) as u32 * 4 + (y & 3)
}

#[no_mangle]
pub extern "C" fn fr_one_ref_twice(v: u32) -> u32 {
    let y = v ^ 9;
    let r = &y;
    same(r, r) + (*r & 8)
}

#[no_mangle]
pub extern "C" fn fr_newtype_dyn(v: u32) -> u32 {
    let y = Y(v ^ 1);
    same(&y, &y)
        + 2 * (addr(&y) == dyn_addr(&y)) as u32
        + 4 * (addr(&y) == addr(&y.0)) as u32
        + (y.0 & 8)
}

#[no_mangle]
pub extern "C" fn fr_pair_whole_and_field(v: u32) -> u32 {
    let p = P { a: v, b: v ^ 5 };
    same(&p, &p) + 2 * (addr(&p) == addr(&p.a)) as u32 + (p.b & 8)
}

#[no_mangle]
pub extern "C" fn fr_field_offsets(v: u32) -> u32 {
    let p = P { a: v, b: v ^ 3 };
    ((addr(&p.b) - addr(&p.a)) as u32) + 8 * (addr(&p) == addr(&p.a)) as u32 + (p.a & 0x10)
}

#[no_mangle]
pub extern "C" fn fr_mixed_field_offsets(v: u32) -> u32 {
    let q = Q {
        x: v as u64,
        y: v as u16,
        z: v as u8,
    };
    let o1 = addr(&q.y).wrapping_sub(addr(&q));
    let o2 = addr(&q.z).wrapping_sub(addr(&q));
    (o1 as u32) * 100 + o2 as u32 + (q.z & 1) as u32
}

#[no_mangle]
pub extern "C" fn fr_nested_field_offsets(v: u32) -> u32 {
    let n = N {
        p: P { a: v, b: 2 },
        c: v ^ 3,
    };
    ((addr(&n.c) - addr(&n.p)) as u32) + 16 * (addr(&n) == addr(&n.p.a)) as u32 + (n.c & 32) + n.p.b
}

#[no_mangle]
pub extern "C" fn fr_tuple_field_offsets(v: u32) -> u32 {
    let t = (v as u8, v ^ 1);
    ((addr(&t.1) as u32).wrapping_sub(addr(&t.0) as u32)) * 2 + same(&t, &t) + (t.1 & 8)
}

#[no_mangle]
pub extern "C" fn fr_wide_tuple_offsets(v: u64) -> u64 {
    let t = (v as u128, v as u32);
    (addr(&t.1) - addr(&t.0)) as u64 + same(&t, &t) as u64
}

#[no_mangle]
pub extern "C" fn fr_float_tuple_offsets(v: u32) -> u32 {
    let t = (v as f32, v as u16);
    (addr(&t.1) as u32).wrapping_sub(addr(&t.0) as u32) + same(&t, &t)
}

#[no_mangle]
pub extern "C" fn fr_array_element_offsets(v: u32) -> u32 {
    let a = [v, v ^ 1];
    ((addr(&a[1]) - addr(&a[0])) as u32) + 8 * (addr(&a) == addr(&a[0])) as u32 + (a[1] & 16)
}

#[no_mangle]
pub extern "C" fn fr_pointer_field_offsets(v: u32) -> u32 {
    let x = v;
    let s = R { r: &x, k: v ^ 1 };
    (addr(&s.k) as u32).wrapping_sub(addr(&s.r) as u32) + same(&s, &s) + *s.r
}

#[no_mangle]
pub extern "C" fn fr_branch_scalar(v: u32) -> u32 {
    let a = v;
    let b = v ^ 1;
    let r = if v & 1 == 0 { &a } else { &b };
    same(r, &a) + 2 * same(r, &b) + 4 * (*r & 1)
}

#[no_mangle]
pub extern "C" fn fr_branch_aggregate(v: u32) -> u32 {
    let p = P { a: v, b: v ^ 1 };
    let q = P { a: v ^ 2, b: 3 };
    let r = if v & 1 == 0 { &p } else { &q };
    same(r, &p) + 2 * same(r, &q) + (r.b & 4)
}

#[no_mangle]
pub extern "C" fn fr_branch_float(v: f64) -> f64 {
    let x = v * 2.0;
    let y = v + 1.0;
    let r = if v > 0.5 { &x } else { &y };
    (same(r, &x) + 2 * same(r, &y)) as f64 + *r
}

#[no_mangle]
pub extern "C" fn fr_mut_writeback_identity(v: u32) -> u32 {
    let mut y = v;
    let a0 = addr(&y);
    bump(&mut y);
    let a1 = addr(&y);
    bump(&mut y);
    y.wrapping_mul(2) + (a0 == a1) as u32
}

#[no_mangle]
pub extern "C" fn fr_dyn_identity_in_loop(v: u32, n: u32) -> u32 {
    let y = P { a: v, b: v ^ 9 };
    let first = dyn_addr(&y);
    let mut ok = 1u32;
    let mut acc = 0u32;
    let mut i = 0;
    while i < n % 40 {
        let d: &dyn Tr = &y;
        if dyn_addr(d) != first {
            ok = 0;
        }
        acc = acc.wrapping_add(d.g());
        i += 1;
    }
    ok + 2 * (addr(&y) == first) as u32 + (acc & 0xfc)
}

#[no_mangle]
pub extern "C" fn fr_u64_two_borrows(v: u64) -> u64 {
    let y = v ^ 13;
    same(&y, &y) as u64 + 2 * (addr(&y) == addr(&y)) as u64
}

#[no_mangle]
pub extern "C" fn fr_join_then_borrow_each_separately(v: u32) -> u32 {
    let a = v;
    let b = v ^ 1;
    let r = if v & 1 == 0 { &a } else { &b };
    let x = *r;
    x.wrapping_add(triple(&a)).wrapping_add(triple(&b))
}

#[no_mangle]
pub extern "C" fn fr_join_then_compare_separately(v: u32) -> u32 {
    let a = v;
    let b = v ^ 5;
    let r = if v & 2 == 0 { &a } else { &b };
    let x = *r;
    x.wrapping_add(a.cmp(&b) as i32 as u32)
}

#[no_mangle]
pub extern "C" fn fr_join_field_and_scalar(v: u32) -> u32 {
    let p = P { a: v, b: v ^ 3 };
    let x = v ^ 7;
    let r = if v & 1 == 0 { &p.b } else { &x };
    same(r, &p.b) + 2 * same(r, &x) + 4 * (addr(&p) + 4 == addr(r)) as u32 + 8 * (*r & 0xff)
}

#[no_mangle]
pub extern "C" fn fr_join_fields_of_two_locals(v: u32) -> u32 {
    let p = P { a: v, b: v ^ 3 };
    let q = P { a: v ^ 9, b: 1 };
    let r = if v & 1 == 0 { &p.b } else { &q.a };
    same(r, &q.a) + 2 * same(r, &p.b) + 4 * (*r & 0xff)
}

#[no_mangle]
pub extern "C" fn fr_join_wide_tuple_field_and_scalar(v: u64) -> u64 {
    let p = (v, v ^ 3);
    let x = v ^ 7;
    let r = if v & 1 == 0 { &p.1 } else { &x };
    same(r, &x) as u64 + 2 * same(r, &p.1) as u64 + 4 * (*r & 0xff)
}

#[no_mangle]
pub extern "C" fn fr_join_element_and_scalar(v: u32) -> u32 {
    let arr = [v, v ^ 1, v ^ 2];
    let x = v ^ 7;
    let i = (v % 3) as usize;
    let r = if v & 1 == 0 { &arr[i] } else { &x };
    same(r, &x) + 2 * same(r, &arr[i]) + 4 * (*r & 0xff)
}

#[no_mangle]
pub extern "C" fn fr_overlapping_joins(v: u32) -> u32 {
    let x = v;
    let y = v ^ 1;
    let z = v ^ 2;
    let r1 = if v & 1 == 0 { &x } else { &y };
    let r2 = if v & 2 == 0 { &y } else { &z };
    same(r1, r2) + 2 * (*r1 & 0xf)
}
