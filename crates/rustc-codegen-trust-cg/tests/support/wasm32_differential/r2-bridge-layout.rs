// wasm32 execution-differential corpus: rustc LAYOUT of aggregates reached
// through a reference.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// An undeclared trust-ir tuple is laid out by the C rule (declaration order,
// natural alignment). Every aggregate here is one rustc lays out differently:
// a struct, tuple or single-variant enum whose fields rustc reorders, a
// `#[repr(packed)]` / `#[repr(packed(N))]` struct, a `#[repr(align(N))]` struct
// an over-aligned single-scalar newtype, and a tagged single-variant enum
// (`#[repr(C)]` / `#[repr(uN)]`: a tag word ahead of the fields, which also
// crosses calls by value). Each is borrowed, passed by
// reference, read and written field-wise and whole through the reference,
// copied with `ptr::copy_nonoverlapping` / `ptr::swap`, reinterpreted through a
// raw pointer at rustc's offsets, and has its address alignment observed. Every
// export takes and returns scalars.

// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=3 -Coverflow-checks=on

#![no_std]
#![allow(dead_code)]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

// --- a struct rustc reorders: `b` at 0, `a` at 4, `c` at 5 -------------------

#[derive(Clone, Copy)]
struct R {
    a: u8,
    b: u32,
    c: u8,
}

#[inline(never)]
fn r_fields(r: &R) -> u32 {
    (r.a as u32) * 1000 + r.b + (r.c as u32) * 7
}

#[inline(never)]
fn r_raw_c(r: &R) -> u32 {
    unsafe { *((r as *const R as *const u8).add(core::mem::offset_of!(R, c))) as u32 }
}

#[inline(never)]
fn r_copy(r: &R) -> u32 {
    let s = *r;
    (s.a as u32) * 1000 + s.b + (s.c as u32) * 7
}

#[inline(never)]
fn r_store(r: &mut R, x: u32) {
    *r = R {
        a: x as u8,
        b: x ^ 9,
        c: 3,
    };
}

#[inline(never)]
fn r_bump(r: &mut R, x: u32) {
    r.b = r.b.wrapping_add(x);
    r.a = r.a.wrapping_add(1);
}

#[no_mangle]
pub extern "C" fn lay_reord_read(x: u32) -> u32 {
    let r = R {
        a: x as u8,
        b: x.wrapping_mul(3),
        c: (x >> 8) as u8,
    };
    r_fields(&r)
        .wrapping_add(r_raw_c(&r))
        .wrapping_add(r_copy(&r))
}

#[no_mangle]
pub extern "C" fn lay_reord_store(x: u32) -> u32 {
    let mut r = R { a: 1, b: 2, c: 3 };
    r_store(&mut r, x);
    let stored = r_fields(&r);
    r_bump(&mut r, x);
    stored ^ (r.a as u32) * 1000 ^ r.b ^ (r.c as u32) * 7
}

#[inline(never)]
fn r_pick(a: &[R; 3], i: usize) -> u32 {
    r_fields(&a[i % 3])
}

#[no_mangle]
pub extern "C" fn lay_reord_array(x: u32) -> u32 {
    let a = [
        R { a: 1, b: x, c: 2 },
        R {
            a: 3,
            b: x ^ 1,
            c: 4,
        },
        R {
            a: 5,
            b: 6,
            c: x as u8,
        },
    ];
    r_pick(&a, x as usize)
}

#[inline(never)]
fn r_assign(dst: &mut R, src: &R) {
    *dst = *src;
}

#[inline(never)]
fn r_make(x: u32) -> R {
    R {
        a: x as u8,
        b: x ^ 1,
        c: 2,
    }
}

#[inline(never)]
fn r_store_call(r: &mut R, x: u32) {
    *r = r_make(x);
}

#[no_mangle]
pub extern "C" fn lay_reord_assign(x: u32) -> u32 {
    let mut a = R { a: 1, b: 2, c: 3 };
    let b = R {
        a: x as u8,
        b: x,
        c: 9,
    };
    r_assign(&mut a, &b);
    let copied = r_fields(&a);
    r_store_call(&mut a, x);
    copied ^ r_fields(&a)
}

// --- a tuple rustc reorders: `.1` at 0, `.2` at 8, `.0` at 10 ----------------

#[inline(never)]
fn t_sum(t: &(u8, u64, u16)) -> u64 {
    t.0 as u64 + t.1 + t.2 as u64 * 5
}

#[inline(never)]
fn t_store(t: &mut (u8, u64, u16), x: u64) {
    *t = (x as u8, x ^ 7, 3);
}

#[no_mangle]
pub extern "C" fn lay_tuple(x: u64) -> u64 {
    let mut t = (1u8, x, 2u16);
    let before = t_sum(&t);
    t_store(&mut t, x);
    before ^ t_sum(&t)
}

#[inline(never)]
fn t_copy(dst: &mut (u8, u32, u8), src: &(u8, u32, u8)) {
    unsafe { core::ptr::copy_nonoverlapping(src as *const _, dst as *mut _, 1) }
}

#[no_mangle]
pub extern "C" fn lay_tuple_copy(x: u32) -> u32 {
    let mut d = (0u8, 0u32, 0u8);
    let s = (x as u8, x.wrapping_mul(3), (x >> 8) as u8);
    t_copy(&mut d, &s);
    (d.0 as u32) * 1000 + d.1 + (d.2 as u32) * 7
}

// --- a single-variant enum whose variant fields rustc reorders ---------------

#[derive(Clone, Copy)]
enum E {
    V(u8, u32, u8),
}

#[inline(never)]
fn e_fields(e: &E) -> u32 {
    match e {
        E::V(a, b, c) => (*a as u32) * 1000 + *b + (*c as u32) * 7,
    }
}

#[inline(never)]
fn e_raw_word(e: &E) -> u32 {
    unsafe { *(e as *const E as *const u32) }
}

#[inline(never)]
fn e_bump(e: &mut E, x: u32) {
    match e {
        E::V(a, b, _) => {
            *a = a.wrapping_add(x as u8);
            *b ^= x;
        }
    }
}

#[no_mangle]
pub extern "C" fn lay_enum_read(x: u32) -> u32 {
    let e = E::V(x as u8, x.wrapping_mul(3), (x >> 8) as u8);
    e_fields(&e)
        .wrapping_add(e_raw_word(&e))
        .wrapping_add(core::mem::size_of::<E>() as u32 * 100_000)
}

#[no_mangle]
pub extern "C" fn lay_enum_write(x: u32) -> u32 {
    let mut e = E::V(x as u8, 5, 6);
    e_bump(&mut e, x);
    e_fields(&e)
}

#[derive(Clone, Copy)]
enum E2 {
    V { a: u16, b: u64, c: u8 },
}

#[inline(never)]
fn e2_store(e: &mut E2, x: u64) {
    *e = E2::V {
        a: x as u16,
        b: x ^ 3,
        c: 1,
    };
}

#[inline(never)]
fn e2_copy(e: &E2) -> u64 {
    let E2::V { a, b, c } = *e;
    a as u64 * 3 + b + c as u64 * 11
}

#[no_mangle]
pub extern "C" fn lay_enum_store(x: u64) -> u64 {
    let mut e = E2::V { a: 1, b: 2, c: 3 };
    let before = e2_copy(&e);
    e2_store(&mut e, x);
    before ^ e2_copy(&e)
}

// --- packed structs: offsets below the natural ones --------------------------

#[repr(packed)]
#[derive(Clone, Copy)]
struct P(u8, u32);

#[inline(never)]
fn p_fields(p: &P) -> u32 {
    let b = p.1;
    (p.0 as u32) * 1000 + b
}

#[inline(never)]
fn p_raw(p: &P) -> u32 {
    unsafe { core::ptr::read_unaligned((p as *const P as *const u8).add(1) as *const u32) }
}

#[inline(never)]
fn p_copy(p: &P) -> u32 {
    let q = *p;
    let b = q.1;
    b ^ q.0 as u32
}

#[no_mangle]
pub extern "C" fn lay_packed(x: u32) -> u32 {
    let p = P(x as u8, x.wrapping_mul(3));
    p_fields(&p)
        .wrapping_add(p_raw(&p))
        .wrapping_add(p_copy(&p))
}

#[inline(never)]
fn p_assign(dst: &mut P, src: &P) {
    *dst = *src;
}

#[no_mangle]
pub extern "C" fn lay_packed_assign(x: u32) -> u32 {
    let mut a = P(1, 2);
    let b = P(x as u8, x);
    p_assign(&mut a, &b);
    let v = a.1;
    v + a.0 as u32
}

#[repr(C, packed(2))]
#[derive(Clone, Copy)]
struct P2 {
    a: u8,
    b: u32,
    c: u16,
}

#[inline(never)]
fn p2_fields(p: &P2) -> u32 {
    let b = p.b;
    let c = p.c;
    (p.a as u32) ^ b ^ ((c as u32) << 3)
}

#[inline(never)]
fn p2_raw_b_low(p: &P2) -> u32 {
    unsafe { *((p as *const P2 as *const u8).add(2) as *const u16) as u32 }
}

#[no_mangle]
pub extern "C" fn lay_packed2(x: u32) -> u32 {
    let p = P2 {
        a: x as u8,
        b: x.wrapping_mul(7),
        c: x as u16 ^ 0x55,
    };
    p2_fields(&p)
        .wrapping_add(p2_raw_b_low(&p))
        .wrapping_add(core::mem::size_of::<P2>() as u32 * 1000)
}

#[repr(packed(2))]
#[derive(Clone, Copy)]
struct Q {
    a: u8,
    b: u64,
    c: u8,
}

#[inline(never)]
fn q_fields(q: &Q) -> u64 {
    let b = q.b;
    (q.a as u64) ^ b ^ ((q.c as u64) << 40)
}

#[inline(never)]
fn q_set(q: &mut Q, x: u64) {
    q.b = x;
    q.c = 17;
}

#[inline(never)]
fn q_store(q: &mut Q, x: u64) {
    *q = Q {
        a: 9,
        b: x ^ 1,
        c: x as u8,
    };
}

#[no_mangle]
pub extern "C" fn lay_packed_mut(x: u64) -> u64 {
    let mut q = Q {
        a: x as u8,
        b: 3,
        c: 4,
    };
    let first = q_fields(&q);
    q_set(&mut q, x ^ 99);
    let second = q_fields(&q);
    q_store(&mut q, x);
    first.wrapping_add(second).wrapping_add(q_fields(&q))
}

// --- over-aligned structs: a larger size and alignment than the fields' ------

#[repr(C, align(16))]
#[derive(Clone, Copy)]
struct A(u32, u32);

#[inline(never)]
fn a_misalign(a: &A) -> u32 {
    ((a as *const A as usize) % 16) as u32
}

#[inline(never)]
fn a_copy(dst: &mut A, src: &A) {
    unsafe { core::ptr::copy_nonoverlapping(src as *const A, dst as *mut A, 1) }
}

#[no_mangle]
pub extern "C" fn lay_align_addr(x: u32) -> u32 {
    let a = A(x, 1);
    let b = A(x, 2);
    let c = A(3, x);
    a_misalign(&a) + a_misalign(&b) * 100 + a_misalign(&c) * 10_000 + a.0 + b.1 + c.0
}

#[no_mangle]
pub extern "C" fn lay_align_copy(x: u32) -> u32 {
    let mut d = A(0, 0);
    let s = A(x, x ^ 5);
    let guard = A(77, 88);
    a_copy(&mut d, &s);
    d.0 ^ d.1 ^ guard.0 ^ guard.1
}

#[repr(align(8))]
#[derive(Clone, Copy)]
struct B {
    a: u8,
    b: u8,
}

#[inline(never)]
fn b_view(b: &B) -> u32 {
    ((b as *const B as usize) % 8) as u32 * 1000 + b.a as u32 + b.b as u32
}

#[no_mangle]
pub extern "C" fn lay_align_bytes(x: u32) -> u32 {
    let p = B { a: x as u8, b: 1 };
    let q = B { a: 2, b: x as u8 };
    b_view(&p) + b_view(&q) * 3
}

// --- an over-aligned single-scalar newtype held as its one leaf --------------

#[repr(align(16))]
#[derive(Clone, Copy)]
struct W(u32);

#[inline(never)]
fn w_view(w: &W) -> u32 {
    ((w as *const W as usize) % 16) as u32 * 1000 + unsafe { *(w as *const W as *const u32) }
}

#[inline(never)]
fn apply<F: Fn() -> u32>(f: F) -> u32 {
    f()
}

#[inline(never)]
fn w_copy(dst: &mut W, src: &W) {
    unsafe { core::ptr::copy_nonoverlapping(src, dst, 1) }
}

#[no_mangle]
pub extern "C" fn lay_newtype_ref(x: u32) -> u32 {
    let a = W(x);
    let pad = 1u8;
    let b = W(x ^ 3);
    w_view(&a) + w_view(&b) * 3 + pad as u32
}

#[no_mangle]
pub extern "C" fn lay_newtype_capture(x: u32) -> u32 {
    let a = W(x);
    let b = W(x ^ 3);
    let c = 7u8;
    apply(|| w_view(&a) + c as u32) + w_view(&b) * 3
}

#[no_mangle]
pub extern "C" fn lay_newtype_copy(x: u32) -> u32 {
    let mut d = W(0);
    let s = W(x);
    w_copy(&mut d, &s);
    d.0
}

// --- tagged single-variant enums: a tag word, then the fields ---------------
//
// A tagged enum is laid out as a `repr(C)` struct of its tag and the variant's
// fields: `T8` is `{ tag: u8 @0, a: u32 @4, b: u8 @8 }` (12 bytes), `TC` is
// `{ tag: c_int @0, a: u8 @4, b: u32 @8 }` (12 bytes) and `T16` is
// `{ tag: u16 @0, a: u8 @2, b: u64 @8, c: u16 @16 }` (24 bytes). No export
// reads a padding byte.

#[repr(u8)]
#[derive(Clone, Copy)]
enum T8 {
    A(u32, u8),
}

#[repr(C)]
#[derive(Clone, Copy)]
enum TC {
    A(u8, u32),
}

#[repr(u16)]
#[derive(Clone, Copy)]
enum T16 {
    A(u8, u64, u16),
}

const _: () = assert!(core::mem::size_of::<T8>() == 12 && core::mem::size_of::<TC>() == 12);

trait TagView {
    fn view(&self) -> u32;
}

impl TagView for TC {
    fn view(&self) -> u32 {
        match self {
            TC::A(a, b) => *b ^ (*a as u32) << 3,
        }
    }
}

#[inline(never)]
fn t8_by_value(e: T8) -> u32 {
    match e {
        T8::A(a, b) => a ^ (b as u32) << 3,
    }
}

#[inline(never)]
fn tc_by_value(e: TC) -> u32 {
    match e {
        TC::A(a, b) => b ^ (a as u32) << 3,
    }
}

#[inline(never)]
fn tc_make(x: u32) -> TC {
    TC::A((x >> 2) as u8, x.wrapping_mul(11))
}

#[inline(never)]
fn t8_read(e: &T8) -> u32 {
    match *e {
        T8::A(a, b) => a.wrapping_mul(3) ^ (b as u32),
    }
}

#[inline(never)]
fn t8_raw(e: &T8) -> u32 {
    let p = e as *const T8 as *const u8;
    unsafe { (*p as u32) ^ (*p.add(8) as u32) << 8 ^ *(p as *const u32).add(1) }
}

#[inline(never)]
fn t8_write(e: &mut T8, x: u32) {
    *e = T8::A(x, (x >> 3) as u8);
}

#[inline(never)]
fn t8_mut(e: &mut T8, x: u32) {
    let T8::A(a, b) = e;
    *a = a.wrapping_add(x);
    *b ^= x as u8;
}

#[inline(never)]
fn tc_read(e: &TC) -> u32 {
    match *e {
        TC::A(a, b) => b.rotate_left(5) ^ (a as u32),
    }
}

#[inline(never)]
fn tc_raw(e: &TC) -> u32 {
    let p = e as *const TC as *const u8;
    unsafe { *(p as *const u32) ^ (*p.add(4) as u32) << 9 ^ *(p.add(8) as *const u32) }
}

#[inline(never)]
fn tc_read_ptr(e: *const TC) -> u32 {
    unsafe {
        match *e {
            TC::A(a, b) => b.wrapping_mul(3) ^ a as u32,
        }
    }
}

#[inline(never)]
fn tc_store_ptr(e: *mut TC, x: u32) {
    unsafe { *e = TC::A(x as u8, x.rotate_left(3)) }
}

#[inline(never)]
fn tc_dyn(t: &dyn TagView) -> u32 {
    t.view()
}

#[inline(never)]
fn t16_bump(h: &mut T16, x: u64) {
    let T16::A(a, b, c) = h;
    *a ^= x as u8;
    *b = b.wrapping_add(x);
    *c = c.wrapping_mul(3);
}

#[inline(never)]
fn t16_by_value(h: T16) -> u64 {
    match h {
        T16::A(a, b, c) => b ^ (a as u64) << 50 ^ (c as u64) << 20,
    }
}

#[no_mangle]
pub extern "C" fn lay_tag_by_value(x: u32) -> u32 {
    tc_by_value(TC::A(x as u8, x ^ 5)) ^ t8_by_value(T8::A(x ^ 5, x as u8)).rotate_left(11)
}

#[no_mangle]
pub extern "C" fn lay_tag_returned(x: u32) -> u32 {
    let e = tc_make(x);
    tc_by_value(e) ^ tc_read(&e)
}

#[no_mangle]
pub extern "C" fn lay_tag_ref(x: u32) -> u32 {
    let e = T8::A(x, x as u8);
    let f = TC::A(x as u8, x ^ 0x5555);
    t8_read(&e) ^ t8_raw(&e) ^ tc_read(&f) ^ tc_raw(&f).rotate_left(7)
}

#[no_mangle]
pub extern "C" fn lay_tag_write(x: u32) -> u32 {
    let mut e = T8::A(1, 2);
    t8_write(&mut e, x);
    t8_mut(&mut e, x);
    t8_read(&e) ^ t8_raw(&e) ^ (core::mem::size_of::<T8>() as u32) << 20
}

#[no_mangle]
pub extern "C" fn lay_tag_raw_ptr(x: u32) -> u32 {
    let e = TC::A(x as u8, x ^ 5);
    let mut f = TC::A(1, 2);
    tc_store_ptr(&mut f, x);
    tc_read_ptr(&e) ^ tc_raw(&f)
}

#[no_mangle]
pub extern "C" fn lay_tag_dyn(x: u32) -> u32 {
    let e = TC::A(x as u8, x ^ 5);
    tc_dyn(&e)
}

#[no_mangle]
pub extern "C" fn lay_tag_capture(x: u32) -> u32 {
    let e = TC::A(x as u8, x ^ 1);
    let c = || tc_read(&e) ^ 3;
    c() ^ tc_by_value(e)
}

#[no_mangle]
pub extern "C" fn lay_tag_option(x: u32) -> u32 {
    let o = if x & 1 == 0 { Some(tc_make(x)) } else { None };
    match o {
        Some(f) => tc_read(&f),
        None => 5,
    }
}

#[no_mangle]
pub extern "C" fn lay_tag_store(x: u32) -> u32 {
    let mut e = tc_make(x);
    {
        let r = &mut e;
        *r = TC::A(3, x ^ 0x77);
    }
    let TC::A(a, b) = e;
    b ^ a as u32
}

#[no_mangle]
pub extern "C" fn lay_tag_wide(x: u64) -> u64 {
    let mut h = T16::A(x as u8, x ^ 3, 7);
    t16_bump(&mut h, x);
    t16_by_value(h) ^ (core::mem::size_of::<T16>() as u64) << 58
}

// --- `ptr::swap` of scalar pointees (the `memmove` it lowers to) -------------

static SWAP_X: u32 = 11;
static SWAP_Y: u32 = 22;

#[inline(never)]
fn swap_u128(a: &mut u128, b: &mut u128) {
    unsafe { core::ptr::swap(a, b) }
}

#[inline(never)]
fn swap_ref(a: &mut &'static u32, b: &mut &'static u32) {
    unsafe { core::ptr::swap(a, b) }
}

#[inline(never)]
fn swap_bool(a: &mut bool, b: &mut bool) {
    unsafe { core::ptr::swap(a, b) }
}

#[inline(never)]
fn swap_char(a: &mut char, b: &mut char) {
    unsafe { core::ptr::swap(a, b) }
}

#[no_mangle]
pub extern "C" fn lay_swap_u128(k: u64) -> u64 {
    let mut a = (k as u128) << 64 | 5;
    let mut b = 7u128;
    swap_u128(&mut a, &mut b);
    (a as u64) ^ ((b >> 64) as u64) ^ (b as u64).rotate_left(5) ^ k
}

#[no_mangle]
pub extern "C" fn lay_swap_ref(k: u32) -> u32 {
    let mut a: &u32 = &SWAP_X;
    let mut b: &u32 = &SWAP_Y;
    if k % 2 == 0 {
        swap_ref(&mut a, &mut b);
    }
    *a * 100 + *b
}

#[no_mangle]
pub extern "C" fn lay_swap_bool(k: u32) -> u32 {
    let mut a = k % 2 == 0;
    let mut b = k % 3 == 0;
    swap_bool(&mut a, &mut b);
    a as u32 * 10 + b as u32
}

#[no_mangle]
pub extern "C" fn lay_swap_char(k: u32) -> u32 {
    let mut a = 'a';
    let mut b = char::from_u32(0x41 + k % 26).unwrap_or('z');
    swap_char(&mut a, &mut b);
    a as u32 * 1000 + b as u32
}
