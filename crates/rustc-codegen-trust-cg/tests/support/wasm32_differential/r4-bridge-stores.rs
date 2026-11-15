// wasm32 execution-differential corpus: whole-value stores through `&mut` /
// `*mut`, borrows of zero-sized places, and scalar stores into address-taken
// aggregates.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// * `ws_*`: `*p = value` for a pointee whose by-reference trust-ir image does
//   not place every field at rustc's offset: a reordered struct, one with an
//   array or nested-struct field, a zero-sized field before a sized one, a
//   `#[repr(C)]` neighbour that an over-long write would clobber, an array of
//   reordered tuples, and the `mem::replace` / `mem::take` / `clone_from` /
//   `FnMut`-capture forms that reach the same store, and a scalarized source
//   whose zero-sized fields all come after its sized leaves. Each must write
//   exactly the pointee's bytes at rustc's offsets.
// * `wz_*`: `*p = value` with a zero-sized pointee, reached through a generic
//   function and the default `Clone::clone_from`.
// * `zb_*`: borrows of zero-sized places. Every element of a zero-sized array
//   has the array's address, a zero-sized field sits at `&s +
//   offset_of!(S, f)`, and one zero-sized local keeps one address.
// * `fb_*`: a borrow of the field at offset 0 joined with a borrow of another
//   field (an `Index` impl, a loop-carried reference).
// * `fc_*`: a cast, unary op or float operation stored into a field of an
//   address-taken struct.
// * `zd_*`: a promoted `&ZST` / `&fn_item` coerced to `&dyn Trait`, including
//   an over-aligned ZST whose data pointer must be aligned to 64.
// * `ct_*`: a non-capturing closure with a tuple-pattern parameter passed by
//   value to `Option::map_or`.
//
// wasm32-differential-flags: -Copt-level=1
// wasm32-differential-flags: -Copt-level=2

#![no_std]
#![allow(dead_code)]

use core::hint::black_box;
use core::marker::PhantomData;
use core::mem::offset_of;
use core::num::NonZeroU64;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

// ---- ws_*: whole-value stores through a pointer --------------------------

// rustc places `c4` at 0 and `c0` at 8.
#[derive(Clone, Copy)]
pub struct Reordered {
    c0: u32,
    c4: u64,
}

#[inline(never)]
fn reordered_set(t: &mut Reordered, k: u64) {
    *t = Reordered {
        c0: k as u32,
        c4: k ^ 0x55,
    };
}

#[inline(never)]
fn reordered_set_raw(t: *mut Reordered, k: u64) {
    unsafe {
        *t = Reordered {
            c0: (k >> 7) as u32,
            c4: k.rotate_left(9),
        }
    };
}

#[no_mangle]
pub extern "C" fn ws_reordered(a: i64) -> u64 {
    let mut t = Reordered { c0: 1, c4: 7 };
    reordered_set(&mut t, a as u64);
    let first = (t.c0 as u64) << 32 ^ t.c4;
    reordered_set_raw(&mut t, first);
    first ^ (t.c0 as u64).rotate_left(17) ^ t.c4
}

// `{u8, u64, u16}` is 16 bytes in rustc's order; its declaration-order image
// is 24, so an image-typed write would run past the object.
#[derive(Clone, Copy)]
pub struct Update3 {
    a: u8,
    b: u64,
    c: u16,
}

#[inline(never)]
fn update3(t: &mut Update3, k: u8) {
    *t = Update3 { a: k, ..*t };
}

#[no_mangle]
pub extern "C" fn ws_struct_update(a: i64) -> u64 {
    let mut t = [
        Update3 {
            a: 1,
            b: a as u64,
            c: 0x7777,
        },
        Update3 { a: 2, b: 3, c: 4 },
    ];
    update3(&mut t[0], (a >> 3) as u8);
    t[0].a as u64 ^ t[0].b.rotate_left(8) ^ (t[0].c as u64) << 48 ^ t[1].b ^ t[1].c as u64
}

#[derive(Clone, Copy)]
pub struct Niche {
    a: u64,
    n: NonZeroU64,
    b: u64,
}

#[inline(never)]
fn niche_set(t: &mut Niche, k: u64) {
    *t = Niche {
        a: k,
        n: NonZeroU64::new(k | 1).unwrap(),
        b: !k,
    };
}

#[no_mangle]
pub extern "C" fn ws_niche(a: i64) -> u64 {
    let mut t = Niche {
        a: 7,
        n: NonZeroU64::new(9).unwrap(),
        b: 11,
    };
    niche_set(&mut t, a as u64);
    t.a ^ t.n.get().rotate_left(20) ^ t.b.rotate_left(40)
}

// An array field: the pointee's image is its slot's uniform lanes.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct LaneC {
    a: u32,
    b: [u8; 4],
    d: u64,
}

#[inline(never)]
fn lane_set(t: &mut LaneC, k: u64) {
    let o = *t;
    *t = LaneC {
        a: o.a ^ 5,
        b: [1, 2, o.b[0], 4],
        d: k,
    };
}

#[no_mangle]
pub extern "C" fn ws_lane_struct(a: i64) -> u64 {
    let mut t = LaneC {
        a: 3,
        b: [9; 4],
        d: 0,
    };
    lane_set(&mut t, a as u64);
    t.d ^ t.a as u64 ^ (u32::from_le_bytes(t.b) as u64) << 20
}

#[derive(Clone, Copy)]
pub struct ArrOnly {
    a: [u32; 3],
}

#[derive(Clone, Copy)]
pub struct Mixed {
    a: [u8; 2],
    b: u16,
    c: u32,
}

#[inline(never)]
fn copy_arr_only(d: &mut ArrOnly, s: &ArrOnly) {
    *d = *s;
}

#[inline(never)]
fn clear_arr_only(d: &mut ArrOnly, k: u32) {
    *d = ArrOnly { a: [k, 0, k ^ 3] };
}

#[inline(never)]
fn copy_mixed(d: &mut Mixed, s: &Mixed) {
    *d = *s;
}

#[no_mangle]
pub extern "C" fn ws_array_field(x: u32, i: u32) -> u32 {
    let mut d = ArrOnly { a: [1, 2, 3] };
    let s = ArrOnly {
        a: [x, x ^ 0x55, x.rotate_left(7)],
    };
    copy_arr_only(&mut d, &s);
    let first = d.a[(i % 3) as usize];
    clear_arr_only(&mut d, x >> 3);
    let mut m = [
        Mixed {
            a: [1, 2],
            b: 3,
            c: 4,
        },
        Mixed {
            a: [5, 6],
            b: 7,
            c: 8,
        },
    ];
    let ms = Mixed {
        a: [x as u8, 9],
        b: x as u16 ^ 0x55,
        c: x ^ 7,
    };
    copy_mixed(&mut m[0], &ms);
    first
        ^ d.a[(i % 3) as usize].rotate_left(3)
        ^ (m[0].a[0] as u32)
        ^ ((m[0].a[1] as u32) << 8)
        ^ ((m[0].b as u32) << 16)
        ^ m[0].c.rotate_left(5)
        ^ m[1].c
        ^ m[1].b as u32
}

// A zero-sized field before the array: `z` sits at rustc offset 8 and lane 1
// of the image at offset 4.
#[derive(Clone, Copy)]
pub struct ZstArr {
    a: [u32; 2],
    z: PhantomData<u8>,
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct ZstArrC {
    a: [u32; 2],
    z: PhantomData<u8>,
}

#[repr(C)]
pub struct Neighbour {
    big: ZstArrC,
    after: u32,
}

pub struct UnitFirst((), [u32; 2]);

#[inline(never)]
fn copy_zst_arr(d: &mut ZstArr, s: &ZstArr) {
    *d = *s;
}

#[inline(never)]
fn store_zst_arr(d: &mut ZstArr, x: u32) {
    *d = ZstArr {
        a: [x, x ^ 0x55],
        z: PhantomData,
    };
}

#[inline(never)]
fn copy_zst_arr_c(d: &mut ZstArrC, s: &ZstArrC) {
    *d = *s;
}

#[inline(never)]
fn make_unit_first(x: u32) -> UnitFirst {
    UnitFirst((), [x, x.wrapping_mul(7)])
}

#[inline(never)]
fn set_unit_first(a: &mut UnitFirst, x: u32) {
    *a = make_unit_first(x);
}

#[no_mangle]
pub extern "C" fn ws_zst_field(x: u32, i: u32) -> u32 {
    let mut d = ZstArr {
        a: [1, 2],
        z: PhantomData,
    };
    let s = ZstArr {
        a: [x, !x],
        z: PhantomData,
    };
    copy_zst_arr(&mut d, &s);
    let first = d.a[0] ^ d.a[1].rotate_left(11);
    store_zst_arr(&mut d, x >> 2);
    let mut o = Neighbour {
        big: ZstArrC {
            a: [1, 2],
            z: PhantomData,
        },
        after: 0x1234,
    };
    let sc = ZstArrC {
        a: [x, x ^ 0x55],
        z: PhantomData,
    };
    copy_zst_arr_c(&mut o.big, &sc);
    let mut u = UnitFirst((), [9, 9]);
    set_unit_first(&mut u, x);
    first ^ d.a[(i % 2) as usize] ^ o.after ^ o.big.a[1].rotate_left(9) ^ u.1[(i % 2) as usize]
}

// A zero-sized field AFTER every sized leaf, written whole from a scalarized
// temporary: the flat binding keys and the leaf positions still agree. (A ZST
// before a sized leaf, where they do not, is `r7-bridge-zst-leaf-keys.rs`.)
#[derive(Clone, Copy)]
pub struct TailZst {
    a: u8,
    b: u64,
    c: u16,
    z: PhantomData<u32>,
}

#[derive(Clone, Copy)]
pub struct TailInner {
    x: u16,
    y: u32,
    z: (),
}

#[derive(Clone, Copy)]
pub struct TailOuter {
    a: u8,
    i: TailInner,
}

#[inline(never)]
fn set_tail_zst(d: &mut TailZst, k: u64) {
    let mut t = TailZst {
        a: k as u8,
        b: k.rotate_left(29),
        c: (k >> 16) as u16,
        z: PhantomData,
    };
    t.b ^= 0x55;
    *d = t;
}

#[inline(never)]
fn set_tail_outer(d: &mut TailOuter, k: u64) {
    let mut t = TailOuter {
        a: k as u8,
        i: TailInner {
            x: (k >> 8) as u16,
            y: (k >> 24) as u32,
            z: (),
        },
    };
    t.i.y ^= 7;
    *d = t;
}

#[no_mangle]
pub extern "C" fn ws_tail_zst(a: i64) -> u64 {
    let k = a as u64;
    let mut g = [TailZst {
        a: 1,
        b: 2,
        c: 3,
        z: PhantomData,
    }; 2];
    set_tail_zst(&mut g[0], k);
    let mut o = [TailOuter {
        a: 4,
        i: TailInner { x: 5, y: 6, z: () },
    }; 2];
    set_tail_outer(&mut o[1], k.rotate_left(7));
    g[0].a as u64
        ^ g[0].b.rotate_left(9)
        ^ (g[0].c as u64) << 40
        ^ g[1].b
        ^ g[1].c as u64
        ^ (o[1].a as u64) << 8
        ^ (o[1].i.x as u64) << 16
        ^ (o[1].i.y as u64) << 32
        ^ o[0].i.y as u64
}

// A nested struct: the scalarized source's leaves are not the image's lanes.
#[derive(Clone, Copy)]
pub struct Inner {
    x: u32,
    y: u16,
}

#[derive(Clone, Copy)]
pub struct Outer {
    a: u8,
    i: Inner,
}

#[derive(Clone, Copy)]
pub struct Inner2 {
    x: u16,
    y: u64,
}

#[derive(Clone, Copy)]
pub struct Outer2 {
    a: u8,
    inner: Inner2,
    b: u32,
}

#[inline(never)]
fn copy_outer(d: &mut Outer, s: &Outer) {
    *d = *s;
}

#[inline(never)]
fn set_outer2(t: &mut Outer2, k: u64) {
    *t = Outer2 {
        a: k as u8,
        inner: Inner2 {
            x: (k >> 8) as u16,
            y: k.rotate_left(13),
        },
        b: (k >> 32) as u32,
    };
}

#[no_mangle]
pub extern "C" fn ws_nested(a: i64) -> u64 {
    let x = a as u32;
    let mut d = Outer {
        a: 1,
        i: Inner { x: 2, y: 3 },
    };
    let s = Outer {
        a: x as u8 ^ 3,
        i: Inner {
            x: x ^ 5,
            y: x as u16 ^ 9,
        },
    };
    copy_outer(&mut d, &s);
    let mut t = Outer2 {
        a: 1,
        inner: Inner2 { x: 2, y: 3 },
        b: 4,
    };
    set_outer2(&mut t, a as u64);
    (d.a as u64)
        ^ (d.i.x.rotate_left(5) as u64)
        ^ ((d.i.y as u64) << 40)
        ^ t.a as u64
        ^ (t.inner.x as u64) << 8
        ^ t.inner.y.rotate_left(3)
        ^ (t.b as u64) << 24
}

#[inline(never)]
fn make_pairs(x: u32) -> [(u8, u32); 2] {
    [
        (x as u8, x ^ 0x1234_5678),
        ((x >> 8) as u8, x.wrapping_mul(3)),
    ]
}

#[inline(never)]
fn set_pairs(a: &mut [(u8, u32); 2], x: u32) {
    *a = make_pairs(x);
}

#[inline(never)]
fn make_tuple_arr(x: u32) -> (u16, [u8; 2], u32) {
    (x as u16, [(x >> 3) as u8, 7], x.rotate_left(13))
}

#[inline(never)]
fn set_tuple_arr(a: &mut (u16, [u8; 2], u32), x: u32) {
    *a = make_tuple_arr(x);
}

#[no_mangle]
pub extern "C" fn ws_array_of_tuples(x: u32) -> u32 {
    let mut a = [(1u8, 1u32); 2];
    set_pairs(&mut a, x);
    let mut t = (1u16, [2u8, 3], 4u32);
    set_tuple_arr(&mut t, x);
    (a[0].0 as u32)
        ^ a[0].1
        ^ (a[1].0 as u32) << 24
        ^ a[1].1.rotate_left(5)
        ^ t.0 as u32
        ^ (t.1[0] as u32) << 16
        ^ (t.1[1] as u32) << 8
        ^ t.2
}

#[derive(Clone, Copy, Default)]
pub struct Big {
    a: [u32; 3],
    t: u32,
}

#[derive(Clone, Copy)]
pub struct Words(pub [u16; 7]);

#[inline(never)]
fn replace_big(d: &mut Big, x: u32) -> Big {
    core::mem::replace(
        d,
        Big {
            a: [x, x + 1, x + 2],
            t: x ^ 7,
        },
    )
}

#[inline(never)]
fn take_big(d: &mut Big) -> Big {
    core::mem::take(d)
}

#[inline(never)]
fn clone_words(a: &mut Words, b: &Words) {
    a.clone_from(b);
}

#[no_mangle]
pub extern "C" fn ws_mem_fns(x: u32, i: u32) -> u32 {
    let x = x & 0xffff;
    let mut b = Big { a: [x; 3], t: 5 };
    let o = replace_big(&mut b, x);
    let t = take_big(&mut b);
    let mut w = Words([1; 7]);
    clone_words(&mut w, &Words([x as u16, 2, 3, 4, 5, 6, (x >> 4) as u16]));
    o.a[1] ^ b.a[2] ^ b.t ^ t.a[0].wrapping_mul(3) ^ t.t ^ w.0[(i % 7) as usize] as u32
}

#[derive(Clone, Copy)]
pub struct State {
    c0: u64,
    c1: u32,
    c2: u8,
    c3: [u16; 3],
    c4: (u16, i64),
}

#[inline(never)]
fn call_n<F: FnMut(u32) -> u64>(n: u32, mut f: F) -> u64 {
    let mut h = 0u64;
    let mut i = 0;
    while i < n {
        h = h.rotate_left(5) ^ f(i);
        i += 1;
    }
    h
}

#[no_mangle]
pub extern "C" fn ws_fnmut_state(a: i64, n: u32) -> u64 {
    let a = a as u64;
    let mut t = State {
        c0: a,
        c1: a as u32,
        c2: a as u8,
        c3: [1, 2, 3],
        c4: (0, 0),
    };
    let h = call_n(n % 12, |i| {
        let o = t;
        t = State {
            c0: o.c0.rotate_left(3) ^ i as u64,
            c1: o.c1.wrapping_mul(0x0100_0193) ^ i,
            c2: o.c2.wrapping_add(i as u8),
            c3: [o.c3[1], o.c3[2], o.c3[0].wrapping_add(o.c2 as u16)],
            c4: (o.c4.0.wrapping_add(1), o.c4.1 ^ o.c0 as i64),
        };
        t.c0 ^ t.c1 as u64
    });
    h ^ t.c0
        ^ t.c1 as u64
        ^ t.c2 as u64
        ^ (t.c3[0] as u64) << 8
        ^ (t.c3[2] as u64) << 24
        ^ t.c4.0 as u64
        ^ t.c4.1 as u64
}

// ---- wz_*: zero-sized pointees --------------------------------------------

#[derive(Clone, Copy)]
pub struct Unit;

#[inline(never)]
fn put<T>(a: &mut T, b: T) {
    *a = b;
}

#[inline(never)]
fn clone_unit(a: &mut Unit, b: &Unit) {
    a.clone_from(b);
}

#[no_mangle]
pub extern "C" fn wz_store(x: u32) -> u32 {
    let mut u = ();
    put(&mut u, ());
    let mut z = Unit;
    clone_unit(&mut z, &Unit);
    put(&mut z, Unit);
    let mut v = 0u32;
    put(&mut v, x ^ 1);
    v
}

// ---- zb_*: borrows of zero-sized places -----------------------------------

pub struct WithUnit {
    a: u32,
    z: (),
    b: u64,
}

pub struct TwoUnits {
    a: u8,
    z1: (),
    b: u32,
    z2: (),
}

pub struct Marked {
    a: u64,
    p: PhantomData<u8>,
    b: u16,
}

#[inline(never)]
fn same_unit(a: &(), b: &()) -> bool {
    core::ptr::eq(a, b)
}

#[inline(never)]
fn unit_distance(p: &(), q: &()) -> usize {
    (q as *const () as usize).wrapping_sub(p as *const () as usize)
}

#[inline(never)]
fn address_of<T>(r: &T) -> usize {
    r as *const T as usize
}

#[inline(never)]
fn marker_base(m: &PhantomData<u8>) -> usize {
    (m as *const PhantomData<u8> as usize).wrapping_sub(offset_of!(Marked, p))
}

#[no_mangle]
pub extern "C" fn zb_array_elements(i: u32) -> u32 {
    let us = [(); 4];
    let units = [Unit, Unit, Unit, Unit];
    let k = (i % 4) as usize;
    let a = core::ptr::eq(&us[k], &us[0]) as u32;
    let b = core::ptr::eq(&units[k], &units[(k + 1) % 4]) as u32;
    let c = core::ptr::eq(&units[1], &units[1]) as u32;
    a | b << 1 | c << 2
}

#[no_mangle]
pub extern "C" fn zb_fields(x: u32) -> u32 {
    let s = WithUnit {
        a: x,
        z: (),
        b: x as u64,
    };
    let off = address_of(&s.z).wrapping_sub(address_of(&s));
    let t = ((), ());
    let two = TwoUnits {
        a: x as u8,
        z1: (),
        b: x,
        z2: (),
    };
    let d = unit_distance(&two.z1, &two.z2);
    let m = Marked {
        a: x as u64,
        p: PhantomData,
        b: x as u16,
    };
    let base = marker_base(&m.p);
    (off == offset_of!(WithUnit, z)) as u32
        | (same_unit(&t.0, &t.1) as u32) << 1
        | ((d == offset_of!(TwoUnits, z2).wrapping_sub(offset_of!(TwoUnits, z1))) as u32) << 2
        | ((base == address_of(&m)) as u32) << 3
        | ((s.a ^ s.b as u32 ^ two.a as u32 ^ two.b ^ m.a as u32 ^ m.b as u32) & 0)
}

#[no_mangle]
pub extern "C" fn zb_same_local(x: u32) -> u32 {
    let a = ();
    let first = &a as *const ();
    let again = black_box(&a) as *const ();
    core::ptr::eq(first, again) as u32 | (x & 0)
}

// ---- fb_*: offset-0 field borrows at a join ---------------------------------

pub struct V3 {
    x: i32,
    y: i32,
    z: i32,
}

impl core::ops::Index<u32> for V3 {
    type Output = i32;

    fn index(&self, i: u32) -> &i32 {
        match i {
            0 => &self.x,
            1 => &self.y,
            _ => &self.z,
        }
    }
}

pub struct WithArr {
    x: i32,
    y: i32,
    w: [u16; 5],
}

#[inline(never)]
fn index_v3(v: &V3, i: u32) -> i32 {
    v[i]
}

#[inline(never)]
fn pick_field(p: &mut WithArr, c: bool) -> &mut i32 {
    if c { &mut p.x } else { &mut p.y }
}

#[inline(never)]
fn walk(p: &(i32, i32, i32), n: u32) -> &i32 {
    let mut r = &p.0;
    let mut i = 0;
    while i < (n & 7) {
        if i & 1 == 0 {
            r = &p.2;
        } else {
            r = &p.0;
        }
        i += 1;
    }
    r
}

#[no_mangle]
pub extern "C" fn fb_join(a: i32, i: u32) -> i32 {
    let v = V3 {
        x: a,
        y: a ^ 5,
        z: a.wrapping_mul(3),
    };
    let mut p = WithArr {
        x: a,
        y: a + 1,
        w: [7; 5],
    };
    *pick_field(&mut p, i & 1 == 0) += 9;
    let t = (a, i as i32, 5 + a);
    index_v3(&v, i % 4) ^ p.x ^ p.y.rotate_left(3) ^ p.w[2] as i32 ^ *walk(&t, i)
}

// ---- fc_*: scalar stores into address-taken structs ----------------------

#[derive(Clone, Copy, Default)]
pub struct Fields {
    a: u64,
    b: u16,
    f: f64,
    l: bool,
}

#[inline(never)]
fn look(k: &Fields) -> u64 {
    k.a ^ (k.b as u64) << 48 ^ k.f.to_bits() ^ k.l as u64
}

#[no_mangle]
pub extern "C" fn fc_cast_into_field(x: u32, y: u32) -> u64 {
    let mut k = Fields::default();
    k.a = x as u64;
    k.b = !(y as u16);
    k.f = y as f64 * 0.5;
    k.l = x < y;
    let first = look(&k);
    k.f = -k.f;
    k.a = (x as i32) as i64 as u64;
    first ^ look(&k).rotate_left(7)
}

// ---- zd_*: promoted zero-sized trait objects -------------------------------

trait Scale {
    fn scale(&self, x: u32) -> u32;
}

struct Triple;

impl Scale for Triple {
    fn scale(&self, x: u32) -> u32 {
        x.wrapping_mul(3)
    }
}

#[inline(never)]
fn call_scale(d: &dyn Scale, x: u32) -> u32 {
    d.scale(x)
}

fn add_seven(x: u32) -> u32 {
    x.wrapping_add(7)
}

#[inline(never)]
fn call_fn(f: &dyn Fn(u32) -> u32, x: u32) -> u32 {
    f(x)
}

#[no_mangle]
pub extern "C" fn zd_promoted(x: u32) -> u32 {
    call_scale(&Triple, x) ^ call_fn(&add_seven, x).rotate_left(3)
}

// The promoted `&ZST` data pointer is the zero-length allocation's alignment,
// so an over-aligned ZST gets an address aligned to 64.
#[repr(align(64))]
struct Wide;

impl Scale for Wide {
    fn scale(&self, x: u32) -> u32 {
        x ^ 0x5a5a
    }
}

#[inline(never)]
fn data_addr(d: &dyn Scale) -> usize {
    d as *const dyn Scale as *const () as usize
}

#[no_mangle]
pub extern "C" fn zd_aligned(x: u32) -> u32 {
    let d: &dyn Scale = &Wide;
    ((data_addr(d) % 64) as u32) ^ d.scale(x) ^ ((data_addr(&Triple) == 0) as u32) << 20
}

// ---- ct_*: a tuple-pattern closure parameter ------------------------------

#[inline(never)]
fn maybe_pair(a: u32) -> Option<(u64, u8)> {
    if a & 1 == 0 {
        Some((a as u64 * 3, a as u8))
    } else {
        None
    }
}

#[no_mangle]
pub extern "C" fn ct_map_or(a: u32) -> u64 {
    maybe_pair(a).map_or(99, |(p, q)| p ^ q as u64)
}
