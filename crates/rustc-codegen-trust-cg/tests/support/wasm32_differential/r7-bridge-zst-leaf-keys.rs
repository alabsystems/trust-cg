// wasm32 execution-differential corpus: reading a scalarized aggregate's
// leaves under the keys its binder gave them when zero-sized fields come
// before sized ones.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// A scalarized aggregate keeps each sized leaf in a projected binding. An
// aggregate with a nested aggregate field keys its leaves by their flat,
// zero-sized-skipping position at every level; any other aggregate keys each
// field by its MIR field index, which counts zero-sized fields. Every reader
// below must find each leaf under that key, never under its leaf position:
//
// * `fs_*`: a field store `h.f = t` from a scalarized nested source
//   (`RawVec`-shaped `Unique { pointer, _marker }`, `Cap`, a ZST allocator and
//   an outer marker; ZSTs first, in the middle, last and first in a nested
//   field; a tuple with an interior unit; a struct with a leading marker).
// * `ws_*`: a whole-value store `*d = t` through `&mut`.
// * `as_*`: an array element store `g[i] = S { .. }` with a moved nested
//   operand.
// * `lit_*`: a struct literal with a moved nested operand, returned by value.
// * `arr_*`: an array literal of scalarized aggregates with leading ZSTs.
// * `mem_*` / `deref_*`: a memory-backed or through-pointer aggregate copied
//   whole into a scalarized local, then read by field.
// * `borrow_*`: `&(*p).k` of a scalarized aggregate after a multi-leaf field.
// * `al_*`: the same reads and stores over field types declared through an
//   associated-type projection (`<u8 as Tr>::O`, `T::O`), which the scheme
//   decision must see normalized, as the binder does.
//
// wasm32-differential-flags: -Copt-level=1
// wasm32-differential-flags: -Copt-level=2

#![no_std]
#![allow(dead_code)]

use core::hint::black_box;
use core::marker::PhantomData;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

// ---- `RawVec`-shaped nesting ------------------------------------------------

#[derive(Clone, Copy)]
pub struct Uq {
    p: u64,
    m: PhantomData<u8>,
}
#[derive(Clone, Copy)]
pub struct Cap(u32);
#[derive(Clone, Copy)]
pub struct Gl;
#[derive(Clone, Copy)]
pub struct RvInner {
    ptr: Uq,
    cap: Cap,
    alloc: Gl,
}
#[derive(Clone, Copy)]
pub struct Rv {
    inner: RvInner,
    m: PhantomData<u16>,
}
#[derive(Clone, Copy)]
pub struct VecLike {
    buf: Rv,
    len: u16,
}

// ---- ZSTs first, middle, last and nested-first --------------------------------

// MIR-field keyed: `p` at key 1, `q` at key 2.
#[derive(Clone, Copy)]
pub struct N1 {
    zf: (),
    p: u32,
    q: u32,
}
#[derive(Clone, Copy)]
pub struct Zs;
// Flat keyed: a, n.p, n.q, b, t.1, t.2, c at 0..7.
#[derive(Clone, Copy)]
pub struct Deep {
    z0: (),
    a: u8,
    n: N1,
    z1: PhantomData<u16>,
    b: u32,
    t: (Zs, u32, u32, ()),
    c: u16,
    zt: (),
}
#[derive(Clone, Copy)]
pub struct HoldDeep {
    h: u8,
    d: Deep,
    k: u32,
}

// MIR-field keyed with an interior marker: a, b, c at keys 0, 1, 3.
#[derive(Clone, Copy)]
pub struct Z3 {
    a: u32,
    b: u32,
    p: PhantomData<u32>,
    c: u32,
}
#[derive(Clone, Copy)]
pub struct Hold {
    h: u16,
    z: Z3,
    n: N1,
    t: u8,
}
// A tuple field with an interior unit: the unit has a binding of its own.
#[derive(Clone, Copy)]
pub struct HoldT {
    h: u16,
    z: (u32, (), u32),
    t: u8,
}

#[inline(never)]
fn look_vec(v: &VecLike) -> u64 {
    v.buf.inner.ptr.p ^ (v.buf.inner.cap.0 as u64).rotate_left(17) ^ (v.len as u64).rotate_left(41)
}

#[inline(never)]
fn look_deep(d: &Deep) -> u64 {
    (d.a as u64)
        ^ (d.n.p as u64).rotate_left(8)
        ^ (d.n.q as u64).rotate_left(13)
        ^ (d.b as u64).rotate_left(24)
        ^ (d.t.1 as u64).rotate_left(36)
        ^ (d.t.2 as u64).rotate_left(45)
        ^ (d.c as u64).rotate_left(52)
}

#[inline(never)]
fn look_hold_deep(h: &HoldDeep) -> u64 {
    (h.h as u64) ^ look_deep(&h.d).rotate_left(3) ^ (h.k as u64).rotate_left(29)
}

#[inline(never)]
fn look_hold(h: &Hold) -> u64 {
    (h.h as u64)
        ^ (h.z.a as u64).rotate_left(5)
        ^ (h.z.b as u64).rotate_left(17)
        ^ (h.z.c as u64).rotate_left(29)
        ^ (h.n.p as u64).rotate_left(37)
        ^ (h.n.q as u64).rotate_left(43)
        ^ (h.t as u64).rotate_left(57)
}

#[inline(never)]
fn look_hold_t(h: &HoldT) -> u64 {
    (h.h as u64)
        ^ (h.z.0 as u64).rotate_left(8)
        ^ (h.z.2 as u64).rotate_left(32)
        ^ (h.t as u64).rotate_left(56)
}

#[inline(never)]
fn mk_rv(x: u64) -> Rv {
    let mut r = Rv {
        inner: RvInner {
            ptr: Uq {
                p: x,
                m: PhantomData,
            },
            cap: Cap((x >> 7) as u32),
            alloc: Gl,
        },
        m: PhantomData,
    };
    r.inner.cap.0 ^= 0x5a5a;
    r
}

#[inline(never)]
fn mk_deep(x: u64) -> Deep {
    let mut d = Deep {
        z0: (),
        a: x as u8,
        n: N1 {
            zf: (),
            p: (x >> 8) as u32,
            q: x.rotate_left(5) as u32,
        },
        z1: PhantomData,
        b: (x >> 3) as u32,
        t: (Zs, (x >> 20) as u32, !x as u32, ()),
        c: (x >> 40) as u16,
        zt: (),
    };
    d.b ^= 0x77;
    d
}

// ---- fs_*: field store `h.f = t` -------------------------------------------

#[no_mangle]
pub extern "C" fn fs_vec(x: u64) -> u64 {
    let mut v = VecLike {
        buf: mk_rv(1),
        len: 3,
    };
    let r0 = look_vec(&v);
    let mut t = Rv {
        inner: RvInner {
            ptr: Uq {
                p: x ^ 0x1111,
                m: PhantomData,
            },
            cap: Cap((x >> 9) as u32),
            alloc: Gl,
        },
        m: PhantomData,
    };
    t.inner.cap.0 = t.inner.cap.0.wrapping_add(black_box(5));
    v.buf = t;
    r0 ^ look_vec(&v)
}

#[no_mangle]
pub extern "C" fn fs_deep(x: u64) -> u64 {
    let mut h = HoldDeep {
        h: 1,
        d: mk_deep(2),
        k: 3,
    };
    let r0 = look_hold_deep(&h);
    let mut t = Deep {
        z0: (),
        a: (x >> 1) as u8,
        n: N1 {
            zf: (),
            p: (x >> 11) as u32,
            q: x.rotate_left(9) as u32,
        },
        z1: PhantomData,
        b: (x >> 5) as u32,
        t: (Zs, (x >> 17) as u32, (x ^ 0xabc) as u32, ()),
        c: (x >> 33) as u16,
        zt: (),
    };
    t.n.q ^= black_box(0x99);
    h.d = t;
    r0 ^ look_hold_deep(&h)
}

#[no_mangle]
pub extern "C" fn fs_flat(x: u64) -> u64 {
    let mut h = Hold {
        h: 1,
        z: Z3 {
            a: 2,
            b: 3,
            p: PhantomData,
            c: 4,
        },
        n: N1 { zf: (), p: 5, q: 6 },
        t: 7,
    };
    let r0 = look_hold(&h);
    let mut z = Z3 {
        a: x as u32,
        b: (x >> 32) as u32,
        p: PhantomData,
        c: (x >> 16) as u32,
    };
    z.c ^= black_box(0x55);
    h.z = z;
    let mut n = N1 {
        zf: (),
        p: !(x as u32),
        q: (x >> 24) as u32,
    };
    n.p ^= black_box(0x33);
    h.n = n;
    r0 ^ look_hold(&h)
}

#[no_mangle]
pub extern "C" fn fs_tup(x: u64) -> u64 {
    let mut h = HoldT {
        h: 1,
        z: (2, (), 3),
        t: 4,
    };
    let r = look_hold_t(&h);
    let mut z = (x as u32, (), (x >> 32) as u32);
    z.0 ^= black_box(0x11);
    h.z = z;
    r ^ look_hold_t(&h)
}

// ---- ws_*: whole-value store `*d = t` ----------------------------------------

#[inline(never)]
fn set_rv(d: &mut Rv, x: u64) {
    let mut t = Rv {
        inner: RvInner {
            ptr: Uq {
                p: x,
                m: PhantomData,
            },
            cap: Cap(!(x as u32)),
            alloc: Gl,
        },
        m: PhantomData,
    };
    t.inner.ptr.p ^= black_box(3);
    *d = t;
}

#[inline(never)]
fn set_deep(d: &mut Deep, x: u64) {
    let mut t = mk_deep(x);
    t.c ^= black_box(0x1234);
    *d = t;
}

#[inline(never)]
fn set_n1(d: &mut N1, x: u64) {
    let mut t = N1 {
        zf: (),
        p: x as u32,
        q: (x >> 32) as u32,
    };
    t.q ^= black_box(9);
    *d = t;
}

#[no_mangle]
pub extern "C" fn ws_rv(x: u64) -> u64 {
    let mut v = VecLike {
        buf: mk_rv(5),
        len: 9,
    };
    set_rv(&mut v.buf, x);
    look_vec(&v)
}

#[no_mangle]
pub extern "C" fn ws_deep(x: u64) -> u64 {
    let mut h = HoldDeep {
        h: 7,
        d: mk_deep(4),
        k: 8,
    };
    set_deep(&mut h.d, x);
    look_hold_deep(&h)
}

#[no_mangle]
pub extern "C" fn ws_n1(x: u64) -> u64 {
    let mut h = Hold {
        h: 1,
        z: Z3 {
            a: 2,
            b: 3,
            p: PhantomData,
            c: 4,
        },
        n: N1 { zf: (), p: 5, q: 6 },
        t: 7,
    };
    set_n1(&mut h.n, x);
    look_hold(&h)
}

// ---- as_*: array element store `g[i] = S { .. }` -----------------------------

#[no_mangle]
pub extern "C" fn as_vec(x: u64, i: u32) -> u64 {
    let mut g = [VecLike {
        buf: mk_rv(2),
        len: 1,
    }; 3];
    let i = (i % 3) as usize;
    let t = mk_rv(x);
    g[i] = VecLike {
        buf: t,
        len: (x >> 3) as u16,
    };
    look_vec(&g[0]) ^ look_vec(&g[1]).rotate_left(1) ^ look_vec(&g[2]).rotate_left(2)
}

#[no_mangle]
pub extern "C" fn as_deep(x: u64, i: u32) -> u64 {
    let mut g = [HoldDeep {
        h: 1,
        d: mk_deep(3),
        k: 2,
    }; 2];
    let i = (i % 2) as usize;
    let t = mk_deep(x);
    g[i] = HoldDeep {
        h: x as u8,
        d: t,
        k: (x >> 30) as u32,
    };
    look_hold_deep(&g[0]) ^ look_hold_deep(&g[1]).rotate_left(7)
}

#[no_mangle]
pub extern "C" fn as_flat(x: u64, i: u32) -> u64 {
    let base = Hold {
        h: 1,
        z: Z3 {
            a: 2,
            b: 3,
            p: PhantomData,
            c: 4,
        },
        n: N1 { zf: (), p: 5, q: 6 },
        t: 7,
    };
    let mut g = [base; 2];
    let i = (i % 2) as usize;
    let mut z = Z3 {
        a: (x >> 3) as u32,
        b: x as u32,
        p: PhantomData,
        c: !(x as u32),
    };
    z.b ^= black_box(0x21);
    let mut n = N1 {
        zf: (),
        p: (x >> 40) as u32,
        q: (x >> 8) as u32,
    };
    n.q ^= black_box(0x42);
    g[i] = Hold {
        h: (x >> 50) as u16,
        z,
        n,
        t: (x >> 2) as u8,
    };
    look_hold(&g[0]) ^ look_hold(&g[1]).rotate_left(9)
}

// ---- lit_*: struct literal with a moved nested operand -------------------------

#[inline(never)]
fn lit_hold_deep(x: u64) -> HoldDeep {
    let mut t = mk_deep(x);
    t.a ^= black_box(0x3c);
    HoldDeep {
        h: (x >> 2) as u8,
        d: t,
        k: (x >> 12) as u32,
    }
}

#[inline(never)]
fn lit_vec(x: u64) -> VecLike {
    let mut t = mk_rv(x);
    t.inner.ptr.p = t.inner.ptr.p.wrapping_mul(black_box(3));
    VecLike {
        buf: t,
        len: (x >> 50) as u16,
    }
}

#[inline(never)]
fn lit_hold(x: u64) -> Hold {
    let mut z = Z3 {
        a: x as u32,
        b: x.rotate_left(3) as u32,
        p: PhantomData,
        c: (x >> 8) as u32,
    };
    z.c ^= black_box(0x55);
    let mut n = N1 {
        zf: (),
        p: (x >> 13) as u32,
        q: (x >> 29) as u32,
    };
    n.p ^= black_box(0x66);
    Hold {
        h: (x >> 4) as u16,
        z,
        n,
        t: (x >> 20) as u8,
    }
}

#[inline(never)]
fn lit_hold_t(x: u64) -> HoldT {
    let mut z = (x as u32, (), (x >> 32) as u32);
    z.2 ^= black_box(0x77);
    HoldT {
        h: (x >> 4) as u16,
        z,
        t: (x >> 20) as u8,
    }
}

#[no_mangle]
pub extern "C" fn lit_all(x: u64) -> u64 {
    let hd = lit_hold_deep(x);
    let v = lit_vec(x ^ 0xf0f0);
    let h = lit_hold(x.rotate_left(7));
    let ht = lit_hold_t(!x);
    look_hold_deep(&hd)
        ^ look_vec(&v).rotate_left(11)
        ^ look_hold(&h).rotate_left(23)
        ^ look_hold_t(&ht).rotate_left(31)
}

// ---- arr_*: array literal of scalarized aggregates -----------------------------

#[inline(never)]
fn arr_n1(x: u64) -> [N1; 2] {
    let mut a = N1 {
        zf: (),
        p: x as u32,
        q: (x >> 32) as u32,
    };
    a.p ^= black_box(1);
    let mut b = N1 {
        zf: (),
        p: (x >> 16) as u32,
        q: !(x as u32),
    };
    b.q ^= black_box(2);
    [a, b]
}

#[no_mangle]
pub extern "C" fn arr_lit(x: u64, i: u32) -> u64 {
    let g = arr_n1(x);
    let e = &g[(i % 2) as usize];
    (e.p as u64) | ((e.q as u64) << 32)
}

// ---- mem_* / deref_*: whole copy into a scalarized local -----------------------

#[derive(Clone, Copy)]
pub struct L1 {
    z: PhantomData<u8>,
    a: u32,
    b: u32,
}

#[inline(never)]
fn poke(p: &mut L1) {
    p.a ^= black_box(1);
}

#[no_mangle]
pub extern "C" fn mem_copy(x: u64) -> u64 {
    let mut s = L1 {
        z: PhantomData,
        a: x as u32,
        b: (x >> 32) as u32 ^ 0x5555,
    };
    poke(&mut s);
    let t = s;
    t.a as u64
}

#[no_mangle]
pub extern "C" fn mem_copy_both(x: u64) -> u64 {
    let mut s = L1 {
        z: PhantomData,
        a: x as u32,
        b: (x >> 32) as u32 ^ 0x5555,
    };
    poke(&mut s);
    let t = s;
    (t.a as u64) | ((t.b as u64) << 32)
}

#[inline(never)]
fn through(r: &&L1) -> u64 {
    let t: L1 = **r;
    t.a as u64
}

#[no_mangle]
pub extern "C" fn deref_copy(x: u64) -> u64 {
    let s = L1 {
        z: PhantomData,
        a: x as u32,
        b: (x >> 32) as u32 ^ 0x5555,
    };
    through(&&s)
}

// ---- borrow_*: `&(*p).k` after a multi-leaf field ------------------------------

#[derive(Clone, Copy)]
pub struct In2 {
    u: u32,
    v: u32,
}
#[derive(Clone, Copy)]
pub struct Ob {
    a: In2,
    k: u32,
    m: PhantomData<u8>,
    j: u32,
}

#[inline(never)]
fn pick(x: u64) -> u64 {
    let mut o = Ob {
        a: In2 {
            u: x as u32,
            v: (x >> 32) as u32,
        },
        k: (x as u32) ^ 0xdead,
        m: PhantomData,
        j: (x >> 16) as u32,
    };
    o.k ^= black_box(3);
    let p = &o;
    let r = &p.k;
    let s = &p.j;
    (*r as u64) | ((*s as u64) << 32)
}

#[no_mangle]
pub extern "C" fn borrow_pick(x: u64) -> u64 {
    pick(x)
}

// ---- al_*: field types declared through an associated-type projection ---------
//
// `o: <u8 as Tr>::O` (and `T::O` at `T = u8`) is the newtype `W`, and
// `z: <u8 as Tr>::Z` is the flattening zero-sized `Zw`. The binder sees the
// normalized field types, so these aggregates use the RECURSIVE FLAT scheme;
// every reader must decide on normalized types too, or it reads `o` for `a`.

pub trait Tr {
    type O: Copy;
    type Z: Copy;
}
#[derive(Clone, Copy)]
pub struct W(u32);
#[derive(Clone, Copy)]
pub struct Zw {
    m: PhantomData<u8>,
}
impl Tr for u8 {
    type O = W;
    type Z = Zw;
}
#[derive(Clone, Copy)]
pub struct As {
    z: (),
    a: u32,
    o: <u8 as Tr>::O,
}
#[derive(Clone, Copy)]
pub struct At {
    z: <u8 as Tr>::Z,
    a: u32,
    b: u32,
}
#[derive(Clone, Copy)]
pub struct Ag<T: Tr> {
    z: (),
    a: u32,
    o: T::O,
}
#[derive(Clone, Copy)]
pub struct Ah {
    h: u16,
    s: Ag<u8>,
    k: u8,
}

fn ag(x: u64) -> Ag<u8> {
    Ag {
        z: (),
        a: x as u32,
        o: W((x >> 32) as u32 ^ 0x5151),
    }
}

#[no_mangle]
pub extern "C" fn al_read(x: u64) -> u64 {
    let s = As {
        z: (),
        a: black_box(x as u32),
        o: W(black_box((x >> 32) as u32 ^ 0x5151)),
    };
    (s.a as u64) ^ ((s.o.0 as u64) << 32)
}

#[no_mangle]
pub extern "C" fn al_zst(x: u64) -> u64 {
    let t = At {
        z: Zw { m: PhantomData },
        a: black_box(x as u32),
        b: black_box((x >> 32) as u32 ^ 0x6262),
    };
    (t.a as u64) ^ ((t.b as u64) << 32)
}

#[no_mangle]
pub extern "C" fn al_generic(x: u64) -> u64 {
    let s = Ag::<u8> {
        z: (),
        a: black_box(x as u32),
        o: W(black_box((x >> 32) as u32 ^ 0x5151)),
    };
    (s.a as u64) ^ ((s.o.0 as u64) << 32)
}

#[inline(never)]
fn al_poke(s: &mut Ag<u8>) {
    s.a ^= black_box(1);
}

#[inline(never)]
fn al_byv(s: Ag<u8>) -> u64 {
    (s.a as u64) ^ ((s.o.0 as u64) << 32)
}

#[no_mangle]
pub extern "C" fn al_mem_copy_byv(x: u64) -> u64 {
    let mut s = ag(x);
    al_poke(&mut s);
    let t = s;
    al_byv(t)
}

#[no_mangle]
pub extern "C" fn al_mem_copy_lit(x: u64) -> u64 {
    let mut s = ag(x);
    al_poke(&mut s);
    let t = s;
    let h = black_box(Ah { h: 3, s: t, k: 4 });
    (h.s.a as u64) ^ ((h.s.o.0 as u64) << 32) ^ ((h.h as u64) << 8)
}

#[no_mangle]
pub extern "C" fn al_fs(x: u64) -> u64 {
    let mut h = black_box(Ah {
        h: 3,
        s: ag(0),
        k: 4,
    });
    let t = ag(x);
    h.s = t;
    (h.s.a as u64) ^ ((h.s.o.0 as u64) << 32) ^ ((h.k as u64) << 16)
}

#[inline(never)]
fn al_put(d: &mut Ag<u8>, x: u64) {
    let t = Ag::<u8> {
        z: (),
        a: black_box(x as u32) ^ 0x77,
        o: W((x >> 32) as u32),
    };
    *d = t;
}

#[no_mangle]
pub extern "C" fn al_ws(x: u64) -> u64 {
    let mut d = ag(0);
    al_put(&mut d, x);
    (d.a as u64) ^ ((d.o.0 as u64) << 32)
}

#[no_mangle]
pub extern "C" fn al_as(x: u64, i: u32) -> u64 {
    let mut g = [ag(1), ag(2), ag(3)];
    let k = (i % 3) as usize;
    let w = W(black_box((x >> 32) as u32));
    g[k] = Ag {
        z: (),
        a: x as u32,
        o: w,
    };
    let e = g[black_box(k)];
    (e.a as u64) ^ ((e.o.0 as u64) << 32)
}
