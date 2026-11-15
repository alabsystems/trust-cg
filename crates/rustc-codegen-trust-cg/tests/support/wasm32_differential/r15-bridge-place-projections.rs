// Every kind of MIR place projection, and the address arithmetic that is
// not one, on wasm32 at O0 to O3.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// At O1 and above the bridge spells a constant-offset address Rust
// guarantees in bounds as a trust-ir `gep inbounds u8 base, [k]`
// (`src/wasm32_inbounds.rs`): fields of a local, through `&`, `&mut` and a
// raw pointer, nested fields, a front `ConstantIndex` of an array place
// (array patterns), fields after a runtime index, enum variant fields,
// packed and zero-sized fields, the lanes of an aggregate copied whole (a
// hidden return buffer, a copy through a reference) and a `&dyn` vtable's
// method slot. The rest stays an integer chain: `ptr::wrapping_add` /
// `wrapping_sub` (which may leave the allocation and come back), integer
// address arithmetic, `ptr::add`, a runtime index, and the elements a slice
// pattern binds from a `&[T]` (the slice element path, `ends` below). Each
// export below exercises one kind; LLVM is the oracle.
#![no_std]
#![allow(dead_code)]

// wasm32-differential-flags: -Copt-level=1
// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=3

use core::marker::PhantomData;
use core::ptr::{addr_of, addr_of_mut};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[derive(Clone, Copy)]
struct S {
    a: u32,
    b: u64,
    c: u16,
}

#[derive(Clone, Copy)]
struct Inner {
    p: u32,
    q: [u16; 3],
}

#[derive(Clone, Copy)]
struct Outer {
    x: u8,
    inner: Inner,
    y: u64,
}

#[repr(C, packed)]
#[derive(Clone, Copy)]
struct Packed {
    a: u8,
    b: u32,
    c: u16,
}

struct WithZst {
    a: u32,
    z: (),
    b: u16,
    m: PhantomData<u8>,
}

#[derive(Clone, Copy)]
struct Big {
    x: [u32; 6],
    y: u64,
}

#[derive(Clone, Copy)]
enum E {
    A(u32, u64),
    B { x: u16, y: u32 },
    C,
}

#[inline(never)]
fn read_ref(s: &S) -> u64 {
    s.b.wrapping_add(u64::from(s.c)) ^ u64::from(s.a)
}

#[inline(never)]
fn bump(s: &mut S, k: u32) {
    s.b = s.b.wrapping_add(u64::from(k));
    s.c ^= k as u16;
    s.a = s.a.rotate_left(k & 31);
}

#[inline(never)]
fn read_raw(p: *const S) -> u64 {
    unsafe { (*p).b ^ u64::from(addr_of!((*p).c).read()) }
}

#[inline(never)]
fn nested(o: &Outer) -> u32 {
    o.inner.p ^ u32::from(o.inner.q[2]) ^ u32::from(o.x)
}

#[inline(never)]
fn nested_mut(o: &mut Outer, k: u16) {
    o.inner.q[1] = o.inner.q[1].wrapping_add(k);
    o.y ^= u64::from(o.inner.q[1]);
}

// A slice pattern on a `&[T]` reads through the slice element path, which
// keeps its integer chain.
#[inline(never)]
fn ends(s: &[u32]) -> u32 {
    match s {
        [a, b, ..] => a.wrapping_mul(3) ^ b,
        [a] => *a,
        [] => 7,
    }
}

#[inline(never)]
fn pick(arr: &[S; 4], i: usize) -> u64 {
    arr[i % 4].b ^ u64::from(arr[(i + 1) % 4].c)
}

#[inline(never)]
fn variant(e: &E) -> u64 {
    match e {
        E::A(x, y) => u64::from(*x) ^ *y,
        E::B { x, y } => u64::from(*x).wrapping_mul(5) ^ u64::from(*y),
        E::C => 11,
    }
}

#[inline(never)]
fn packed_ref(p: &Packed) -> u32 {
    let b = unsafe { addr_of!(p.b).read_unaligned() };
    let c = p.c;
    b ^ u32::from(c) ^ u32::from(p.a)
}

#[inline(never)]
fn packed_raw(p: *mut Packed, k: u32) -> u32 {
    unsafe {
        addr_of_mut!((*p).b).write_unaligned(k.wrapping_mul(7));
        addr_of!((*p).b).read_unaligned() ^ u32::from((*p).a)
    }
}

#[inline(never)]
fn zst_fields(w: &WithZst) -> u32 {
    let base = w as *const WithZst as usize;
    let z = addr_of!(w.z) as usize - base;
    let m = addr_of!(w.m) as usize - base;
    w.a ^ u32::from(w.b) ^ (z as u32) << 8 ^ (m as u32) << 16
}

#[inline(never)]
fn make_big(a: u32, b: u64) -> Big {
    Big {
        x: [a, a ^ 1, a.wrapping_mul(3), 4, 5, a >> 1],
        y: b,
    }
}

#[inline(never)]
fn copy_through(dst: &mut Big, src: &Big) {
    *dst = *src;
}

trait Shape {
    fn area(&self, k: u32) -> u32;
    fn sides(&self) -> u32;
}

struct Rect {
    w: u32,
    h: u32,
}

struct Tri {
    b: u32,
    h: u32,
    pad: u64,
}

impl Shape for Rect {
    fn area(&self, k: u32) -> u32 {
        self.w.wrapping_mul(self.h).wrapping_add(k)
    }
    fn sides(&self) -> u32 {
        4
    }
}

impl Shape for Tri {
    fn area(&self, k: u32) -> u32 {
        (self.b.wrapping_mul(self.h) / 2) ^ k ^ self.pad as u32
    }
    fn sides(&self) -> u32 {
        3
    }
}

#[inline(never)]
fn dyn_call(s: &dyn Shape, k: u32) -> u32 {
    s.area(k).wrapping_mul(s.sides())
}

#[derive(Clone, Copy)]
struct Wrap {
    h: u16,
    arr: [S; 3],
}

// Array patterns lower to front `ConstantIndex` projections of an array
// place, through `&`, `&mut` and a raw pointer, with a field prefix and a
// field suffix.
#[inline(never)]
fn const_elems(a: &[u32; 4]) -> u32 {
    let [x, _, y, ..] = *a;
    x.wrapping_mul(5) ^ y
}

#[inline(never)]
fn const_elem_field(w: &Wrap) -> u64 {
    let [_, ref m, ..] = w.arr;
    m.b ^ u64::from(w.h)
}

#[inline(never)]
fn const_elem_mut(w: &mut Wrap, k: u64) {
    let [_, _, last] = &mut w.arr;
    last.b ^= k;
    last.c = last.c.wrapping_add(k as u16);
}

#[inline(never)]
fn const_elem_raw(p: *const Wrap) -> u32 {
    unsafe {
        let [_, ref m, _] = (*p).arr;
        m.a ^ u32::from((*p).h)
    }
}

#[no_mangle]
pub extern "C" fn field_local(a: u32, b: u64) -> u64 {
    let s = S { a, b, c: a as u16 };
    read_ref(&s) ^ u64::from(s.c)
}

#[no_mangle]
pub extern "C" fn field_mut_ref(a: u32, b: u64) -> u64 {
    let mut s = S {
        a,
        b,
        c: (a >> 3) as u16,
    };
    bump(&mut s, a);
    bump(&mut s, a ^ 5);
    read_ref(&s)
}

#[no_mangle]
pub extern "C" fn field_raw_pointer(a: u32, b: u64) -> u64 {
    let s = S {
        a,
        b: b.rotate_left(3),
        c: 0x1234,
    };
    read_raw(&s)
}

#[no_mangle]
pub extern "C" fn nested_fields(a: u32, b: u32) -> u64 {
    let mut o = Outer {
        x: a as u8,
        inner: Inner {
            p: b,
            q: [a as u16, b as u16, (a ^ b) as u16],
        },
        y: u64::from(a) << 32,
    };
    nested_mut(&mut o, b as u16);
    u64::from(nested(&o)) ^ o.y
}

#[no_mangle]
pub extern "C" fn constant_index(a: u32, b: u32) -> u32 {
    let v = [a, b, a ^ b, 9];
    let n = (b % 5) as usize;
    ends(&v[..n.min(4)]) ^ v[3] ^ v[0]
}

#[no_mangle]
pub extern "C" fn index_then_field(a: u32, i: u32) -> u64 {
    let arr = [
        S { a, b: 1, c: 2 },
        S {
            a: 3,
            b: u64::from(a),
            c: 4,
        },
        S {
            a: 5,
            b: 6,
            c: a as u16,
        },
        S {
            a: 7,
            b: u64::from(i),
            c: 8,
        },
    ];
    pick(&arr, i as usize)
}

#[no_mangle]
pub extern "C" fn enum_fields(a: u32, b: u64) -> u64 {
    let e = match a % 3 {
        0 => E::A(a, b),
        1 => E::B {
            x: a as u16,
            y: b as u32,
        },
        _ => E::C,
    };
    variant(&e)
}

#[no_mangle]
pub extern "C" fn packed_fields(a: u32, b: u32) -> u32 {
    let mut p = Packed {
        a: a as u8,
        b,
        c: (a >> 16) as u16,
    };
    let r = packed_ref(&p);
    r ^ packed_raw(&mut p, a) ^ { p.b }
}

#[no_mangle]
pub extern "C" fn zst_projection(a: u32, b: u32) -> u32 {
    let w = WithZst {
        a,
        z: (),
        b: b as u16,
        m: PhantomData,
    };
    zst_fields(&w)
}

#[no_mangle]
pub extern "C" fn aggregate_return(a: u32, b: u64) -> u64 {
    let big = make_big(a, b);
    let mut acc = big.y;
    for x in big.x {
        acc = acc.wrapping_mul(31).wrapping_add(u64::from(x));
    }
    acc
}

#[no_mangle]
pub extern "C" fn aggregate_copy(a: u32, b: u64) -> u64 {
    let src = make_big(a, b);
    let mut dst = make_big(b as u32, u64::from(a));
    copy_through(&mut dst, &src);
    dst.y ^ u64::from(dst.x[5]) ^ u64::from(dst.x[2])
}

#[no_mangle]
pub extern "C" fn vtable_slots(a: u32, b: u32) -> u32 {
    let r = Rect { w: a, h: b };
    let t = Tri {
        b: a,
        h: b,
        pad: u64::from(a ^ b),
    };
    let s: &dyn Shape = if a & 1 == 0 { &r } else { &t };
    dyn_call(s, b) ^ dyn_call(&t, a)
}

#[no_mangle]
pub extern "C" fn constant_index_through_references(a: u32, b: u64) -> u64 {
    let v = [a, a ^ 3, a.wrapping_mul(7), b as u32];
    let mut w = Wrap {
        h: (a >> 4) as u16,
        arr: [
            S { a, b, c: 1 },
            S {
                a: a ^ 9,
                b: b.rotate_left(5),
                c: 2,
            },
            S {
                a: 3,
                b: u64::from(a),
                c: a as u16,
            },
        ],
    };
    const_elem_mut(&mut w, b);
    u64::from(const_elems(&v))
        ^ const_elem_field(&w)
        ^ u64::from(const_elem_raw(&w))
        ^ w.arr[2].b
        ^ u64::from(w.arr[2].c)
}

/// `wrapping_add` may leave the allocation and come back: it stays an
/// integer chain, never a GEP.
#[no_mangle]
pub extern "C" fn wrapping_round_trip(a: u32, k: u32) -> u32 {
    let v = [a, a ^ 0x55, a.wrapping_add(k)];
    let p = v.as_ptr();
    let far = (k as usize) << 20;
    let q = p.wrapping_add(far).wrapping_sub(far);
    unsafe { q.wrapping_add(2).read() ^ q.read() }
}

/// Integer address arithmetic stays integer arithmetic.
#[no_mangle]
pub extern "C" fn integer_address(a: u32, b: u32) -> u32 {
    let s = S {
        a,
        b: u64::from(b),
        c: 3,
    };
    // Both compilers lay `S` out alike; the words read are fields, not padding.
    let base = &s as *const S as usize;
    let at = base + 8;
    unsafe { (at as *const u32).read() ^ (base as *const u32).read() }
}

/// `ptr::add` stays an integer chain (`wasm32_inbounds` module docs).
#[no_mangle]
pub extern "C" fn pointer_add(a: u32, k: u32) -> u32 {
    let v = [a, a ^ k, 3, a.wrapping_mul(k)];
    let p = v.as_ptr();
    unsafe { p.add(1).read() ^ p.add((k % 4) as usize).read() ^ p.add(3).read() }
}
