// wasm32 execution-differential corpus: trait objects and runtime-call
// declarations.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Each export reduces to a scalar what wasm32's pointer width changes in the
// bridge: `&dyn Trait` as a two-word (8-byte) element of arrays and slices
// (built, indexed, iterated and copied whole), returned by value, upcast to a
// non-first supertrait and measured by `size_of_val` / `align_of_val`; the C
// bulk-memory libcalls (`memcpy`, `memmove`, `memset`, `memcmp`), emitted by the
// bridge or declared by the crate, whose import types must match the library's;
// wrapping pointer offsets; `bool as u8` / `bool as i8`;
// and casts between pointers and 64-bit integers.

#![no_std]
#![allow(dead_code)]

use core::mem::MaybeUninit;
use core::sync::atomic::{AtomicBool, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

trait Shape {
    fn sides(&self) -> u32;
}
struct Square(u32);
struct Circle(u64);
impl Shape for Square {
    fn sides(&self) -> u32 {
        self.0.wrapping_add(4)
    }
}
impl Shape for Circle {
    fn sides(&self) -> u32 {
        (self.0 as u32).wrapping_mul(3) ^ 1
    }
}

#[inline(never)]
fn shape_at(v: &[&dyn Shape], i: usize) -> u32 {
    v[i].sides()
}

// `[&dyn T; 3]` built in place and indexed at a runtime index through a slice.
#[no_mangle]
pub extern "C" fn dyn_array_index(a: u32) -> u32 {
    let s = Square(a);
    let c = Circle(u64::from(a) + 7);
    let t = Square(a ^ 5);
    let arr: [&dyn Shape; 3] = [&s, &c, &t];
    shape_at(&arr, (a % 3) as usize)
}

// The array written by the constructor and read by `slice::Iter`.
#[no_mangle]
pub extern "C" fn dyn_array_iter(a: u32) -> u32 {
    let s = Square(a);
    let c = Circle(u64::from(a));
    let arr: [&dyn Shape; 2] = [&c, &s];
    let mut acc = 0u32;
    for d in arr.iter() {
        acc = acc.wrapping_mul(31).wrapping_add(d.sides());
    }
    acc
}

// A one-element slice built by `slice::from_ref`, read by the indexing path.
#[no_mangle]
pub extern "C" fn dyn_slice_from_ref(a: u32) -> u32 {
    let c = Circle(u64::from(a));
    let d: &dyn Shape = &c;
    shape_at(core::slice::from_ref(&d), 0)
}

#[inline(never)]
fn make_pair<'a>(x: &'a dyn Shape, y: &'a dyn Shape) -> [&'a dyn Shape; 2] {
    [x, y]
}

// A `[&dyn T; 2]` returned by value, then copied whole (`let ys = xs`).
#[no_mangle]
pub extern "C" fn dyn_array_copy(a: u32) -> u32 {
    let s = Square(a >> 3);
    let c = Circle(u64::from(a) + 50);
    let xs = make_pair(&s, &c);
    let ys = xs;
    shape_at(&ys, (a & 1) as usize)
}

#[inline(never)]
fn pick<'a>(k: u32, s: &'a Square, c: &'a Circle) -> &'a dyn Shape {
    if k & 1 == 0 { s } else { c }
}

// A `&dyn T` returned by value.
#[no_mangle]
pub extern "C" fn dyn_return(k: u32) -> u32 {
    let s = Square(k);
    let c = Circle(u64::from(k) * 2);
    pick(k, &s, &c).sides()
}

trait Base {
    fn b0(&self, x: u32) -> u32;
}
trait Other {
    fn o0(&self, x: u32) -> u32;
}
trait Sub: Base + Other {
    fn s0(&self, x: u32) -> u32;
}
struct Both {
    pad: u8,
    k: u32,
}
impl Base for Both {
    fn b0(&self, x: u32) -> u32 {
        x ^ self.k
    }
}
impl Other for Both {
    fn o0(&self, x: u32) -> u32 {
        x.wrapping_add(self.k)
    }
}
impl Sub for Both {
    fn s0(&self, x: u32) -> u32 {
        x.wrapping_mul(self.k | 1)
    }
}
#[inline(never)]
fn use_other(o: &dyn Other, x: u32) -> u32 {
    o.o0(x)
}

// Upcast to the second supertrait (a secondary vtable pointer).
#[no_mangle]
pub extern "C" fn dyn_upcast(x: u32, k: u32) -> u32 {
    let b = Both { pad: 3, k };
    let s: &dyn Sub = &b;
    let o: &dyn Other = s;
    use_other(o, x) ^ s.s0(x)
}

// `size_of_val` / `align_of_val` read the vtable's size and align words.
#[no_mangle]
pub extern "C" fn dyn_size_align(k: u32) -> u32 {
    let s = Square(1);
    let c = Circle(2);
    let d: &dyn Shape = if k % 2 == 0 { &s } else { &c };
    core::mem::size_of_val(d) as u32 | (core::mem::align_of_val(d) as u32) << 8
}

// `copy_nonoverlapping` with a runtime count: the `memcpy` libcall.
#[no_mangle]
pub extern "C" fn mem_copy_nonoverlapping(x: u32, k: u32) -> u32 {
    let a = [x, x ^ 3, x.wrapping_add(9)];
    let mut b = [7u32; 3];
    unsafe { core::ptr::copy_nonoverlapping(a.as_ptr(), b.as_mut_ptr(), (k % 4) as usize) };
    b[0] ^ b[1].rotate_left(8) ^ b[2].rotate_left(16)
}

// `ptr::copy` with a runtime count: the `memmove` libcall, overlapping.
#[no_mangle]
pub extern "C" fn mem_copy_overlapping(x: u32, k: u32) -> u32 {
    let mut a = [x, x ^ 1, x ^ 2, x ^ 3];
    let p = a.as_mut_ptr();
    unsafe { core::ptr::copy(p, p.add(1), (k % 4) as usize) };
    a[1] ^ a[2].rotate_left(8) ^ a[3].rotate_left(16)
}

// `copy_from_slice` and `copy_within` over bytes.
#[no_mangle]
pub extern "C" fn mem_slice_copies(x: u32, k: u32) -> u32 {
    let src = [x as u8, (x >> 8) as u8, (x >> 16) as u8, (x >> 24) as u8];
    let mut dst = [0u8; 8];
    let n = (k % 5) as usize;
    dst[..n].copy_from_slice(&src[..n]);
    dst.copy_within(0..4, (k % 5) as usize);
    dst[0] as u32 | (dst[3] as u32) << 8 | (dst[5] as u32) << 16 | (dst[7] as u32) << 24
}

// `ptr::write_bytes`, `<[u8]>::fill`, `<[u32]>::fill` and
// `MaybeUninit::zeroed`: the `memset` libcall.
#[no_mangle]
pub extern "C" fn mem_set(v: u32, n: u32) -> u32 {
    let mut a = [0x55u8; 8];
    unsafe { core::ptr::write_bytes(a.as_mut_ptr(), v as u8, (n % 9) as usize) };
    let mut b = [0u8; 8];
    b[..(n % 9) as usize].fill(v as u8 ^ 0x3c);
    let mut w = [1u32, 2, 3, 4, 5, 6];
    w[(n % 7) as usize..].fill(v);
    let z: [u32; 4] = unsafe { MaybeUninit::<[u32; 4]>::zeroed().assume_init() };
    (a[0] as u32 | (a[7] as u32) << 8 | (b[0] as u32) << 16 | (b[7] as u32) << 24)
        ^ w[5]
        ^ w[0]
        ^ z[(n % 4) as usize]
}

// `bool as u8` / `bool as i8`, `<bool as Ord>::cmp` and `AtomicBool::fetch_xor`.
#[no_mangle]
pub extern "C" fn bool_to_byte(a: i32, b: i32) -> u32 {
    let (p, q) = (a < b, a == 0);
    let u = p as u8 * 3 + q as u8;
    let i = (q as i8) - (p as i8);
    let ord = p.cmp(&q) as i8;
    let flag = AtomicBool::new(p);
    let old = flag.fetch_xor(q, Ordering::SeqCst);
    u as u32
        | ((i as u8) as u32) << 8
        | ((ord as u8) as u32) << 16
        | (old as u32) << 24
        | (flag.load(Ordering::SeqCst) as u32) << 25
}

// `<*const T>::wrapping_add` / `wrapping_sub` / `wrapping_offset`
// (the `arith_offset` intrinsic).
#[no_mangle]
pub extern "C" fn ptr_wrapping(k: u32) -> u32 {
    let a = [10u32, 20, 30, 40];
    let p = a.as_ptr();
    let q = p.wrapping_add((k % 4) as usize);
    let r = q.wrapping_sub((k / 4 % 2) as usize);
    let r = if r < p { p } else { r };
    let s = p.wrapping_offset(3).wrapping_offset(-((k % 3) as isize));
    unsafe { *q + *r * 3 + *s * 7 }
}

// `ptr as u64` / `ptr as i64`: the pointer zero-extended to 64 bits; and
// `u64 as *const T`: the integer truncated to the 32-bit `usize`.
#[no_mangle]
pub extern "C" fn ptr_as_u64(k: u32) -> u64 {
    let a = [1u64, 2, 3, 4];
    let p = &a[0] as *const u64;
    let q = &a[(k % 4) as usize] as *const u64;
    let d = (q as u64).wrapping_sub(p as u64);
    let e = (q as i64) - (p as i64);
    let high = (p as u64) >> 32 | ((p as i64) >> 32) as u64;
    let back = ((q as u64) | u64::from(k) << 40) as *const u64;
    d + (e as u64) * 3 + high + unsafe { *back } * 1000
}

// User `extern "C"` declarations of the bulk-memory routines, with typed and
// `c_void` pointers: each is the C prototype, so each links to the library
// definition rather than a trapping signature-mismatch stub. The crate's
// `memset` calls from `mem_set` share this declaration.
mod user_libc {
    use core::ffi::{c_int, c_void};
    extern "C" {
        pub fn memset(p: *mut u8, c: i32, n: usize) -> *mut u8;
        pub fn memcmp(a: *const c_void, b: *const c_void, n: usize) -> c_int;
        pub fn memcpy(d: *mut c_void, s: *const c_void, n: usize) -> *mut c_void;
        pub fn memmove(d: *mut c_void, s: *const c_void, n: usize) -> *mut c_void;
    }
}

#[no_mangle]
pub extern "C" fn mem_user_declared(v: u32, n: u32) -> u32 {
    use user_libc::*;
    let mut s = [1u8; 8];
    let set = unsafe { memset(s.as_mut_ptr(), v as i32, (n % 9) as usize) };
    let a = [v as u8, 2, 3, 4];
    let mut b = [v as u8, 2, (n >> 8) as u8, 4];
    let c = unsafe { memcmp(a.as_ptr().cast(), b.as_ptr().cast(), (n % 5) as usize) };
    let cp = unsafe { memcpy(b.as_mut_ptr().cast(), a.as_ptr().cast(), (n % 3) as usize) };
    let mut m = [1u8, 2, 3, 4, 5, 6];
    let mv = unsafe {
        memmove(
            m.as_mut_ptr().add(1).cast(),
            m.as_ptr().cast(),
            (n % 6) as usize,
        )
    };
    (set == s.as_mut_ptr()) as u32
        | (s[0] as u32) << 1
        | (s[7] as u32) << 9
        | ((c.signum() + 1) as u32) << 17
        | ((cp == b.as_mut_ptr().cast()) as u32) << 19
        | (b[2] as u32) << 20
        | ((mv == m.as_mut_ptr().wrapping_add(1).cast()) as u32) << 28
        | ((m[5] as u32) & 7) << 29
}
