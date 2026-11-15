// Over-aligned aggregates and by-memory `extern "C"` values, on wasm32.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ALIGNMENT. A `#[repr(align(32))]` / `align(64)` / `align(4096)` aggregate
// gets a memory slot at rustc's alignment (the wasm lane realigns its frame),
// so every address below is as aligned as Rust guarantees, field offsets and
// array strides are rustc's, and copies, by-value passing (rustc passes these
// indirectly), returns, `&dyn` receivers, closures capturing one, `Option` of
// one, statics and a scalar cell padded by `align(64)` all agree with LLVM.
// An address modulo the type's own alignment is always 0 on both sides; no
// export compares an address modulo anything larger.
//
// BY-MEMORY `extern "C"` VALUES. rustc's wasm32 C ABI passes a union whose
// members are not one same-size unit (`union { u32, u16 }`,
// `union { f64, u64 }`), a padded one-field union or struct, a one-lane
// `align(16)` struct and an `align(32)` struct through memory: a pointer to a
// caller-made copy, and a caller buffer (`sret`) for a return. Each is called
// directly, through a `fn` pointer, through a vtable slot (an `extern "C"`
// trait method), and in the dependency `extern/r5-bridge-align-abi-dep.rs`,
// which each side builds with its own backend.
//
// THE BOUNDARY WITH LLVM. The dependency `extern/r5-bridge-align-abi-llvm.rs`
// is built by LLVM on both sides, so the `lb_*` exports cross the ABI
// boundary between this backend's code and LLVM's: by-memory C values and
// Rust-ABI over-aligned values (rustc passes both as a pointer the callee may
// use as the value's address), passed and returned directly, through `fn`
// pointers and through trait objects, with LLVM as the callee and as the
// caller.
#![no_std]
#![allow(dead_code)]

// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Ccodegen-units=4 -Copt-level=1
// wasm32-differential-extern: align_abi_dep r5-bridge-align-abi-dep.rs
// wasm32-differential-extern-llvm: align_abi_llvm r5-bridge-align-abi-llvm.rs

extern crate align_abi_dep;
extern crate align_abi_llvm;

use core::hint::black_box;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[inline(never)]
fn addr_mod<T>(x: &T, m: usize) -> u32 {
    (x as *const T as usize % m) as u32
}

// ---- over-aligned aggregates ----------------------------------------------

#[repr(C, align(32))]
#[derive(Clone, Copy)]
pub struct A32 {
    pub a: u32,
    pub b: u64,
}

#[repr(align(64))]
#[derive(Clone, Copy)]
pub struct A64 {
    pub x: u128,
    pub y: [u16; 3],
}

#[repr(align(64))]
#[derive(Clone, Copy)]
struct Cell64 {
    a: u64,
}

#[derive(Clone, Copy)]
struct OuterCell {
    x: Cell64,
}

#[derive(Clone, Copy)]
struct Nest {
    t: u8,
    inner: A64,
    z: u32,
}

#[repr(align(4096))]
#[derive(Clone, Copy)]
struct Page {
    v: u32,
}

#[repr(align(64))]
struct Z64;

trait Get {
    fn get(&self) -> u64;
}

impl Get for A32 {
    fn get(&self) -> u64 {
        (self.a as u64 ^ self.b) + addr_mod(self, 32) as u64
    }
}

impl Get for A64 {
    fn get(&self) -> u64 {
        (self.x >> 64) as u64 + self.y[2] as u64 + addr_mod(self, 64) as u64
    }
}

#[inline(never)]
fn take_a32(x: A32) -> u64 {
    x.a as u64 ^ x.b ^ addr_mod(&x, 32) as u64
}

#[inline(never)]
fn make_a32(k: u32) -> A32 {
    A32 {
        a: k,
        b: (k as u64) << 7,
    }
}

#[inline(never)]
fn take_a64(x: A64) -> u64 {
    (x.x as u64).wrapping_add(x.y[0] as u64) + addr_mod(&x, 64) as u64
}

#[inline(never)]
fn bump(x: &mut A32, k: u32) {
    x.a = x.a.wrapping_mul(3).wrapping_add(k);
    x.b ^= 0x55;
}

#[inline(never)]
fn maybe_a32(k: u32) -> Option<A32> {
    if k % 3 == 0 {
        None
    } else {
        Some(A32 { a: k, b: 1 })
    }
}

#[inline(never)]
fn make_nest(k: u32) -> Nest {
    Nest {
        t: k as u8,
        inner: A64 {
            x: (k as u128) << 70,
            y: [k as u16, 2, 3],
        },
        z: !k,
    }
}

static S64: A64 = A64 {
    x: 1 << 100,
    y: [7, 8, 9],
};

static mut SM32: A32 = A32 { a: 1, b: 2 };

#[no_mangle]
pub extern "C" fn al_local(k: u32) -> u32 {
    let p = 1u8;
    let x = A32 { a: k, b: 1 };
    let y = A64 {
        x: k as u128,
        y: [1, 2, 3],
    };
    addr_mod(&p, 1) + addr_mod(&x, 32) + addr_mod(&y, 64) + addr_mod(&y.y, 2) + x.a
}

#[no_mangle]
pub extern "C" fn al_cell(k: u32) -> u32 {
    let o = OuterCell {
        x: Cell64 { a: k as u64 },
    };
    addr_mod(&o, 64) + addr_mod(&o.x, 64) + o.x.a as u32
}

#[no_mangle]
pub extern "C" fn al_nest(k: u32) -> u64 {
    let n = make_nest(k);
    let r = black_box(&n);
    let off = (&r.inner as *const A64 as usize - r as *const Nest as usize) as u64;
    addr_mod(r, 64) as u64 + off * 1000 + (r.inner.x >> 70) as u64 + r.z as u64 + r.t as u64
}

#[no_mangle]
pub extern "C" fn al_copy(k: u32) -> u64 {
    let x = A32 { a: k, b: 77 };
    let y = black_box(x);
    let z = y;
    take_a32(z) + take_a32(make_a32(k ^ 5)) + addr_mod(&z, 32) as u64
}

#[no_mangle]
pub extern "C" fn al_a64(k: u32) -> u64 {
    let x = A64 {
        x: (k as u128) << 64 | k as u128,
        y: [k as u16, 2, 3],
    };
    take_a64(black_box(x)) + addr_mod(&x, 64) as u64
}

#[no_mangle]
pub extern "C" fn al_refs(k: u32) -> u64 {
    let mut x = make_a32(k);
    bump(&mut x, k);
    let d: &dyn Get = black_box(&x);
    d.get() + addr_mod(&x, 32) as u64
}

#[no_mangle]
pub extern "C" fn al_dyn64(k: u32) -> u64 {
    let a = A64 {
        x: (k as u128) << 64,
        y: [0, 0, 5],
    };
    let d: &dyn Get = black_box(&a);
    d.get()
}

#[no_mangle]
pub extern "C" fn al_array(k: u32) -> u64 {
    let mut a = [A32 { a: 0, b: 0 }; 4];
    let i = (k % 4) as usize;
    a[i].b = k as u64;
    let c = a;
    let s = black_box(&c);
    let stride = (&s[1] as *const A32 as usize - &s[0] as *const A32 as usize) as u64;
    s[i].b + addr_mod(&s[3], 32) as u64 + stride * 100
}

#[no_mangle]
pub extern "C" fn al_option(k: u32) -> u64 {
    match maybe_a32(k) {
        Some(a) => a.b + a.a as u64 + addr_mod(&a, 32) as u64,
        None => 99,
    }
}

#[no_mangle]
pub extern "C" fn al_replace(k: u32) -> u64 {
    let mut x = A32 { a: k, b: 1 };
    let y = A32 { a: 2, b: k as u64 };
    let z = core::mem::replace(&mut x, y);
    x.b + z.a as u64 * 3 + addr_mod(&x, 32) as u64
}

#[no_mangle]
pub extern "C" fn al_closure(k: u32) -> u64 {
    let a = A32 { a: k, b: 7 };
    let f = move |j: u32| a.a as u64 + j as u64 + addr_mod(&a, 32) as u64;
    black_box(f)(3)
}

#[no_mangle]
pub extern "C" fn al_statics(k: u32) -> u64 {
    let r = black_box(&S64);
    let s = unsafe {
        let p = &raw mut SM32;
        (*p).a = (*p).a.wrapping_add(k);
        addr_mod(&*p, 32) as u64 + (*p).a as u64 + (*p).b
    };
    addr_mod(r, 64) as u64 + (r.x >> 100) as u64 + r.y[(k % 3) as usize] as u64 + s
}

#[no_mangle]
pub extern "C" fn al_page(k: u32) -> u32 {
    let p = Page { v: k };
    let q = black_box(p);
    addr_mod(&q, 4096) + q.v
}

#[no_mangle]
pub extern "C" fn al_zst(k: u32) -> u32 {
    let z = Z64;
    addr_mod(&z, 64) + k
}

// ---- by-memory `extern "C"` values -----------------------------------------

#[repr(C)]
#[derive(Clone, Copy)]
pub union U4 {
    pub a: u32,
    pub c: u16,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub union U8 {
    pub a: u64,
    pub b: [u8; 8],
}

#[repr(C)]
#[derive(Clone, Copy)]
pub union F8 {
    pub f: f64,
    pub u: u64,
}

#[repr(C, align(8))]
#[derive(Clone, Copy)]
pub union Q {
    pub a: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct WQ {
    pub q: Q,
}

#[repr(C, align(8))]
#[derive(Clone, Copy)]
pub struct S8 {
    pub a: u32,
}

#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct A16 {
    pub a: u32,
    pub b: u64,
}

#[repr(C, align(64))]
#[derive(Clone, Copy)]
pub union UA {
    pub a: u32,
    pub c: u16,
}

#[inline(never)]
extern "C" fn c_take_u4(x: U4) -> u32 {
    unsafe { x.a ^ 0x1234 }
}

#[inline(never)]
extern "C" fn c_take_u8(x: U8) -> u64 {
    unsafe { x.a.rotate_left(7) ^ x.b[3] as u64 }
}

#[inline(never)]
extern "C" fn c_take_f8(x: F8) -> u64 {
    unsafe { x.u ^ 1 }
}

#[inline(never)]
extern "C" fn c_take_many(k: u32, x: U4, y: U8, z: u64, q: Q) -> u64 {
    unsafe { k as u64 + x.a as u64 * 3 + y.a + z + q.a as u64 }
}

#[inline(never)]
extern "C" fn c_take_addr(x: U4) -> u32 {
    let p = &x as *const U4 as usize;
    unsafe { x.a + (p % 4) as u32 }
}

#[inline(never)]
extern "C" fn c_take_mut(mut x: U4, k: u32) -> u32 {
    unsafe {
        x.a = x.a.wrapping_add(k);
        x.a
    }
}

#[inline(never)]
extern "C" fn c_take_q(x: Q) -> u32 {
    unsafe { x.a ^ 0x77 }
}

#[inline(never)]
extern "C" fn c_take_wq(x: WQ) -> u32 {
    c_take_q(x.q) + 1
}

#[inline(never)]
extern "C" fn c_take_s8(x: S8) -> u32 {
    x.a.wrapping_mul(9)
}

#[inline(never)]
extern "C" fn c_take_a16(x: A16) -> u64 {
    x.a as u64 + x.b * 3 + addr_mod(&x, 16) as u64
}

#[inline(never)]
extern "C" fn c_take_a32(x: A32, k: u32) -> u64 {
    x.a as u64 ^ x.b ^ k as u64 ^ addr_mod(&x, 32) as u64
}

#[inline(never)]
extern "C" fn c_take_ua(x: UA) -> u32 {
    unsafe { x.a ^ 9 }
}

#[inline(never)]
extern "C" fn c_ret_u4(k: u32) -> U4 {
    U4 { a: k ^ 0x5555_aaaa }
}

#[inline(never)]
extern "C" fn c_ret_u8(k: u64) -> U8 {
    U8 {
        a: k.wrapping_mul(0x1_0000_0001),
    }
}

#[inline(never)]
extern "C" fn c_ret_f8(k: u64) -> F8 {
    F8 { u: k | 1 }
}

#[inline(never)]
extern "C" fn c_ret_q(k: u32) -> Q {
    Q {
        a: k.rotate_left(3),
    }
}

#[inline(never)]
extern "C" fn c_ret_wq(k: u32) -> WQ {
    WQ { q: Q { a: k ^ 5 } }
}

#[inline(never)]
extern "C" fn c_ret_s8(k: u32) -> S8 {
    S8 { a: k + 11 }
}

#[inline(never)]
extern "C" fn c_ret_a16(k: u32) -> A16 {
    A16 { a: !k, b: k as u64 }
}

#[inline(never)]
extern "C" fn c_ret_a32(k: u32) -> A32 {
    A32 {
        a: k,
        b: (k as u64) << 33,
    }
}

#[inline(never)]
extern "C" fn c_ret_ua(k: u32) -> UA {
    UA {
        a: k.wrapping_add(17),
    }
}

#[inline(never)]
extern "C" fn c_echo_u8(x: U8) -> U8 {
    x
}

#[inline(never)]
extern "C" fn c_echo_q(x: Q) -> Q {
    x
}

trait CMethod {
    extern "C" fn m(&self, x: U4) -> Q;
    extern "C" fn n(&self, x: A32) -> U8;
}

struct Obj(u32);

impl CMethod for Obj {
    extern "C" fn m(&self, x: U4) -> Q {
        unsafe { Q { a: x.a ^ self.0 } }
    }

    extern "C" fn n(&self, x: A32) -> U8 {
        U8 {
            a: x.b ^ self.0 as u64 ^ addr_mod(&x, 32) as u64,
        }
    }
}

#[no_mangle]
pub extern "C" fn cu_take(k: u32) -> u64 {
    c_take_u4(U4 { a: k }) as u64
        + c_take_u8(U8 { a: k as u64 * 3 })
        + c_take_f8(F8 { f: k as f64 })
        + c_take_addr(U4 { a: k }) as u64
        + c_take_mut(U4 { a: k }, 7) as u64
}

#[no_mangle]
pub extern "C" fn cu_many(k: u32, z: u64) -> u64 {
    c_take_many(k, U4 { a: k ^ 3 }, U8 { a: z }, z >> 3, Q { a: k })
}

#[no_mangle]
pub extern "C" fn cu_ret(k: u32) -> u64 {
    unsafe { c_ret_u4(k).a as u64 + c_ret_u8(k as u64).a + c_ret_f8(k as u64).u }
}

#[no_mangle]
pub extern "C" fn cu_chain(k: u32) -> u32 {
    c_take_u4(c_ret_u4(k)) ^ c_take_q(c_echo_q(c_ret_q(k))) ^ c_take_wq(c_ret_wq(k))
}

#[no_mangle]
pub extern "C" fn cu_padded(k: u32) -> u64 {
    let s = c_ret_s8(k);
    let q = c_ret_q(k ^ 1);
    let p = black_box(&q as *const Q as *const u32);
    c_take_s8(s) as u64
        + unsafe { *p } as u64
        + addr_mod(&q, 8) as u64
        + unsafe { c_echo_u8(U8 { a: k as u64 }).a }
}

#[no_mangle]
pub extern "C" fn cu_aligned(k: u32) -> u64 {
    let r = c_ret_a32(k);
    let h = c_ret_a16(k);
    c_take_a32(r, k)
        + r.b
        + addr_mod(&r, 32) as u64
        + c_take_a16(h)
        + c_take_a16(A16 { a: k, b: 5 })
}

#[no_mangle]
pub extern "C" fn cu_union_a64(k: u32) -> u32 {
    c_take_ua(c_ret_ua(k)) ^ unsafe { c_ret_ua(k ^ 3).a }
}

#[no_mangle]
pub extern "C" fn cu_fn_ptr(k: u32) -> u64 {
    let t4: extern "C" fn(U4) -> u32 = black_box(c_take_u4);
    let r4: extern "C" fn(u32) -> U4 = black_box(c_ret_u4);
    let e8: extern "C" fn(U8) -> U8 = black_box(c_echo_u8);
    let rq: extern "C" fn(u32) -> Q = black_box(c_ret_q);
    let ta: extern "C" fn(A32, u32) -> u64 = black_box(c_take_a32);
    let rh: extern "C" fn(u32) -> A16 = black_box(c_ret_a16);
    t4(r4(k)) as u64
        + unsafe { r4(k ^ 9).a } as u64
        + unsafe { e8(U8 { a: k as u64 * 7 }).a }
        + unsafe { rq(k).a } as u64
        + ta(A32 { a: k, b: 2 }, 1)
        + rh(k).b
}

#[no_mangle]
pub extern "C" fn cu_vtable(k: u32) -> u64 {
    let o = Obj(k.wrapping_mul(31));
    let d: &dyn CMethod = black_box(&o);
    unsafe { d.m(U4 { a: k }).a as u64 + d.n(A32 { a: k, b: 9 }).a }
}

#[no_mangle]
pub extern "C" fn cu_upstream(k: u32) -> u64 {
    use align_abi_dep as dep;
    let r = dep::dep_ret_u4(k);
    let q = dep::dep_echo_q(dep::Q { a: k });
    let a = dep::dep_ret_a32(k);
    dep::dep_take_u4(r, k) as u64
        + unsafe { q.a } as u64
        + dep::dep_take_a32(a)
        + addr_mod(&a, 32) as u64
}

// ---- the boundary with LLVM-built code ---------------------------------------

mod boundary {
    use align_abi_llvm::{C32, LObj, LTrait, R64, R128, S8, U4, U8, addr_mod};
    use core::hint::black_box;

    pub extern "C" fn b_c_callee(x: U4, y: C32) -> U8 {
        U8 {
            a: unsafe { x.a } as u64 + y.b * 7 + y.a as u64 + (addr_mod(&y, 32) << 40),
        }
    }

    pub extern "C" fn b_c_ret(k: u32) -> U4 {
        U4 {
            a: k.rotate_left(9),
        }
    }

    pub fn b_rust_callee(x: C32, y: R64) -> u64 {
        x.a as u64
            + x.b
            + y.a * 3
            + y.b as u64
            + (addr_mod(&x, 32) << 32)
            + (addr_mod(&y, 64) << 48)
    }

    pub fn b_rust_ret(k: u32) -> R64 {
        let mut x = R64 { a: 0, b: k };
        x.a = addr_mod(&x, 64) + 5;
        x
    }

    pub struct Mine(pub u64);

    impl LTrait for Mine {
        fn m(&self, x: C32) -> u64 {
            self.0 + x.b * 2 + (addr_mod(&x, 32) << 40)
        }

        fn r(&self, k: u32) -> R64 {
            let mut x = R64 { a: 0, b: k };
            x.a = addr_mod(&x, 64) + self.0;
            x
        }

        extern "C" fn c(&self, x: U8) -> U4 {
            U4 {
                a: unsafe { x.a as u32 }.wrapping_add(self.0 as u32),
            }
        }
    }

    pub fn obj(k: u32) -> LObj {
        LObj(k)
    }

    pub fn s8(k: u32) -> S8 {
        S8 { a: k }
    }

    pub fn r128(k: u32) -> R128 {
        R128 {
            a: k as u16 ^ 3,
            b: [4, 5, k as u8],
        }
    }

    pub fn keep<T>(x: T) -> T {
        black_box(x)
    }

    /// Direct calls from a frame whose other slots put a copy aligned only
    /// to 16 bytes at an address that is not 32- or 64-aligned.
    #[inline(never)]
    pub fn padded_calls(k: u32) -> u64 {
        let pad = [k as u8; 48];
        let r = black_box(R64 { a: k as u64, b: 2 });
        let x = C32 { a: k, b: 6 };
        black_box(&pad);
        align_abi_llvm::l_take_r64(r)
            + align_abi_llvm::l_take_c32(x, 3)
            + align_abi_llvm::l_take_two(k, x, r128(k ^ 1))
            + pad[5] as u64
    }
}

/// This backend calls LLVM's C-ABI functions directly.
#[no_mangle]
pub extern "C" fn lb_c_direct(k: u32) -> u64 {
    use align_abi_llvm as l;
    let r = l::l_ret_c32(k);
    l::l_take_u4(l::U4 { a: k }, k ^ 5) as u64
        + l::l_take_u8(l::U8 { a: k as u64 * 3 })
        + l::l_take_f8(l::F8 { f: k as f64 })
        + l::l_take_s8(boundary::s8(k))
        + l::l_take_c32(l::C32 { a: k, b: 7 }, 1)
        + r.b
        + unsafe { l::l_ret_u4(k).a as u64 + l::l_ret_u8(k as u64).a }
}

/// This backend calls LLVM's Rust-ABI functions directly, over-aligned values
/// by value and returned.
#[no_mangle]
pub extern "C" fn lb_rust_direct(k: u32) -> u64 {
    use align_abi_llvm as l;
    let r = l::l_ret_r64(k);
    let s = l::l_ret_r128(k);
    l::l_take_r64(l::R64 { a: k as u64, b: 1 })
        + l::l_take_two(k, l::C32 { a: k, b: 2 }, boundary::r128(k))
        + r.a
        + r.b as u64
        + ((addr_mod(&r, 64) as u64) << 40)
        + s.a as u64
        + s.b[2] as u64
        + boundary::padded_calls(k)
}

/// LLVM calls this backend's functions through pointers, and this backend
/// calls LLVM's through pointers LLVM hands over.
#[no_mangle]
pub extern "C" fn lb_fn_ptr(k: u32) -> u64 {
    use align_abi_llvm as l;
    let f = l::l_fn_ptr();
    let g = l::l_c_fn_ptr();
    l::l_call_c(boundary::b_c_callee, k)
        + l::l_call_c_ret(boundary::b_c_ret, k) as u64
        + l::l_call_rust(boundary::b_rust_callee, k)
        + l::l_call_rust_ret(boundary::b_rust_ret, k)
        + f(l::R64 { a: k as u64, b: 9 })
        + g(boundary::keep(l::C32 { a: 2, b: k as u64 }), k)
}

/// Trait objects built on each side, called on the other.
#[no_mangle]
pub extern "C" fn lb_vtable(k: u32) -> u64 {
    use align_abi_llvm as l;
    let d = l::l_obj();
    let mine = boundary::Mine(k as u64);
    let theirs = boundary::obj(k ^ 7);
    d.m(l::C32 { a: k, b: 4 })
        + d.r(k).a
        + unsafe { d.c(l::U8 { a: k as u64 }).a } as u64
        + l::l_use_dyn(black_box(&mine), k)
        + l::l_use_dyn(black_box(&theirs), k ^ 1)
}
