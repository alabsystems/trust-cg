// wasm32 execution-differential corpus: the C ABI's narrow-integer
// extensions and one-field 128-bit aggregates at the boundary with LLVM, and
// the compile-resource shapes of the retained-address analysis and of large
// arrays passed by reference.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// * `ze_*` / `zr_*` / `zp_*`: rustc's wasm32 C ABI extends an 8- or 16-bit
//   integer `BackendRepr::Scalar` to the `i32` it travels as, by the
//   primitive's signedness, and the receiver relies on it. The values here
//   are held in one-lane memory slots by this backend (`Option<NonZeroU8>`,
//   `Option<NonZeroU16>`, `Option<#[repr(u8)] enum>` and an `Option` of an
//   enum with a discriminant of 200, `Result<(), NonZeroU8>`, a plain and a
//   `#[repr(transparent)]` newtype around `Option<NonZeroU8>`, `(u8,)`,
//   `(u16,)`, and the sign-extended `Option<NonZeroI8>` / `Option<NonZeroI16>`).
//   `ze_*` passes each as an argument to an LLVM-built callee, `zr_*` hands
//   this crate's definitions returning each to an LLVM-built caller through a
//   `fn` pointer, and `zp_*` has LLVM pass one to this crate's definition. The
//   LLVM side is `extern/r7-bridge-abi-llvm.rs`; with optimization it reads
//   the `i32` without re-extending it.
// * `cw_*`: a `#[repr(C)]` struct around one `i128` / `u128`, which rustc casts
//   to one 16-byte integer: two `i64` halves as an argument and a caller
//   buffer as a return, called directly in both directions and through `fn`
//   pointers.
// * `rc_*`: chains of calls passing a local's address down (a 64-deep
//   generic chain whose leaf keeps the pointer, and a mutually recursive
//   pair), whose retained-address summaries are solved once per crate.
// * `ab_*`: arrays of 4096 and 65536 elements passed by `&mut` / `&` and built
//   by a repeat expression.
//
// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=s -Ccodegen-units=4
// wasm32-differential-flags: -Copt-level=1 -Coverflow-checks=on
// wasm32-differential-extern-llvm: abi_llvm r7-bridge-abi-llvm.rs

#![no_std]
#![allow(improper_ctypes_definitions)]

extern crate abi_llvm;

use abi_llvm::{CU, CW, E8, Plain, T, W};
use core::hint::black_box;
use core::num::{NonZeroI8, NonZeroI16, NonZeroU8, NonZeroU16};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

fn e8(x: u32) -> Option<E8> {
    match x & 3 {
        0 => None,
        1 => Some(E8::A),
        2 => Some(E8::B),
        _ => Some(E8::C),
    }
}

fn plain(x: u32) -> Option<Plain> {
    match x % 3 {
        0 => None,
        1 => Some(Plain::A),
        _ => Some(Plain::B),
    }
}

fn res(x: u32) -> Result<(), NonZeroU8> {
    match NonZeroU8::new(x as u8) {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

// ---- ze_*: extended arguments to an LLVM callee ------------------------------

#[no_mangle]
pub extern "C" fn ze_nz8(x: u32) -> u32 {
    abi_llvm::take_nz8(NonZeroU8::new(black_box(x) as u8))
}

#[no_mangle]
pub extern "C" fn ze_nz16(x: u32) -> u32 {
    abi_llvm::take_nz16(NonZeroU16::new(black_box(x) as u16))
}

#[no_mangle]
pub extern "C" fn ze_nzi8(x: u32) -> i32 {
    abi_llvm::take_nzi8(NonZeroI8::new(black_box(x) as i8))
}

#[no_mangle]
pub extern "C" fn ze_nzi16(x: u32) -> i32 {
    abi_llvm::take_nzi16(NonZeroI16::new(black_box(x) as i16))
}

#[no_mangle]
pub extern "C" fn ze_e8(x: u32) -> u32 {
    abi_llvm::take_e8(e8(black_box(x)))
}

#[no_mangle]
pub extern "C" fn ze_plain(x: u32) -> u32 {
    abi_llvm::take_plain(plain(black_box(x)))
}

#[no_mangle]
pub extern "C" fn ze_res(x: u32) -> u32 {
    abi_llvm::take_res(res(black_box(x)))
}

#[no_mangle]
pub extern "C" fn ze_wrap(x: u32) -> u32 {
    let v = NonZeroU8::new(black_box(x) as u8);
    abi_llvm::take_w(W(v)) ^ abi_llvm::take_t(T(v)) << 9
}

#[no_mangle]
pub extern "C" fn ze_tuple(x: u32) -> u32 {
    let x = black_box(x);
    abi_llvm::take_t8((x as u8,)) ^ abi_llvm::take_t16(((x >> 3) as u16,)) << 8
}

/// A `fn` pointer to the LLVM callee: the call site declares the pointer's
/// own signature.
#[no_mangle]
pub extern "C" fn ze_ptr(x: u32) -> u32 {
    let f: extern "C" fn(Option<NonZeroU8>) -> u32 = black_box(abi_llvm::take_nz8);
    let g: extern "C" fn(Option<NonZeroU16>) -> u32 = black_box(abi_llvm::take_nz16);
    f(NonZeroU8::new(x as u8)) ^ g(NonZeroU16::new(x.rotate_left(7) as u16)) << 4
}

// ---- zr_*: extended returns read by an LLVM caller -----------------------------

extern "C" fn give_nz8(x: u32) -> Option<NonZeroU8> {
    NonZeroU8::new(x as u8)
}

extern "C" fn give_nz16(x: u32) -> Option<NonZeroU16> {
    NonZeroU16::new(x as u16)
}

extern "C" fn give_nzi8(x: u32) -> Option<NonZeroI8> {
    NonZeroI8::new(x as i8)
}

extern "C" fn give_e8(x: u32) -> Option<E8> {
    e8(x)
}

extern "C" fn give_plain(x: u32) -> Option<Plain> {
    plain(x)
}

extern "C" fn give_res(x: u32) -> Result<(), NonZeroU8> {
    res(x)
}

extern "C" fn give_w(x: u32) -> W {
    W(NonZeroU8::new(x as u8 ^ 0x80))
}

extern "C" fn give_t(x: u32) -> T {
    T(NonZeroU8::new(!x as u8))
}

extern "C" fn give_t8(x: u32) -> (u8,) {
    (x as u8 | 0x80,)
}

extern "C" fn give_t16(x: u32) -> (u16,) {
    (x as u16 ^ 0x8000,)
}

#[no_mangle]
pub extern "C" fn zr_nz(x: u32) -> u32 {
    abi_llvm::call_nz8(black_box(give_nz8), x)
        ^ abi_llvm::call_nz16(black_box(give_nz16), x.rotate_left(5)) << 4
}

#[no_mangle]
pub extern "C" fn zr_nzi8(x: u32) -> i32 {
    abi_llvm::call_nzi8(black_box(give_nzi8), x)
}

#[no_mangle]
pub extern "C" fn zr_enum(x: u32) -> u32 {
    abi_llvm::call_e8(black_box(give_e8), x) ^ abi_llvm::call_plain(black_box(give_plain), x) << 8
}

#[no_mangle]
pub extern "C" fn zr_res(x: u32) -> u32 {
    abi_llvm::call_res(black_box(give_res), x)
}

#[no_mangle]
pub extern "C" fn zr_wrap(x: u32) -> u32 {
    abi_llvm::call_w(black_box(give_w), x) ^ abi_llvm::call_t(black_box(give_t), x) << 9
}

#[no_mangle]
pub extern "C" fn zr_tuple(x: u32) -> u32 {
    abi_llvm::call_t8(black_box(give_t8), x) ^ abi_llvm::call_t16(black_box(give_t16), x) << 8
}

/// The same definitions called directly by this crate: both sides of each
/// call follow the one declaration.
#[no_mangle]
pub extern "C" fn zr_local(x: u32) -> u32 {
    let a = give_nz8(black_box(x)).map_or(1000, |v| v.get() as u32);
    let b = give_e8(black_box(x)).map_or(7, |e| e as u32);
    let c = give_t16(black_box(x)).0 as u32;
    let d = give_nzi8(black_box(x)).map_or(-1000, |v| v.get() as i32) as u32;
    a ^ b << 10 ^ c << 13 ^ d.rotate_left(3)
}

// ---- zp_*: LLVM passes an extended argument to this crate ----------------------

extern "C" fn read_nz8(v: Option<NonZeroU8>) -> u32 {
    v.map_or(1000, |v| v.get() as u32 * 3)
}

#[no_mangle]
pub extern "C" fn zp_nz8(x: u32) -> u32 {
    abi_llvm::pass_nz8(black_box(read_nz8), x)
}

// ---- cw_*: one-field 128-bit aggregates ----------------------------------------

fn fold(x: u128) -> u64 {
    (x >> 64) as u64 ^ (x as u64).rotate_left(1)
}

#[inline(never)]
extern "C" fn own_ccu(a: CU, k: u32) -> CU {
    CU {
        v: a.v.wrapping_mul(k as i128 | 1) ^ 0x1234_5678_9abc,
    }
}

#[no_mangle]
pub extern "C" fn cw_direct(a: u64, b: u32) -> u64 {
    fold(
        abi_llvm::ccu(
            CU {
                v: (a as i128) << 70 | b as i128,
            },
            b,
        )
        .v as u128,
    )
}

#[no_mangle]
pub extern "C" fn cw_three(a: u64, b: u32) -> u64 {
    let r = abi_llvm::ccw(
        b,
        CW {
            v: (a as u128) << 64 | b as u128,
        },
        CW { v: !(a as u128) },
    );
    fold(r.v)
}

#[no_mangle]
pub extern "C" fn cw_llvm_calls(a: u64, b: u32) -> u64 {
    fold(abi_llvm::via_ccu(black_box(own_ccu), (a as i128) << 63 | b as i128, b) as u128)
}

#[no_mangle]
pub extern "C" fn cw_ptr(a: u64, b: u32) -> u64 {
    let f: extern "C" fn(CU, u32) -> CU = black_box(abi_llvm::ccu);
    let g: extern "C" fn(CU, u32) -> CU = black_box(own_ccu);
    fold(f(CU { v: a as i128 - 7 }, b).v as u128) ^ fold(g(CU { v: -(a as i128) }, b).v as u128)
}

// ---- rc_*: retained-address chains -----------------------------------------------

static mut KEPT: *mut u32 = core::ptr::null_mut();

trait Step {
    fn go(p: &mut u32, k: u32) -> u32;
}

struct Leaf;

struct S<X>(X);

impl Step for Leaf {
    #[inline(never)]
    fn go(p: &mut u32, k: u32) -> u32 {
        unsafe { KEPT = p };
        *p ^ k
    }
}

impl<X: Step> Step for S<X> {
    #[inline(never)]
    fn go(p: &mut u32, k: u32) -> u32 {
        let mut t = *p ^ k;
        let r = X::go(&mut t, k.wrapping_add(1));
        *p = t;
        r
    }
}

type X2<X> = S<S<X>>;
type X4<X> = X2<X2<X>>;
type X8<X> = X4<X4<X>>;
type X16<X> = X8<X8<X>>;
type X32<X> = X16<X16<X>>;
type X64<X> = X32<X32<X>>;

#[inline(never)]
fn poke(v: u32) {
    unsafe {
        let p = KEPT;
        if !p.is_null() {
            *p = (*p).wrapping_mul(3) ^ v;
        }
    }
}

/// The leaf keeps the address of the deepest `t`; the write through it
/// after the chain returns is not observable here (that `t` is dead), but
/// every level keeps its own `t` in memory exactly as the summaries say.
#[no_mangle]
pub extern "C" fn rc_chain(x: u32, k: u32) -> u32 {
    let mut a = x;
    let r = <X64<Leaf>>::go(&mut a, k);
    unsafe { KEPT = &mut a };
    poke(r);
    unsafe { KEPT = core::ptr::null_mut() };
    a ^ r.rotate_left(9)
}

#[inline(never)]
fn ping(p: &mut u32, n: u32) -> u32 {
    if n == 0 {
        unsafe { KEPT = p };
        return *p;
    }
    let mut t = *p ^ n;
    let r = pong(&mut t, n - 1);
    *p = p.wrapping_add(t);
    r
}

#[inline(never)]
fn pong(p: &mut u32, n: u32) -> u32 {
    let mut u = p.rotate_left(3);
    let r = ping(&mut u, n);
    *p ^= u;
    r.wrapping_add(1)
}

#[no_mangle]
pub extern "C" fn rc_mutual(x: u32, n: u32) -> u32 {
    let mut a = x;
    let r = ping(&mut a, n % 9);
    unsafe { KEPT = core::ptr::null_mut() };
    a ^ r << 3
}

// ---- ab_*: large arrays by reference -----------------------------------------------

#[inline(never)]
fn touch(a: &mut [u32; 4096], i: u32) {
    if let Some(e) = a.get_mut(i as usize % 4096) {
        *e = i;
    }
}

#[inline(never)]
fn read_big(a: &[u8; 65536], i: u32) -> u32 {
    a.get(i as usize % 65536).map_or(0, |v| *v as u32)
}

#[no_mangle]
pub extern "C" fn ab_mut(i: u32) -> u32 {
    let mut a = [0u32; 4096];
    touch(&mut a, i);
    let [first, .., last] = &a;
    first ^ last.rotate_left(3) ^ a.iter().fold(0u32, |s, v| s.wrapping_add(*v))
}

#[no_mangle]
pub extern "C" fn ab_shared(i: u32) -> u32 {
    let a = [7u8; 65536];
    read_big(&a, i) ^ read_big(&a, i.rotate_left(5))
}
