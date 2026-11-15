// wasm32 execution-differential corpus: fn-pointer constants, statics that
// share one allocation, foreign statics, case-colliding item symbols,
// thread-locals, over-aligned statics, `clone_from` and multi-CGU copies.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// * `fp_*`: a `const` of `fn(..)` pointer type (plain, associated, `extern
//   "C"`, and a raw `*const ()`) used as a value and CALLED directly: the
//   constant is the function's code address, and a call through it is an
//   indirect call through that address.
// * `ns_*`: statics whose values point into ONE promoted allocation (`B` and
//   `C` are read out of `A`, and `AA`/`CC` one level deeper): the pointers
//   share provenance, so `offset_from` and pointer equality are defined. A
//   `const` pointing into such an allocation is in
//   `r4-bridge-statics-const-alloc.rs`.
// * `fs_*`: an immutable `extern`-block static (defined `#[no_mangle]` in
//   another module) read, address-taken and stored in a static initializer.
// * `cs_*`: item symbols differing only in letter case (`Table`/`TABLE`,
//   `static COUNTER`/`fn counter`), whose per-item objects must stay distinct
//   files on a case-insensitive filesystem.
// * `tl_*`: a `#[thread_local]` static read and written from two modules; a
//   wasm32 session without atomics has one thread.
// * `al_*`: 16-byte (`u128`, `i128`, `repr(align(16))`) and 64-byte aligned
//   statics, including one reached through another static's pointer.
// * `cf_*`: `Clone::clone_from` of a derived-`Clone` newtype around an array,
//   of a unit struct, and of structs whose scalar leaves are not their fields
//   (an array next to zero-sized fields, a nested tuple).
// * `ab_*`: Rust-ABI functions of this crate taking and returning values
//   rustc's wasm32 ABI passes through memory (`[u64; 1]`, a union): every
//   caller and body is this backend's.
// * `lc_*`: `#[inline(always)]` / `#[inline]` functions used from several
//   modules, which rustc copies CGU-private into every codegen unit that uses
//   them (the `-Ccodegen-units=16` configurations).
//
// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Ccodegen-units=16
// wasm32-differential-flags: -Copt-level=2 -Ccodegen-units=16

#![no_std]
#![allow(dead_code, non_upper_case_globals, static_mut_refs)]
#![feature(thread_local)]

use core::hint::black_box;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

// ---- fn-pointer constants ------------------------------------------------

#[inline(never)]
fn double(x: u32) -> u32 {
    x.wrapping_mul(2)
}

#[inline(never)]
fn triple(x: u32) -> u32 {
    x.wrapping_mul(3).wrapping_add(1)
}

extern "C" fn c_quad(x: u32) -> u32 {
    x.wrapping_mul(4) ^ 5
}

const F: fn(u32) -> u32 = double;
const CF: extern "C" fn(u32) -> u32 = c_quad;
const RAW: *const () = triple as *const ();

trait HasOp {
    const OP: fn(u32) -> u32;
}
struct Dbl;
struct Tpl;
impl HasOp for Dbl {
    const OP: fn(u32) -> u32 = double;
}
impl HasOp for Tpl {
    const OP: fn(u32) -> u32 = triple;
}

#[inline(never)]
fn via_assoc<O: HasOp>(x: u32) -> u32 {
    (O::OP)(x)
}

#[inline(never)]
fn apply(f: fn(u32) -> u32, x: u32) -> u32 {
    f(x)
}

#[inline(never)]
fn call_raw(p: *const (), x: u32) -> u32 {
    let f: fn(u32) -> u32 = unsafe { core::mem::transmute(p) };
    f(x)
}

#[no_mangle]
pub extern "C" fn fp_direct(x: u32) -> u32 {
    F(x) ^ CF(x).rotate_left(3) ^ (Dbl::OP)(x ^ 7)
}

#[no_mangle]
pub extern "C" fn fp_value(x: u32) -> u32 {
    apply(F, x) ^ black_box(F)(x ^ 1) ^ via_assoc::<Tpl>(x) ^ via_assoc::<Dbl>(x >> 3)
}

#[no_mangle]
pub extern "C" fn fp_raw(x: u32) -> u32 {
    call_raw(RAW, x) ^ call_raw(black_box(RAW), x >> 1)
}

#[no_mangle]
pub extern "C" fn fp_same(x: u32) -> u32 {
    let item: fn(u32) -> u32 = double;
    (black_box(F) as usize == black_box(item) as usize) as u32
        | ((black_box(RAW) as usize == (triple as fn(u32) -> u32) as usize) as u32) << 1
        | (x & 0)
}

// ---- statics sharing one allocation --------------------------------------

mod shared {
    pub static A: &[u32; 5] = &[10, 20, 30, 40, 50];
    pub static B: &u32 = &A[2];
    pub static C: &[u32; 5] = A;
    pub static AA: &&[u16; 3] = &&[7, 8, 9];
    pub static CC: &[u16; 3] = *AA;
}

#[no_mangle]
pub extern "C" fn ns_offset(i: u32) -> u32 {
    let off = unsafe { (shared::B as *const u32).offset_from(shared::A.as_ptr()) } as u32;
    off.wrapping_mul(1000)
        .wrapping_add(shared::A[(off as usize + i as usize) % 5])
}

#[no_mangle]
pub extern "C" fn ns_identity(i: u32) -> u32 {
    let same_a = core::ptr::eq(shared::A, shared::C) as u32;
    let walked = (shared::A.as_ptr().wrapping_add(2) == shared::B as *const u32) as u32;
    let same_aa = core::ptr::eq(*shared::AA, shared::CC) as u32;
    same_a | walked << 1 | same_aa << 2 | (shared::CC[(i % 3) as usize] as u32) << 4
}

// ---- foreign statics -----------------------------------------------------

mod defs {
    #[no_mangle]
    pub static TCG_R4_V: u32 = 41;
    #[no_mangle]
    pub static TCG_R4_T: [u16; 4] = [3, 30, 300, 3000];
}

mod decl {
    extern "C" {
        pub static TCG_R4_V: u32;
        pub static TCG_R4_T: [u16; 4];
    }
    pub static PV: &u32 = unsafe { &TCG_R4_V };
}

#[no_mangle]
pub extern "C" fn fs_read(i: u32) -> u32 {
    unsafe { decl::TCG_R4_V + decl::TCG_R4_T[(i % 4) as usize] as u32 }
}

#[no_mangle]
pub extern "C" fn fs_addr(i: u32) -> u32 {
    let p = unsafe { core::ptr::addr_of!(decl::TCG_R4_T) } as *const u16;
    let same = (unsafe { core::ptr::addr_of!(decl::TCG_R4_V) } == decl::PV as *const u32) as u32;
    unsafe { *p.add((i % 4) as usize) as u32 + *decl::PV + same * 100_000 }
}

// ---- case-colliding item symbols -----------------------------------------

mod cs {
    pub static Table: [u32; 2] = [1, 2];
    pub static TABLE: [u32; 2] = [30, 40];
    pub static mut COUNTER: u32 = 0;
    #[inline(never)]
    pub fn counter() -> u32 {
        unsafe {
            COUNTER = COUNTER.wrapping_add(1);
            COUNTER
        }
    }
}

#[no_mangle]
pub extern "C" fn cs_tables(i: u32) -> u32 {
    cs::Table[(i % 2) as usize] + cs::TABLE[(i % 2) as usize]
}

#[no_mangle]
pub extern "C" fn cs_counter(x: u32) -> u32 {
    cs::counter() ^ x
}

// ---- thread-locals -------------------------------------------------------

mod tl {
    #[thread_local]
    pub static mut TL: u32 = 7;
    #[thread_local]
    pub static TLC: core::cell::Cell<u64> = core::cell::Cell::new(3);
    #[inline(never)]
    pub fn bump(v: u32) -> u32 {
        unsafe {
            TL = TL.wrapping_mul(3) ^ v;
            TL
        }
    }
}

mod tl_reader {
    #[inline(never)]
    pub fn read() -> u32 {
        unsafe { super::tl::TL }
    }
}

#[no_mangle]
pub extern "C" fn tl_bump(v: u32) -> u32 {
    tl::bump(v) ^ tl_reader::read() << 1
}

#[no_mangle]
pub extern "C" fn tl_cell(v: u64) -> u64 {
    tl::TLC.set(tl::TLC.get().wrapping_mul(5) ^ v);
    tl::TLC.get()
}

// ---- over-aligned statics ------------------------------------------------

#[repr(C, align(16))]
pub struct A16(pub [u32; 4]);

#[repr(C, align(64))]
pub struct A64(pub u8, pub u32);

mod al {
    use super::{A16, A64};
    pub static BIG: u128 = 0x0123_4567_89ab_cdef_fedc_ba98_7654_3210;
    pub static WIDE: [i128; 2] = [-5, 1 << 100];
    pub static V16: A16 = A16([1, 2, 3, 4]);
    pub static mut M64: A64 = A64(7, 9);
    pub static R16: &A16 = &A16([5, 6, 7, 8]);
}

#[no_mangle]
pub extern "C" fn al_addresses(x: u32) -> u32 {
    let big = core::ptr::addr_of!(al::BIG) as usize % 16;
    let wide = core::ptr::addr_of!(al::WIDE) as usize % 16;
    let v16 = core::ptr::addr_of!(al::V16) as usize % 16;
    let m64 = unsafe { core::ptr::addr_of!(al::M64) } as usize % 64;
    let r16 = (al::R16 as *const A16) as usize % 16;
    (big | wide | v16 | m64 | r16) as u32 | (x & 0)
}

#[no_mangle]
pub extern "C" fn al_values(i: u32) -> u64 {
    let big = (al::BIG >> (i % 128)) as u64;
    let wide = (al::WIDE[(i % 2) as usize] >> (i % 101)) as u64;
    let lanes = al::V16.0[(i % 4) as usize] as u64 ^ (al::R16.0[(i % 4) as usize] as u64) << 8;
    let m64 = unsafe {
        al::M64.1 = al::M64.1.wrapping_add(i);
        al::M64.1 as u64 ^ al::M64.0 as u64
    };
    big ^ wide.rotate_left(17) ^ lanes ^ m64 << 40
}

// ---- clone_from ----------------------------------------------------------

#[derive(Clone, Copy)]
pub struct Arr(pub [u16; 7]);

#[derive(Clone, Copy)]
pub struct Zst;

#[derive(Clone)]
pub struct Two(pub u8, pub u64);

#[inline(never)]
fn clone_arr(a: &mut Arr, b: &Arr) {
    a.clone_from(b)
}

#[inline(never)]
fn clone_zst(a: &mut Zst, b: &Zst) {
    a.clone_from(b)
}

#[inline(never)]
fn clone_two(a: &mut Two, b: &Two) {
    a.clone_from(b)
}

#[no_mangle]
pub extern "C" fn cf_arr(x: u32, i: u32) -> u32 {
    let mut a = Arr([1; 7]);
    let b = Arr([x as u16, 2, 3, 4, 5, 6, (x >> 16) as u16]);
    clone_arr(&mut a, &b);
    let mut z = Zst;
    clone_zst(&mut z, &Zst);
    a.0[(i % 7) as usize] as u32
}

#[no_mangle]
pub extern "C" fn cf_two(x: u32) -> u64 {
    let mut a = Two(1, 2);
    clone_two(&mut a, &Two(x as u8, x as u64 * 3));
    a.0 as u64 ^ a.1
}

#[derive(Clone, Copy)]
pub struct ArrZst(pub [u8; 2], pub core::marker::PhantomData<u8>, pub u32);

#[derive(Clone, Copy)]
pub struct ArrUnit(pub [u16; 2], pub ());

#[derive(Clone, Copy)]
pub struct Units(pub u8, pub [u8; 2], pub (), pub ());

#[derive(Clone, Copy)]
pub struct Nested(pub (u8, u8), pub u16);

#[inline(never)]
fn clone_arr_zst(a: &mut ArrZst, b: &ArrZst) {
    a.clone_from(b)
}

#[inline(never)]
fn clone_arr_unit(a: &mut ArrUnit, b: &ArrUnit) {
    a.clone_from(b)
}

#[inline(never)]
fn clone_units(a: &mut Units, b: &Units) {
    a.clone_from(b)
}

#[inline(never)]
fn clone_nested(a: &mut Nested, b: &Nested) {
    a.clone_from(b)
}

#[no_mangle]
pub extern "C" fn cf_leaves(x: u32) -> u64 {
    let mut a = ArrZst([9, 9], core::marker::PhantomData, 9);
    clone_arr_zst(
        &mut a,
        &ArrZst(
            [x as u8, (x >> 8) as u8],
            core::marker::PhantomData,
            x.rotate_left(5),
        ),
    );
    let mut b = ArrUnit([9, 9], ());
    clone_arr_unit(&mut b, &ArrUnit([x as u16, (x >> 16) as u16], ()));
    let mut c = Units(9, [9, 9], (), ());
    clone_units(
        &mut c,
        &Units(x as u8, [(x >> 8) as u8, (x >> 16) as u8], (), ()),
    );
    let mut d = Nested((9, 9), 9);
    clone_nested(&mut d, &Nested((x as u8, (x >> 8) as u8), (x >> 16) as u16));
    let a_bits = a.0[0] as u64 | (a.0[1] as u64) << 8 | (a.2 as u64) << 16;
    let b_bits = b.0[0] as u64 | (b.0[1] as u64) << 16;
    let c_bits = c.0 as u64 | (c.1[0] as u64) << 8 | (c.1[1] as u64) << 16;
    let d_bits = d.0.0 as u64 | (d.0.1 as u64) << 8 | (d.1 as u64) << 16;
    a_bits ^ b_bits.rotate_left(11) ^ c_bits.rotate_left(23) ^ d_bits.rotate_left(37)
}

// ---- Rust-ABI by-memory values -------------------------------------------

#[derive(Clone, Copy)]
pub struct One(pub [u64; 1]);

#[derive(Clone, Copy)]
pub union Word {
    pub a: u64,
    pub b: [u8; 8],
}

#[inline(never)]
fn take_one(x: One, y: [f64; 1]) -> u64 {
    x.0[0] ^ y[0].to_bits()
}

#[inline(never)]
fn make_one(k: u64) -> One {
    One([k.rotate_left(3)])
}

#[inline(never)]
fn take_word(w: Word, i: u32) -> u64 {
    unsafe { w.a ^ w.b[(i % 8) as usize] as u64 }
}

#[no_mangle]
pub extern "C" fn ab_values(k: u64, i: u32) -> u64 {
    take_one(black_box(make_one(k)), [k as f64]) ^ take_word(black_box(Word { a: k }), i)
}

// ---- multi-CGU copies ----------------------------------------------------

#[inline(always)]
fn mix(x: u64) -> u64 {
    x.rotate_left(13) ^ x.wrapping_mul(0x9e37_79b9)
}

#[inline]
fn fold(x: u32) -> u32 {
    x.wrapping_add(0x55).rotate_right(3)
}

pub mod lc_a {
    #[inline(never)]
    pub fn f(x: u64) -> u64 {
        super::mix(x) ^ super::fold(x as u32) as u64
    }
}

pub mod lc_b {
    #[inline(never)]
    pub fn g(x: u64) -> u64 {
        super::mix(x ^ 1).rotate_left(5) ^ super::fold((x >> 7) as u32) as u64
    }
}

pub mod lc_c {
    #[inline(never)]
    pub fn h(x: u64) -> u64 {
        super::mix(x >> 3) ^ x.rotate_left(9)
    }
}

#[no_mangle]
pub extern "C" fn lc_mix(x: u64) -> u64 {
    lc_a::f(x) ^ lc_b::g(x) ^ lc_c::h(x)
}
