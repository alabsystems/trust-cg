// wasm32 execution-differential corpus: locals whose address a callee may
// keep, and the loop-header and constant shapes lowered with them.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// * `ra_*`: a local's address escapes to code that KEEPS it past the call
//   that received it: an out-parameter, a static, a returned raw pointer or
//   integer, an `AtomicPtr`, a trait object, a function pointer, a closure,
//   an integer an address-taking helper wrote into a static, a union. A later
//   write through the kept address (in straight-line code, in a loop whose
//   header carries a counter, in a loop whose header carries nothing, through
//   `copy_nonoverlapping`, through a helper taking the address as an integer)
//   must be seen by the next direct read of the local. `ra_shared_kept`
//   keeps a SHARED borrow and reads it back while the local is unchanged.
// * `rp_*`: a POINTER or reference local whose own address is kept, so a
//   callee may retarget or advance it (an opaque fn-pointer callee, a static
//   keeper, an entry argument). Every later deref, reborrow, field access,
//   index and whole-struct copy through it must use its current value.
// * `hd_*`: loop headers that carry no scalar: a store through an argument
//   reassigned before the loop, and a write-only cursor pointer reassigned
//   inside the loop.
// * `ce_*`: a fieldless enum in memory, stored through a pointer and written
//   by a variant aggregate after its address was kept.
// * `fc_*`: constants of single-float-leaf wrappers (`struct C(f32)`,
//   `Cell<f64>`, a one-variant enum, a signaling-NaN newtype) passed by
//   reference and by value.
//
// wasm32-differential-flags: -Copt-level=1
// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=s

#![no_std]

use core::cell::Cell;
use core::ptr::{self, NonNull};
use core::sync::atomic::{AtomicPtr, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

// ---------------------------------------------------------------- ra_*

#[derive(Clone, Copy)]
struct P {
    a: u32,
    b: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct T {
    a: u32,
    b: u32,
}

static mut KEPT_U32: *mut u32 = ptr::null_mut();
static mut KEPT_ARR: *mut u32 = ptr::null_mut();
static mut KEPT_P: *mut P = ptr::null_mut();
static mut KEPT_ADDR: usize = 0;
static mut KEPT_SHARED: *const u32 = ptr::null();
static KEPT_ATOMIC: AtomicPtr<u32> = AtomicPtr::new(ptr::null_mut());

#[inline(never)]
fn stash_arr(a: &mut [u32; 4], out: &mut *mut u32) {
    *out = a as *mut [u32; 4] as *mut u32;
}

#[inline(never)]
fn stash_u32(a: &mut u32, out: &mut *mut u32) {
    *out = a;
}

#[inline(never)]
fn keep_u32(a: &mut u32) {
    unsafe { KEPT_U32 = a }
}

#[inline(never)]
fn poke(v: u32) {
    unsafe { *KEPT_U32 = (*KEPT_U32).wrapping_mul(3) ^ v }
}

#[inline(never)]
fn keep_arr(a: &mut [u32; 4]) {
    unsafe { KEPT_ARR = a as *mut [u32; 4] as *mut u32 }
}

#[inline(never)]
fn addr_of_arr(a: &mut [u32; 4]) -> usize {
    a as *mut [u32; 4] as usize
}

#[inline(never)]
fn addr_of_u32(a: &mut u32) -> usize {
    a as *mut u32 as usize
}

#[inline(never)]
fn stash_p(p: &mut P, out: &mut *mut P) {
    *out = p;
}

#[inline(never)]
fn keep_p(p: &mut P) {
    unsafe { KEPT_P = p }
}

#[inline(never)]
fn keep_t_addr(t: &mut T) {
    unsafe { KEPT_ADDR = t as *mut T as usize }
}

/// Writes through an address it receives as an integer.
#[inline(never)]
fn write_at(addr: usize, v: u32) {
    unsafe { *(addr as *mut u32) = v }
}

#[inline(never)]
fn to_raw(x: &mut u32) -> *mut u32 {
    x
}

#[inline(never)]
fn keep_shared(x: &u32) {
    unsafe { KEPT_SHARED = x }
}

#[inline(never)]
fn read_shared() -> u32 {
    unsafe { *KEPT_SHARED }
}

#[inline(never)]
fn atomic_keep_bump(x: &mut u32) -> u32 {
    KEPT_ATOMIC.store(x as *mut u32, Ordering::Release);
    let q = KEPT_ATOMIC.load(Ordering::Acquire);
    unsafe {
        *q = (*q).wrapping_add(5);
        *q
    }
}

/// Writes through the address `atomic_keep_bump` left in `KEPT_ATOMIC`, after
/// that call returned.
#[inline(never)]
fn atomic_poke(v: u32) {
    let q = KEPT_ATOMIC.load(Ordering::Acquire);
    unsafe { *q = (*q).wrapping_mul(3) ^ v }
}

trait Keeper {
    fn keep(&self, p: &mut u32);
}

struct StaticKeeper;

impl Keeper for StaticKeeper {
    #[inline(never)]
    fn keep(&self, p: &mut u32) {
        unsafe { KEPT_U32 = p }
    }
}

#[inline(never)]
fn keep_dyn(k: &dyn Keeper, p: &mut u32) {
    k.keep(p)
}

#[inline(never)]
fn apply<F: FnMut(&mut u32)>(mut f: F, p: &mut u32) {
    f(p)
}

#[derive(Clone, Copy)]
union Word {
    int: usize,
    ptr: *mut u32,
}

#[inline(never)]
fn put_word(w: Word, v: u32) {
    unsafe { *w.ptr = v }
}

#[no_mangle]
pub extern "C" fn ra_out_param_loop(x: u32) -> u32 {
    let mut a = [0u32; 4];
    let mut q = ptr::null_mut();
    stash_arr(&mut a, &mut q);
    for i in 0..4usize {
        unsafe { *q.add(i) = x ^ (i as u32) }
    }
    a[1].wrapping_add(a[3])
}

#[no_mangle]
pub extern "C" fn ra_static_array(x: u32) -> u32 {
    let mut a = [0u32; 4];
    keep_arr(&mut a);
    for i in 0..4usize {
        unsafe { *KEPT_ARR.add(i) = x ^ (i as u32) }
    }
    a[1].wrapping_add(a[3])
}

#[no_mangle]
pub extern "C" fn ra_returned_usize_loop(x: u32) -> u32 {
    let mut a = [0u32; 4];
    let p = addr_of_arr(&mut a) as *mut u32;
    let mut s = 0u32;
    let mut i = 0usize;
    while i < 4 {
        unsafe { *p.add(i) = x ^ (i as u32) }
        s = s.wrapping_add(i as u32);
        i += 1;
    }
    a[1].wrapping_add(a[3]) ^ s
}

#[no_mangle]
pub extern "C" fn ra_scalar_out_param(x: u32) -> u32 {
    let mut a = 0u32;
    let mut q = ptr::null_mut();
    stash_u32(&mut a, &mut q);
    unsafe { *q = x }
    a
}

#[no_mangle]
pub extern "C" fn ra_scalar_out_param_loop(x: u32) -> u32 {
    let mut a = 0u32;
    let mut q = ptr::null_mut();
    stash_u32(&mut a, &mut q);
    for k in 0..4u32 {
        unsafe { *q = (*q).wrapping_mul(3) ^ x.wrapping_add(k) }
    }
    a
}

#[no_mangle]
pub extern "C" fn ra_static_poke(x: u32) -> u32 {
    let mut a = 1u32;
    keep_u32(&mut a);
    poke(x);
    a
}

#[no_mangle]
pub extern "C" fn ra_static_poke_loop(x: u32) -> u32 {
    let mut a = 1u32;
    keep_u32(&mut a);
    for k in 0..4u32 {
        poke(x.wrapping_add(k));
    }
    a
}

#[no_mangle]
pub extern "C" fn ra_returned_usize_scalar(x: u32) -> u32 {
    let mut a = 1u32;
    let p = addr_of_u32(&mut a);
    for k in 0..4u32 {
        unsafe {
            let q = p as *mut u32;
            *q = (*q).wrapping_mul(3) ^ x.wrapping_add(k);
        }
    }
    a
}

#[no_mangle]
pub extern "C" fn ra_struct_out_param_loop(x: u32) -> u32 {
    let mut p = P { a: 0, b: 7 };
    let mut q = ptr::null_mut();
    stash_p(&mut p, &mut q);
    for k in 0..4u32 {
        unsafe { (*q).a ^= x.wrapping_add(k) }
    }
    p.a.wrapping_mul(3) ^ p.b
}

#[no_mangle]
pub extern "C" fn ra_int_helper_loop(x: u32, y: u32) -> u32 {
    let mut t = T { a: x, b: y };
    keep_t_addr(&mut t);
    for _ in 0..3 {
        write_at(unsafe { KEPT_ADDR }, y.wrapping_add(1));
    }
    t.a.wrapping_mul(7) ^ t.b
}

#[no_mangle]
pub extern "C" fn ra_int_helper_straight(x: u32, y: u32) -> u32 {
    let mut s = x;
    let a = addr_of_u32(&mut s);
    write_at(a, y ^ 3);
    s
}

#[no_mangle]
pub extern "C" fn ra_union_word(x: u32, y: u32) -> u32 {
    let mut t = T { a: x, b: y };
    keep_t_addr(&mut t);
    for _ in 0..3 {
        put_word(
            Word {
                int: unsafe { KEPT_ADDR },
            },
            y ^ 5,
        );
    }
    t.a ^ t.b.wrapping_mul(3)
}

#[no_mangle]
pub extern "C" fn ra_copy_into_kept(x: u32, y: u32) -> u32 {
    let mut p = P { a: x, b: y };
    keep_p(&mut p);
    let src = [P { a: 1, b: 2 }, P { a: y, b: x }];
    let mut k = 0u32;
    for v in src.iter() {
        unsafe { ptr::copy_nonoverlapping(v, KEPT_P, 1) }
        k += 1;
    }
    p.a ^ p.b.wrapping_mul(3) ^ k
}

#[no_mangle]
pub extern "C" fn ra_write_into_kept_straight(x: u32, y: u32) -> u32 {
    let mut p = P { a: x, b: y };
    keep_p(&mut p);
    unsafe { KEPT_P.write(P { a: y ^ 9, b: x ^ 4 }) }
    p.a ^ p.b.wrapping_mul(3)
}

#[no_mangle]
pub extern "C" fn ra_returned_raw(a: u32) -> u32 {
    let mut x = a;
    let p = to_raw(&mut x);
    unsafe { *p = 7 }
    x
}

#[no_mangle]
pub extern "C" fn ra_from_mut(a: u32) -> u32 {
    let mut x = a;
    let p = ptr::from_mut(&mut x);
    unsafe { p.write(a ^ 0x55) }
    x
}

#[no_mangle]
pub extern "C" fn ra_nonnull_from(a: u32) -> u32 {
    let mut x = a;
    let p = NonNull::from(&mut x);
    unsafe { *p.as_ptr() = a.wrapping_add(11) }
    x
}

#[no_mangle]
pub extern "C" fn ra_atomic_ptr(a: u32) -> u32 {
    let mut x = a;
    let r = atomic_keep_bump(&mut x);
    atomic_poke(a ^ 0x5a);
    r ^ x.wrapping_mul(3)
}

#[no_mangle]
pub extern "C" fn ra_dyn_keeper(x: u32) -> u32 {
    let mut a = x;
    keep_dyn(&StaticKeeper, &mut a);
    poke(x ^ 1);
    a
}

#[no_mangle]
pub extern "C" fn ra_fn_pointer_keeper(x: u32) -> u32 {
    let keep: fn(&mut u32) = keep_u32;
    let mut a = x;
    keep(&mut a);
    poke(x ^ 2);
    a
}

#[no_mangle]
pub extern "C" fn ra_closure_keeper(x: u32) -> u32 {
    let mut a = x;
    apply(|p: &mut u32| unsafe { KEPT_U32 = p }, &mut a);
    for k in 0..2u32 {
        poke(x.wrapping_add(k));
    }
    a
}

#[no_mangle]
pub extern "C" fn ra_shared_kept(x: u32) -> u32 {
    let a = x.wrapping_mul(5);
    keep_shared(&a);
    read_shared() ^ a
}

// ---------------------------------------------------------------- rp_*

static mut KEPT_PP: *mut *mut u32 = ptr::null_mut();
static mut KEPT_PS: *mut *mut P = ptr::null_mut();
static mut KEPT_RA: *mut &'static mut [u32; 4] = ptr::null_mut();
static mut KEPT_RR: *mut &'static mut u32 = ptr::null_mut();
static mut OTHER: [u32; 8] = [0; 8];
static mut OTHER_P: P = P { a: 0, b: 0 };

#[inline(never)]
fn keep_pp(pp: &mut *mut u32) {
    unsafe { KEPT_PP = pp }
}

/// Points the kept pointer at `OTHER[i & 3]`.
#[inline(never)]
fn retarget(i: u32) {
    unsafe { *KEPT_PP = ptr::addr_of_mut!(OTHER[(i & 3) as usize]) }
}

/// Advances the kept pointer by one element.
#[inline(never)]
fn advance_kept_pointer() {
    unsafe { *KEPT_PP = (*KEPT_PP).add(1) }
}

#[inline(never)]
fn advance(pp: &mut *mut u32) {
    unsafe { *pp = pp.add(1) }
}

#[inline(never)]
fn bump(p: &mut u32, v: u32) {
    *p = p.wrapping_add(v)
}

#[inline(never)]
fn keep_ps(pp: &mut *mut P) {
    unsafe { KEPT_PS = pp }
}

#[inline(never)]
fn retarget_p() {
    unsafe { *KEPT_PS = ptr::addr_of_mut!(OTHER_P) }
}

#[inline(never)]
fn keep_ra(pp: &mut &mut [u32; 4]) {
    unsafe { KEPT_RA = pp as *mut &mut [u32; 4] as *mut &'static mut [u32; 4] }
}

#[inline(never)]
fn retarget_ra() {
    unsafe { *KEPT_RA = &mut *(ptr::addr_of_mut!(OTHER) as *mut [u32; 4]) }
}

#[inline(never)]
fn keep_rr(pp: &mut &mut u32) {
    unsafe { KEPT_RR = pp as *mut &mut u32 as *mut &'static mut u32 }
}

#[inline(never)]
fn retarget_rr() {
    unsafe { *KEPT_RR = &mut *ptr::addr_of_mut!(OTHER[5]) }
}

fn other_digest() -> u32 {
    let mut s = 0u32;
    for k in 0..8 {
        s = s.wrapping_mul(31).wrapping_add(unsafe { OTHER[k] });
    }
    s
}

fn reset_other() {
    for k in 0..8 {
        unsafe { OTHER[k] = (k as u32 + 1) * 10 }
    }
}

#[inline(never)]
fn store_through_kept_arg(mut p: *mut u32, v: u32) {
    keep_pp(&mut p);
    retarget(v);
    unsafe { *p = v }
}

#[inline(never)]
fn walk_kept_arg(mut p: *mut u32, n: u32) -> u32 {
    keep_pp(&mut p);
    let mut s = 0u32;
    let mut i = 0;
    while i < n {
        s = s.wrapping_mul(7).wrapping_add(unsafe { *p });
        advance_kept_pointer();
        i += 1;
    }
    s
}

#[inline(never)]
fn via_kept_ref(mut r: &mut u32, v: u32) -> u32 {
    keep_rr(&mut r);
    retarget_rr();
    *r = v;
    *r + 1
}

#[no_mangle]
pub extern "C" fn rp_fn_pointer_cursor(v: u32) -> u32 {
    let f: fn(&mut *mut u32) = core::hint::black_box(advance);
    let mut a = [1u32, 2, 3, 4];
    let mut p = a.as_mut_ptr();
    f(&mut p);
    unsafe { *p = v }
    a[0] ^ a[1].rotate_left(3) ^ a[2].rotate_left(9)
}

#[no_mangle]
pub extern "C" fn rp_reborrow(v: u32) -> u32 {
    reset_other();
    let mut a = [1u32, 2, 3, 4];
    let mut p = a.as_mut_ptr();
    keep_pp(&mut p);
    retarget(v);
    unsafe { bump(&mut *p, v) }
    a[0].wrapping_mul(7) ^ other_digest()
}

#[no_mangle]
pub extern "C" fn rp_read_modify_write(v: u32) -> u32 {
    reset_other();
    let mut a = [1u32, 2, 3, 4];
    let mut p = a.as_mut_ptr();
    keep_pp(&mut p);
    retarget(v);
    unsafe { *p = (*p).wrapping_mul(3).wrapping_add(v) }
    a[0] ^ other_digest()
}

#[no_mangle]
pub extern "C" fn rp_struct_fields(v: u32) -> u32 {
    let mut s = P { a: 1, b: 2 };
    unsafe { OTHER_P = P { a: 100, b: 200 } }
    let mut p: *mut P = &mut s;
    keep_ps(&mut p);
    if v & 1 == 1 {
        retarget_p();
    }
    let r = unsafe { (*p).a };
    unsafe { (*p).b = r.wrapping_add(v) }
    let copy = unsafe { *p };
    copy.a ^ copy.b.rotate_left(5) ^ s.b ^ unsafe { OTHER_P.b }.rotate_left(11)
}

#[no_mangle]
pub extern "C" fn rp_array_index(v: u32) -> u32 {
    reset_other();
    let mut arr = [1u32, 2, 3, 4];
    let mut r: &mut [u32; 4] = &mut arr;
    keep_ra(&mut r);
    if v & 4 == 4 {
        retarget_ra();
    }
    let i = (v & 3) as usize;
    r[i] = r[i].wrapping_add(v);
    r[i] ^ arr[i].rotate_left(7) ^ other_digest()
}

#[no_mangle]
pub extern "C" fn rp_cursor_loop(v: u32) -> u32 {
    let mut a = [0u32; 8];
    let mut p = a.as_mut_ptr();
    keep_pp(&mut p);
    let n = (v & 3) + 1;
    let mut i = 0;
    while i < n {
        unsafe { *p = v.wrapping_add(i) }
        advance_kept_pointer();
        i += 1;
    }
    let mut s = 0u32;
    for k in 0..8 {
        s = s.wrapping_mul(31).wrapping_add(a[k]);
    }
    s
}

#[no_mangle]
pub extern "C" fn rp_join(v: u32) -> u32 {
    reset_other();
    let mut a = [7u32, 8, 9, 10];
    let mut p = a.as_mut_ptr();
    keep_pp(&mut p);
    if v & 1 == 1 {
        retarget(v >> 1);
    } else {
        p = unsafe { p.add(2) };
    }
    let r = unsafe { *p };
    r.wrapping_add(a[2])
}

#[no_mangle]
pub extern "C" fn rp_entry_arg_store(v: u32) -> u32 {
    reset_other();
    let mut a = [1u32, 2, 3, 4];
    store_through_kept_arg(a.as_mut_ptr(), v);
    a[0].wrapping_mul(7) ^ other_digest()
}

#[no_mangle]
pub extern "C" fn rp_entry_arg_walk(v: u32) -> u32 {
    let mut a = [3u32, 5, 7, 11, 13, 17, 19, 23];
    walk_kept_arg(a.as_mut_ptr(), (v & 7) + 1)
}

#[no_mangle]
pub extern "C" fn rp_entry_arg_ref(v: u32) -> u32 {
    reset_other();
    let mut x = 9u32;
    let a = via_kept_ref(&mut x, v);
    a ^ x.wrapping_mul(3) ^ other_digest().wrapping_mul(11)
}

// ---------------------------------------------------------------- hd_*

#[inline(never)]
fn store_through_reassigned<'a>(mut p: &'a mut u32, q: &'a mut u32) {
    p = q;
    for k in 0..4 {
        *p = k;
    }
}

#[no_mangle]
pub extern "C" fn hd_reassigned_arg(x: u32) -> u32 {
    let mut a = x;
    let mut b = x ^ 0x55;
    store_through_reassigned(&mut a, &mut b);
    a.wrapping_mul(31) ^ b
}

#[inline(never)]
fn cursor_fill(a: &mut [u32; 4]) {
    let base = a.as_mut_ptr();
    let mut p = base;
    for k in 0..4usize {
        unsafe {
            *p = k as u32 + 1;
            p = base.add((k + 1) & 3);
        }
    }
}

#[no_mangle]
pub extern "C" fn hd_cursor(x: u32) -> u32 {
    let mut a = [x, x >> 3, x >> 5, x >> 7];
    cursor_fill(&mut a);
    a[0] ^ a[1] << 3 ^ a[2] << 6 ^ a[3] << 9
}

// ---------------------------------------------------------------- ce_*

#[derive(Clone, Copy, PartialEq)]
enum S3 {
    A,
    B,
    C,
}

#[repr(u8)]
#[derive(Clone, Copy)]
enum Tagged {
    Low = 7,
    High = 200,
}

static mut KEPT_S3: *mut S3 = ptr::null_mut();

#[inline(never)]
fn set_s3(p: *mut S3, n: u32) {
    if n == 1 {
        unsafe { *p = S3::B }
    }
}

#[inline(never)]
fn keep_s3(p: &mut S3) {
    unsafe { KEPT_S3 = p }
}

#[inline(never)]
fn advance_kept() {
    unsafe {
        *KEPT_S3 = match *KEPT_S3 {
            S3::A => S3::B,
            S3::B => S3::C,
            S3::C => S3::A,
        }
    }
}

#[no_mangle]
pub extern "C" fn ce_raw_ptr(n: u32) -> u32 {
    let mut s = S3::A;
    let p = &mut s as *mut S3;
    if n & 1 == 1 {
        unsafe { *p = S3::C }
    }
    match s {
        S3::A => 1,
        S3::B => 2,
        S3::C => 3,
    }
}

#[no_mangle]
pub extern "C" fn ce_callee_store(n: u32) -> u32 {
    let mut s = S3::A;
    set_s3(&mut s, n);
    s as u32
}

#[no_mangle]
pub extern "C" fn ce_kept_variant_write(n: u32) -> u32 {
    let mut s = S3::A;
    keep_s3(&mut s);
    if n & 1 == 1 {
        s = S3::C;
    }
    for _ in 0..(n & 3) {
        advance_kept();
    }
    s as u32 + if s == S3::B { 10 } else { 0 }
}

#[no_mangle]
pub extern "C" fn ce_repr_u8(n: u32) -> u32 {
    let mut t = Tagged::Low;
    let p = &mut t as *mut Tagged;
    if n > 3 {
        unsafe { *p = Tagged::High }
    }
    t as u8 as u32
}

// ---------------------------------------------------------------- fc_*

struct C32(f32);

struct Circle64 {
    r: f64,
}

enum OneF64 {
    Only(f64),
}

#[derive(Clone, Copy)]
struct Bits32(f32);

#[inline(never)]
fn get_c32(c: &C32) -> f32 {
    c.0
}

#[inline(never)]
fn get_cell(c: &Cell<f64>) -> f64 {
    c.get()
}

#[inline(never)]
fn area(c: &Circle64) -> f64 {
    c.r * 2.0
}

#[inline(never)]
fn make_one(flag: bool) -> OneF64 {
    if flag {
        OneF64::Only(-3.0)
    } else {
        OneF64::Only(0.5)
    }
}

#[inline(never)]
fn pick(flag: bool) -> Bits32 {
    if flag {
        Bits32(f32::from_bits(0x7fa0_0000))
    } else {
        Bits32(-2.5)
    }
}

#[no_mangle]
pub extern "C" fn fc_newtype_f32(x: f32) -> f32 {
    let c = C32(1.5);
    get_c32(&c) + x
}

#[no_mangle]
pub extern "C" fn fc_cell_f64(x: f64) -> f64 {
    let c = Cell::new(0.25f64);
    get_cell(&c) * x
}

#[no_mangle]
pub extern "C" fn fc_struct_f64(x: f64) -> f64 {
    let c = Circle64 { r: 1.5 };
    area(&c) + x
}

#[no_mangle]
pub extern "C" fn fc_enum_f64(x: f64) -> f64 {
    let OneF64::Only(v) = make_one(x < 1.0);
    v - x
}

#[no_mangle]
pub extern "C" fn fc_snan_newtype(n: u32) -> u32 {
    pick(n & 1 == 1).0.to_bits()
}
