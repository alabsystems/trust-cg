// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Abort-built frames whose exception tables differ by call-site region.
//!
//! Under `panic=abort` every function here is `nounwind`. LLVM's call-site
//! table for such a function lists its invoke ranges plus a "keep unwinding"
//! entry for each region between them that holds a call it cannot prove
//! `nounwind` from the callee's declaration (any indirect call); a region of
//! direct `nounwind` calls only is a gap, where a phase-one search fails. The
//! foreign callback reaches each region through a nested abort-built callee
//! whose own termination pad is a cleanup, so the search continues into the
//! region under test.
#![no_std]
#![feature(core_intrinsics, thread_local)]
#![allow(internal_features)]

// The linked Rust panic runtime and allocator, as in the corpus.
extern crate std;
use std::boxed::Box;

unsafe extern "C" {
    fn terminate_region_record_drop(id: u64);
}
unsafe extern "C-unwind" {
    fn terminate_region_callback(id: u64);
}
// A Rust-ABI driver function: under `panic=abort` its declaration here is
// `nounwind`, so a call to it is a plain call, never an invoke.
unsafe extern "Rust" {
    fn terminate_region_rust_callback(id: u64);
    fn terminate_region_rust_callback_ret(id: u64) -> u64;
}

pub struct Guard(u64);

impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe {
            terminate_region_record_drop(self.0);
            terminate_region_callback(self.0);
        }
    }
}

pub trait Region {
    fn reach(&self, id: u64);
}

pub struct Direct;

impl Region for Direct {
    #[inline(never)]
    fn reach(&self, id: u64) {
        unsafe { terminate_region_callback(id) }
    }
}

pub struct GuardInBox(#[allow(dead_code)] Guard);

impl Region for GuardInBox {
    fn reach(&self, _id: u64) {}
}

/// The nested abort-built callee: a direct call to it is `nounwind`.
#[unsafe(no_mangle)]
#[inline(never)]
pub fn region_inner(id: u64) {
    unsafe { terminate_region_callback(id) }
}

/// The same callee through the C ABI, for an `extern "C"` function pointer.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn region_inner_c(id: u64) {
    unsafe { terminate_region_callback(id) }
}

/// A direct `nounwind` call after the invoke: the region is a gap.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_direct(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    region_inner(2);
    x
}

/// A Rust function-pointer call after the invoke: the region keeps unwinding.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_indirect(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let inner: fn(u64) = core::hint::black_box(region_inner as fn(u64));
    inner(2);
    x
}

/// A `&dyn` method call after the invoke: an indirect call.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_dyn(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let target: &dyn Region = core::hint::black_box(&Direct as &dyn Region);
    target.reach(2);
    x
}

/// An `extern "C"` function-pointer call after the invoke: still indirect,
/// though its call site cannot unwind by its ABI.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_c_pointer(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let inner: extern "C" fn(u64) = core::hint::black_box(region_inner_c as extern "C" fn(u64));
    inner(2);
    x
}

/// An indirect call before the first invoke: [start, invoke) keeps unwinding.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_indirect_first(x: u64) -> u64 {
    let inner: fn(u64) = core::hint::black_box(region_inner as fn(u64));
    inner(1);
    unsafe { terminate_region_callback(2) };
    x
}

/// Two guards around one foreign call: a nested panic in either cleanup Drop
/// reaches a region of direct `nounwind` calls only.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_two_guards(x: u64) -> u64 {
    let _first = Guard(1);
    let _second = Guard(2);
    unsafe { terminate_region_callback(10) };
    x
}

/// A guard per loop iteration: several invoke ranges, nested cleanup panics.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_loop(n: u64) -> u64 {
    let mut acc = 0;
    let mut i = 0;
    while i < n {
        let _guard = Guard(100 + i);
        unsafe { terminate_region_callback(20 + i) };
        acc += i;
        i += 1;
    }
    acc
}

/// A boxed trait object holding a guard: its cleanup runs drop glue.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_box_dyn_guard(x: u64) -> u64 {
    let _guard: Box<dyn Region> = Box::new(GuardInBox(Guard(3)));
    unsafe { terminate_region_callback(30) };
    x
}

/// A guard, then an indirect call after the invoke.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_guard_indirect(x: u64) -> u64 {
    let _guard = Guard(4);
    unsafe { terminate_region_callback(40) };
    let inner: fn(u64) = core::hint::black_box(region_inner as fn(u64));
    inner(41);
    x
}

/// A direct and an indirect call in one region: a panic through the DIRECT
/// `nounwind` call keeps unwinding too, because the region is covered.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_mixed(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    region_inner(2);
    let inner: fn(u64) = core::hint::black_box(region_inner as fn(u64));
    inner(3);
    x
}

/// Two invokes sharing one guard's cleanup, a direct `nounwind` call between
/// them. LLVM keeps the two invoke entries apart (each foreign call has its
/// own landing pad), so the call between them is a gap.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_between_invokes(x: u64) -> u64 {
    let _guard = Guard(5);
    unsafe { terminate_region_callback(50) };
    region_inner(51);
    unsafe { terminate_region_callback(52) };
    x
}

/// An indirect call between two invokes and a direct one after the second:
/// the decision is per region.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_per_region(x: u64) -> u64 {
    unsafe { terminate_region_callback(60) };
    let inner: fn(u64) = core::hint::black_box(region_inner as fn(u64));
    inner(61);
    unsafe { terminate_region_callback(62) };
    region_inner(63);
    x
}

static BYTES_A: [u8; 100] = [7; 100];
static BYTES_B: [u8; 100] = [7; 100];

/// A `memcmp` libcall (the `compare_bytes` intrinsic) and then a `nounwind`
/// driver Rust call, both after the invoke. rustc declares `memcmp` with no
/// attributes and LLVM infers `nounwind` for it only above O0, so at O0 the
/// region keeps unwinding (the driver catches the Rust callback's panic) and
/// at O1-O3 it is a gap (the search fails).
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_memcmp(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let a: &[u8; 100] = core::hint::black_box(&BYTES_A);
    let b: &[u8; 100] = core::hint::black_box(&BYTES_B);
    let order = unsafe {
        core::intrinsics::compare_bytes(a.as_ptr(), b.as_ptr(), core::hint::black_box(100usize))
    };
    unsafe { terminate_region_rust_callback(2) };
    core::hint::black_box(order);
    x
}

// The frames below hold, after the invoke, one operation the backend lowers to
// a call it creates itself (a runtime helper, a libm or compiler-rt routine, a
// memory libcall) and then the `nounwind` driver Rust callback, whose panic is
// the one under test. LLVM lowers the same operation on its own terms: where it
// expands, folds or inlines it the region is a gap (the search fails), where it
// emits a libcall that may unwind the region is covered (the driver catches).

/// `[0u8; 64]`: a `memset` call under LLVM at O0, expanded inline at O1-O3.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_array_fill(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let bytes = [0u8; 64];
    let bytes: &[u8; 64] = core::hint::black_box(&bytes);
    unsafe { terminate_region_rust_callback(2) };
    x + u64::from(bytes[3])
}

/// `[7u8; 1024]`: a `memset` call under LLVM at every level.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_array_fill_large(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let bytes = [7u8; 1024];
    let bytes: &[u8; 1024] = core::hint::black_box(&bytes);
    unsafe { terminate_region_rust_callback(2) };
    x + u64::from(bytes[3])
}

/// `write_bytes` of 64 bytes: a `memset` call under LLVM at O0, expanded inline
/// at O1-O3.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_memset(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let mut bytes = core::mem::MaybeUninit::<[u8; 64]>::uninit();
    let start = bytes.as_mut_ptr() as *mut u8;
    unsafe { core::intrinsics::write_bytes(start, 0xAB, 64) };
    let start = core::hint::black_box(start);
    unsafe { terminate_region_rust_callback(2) };
    x + u64::from(unsafe { *start.add(3) })
}

/// `mul_add`: `fmadd` under LLVM at every level.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_fma(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let product = core::intrinsics::fmaf64(
        core::hint::black_box(1.5),
        core::hint::black_box(2.5),
        core::hint::black_box(0.25),
    );
    unsafe { terminate_region_rust_callback(2) };
    x + product as u64
}

/// `powi` by a constant: a `__powidf2` call under LLVM at O0, multiplies at
/// O1-O3.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_powi(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let power = unsafe { core::intrinsics::powif64(core::hint::black_box(1.5), 3) };
    unsafe { terminate_region_rust_callback(2) };
    x + power as u64
}

/// `sin` of a constant: a `sin` call under LLVM at O0, folded at O1-O3.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_sin_constant(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let sine = unsafe { core::intrinsics::sinf64(2.0) };
    unsafe { terminate_region_rust_callback(2) };
    x + core::hint::black_box(sine) as u64
}

/// `sin` of a runtime value: a `sin` call under LLVM at every level.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_sin_runtime(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let sine = unsafe { core::intrinsics::sinf64(core::hint::black_box(2.0)) };
    unsafe { terminate_region_rust_callback(2) };
    x + core::hint::black_box(sine) as u64
}

/// `i128::checked_mul`: multiply-high instructions under LLVM at every level
/// (the backend's own expansion divides).
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_i128_checked_mul(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let a = core::hint::black_box(0x1234_5678_9abc_def0_1122_i128);
    let b = core::hint::black_box(0x77_0000_0003_i128);
    let product = a.checked_mul(b).map_or(9, |product| product as u64);
    unsafe { terminate_region_rust_callback(2) };
    x + (product & 0xff)
}

/// `i128` division of two values LLVM cannot see, whose quotient a
/// `black_box` reads: a `__divti3` call under LLVM at every level.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_i128_div(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let a = core::hint::black_box(0x1234_5678_9abc_def0_1122_i128);
    let b = core::hint::black_box(0x77_0000_0003_i128);
    let quotient = a / b;
    unsafe { terminate_region_rust_callback(2) };
    x + (core::hint::black_box(quotient) as u64 & 0xff)
}

/// `u128` division by a literal: a `__udivti3` call under LLVM at O0, expanded
/// into multiplies at O1-O3.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_u128_div_literal(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let wide = (u128::from(core::hint::black_box(x)) << 70) | 0x1234_5678;
    let quotient = (wide / 3) as u64;
    unsafe { terminate_region_rust_callback(2) };
    x ^ quotient
}

/// A `u128` division of two zero-extended `u64` values: a `__udivti3` call
/// under LLVM at O0, one 64-bit `udiv` at O1-O3.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_u128_narrow_div(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let dividend = u128::from(core::hint::black_box(x));
    let quotient = dividend / u128::from(core::hint::black_box(3u64));
    unsafe { terminate_region_rust_callback(2) };
    x ^ quotient as u64
}

/// An `f64` -> `i128` conversion nothing reads: deleted under LLVM at every
/// level, O0 included.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_dead_f64_to_i128(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let _unused = core::hint::black_box(2.5f64) as i128;
    unsafe { terminate_region_rust_callback(2) };
    x
}

/// `[5u8; 2048]` read at four constant indices: a `memset` call under LLVM at
/// O0, folded away at O1-O3.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_fill_folded(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let bytes = [5u8; 2048];
    let head: u64 = bytes[..4].iter().map(|&byte| u64::from(byte)).sum();
    unsafe { terminate_region_rust_callback(2) };
    x + head
}

pub fn region_two() -> f64 {
    2.0
}

/// `sin` of a constant LLVM derives through a helper: a `sin` call under LLVM
/// at O0, folded at O1-O3.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_sin_derived(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let sine = unsafe { core::intrinsics::sinf64(region_two()) };
    unsafe { terminate_region_rust_callback(2) };
    x + core::hint::black_box(sine) as u64
}

#[thread_local]
static mut REGION_TLS: u64 = 11;

/// A thread-local read of a value nothing writes: the TLV descriptor's thunk
/// call under LLVM at O0 (an indirect call: covered), folded to the constant
/// at O1-O3 (a gap).
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_tls_constant(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let value = unsafe { REGION_TLS };
    unsafe { terminate_region_rust_callback(2) };
    x ^ value
}

#[inline(never)]
pub fn region_nounwind_target(id: u64) {
    unsafe { terminate_region_rust_callback(id) }
}

/// A call through a local `fn` pointer holding a fn item: a direct call to
/// the `nounwind` item under LLVM at every level.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_fn_pointer_local(x: u64) -> u64 {
    let target: fn(u64) = region_nounwind_target;
    unsafe { terminate_region_callback(1) };
    target(2);
    x
}

pub struct Known;

impl Region for Known {
    #[inline(never)]
    fn reach(&self, id: u64) {
        unsafe { terminate_region_rust_callback(id) }
    }
}

/// A `&dyn` method call on an object this frame built from a known type: an
/// indirect call under LLVM at O0, the devirtualized direct `nounwind` call at
/// O1-O3.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_dyn_known(x: u64) -> u64 {
    let known = Known;
    let target: &dyn Region = &known;
    unsafe { terminate_region_callback(1) };
    target.reach(2);
    x
}

/// A call through a `Box<dyn Fn>` this frame built from a fn item: a direct
/// `nounwind` call under LLVM at every level (`<Box<F> as Fn>::call` at O0,
/// the item at O1-O3).
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_box_dyn_fn(x: u64) -> u64 {
    let target: Box<dyn Fn(u64)> = Box::new(region_nounwind_target);
    unsafe { terminate_region_callback(1) };
    target(2);
    x
}

pub fn region_wrapper(id: u64) {
    unsafe { terminate_region_callback(id) }
}

/// A `nounwind` call, then a small local function whose foreign call has a
/// terminate pad. This frame has no foreign edge of its own: at O0 it has no
/// table and the search continues past it; at O1-O3 LLVM inlines the function,
/// the frame gets that pad's table, and the first call's region is a gap.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_inlined_pad(x: u64) -> u64 {
    unsafe { terminate_region_rust_callback(1) };
    region_wrapper(2);
    x
}

/// A call through a `Box<dyn Fn>` whose vtable LLVM cannot see: a direct
/// `nounwind` call to `<Box<F> as Fn>::call` under LLVM at O0 (a gap), the
/// inlined indirect call at O1-O3 (covered).
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_box_dyn_opaque(x: u64) -> u64 {
    let target: Box<dyn Fn(u64)> = core::hint::black_box(Box::new(region_nounwind_target));
    unsafe { terminate_region_callback(1) };
    target(2);
    x
}

static REGION_TARGET: fn(u64) = region_nounwind_target;

/// A call through an immutable `static` `fn` pointer: a direct call to the
/// `nounwind` item under LLVM at every level.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_fn_pointer_static(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    REGION_TARGET(2);
    x
}

static REGION_TABLE: [fn(u64); 2] = [region_inner, region_nounwind_target];

/// A call through an element of an immutable `static` table of `fn`
/// pointers: an indirect call under LLVM at O0, the folded direct call to the
/// `nounwind` item at O1-O3.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_fn_pointer_table(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    REGION_TABLE[1](2);
    x
}

/// A call through a `fn` pointer coerced from a non-capturing closure: a
/// direct call to the closure's `nounwind` `call_once` shim under LLVM at
/// every level.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_fn_pointer_closure(x: u64) -> u64 {
    let target: fn(u64) = |id| unsafe { terminate_region_rust_callback(id) };
    unsafe { terminate_region_callback(1) };
    target(2);
    x
}

/// `rotate_left` (the backend's slice-reverse helper): no libcall under LLVM.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_rotate(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let mut bytes = [1u8, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];
    core::hint::black_box(&mut bytes).rotate_left(5);
    unsafe { terminate_region_rust_callback(2) };
    x + u64::from(core::hint::black_box(&bytes)[0])
}

/// `print!` (a decoded `print!` calls std's own `_print` here too):
/// `std::io::_print`, a `nounwind` Rust-ABI call at every level.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_print(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    std::print!("REGION PRINT\n");
    unsafe { terminate_region_rust_callback(2) };
    x
}

/// The frame's last call returns its result: LLVM keeps `bl` (the
/// `black_box` alloca escapes, so the call is not marked `tail`) and the
/// region is a gap. A tail branch would skip this frame's table.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_tail(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    unsafe { terminate_region_rust_callback_ret(core::hint::black_box(x) - 3) }
}

// Review rows (2026-10-10): what the frame states about a callee must hold on
// every path, and only operations LLVM cannot fold keep a libcall.

/// The target a caller passes: its callback id is `id + 10`, so a call that
/// reaches another target is visible in the trace.
#[inline(never)]
pub fn region_kept_target(id: u64) {
    unsafe { terminate_region_rust_callback(id + 10) }
}

pub struct KeptRegion;

impl Region for KeptRegion {
    #[inline(never)]
    fn reach(&self, id: u64) {
        unsafe { terminate_region_rust_callback(id + 10) }
    }
}

/// A `fn` pointer parameter the frame reassigns on one path only: on the
/// path that keeps the caller's value the call is not the reassigned item's.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_fn_pointer_param_frame(
    mut target: fn(u64),
    replace: bool,
    x: u64,
) -> u64 {
    if replace {
        target = region_nounwind_target;
    }
    unsafe { terminate_region_callback(1) };
    target(2);
    x
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_fn_pointer_param(x: u64) -> u64 {
    region_fn_pointer_param_frame(
        core::hint::black_box(region_kept_target as fn(u64)),
        core::hint::black_box(false),
        x,
    )
}

/// The same with a non-capturing closure as the reassigned value.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_closure_param_frame(
    mut target: fn(u64),
    replace: bool,
    x: u64,
) -> u64 {
    if replace {
        target = |id| unsafe { terminate_region_rust_callback(id) };
    }
    unsafe { terminate_region_callback(1) };
    target(2);
    x
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_closure_param(x: u64) -> u64 {
    region_closure_param_frame(
        core::hint::black_box(region_kept_target as fn(u64)),
        core::hint::black_box(false),
        x,
    )
}

/// A `&dyn` parameter reassigned to a known object on one path only.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_dyn_param_frame(
    mut target: &dyn Region,
    replace: bool,
    x: u64,
) -> u64 {
    if replace {
        target = &Known;
    }
    unsafe { terminate_region_callback(1) };
    target.reach(2);
    x
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_dyn_param(x: u64) -> u64 {
    let kept = KeptRegion;
    region_dyn_param_frame(
        core::hint::black_box(&kept as &dyn Region),
        core::hint::black_box(false),
        x,
    )
}

/// A `Box<dyn Fn>` parameter replaced by a box of a fn item on one path only.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_box_dyn_param_frame(
    mut target: Box<dyn Fn(u64)>,
    replace: bool,
    x: u64,
) -> u64 {
    if replace {
        target = Box::new(region_nounwind_target);
    }
    unsafe { terminate_region_callback(1) };
    target(2);
    x
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_box_dyn_param(x: u64) -> u64 {
    region_box_dyn_param_frame(
        core::hint::black_box(Box::new(region_kept_target) as Box<dyn Fn(u64)>),
        core::hint::black_box(false),
        x,
    )
}

/// A closure `fn` pointer the frame overwrites through `&raw const`: the call
/// reaches the stored value, not the closure the local was built from.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_closure_raw_written(x: u64) -> u64 {
    #[allow(unused_mut)]
    let mut target: fn(u64) = |id| unsafe { terminate_region_rust_callback(id) };
    let written = core::hint::black_box((&raw const target).cast_mut());
    unsafe { written.write(region_kept_target) };
    unsafe { terminate_region_callback(1) };
    target(2);
    x
}

pub trait PinnedRegion {
    fn reach_pinned(self: core::pin::Pin<&Self>, id: u64);
}

pub struct PinnedKnown;

impl PinnedRegion for PinnedKnown {
    #[inline(never)]
    fn reach_pinned(self: core::pin::Pin<&Self>, id: u64) {
        unsafe { terminate_region_rust_callback(id) }
    }
}

impl PinnedRegion for &PinnedKnown {
    #[inline(never)]
    fn reach_pinned(self: core::pin::Pin<&Self>, id: u64) {
        unsafe { terminate_region_rust_callback(id + 10) }
    }
}

/// A `Pin<&dyn>` method call on an object this frame built: the callee is
/// `PinnedKnown`'s method, never `&PinnedKnown`'s (`Pin<P>` holds the
/// pointer `P`; its first type argument is not the pointee).
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_pin_dyn(x: u64) -> u64 {
    let known = PinnedKnown;
    let concrete: core::pin::Pin<&PinnedKnown> = core::pin::Pin::new(&known);
    let pinned: core::pin::Pin<&dyn PinnedRegion> = concrete;
    unsafe { terminate_region_callback(1) };
    pinned.reach_pinned(2);
    x
}

/// A `u128` division of two constants: LLVM's IRBuilder folds it as it builds
/// the IR, at O0 too, so there is no libcall at any level.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_u128_const_div(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let limit = u128::MAX / 10;
    unsafe { terminate_region_rust_callback(2) };
    x ^ limit as u64
}

/// An `f64` remainder of two constants: folded the same way (no `fmod`).
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_f64_const_rem(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let rem = 7.5f64 % 2.0;
    unsafe { terminate_region_rust_callback(2) };
    x + rem as u64
}

/// One opaque value divided by itself: a `__udivti3` call at O0, folded to 1
/// by LLVM's InstSimplify at O1-O3 although the value is unknown.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_u128_self_div(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let a = core::hint::black_box((u128::from(x) << 70) | 3);
    let quotient = a / a;
    core::hint::black_box(quotient);
    unsafe { terminate_region_rust_callback(2) };
    x
}

/// A `u128` from an `#[inline(always)]` conversion of a constant, divided by a
/// constant: LLVM's O0 AlwaysInliner inlines the conversion and the division
/// folds, so there is no libcall at any level.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_u128_from_const_div(x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let a = u128::from(10u64);
    let quotient = a / 3;
    unsafe { terminate_region_rust_callback(2) };
    x ^ quotient as u64
}

/// A slice's length from an array unsized in the frame: the metadata is the
/// array's static length, so the division folds at O0 too.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_slice_len_div_frame(array: &[u8; 3], x: u64) -> u64 {
    unsafe { terminate_region_callback(1) };
    let slice: &[u8] = array;
    let quotient = slice.len() as u128 / 3;
    unsafe { terminate_region_rust_callback(2) };
    x ^ quotient as u64
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_slice_len_div(x: u64) -> u64 {
    let array = [1u8, 2, 3];
    region_slice_len_div_frame(core::hint::black_box(&array), x)
}

/// A `fn` pointer field the frame overwrites through `&raw const` of the
/// field: the call reaches the stored value.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn region_field_raw_written(x: u64) -> u64 {
    #[allow(unused_mut)]
    let mut pair: (fn(u64), u64) = (region_nounwind_target as fn(u64), x);
    let written = core::hint::black_box((&raw const pair.0).cast_mut());
    unsafe { written.write(region_kept_target) };
    unsafe { terminate_region_callback(1) };
    (pair.0)(2);
    pair.1
}
