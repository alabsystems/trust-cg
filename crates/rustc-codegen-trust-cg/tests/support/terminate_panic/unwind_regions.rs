// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Unwind-built frames that call a Rust-defined `extern "C"` callee whose
//! panic reaches the caller (OD-NOUNWIND-CALLEE-EDGE-20261011).
//!
//! Under `panic=unwind` such a callee's own cleanup chain ends in
//! `terminate(abi)`, and the caller's call to it has no unwind edge in MIR
//! (`unwind unreachable`), so MIR runs the callee's cleanups and then aborts
//! with "panic in a function that cannot unwind". LLVM's binary does so only
//! where the unwinder's search phase passes the caller and every frame above
//! it: where the caller has no exception table, or its table covers the call
//! (a neighbouring call that may unwind, a merged range of same-pad invokes,
//! or an inlined callee). In a gap the search fails and the process aborts
//! ("failed to initiate panic, error 3") before any cleanup runs. The frames
//! below place the call in each of those positions; the controls call a callee
//! that may unwind from a region with no landing pad, where both binaries must
//! catch the panic.
#![no_std]
extern crate std;
use core::hint::black_box;

unsafe extern "C" {
    fn terminate_region_record_drop(id: u64);
    fn getpid() -> i32;
    fn qsort(
        base: *mut core::ffi::c_void,
        n: usize,
        width: usize,
        compar: extern "C" fn(*const core::ffi::c_void, *const core::ffi::c_void) -> i32,
    );
}
unsafe extern "C-unwind" {
    fn terminate_region_callback(id: u64);
}
unsafe extern "Rust" {
    fn terminate_region_rust_callback(id: u64);
}

pub struct Loud(u64);
impl Drop for Loud {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe { terminate_region_record_drop(self.0) }
    }
}

/// The Rust-defined `extern "C"` callee: its FnAbi cannot unwind.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn uw_c_callee(id: u64) {
    let _l = Loud(id);
    unsafe { terminate_region_callback(id) }
}

/// Control: the same body behind `extern "C-unwind"`.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_cu_callee(id: u64) {
    let _l = Loud(id);
    unsafe { terminate_region_callback(id) }
}

/// Control: the same body behind the Rust ABI.
#[unsafe(no_mangle)]
#[inline(never)]
pub fn uw_rust_callee(id: u64) {
    let _l = Loud(id);
    unsafe { terminate_region_callback(id) }
}

// (a) a caller with landing pads of its own; the call is before the first invoke.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_padded_before(x: u64) -> u64 {
    uw_c_callee(1);
    let _g = Loud(2);
    unsafe { terminate_region_callback(20) };
    x
}

// (a2) the call after the last invoke, sharing its region with the guard's
// normal-path Drop call (may-unwind unless LLVM infers nounwind).
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_padded_after(x: u64) -> u64 {
    {
        let _g = Loud(2);
        unsafe { terminate_region_callback(20) };
    }
    uw_c_callee(21);
    x
}

// (a3) the call after the last invoke while the guard is still live: the
// region after it holds the guard's normal-path Drop.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_padded_live(x: u64) -> u64 {
    let _g = Loud(2);
    unsafe { terminate_region_callback(20) };
    uw_c_callee(21);
    x
}

// (b) a caller with no landing pads.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_no_pads(x: u64) -> u64 {
    uw_c_callee(1);
    black_box(x)
}

// (c) between two Rust-ABI invokes that share one cleanup pad.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_between_shared(x: u64) -> u64 {
    let _g = Loud(3);
    unsafe { terminate_region_rust_callback(30) };
    uw_c_callee(31);
    unsafe { terminate_region_rust_callback(32) };
    x
}

// (c2) between two C-unwind invokes (each foreign call gets its own pad).
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_between_foreign(x: u64) -> u64 {
    let _g = Loud(3);
    unsafe { terminate_region_callback(30) };
    uw_c_callee(31);
    unsafe { terminate_region_callback(32) };
    x
}

// (d) through an `extern "C"` fn pointer LLVM cannot see.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_c_pointer(x: u64) -> u64 {
    let _g = Loud(4);
    unsafe { terminate_region_callback(40) };
    let f: extern "C" fn(u64) = black_box(uw_c_callee as extern "C" fn(u64));
    f(41);
    unsafe { terminate_region_callback(42) };
    x
}

// (d2) through an `extern "C"` fn pointer holding a known item.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_c_pointer_known(x: u64) -> u64 {
    let _g = Loud(4);
    unsafe { terminate_region_callback(40) };
    let f: extern "C" fn(u64) = uw_c_callee;
    f(41);
    unsafe { terminate_region_callback(42) };
    x
}

// (e) from the caller's cleanup: a Drop that calls the extern "C" callee.
pub struct CallsC(u64);
impl Drop for CallsC {
    #[inline(never)]
    fn drop(&mut self) {
        uw_c_callee(self.0)
    }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_cleanup_calls_c(x: u64) -> u64 {
    let _g = CallsC(5);
    unsafe { terminate_region_callback(50) };
    x
}

// (e2) the same Drop, inlinable into the cleanup pad.
pub struct CallsCInline(u64);
impl Drop for CallsCInline {
    #[inline]
    fn drop(&mut self) {
        uw_c_callee(self.0)
    }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_cleanup_calls_c_inline(x: u64) -> u64 {
    let _g = CallsCInline(5);
    unsafe { terminate_region_callback(50) };
    x
}

// (f) control: extern "C-unwind" callee must keep unwinding.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_padded_cu(x: u64) -> u64 {
    let _g = Loud(6);
    unsafe { terminate_region_callback(60) };
    uw_cu_callee(61);
    x
}

// (f2) control: Rust-ABI callee must keep unwinding.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_padded_rust(x: u64) -> u64 {
    let _g = Loud(6);
    unsafe { terminate_region_callback(60) };
    uw_rust_callee(61);
    x
}

// (g) libc-declared extern "C" callee in the same region as the panicking
// Rust-defined extern "C" callee.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_libc_region(x: u64) -> u64 {
    let _g = Loud(7);
    unsafe { terminate_region_callback(70) };
    let pid = unsafe { getpid() };
    uw_c_callee(71);
    x + u64::from(black_box(pid) == 0)
}

// (g2) libc qsort with a comparator that panics with no live Drop: the
// comparator's own Terminate(Abi) edge carries the empty filter, so the
// search stops inside it and nothing unwinds through libc.
extern "C" fn uw_compare(a: *const core::ffi::c_void, b: *const core::ffi::c_void) -> i32 {
    // An extern "C" Rust fn: the C-unwind callback's panic terminates here.
    unsafe { terminate_region_callback(80) };
    let (a, b) = unsafe { (*(a as *const u64), *(b as *const u64)) };
    (a > b) as i32 - (a < b) as i32
}
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_libc_qsort(x: u64) -> u64 {
    let _g = Loud(8);
    unsafe { terminate_region_callback(81) };
    let mut data = [3u64, 1, 2];
    unsafe { qsort(data.as_mut_ptr().cast(), 3, 8, uw_compare) };
    x + black_box(data)[0]
}

// (g3) the same comparator-filter control with qsort between two C-unwind
// invokes: the search never reaches this frame either.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_libc_qsort_gap(x: u64) -> u64 {
    let _g = Loud(8);
    let mut data = [3u64, 1, 2];
    unsafe { terminate_region_callback(81) };
    unsafe { qsort(data.as_mut_ptr().cast(), 3, 8, uw_compare) };
    unsafe { terminate_region_callback(82) };
    x + black_box(data)[0]
}

// (g4) a comparator with a live Drop: its `terminate(abi)` follows a cleanup,
// so the search continues through libc's qsort frame into this frame, where
// the `nounwind` qsort call sits between two C-unwind invokes with their own
// pads.
extern "C" fn uw_compare_loud(a: *const core::ffi::c_void, b: *const core::ffi::c_void) -> i32 {
    let _l = Loud(85);
    unsafe { terminate_region_callback(80) };
    let (a, b) = unsafe { (*(a as *const u64), *(b as *const u64)) };
    (a > b) as i32 - (a < b) as i32
}
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_libc_qsort_unwinds(x: u64) -> u64 {
    let _g = Loud(8);
    let mut data = [3u64, 1, 2];
    unsafe { terminate_region_callback(81) };
    unsafe { qsort(data.as_mut_ptr().cast(), 3, 8, uw_compare_loud) };
    unsafe { terminate_region_callback(82) };
    x + black_box(data)[0]
}

/// A Rust-ABI callee that cannot panic but is not declared nounwind.
#[unsafe(no_mangle)]
#[inline(never)]
pub fn uw_rust_quiet(id: u64) -> u64 {
    black_box(id)
}

// (h) a Rust-ABI call shares the region before the first invoke.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_rust_shares_region(x: u64) -> u64 {
    uw_c_callee(1);
    let y = uw_rust_quiet(x);
    let _g = Loud(2);
    unsafe { terminate_region_callback(20) };
    y
}

// (i) print! shares the region before the first invoke (LLVM: std::io::_print,
// a Rust-ABI call that may unwind under panic=unwind).
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_print_region(x: u64) -> u64 {
    uw_c_callee(1);
    std::print!("PRINT\n");
    let _g = Loud(2);
    unsafe { terminate_region_callback(20) };
    x
}

// (j) a Box guard: the cleanup pad holds a nounwind dealloc and _Unwind_Resume;
// the extern "C" call follows the invoke.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_resume_region(x: u64) -> u64 {
    let b = std::boxed::Box::new(black_box(x));
    unsafe { terminate_region_callback(90) };
    uw_c_callee(91);
    *b
}

/// A Rust-defined `extern "C"` callee with no Drop local: its panic's unwind
/// action is a direct Terminate(Abi).
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn uw_c_bare(id: u64) {
    unsafe { terminate_region_callback(id) }
}

// (k) the bare callee before the first invoke (cf. padded_before).
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_bare_before(x: u64) -> u64 {
    uw_c_bare(1);
    let _g = Loud(2);
    unsafe { terminate_region_callback(20) };
    x
}

/// An `extern "C"` callee LLVM may inline (no `#[inline(never)]`).
pub extern "C" fn uw_c_inlinable(id: u64) {
    let _l = Loud(id);
    unsafe { terminate_region_callback(id) }
}

// (l) the inlinable callee before the first invoke.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_inlinable_before(x: u64) -> u64 {
    uw_c_inlinable(1);
    let _g = Loud(2);
    unsafe { terminate_region_callback(20) };
    x
}

/// A Rust-ABI callee with no Drop local, called from an unprotected region.
#[unsafe(no_mangle)]
#[inline(never)]
pub fn uw_rust_bare(id: u64) {
    unsafe { terminate_region_callback(id) }
}

// (n) control: a Rust-ABI callee panics before the caller's first invoke;
// the caller's region holds a call that may unwind, so the panic is caught.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_rust_unprotected(x: u64) -> u64 {
    uw_rust_bare(1);
    let _g = Loud(2);
    unsafe { terminate_region_callback(20) };
    x
}

// (o) control: an `extern "C-unwind"` callee before the first invoke.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_cu_unprotected(x: u64) -> u64 {
    uw_cu_callee(1);
    let _g = Loud(2);
    unsafe { terminate_region_callback(20) };
    x
}

// The fn pointer the next two controls call, read with a plain load so that
// no call (such as `black_box`) shares their region.
static mut RUST_BARE: fn(u64) = uw_rust_bare;

// (p) control: a Rust-ABI fn pointer before the first invoke.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_rust_pointer_unprotected(x: u64) -> u64 {
    let f: fn(u64) = unsafe { *(&raw const RUST_BARE) };
    f(1);
    let _g = Loud(2);
    unsafe { terminate_region_callback(20) };
    x
}

// (q) control: a `&dyn Fn` call before the first invoke.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn uw_dyn_unprotected(x: u64) -> u64 {
    let f: &dyn Fn(u64) = unsafe { &*(&raw const RUST_BARE) };
    f(1);
    let _g = Loud(2);
    unsafe { terminate_region_callback(20) };
    x
}
