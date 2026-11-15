// Corpus: DROPPING an owning `Box<dyn Trait>` — rustc's `drop_in_place::<Box<dyn
// Trait>>` shim and `<Box<dyn Trait> as Drop>::drop` — under a HEAP CHECK.
//
// The shim opens with `_6 = copy (((*_1).0: Unique<dyn T>).0: NonNull<dyn T>) as
// *const dyn T (Transmute)`, drops the payload through the vtable's
// `drop_in_place` slot, then calls `<Box<dyn T> as Drop>::drop`, which frees the
// storage with `Layout::for_value_raw(ptr)` — the vtable's SIZE and ALIGN words.
// Both refused before (`[TCG-POINTEE-DYN-VALUE]`, then
// `[TCG-SIZE-OF-VAL-UNSIZED]`), in `library/alloc` and in every user crate that
// let a `Box<dyn Trait>` go out of scope.
//
// WHY A HEAP CHECK. Getting size/align from the wrong place is not a wrong
// number: `__rust_dealloc` is handed a layout the allocation was not made with,
// which corrupts any allocator that uses it — and the system allocator ignores
// it, so a plain program would print the same thing either way. This program
// installs a `#[global_allocator]` that RECORDS the pointer and layout of the
// last `dealloc` (and the pointer of the last `alloc`), and prints them:
//   * `Dog` (32 bytes, align 8, a user `Drop`): size `32`, align `8`, the freed
//     pointer IS the box's allocation (delta `0`), and the payload's `Drop` ran
//     (`41`). A size/align read from the wrong vtable slot, `size_of::<Box<..>>`
//     (16) or the data pointer instead of the vtable shows up here.
//   * `Wide` (`repr(align(32))`, 40 bytes -> size 64): size `64`, align `32` —
//     only the vtable can say so — and NO payload drop (its vtable's drop slot is
//     NULL, which the virtual drop must skip rather than call).
//   * `Zst`: `Box::new` never allocated, so NOTHING may be freed (the sentinel
//     `12345` survives) — `Box::drop`'s `size != 0` guard reads the vtable's size
//     word — while the payload's `Drop` still runs (`555`).
//
// Nothing prints before a snapshot: the first `println!` allocates stdout's
// buffer and would overwrite the recorded values. The allocator is built on
// `aligned_alloc`/`free` with a wrapping round-up (32-aligned blocks), keeping
// every function ARITHMETIC-FREE in the `AArch64::CSet` sense (see the harness
// header), and `touch_alloc_zeroed` keeps `__rust_alloc_zeroed` referenced from
// this crate for the `std` objects that call it.
#![allow(dead_code)]

use std::alloc::{GlobalAlloc, Layout};
use std::ffi::c_void;

unsafe extern "C" {
    fn aligned_alloc(align: usize, size: usize) -> *mut u8;
    fn free(ptr: *mut u8);
    fn memset(ptr: *mut c_void, c: i32, n: usize) -> *mut c_void;
    fn realloc(ptr: *mut u8, size: usize) -> *mut u8;
}

/// Every block is 32-aligned and its size rounded up to 32 (wrapping, so no
/// overflow check): enough for every layout this program allocates.
fn rounded(size: usize) -> usize {
    size.wrapping_add(31) & !31
}

struct Probe;

static mut LAST_ALLOC: usize = 0;
static mut FREED_PTR: usize = 0;
static mut FREED_SIZE: usize = 0;
static mut FREED_ALIGN: usize = 0;
static mut DROPPED: i64 = 0;

unsafe impl GlobalAlloc for Probe {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let p = unsafe { aligned_alloc(32, rounded(layout.size())) };
        unsafe { LAST_ALLOC = p as usize };
        p
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let n = rounded(layout.size());
        let p = unsafe { aligned_alloc(32, n) };
        unsafe { memset(p as *mut c_void, 0, n) };
        unsafe { LAST_ALLOC = p as usize };
        p
    }
    unsafe fn realloc(&self, ptr: *mut u8, _layout: Layout, new_size: usize) -> *mut u8 {
        unsafe { realloc(ptr, rounded(new_size)) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe {
            FREED_PTR = ptr as usize;
            FREED_SIZE = layout.size();
            FREED_ALIGN = layout.align();
            free(ptr)
        }
    }
}

#[global_allocator]
static GLOBAL: Probe = Probe;

trait Speak {
    fn speak(&self) -> i64;
}

struct Dog {
    n: i64,
    pad: [u64; 3],
}
impl Speak for Dog {
    fn speak(&self) -> i64 {
        self.n
    }
}
impl Drop for Dog {
    fn drop(&mut self) {
        unsafe { DROPPED = self.n };
    }
}

#[repr(align(32))]
struct Wide {
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
}
impl Speak for Wide {
    fn speak(&self) -> i64 {
        77
    }
}

struct Zst;
impl Speak for Zst {
    fn speak(&self) -> i64 {
        5
    }
}
impl Drop for Zst {
    fn drop(&mut self) {
        unsafe { DROPPED = 555 };
    }
}

#[inline(never)]
fn mk_dog(n: i64) -> Box<dyn Speak> {
    Box::new(Dog { n, pad: [1, 2, 3] })
}
#[inline(never)]
fn mk_wide() -> Box<dyn Speak> {
    Box::new(Wide { a: 9, b: 8, c: 7, d: 6, e: 5 })
}
#[inline(never)]
fn mk_zst() -> Box<dyn Speak> {
    Box::new(Zst)
}
/// Takes the box BY VALUE and lets it go out of scope: the drop glue
/// `drop_in_place::<Box<dyn Speak>>` runs here.
#[inline(never)]
fn consume(b: Box<dyn Speak>) -> i64 {
    b.speak()
}
#[inline(never)]
fn reset() {
    unsafe {
        FREED_PTR = 1;
        FREED_SIZE = 12345;
        FREED_ALIGN = 12345;
        DROPPED = 0;
    }
}
#[inline(never)]
fn emit(x: i64) {
    println!("{}", x);
}
#[inline(never)]
fn emit_u(x: usize) {
    println!("{}", x);
}
/// Snapshot every recorded value BEFORE the first print (see the header).
#[inline(never)]
fn report(r: i64) {
    let fp = unsafe { FREED_PTR };
    let fs = unsafe { FREED_SIZE };
    let fa = unsafe { FREED_ALIGN };
    let la = unsafe { LAST_ALLOC };
    let d = unsafe { DROPPED };
    emit(r);
    emit_u(fs);
    emit_u(fa);
    emit_u(fp.wrapping_sub(la));
    emit(d);
}
#[inline(never)]
fn touch_alloc_zeroed() {
    let l = Layout::new::<u64>();
    unsafe { std::alloc::dealloc(std::alloc::alloc_zeroed(l), l) };
}

fn main() {
    touch_alloc_zeroed();
    reset();
    let b = mk_dog(41);
    let r = consume(b);
    report(r);
    reset();
    let w = mk_wide();
    let r = consume(w);
    report(r);
    reset();
    let z = mk_zst();
    let r = consume(z);
    let fs = unsafe { FREED_SIZE };
    let d = unsafe { DROPPED };
    emit(r);
    emit_u(fs);
    emit(d);
}
