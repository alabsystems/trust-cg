// CORPUS FIXTURE — an allocation-error hook that PANICS (installed by the
// LLVM-built `alloc_error_hook_set` rlib) makes `handle_alloc_error` unwind.
// The bridge's allocation-failure call stands in for the call std makes inside
// `Box::new` / `vec!`, so it must carry that source call's unwind edge:
//
//   * a live `Guard` (rows `a`..`d`): the cleanup edge runs its Drop, which
//     prints `guard N dropped`, and the panic reaches `lang_start` (exit 101);
//   * an `extern "C"` frame (row `f`): the terminate edge aborts with "panic in
//     a function that cannot unwind";
//   * a `BTreeMap` / `HashMap` built and filled in a guarded frame (rows `g`,
//     `h`): std's empty map allocates nothing, so the FIRST insert's allocation
//     is the one that fails, and the panic leaves through the insert call's
//     cleanup edge (the guard's Drop runs). The bridge's map model requests a
//     different SIZE than std's nodes, so these rows compare the hook's
//     `hooked N` size only by presence.
//
// The allocator fails the first request of the armed size, then disarms, so
// the panic machinery's own allocations (the message, the payload box, a
// backtrace) are served. `z` arms nothing.
extern crate alloc_error_hook_set;

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::Relaxed};

static FAIL_SIZE: AtomicUsize = AtomicUsize::new(0);
static FAIL_NEXT: AtomicBool = AtomicBool::new(false);

struct FailOneSize;

unsafe impl GlobalAlloc for FailOneSize {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        if FAIL_NEXT.swap(false, Relaxed) {
            return std::ptr::null_mut();
        }
        if l.size() == FAIL_SIZE.load(Relaxed) {
            // One-shot: the failure path's own allocations must succeed.
            FAIL_SIZE.store(0, Relaxed);
            std::ptr::null_mut()
        } else {
            unsafe { System.alloc(l) }
        }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        unsafe { System.dealloc(p, l) }
    }
}

#[global_allocator]
static GLOBAL: FailOneSize = FailOneSize;

struct Guard(u32);

impl Drop for Guard {
    fn drop(&mut self) {
        FAIL_SIZE.store(0, Relaxed);
        FAIL_NEXT.store(false, Relaxed);
        println!("guard {} dropped", self.0);
    }
}

#[inline(never)]
fn arm(n: usize) {
    FAIL_SIZE.store(n, Relaxed);
}

#[inline(never)]
fn box_array_guard() -> u64 {
    let _g = Guard(10);
    arm(72);
    let b = Box::new([41u64; 9]);
    arm(0);
    b[8] + 1
}

#[inline(never)]
fn box_big_guard() -> u64 {
    let _g = Guard(11);
    arm(4104);
    let b = Box::new([2u64; 513]);
    arm(0);
    b[0] + b[512]
}

#[inline(never)]
fn from_elem_guard() -> u16 {
    let _g = Guard(12);
    arm(102);
    let v = vec![7u16; 51];
    arm(0);
    v[50]
}

#[inline(never)]
fn vec_literal_guard() -> u64 {
    let _g = Guard(13);
    arm(56);
    let v = vec![1u64, 2, 3, 4, 5, 6, 7];
    arm(0);
    v[6]
}

// The frame drops nothing and holds no `Assert`, so under panic=unwind the
// `Box::new` call's terminate edge is its only kind of unwind edge (a local
// box's drop would add a cleanup edge, an `Assert` a terminate edge of its
// own, and either turns EH on regardless of the allocation).
#[inline(never)]
extern "C" fn box_in_nounwind_frame() -> Box<u64> {
    arm(8);
    Box::new(41u64)
}

/// The box comes back and is dropped at the end of this frame's scope.
#[inline(never)]
fn box_from_nounwind_frame() -> u64 {
    let _b = box_in_nounwind_frame();
    41
}

#[inline(never)]
fn btreemap_guard() -> u64 {
    let _g = Guard(14);
    FAIL_NEXT.store(true, Relaxed);
    let mut m = std::collections::BTreeMap::new();
    m.insert(1u64, 2u64);
    m.insert(3u64, 4u64);
    FAIL_NEXT.store(false, Relaxed);
    m.len() as u64
}

#[inline(never)]
fn hashmap_guard() -> u64 {
    let _g = Guard(15);
    FAIL_NEXT.store(true, Relaxed);
    let mut h = std::collections::HashMap::new();
    h.insert(1u64, 2u64);
    h.insert(3u64, 4u64);
    FAIL_NEXT.store(false, Relaxed);
    h.len() as u64
}

unsafe extern "C" {
    fn getenv(name: *const u8) -> *const u8;
}

fn shape() -> u8 {
    unsafe {
        let p = getenv(b"ALLOC_SHAPE\0".as_ptr());
        if p.is_null() { 0 } else { *p }
    }
}

fn main() {
    alloc_error_hook_set::install();
    let which = shape();
    println!("start {which}");
    let r = match which {
        b'a' => box_array_guard(),
        b'b' => box_big_guard(),
        b'c' => from_elem_guard() as u64,
        b'd' => vec_literal_guard(),
        b'f' => box_from_nounwind_frame(),
        b'g' => btreemap_guard(),
        b'h' => hashmap_guard(),
        _ => 0,
    };
    println!("returned {r}");
}
