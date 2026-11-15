// Host side of `mir_families_aarch64`'s drop differential (ledger L06-P8),
// ALWAYS compiled by rustc's LLVM backend: a counting global allocator (every
// allocation minus every free), a `catch_unwind` boundary, and a silent panic
// hook. The guest crate (`drop_guest.rs`) is compiled by the bridge or by LLVM
// and linked against this one, so both sides observe frees and caught panics
// through the same code.
#![crate_type = "rlib"]
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicIsize, Ordering::Relaxed};

pub struct Counting;

static LIVE: AtomicIsize = AtomicIsize::new(0);

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        LIVE.fetch_add(1, Relaxed);
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        LIVE.fetch_sub(1, Relaxed);
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

/// Allocations not yet freed.
#[inline(never)]
pub fn live() -> isize {
    LIVE.load(Relaxed)
}

/// Run `scenario`; whether it unwound out (a caught panic).
#[inline(never)]
pub fn caught(scenario: fn()) -> bool {
    std::panic::catch_unwind(scenario).is_err()
}

/// Silence the default hook's message (both sides run the same hook).
#[inline(never)]
pub fn quiet() {
    std::panic::set_hook(Box::new(|_| {}));
}
