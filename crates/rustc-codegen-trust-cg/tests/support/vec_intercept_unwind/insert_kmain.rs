//! Driver of `insert_klib.rs` (always LLVM-built): each case inserts at index
//! `3` (past the end: std panics) or `1` (in bounds) under `catch_unwind` and
//! prints the element drops and the net change in live heap blocks.

use std::alloc::{GlobalAlloc, Layout, System};
use std::hint::black_box;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::atomic::{AtomicIsize, Ordering::SeqCst};

static LIVE: AtomicIsize = AtomicIsize::new(0);

struct Counting;

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        LIVE.fetch_add(1, SeqCst);
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        LIVE.fetch_sub(1, SeqCst);
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static ALLOCATOR: Counting = Counting;

const CASES: &[&str] = &[
    "d_oob",
    "d_in_bounds",
    "box_oob",
    "box_in_bounds",
    "box_d_oob",
    "box_d_in_bounds",
];

fn drops() -> u32 {
    unsafe { klib::DROPS }
}

fn report<T>(mut v: Vec<T>, index: usize, insert: fn(&mut Vec<T>, usize)) {
    let drops_before = drops();
    let live_before = LIVE.load(SeqCst);
    let panicked = catch_unwind(AssertUnwindSafe(|| insert(&mut v, black_box(index)))).is_err();
    println!(
        "panicked={panicked} len={} drops={} net_live_blocks={}",
        v.len(),
        drops() - drops_before,
        LIVE.load(SeqCst) - live_before
    );
}

fn main() {
    let case = std::env::args().nth(1).unwrap_or_default();
    if case == "--list" {
        for case in CASES {
            println!("{case}");
        }
        return;
    }
    std::panic::set_hook(Box::new(|_| {}));
    // The first panic of a thread allocates runtime state; keep it out of the
    // block counts.
    let _ = catch_unwind(|| panic!("warm-up"));
    // Room for one more element, so an in-bounds insert does not reallocate.
    let mut ds = Vec::with_capacity(4);
    ds.extend([klib::D(0), klib::D(1)]);
    let mut boxes = Vec::with_capacity(4);
    boxes.extend([Box::new(0u64), Box::new(1)]);
    let mut boxed_ds = Vec::with_capacity(4);
    boxed_ds.extend([Box::new(klib::D(0)), Box::new(klib::D(1))]);
    match case.as_str() {
        "d_oob" => report(ds, 3, klib::insert_d),
        "d_in_bounds" => report(ds, 1, klib::insert_d),
        "box_oob" => report(boxes, 3, klib::insert_box),
        "box_in_bounds" => report(boxes, 1, klib::insert_box),
        "box_d_oob" => report(boxed_ds, 3, klib::insert_box_d),
        "box_d_in_bounds" => report(boxed_ds, 1, klib::insert_box_d),
        other => panic!("unknown case {other:?}"),
    }
}
