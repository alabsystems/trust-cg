//! Driver of `copy_klib.rs` (always LLVM-built): `--list` prints the cases;
//! a case name runs one case under `catch_unwind` and prints what std
//! guarantees after the unwind (the Vec's contents, or the net change in live
//! heap blocks counted by this program's global allocator).

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
    "retain_u32",
    "retain_mut_u32",
    "retain_pair",
    "retain_large",
    "retain_keep_all",
    "retain_no_panic",
    "dedup_by_u32",
    "dedup_by_key_u32",
    "dedup_by_key_first",
    "resize_with_u32",
    "collect_map",
    "collect_map_ok",
    "owned_count",
    "owned_count_ok",
];

/// Whether `f` unwound; the panic payload is dropped before this returns.
fn unwound(f: impl FnOnce()) -> bool {
    catch_unwind(AssertUnwindSafe(f)).is_err()
}

fn in_place<T: std::fmt::Debug>(mut v: Vec<T>, f: fn(&mut Vec<T>)) {
    let panicked = unwound(|| f(&mut v));
    println!("panicked={panicked} len={} v={v:?}", v.len());
}

/// The net change in live heap blocks across `f`.
fn net_blocks(f: impl FnOnce() -> bool) {
    let before = LIVE.load(SeqCst);
    let panicked = f();
    println!(
        "panicked={panicked} net_live_blocks={}",
        LIVE.load(SeqCst) - before
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
    let _ = unwound(|| panic!("warm-up"));
    let small = || black_box(vec![3u32, 1, 4, 1, 5, 9]);
    match case.as_str() {
        "retain_u32" => in_place(small(), klib::retain_u32),
        "retain_mut_u32" => in_place(small(), klib::retain_mut_u32),
        "retain_pair" => in_place(
            black_box(vec![
                (3u32, 30u32),
                (1, 10),
                (4, 40),
                (1, 11),
                (5, 50),
                (9, 90),
            ]),
            klib::retain_pair,
        ),
        "retain_large" => {
            let mut v: Vec<u32> = black_box((0..1000).collect());
            let panicked = unwound(|| klib::retain_large(&mut v));
            let sum: u64 = v.iter().map(|&x| u64::from(x)).sum();
            println!(
                "panicked={panicked} len={} sum={sum} head={:?} mid={:?}",
                v.len(),
                &v[..6],
                &v[598..604]
            );
        }
        "retain_keep_all" => in_place(small(), klib::retain_keep_all),
        "retain_no_panic" => in_place(small(), klib::retain_no_panic),
        "dedup_by_u32" => in_place(small(), klib::dedup_by_u32),
        "dedup_by_key_u32" => in_place(small(), klib::dedup_by_key_u32),
        "dedup_by_key_first" => in_place(small(), klib::dedup_by_key_first),
        "resize_with_u32" => in_place(black_box(vec![3u32, 1]), klib::resize_with_u32),
        "collect_map" => {
            let input: [u8; 4] = black_box([1, 2, 13, 4]);
            net_blocks(|| unwound(|| drop(klib::collect_map(&input))));
        }
        "collect_map_ok" => {
            let input: [u8; 4] = black_box([1, 2, 3, 4]);
            net_blocks(|| unwound(|| drop(klib::collect_map(&input))));
        }
        "owned_count" => net_blocks(|| {
            let v = black_box(vec![2u32, 4, 13, 6]);
            unwound(move || {
                black_box(klib::owned_count(v));
            })
        }),
        "owned_count_ok" => net_blocks(|| {
            let v = black_box(vec![2u32, 4, 7, 6]);
            unwound(move || {
                black_box(klib::owned_count(v));
            })
        }),
        other => panic!("unknown case {other:?}"),
    }
}
