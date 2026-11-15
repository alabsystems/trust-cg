// Constant and live iterator images must preserve Chain's Option payloads,
// allocation requests, capacity and complete element order at every opt level.
extern crate chain_observer;

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

static ALLOCS: AtomicUsize = AtomicUsize::new(0);
static DEALLOCS: AtomicUsize = AtomicUsize::new(0);
static REQUESTED: AtomicUsize = AtomicUsize::new(0);
static FREED: AtomicUsize = AtomicUsize::new(0);

struct Counting;

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOCS.fetch_add(1, Relaxed);
        REQUESTED.fetch_add(layout.size(), Relaxed);
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        DEALLOCS.fetch_add(1, Relaxed);
        FREED.fetch_add(layout.size(), Relaxed);
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

unsafe extern "C" {
    fn getenv(name: *const u8) -> *const u8;
}

#[inline(never)]
fn report(capacity: usize, sum: u64, observed: u64) {
    let allocs = ALLOCS.load(Relaxed);
    let deallocs = DEALLOCS.load(Relaxed);
    let requested = REQUESTED.load(Relaxed);
    let freed = FREED.load(Relaxed);
    let observations = chain_observer::observations();
    println!(
        "allocs={allocs} deallocs={deallocs} requested={requested} freed={freed} cap={capacity} sum={sum} observed={observed} observations={observations}"
    );
}

#[inline(never)]
fn finish(values: Vec<u64>, observed: u64) {
    let capacity;
    let mut sum = 0u64;
    {
        let owned = values;
        capacity = owned.capacity();
        for value in &owned {
            sum = sum.wrapping_mul(31).wrapping_add(*value);
        }
    }
    report(capacity, sum, observed);
}

#[inline(never)]
fn live_left(n: u64) {
    let iter = (0..n).chain(5..7);
    let observed = unsafe { chain_observer::observe_u64(&iter) };
    finish(iter.collect(), observed);
}

#[inline(never)]
fn live_right(n: u64) {
    let iter = (5..7).chain(0..n);
    let observed = unsafe { chain_observer::observe_u64(&iter) };
    finish(iter.collect(), observed);
}

#[inline(never)]
fn both_constant() {
    let iter = (1u64..4).chain(0x1_0000_0000..0x1_0000_0002);
    let observed = unsafe { chain_observer::observe_u64(&iter) };
    finish(iter.collect(), observed);
}

#[inline(never)]
fn empty_left() {
    let iter = (9u64..9).chain(5..7);
    let observed = unsafe { chain_observer::observe_u64(&iter) };
    finish(iter.collect(), observed);
}

#[inline(never)]
fn both_empty() {
    let iter = (7u64..3).chain(10..7);
    let observed = unsafe { chain_observer::observe_u64(&iter) };
    finish(iter.collect(), observed);
}

#[inline(never)]
fn narrow() {
    let iter = (0u32..3).chain(5..7);
    let observed = unsafe { chain_observer::observe_u32(&iter) };
    let capacity;
    let mut sum = 0u64;
    {
        let values: Vec<u32> = iter.collect();
        capacity = values.capacity();
        for value in &values {
            sum = sum.wrapping_mul(31).wrapping_add(u64::from(*value));
        }
    }
    report(capacity, sum, observed);
}

#[inline(never)]
fn signed() {
    let iter = (-2i64..1).chain(5..7);
    let observed = unsafe { chain_observer::observe_i64(&iter) };
    let capacity;
    let mut sum = 0u64;
    {
        let values: Vec<i64> = iter.collect();
        capacity = values.capacity();
        for value in &values {
            sum = sum.wrapping_mul(31).wrapping_add(*value as u64);
        }
    }
    report(capacity, sum, observed);
}

static LEFT: [u64; 3] = [2, 0x1_0000_0003, 7];
static RIGHT: [u64; 2] = [11, 13];

#[inline(never)]
fn relocated_slices() {
    let iter = LEFT.iter().chain(RIGHT.iter());
    let observed = unsafe { chain_observer::observe_slices(&iter) };
    finish(iter.copied().collect(), observed);
}

fn main() {
    let which = unsafe {
        let ptr = getenv(b"ALLOC_SHAPE\0".as_ptr());
        if ptr.is_null() { 0 } else { *ptr }
    };
    ALLOCS.store(0, Relaxed);
    DEALLOCS.store(0, Relaxed);
    REQUESTED.store(0, Relaxed);
    FREED.store(0, Relaxed);
    match which {
        b'a' => live_left(3),
        b'b' => live_right(3),
        b'c' => both_constant(),
        b'd' => empty_left(),
        b'e' => both_empty(),
        b'f' => narrow(),
        b'g' => signed(),
        b'h' => relocated_slices(),
        _ => panic!("unknown allocation shape"),
    }
}
