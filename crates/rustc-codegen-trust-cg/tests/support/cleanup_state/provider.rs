use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

static OBSERVED: AtomicUsize = AtomicUsize::new(0);
static PTR0: AtomicUsize = AtomicUsize::new(0);
static PTR1: AtomicUsize = AtomicUsize::new(0);
static LIVE0: AtomicUsize = AtomicUsize::new(0);
static LIVE1: AtomicUsize = AtomicUsize::new(0);
static VALUE0: AtomicU64 = AtomicU64::new(0);
static VALUE1: AtomicU64 = AtomicU64::new(0);
static FREED0: AtomicUsize = AtomicUsize::new(0);
static FREED1: AtomicUsize = AtomicUsize::new(0);
static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);
static DROP_TAG: AtomicU64 = AtomicU64::new(0);

struct TrackingAllocator;
unsafe impl GlobalAlloc for TrackingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let address = ptr as usize;
        if LIVE0.compare_exchange(address, 0, Ordering::SeqCst, Ordering::SeqCst).is_ok() {
            FREED0.fetch_add(1, Ordering::SeqCst);
        }
        if LIVE1.compare_exchange(address, 0, Ordering::SeqCst, Ordering::SeqCst).is_ok() {
            FREED1.fetch_add(1, Ordering::SeqCst);
        }
        unsafe { System.dealloc(ptr, layout) }
    }
}
#[global_allocator]
static ALLOCATOR: TrackingAllocator = TrackingAllocator;

#[derive(Debug)]
pub struct ProbePanic(pub u8);

#[inline(never)]
pub fn may_unwind(site: u8, panic_site: u8) -> u64 {
    if site == panic_site {
        std::panic::panic_any(ProbePanic(site));
    }
    0x9000 + u64::from(site)
}

#[inline(never)]
pub fn make_box(value: u64, site: u8, panic_site: u8) -> Box<u64> {
    may_unwind(site, panic_site);
    Box::new(value)
}

/// The LLVM provider reads the actual initialized pointee, independently of
/// the consumer's return-value lowering. A live pointer is tracked only once;
/// subsequent unrelated allocations cannot satisfy a missing buffer free.
#[inline(never)]
pub unsafe fn observe_box(address: usize) {
    let value = unsafe { *(address as *const u64) };
    let index = OBSERVED.fetch_add(1, Ordering::SeqCst);
    let (pointer, live, payload) = match index {
        0 => (&PTR0, &LIVE0, &VALUE0),
        1 => (&PTR1, &LIVE1, &VALUE1),
        _ => std::process::exit(90),
    };
    pointer.store(address, Ordering::SeqCst);
    live.store(address, Ordering::SeqCst);
    payload.store(value, Ordering::SeqCst);
}

#[inline(never)]
pub fn record_drop(tag: u64) {
    DROP_TAG.store(tag, Ordering::SeqCst);
    DROP_COUNT.fetch_add(1, Ordering::SeqCst);
}

pub fn reset() {
    for value in [&OBSERVED, &PTR0, &PTR1, &LIVE0, &LIVE1, &FREED0, &FREED1, &DROP_COUNT] {
        value.store(0, Ordering::SeqCst);
    }
    for value in [&VALUE0, &VALUE1, &DROP_TAG] {
        value.store(0, Ordering::SeqCst);
    }
}
pub fn observed_count() -> usize { OBSERVED.load(Ordering::SeqCst) }
pub fn box_observation(index: usize) -> (usize, u64, usize) {
    let (pointer, payload, frees) = match index {
        0 => (&PTR0, &VALUE0, &FREED0),
        1 => (&PTR1, &VALUE1, &FREED1),
        _ => panic!("bad observation index"),
    };
    (pointer.load(Ordering::SeqCst), payload.load(Ordering::SeqCst), frees.load(Ordering::SeqCst))
}
pub fn drop_observation() -> (usize, u64) {
    (DROP_COUNT.load(Ordering::SeqCst), DROP_TAG.load(Ordering::SeqCst))
}
