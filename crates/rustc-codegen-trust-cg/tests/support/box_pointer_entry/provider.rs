//! LLVM-built provider and allocator oracle; every boundary uses Rust metadata.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicI64, AtomicUsize, Ordering};

pub const FREE_OLD: usize = 1;
pub const FREE_NEW: usize = 2;
pub const READ: usize = 3;
pub const RETARGET_BEGIN: usize = 4;
pub const RETARGET_END: usize = 5;

static OLD: AtomicUsize = AtomicUsize::new(0);
static NEW: AtomicUsize = AtomicUsize::new(0);
static OLD_FREES: AtomicUsize = AtomicUsize::new(0);
static NEW_FREES: AtomicUsize = AtomicUsize::new(0);
static BAD_LAYOUT: AtomicUsize = AtomicUsize::new(0);
static READS: AtomicUsize = AtomicUsize::new(0);
static RETARGETS: AtomicUsize = AtomicUsize::new(0);
static OBSERVED: AtomicUsize = AtomicUsize::new(0);
static PAYLOAD: AtomicI64 = AtomicI64::new(0);
static BEFORE: AtomicUsize = AtomicUsize::new(0);
static AFTER: AtomicUsize = AtomicUsize::new(0);
static BEFORE_PAYLOAD: AtomicI64 = AtomicI64::new(0);
static AFTER_PAYLOAD: AtomicI64 = AtomicI64::new(0);
static EVENT_COUNT: AtomicUsize = AtomicUsize::new(0);
static EVENTS: [AtomicUsize; 8] = [const { AtomicUsize::new(0) }; 8];

fn event(kind: usize) {
    let slot = EVENT_COUNT.fetch_add(1, Ordering::SeqCst);
    if let Some(destination) = EVENTS.get(slot) {
        destination.store(kind, Ordering::SeqCst);
    }
}

struct Tracking;
unsafe impl GlobalAlloc for Tracking {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { System.alloc(layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        unsafe { System.alloc_zeroed(layout) }
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        unsafe { System.realloc(pointer, layout, size) }
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        let address = pointer as usize;
        let counter = if address != 0 && address == OLD.load(Ordering::SeqCst) {
            event(FREE_OLD);
            Some(&OLD_FREES)
        } else if address != 0 && address == NEW.load(Ordering::SeqCst) {
            event(FREE_NEW);
            Some(&NEW_FREES)
        } else {
            None
        };
        if let Some(counter) = counter {
            let real = Layout::new::<i64>();
            if layout != real {
                BAD_LAYOUT.fetch_add(1, Ordering::SeqCst);
            }
            // These addresses were allocated as real Box<i64>s. Count a bad
            // layout or repeated free, but do not add allocator UB to the
            // diagnostic: release each tracked allocation once, at its real
            // layout. The driver still rejects every such erroneous attempt.
            if counter.fetch_add(1, Ordering::SeqCst) == 0 {
                unsafe { System.dealloc(pointer, real) };
            }
        } else {
            unsafe { System.dealloc(pointer, layout) };
        }
    }
}

#[global_allocator]
static ALLOCATOR: Tracking = Tracking;

#[inline(never)]
pub fn make_box(payload: i64) -> Box<i64> {
    Box::new(std::hint::black_box(payload))
}

pub fn address(value: &i64) -> usize {
    value as *const i64 as usize
}

pub fn box_layout() -> (usize, usize) {
    let layout = Layout::new::<i64>();
    (layout.size(), layout.align())
}

pub fn begin(old: usize, new: usize) {
    assert_ne!(old, 0);
    assert_ne!(old, new);
    assert_eq!(OLD.load(Ordering::SeqCst), 0);
    assert_eq!(NEW.load(Ordering::SeqCst), 0);
    for atomic in [
        &OLD_FREES,
        &NEW_FREES,
        &BAD_LAYOUT,
        &READS,
        &RETARGETS,
        &OBSERVED,
        &BEFORE,
        &AFTER,
        &EVENT_COUNT,
    ] {
        atomic.store(0, Ordering::SeqCst);
    }
    for atomic in [&PAYLOAD, &BEFORE_PAYLOAD, &AFTER_PAYLOAD] {
        atomic.store(0, Ordering::SeqCst);
    }
    for atomic in &EVENTS {
        atomic.store(0, Ordering::SeqCst);
    }
    OLD.store(old, Ordering::SeqCst);
    NEW.store(new, Ordering::SeqCst);
}

// This opaque provider call writes the consumer's actual Box cell. It is not
// a C declaration of a Rust Box and supplies no compiler receipt or image.
#[inline(never)]
pub fn replace_box(place: &mut Box<i64>, replacement: Box<i64>) {
    RETARGETS.fetch_add(1, Ordering::SeqCst);
    BEFORE.store(address(place.as_ref()), Ordering::SeqCst);
    BEFORE_PAYLOAD.store(**place, Ordering::SeqCst);
    event(RETARGET_BEGIN);
    *place = replacement;
    AFTER.store(address(place.as_ref()), Ordering::SeqCst);
    AFTER_PAYLOAD.store(**place, Ordering::SeqCst);
    event(RETARGET_END);
}

#[inline(never)]
pub fn observe(pointer: *const i64, payload: i64) -> i64 {
    READS.fetch_add(1, Ordering::SeqCst);
    OBSERVED.store(pointer as usize, Ordering::SeqCst);
    PAYLOAD.store(payload, Ordering::SeqCst);
    event(READ);
    payload
}

#[derive(Debug)]
pub struct Snapshot {
    pub old_frees: usize,
    pub new_frees: usize,
    pub bad_layout: usize,
    pub reads: usize,
    pub retargets: usize,
    pub observed: usize,
    pub payload: i64,
    pub before: usize,
    pub after: usize,
    pub before_payload: i64,
    pub after_payload: i64,
    pub event_count: usize,
    pub events: [usize; 8],
}

pub fn finish() -> Snapshot {
    let result = Snapshot {
        old_frees: OLD_FREES.load(Ordering::SeqCst),
        new_frees: NEW_FREES.load(Ordering::SeqCst),
        bad_layout: BAD_LAYOUT.load(Ordering::SeqCst),
        reads: READS.load(Ordering::SeqCst),
        retargets: RETARGETS.load(Ordering::SeqCst),
        observed: OBSERVED.load(Ordering::SeqCst),
        payload: PAYLOAD.load(Ordering::SeqCst),
        before: BEFORE.load(Ordering::SeqCst),
        after: AFTER.load(Ordering::SeqCst),
        before_payload: BEFORE_PAYLOAD.load(Ordering::SeqCst),
        after_payload: AFTER_PAYLOAD.load(Ordering::SeqCst),
        event_count: EVENT_COUNT.load(Ordering::SeqCst),
        events: std::array::from_fn(|index| EVENTS[index].load(Ordering::SeqCst)),
    };
    // End observation before assertions/printing may allocate and reuse one
    // of the already-freed addresses. Consumer events are all synchronous.
    OLD.store(0, Ordering::SeqCst);
    NEW.store(0, Ordering::SeqCst);
    result
}
