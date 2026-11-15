use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

static ADDRESS: AtomicUsize = AtomicUsize::new(0);
static OBSERVED: AtomicU64 = AtomicU64::new(0);
static DROPS: AtomicUsize = AtomicUsize::new(0);
static DROPPED: AtomicU64 = AtomicU64::new(0);

#[derive(Debug)]
pub struct ProbePanic;

pub fn reset() {
    ADDRESS.store(0, Ordering::SeqCst);
    OBSERVED.store(0, Ordering::SeqCst);
    DROPS.store(0, Ordering::SeqCst);
    DROPPED.store(0, Ordering::SeqCst);
}

#[inline(never)]
pub fn replace_reference<'a>(place: &mut &'a u64, new: &'a u64) {
    *place = new;
    ADDRESS.store(new as *const u64 as usize, Ordering::SeqCst);
}

#[inline(never)]
pub fn replace_value(place: &mut u64, new: u64) {
    *place = new;
    ADDRESS.store(place as *mut u64 as usize, Ordering::SeqCst);
}

#[inline(never)]
pub fn observe(place: &u64) {
    assert_eq!(place as *const u64 as usize, ADDRESS.load(Ordering::SeqCst));
    OBSERVED.store(*place, Ordering::SeqCst);
}

#[inline(never)]
pub fn record_reference_drop(place: &&u64) {
    record_value_drop(*place);
}

#[inline(never)]
pub fn record_value_drop(place: &u64) {
    assert_eq!(place as *const u64 as usize, ADDRESS.load(Ordering::SeqCst));
    DROPPED.store(*place, Ordering::SeqCst);
    DROPS.fetch_add(1, Ordering::SeqCst);
}

#[inline(never)]
pub fn may_unwind(do_panic: bool) {
    if do_panic {
        std::panic::panic_any(ProbePanic);
    }
}

#[inline(never)]
pub fn tuple_tail(do_panic: bool) -> u64 {
    may_unwind(do_panic);
    7
}

pub fn observation() -> (usize, u64, usize, u64) {
    (ADDRESS.load(Ordering::SeqCst), OBSERVED.load(Ordering::SeqCst),
        DROPS.load(Ordering::SeqCst), DROPPED.load(Ordering::SeqCst))
}
