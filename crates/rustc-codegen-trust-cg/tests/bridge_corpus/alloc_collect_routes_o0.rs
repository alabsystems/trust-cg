// CORPUS FIXTURE — the `SpecFromIter` route std's `collect()` takes, observed
// through `capacity()` and a counting `#[global_allocator]`, for the shapes
// the bridge compiles only at -O0 (`StepBy` is refused by name past -O0, the
// owning `vec::IntoIter` source past -O1):
//
//   * `v.into_iter().map(..)` / `.filter(..)` into the same element layout
//     collects IN PLACE (in_place_collect.rs): the source buffer and its
//     capacity are reused, nothing is allocated or freed;
//   * `v.into_iter().collect()` reuses the buffer unless the iterator has
//     advanced and holds less than half its capacity, in which case it
//     appends to a fresh `reserve(len)` buffer and frees the source;
//   * a layout-changing `map` (`u64 -> u32`) or a `rev()` is not in-place:
//     `TrustedLen` sizing (`with_capacity(n)`), then the source is freed;
//   * `step_by` over a `TrustedRandomAccess` range or slice iterator, and a
//     `chain` of two ranges, are `TrustedLen`: `with_capacity` of the exact
//     remaining count (the range chain is also refused past -O0).
//
// Before the fix the bridge pushed every one of these into a fresh buffer
// grown from `MIN_NON_ZERO_CAP` and leaked the source buffer.
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

static ALLOCS: AtomicUsize = AtomicUsize::new(0);
static DEALLOCS: AtomicUsize = AtomicUsize::new(0);
static BYTES: AtomicUsize = AtomicUsize::new(0);

struct Counting;

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        ALLOCS.fetch_add(1, Relaxed);
        BYTES.fetch_add(l.size(), Relaxed);
        unsafe { System.alloc(l) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        DEALLOCS.fetch_add(1, Relaxed);
        BYTES.fetch_add(l.size() << 32, Relaxed);
        unsafe { System.dealloc(p, l) }
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

unsafe extern "C" {
    fn getenv(name: *const u8) -> *const u8;
}

fn shape() -> u8 {
    unsafe {
        let p = getenv(b"ALLOC_SHAPE\0".as_ptr());
        if p.is_null() { 0 } else { *p }
    }
}

#[inline(never)]
fn reset() {
    ALLOCS.store(0, Relaxed);
    DEALLOCS.store(0, Relaxed);
    BYTES.store(0, Relaxed);
}

/// `freed` packs the freed byte count above bit 32 of `BYTES`.
#[inline(never)]
fn report(cap: u64, sum: u64) {
    let a = ALLOCS.load(Relaxed);
    let d = DEALLOCS.load(Relaxed);
    let b = BYTES.load(Relaxed);
    let requested = b & 0xffff_ffff;
    let freed = b >> 32;
    println!("allocs={a} deallocs={d} requested={requested} freed={freed} cap={cap} sum={sum}");
}

#[inline(never)]
fn sum64(v: &[u64]) -> u64 {
    let mut s = 0u64;
    let mut i = 0;
    while i < v.len() {
        s = s.wrapping_mul(31).wrapping_add(v[i]);
        i += 1;
    }
    s
}

#[inline(never)]
fn into_iter_map(n: u64) {
    let v: Vec<u64> = vec![1, 2, 3, n];
    reset();
    let w: Vec<u64> = v.into_iter().map(|x| x * 2).collect();
    report(w.capacity() as u64, sum64(&w));
}

#[inline(never)]
fn into_iter_filter(n: u64) {
    let v: Vec<u64> = vec![1, 2, 3, n, 5, 6];
    reset();
    let w: Vec<u64> = v.into_iter().filter(|x| x % 2 == 1).collect();
    report(w.capacity() as u64, sum64(&w));
}

#[inline(never)]
fn into_iter_direct(n: u64) {
    let v: Vec<u64> = vec![1, 2, 3, n];
    reset();
    let w: Vec<u64> = v.into_iter().collect();
    report(w.capacity() as u64, sum64(&w));
}

#[inline(never)]
fn into_iter_advanced(n: u64, skip: usize) {
    let v: Vec<u64> = vec![1, 2, 3, 4, 5, 6, 7, n];
    let mut it = v.into_iter();
    let mut i = 0;
    while i < skip {
        it.next();
        i += 1;
    }
    reset();
    let w: Vec<u64> = it.collect();
    report(w.capacity() as u64, sum64(&w));
}

#[inline(never)]
fn into_iter_narrowing(n: u64) {
    let v: Vec<u64> = vec![1, 2, 3, n, 5];
    reset();
    let w: Vec<u32> = v.into_iter().map(|x| x as u32).collect();
    let mut s = 0u64;
    let mut i = 0;
    while i < w.len() {
        s = s * 31 + w[i] as u64;
        i += 1;
    }
    report(w.capacity() as u64, s);
}

#[inline(never)]
fn into_iter_rev(n: u64) {
    let v: Vec<u64> = vec![1, 2, 3, n, 5];
    reset();
    let w: Vec<u64> = v.into_iter().rev().collect();
    report(w.capacity() as u64, sum64(&w));
}

#[inline(never)]
fn step_by_range(n: u64) {
    reset();
    let v: Vec<u64> = (0..n).step_by(3).collect();
    let w: Vec<u64> = (1..n).step_by(4).collect();
    report(
        v.capacity() as u64 * 100 + w.capacity() as u64,
        sum64(&v) + sum64(&w),
    );
}

#[inline(never)]
fn step_by_slice(a: &[u64]) {
    reset();
    let v: Vec<u64> = a.iter().copied().step_by(2).collect();
    report(v.capacity() as u64, sum64(&v));
}

// Row `k`: a `StepBy` (or a `Skip` over a reversed range) ABOVE a `.rev()` is not `TrustedLen` (`Rev` has no
// `TrustedRandomAccess`): std reserves `max(MIN_NON_ZERO_CAP, n)` at the first
// element, not exactly `n`.
#[inline(never)]
fn step_by_above_rev(a: &[u64], n: u64) {
    reset();
    let v: Vec<u64> = a.iter().rev().step_by(2).copied().collect();
    let w: Vec<u64> = (0..n).rev().step_by(4).collect();
    let x: Vec<u64> = (0..n).rev().skip(8).collect();
    report(
        v.capacity() as u64 * 10000 + w.capacity() as u64 * 100 + x.capacity() as u64,
        sum64(&v) + sum64(&w) + sum64(&x),
    );
}

#[inline(never)]
fn chain_ranges(n: u64) {
    reset();
    let v: Vec<u64> = (0..n).chain(5..7).collect();
    report(v.capacity() as u64, sum64(&v));
}

fn main() {
    let which = shape();
    println!("start {which}");
    let k = (which as u64) & 0;
    let src = [1u64, 2, 3, 4, 5, 6, 7];
    match which {
        b'a' => into_iter_map(4 + k),
        b'b' => into_iter_filter(4 + k),
        b'c' => into_iter_direct(4 + k),
        b'd' => into_iter_advanced(8 + k, 3),
        b'e' => into_iter_advanced(8 + k, 6),
        b'f' => into_iter_narrowing(4 + k),
        b'g' => into_iter_rev(4 + k),
        b'h' => step_by_range(10 + k),
        b'i' => step_by_slice(&src),
        b'j' => chain_ranges(3 + k),
        b'k' => step_by_above_rev(&src[..5], 10 + k),
        _ => {}
    }
    println!("end");
}
