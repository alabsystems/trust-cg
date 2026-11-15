// CORPUS FIXTURE — what each bridge-modelled constructor asks the global
// allocator for, counted by a `#[global_allocator]` (calls to `alloc`,
// `alloc_zeroed` and `dealloc`, and the bytes requested), against LLVM's
// binary built from the same std:
//
//   * `vec![0; n]` (any `IsZero` element whose bits are zero) takes
//     `RawVec::with_capacity_zeroed`, i.e. `alloc_zeroed`; any other element,
//     `-0.0` and a struct included, takes `alloc` and a fill;
//   * empty `vec![x; 0]` / `repeat(0)` / `split_off(len)`, a ZST `Box` and an
//     empty `BTreeMap` / `HashMap` request nothing and free nothing;
//   * `collect()` from an exact-size iterator requests exactly its length.
//
// Before the fix the bridge called `alloc` for `vec![0u8; n]`, made a
// one-element request for each empty constructor, freed the dangling pointer
// of a ZST box, and requested `MIN_NON_ZERO_CAP`-doubling buffers for
// `collect()`.
//
// `ALLOC_SHAPE` (first byte) selects the row; each row resets the counters,
// runs, and prints them with the row's result.
use std::alloc::{GlobalAlloc, Layout, System};
use std::hint::black_box as bb;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

static ALLOCS: AtomicUsize = AtomicUsize::new(0);
static ZEROED: AtomicUsize = AtomicUsize::new(0);
static DEALLOCS: AtomicUsize = AtomicUsize::new(0);
static BYTES: AtomicUsize = AtomicUsize::new(0);

struct Counting;

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        ALLOCS.fetch_add(1, Relaxed);
        BYTES.fetch_add(l.size(), Relaxed);
        unsafe { System.alloc(l) }
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        ZEROED.fetch_add(1, Relaxed);
        BYTES.fetch_add(l.size(), Relaxed);
        unsafe { System.alloc_zeroed(l) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        DEALLOCS.fetch_add(1, Relaxed);
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
    ZEROED.store(0, Relaxed);
    DEALLOCS.store(0, Relaxed);
    BYTES.store(0, Relaxed);
}

#[inline(never)]
fn report(r: u64) {
    let a = ALLOCS.load(Relaxed);
    let z = ZEROED.load(Relaxed);
    let d = DEALLOCS.load(Relaxed);
    let b = BYTES.load(Relaxed);
    println!("allocs={a} zeroed={z} deallocs={d} bytes={b} r={r}");
}

#[inline(never)]
fn zeroed_bytes(n: usize) -> u64 {
    let z = vec![0u8; n];
    let f = vec![1u8; n];
    let kept = keep(z.as_ptr() as usize) + keep(f.as_ptr() as usize);
    kept + z[n - 1] as u64 + f[n - 1] as u64
}

#[inline(never)]
fn zeroed_words(n: usize) -> u64 {
    let z = vec![0u64; n];
    let f = vec![3u64; n];
    let kept = keep(z.as_ptr() as usize) + keep(f.as_ptr() as usize);
    kept + z[n - 1] + f[n - 1]
}

#[inline(never)]
fn zeroed_floats(n: usize) -> u64 {
    let z = vec![0.0f64; n];
    let neg = vec![-0.0f64; n];
    let kept = keep(z.as_ptr() as usize) + keep(neg.as_ptr() as usize);
    kept + (z[n - 1] + neg[n - 1]) as u64 + neg[0].is_sign_negative() as u64
}

/// Lets each buffer's address escape, so LLVM keeps the allocation.
#[inline(never)]
fn keep(address: usize) -> u64 {
    bb(address) as u64 & 0
}

#[derive(Clone, Copy)]
struct P {
    a: u64,
    b: u32,
}

#[inline(never)]
fn zeroed_aggregates(n: usize) -> u64 {
    let t = vec![(0u32, 0u16); n];
    let s = vec![P { a: 0, b: 0 }; n];
    let u = vec![(0u32, 1u16); n];
    let kept = keep(t.as_ptr() as usize) + keep(s.as_ptr() as usize) + keep(u.as_ptr() as usize);
    kept + t[n - 1].0 as u64 + s[n - 1].a + s[n - 1].b as u64 + u[n - 1].1 as u64
}

#[inline(never)]
fn empties(n: usize) -> u64 {
    let a = vec![7u32; n];
    let b = [1u8, 2].repeat(n);
    let mut c: Vec<u64> = vec![1, 2, 3];
    let len = c.len();
    let t = c.split_off(len);
    let s = "ab".repeat(n);
    (a.len() + b.len() + t.len() + s.len()) as u64
}

#[inline(never)]
fn zst_boxes() -> u64 {
    let a = Box::new(());
    let b = Box::new([0u64; 0]);
    let kept = keep(&*a as *const () as usize) + keep(b.as_ptr() as usize);
    kept + std::mem::size_of_val(&*a) as u64 + b.len() as u64
}

#[inline(never)]
fn collect_exact(a: &[u64]) -> u64 {
    let v: Vec<u64> = a.iter().copied().collect();
    let r: Vec<u64> = (0..a.len() as u64).collect();
    let kept = keep(v.as_ptr() as usize) + keep(r.as_ptr() as usize);
    kept + v.len() as u64 + r.capacity() as u64
}

#[inline(never)]
fn empty_maps() -> u64 {
    let b: std::collections::BTreeMap<u64, u64> = std::collections::BTreeMap::new();
    let h: std::collections::HashMap<u64, u64> = std::collections::HashMap::new();
    b.len() as u64 + h.len() as u64
}

fn main() {
    let which = shape();
    println!("start {which}");
    let k = (which as usize) & 0;
    let src = [3u64, 4, 5, 6, 7];
    reset();
    let r = match which {
        b'a' => zeroed_bytes(100 + k),
        b'b' => zeroed_words(5 + k),
        b'c' => zeroed_floats(4 + k),
        b'd' => zeroed_aggregates(3 + k),
        b'e' => empties(k),
        b'f' => zst_boxes(),
        b'g' => collect_exact(&src[..3 + k]),
        b'h' => empty_maps(),
        _ => 0,
    };
    report(r);
}
