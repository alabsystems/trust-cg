// CORPUS FIXTURE — std allocates NOTHING for a zero-length or zero-sized
// collection: `vec![x; 0]`, `repeat(0)`, `[T; 0].repeat(n)`, a
// `split_off(len)` tail, `BTreeMap::new()`, `HashMap::new()`, `Vec::new()`,
// `Box::new(())` and `Box::new([u64; 0])` all keep a dangling, aligned pointer
// and never call the allocator. With an allocator that fails EVERY request
// (armed after `println!("start ..")`), LLVM's binary therefore completes each
// row and prints `99 = 0`. A bridge model that reserves a placeholder element
// (or a map slot) reaches the allocation-error handler instead and aborts
// "memory allocation of N bytes failed".
//
// The row is the first byte of `ALLOC_SHAPE`; `z` arms nothing (the control).
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, Ordering::Relaxed};

static FAIL_ALL: AtomicBool = AtomicBool::new(false);

struct FailWhenArmed;

unsafe impl GlobalAlloc for FailWhenArmed {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        if FAIL_ALL.load(Relaxed) {
            return std::ptr::null_mut();
        }
        unsafe { System.alloc(l) }
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        if FAIL_ALL.load(Relaxed) {
            return std::ptr::null_mut();
        }
        unsafe { System.alloc_zeroed(l) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        unsafe { System.dealloc(p, l) }
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        if FAIL_ALL.load(Relaxed) {
            return std::ptr::null_mut();
        }
        unsafe { System.realloc(p, l, n) }
    }
}

#[global_allocator]
static GLOBAL: FailWhenArmed = FailWhenArmed;

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
fn show(tag: u64, v: u64) {
    println!("{tag} = {v}");
}

#[inline(never)]
fn from_elem_zero(n: usize) -> u64 {
    let v = vec![7u32; n];
    v.len() as u64
}

#[derive(Clone, Copy)]
struct P {
    a: u64,
    b: u32,
}

#[inline(never)]
fn from_elem_zero_struct(n: usize) -> u64 {
    let v = vec![P { a: 1, b: 2 }; n];
    v.len() as u64
}

#[inline(never)]
fn repeat_zero(n: usize) -> u64 {
    let v = [1u16, 2, 3].repeat(n);
    v.len() as u64
}

#[inline(never)]
fn str_repeat_zero(n: usize) -> u64 {
    let s = "abc".repeat(n);
    s.len() as u64
}

#[inline(never)]
fn repeat_empty_slice(n: usize) -> u64 {
    let e: [u64; 0] = [];
    let v = e.repeat(n);
    v.len() as u64
}

#[inline(never)]
fn split_off_at_len(v: &mut Vec<u64>) -> u64 {
    let len = v.len();
    let t = v.split_off(len);
    t.len() as u64
}

#[inline(never)]
fn btreemap_new_only() -> u64 {
    let m: std::collections::BTreeMap<u64, u64> = std::collections::BTreeMap::new();
    m.len() as u64
}

#[inline(never)]
fn hashmap_new_only() -> u64 {
    let m: std::collections::HashMap<u64, u64> = std::collections::HashMap::new();
    m.len() as u64
}

#[inline(never)]
fn vec_new_only() -> u64 {
    let v: Vec<u64> = Vec::new();
    v.len() as u64
}

#[inline(never)]
fn box_zst() -> u64 {
    let b = Box::new(());
    let c = Box::new([0u64; 0]);
    std::mem::size_of_val(&*b) as u64 + c.len() as u64
}

#[inline(never)]
fn zeroed_from_elem_zero(n: usize) -> u64 {
    let v = vec![0u8; n];
    v.len() as u64
}

fn main() {
    let which = shape();
    println!("start {which}");
    let n0 = (which as usize) & 0;
    let mut pre: Vec<u64> = vec![1, 2, 3];
    FAIL_ALL.store(which != b'z', Relaxed);
    let r = match which {
        b'a' => from_elem_zero(n0),
        b'b' => from_elem_zero_struct(n0),
        b'c' => repeat_zero(n0),
        b'd' => str_repeat_zero(n0),
        b'e' => repeat_empty_slice(5),
        b'f' => split_off_at_len(&mut pre),
        b'g' => btreemap_new_only(),
        b'h' => hashmap_new_only(),
        b'i' => vec_new_only(),
        b'j' => box_zst(),
        b'k' => zeroed_from_elem_zero(n0),
        _ => 0,
    };
    FAIL_ALL.store(false, Relaxed);
    show(99, r);
}
