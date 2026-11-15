use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};
static WATCH: AtomicUsize = AtomicUsize::new(0);
static FREES: AtomicUsize = AtomicUsize::new(0);
struct Heap;
unsafe impl GlobalAlloc for Heap {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        unsafe { System.alloc(l) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        if p as usize == WATCH.load(Ordering::SeqCst) {
            FREES.fetch_add(1, Ordering::SeqCst);
        }
        unsafe { System.dealloc(p, l) }
    }
}
#[global_allocator]
static HEAP: Heap = Heap;
#[allow(improper_ctypes)]
unsafe extern "C" {
    fn tcg_string_convert(v: Vec<u8>) -> String;
}
fn main() {
    for n in [0usize, 1, 5, 17, 128] {
        let mut v = Vec::with_capacity(n + 16);
        for i in 0..n {
            v.push(b'a' + (i % 26) as u8);
        }
        let ptr = v.as_ptr();
        let cap = v.capacity();
        let before = FREES.load(Ordering::SeqCst);
        WATCH.store(ptr as usize, Ordering::SeqCst);
        let s = unsafe { tcg_string_convert(v) };
        if s.len() != n || s.as_ptr() != ptr || s.capacity() != cap {
            std::process::exit(81);
        }
        for i in 0..n {
            if s.as_bytes()[i] != b'a' + (i % 26) as u8 {
                std::process::exit(82);
            }
        }
        drop(s);
        if FREES.load(Ordering::SeqCst) != before + 1 {
            std::process::exit(83);
        }
        WATCH.store(0, Ordering::SeqCst);
    }
}
