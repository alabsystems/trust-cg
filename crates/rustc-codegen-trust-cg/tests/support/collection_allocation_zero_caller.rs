extern crate c;
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
static ARMED: AtomicBool = AtomicBool::new(false);
static ALLOCS: AtomicUsize = AtomicUsize::new(0);
struct Counting;
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if ARMED.load(Ordering::SeqCst) {
            ALLOCS.fetch_add(1, Ordering::SeqCst);
        }
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        unsafe { System.dealloc(pointer, layout) }
    }
}
#[global_allocator]
static ALLOC: Counting = Counting;
fn main() {
    ARMED.store(true, Ordering::SeqCst);
    let good = {
        let a = c::vnew();
        let b = c::vzero();
        let c = c::snew();
        let d = c::szero();
        a.is_empty()
            && b.is_empty()
            && c.is_empty()
            && d.is_empty()
            && a.capacity() == 0
            && b.capacity() == 0
            && c.capacity() == 0
            && d.capacity() == 0
            && !a.as_ptr().is_null()
            && !b.as_ptr().is_null()
            && !c.as_ptr().is_null()
            && !d.as_ptr().is_null()
    };
    ARMED.store(false, Ordering::SeqCst);
    if !good || ALLOCS.load(Ordering::SeqCst) != 0 {
        std::process::exit(2);
    }
}
