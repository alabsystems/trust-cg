extern crate c;
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};
static DROPS: AtomicUsize = AtomicUsize::new(0);
static TARGET: AtomicUsize = AtomicUsize::new(0);
static FREED: AtomicUsize = AtomicUsize::new(0);
struct Counting;
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        if TARGET
            .compare_exchange(pointer as usize, 0, Ordering::SeqCst, Ordering::SeqCst)
            .is_ok()
        {
            FREED.fetch_add(1, Ordering::SeqCst);
        }
        unsafe { System.dealloc(pointer, layout) }
    }
}
#[global_allocator]
static ALLOC: Counting = Counting;
#[unsafe(no_mangle)]
pub extern "C" fn mark_drop() {
    DROPS.fetch_add(1, Ordering::SeqCst);
}
#[unsafe(no_mangle)]
pub extern "C" fn record_buffer(pointer: usize) {
    TARGET.store(pointer, Ordering::SeqCst);
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    for method in 0u8..3 {
        for request in 0u8..3 {
            DROPS.store(0, Ordering::SeqCst);
            FREED.store(0, Ordering::SeqCst);
            TARGET.store(0, Ordering::SeqCst);
            let n = match request {
                0 => 3,
                1 => usize::MAX / 8 + usize::from(method == 0),
                _ => isize::MAX as usize / 8 + usize::from(method == 0),
            };
            let result = std::panic::catch_unwind(|| {
                c::f(std::hint::black_box(method), std::hint::black_box(n))
            });
            let accepted = match result {
                Ok(v) if request == 0 => {
                    let valid = v.len() == usize::from(method != 0)
                        && v.capacity() == if method == 0 { 3 } else { 4 }
                        && !v.as_ptr().is_null();
                    drop(v);
                    valid
                }
                Ok(v) => {
                    std::mem::forget(v);
                    false
                }
                Err(_) => request != 0,
            };
            let wanted_free = usize::from(request == 0 || method != 0);
            if !accepted
                || DROPS.load(Ordering::SeqCst) != 1
                || FREED.load(Ordering::SeqCst) != wanted_free
            {
                eprintln!(
                    "method={method}, request={request}, accepted={accepted}, drops={}, freed={}, expected_freed={wanted_free}",
                    DROPS.load(Ordering::SeqCst),
                    FREED.load(Ordering::SeqCst)
                );
                std::process::exit(2);
            }
        }
    }
}
