// ---- appended by tests/slice_capabilities_3_linux.rs (`leak_checked`) ----
// A counting global allocator over `System`: the program's own `main` is
// renamed `fixture_main`, and this `main` prints the number of allocations
// still live when it returns. The bridge arm and the LLVM arm must print the
// same count (stdout's line buffer is one live allocation in both), so a
// missing drop or a double free of a held header is a different output.
mod live_alloc_counter {
    use std::alloc::{GlobalAlloc, Layout, System};
    use std::sync::atomic::{AtomicIsize, Ordering};

    pub struct Counting;
    pub static LIVE: AtomicIsize = AtomicIsize::new(0);

    unsafe impl GlobalAlloc for Counting {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            let p = unsafe { System.alloc(layout) };
            if !p.is_null() {
                LIVE.fetch_add(1, Ordering::Relaxed);
            }
            p
        }
        unsafe fn dealloc(&self, p: *mut u8, layout: Layout) {
            LIVE.fetch_sub(1, Ordering::Relaxed);
            unsafe { System.dealloc(p, layout) }
        }
        unsafe fn realloc(&self, p: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
            unsafe { System.realloc(p, layout, new_size) }
        }
    }

    pub fn live() -> isize {
        LIVE.load(Ordering::Relaxed)
    }
}

#[global_allocator]
static LIVE_ALLOC_COUNTER: live_alloc_counter::Counting = live_alloc_counter::Counting;

fn main() {
    let before = live_alloc_counter::live();
    fixture_main();
    let after = live_alloc_counter::live();
    println!("live allocations: {}", after - before);
}
