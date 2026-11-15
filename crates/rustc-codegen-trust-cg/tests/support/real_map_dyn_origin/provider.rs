use std::alloc::{GlobalAlloc, Layout, System};
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};

pub type Map = BTreeMap<u64, u64>;
static TARGET: AtomicUsize = AtomicUsize::new(0);
static FREES: AtomicUsize = AtomicUsize::new(0);
static BAD_LAYOUT: AtomicUsize = AtomicUsize::new(0);

struct Tracking;
unsafe impl GlobalAlloc for Tracking {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { System.alloc(layout) }
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        unsafe { System.alloc_zeroed(layout) }
    }
    unsafe fn realloc(&self, p: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        unsafe { System.realloc(p, layout, size) }
    }
    unsafe fn dealloc(&self, p: *mut u8, layout: Layout) {
        if p as usize == TARGET.load(Ordering::SeqCst) {
            let prior = FREES.fetch_add(1, Ordering::SeqCst);
            let real = Layout::new::<Map>();
            if layout != real {
                BAD_LAYOUT.fetch_add(1, Ordering::SeqCst);
            }
            // Observe erroneous attempts without adding allocator UB to the
            // diagnostic: this address was allocated for exactly one real Map.
            // Count a repeated free, but physically release this target once.
            if prior == 0 {
                unsafe { System.dealloc(p, real) };
            }
            return;
        }
        unsafe { System.dealloc(p, layout) }
    }
}
#[global_allocator]
static ALLOCATOR: Tracking = Tracking;

#[inline(never)]
pub fn make_map(filled: bool) -> Box<Map> {
    let mut map = Map::new();
    if std::hint::black_box(filled) {
        map.insert(11, 101);
        map.insert(29, 203);
    }
    let value = Box::new(map);
    FREES.store(0, Ordering::SeqCst);
    BAD_LAYOUT.store(0, Ordering::SeqCst);
    TARGET.store((&*value as *const Map) as usize, Ordering::SeqCst);
    value
}

#[inline(never)]
pub fn observation() -> (usize, usize) {
    (
        FREES.load(Ordering::SeqCst),
        BAD_LAYOUT.load(Ordering::SeqCst),
    )
}

#[inline(never)]
pub fn map_layout() -> (usize, usize) {
    (std::mem::size_of::<Map>(), std::mem::align_of::<Map>())
}
