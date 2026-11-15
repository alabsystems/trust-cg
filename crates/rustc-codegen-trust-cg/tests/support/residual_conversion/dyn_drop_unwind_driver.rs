use std::sync::{
    Mutex,
    atomic::{AtomicBool, AtomicUsize, Ordering},
};
static LOG: Mutex<Vec<(u64, u64, usize)>> = Mutex::new(Vec::new());
static PANIC: AtomicBool = AtomicBool::new(false);
static WATCH: AtomicUsize = AtomicUsize::new(0);
static COUNT: AtomicUsize = AtomicUsize::new(0);
static CLOCK: AtomicUsize = AtomicUsize::new(0);
static FREE: AtomicUsize = AtomicUsize::new(0);
struct Allocator;
unsafe impl std::alloc::GlobalAlloc for Allocator {
    unsafe fn alloc(&self, layout: std::alloc::Layout) -> *mut u8 {
        unsafe { std::alloc::System.alloc(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: std::alloc::Layout) {
        if ptr as usize == WATCH.load(Ordering::Relaxed) {
            COUNT.fetch_add(1, Ordering::Relaxed);
            FREE.store(CLOCK.fetch_add(1, Ordering::Relaxed), Ordering::Relaxed);
        }
        unsafe {
            std::alloc::System.dealloc(ptr, layout);
        }
    }
}
#[global_allocator]
static ALLOCATOR: Allocator = Allocator;
#[unsafe(no_mangle)]
pub extern "C" fn dyn_watch(ptr: *const u8) {
    assert_ne!(ptr as usize, 0);
    WATCH.store(ptr as usize, Ordering::Relaxed);
}
#[unsafe(no_mangle)]
pub extern "C" fn dyn_event(kind: u64, value: u64) {
    let time = CLOCK.fetch_add(1, Ordering::Relaxed);
    LOG.lock().unwrap().push((kind, value, time));
}
unsafe extern "C-unwind" fn callback(value: u64) {
    dyn_event(1, value);
    if PANIC.load(Ordering::Relaxed) {
        panic!("dynamic drop");
    }
}
struct Item(u64);
impl Drop for Item {
    fn drop(&mut self) {
        unsafe {
            callback(self.0);
        }
    }
}
unsafe extern "Rust" {
    fn check_dyn(item: Box<dyn std::any::Any>, value: u64);
}
fn main() {
    std::panic::set_hook(Box::new(|info| {
        if info.payload().downcast_ref::<&str>() != Some(&"dynamic drop") {
            eprintln!("{info}");
        }
    }));
    // Reserve before tracking allocations; the log itself must not reuse the freed address.
    LOG.lock().unwrap().reserve(8);
    let mut checks = 0;
    for seed in 0..256_u64 {
        let value = seed.wrapping_mul(0x9e3779b97f4a7c15);
        for plain in [false, true] {
            for panic in [false, true] {
                COUNT.store(0, Ordering::Relaxed);
                CLOCK.store(0, Ordering::Relaxed);
                FREE.store(usize::MAX, Ordering::Relaxed);
                PANIC.store(panic, Ordering::Relaxed);
                let item: Box<dyn std::any::Any> = if plain {
                    Box::new(value)
                } else {
                    Box::new(Item(value))
                };
                // This target's Rust trait-object ABI puts optional drop glue in slot zero.
                let (_, vtable): (*const u8, *const usize) = unsafe { std::mem::transmute(&*item) };
                assert_eq!(unsafe { *vtable } == 0, plain, "null drop slot control");
                dyn_watch(&*item as *const dyn std::any::Any as *const u8);
                let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
                    check_dyn(item, value)
                }));
                WATCH.store(0, Ordering::Relaxed);
                assert_eq!(outcome.is_err(), panic && !plain);
                assert_eq!(COUNT.load(Ordering::Relaxed), 1, "one deallocation");
                let expected = if plain {
                    vec![(2, value, 1), (5, value, 2)]
                } else if panic {
                    vec![(1, value, 0), (5, value, 2)]
                } else {
                    vec![(1, value, 0), (2, value, 2), (5, value, 3)]
                };
                assert_eq!(*LOG.lock().unwrap(), expected);
                assert_eq!(
                    FREE.load(Ordering::Relaxed),
                    if plain { 0 } else { 1 },
                    "free after drop, before caller cleanup"
                );
                LOG.lock().unwrap().clear();
                checks += 1;
            }
        }
    }
    println!("PASS indirect_dyn_drop checks={checks}");
}
