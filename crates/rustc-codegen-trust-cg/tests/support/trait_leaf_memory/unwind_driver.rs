use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::SeqCst};
static ENABLED: AtomicBool = AtomicBool::new(false);
static CALLS: AtomicUsize = AtomicUsize::new(0);
static DROPS: AtomicUsize = AtomicUsize::new(0);
#[unsafe(no_mangle)]
pub extern "C" fn note_drop() {
    DROPS.fetch_add(1, SeqCst);
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn maybe_panic() {
    CALLS.fetch_add(1, SeqCst);
    if ENABLED.load(SeqCst) {
        std::panic::panic_any(123_u64);
    }
}
unsafe extern "C-unwind" {
    fn projected_trait_wrapper(seed: u64, value: u64, storage: *mut u64) -> u64;
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    for enabled in [false, true] {
        ENABLED.store(enabled, SeqCst);
        CALLS.store(0, SeqCst);
        DROPS.store(0, SeqCst);
        let mut storage = [0x7192_3344_5506_aabb, 0, 0xcd17_0511_1000_789a];
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
            projected_trait_wrapper(14, 7, &mut storage[1])
        }));
        if enabled {
            assert_eq!(*result.unwrap_err().downcast::<u64>().unwrap(), 123);
        } else {
            assert_eq!(result.unwrap(), 39);
        }
        assert_eq!(storage[1], if enabled { 14 } else { 22 });
        assert_eq!(DROPS.load(SeqCst), 1);
        assert_eq!(CALLS.load(SeqCst), 1);
        assert_eq!(storage[0], 0x7192_3344_5506_aabb);
        assert_eq!(storage[2], 0xcd17_0511_1000_789a);
    }
    println!("PASS trait_leaf_unwind checks=12");
}
