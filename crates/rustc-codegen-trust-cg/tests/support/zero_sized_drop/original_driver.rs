use std::sync::atomic::{AtomicUsize, Ordering};
static DROPS: AtomicUsize = AtomicUsize::new(0);
static CALLS: AtomicUsize = AtomicUsize::new(0);
unsafe extern "C-unwind" {
    fn try_pair(enabled: u64) -> u64;
    fn try_single(enabled: u64) -> u64;
}
#[unsafe(no_mangle)]
pub extern "C" fn note_drop() {
    DROPS.fetch_add(1, Ordering::SeqCst);
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn maybe_panic(item: u64, enabled: u64) {
    CALLS.fetch_add(1, Ordering::SeqCst);
    if enabled != 0 && item == 2 {
        std::panic::panic_any(123_u64);
    }
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    for pair in [false, true] {
        for enabled in [0, 1] {
            DROPS.store(0, Ordering::SeqCst);
            CALLS.store(0, Ordering::SeqCst);
            let result = std::panic::catch_unwind(|| unsafe {
                if pair {
                    try_pair(enabled)
                } else {
                    try_single(enabled)
                }
            });
            if enabled == 0 {
                let mut expected = 7_u64;
                for item in 0..if pair { 4 } else { 5 } {
                    expected = expected * 3 + item;
                }
                assert_eq!(result.unwrap(), expected);
            } else {
                assert_eq!(*result.unwrap_err().downcast::<u64>().unwrap(), 123);
            }
            assert_eq!(DROPS.load(Ordering::SeqCst), 1);
            assert_eq!(
                CALLS.load(Ordering::SeqCst),
                if enabled == 0 { 5 } else { 3 }
            );
        }
    }
    println!("PASS try_fold_unwind checks=12");
}
