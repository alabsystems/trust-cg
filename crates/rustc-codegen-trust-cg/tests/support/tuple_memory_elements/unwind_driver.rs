use std::sync::atomic::{AtomicU64, Ordering::SeqCst};
static DROPS: AtomicU64 = AtomicU64::new(0);
static CALLS: AtomicU64 = AtomicU64::new(0);
static TAG: AtomicU64 = AtomicU64::new(0);
static EVENTS: AtomicU64 = AtomicU64::new(0);
static PANIC: AtomicU64 = AtomicU64::new(0);
#[unsafe(no_mangle)]
pub extern "C" fn record_drop(tag: u64) {
    DROPS.fetch_add(1, SeqCst);
    TAG.store(tag, SeqCst);
    EVENTS.store(EVENTS.load(SeqCst) * 10 + 1, SeqCst);
}
#[unsafe(no_mangle)]
pub unsafe extern "C-unwind" fn cleanup_callback(value: u64) -> u64 {
    CALLS.fetch_add(1, SeqCst);
    EVENTS.store(EVENTS.load(SeqCst) * 10 + 2, SeqCst);
    if PANIC.load(SeqCst) != 0 {
        std::panic::panic_any(0x4321u64 ^ value);
    }
    value.wrapping_mul(3).wrapping_add(5)
}
unsafe extern "C-unwind" {
    fn conditional_drop(value: u64) -> u64;
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut checks = 0;
    for panic in 0..2 {
        for value in 0..32 {
            DROPS.store(0, SeqCst);
            CALLS.store(0, SeqCst);
            TAG.store(0, SeqCst);
            EVENTS.store(0, SeqCst);
            PANIC.store(panic, SeqCst);
            let result = std::panic::catch_unwind(|| unsafe { conditional_drop(value) });
            if panic == 0 {
                assert_eq!(result.unwrap(), value * 3 + 5);
            } else {
                assert_eq!(
                    *result.unwrap_err().downcast::<u64>().unwrap(),
                    0x4321 ^ value
                );
            }
            checks += 1;
            assert_eq!(DROPS.load(SeqCst), 1);
            checks += 1;
            assert_eq!(CALLS.load(SeqCst), 1);
            checks += 1;
            assert_eq!(TAG.load(SeqCst), value ^ 0x1234 ^ 0xabcd);
            checks += 1;
            assert_eq!(EVENTS.load(SeqCst), if value & 1 == 0 { 12 } else { 21 });
            checks += 1;
        }
    }
    println!("PASS cleanup_bool_flag checks={checks}");
}
