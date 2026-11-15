use std::sync::atomic::{AtomicU64, Ordering};
static EVENTS: AtomicU64 = AtomicU64::new(0);
#[unsafe(no_mangle)]
pub extern "C" fn fat_event(value: u64) { EVENTS.fetch_add(value, Ordering::Relaxed); }
unsafe extern "Rust" {
    fn virtual_str(op: &dyn Fn(&str, u64, bool) -> u64, text: &str, seed: u64, fail: bool) -> u64;
    fn virtual_slice(op: &mut dyn FnMut(&mut [u64], u64, bool) -> u64, data: &mut [u64], seed: u64, fail: bool) -> u64;
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let string = |text: &str, seed: u64, fail: bool| {
        if fail { std::panic::panic_any(seed); }
        seed.wrapping_add(text.len() as u64).wrapping_add(text.as_bytes()[0] as u64)
    };
    let mut hits = 0;
    let mut slice = |data: &mut [u64], seed: u64, fail: bool| {
        hits += 1;
        data[0] = seed;
        if fail { std::panic::panic_any(seed); }
        seed.wrapping_add(data.len() as u64)
    };
    for seed in 0..128 {
        for fail in [false,true] {
            EVENTS.store(0, Ordering::Relaxed);
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe { virtual_str(&string, "bonjour", seed, fail) }));
            if fail { assert_eq!(*result.unwrap_err().downcast::<u64>().unwrap(), seed); }
            else { assert_eq!(result.unwrap(), seed+7+98); }
            assert_eq!(EVENTS.load(Ordering::Relaxed), 1);
            EVENTS.store(0, Ordering::Relaxed);
            let mut data=[0;5];
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe { virtual_slice(&mut slice, &mut data, seed, fail) }));
            if fail { assert_eq!(*result.unwrap_err().downcast::<u64>().unwrap(), seed); }
            else { assert_eq!(result.unwrap(), seed+5); }
            assert_eq!(data[0],seed);
            assert_eq!(EVENTS.load(Ordering::Relaxed), 1);
        }
    }
    assert_eq!(hits,256);
    println!("PASS fat_fn checks=1281 panics=256");
}
