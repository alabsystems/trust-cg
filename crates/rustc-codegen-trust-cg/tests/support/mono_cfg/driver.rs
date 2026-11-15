use std::sync::atomic::{AtomicU64, Ordering};
static LAST: AtomicU64 = AtomicU64::new(0);
static CALLS: AtomicU64 = AtomicU64::new(0);
#[unsafe(no_mangle)]
pub fn observe(value: u64, marker: u64) -> u64 {
    LAST.store(marker, Ordering::Relaxed);
    CALLS.fetch_add(1, Ordering::Relaxed);
    value.rotate_right(marker as u32) ^ marker
}
unsafe extern "Rust" {
    fn mono_0(value: u64, dynamic: bool) -> u64;
    fn mono_1(value: u64, dynamic: bool) -> u64;
    fn mono_2(value: u64, dynamic: bool) -> u64;
    fn mono_3(value: u64, dynamic: bool) -> u64;
    fn mono_4(value: u64, dynamic: bool) -> u64;
    fn mono_5(value: u64, dynamic: bool) -> u64;
    fn mono_63(value: u64, dynamic: bool) -> u64;
    fn mono_64(value: u64, dynamic: bool) -> u64;
    fn mono_drop_word(value: *mut u64);
    fn mono_drop_slice(value: *mut [u32]);
    fn mono_drop_zst(value: *mut ());
    fn mono_drop_fn() -> unsafe fn(*mut u64);
    fn mono_live_drop(value: u64);
}
fn main() {
    let functions: [(usize, unsafe extern "Rust" fn(u64, bool) -> u64); 8] = [
        (0, mono_0),
        (1, mono_1),
        (2, mono_2),
        (3, mono_3),
        (4, mono_4),
        (5, mono_5),
        (63, mono_63),
        (64, mono_64),
    ];
    let mut random = 0x91e10da5c79e7b1du64;
    let mut checks = 0;
    for index in 0..4096 {
        random ^= random << 13;
        random ^= random >> 7;
        random ^= random << 17;
        let x = [0, 1, u64::MAX, 1 << 63, (1 << 63) - 1]
            .get(index)
            .copied()
            .unwrap_or(random);
        for (n, f) in functions {
            let value = match n % 3 {
                0 if n < 3 => x.wrapping_add(n as u64 + 7),
                0 => x.rotate_left(n as u32),
                1 => x ^ (n as u64).wrapping_mul(0x123456789),
                _ => x.wrapping_mul(n as u64 + 3),
            };
            for dynamic in [false, true] {
                let before = CALLS.load(Ordering::Relaxed);
                let marker = if dynamic { 17 } else { 29 };
                assert_eq!(
                    unsafe { f(x, dynamic) },
                    value.rotate_right(marker as u32) ^ marker
                );
                assert_eq!(LAST.load(Ordering::Relaxed), marker);
                assert_eq!(CALLS.load(Ordering::Relaxed), before + 1);
                checks += 1;
            }
        }
        let before = CALLS.load(Ordering::Relaxed);
        let mut word = x;
        let mut array = [x as u32, (x >> 32) as u32, 7];
        unsafe {
            mono_drop_word(&mut word);
            mono_drop_slice(&mut array[..]);
            mono_drop_slice(&mut array[..0]);
            mono_drop_zst(&mut ());
            mono_drop_fn()(&mut word);
        }
        assert_eq!(word, x);
        assert_eq!(array, [x as u32, (x >> 32) as u32, 7]);
        assert_eq!(CALLS.load(Ordering::Relaxed), before);
        unsafe { mono_live_drop(x) };
        assert_eq!(LAST.load(Ordering::Relaxed), 43);
        assert_eq!(CALLS.load(Ordering::Relaxed), before + 1);
        checks += 6;
    }
    assert_eq!(checks, 90112);
    println!("PASS mono_cfg checks={checks}");
}
