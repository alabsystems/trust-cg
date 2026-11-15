use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::{Duration, Instant};

unsafe extern "Rust" {
    fn store_u128(p: *mut u128, value: u128);
    fn store_i128(p: *mut i128, value: i128);
    fn add_u128(p: *mut u128, value: u128) -> u128;
    fn add_i128(p: *mut i128, value: i128) -> i128;
    fn load_u128_acquire(p: *const u128) -> u128;
}

#[repr(C, align(16))]
struct Slot<T>(core::cell::UnsafeCell<T>);
unsafe impl<T> Sync for Slot<T> {}

/// Keeps a value off every other value's cache line.
#[repr(C, align(128))]
struct Line<T>(T);

/// The contended-store section's shared state; only `pairs` is stored to by
/// the 128-bit operations under test.
struct Contended {
    pairs: Line<Slot<u128>>,
    stored: [Line<AtomicU64>; 2],
    deadline_ns: Line<AtomicU64>,
    done: AtomicBool,
}

const THREADS: u128 = 4;
const ADDS: u128 = 40_000;
const LOADS: usize = 200_000;
const STORE_WINDOW: Duration = Duration::from_millis(250);

fn main() {
    let mut checks = 0u64;
    // Values: every store/add result is compared with plain u128/i128 math.
    let values: [u128; 9] = [
        0,
        1,
        u128::MAX,
        1 << 127,
        (1 << 64) - 1,
        1 << 64,
        0xaaaa_aaaa_aaaa_aaaa_5555_5555_5555_5555,
        0x0123_4567_89ab_cdef_fedc_ba98_7654_3210,
        0xffff_ffff_ffff_ffff_0000_0000_0000_0001,
    ];
    for &v in &values {
        for &d in &values {
            let slot = Slot(core::cell::UnsafeCell::new(v));
            let old = unsafe { add_u128(slot.0.get(), d) };
            assert_eq!(old, v);
            assert_eq!(unsafe { *slot.0.get() }, v.wrapping_add(d));
            let islot = Slot(core::cell::UnsafeCell::new(v as i128));
            let iold = unsafe { add_i128(islot.0.get(), d as i128) };
            assert_eq!(iold, v as i128);
            assert_eq!(
                unsafe { *islot.0.get() },
                (v as i128).wrapping_add(d as i128)
            );
            unsafe { store_u128(slot.0.get(), d) };
            assert_eq!(unsafe { *slot.0.get() }, d);
            unsafe { store_i128(islot.0.get(), !(d as i128)) };
            assert_eq!(unsafe { *islot.0.get() }, !(d as i128));
            checks += 6;
        }
    }
    // Contended fetch_add: a lost update or a torn carry changes the total.
    let delta: u128 = 0x0000_0000_0000_0001_ffff_ffff_ffff_ffff;
    let shared = Arc::new(Slot(core::cell::UnsafeCell::new(0u128)));
    let workers: Vec<_> = (0..THREADS)
        .map(|_| {
            let shared = Arc::clone(&shared);
            std::thread::spawn(move || {
                for _ in 0..ADDS {
                    unsafe { add_u128(shared.0.get(), delta) };
                }
            })
        })
        .collect();
    for worker in workers {
        worker.join().unwrap();
    }
    assert_eq!(
        unsafe { *shared.0.get() },
        delta.wrapping_mul(THREADS * ADDS)
    );
    checks += 1;
    // Contended stores: writers store only hi == lo pairs while main loads; a
    // torn store (or load) shows a pair whose halves differ. Every access is
    // an exclusive-pair loop, so writers that never pause can keep breaking
    // main's LDAXP/STXP reservation: on the Linux AArch64 host the loads took
    // up to 40 s in both lanes. The writers therefore stop STORE_WINDOW after
    // main starts loading, and any loads still left run uncontended. The
    // window bounds that starvation only: a load loop that ends inside it is
    // contended throughout.
    let state = Arc::new(Contended {
        pairs: Line(Slot(core::cell::UnsafeCell::new(0u128))),
        stored: [Line(AtomicU64::new(0)), Line(AtomicU64::new(0))],
        deadline_ns: Line(AtomicU64::new(u64::MAX)),
        done: AtomicBool::new(false),
    });
    let start = Instant::now();
    let writers: Vec<_> = (0..2)
        .map(|w| {
            let state = Arc::clone(&state);
            std::thread::spawn(move || {
                let mut x = 0x9e37_79b9_7f4a_7c15u64 ^ w as u64;
                let mut n = 0u64;
                while !state.done.load(Ordering::Relaxed) {
                    if n % 256 == 0
                        && start.elapsed()
                            >= Duration::from_nanos(state.deadline_ns.0.load(Ordering::Relaxed))
                    {
                        break;
                    }
                    x = x
                        .wrapping_mul(6364136223846793005)
                        .wrapping_add(1442695040888963407);
                    let pair = (x as u128) << 64 | x as u128;
                    unsafe { store_u128(state.pairs.0.0.get(), pair) };
                    n += 1;
                    state.stored[w].0.store(n, Ordering::Relaxed);
                }
            })
        })
        .collect();
    let stored = |state: &Contended| -> u64 {
        state
            .stored
            .iter()
            .map(|count| count.0.load(Ordering::Relaxed))
            .sum()
    };
    // The window opens once both writers are storing.
    while state
        .stored
        .iter()
        .any(|count| count.0.load(Ordering::Relaxed) < 128)
    {
        std::thread::yield_now();
    }
    let before = stored(&state);
    state.deadline_ns.0.store(
        (start.elapsed() + STORE_WINDOW).as_nanos() as u64,
        Ordering::Relaxed,
    );
    let mut torn = 0u64;
    for i in 0..LOADS {
        let seen = unsafe { load_u128_acquire(state.pairs.0.0.get()) };
        if (seen >> 64) as u64 != seen as u64 {
            torn += 1;
        }
        checks += 1;
        if i % 256 == 255 {
            std::thread::yield_now();
        }
    }
    let after = stored(&state);
    state.done.store(true, Ordering::Relaxed);
    for writer in writers {
        writer.join().unwrap();
    }
    assert_eq!(torn, 0, "torn 128-bit store/load pairs");
    assert!(after > before, "the writers did not store during the loads");
    println!("PASS atomic128_store_add checks={checks}");
}
