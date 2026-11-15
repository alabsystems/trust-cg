#![feature(core_intrinsics)]
#![allow(internal_features)]
use core::intrinsics::{AtomicOrdering, atomic_store};
use std::cell::UnsafeCell;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Barrier};
unsafe extern "Rust" {
    fn load_u128_relaxed(p: *const u128) -> u128;
    fn load_u128_acquire(p: *const u128) -> u128;
    fn load_u128_seqcst(p: *const u128) -> u128;
    fn load_i128_relaxed(p: *const i128) -> i128;
    fn load_i128_acquire(p: *const i128) -> i128;
    fn load_i128_seqcst(p: *const i128) -> i128;
}
#[repr(C, align(16))]
struct Shared {
    value: UnsafeCell<u128>,
    stop: AtomicBool,
    progress: AtomicU64,
    start: Barrier,
}
// Every access to value after publication is a 128-bit atomic operation.
unsafe impl Sync for Shared {}
fn main() {
    let mut checks = 0;
    for mode in 0..6 {
        let state = Arc::new(Shared {
            value: UnsafeCell::new(0),
            stop: AtomicBool::new(false),
            progress: AtomicU64::new(0),
            start: Barrier::new(2),
        });
        assert_eq!(state.value.get() as usize % 16, 0);
        let writer_state = state.clone();
        let writer = std::thread::spawn(move || {
            writer_state.start.wait();
            let mut n = 0u64;
            let mut writes = 0u64;
            while !writer_state.stop.load(Ordering::Acquire) {
                n = n.wrapping_add(0x9e3779b97f4a7c15);
                let bits = (n as u128) << 64 | n as u128;
                unsafe {
                    atomic_store::<u128, { AtomicOrdering::Release }>(
                        writer_state.value.get(),
                        bits,
                    );
                }
                writes += 1;
                writer_state.progress.store(writes, Ordering::Release);
            }
            writes
        });
        state.start.wait();
        while state.progress.load(Ordering::Acquire) < 128 {
            std::thread::yield_now();
        }
        let before = state.progress.load(Ordering::Acquire);
        for i in 0..32768 {
            let p = state.value.get();
            let bits = unsafe {
                match mode {
                    0 => load_u128_relaxed(p),
                    1 => load_u128_acquire(p),
                    2 => load_u128_seqcst(p),
                    3 => load_i128_relaxed(p.cast()) as u128,
                    4 => load_i128_acquire(p.cast()) as u128,
                    5 => load_i128_seqcst(p.cast()) as u128,
                    _ => unreachable!(),
                }
            };
            assert_eq!(
                bits as u64,
                (bits >> 64) as u64,
                "torn read mode={mode} iteration={i}"
            );
            checks += 1;
            if i % 256 == 0 {
                std::thread::yield_now();
            }
        }
        let after = state.progress.load(Ordering::Acquire);
        state.stop.store(true, Ordering::Release);
        let writes = writer.join().unwrap();
        assert!(
            after > before,
            "writer did not advance during the reader loop"
        );
        assert!(writes >= after);
    }
    assert_eq!(checks, 196608);
    println!("PASS atomic128_load_contention checks={checks}");
}
