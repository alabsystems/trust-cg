// CORPUS FIXTURE — ATOMICS slice 1: x86 atomic load/store/RMW frontend hookup.
//
// Exercises the in-scope single-thread atomic surface across widths and orderings
// over `core::sync::atomic`, folding every observation into ONE exit code (mod
// 251) so the bridge-vs-LLVM differential is a pure exit-code oracle. Every op
// lowers to an already-proven trust-ir AtomicLoad / AtomicStore / AtomicRMW (ZERO
// new proofs):
//
//   * load  @ Relaxed / Acquire / SeqCst  (plain MOV r,[m] on x86 TSO)
//   * store @ Relaxed / Release           (plain MOV [m],r; SeqCst store out of
//                                           scope, stays fail-closed)
//   * fetch_add / fetch_sub / fetch_and / fetch_or / fetch_xor  (LOCK-CMPXCHG
//     retry loop; returns the OLD value; sound at every ordering)
//   * load/store widths: AtomicU8/I8, AtomicU16/I16, AtomicU32/I32, AtomicU64/
//     I64/Usize  (all opt levels)
//   * RMW widths: AtomicU32/I32/U64/I64/Usize  (all opt levels)
//
// SCOPE NOTES (kept out of this all-opt-level fixture on purpose): AtomicBool
// (`-O0` ctor bool->u8 transmute + B1/I8 return ABI — pre-existing gap; O2/O3 ok);
// NARROW (I8/I16) RMW at O2/O3 (`AtomicRmwCasLoop8/16` fixed-RAX/R10 scratch
// conflict in the encoder — backend regalloc, not frontend; O0 ok). Both stay
// fail-closed where unsupported. SeqCst store / swap / compare_exchange / fence /
// AtomicPtr / u128 remain fail-closed (slices 2-4).
//
// Single-threaded semantics are fully deterministic, so LLVM and the bridge must
// produce the identical exit code at O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::sync::atomic::{
    AtomicI16, AtomicI32, AtomicI64, AtomicU16, AtomicU32, AtomicU64, AtomicU8, AtomicUsize,
    Ordering,
};

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;

    // --- load / store round-trips across orderings and widths ---
    let a = AtomicUsize::new(7);
    a.store(41, Ordering::Relaxed);
    acc = acc.wrapping_add(a.load(Ordering::Relaxed) as u64); // 41
    a.store(3, Ordering::Release);
    acc = acc.wrapping_add(a.load(Ordering::Acquire) as u64); // 3
    acc = acc.wrapping_add(a.load(Ordering::SeqCst) as u64); // 3

    let u8v = AtomicU8::new(0);
    u8v.store(200, Ordering::Relaxed);
    acc = acc.wrapping_add(u8v.load(Ordering::Relaxed) as u64); // 200

    let i16v = AtomicI16::new(0);
    i16v.store(-1234, Ordering::Release);
    acc = acc.wrapping_add((i16v.load(Ordering::Relaxed) as i64 as u64) & 0xffff); // 0xfb2e

    let u16v = AtomicU16::new(40000);
    u16v.store(12345, Ordering::Relaxed);
    acc = acc.wrapping_add(u16v.load(Ordering::SeqCst) as u64); // 12345

    let u32v = AtomicU32::new(1000);
    u32v.store(123456, Ordering::Relaxed);
    acc = acc.wrapping_add(u32v.load(Ordering::SeqCst) as u64); // 123456

    let i32ls = AtomicI32::new(0);
    i32ls.store(-7, Ordering::Release);
    acc = acc.wrapping_add((i32ls.load(Ordering::Acquire) as i64 as u64) & 0xff); // 0xf9

    let i64ls = AtomicI64::new(0);
    i64ls.store(-1, Ordering::Relaxed);
    acc = acc.wrapping_add((i64ls.load(Ordering::Relaxed) as u64) & 0xff); // 0xff

    // --- fetch_add / fetch_sub returning the OLD value (64-bit) ---
    let c = AtomicU64::new(100);
    let old = c.fetch_add(5, Ordering::Relaxed); // old = 100
    acc = acc.wrapping_add(old); // +100
    acc = acc.wrapping_add(c.load(Ordering::Relaxed)); // now 105
    let old2 = c.fetch_sub(30, Ordering::SeqCst); // old = 105
    acc = acc.wrapping_add(old2); // +105
    acc = acc.wrapping_add(c.load(Ordering::Relaxed)); // now 75

    // --- fetch_and / fetch_or / fetch_xor at mixed orderings (32-bit) ---
    let d = AtomicU32::new(0b1100);
    acc = acc.wrapping_add(d.fetch_and(0b1010, Ordering::AcqRel) as u64); // old 12
    acc = acc.wrapping_add(d.load(Ordering::Relaxed) as u64); // 0b1000 = 8
    acc = acc.wrapping_add(d.fetch_or(0b0001, Ordering::Release) as u64); // old 8
    acc = acc.wrapping_add(d.load(Ordering::Relaxed) as u64); // 0b1001 = 9
    acc = acc.wrapping_add(d.fetch_xor(0b1111, Ordering::Acquire) as u64); // old 9
    acc = acc.wrapping_add(d.load(Ordering::Relaxed) as u64); // 0b0110 = 6

    // --- signed 32-bit RMW ---
    let e = AtomicI32::new(-10);
    let _ = e.fetch_add(3, Ordering::Relaxed); // -7
    acc = acc.wrapping_add((e.load(Ordering::Relaxed) as i64 as u64) & 0xff); // 0xf9

    // --- an Arc-style refcount increment/decrement loop over a shared counter ---
    let rc = AtomicUsize::new(1);
    for _ in 0..10 {
        rc.fetch_add(1, Ordering::Relaxed);
    }
    for _ in 0..4 {
        rc.fetch_sub(1, Ordering::Release);
    }
    acc = acc.wrapping_add(rc.load(Ordering::Acquire) as u64); // 1 + 10 - 4 = 7

    // --- i64 width RMW ---
    let h = AtomicI64::new(1_000_000);
    let _ = h.fetch_add(2_000_000, Ordering::SeqCst); // 3_000_000
    acc = acc.wrapping_add((h.load(Ordering::Relaxed) as u64) & 0xff); // 3_000_000 & 0xff

    (acc % 251) as i32
}
