// CORPUS FIXTURE — ATOMICS slice 2: swap + SOUND SeqCst store + NARROW-width RMW.
//
// Extends slice 1 with the backend pieces that were previously fail-closed:
//
//   * swap()  -> atomic_xchg  (all widths/orderings): routed through the LOCK-
//     CMPXCHG retry loop pseudo (the bare XCHG fast path was DELETED — it had no
//     per-instruction proof). Cert-covered by AtomicRmwCasLoop_Xchg_I{8,16,32,64}
//     (old-value return + new-memory == operand). Returns the OLD value.
//
//   * store @ SeqCst: now SOUND (was a ud2 trap in slice 1). Lowered as an atomic
//     XCHG-and-discard (Inst::AtomicRMW { Xchg }, result dropped) — the standard
//     C++-on-x86 SeqCst-store mapping (a locked exchange that writes the value AND
//     is a full barrier). The store effect is the Xchg `updates memory` proof.
//
//   * NARROW (I8/I16) fetch_* / swap at O2/O3: the AtomicRmwCasLoop8/16 fixed
//     RAX/R10 clobber is now DECLARED to the register allocator (the byte/word
//     alias AL/AX now maps to its parent RAX for the implicit-def), so the
//     allocator no longer places the source/base into RAX and the encoder's
//     fixed-register conflict never fires. Works at all opt levels.
//
// Everything folds into ONE exit code (mod 251) so the bridge-vs-LLVM differential
// is a pure exit-code oracle, deterministic single-thread => identical at O0/O2/O3.
//
// STILL fail-closed (slices 3-4): compare_exchange (bare Cmpxchg, no proof),
// fence (retracted MFENCE), AtomicPtr, u128/non-scalar, unknown ordering.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::sync::atomic::{
    AtomicI16, AtomicI32, AtomicI64, AtomicI8, AtomicU16, AtomicU32, AtomicU64, AtomicU8,
    AtomicUsize, Ordering,
};

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;

    // --- swap() returns the OLD value; the new value is stored (64-bit) ---
    let a = AtomicUsize::new(10);
    let old_a = a.swap(99, Ordering::SeqCst); // old = 10
    acc = acc.wrapping_add(old_a as u64); // +10
    acc = acc.wrapping_add(a.load(Ordering::Relaxed) as u64); // now 99

    // --- swap at every ordering (32-bit) ---
    let b = AtomicU32::new(1);
    acc = acc.wrapping_add(b.swap(2, Ordering::Relaxed) as u64); // old 1
    acc = acc.wrapping_add(b.swap(3, Ordering::Acquire) as u64); // old 2
    acc = acc.wrapping_add(b.swap(4, Ordering::Release) as u64); // old 3
    acc = acc.wrapping_add(b.swap(5, Ordering::AcqRel) as u64); // old 4
    acc = acc.wrapping_add(b.load(Ordering::Relaxed) as u64); // now 5

    // --- signed swap (32-bit) ---
    let c = AtomicI32::new(-100);
    acc = acc.wrapping_add((c.swap(7, Ordering::SeqCst) as i64 as u64) & 0xff); // old -100
    acc = acc.wrapping_add((c.load(Ordering::Relaxed) as i64 as u64) & 0xff); // now 7

    // --- 64-bit swap ---
    let d = AtomicI64::new(1_000);
    acc = acc.wrapping_add((d.swap(-1, Ordering::Relaxed) as u64) & 0xff); // old 1000
    acc = acc.wrapping_add((d.load(Ordering::Relaxed) as u64) & 0xff); // now -1 => 0xff

    // --- SOUND SeqCst STORE (was fail-closed in slice 1) across widths ---
    let e = AtomicUsize::new(0);
    e.store(12345, Ordering::SeqCst);
    acc = acc.wrapping_add(e.load(Ordering::Relaxed) as u64); // 12345

    let e32 = AtomicU32::new(0);
    e32.store(65000, Ordering::SeqCst);
    acc = acc.wrapping_add(e32.load(Ordering::Relaxed) as u64); // 65000

    let e64 = AtomicI64::new(0);
    e64.store(-2, Ordering::SeqCst);
    acc = acc.wrapping_add((e64.load(Ordering::Relaxed) as u64) & 0xff); // 0xfe

    // --- SeqCst store then Relaxed store, ensure both land ---
    let f = AtomicU64::new(1);
    f.store(2, Ordering::SeqCst);
    f.store(3, Ordering::Relaxed);
    acc = acc.wrapping_add(f.load(Ordering::SeqCst)); // 3

    // --- NARROW (I8/I16) RMW + swap at ALL opt levels (was O0-only) ---
    let g8 = AtomicU8::new(100);
    acc = acc.wrapping_add(g8.fetch_add(50, Ordering::SeqCst) as u64); // old 100
    acc = acc.wrapping_add(g8.load(Ordering::Relaxed) as u64); // 150
    acc = acc.wrapping_add(g8.fetch_sub(10, Ordering::Relaxed) as u64); // old 150
    acc = acc.wrapping_add(g8.fetch_and(0b1111_0000, Ordering::AcqRel) as u64); // old 140
    acc = acc.wrapping_add(g8.fetch_or(0b0000_0011, Ordering::Release) as u64); // old (140&0xf0)=128
    acc = acc.wrapping_add(g8.fetch_xor(0xff, Ordering::Acquire) as u64); // old (128|3)=131
    acc = acc.wrapping_add(g8.swap(42, Ordering::SeqCst) as u64); // old (131^0xff)=124
    acc = acc.wrapping_add(g8.load(Ordering::Relaxed) as u64); // 42

    let s8 = AtomicI8::new(-5);
    acc = acc.wrapping_add((s8.fetch_add(3, Ordering::Relaxed) as i64 as u64) & 0xff); // old -5 => 0xfb
    acc = acc.wrapping_add((s8.load(Ordering::Relaxed) as i64 as u64) & 0xff); // -2 => 0xfe

    let g16 = AtomicU16::new(40000);
    acc = acc.wrapping_add(g16.fetch_add(1000, Ordering::SeqCst) as u64); // old 40000
    acc = acc.wrapping_add(g16.load(Ordering::Relaxed) as u64); // 41000
    acc = acc.wrapping_add(g16.fetch_sub(500, Ordering::Relaxed) as u64); // old 41000
    acc = acc.wrapping_add(g16.swap(12345, Ordering::AcqRel) as u64); // old 40500
    acc = acc.wrapping_add(g16.load(Ordering::Relaxed) as u64); // 12345

    let s16 = AtomicI16::new(-1000);
    acc = acc.wrapping_add((s16.fetch_add(500, Ordering::Relaxed) as i64 as u64) & 0xffff); // old -1000
    acc = acc.wrapping_add((s16.load(Ordering::Relaxed) as i64 as u64) & 0xffff); // -500

    // --- narrow RMW inside a loop (exercises O2/O3 regalloc under pressure) ---
    let ctr8 = AtomicU8::new(0);
    for _ in 0..7 {
        ctr8.fetch_add(3, Ordering::Relaxed);
    }
    acc = acc.wrapping_add(ctr8.load(Ordering::Relaxed) as u64); // 21

    let ctr16 = AtomicU16::new(1);
    for _ in 0..5 {
        ctr16.fetch_add(100, Ordering::Relaxed);
    }
    acc = acc.wrapping_add(ctr16.load(Ordering::Relaxed) as u64); // 501

    (acc % 251) as i32
}
