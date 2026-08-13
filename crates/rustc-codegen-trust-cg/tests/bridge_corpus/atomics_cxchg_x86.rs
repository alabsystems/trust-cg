// CORPUS FIXTURE — ATOMICS slice 4: COMPARE-EXCHANGE.
//
// Exercises `AtomicT::compare_exchange` and `compare_exchange_weak` at i32/u32/
// i64/usize widths, covering BOTH the SUCCESS path (current == expected -> memory
// becomes new, returns Ok(old==expected)) and the FAILURE path (current !=
// expected -> memory UNCHANGED, returns Err(actual current)). It probes the
// returned old VALUE, the `is_ok()`/`is_err()` bool, and the memory value read
// back afterwards — so a wrong old value, a wrong success flag, a dropped
// conditional store, or an unconditional store would all change the exit code.
//
// x86 lowering (slice 4): `atomic_cxchg{,weak}::<T, ORD_SUCC, ORD_FAIL>` ->
// `Inst::CmpXchg` -> LOCK CMPXCHG (F0 0F B1). The instruction returns the old
// value in RAX; the success bool is re-derived as `Icmp Equal(old, expected)`
// (exactly the ZF CMPXCHG sets). The whole conditional data flow is bound to the
// genuine `Cmpxchg_I{32,64}` proofs (returns-old + conditional-store +
// success-flag), with the two negative controls (unconditional store / returns-
// desired / backwards flag) refuting to witness non-vacuity.
//
// `compare_exchange_weak` NEVER spuriously fails on x86 CMPXCHG, so it is lowered
// IDENTICALLY to strong (a sound refinement) — this fixture relies on the weak
// form succeeding/failing deterministically exactly like strong.
//
// STILL fail-closed (documented boundaries): narrow AtomicI8/I16/AtomicBool
// compare_exchange (only i32/i64 CMPXCHG is proven), AtomicPtr, u128/non-scalar,
// invalid failure orderings, unknown orderings.
//
// Everything folds into ONE exit code (mod 251); single-threaded => identical at
// O0/O2/O3.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::sync::atomic::{AtomicI32, AtomicI64, AtomicU32, AtomicUsize, Ordering};

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;

    // --- u32 SUCCESS: 5 == 5 -> becomes 10, returns Ok(5) ---
    let a = AtomicU32::new(5);
    let r = a.compare_exchange(5, 10, Ordering::SeqCst, Ordering::SeqCst);
    match r {
        Ok(old) => acc = acc.wrapping_add(old as u64), // +5 (returned old)
        Err(cur) => acc = acc.wrapping_add(1000 + cur as u64),
    }
    if r.is_ok() {
        acc = acc.wrapping_add(1); // +1 (flag true)
    }
    acc = acc.wrapping_add(a.load(Ordering::SeqCst) as u64); // +10 (store landed)

    // --- u32 FAILURE: current 10 != expected 999 -> UNCHANGED, returns Err(10) ---
    let r2 = a.compare_exchange(999, 7, Ordering::SeqCst, Ordering::Acquire);
    match r2 {
        Ok(old) => acc = acc.wrapping_add(5000 + old as u64),
        Err(cur) => acc = acc.wrapping_add(cur as u64), // +10 (actual current)
    }
    if r2.is_err() {
        acc = acc.wrapping_add(2); // +2 (flag false)
    }
    acc = acc.wrapping_add(a.load(Ordering::SeqCst) as u64); // +10 (unchanged)

    // --- i32 signed SUCCESS with a negative desired: -1 -> becomes -42 ---
    let s = AtomicI32::new(-1);
    let rs = s.compare_exchange(-1, -42, Ordering::AcqRel, Ordering::Relaxed);
    match rs {
        Ok(old) => acc = acc.wrapping_add((old as i64 as u64).wrapping_add(100)), // +(-1)+100 = +99
        Err(_) => acc = acc.wrapping_add(9999),
    }
    acc = acc.wrapping_add((s.load(Ordering::SeqCst) as i64 as u64).wrapping_add(50)); // +(-42)+50 = +8

    // --- i64 SUCCESS via a CAS RETRY LOOP (the canonical compare_exchange idiom) ---
    let c = AtomicI64::new(100);
    let mut cur = c.load(Ordering::Relaxed);
    loop {
        let want = cur + 23;
        match c.compare_exchange(cur, want, Ordering::SeqCst, Ordering::SeqCst) {
            Ok(_) => break,
            Err(actual) => cur = actual,
        }
    }
    acc = acc.wrapping_add(c.load(Ordering::SeqCst) as u64); // +123

    // --- usize compare_exchange_weak (== strong on x86) SUCCESS then FAILURE ---
    let w = AtomicUsize::new(7);
    let mut got = 0u64;
    // weak may spuriously fail on other arches; on x86 it does not — retry loop
    // still terminates in one iteration here.
    loop {
        match w.compare_exchange_weak(7, 21, Ordering::SeqCst, Ordering::Relaxed) {
            Ok(old) => {
                got = old as u64;
                break;
            }
            Err(_) => break, // x86: never spuriously fails, so this arm is unreachable
        }
    }
    acc = acc.wrapping_add(got); // +7 (returned old)
    acc = acc.wrapping_add(w.load(Ordering::SeqCst) as u64); // +21 (store landed)
    // weak FAILURE: expected 999 != current 21 -> Err(21), unchanged.
    let wf = w.compare_exchange_weak(999, 0, Ordering::SeqCst, Ordering::SeqCst);
    if wf.is_err() {
        acc = acc.wrapping_add(3); // +3
    }
    acc = acc.wrapping_add(w.load(Ordering::SeqCst) as u64); // +21 (unchanged)

    // Expected total:
    //   u32:  5 +1 +10 +10 +2 +10                    = 38
    //   i32:  99 +8                                   = 107
    //   i64:  123                                     = 123
    //   usize:7 +21 +3 +21                            = 52
    //   sum = 320
    (acc % 251) as i32
}
