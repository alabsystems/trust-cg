// Corpus: `AtomicPtr<T>` — an atomic whose ELEMENT is a raw pointer.
//
// `atomic_memory_ty` refused a pointer element with the reason "its swap is
// unproven; keep the whole type fail-closed to avoid a partial surface". That was
// accurate when written: `atomic_proofs` carried `SWP_I32: mem[addr] = operand`
// but NO 64-bit sibling, while LDADD / LDSMAX / LDSMIN / LDUMAX / LDUMIN each
// carried both widths. A pointer atomic is pointer-width — 64-bit here — so there
// was no width-correct memory obligation to credit a 64-bit exchange against.
//
// `SWP_I64: mem[addr] = operand` now exists, and `Swp*` is credited in
// `operand_sensitive_or_opcode_query` PER EMITTED WIDTH rather than opcode-wide.
// That distinction is the whole point: `encode_lse_atomic` derives the access size
// from Rt's register class, EXCEPT for the narrow forms, which carry a 4th
// access-size immediate precisely because i8/i16/i32 all use W registers. A
// byte/half SWP therefore still has no proof and still fails closed, instead of
// being silently credited to the 32-bit theorem.
//
// The atomic lives in a STATIC, not a local. A local `AtomicPtr` is scalarized
// and passing `&self` to an accessor then hits `[TCG-INTERIOR-MUT-SNAPSHOT]` —
// an unrelated, correct refusal about `!Freeze` referents that would mask this
// fixture entirely (measured: the local form refuses identically on BOTH the
// control and the subject, so it would have proved nothing). A static is also
// what the census root actually looks like: `io::error::OsFunctions` is reached
// through a static `AtomicPtr`.
//
// WHY EVERY ROW IS A WRONG NUMBER, NOT A CRASH, IF THE WIDTH IS WRONG: each
// pointer targets a distinct value, so a swapped, stale or mis-ordered pointer
// prints a different number rather than trapping. (A truncated pointer would
// likely fault instead — also a visible divergence, in the exit code.)
//   * `load 11` — the initial pointer survives being stored into the atomic.
//   * `store 22` — a plain atomic pointer store, then read back.
//   * `swap 22 33` — the exchange returns the OLD pointer and installs the new
//     one. This is the row the SWP proof is about; both halves are checked, so an
//     exchange that returned the new value would print `33 33`.
//
// SCOPE: load / store / swap only. `compare_exchange` over a pointer is refused
// by a SEPARATE gate ("atomic compare_exchange over PtrMut(I64) ... only I32/I64
// have a faithful LOCK-CMPXCHG proof"), and that is left alone here — the census
// roots this fixture is about are `atomic_load` and `atomic_store`. Widening the
// CAS gate is its own increment, and it should carry the same width-correct
// credit treatment as SWP: the `Cas*` arm is still opcode-wide on
// `"cas_i32: success path"` even though `CAS_I64: success path` exists.
#![allow(dead_code)]

use std::ptr::addr_of_mut;
use std::sync::atomic::{AtomicPtr, Ordering};

static mut A: i64 = 11;
static mut B: i64 = 22;
static mut C: i64 = 33;

static P: AtomicPtr<i64> = AtomicPtr::new(std::ptr::null_mut());

fn main() {
    unsafe {
        let pa: *mut i64 = addr_of_mut!(A);
        let pb: *mut i64 = addr_of_mut!(B);
        let pc: *mut i64 = addr_of_mut!(C);

        // Each value is bound to a LOCAL before printing: a deref written inline
        // inside a `format!` argument refuses with "format! arg reference does not
        // trace to a value local", which is unrelated to this fixture's subject.
        P.store(pa, Ordering::SeqCst);
        let v0 = *P.load(Ordering::SeqCst);
        println!("load {}", v0); // 11

        P.store(pb, Ordering::SeqCst);
        let v1 = *P.load(Ordering::SeqCst);
        println!("store {}", v1); // 22

        let old = P.swap(pc, Ordering::SeqCst);
        let v2 = *old;
        let v3 = *P.load(Ordering::SeqCst);
        println!("swap {} {}", v2, v3); // 22 33

        // Swap back, so a lowering that confused the two SWP halves (returning the
        // NEW value instead of the old) is caught a second time with the roles
        // reversed rather than only once.
        let old2 = P.swap(pa, Ordering::SeqCst);
        let v4 = *old2;
        let v5 = *P.load(Ordering::SeqCst);
        println!("swapback {} {}", v4, v5); // 33 11
    }
}
