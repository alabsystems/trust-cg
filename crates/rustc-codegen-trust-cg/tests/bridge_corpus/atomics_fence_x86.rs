// CORPUS FIXTURE — ATOMICS slice 3: FENCES.
//
// Exercises `core::sync::atomic::fence` (a cross-thread memory barrier) and
// `compiler_fence` (a compiler-only fence) at every ordering, interleaved with
// real atomic loads/stores/RMWs so the fences sit between observable memory
// accesses that must not be reordered across them.
//
// x86 TSO lowering (slice 3):
//   * fence(Relaxed/Acquire/Release/AcqRel) -> ZERO instructions (TSO already
//     forbids the reorderings these forbid; matches LLVM's empty codegen). The
//     COMPILER-ordering barrier is still kept by the HAS_SIDE_EFFECTS Fence node
//     in the IR (no pre-isel pass hoists/sinks a memory op across it).
//   * fence(SeqCst) -> a single MFENCE, bound to the GENUINE single-thread
//     identity proof (MFENCE writes no register / no memory). Cross-thread
//     ordering is an Intel-SDM architectural axiom, not an SMT theorem.
//   * compiler_fence(any) -> Inst::Fence too; at SeqCst it emits a redundant but
//     SOUND MFENCE (over-strong, never wrong).
//
// Everything folds into ONE exit code (mod 251) so the bridge-vs-LLVM
// differential is a pure exit-code oracle; single-threaded => identical at
// O0/O2/O3. A dropped fence never changes the single-thread VALUE (that is the
// point — fences are ordering-only), so this fixture's oracle is the COMPILE +
// exit-match that the fence path lowers at all (and that the surrounding atomics
// keep working around it); the disasm golden (Acquire/Release = no instruction,
// SeqCst = MFENCE) is asserted separately in the lane's validation.
//
// STILL fail-closed (slice 4): compare_exchange (bare Cmpxchg, no proof),
// AtomicPtr, u128/non-scalar, unknown ordering.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::sync::atomic::{compiler_fence, fence, AtomicU32, AtomicU64, AtomicUsize, Ordering};

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;

    // --- Release/Acquire fence pair around a publish/consume of a flag ---
    // Producer: write data, Release fence, publish flag.
    let data = AtomicU64::new(0);
    let flag = AtomicUsize::new(0);
    data.store(42, Ordering::Relaxed);
    fence(Ordering::Release); // zero-instruction on x86 TSO
    flag.store(1, Ordering::Relaxed);

    // Consumer: read flag, Acquire fence, read data.
    let seen = flag.load(Ordering::Relaxed);
    fence(Ordering::Acquire); // zero-instruction on x86 TSO
    if seen == 1 {
        acc = acc.wrapping_add(data.load(Ordering::Relaxed)); // +42
    }

    // --- AcqRel fence between an RMW and a load ---
    let ctr = AtomicU32::new(10);
    let old = ctr.fetch_add(5, Ordering::Relaxed); // old 10
    fence(Ordering::AcqRel); // zero-instruction on x86 TSO
    acc = acc.wrapping_add(old as u64); // +10
    acc = acc.wrapping_add(ctr.load(Ordering::Relaxed) as u64); // +15

    // --- SeqCst fence (the ONE that lowers to MFENCE) between two stores ---
    let x = AtomicU64::new(0);
    let y = AtomicU64::new(0);
    x.store(7, Ordering::Relaxed);
    fence(Ordering::SeqCst); // -> MFENCE
    y.store(9, Ordering::Relaxed);
    acc = acc.wrapping_add(x.load(Ordering::SeqCst)); // +7
    acc = acc.wrapping_add(y.load(Ordering::SeqCst)); // +9

    // (Relaxed fences are a rustc compile error — `memory fences cannot have
    // Relaxed ordering` — so they are not written here; the backend still lowers
    // a Relaxed Inst::Fence to zero instructions, but it is unreachable from safe
    // Rust.)
    acc = acc.wrapping_add(3);

    // --- compiler_fence at every ordering (compiler-only; no hardware barrier
    //     except a redundant/sound MFENCE at SeqCst) ---
    let z = AtomicUsize::new(100);
    compiler_fence(Ordering::Acquire);
    let za = z.load(Ordering::Relaxed);
    compiler_fence(Ordering::Release);
    z.store(za.wrapping_add(1), Ordering::Relaxed);
    compiler_fence(Ordering::AcqRel);
    compiler_fence(Ordering::SeqCst);
    acc = acc.wrapping_add(z.load(Ordering::Relaxed) as u64); // +101

    // --- fences inside a loop (exercises O2/O3 code motion around the barrier) ---
    let loop_ctr = AtomicU64::new(0);
    for i in 0..8u64 {
        loop_ctr.store(i, Ordering::Relaxed);
        fence(Ordering::SeqCst); // MFENCE each iteration; must not be hoisted out
        acc = acc.wrapping_add(loop_ctr.load(Ordering::Relaxed)); // +0..+7 = +28
    }

    (acc % 251) as i32
}
