// CORPUS FIXTURE (OPT-6b, ADVERSARIAL) — bounds checks that must be KEPT.
//
// Every shape here defeats one leg of the dominating-compare analysis or of
// the solver implication, so the check must stay (legacy lowering) — and,
// because every access is still IN BOUNDS at runtime, the observable result
// must equal LLVM's whether or not anything fired. The would-trap OOB
// versions of these same shapes are pinned by `dom_bounds_refutation_x86.rs`
// (they cannot live in this no_std corpus: an LLVM bounds-panic hangs in the
// `loop {}` panic handler while the kept trust-cg check traps).
//
//   (a) WEAKER dominating fact: guard `t < 64` over a `[u8; 16]` — the
//       implication (t <u 64 => t <u 16) is REFUTED by the ay lane (witness
//       t = 16); the runtime stays in bounds only via a solver-invisible
//       runtime limit, which the analysis must not credit.
//   (b) Index MUTATED between guard and check: `q += 1` after the guard
//       compare — the copy-chain resolution refuses (the index no longer
//       roots to the guarded value).
//   (c) DERIVED index: `a[t - 1]` — the index roots to a `Sub`, not a bare
//       copy of the guarded local; refused.
//
// Expected exit: (a) sums b[0..10] = 0+..+9 = 45; (b) writes a[1..=31] = 1,
// reads back a[31] = 1; (c) writes c[0..=6] = 3, reads back c[6] = 3.
// 45 + 1 + 3 = 49.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    // (a) weaker dominating fact — the only CONSTANT-bound dominating compare
    //     (`t < 64`) does NOT imply `t < 16`; the runtime protector
    //     (`t >= lim` with runtime `lim`) is not a constant compare, so the
    //     analysis skips it and the solver refutes the weak fact.
    let mut b = [0u8; 16];
    let mut init = black_box(0usize);
    while init < 16 {
        b[init] = init as u8;
        init += 1;
    }
    let lim = black_box(10usize);
    let mut s = 0i32;
    let mut t = black_box(0usize);
    while t < 64 {
        if t >= lim {
            break;
        }
        s += b[t] as i32;
        t += 1;
    }

    // (b) index mutated between the guard and the check: the fact `q < 31`
    //     is about the PRE-increment value; the checked index is q+1. In
    //     bounds at runtime (q <= 31 < 32), but the analysis must refuse.
    let mut a = [0u8; 32];
    let mut q = black_box(0usize);
    while q < 31 {
        q += 1;
        a[q] = 1;
    }
    let back = a[black_box(31usize) & 31] as i32;

    // (c) derived index: `t2 - 1` is not a bare copy of the guarded `t2`.
    //     In bounds at runtime (t2 in 1..=7 -> index 0..=6), but refused.
    let mut c = [0u8; 8];
    let mut t2 = black_box(1usize);
    while t2 < 8 {
        c[t2 - 1] = 3;
        t2 += 1;
    }
    let back_c = c[black_box(6usize) & 7] as i32;

    s + back + back_c
}
