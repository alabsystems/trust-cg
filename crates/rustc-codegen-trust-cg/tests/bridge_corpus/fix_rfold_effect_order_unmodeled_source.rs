// CORPUS FIXTURE — a reversed sum whose closure has an EFFECT, over a source the
// back-to-front drive does not model (`zip`, `chain`, `RangeInclusive`).
//
// rustc's `rfold` calls the `map` closure on the LAST item first. The bridge's
// `rfold` route drove the FORWARD chain for every integer sum, so the closure's
// effects ran front to back: measured on the unpatched base at `-Copt-level=2`/`3`
// (`no-proof-certs`), `zip` printed `1 2 3 4 = 30` where LLVM prints `4 3 2 1 = 30`,
// `chain` `0 1 2 10 11 12` where LLVM prints `12 11 10 2 1 0`, and `RangeInclusive`
// likewise. The forward drive is now kept only where the order is unobservable
// (`rfold_reduction_order_blind`), so these chains take the back-to-front drive,
// which does not model these sources: the bridge REFUSES them by name
// (`[TCG-ITER-RFOLD-ORDER]`).
//
// HOW IT FAILS IF THE ORDER FIX IS REVERTED: it COMPILES and its stdout DIVERGES
// from LLVM — a hard failure. A refusal is the correct outcome today; a future
// back-to-front model of these sources must MATCH.
//
// UPDATE 2026-09-30: `RangeInclusive` now HAS a back-to-front model (std's
// `spec_next_back`, see `emit_source_next`), so `inclusive_map` alone compiles
// and matches LLVM (`4 3 2 1 0`-ordered effects: the `map_effect` case of
// `fix_rev_range_inclusive_folds.rs`, a must-match row of
// `rev_range_inclusive_fold_differential.rs`). This program still refuses as a
// whole on `zip_map` / `chain_map`.
use std::hint::black_box;

fn show(x: u64) {
    print!("{x} ");
}

#[inline(never)]
fn zip_map(a: &[u64]) -> u64 {
    a.iter()
        .zip(a.iter())
        .rev()
        .map(|(x, y)| {
            show(*x);
            x * y
        })
        .sum()
}
#[inline(never)]
fn chain_map(n: u64) -> u64 {
    (0..n)
        .chain(10..n + 10)
        .rev()
        .map(|x| {
            show(x);
            x
        })
        .sum()
}
#[inline(never)]
fn inclusive_map(n: u64) -> u64 {
    (0..=n)
        .rev()
        .map(|x| {
            show(x);
            x * 3
        })
        .sum()
}

fn main() {
    let v = black_box([1u64, 2, 3, 4]);
    println!("= {}", zip_map(&v));
    println!("= {}", chain_map(black_box(3)));
    println!("= {}", inclusive_map(black_box(3)));
}
