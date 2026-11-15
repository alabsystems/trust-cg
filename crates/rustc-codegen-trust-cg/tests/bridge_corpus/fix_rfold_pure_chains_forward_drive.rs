// CORPUS FIXTURE — CONTROL: a reversed WRAPPING sum/product over closures with no
// effect keeps its FORWARD drive.
//
// `rfold_reduction_order_blind` keeps the forward-drive shortcut of the `rfold`
// route only where the visiting order is unobservable: the arithmetic wraps
// (overflow checks OFF) and every `map`/`filter` closure has no effect. Each
// function below is such a chain, and each COMPILED and MATCHED LLVM before the
// order gate existed.
// The `zip` row is the subtle one: `x * y` over two `&u64` inlines core's
// `#[rustc_inherit_overflow_checks]` `Mul`, whose MIR keeps an overflow `Assert`
// even when this crate turns overflow checks off (codegen, and the bridge's
// `lower_assert_terminator`, elide it). An effect analysis that treated that
// elided `Assert` as an effect sent the chain to the back-to-front drive, which
// does not model `rev()` over `zip()`, and REFUSED a program that used to compile:
// measured (`no-proof-certs`, O2 and O3), origin/main 5828b4ce6 printed
// `30 9 18 30 120` like LLVM, and origin/main 32ed6a49d — whose order gate
// counted every `Assert` — refused the crate with `[TCG-ITER-RFOLD-ORDER]`
// ("rev() over a zip() is not modeled").
//
// Run at `-Copt-level=2`/`3` with overflow checks OFF (their default there). HOW IT
// FAILS IF THE ORDER GATE OVER-REFUSES: a named `[TCG-ITER-RFOLD-ORDER]` refusal of
// a row that must compile — a hard failure of this gate.
use std::hint::black_box;

#[inline(always)]
fn nothing(_x: u64) {}

#[inline(never)]
fn slice_map(v: &[u64]) -> u64 {
    v.iter()
        .rev()
        .map(|&x| {
            nothing(x);
            x * 3
        })
        .sum()
}
#[inline(never)]
fn slice_filter(v: &[u64]) -> u64 {
    v.iter()
        .rev()
        .filter(|x| {
            nothing(**x);
            **x > 1
        })
        .sum()
}
#[inline(never)]
fn range_map(n: u64) -> u64 {
    (0..n)
        .rev()
        .map(|x| {
            nothing(x);
            x * 3
        })
        .sum()
}
#[inline(never)]
fn zip_map(a: &[u64]) -> u64 {
    a.iter()
        .zip(a.iter())
        .rev()
        .map(|(x, y)| {
            nothing(*x);
            x * y
        })
        .sum()
}
#[inline(never)]
fn product_map(v: &[u64]) -> u64 {
    v.iter()
        .rev()
        .map(|&x| {
            nothing(x);
            x + 1
        })
        .product()
}

fn main() {
    let v = black_box([1u64, 2, 3, 4]);
    println!("{}", slice_map(&v));
    println!("{}", slice_filter(&v));
    println!("{}", range_map(black_box(4)));
    println!("{}", zip_map(&v));
    println!("{}", product_map(&v));
}
