// PRE-EXISTING O0 REGALLOC P0 (found 2026-07-17 by the dyn-Fn fuzz, task #66):
// a plain 3-arg fn call with product-computed args under register pressure (6
// live locals + an inert +0) corrupts the args at -Copt-level=0 ONLY (O2/O3 ok).
// tcg=41 vs std=29. NOT dyn-Fn-specific — no dyn dispatch here. Deleting the
// trailing `+0` makes it PASS (an exact IR-shape/spill threshold).
fn call3_static(a: i64, b: i64, c: i64) -> i64 { a - b * 2 + c * 3 }
fn main() {
    let v1=1i64; let v2=2i64; let v3=3i64; let v4=4i64; let v5=5i64; let v6=6i64;
    let sum_before = v1+v2+v3+v4+v5+v6+0;
    let r = call3_static(v1*v2, v3*v4, v1*v3);
    let sum_after = v1+v2+v3+v4+v5+v6+sum_before;
    std::process::exit((r + sum_after).rem_euclid(128) as i32);
}
