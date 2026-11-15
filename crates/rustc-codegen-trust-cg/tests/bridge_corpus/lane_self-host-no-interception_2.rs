// CORPUS FIXTURE — lane `self-host-no-interception`, program 2 (O0 only).
//
// REGRESSION GUARD for the self-host rule (`std_def_is_interceptable`) over
// the STRIDE and OWNING iterator families whose method guards
// ([TCG-STRIDE-ITER-METHOD] / [TCG-OWNING-ITER-METHOD]) this lane gates on
// locality: `windows` / `chunks` / `chunks_exact` (+ `remainder`) / `rchunks`
// / `rchunks_exact` over a slice, and the by-value `vec::IntoIter` /
// `vec::Drain` / `array::IntoIter` `for` loops. All are NON-LOCAL std defs
// here, so the bridge's interceptions must still drive them. O0-only: when
// this program was written the -O2 aggregate-inlined stride ctor was a
// separate refusal ([TCG-STRIDE-ITER-INLINE], removed 2026-10-04 when the
// bridge's stride state became std's own). Accumulations are order-sensitive.
fn main() {
    let mut v: Vec<u64> = Vec::new();
    for x in 1..8u64 { v.push(x); }
    let mut w: u64 = 0;
    for pair in v.windows(2) { w = w * 10 + pair[0] * pair[1] % 10; }
    let mut c: u64 = 0;
    for chunk in v.chunks(3) { c = c * 100 + chunk.len() as u64 * 10 + chunk[0]; }
    let ce = v.chunks_exact(2);
    let rem: u64 = ce.remainder().iter().sum();
    let mut cx: u64 = 0;
    for chunk in v.chunks_exact(2) { cx = cx * 10 + chunk[1]; }
    let mut rc: u64 = 0;
    for chunk in v.rchunks(3) { rc = rc * 100 + chunk.len() as u64 * 10 + chunk[0]; }
    let mut rx: u64 = 0;
    for chunk in v.rchunks_exact(3) { rx = rx * 10 + chunk[2]; }
    let mut vi: u64 = 0;
    for x in v.clone() { vi = vi * 2 + x; }
    let mut d = v.clone();
    let mut dr: u64 = 0;
    for x in d.drain(4..) { dr = dr * 10 + x; }
    let mut ai: u64 = 0;
    for x in [9u64, 8, 7] { ai = ai * 10 + x; }
    let mut left: u64 = 0;
    for x in d.iter() { left = left * 10 + x; }
    println!("{w} {c} {rem} {cx} {rc} {rx} {vi} {dr} {left} {ai}");
}
