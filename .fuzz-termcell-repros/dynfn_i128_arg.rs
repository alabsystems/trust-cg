// P0 REPRO (fixed 2026-07-17 by the <=64-bit element guard): a 128-bit dyn-Fn
// argument (i128/u128) needs 2 GPR slots; the tuple-spread treated it as one
// register, mis-slotting the following args. `&dyn Fn(i64,i128,i64)` at O0
// returned 7 vs std 108. Now fail-closes. Compile with -Coverflow-checks=off.
fn main() {
    let f: &dyn Fn(i64, i128, i64) -> i64 = &|a, b, c| a + (b % 1000) as i64 - c;
    std::process::exit((f(1000, 7, 3)).rem_euclid(128) as i32);
}
