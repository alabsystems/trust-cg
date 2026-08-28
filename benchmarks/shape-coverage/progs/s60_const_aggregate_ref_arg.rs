// passing &CONST_STRUCT to a fn (f(&P{..})) — O1 promotes it to a const &P arg;
// must compile+match at all opts (was O1 decline). Companion to s57 (scalar).
use std::hint::black_box as bb;
#[derive(Clone, Copy)] struct P { x: u64, y: u64 }
fn dist(a: &P, b: &P) -> u64 { a.x.wrapping_sub(b.x).wrapping_mul(a.y.wrapping_add(b.y)) }
fn main() {
    let p = P { x: bb(10), y: bb(20) };
    // &const struct passed as arg
    let acc = dist(&p, &P { x: 1, y: 2 }).wrapping_add(dist(&P { x: 5, y: 6 }, &p));
    std::process::exit((acc % 233) as i32);
}
