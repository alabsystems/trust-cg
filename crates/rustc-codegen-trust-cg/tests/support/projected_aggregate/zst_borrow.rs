#![no_std]
extern crate projected_aggregate_types;
use projected_aggregate_types::WithZst;
// A `&mut` borrow of a by-value repr(Rust) aggregate whose zero-sized fields
// sit between its sized ones, followed by a whole-value move.
#[unsafe(no_mangle)]
pub fn borrowed(mut v: WithZst, cb: fn(&mut WithZst)) -> u64 {
    cb(&mut v);
    consume(v)
}

#[inline(never)]
fn consume(v: WithZst) -> u64 {
    v.a ^ (v.b as u64)
}
