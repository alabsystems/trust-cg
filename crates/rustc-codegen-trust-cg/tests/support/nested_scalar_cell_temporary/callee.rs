extern crate cleanup_cell_transport_provider as provider;
use std::num::Saturating;
#[inline(never)]
fn make_word(input: u64) -> Saturating<usize> { Saturating(input as usize) }
#[inline(never)]
fn local_tuple<T>(make: fn(u64) -> T, input: u64, do_panic: bool) -> T {
    let value = make(input);
    let pair = (value, provider::tuple_tail(do_panic));
    pair.0
}
#[inline(never)]
pub fn sum(input: u64, do_panic: bool) -> usize {
    local_tuple(make_word, input, do_panic).0
}
