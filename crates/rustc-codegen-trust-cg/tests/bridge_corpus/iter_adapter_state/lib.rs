// Fixture library for `tests/iterator_adapter_state_differential.rs`: every
// function hands a std iterator adapter whose state std code may already have
// advanced to a bridge-intercepted terminal, or returns a bridge-built adapter
// to std code. The library is compiled by the backend under test, the driver
// (`main.rs`) by LLVM. Every output is fully determined by std.
#![feature(type_alias_impl_trait)]

use std::iter::Chain;
use std::ops::Range;
use std::slice::Iter;

// --- `Chain { a: Option<A>, b: Option<B> }`: std stores `None` into a half
// once it runs out; that half's payload is then dead (a null cursor for
// `slice::Iter`, stale bytes for `Range`).
#[inline(never)]
pub fn chain_slice_count(c: Chain<Iter<'_, u32>, Iter<'_, u32>>) -> usize {
    c.count()
}
#[inline(never)]
pub fn chain_slice_fold(c: Chain<Iter<'_, u32>, Iter<'_, u32>>) -> u64 {
    c.fold(0u64, |acc, x| acc * 100 + u64::from(*x))
}
#[inline(never)]
pub fn chain_slice_collect(c: Chain<Iter<'_, u32>, Iter<'_, u32>>) -> Vec<u32> {
    c.copied().collect()
}
#[inline(never)]
pub fn chain_range_count(c: Chain<Range<u64>, Range<u64>>) -> usize {
    c.count()
}
#[inline(never)]
pub fn chain_range_sum(c: Chain<Range<u64>, Range<u64>>) -> u64 {
    c.sum()
}
// --- `TakeWhile { iter, flag, predicate }`: once the predicate answers false,
// std sets `flag` and every later pull yields nothing (it is fused).
#[inline(never)]
pub fn take_while_first_none(a: u32, b: u32) -> (Option<u32>, u32) {
    let mut it = (a..b).take_while(|x| x % 7 != 3);
    let first = it.next();
    (first, it.sum())
}
#[inline(never)]
pub fn take_while_drained_count(a: u32, b: u32) -> (u32, usize) {
    let mut it = (a..b).take_while(|x| x % 7 != 3);
    let mut sum = 0;
    while let Some(x) = it.next() {
        sum += x;
    }
    (sum, it.count())
}
#[inline(never)]
pub fn take_while_predicate_calls(a: u32, b: u32) -> (Option<u32>, u32, u32) {
    let mut calls = 0u32;
    let mut it = (a..b).take_while(|x| {
        calls += 1;
        x % 7 != 3
    });
    let first = it.next();
    let rest = it.map(|x| x * 10).sum();
    (first, rest, calls)
}
pub type TakeWhileIter = impl Iterator<Item = u32>;
#[define_opaque(TakeWhileIter)]
#[inline(never)]
pub fn take_while_make(a: u32, b: u32) -> TakeWhileIter {
    (a..b).take_while(|x| x % 7 != 3)
}
#[inline(never)]
pub fn take_while_sum(it: TakeWhileIter) -> u32 {
    it.sum()
}

// --- `FlatMap { inner: FlattenCompat { iter: Fuse<Map<I, F>>, frontiter,
// backiter } }`: a bridge-built value must be std's, wherever it is read.
#[inline(never)]
pub fn flat_map_u32(n: u32) -> impl Iterator<Item = u32> {
    (0..n).flat_map(|x| 0..x)
}
#[inline(never)]
pub fn flat_map_usize(n: usize) -> impl Iterator<Item = usize> {
    (1..n).flat_map(|x| x..2 * x)
}
#[inline(never)]
pub fn flat_map_size_hint(n: u32) -> (usize, Option<usize>) {
    (0..n).flat_map(|x| 0..x).size_hint()
}
pub type FlatMapDoubleEnded = impl DoubleEndedIterator<Item = i64> + Clone;
#[define_opaque(FlatMapDoubleEnded)]
#[inline(never)]
pub fn flat_map_double_ended(n: i64) -> FlatMapDoubleEnded {
    (0..n).flat_map(|x| 0..x)
}
