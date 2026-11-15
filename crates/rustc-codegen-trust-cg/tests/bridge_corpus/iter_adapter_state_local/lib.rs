// Fixture library for `tests/iterator_adapter_state_differential.rs`: a
// `Chain` advanced by std's real `Chain::next` inside this (bridge-compiled)
// library, until std clears a half to `None`, then handed to a
// bridge-intercepted terminal. Compiled at -O1..-O3 only: at -O0 the exported
// share-generics instance of `Chain::next` meets an unrelated refusal (its
// by-value `FnOnce` closure environment). Every output is fully determined by
// std.

#[inline(never)]
pub fn chain_local_fold(a: &[u32], b: &[u32], k: usize) -> u64 {
    let mut c = a.iter().chain(b.iter());
    for _ in 0..k {
        c.next();
    }
    c.fold(0u64, |acc, x| acc * 100 + u64::from(*x))
}
#[inline(never)]
pub fn chain_local_back_count(a: &[u32], b: &[u32], k: usize) -> usize {
    let mut c = a.iter().chain(b.iter());
    for _ in 0..k {
        c.next_back();
    }
    c.map(|x| x * 2).count()
}
