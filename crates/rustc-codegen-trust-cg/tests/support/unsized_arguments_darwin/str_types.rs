#![no_std]
#![feature(unsized_fn_params)]
/// What a callee observed: a running hash, the summed element lengths, and the
/// data address of the slice it was handed (the caller's own storage).
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Acc {
    pub h: u64,
    pub n: usize,
    pub p: usize,
}
impl Acc {
    pub const fn new(seed: u64) -> Self {
        Acc {
            h: seed,
            n: 0,
            p: 0,
        }
    }
}
pub trait StrSink {
    fn take(&self, s: [&str], seed: u8, t: &mut Acc);
}
