// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared dense-set storage; analyses own their universes and transfers.

#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct BitSet {
    words: Vec<u64>,
}

impl BitSet {
    #[inline]
    pub(crate) fn new(n_vregs: usize) -> Self {
        Self {
            words: vec![0u64; n_vregs.div_ceil(64)],
        }
    }
    #[inline]
    pub(crate) fn insert(&mut self, id: u32) {
        self.words[id as usize / 64] |= 1u64 << (id % 64);
    }
    #[inline]
    pub(crate) fn remove(&mut self, id: u32) {
        self.words[id as usize / 64] &= !(1u64 << (id % 64));
    }
    #[inline]
    pub(crate) fn contains(&self, id: u32) -> bool {
        (self.words[id as usize / 64] >> (id % 64)) & 1 != 0
    }
    #[inline]
    pub(crate) fn clear(&mut self) {
        self.words.iter_mut().for_each(|w| *w = 0);
    }
    /// `self |= other` (both must be the same width).
    #[inline]
    pub(crate) fn union_from(&mut self, other: &BitSet) {
        for (a, b) in self.words.iter_mut().zip(&other.words) {
            *a |= *b;
        }
    }
    /// Copy `other` into `self` without reallocating (same width).
    #[inline]
    pub(crate) fn copy_from(&mut self, other: &BitSet) {
        self.words.copy_from_slice(&other.words);
    }
    /// Iterate the ids of set bits in ascending order.
    pub(crate) fn iter(&self) -> impl Iterator<Item = u32> + '_ {
        self.words.iter().enumerate().flat_map(|(wi, &word)| {
            let base = (wi * 64) as u32;
            let mut bits = word;
            std::iter::from_fn(move || {
                if bits == 0 {
                    None
                } else {
                    let b = bits.trailing_zeros();
                    bits &= bits - 1;
                    Some(base + b)
                }
            })
        })
    }

    #[inline]
    pub(crate) fn subtract(&mut self, other: &Self) {
        debug_assert_eq!(self.words.len(), other.words.len());
        for (a, b) in self.words.iter_mut().zip(&other.words) {
            *a &= !*b;
        }
    }

    /// All three sets use the same dense universe.
    #[inline]
    pub(crate) fn union_difference(&mut self, added: &Self, removed: &Self) {
        debug_assert_eq!(self.words.len(), added.words.len());
        debug_assert_eq!(self.words.len(), removed.words.len());
        for ((a, b), c) in self.words.iter_mut().zip(&added.words).zip(&removed.words) {
            *a |= *b & !*c;
        }
    }

    #[cfg(test)]
    pub(crate) fn storage_bytes(&self) -> usize {
        self.words.capacity() * std::mem::size_of::<u64>()
    }
}
