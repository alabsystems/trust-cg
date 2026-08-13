//! Fast, deterministic hashing for compile-time-hot lookup maps.
//!
//! The default `std::collections::HashMap` uses SipHash-1-3 with a
//! per-process-random seed. For the small integer-shaped keys that dominate the
//! backend's hot passes (`VReg`, `PReg`, `InstId`, `(usize, usize)` DAG edges,
//! …) SipHash is both slow *and* the random seed is wasted: the compiler's
//! output is engineered to be independent of hash-map iteration order (verified
//! by byte-identical object files across separate process invocations, which
//! carry different SipHash seeds). Swapping in a fixed-seed multiply-rotate
//! hasher therefore leaves every emitted byte unchanged while removing the
//! SipHash cost from the profile.
//!
//! This is the well-known FxHash construction (a rotate-xor-multiply mixer,
//! same family rustc uses internally). It has a *fixed* seed, so it is fully
//! deterministic — a stronger guarantee than the SipHash it replaces.

use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher};

const SEED: u64 = 0x51_7c_c1_b7_27_22_0a_95;
const ROTATE: u32 = 5;

/// Deterministic FxHash-style hasher. Fixed seed; no randomness.
#[derive(Default)]
pub struct FxHasher {
    hash: u64,
}

impl FxHasher {
    #[inline]
    fn add(&mut self, word: u64) {
        self.hash = (self.hash.rotate_left(ROTATE) ^ word).wrapping_mul(SEED);
    }
}

impl Hasher for FxHasher {
    #[inline]
    fn write(&mut self, mut bytes: &[u8]) {
        while bytes.len() >= 8 {
            let mut chunk = [0u8; 8];
            chunk.copy_from_slice(&bytes[..8]);
            self.add(u64::from_le_bytes(chunk));
            bytes = &bytes[8..];
        }
        if bytes.len() >= 4 {
            let mut chunk = [0u8; 4];
            chunk.copy_from_slice(&bytes[..4]);
            self.add(u64::from(u32::from_le_bytes(chunk)));
            bytes = &bytes[4..];
        }
        if bytes.len() >= 2 {
            let mut chunk = [0u8; 2];
            chunk.copy_from_slice(&bytes[..2]);
            self.add(u64::from(u16::from_le_bytes(chunk)));
            bytes = &bytes[2..];
        }
        if let Some(&byte) = bytes.first() {
            self.add(u64::from(byte));
        }
    }

    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.add(u64::from(i));
    }

    #[inline]
    fn write_u16(&mut self, i: u16) {
        self.add(u64::from(i));
    }

    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.add(u64::from(i));
    }

    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.add(i);
    }

    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64);
    }

    #[inline]
    fn finish(&self) -> u64 {
        self.hash
    }
}

/// `BuildHasher` for [`FxHasher`].
pub type FxBuildHasher = BuildHasherDefault<FxHasher>;

/// Drop-in `HashMap` using the deterministic fast hasher.
pub type FxHashMap<K, V> = HashMap<K, V, FxBuildHasher>;

/// Drop-in `HashSet` using the deterministic fast hasher.
pub type FxHashSet<K> = HashSet<K, FxBuildHasher>;

#[cfg(test)]
mod tests {
    use super::*;
    use std::hash::Hash;

    fn hash_of<T: Hash>(v: &T) -> u64 {
        let mut h = FxHasher::default();
        v.hash(&mut h);
        h.finish()
    }

    #[test]
    fn deterministic_same_seed_every_instance() {
        // Two independent hashers agree — no random seed involved.
        assert_eq!(hash_of(&123u32), hash_of(&123u32));
        assert_eq!(hash_of(&(7usize, 9usize)), hash_of(&(7usize, 9usize)));
        assert_ne!(hash_of(&1u32), hash_of(&2u32));
    }

    #[test]
    fn map_and_set_roundtrip() {
        let mut m: FxHashMap<u32, u32> = FxHashMap::default();
        for i in 0..1000u32 {
            m.insert(i, i * 2);
        }
        for i in 0..1000u32 {
            assert_eq!(m.get(&i), Some(&(i * 2)));
        }
        let mut s: FxHashSet<(u32, u32)> = FxHashSet::default();
        s.insert((1, 2));
        s.insert((1, 2));
        assert_eq!(s.len(), 1);
        assert!(s.contains(&(1, 2)));
    }
}
