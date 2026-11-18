//! A map kept as one vector of `(key, value)` pairs in strictly ascending key
//! order, for the small per-block symbolic states of the regalloc translation
//! validator.
//!
//! It is a drop-in for the subset of `BTreeMap` those states use and has the
//! same abstract value: a finite map from keys to values. Every operation here
//! returns what the `BTreeMap` operation of the same name returns on the same
//! map, iteration visits keys in ascending order as `BTreeMap` does, and two
//! maps compare equal exactly when they hold the same pairs. Only the
//! representation differs: one allocation per map instead of one per B-tree
//! node, so cloning a state is one copy and a lookup is a binary search over
//! contiguous memory. `sorted_vec_map_matches_btreemap` drives random
//! operation sequences against `BTreeMap` and requires identical results.
//!
//! The validator's states hold the locations (or vregs) live across one
//! block; insertion into the middle is linear in the map's length, which those
//! sizes make cheaper than B-tree node traffic.

use std::fmt;

#[derive(Clone, PartialEq, Eq)]
pub(crate) struct SortedVecMap<K, V> {
    /// Strictly ascending by key; no key occurs twice.
    entries: Vec<(K, V)>,
}

impl<K, V> Default for SortedVecMap<K, V> {
    fn default() -> Self {
        Self {
            entries: Vec::new(),
        }
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for SortedVecMap<K, V> {
    /// Formats as `BTreeMap` does (`{k: v, ...}`), so a diagnostic that prints
    /// a state reads the same as before.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map()
            .entries(self.entries.iter().map(|(k, v)| (k, v)))
            .finish()
    }
}

impl<K: Ord + Copy, V> SortedVecMap<K, V> {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    fn position(&self, key: &K) -> Result<usize, usize> {
        self.entries.binary_search_by(|(k, _)| k.cmp(key))
    }

    pub(crate) fn get(&self, key: &K) -> Option<&V> {
        self.position(key).ok().map(|i| &self.entries[i].1)
    }

    #[cfg(test)]
    pub(crate) fn contains_key(&self, key: &K) -> bool {
        self.position(key).is_ok()
    }

    /// `BTreeMap::insert`: the previous value for `key`, if any.
    pub(crate) fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self.position(&key) {
            Ok(i) => Some(std::mem::replace(&mut self.entries[i].1, value)),
            Err(i) => {
                self.entries.insert(i, (key, value));
                None
            }
        }
    }

    /// `BTreeMap::remove`.
    pub(crate) fn remove(&mut self, key: &K) -> Option<V> {
        match self.position(key) {
            Ok(i) => Some(self.entries.remove(i).1),
            Err(_) => None,
        }
    }

    /// `BTreeMap::entry(key).or_insert_with(default)`.
    pub(crate) fn get_or_insert_with(&mut self, key: K, default: impl FnOnce() -> V) -> &mut V {
        let i = match self.position(&key) {
            Ok(i) => i,
            Err(i) => {
                self.entries.insert(i, (key, default()));
                i
            }
        };
        &mut self.entries[i].1
    }

    /// `BTreeMap::retain`: keeps the pairs for which `keep` is true, visiting
    /// them in ascending key order.
    pub(crate) fn retain(&mut self, mut keep: impl FnMut(&K, &mut V) -> bool) {
        self.entries.retain_mut(|(k, v)| keep(k, v));
    }

    pub(crate) fn clear(&mut self) {
        self.entries.clear();
    }

    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    #[cfg(test)]
    /// Ascending key order, as `BTreeMap::iter`.
    pub(crate) fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.entries.iter().map(|(k, v)| (k, v))
    }

    #[cfg(test)]
    /// Ascending keys, as `BTreeMap::keys`.
    pub(crate) fn keys(&self) -> impl Iterator<Item = &K> {
        self.entries.iter().map(|(k, _)| k)
    }

    /// The union of the two maps' keys, each mapped to `both(a, b)` where both
    /// maps hold it and to a clone of the one value where only one does.
    ///
    /// Equal to building a fresh `BTreeMap` by inserting `both(va, vb)` or
    /// `va.clone()` for every pair of `a`, then `entry(k).or_insert_with(||
    /// vb.clone())` for every pair of `b`: the same key set, and each key's
    /// value is decided by which maps hold it, not by visiting order. It is
    /// computed in one merge of the two ascending sequences.
    pub(crate) fn union_with(a: &Self, b: &Self, mut both: impl FnMut(&V, &V) -> V) -> Self
    where
        V: Clone,
    {
        let mut entries = Vec::with_capacity(a.entries.len().max(b.entries.len()));
        let (mut i, mut j) = (0, 0);
        while i < a.entries.len() && j < b.entries.len() {
            let (ka, va) = &a.entries[i];
            let (kb, vb) = &b.entries[j];
            match ka.cmp(kb) {
                std::cmp::Ordering::Less => {
                    entries.push((*ka, va.clone()));
                    i += 1;
                }
                std::cmp::Ordering::Greater => {
                    entries.push((*kb, vb.clone()));
                    j += 1;
                }
                std::cmp::Ordering::Equal => {
                    entries.push((*ka, both(va, vb)));
                    i += 1;
                    j += 1;
                }
            }
        }
        entries.extend(a.entries[i..].iter().cloned());
        entries.extend(b.entries[j..].iter().cloned());
        Self { entries }
    }
}

impl<'a, K, V> IntoIterator for &'a SortedVecMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = std::iter::Map<std::slice::Iter<'a, (K, V)>, fn(&'a (K, V)) -> (&'a K, &'a V)>;

    fn into_iter(self) -> Self::IntoIter {
        fn pair<K, V>((k, v): &(K, V)) -> (&K, &V) {
            (k, v)
        }
        self.entries.iter().map(pair)
    }
}

impl<K: Ord + Copy, V> FromIterator<(K, V)> for SortedVecMap<K, V> {
    /// As `BTreeMap::from_iter`: a later pair for a key replaces an earlier one.
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut map = Self::new();
        for (k, v) in iter {
            map.insert(k, v);
        }
        map
    }
}

#[cfg(test)]
mod tests {
    use super::SortedVecMap;
    use std::collections::BTreeMap;

    /// Small deterministic generator (no external crate).
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0 >> 33
        }
    }

    fn same(a: &SortedVecMap<u16, u32>, b: &BTreeMap<u16, u32>) -> bool {
        a.len() == b.len()
            && a.is_empty() == b.is_empty()
            && a.iter()
                .map(|(k, v)| (*k, *v))
                .eq(b.iter().map(|(k, v)| (*k, *v)))
            && a.keys().copied().eq(b.keys().copied())
            && format!("{a:?}") == format!("{b:?}")
    }

    /// Every operation the validator uses returns what `BTreeMap` returns,
    /// over random sequences on a small key universe (so hits, misses,
    /// replacements and removals all occur), and the merge-based union equals
    /// the insert-then-`or_insert_with` construction it replaces.
    #[test]
    fn sorted_vec_map_matches_btreemap() {
        let mut rng = Lcg(0x5eed);
        for round in 0..400 {
            let mut m: SortedVecMap<u16, u32> = SortedVecMap::new();
            let mut r: BTreeMap<u16, u32> = BTreeMap::new();
            let universe = 1 + (round % 40) as u64;
            for _ in 0..200 {
                let k = (rng.next() % universe) as u16;
                let v = rng.next() as u32;
                match rng.next() % 8 {
                    0..=2 => assert_eq!(m.insert(k, v), r.insert(k, v)),
                    3 => assert_eq!(m.remove(&k), r.remove(&k)),
                    4 => {
                        assert_eq!(m.get(&k), r.get(&k));
                        assert_eq!(m.contains_key(&k), r.contains_key(&k));
                    }
                    5 => {
                        let got = *m.get_or_insert_with(k, || v);
                        let want = *r.entry(k).or_insert_with(|| v);
                        assert_eq!(got, want);
                    }
                    6 => {
                        let modulus = 2 + (rng.next() % 3) as u16;
                        m.retain(|k, v| {
                            *v = v.wrapping_add(1);
                            k % modulus != 0
                        });
                        r.retain(|k, v| {
                            *v = v.wrapping_add(1);
                            k % modulus != 0
                        });
                    }
                    _ => {
                        if rng.next() % 16 == 0 {
                            m.clear();
                            r.clear();
                        }
                    }
                }
                assert!(same(&m, &r), "diverged in round {round}");
            }
            // Equality is map equality.
            let m2: SortedVecMap<u16, u32> = r.iter().map(|(k, v)| (*k, *v)).collect();
            assert!(m == m2);
            let mut m3 = m2.clone();
            if let Some((&k, _)) = r.iter().next() {
                m3.insert(k, r[&k].wrapping_add(1));
                assert!(m != m3);
            }
            // Union equals the BTreeMap construction it stands for.
            let mut other_r: BTreeMap<u16, u32> = BTreeMap::new();
            for _ in 0..(rng.next() % 30) {
                other_r.insert((rng.next() % universe) as u16, rng.next() as u32);
            }
            let other_m: SortedVecMap<u16, u32> = other_r.iter().map(|(k, v)| (*k, *v)).collect();
            let both = |a: &u32, b: &u32| a.wrapping_mul(31) ^ b;
            let mut want: BTreeMap<u16, u32> = BTreeMap::new();
            for (k, va) in &r {
                match other_r.get(k) {
                    Some(vb) => want.insert(*k, both(va, vb)),
                    None => want.insert(*k, *va),
                };
            }
            for (k, vb) in &other_r {
                want.entry(*k).or_insert_with(|| *vb);
            }
            let got = SortedVecMap::union_with(&m, &other_m, both);
            assert!(same(&got, &want), "union diverged in round {round}");
        }
    }
}
