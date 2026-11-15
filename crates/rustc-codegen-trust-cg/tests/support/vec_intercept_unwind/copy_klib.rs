//! Library side of `vec_intercept_unwind_guard_differential`: intercepted `Vec`
//! and iterator methods whose user closure unwinds part-way through, over
//! elements that need no drop. Compiled by LLVM (the oracle) and by the bridge.

/// Removes the 1s, then the predicate panics on 5: std's `PanicGuard`
/// leaves `[3, 4, 5, 9]`.
#[inline(never)]
pub fn retain_u32(v: &mut Vec<u32>) {
    v.retain(|&x| {
        if x == 5 {
            panic!("retain");
        }
        x != 1
    })
}

/// `retain_mut` mutates the elements it keeps before it panics.
#[inline(never)]
pub fn retain_mut_u32(v: &mut Vec<u32>) {
    v.retain_mut(|x| {
        if *x == 5 {
            panic!("retain_mut");
        }
        *x += 10;
        *x != 11
    })
}

/// A two-lane element (class-2 tuple image).
#[inline(never)]
pub fn retain_pair(v: &mut Vec<(u32, u32)>) {
    v.retain(|&(a, _)| {
        if a == 5 {
            panic!("retain_pair");
        }
        a != 1
    })
}

/// Panics after 600 removals in a 1000-element Vec.
#[inline(never)]
pub fn retain_large(v: &mut Vec<u32>) {
    v.retain(|&x| {
        if x == 900 {
            panic!("retain_large");
        }
        x % 3 != 0
    })
}

/// Control: the predicate panics before anything was removed.
#[inline(never)]
pub fn retain_keep_all(v: &mut Vec<u32>) {
    v.retain(|&x| {
        if x == 5 {
            panic!("retain_keep_all");
        }
        true
    })
}

/// Control: no panic.
#[inline(never)]
pub fn retain_no_panic(v: &mut Vec<u32>) {
    v.retain(|&x| x != 1)
}

/// std's `FillGapOnDrop` leaves `[3, 4, 1, 9]`.
#[inline(never)]
pub fn dedup_by_u32(v: &mut Vec<u32>) {
    v.dedup_by(|a, b| {
        if *a == 9 {
            panic!("dedup_by");
        }
        (*a + *b) % 2 == 0
    })
}

/// `dedup_by_key` is `dedup_by` with a key comparison: `[3, 4, 1, 9]`.
#[inline(never)]
pub fn dedup_by_key_u32(v: &mut Vec<u32>) {
    v.dedup_by_key(|x| {
        if *x == 9 {
            panic!("dedup_by_key");
        }
        *x % 2
    })
}

/// Control: the key panics on the first element, before any gap opens.
#[inline(never)]
pub fn dedup_by_key_first(v: &mut Vec<u32>) {
    v.dedup_by_key(|x| {
        if *x == 3 {
            panic!("dedup_by_key_first");
        }
        *x % 2
    })
}

/// The third generator call panics: std's `SetLenOnDrop` keeps the two
/// elements already written, `[3, 1, 71, 72]`.
#[inline(never)]
pub fn resize_with_u32(v: &mut Vec<u32>) {
    let mut calls = 0;
    v.resize_with(6, || {
        calls += 1;
        if calls == 3 {
            panic!("resize_with");
        }
        calls + 70
    })
}

/// The collected Vec's buffer is std's local `Vec` while the map closure runs.
#[inline(never)]
pub fn collect_map(a: &[u8]) -> Vec<u8> {
    a.iter()
        .map(|&x| {
            if x == 13 {
                panic!("collect_map");
            }
            x
        })
        .collect()
}

/// The consumed `vec::IntoIter` is std's to drop while the filter closure runs.
#[inline(never)]
pub fn owned_count(v: Vec<u32>) -> usize {
    v.into_iter()
        .filter(|&x| {
            if x == 13 {
                panic!("owned_count");
            }
            x % 2 == 0
        })
        .count()
}
