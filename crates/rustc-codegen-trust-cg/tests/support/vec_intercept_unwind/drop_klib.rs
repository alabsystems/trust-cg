//! Library side of `vec_intercept_unwind_guard_differential`: in-place `Vec`
//! compactions over class-1 newtypes that need drop, where an element's `Drop`
//! (armed by the driver, once) or the user closure panics part-way through.
//!
//! std removes an element by first moving its read cursor past it and then
//! dropping it (`retain_mut`'s `g.read`, `dedup_by`'s `gap.read`), so a
//! panicking drop leaves that element out of the Vec when the guard closes
//! the gap. A compaction that drops before advancing moves the element whose
//! drop panicked back into the Vec, where it is dropped a second time.
//!
//! `resize_with` is not here: as a library this crate also instantiates
//! std's `truncate::<W>`, whose `drop_in_place::<[W]>` the bridge refuses
//! under `panic=unwind` ([TCG-EH-CLEANUP-LOOP]). Its shrink is the whole
//! program `bridge_corpus/fix_vec_shrink_drop_panics_unwind.rs`.

use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering::SeqCst};

/// The value of every drop, in order (the first 64).
pub static LOG: [AtomicU32; 64] = [const { AtomicU32::new(0) }; 64];
pub static N: AtomicUsize = AtomicUsize::new(0);
/// The value whose next drop panics (once); 0 arms nothing.
pub static ARM: AtomicU32 = AtomicU32::new(0);

fn record(x: u32) {
    let i = N.fetch_add(1, SeqCst);
    if i < 64 {
        LOG[i].store(x, SeqCst);
    }
    if x == ARM.load(SeqCst) {
        ARM.store(0, SeqCst);
        panic!("drop {x}");
    }
}

/// A `Drop` newtype of one scalar (class 1).
#[derive(Debug)]
pub struct W(pub u32);

impl Drop for W {
    fn drop(&mut self) {
        record(self.0);
    }
}

/// Derived `PartialEq` and `Drop`: `dedup` runs std's body.
#[derive(Debug, PartialEq)]
pub struct D(pub u32);

impl Drop for D {
    fn drop(&mut self) {
        record(self.0);
    }
}

/// A hand-written `PartialEq` (`/ 10`, panics on 59) and `Drop`.
#[derive(Debug)]
pub struct E(pub u32);

impl PartialEq for E {
    fn eq(&self, other: &E) -> bool {
        if self.0 == 59 {
            panic!("eq");
        }
        self.0 / 10 == other.0 / 10
    }
}

impl Drop for E {
    fn drop(&mut self) {
        record(self.0);
    }
}

/// Logged by its drop: shows the caller's cleanup ran during the unwind.
pub struct Local(pub u32);

impl Drop for Local {
    fn drop(&mut self) {
        record(self.0);
    }
}

#[inline(never)]
pub fn retain_even(v: &mut Vec<W>) {
    v.retain(|w| w.0 % 2 == 0)
}

#[inline(never)]
pub fn retain_mut_even(v: &mut Vec<W>) {
    v.retain_mut(|w| {
        w.0 += 100;
        w.0 % 2 == 0
    })
}

#[inline(never)]
pub fn retain_pred_panics(v: &mut Vec<W>) {
    v.retain(|w| {
        if w.0 == 5 {
            panic!("pred");
        }
        w.0 % 2 == 0
    })
}

#[inline(never)]
pub fn retain_with_local(v: &mut Vec<W>) {
    let _local = Local(1000);
    v.retain(|w| w.0 % 2 == 0)
}

#[inline(never)]
pub fn dedup_by_tens(v: &mut Vec<W>) {
    v.dedup_by(|a, b| a.0 / 10 == b.0 / 10)
}

#[inline(never)]
pub fn dedup_by_cmp_panics(v: &mut Vec<W>) {
    v.dedup_by(|a, b| {
        if a.0 == 59 {
            panic!("cmp");
        }
        a.0 / 10 == b.0 / 10
    })
}

#[inline(never)]
pub fn dedup_by_key_tens(v: &mut Vec<W>) {
    v.dedup_by_key(|w| w.0 / 10)
}

#[inline(never)]
pub fn dedup_by_key_panics(v: &mut Vec<W>) {
    v.dedup_by_key(|w| {
        if w.0 == 59 {
            panic!("key");
        }
        w.0 / 10
    })
}

#[inline(never)]
pub fn dedup_derived(v: &mut Vec<D>) {
    v.dedup()
}

#[inline(never)]
pub fn dedup_user_eq(v: &mut Vec<E>) {
    v.dedup()
}
