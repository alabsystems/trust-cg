//! `Box<[T]>` whose element needs drop. Its drop glue reads `{data, len}` through
//! the deref-led transmute and passes it to `drop_glue::<[T]>`, so the length
//! lane decides how many elements are dropped: `Counted` records every drop.
use std::sync::atomic::{AtomicUsize, Ordering};

pub static DROPS: AtomicUsize = AtomicUsize::new(0);
pub static DROP_SUM: AtomicUsize = AtomicUsize::new(0);

pub struct Counted(pub usize);
impl Drop for Counted {
    fn drop(&mut self) {
        DROPS.fetch_add(1, Ordering::SeqCst);
        DROP_SUM.fetch_add(self.0, Ordering::SeqCst);
    }
}

pub struct WStrings { pub k: u8, pub v: Box<[String]> }

#[inline(never)]
pub fn set_strings(t: &mut WStrings, b: Box<[String]>) { t.v = b; }

#[inline(never)]
pub fn drop_strings(b: Box<[String]>) { drop(b) }

#[inline(never)]
pub fn drop_counted(b: Box<[Counted]>) { drop(b) }

#[inline(never)]
pub fn drop_boxed_strs(b: Box<[Box<str>]>) { drop(b) }

#[inline(never)]
pub fn drop_vecs(b: Box<[Vec<u64>]>) { drop(b) }
