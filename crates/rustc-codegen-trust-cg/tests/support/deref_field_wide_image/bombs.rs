//! A `Box<[T]>` whose element's `Drop` panics, built with panic=unwind: the
//! element drop is an invoke whose cleanup still frees the box, and rustc's
//! slice glue keeps dropping the remaining elements while it unwinds.
use std::sync::atomic::{AtomicUsize, Ordering};

pub static DROPS: AtomicUsize = AtomicUsize::new(0);
pub static DROP_SUM: AtomicUsize = AtomicUsize::new(0);

/// `Bomb(id, fuse)` panics when it is dropped and `id == fuse`.
pub struct Bomb(pub usize, pub usize);
impl Drop for Bomb {
    fn drop(&mut self) {
        DROPS.fetch_add(1, Ordering::SeqCst);
        DROP_SUM.fetch_add(self.0 + 1, Ordering::SeqCst);
        if self.0 == self.1 {
            panic!("bomb {}", self.0);
        }
    }
}

#[inline(never)]
pub fn drop_bombs(b: Box<[Bomb]>) { drop(b) }
