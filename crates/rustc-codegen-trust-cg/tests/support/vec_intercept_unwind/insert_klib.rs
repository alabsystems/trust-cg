//! Library side of `vec_intercept_unwind_guard_differential`: `Vec::insert`
//! past the end moves its element in and then panics; std's `insert` owns the
//! element and drops it during the unwind.

pub static mut DROPS: u32 = 0;

pub struct D(pub u32);

impl Drop for D {
    fn drop(&mut self) {
        unsafe { DROPS += 1 }
    }
}

#[inline(never)]
pub fn insert_d(v: &mut Vec<D>, i: usize) {
    v.insert(i, D(9))
}

#[inline(never)]
pub fn insert_box(v: &mut Vec<Box<u64>>, i: usize) {
    v.insert(i, Box::new(9))
}

#[inline(never)]
pub fn insert_box_d(v: &mut Vec<Box<D>>, i: usize) {
    v.insert(i, Box::new(D(9)))
}
