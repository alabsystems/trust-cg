//! Library side of `vec_intercept_unwind_guard_differential`: in-place `Vec`
//! compactions over `Box<u32>` whose closure unwinds after the buffer was
//! partly compacted. A compaction that keeps its original `len` there owns one
//! box in two slots, and dropping the Vec frees it twice.

#[inline(never)]
pub fn retain_box(v: &mut Vec<Box<u32>>) {
    v.retain(|b| {
        if **b == 5 {
            panic!("retain_box");
        }
        **b != 1
    })
}

#[inline(never)]
pub fn dedup_by_box(v: &mut Vec<Box<u32>>) {
    v.dedup_by(|a, b| {
        if **a == 9 {
            panic!("dedup_by_box");
        }
        (**a + **b) % 2 == 0
    })
}
