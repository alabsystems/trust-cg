#![no_std]
#![feature(core_intrinsics)]
use core::mem::MaybeUninit;
#[repr(C)]
pub struct Pair {
    first: u64,
    second: u64,
}
#[unsafe(no_mangle)]
pub extern "C" fn pair(condition: bool, first: Pair, second: Pair) -> Pair {
    choose(condition, first, second)
}
#[inline(never)]
fn choose<T>(condition: bool, true_val: T, false_val: T) -> T {
    // FIXME(https://github.com/rust-lang/unsafe-code-guidelines/issues/245):
    // Change this to use ManuallyDrop instead.
    let mut true_val = MaybeUninit::new(true_val);
    let mut false_val = MaybeUninit::new(false_val);

    struct DropOnPanic<T> {
        // Invariant: valid pointer and points to an initialized value that is not further used,
        // i.e. it can be dropped by this guard.
        inner: *mut T,
    }

    impl<T> Drop for DropOnPanic<T> {
        fn drop(&mut self) {
            // SAFETY: Must be guaranteed on construction of local type `DropOnPanic`.
            unsafe { self.inner.drop_in_place() }
        }
    }

    let true_ptr = true_val.as_mut_ptr();
    let false_ptr = false_val.as_mut_ptr();

    // SAFETY: The value that is not selected is dropped, and the selected one
    // is returned. This is necessary because the intrinsic doesn't drop the
    // value that is  not selected.
    unsafe {
        // Extract the selected value first, ensure it is dropped as well if dropping the unselected
        // value panics. We construct a temporary by-pointer guard around the selected value while
        // dropping the unselected value. Arguments overlap here, so we can not use mutable
        // reference for these arguments.
        let guard = core::intrinsics::select_unpredictable(condition, true_ptr, false_ptr);
        let drop = core::intrinsics::select_unpredictable(condition, false_ptr, true_ptr);

        // SAFETY: both pointers are well-aligned and point to initialized values inside a
        // `MaybeUninit` each. In both possible values for `condition` the pointer `guard` and
        // `drop` do not alias (even though the two argument pairs we have selected from did alias
        // each other).
        let guard = DropOnPanic { inner: guard };
        drop.drop_in_place();
        core::mem::forget(guard);

        // Note that it is important to use the values here. Reading from the pointer we got makes
        // LLVM forget the !unpredictable annotation sometimes (in tests, integer sized values in
        // particular seemed to confuse it, also observed in llvm/llvm-project #82340).
        core::intrinsics::select_unpredictable(condition, true_val, false_val).assume_init()
    }
}
