#![no_std]
#![feature(core_intrinsics)]
#![allow(improper_ctypes, improper_ctypes_definitions)]
use core::mem::MaybeUninit;
unsafe extern "C" {
    fn replace_word(slot: *mut usize, replacement: usize);
    fn replace_wide(slot: *mut u128, replacement: u128);
    fn replace_pointer(slot: *mut *const u8, replacement: *const u8);

    fn replace_bool(slot: *mut bool, replacement: bool);
    fn replace_char(slot: *mut char, replacement: char);
    fn replace_u32(slot: *mut u32, replacement: u32);
    fn replace_u64(slot: *mut u64, replacement: u64);
    fn replace_reference(slot: *mut &u64, replacement: &u64);
    fn replace_function(slot: *mut extern "C" fn() -> u64, replacement: extern "C" fn() -> u64);
    fn replace_byte(slot: *mut u8, replacement: u8);
    fn fill_u64(slot: *mut u64, replacement: u64);
}

#[unsafe(no_mangle)]
pub extern "C" fn storage_word(value: usize, replacement: usize) -> usize {
    let mut storage = MaybeUninit::new(value);
    unsafe {
        replace_word(storage.as_mut_ptr(), replacement);
        storage.assume_init()
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn storage_wide(value: u128, replacement: u128) -> u128 {
    let mut storage = MaybeUninit::new(value);
    unsafe {
        replace_wide(storage.as_mut_ptr(), replacement);
        storage.assume_init()
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn storage_pointer(value: *const u8, replacement: *const u8) -> *const u8 {
    let mut storage = MaybeUninit::new(value);
    unsafe {
        replace_pointer(storage.as_mut_ptr(), replacement);
        storage.assume_init()
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn storage_boolean(value: bool, replacement: bool) -> bool {
    let mut storage = MaybeUninit::new(value);
    unsafe {
        replace_bool(storage.as_mut_ptr(), replacement);
        storage.assume_init()
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn storage_character(value: char, replacement: char) -> char {
    let mut storage = MaybeUninit::new(value);
    unsafe {
        replace_char(storage.as_mut_ptr(), replacement);
        storage.assume_init()
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn storage_float32(value: u32, replacement: u32) -> u32 {
    let mut storage = MaybeUninit::new(f32::from_bits(value));
    unsafe {
        replace_u32(storage.as_mut_ptr().cast(), replacement);
        storage.assume_init().to_bits()
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn storage_float64(value: u64, replacement: u64) -> u64 {
    let mut storage = MaybeUninit::new(f64::from_bits(value));
    unsafe {
        replace_u64(storage.as_mut_ptr().cast(), replacement);
        storage.assume_init().to_bits()
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn storage_reference<'a>(value: &'a u64, replacement: &'a u64) -> &'a u64 {
    let mut storage = MaybeUninit::new(value);
    unsafe {
        replace_reference(storage.as_mut_ptr(), replacement);
        storage.assume_init()
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn storage_function(
    value: extern "C" fn() -> u64,
    replacement: extern "C" fn() -> u64,
) -> extern "C" fn() -> u64 {
    let mut storage = MaybeUninit::new(value);
    unsafe {
        replace_function(storage.as_mut_ptr(), replacement);
        storage.assume_init()
    }
}
#[repr(C)]
union WordFloat {
    word: u64,
    float: f64,
}
#[unsafe(no_mangle)]
pub extern "C" fn storage_custom(value: u64, replacement: u64) -> u64 {
    let mut storage = WordFloat { word: value };
    unsafe {
        replace_u64((&raw mut storage).cast(), replacement);
        storage.word
    }
}
#[repr(C)]
union SmallWide {
    small: u8,
    wide: u64,
}
#[unsafe(no_mangle)]
pub extern "C" fn storage_partial(value: u8, replacement: u8) -> u8 {
    let mut storage = SmallWide { small: value };
    unsafe {
        replace_byte((&raw mut storage).cast(), replacement);
        storage.small
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn storage_uninit(_value: u64, replacement: u64) -> u64 {
    let mut storage = MaybeUninit::<u64>::uninit();
    // This callback only writes. The initial storage must not be read.
    unsafe {
        fill_u64(storage.as_mut_ptr(), replacement);
        storage.assume_init()
    }
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

#[unsafe(no_mangle)]
pub extern "C" fn select_word(condition: bool, first: usize, second: usize) -> usize {
    choose(condition, first, second)
}

#[unsafe(no_mangle)]
pub extern "C" fn select_wide(condition: bool, first: u128, second: u128) -> u128 {
    choose(condition, first, second)
}

#[unsafe(no_mangle)]
pub extern "C" fn select_pointer(
    condition: bool,
    first: *const u8,
    second: *const u8,
) -> *const u8 {
    choose(condition, first, second)
}

#[unsafe(no_mangle)]
pub extern "C" fn storage_reassign(first: u64, second: u64, third: u64, fourth: u64) -> u64 {
    let mut storage = MaybeUninit::new(first);
    unsafe {
        replace_u64(storage.as_mut_ptr(), second);
    }
    storage = MaybeUninit::new(third);
    unsafe {
        replace_u64(storage.as_mut_ptr(), fourth);
        storage.assume_init()
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn storage_copy(first: u64, second: u64, third: u64) -> u64 {
    let mut storage = MaybeUninit::new(first);
    unsafe {
        replace_u64(storage.as_mut_ptr(), second);
    }
    let mut copied = storage;
    unsafe {
        replace_u64(copied.as_mut_ptr(), third);
        copied.assume_init()
    }
}
