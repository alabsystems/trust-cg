#![no_std]
#[repr(transparent)]
struct Scalar<T>(core::cell::UnsafeCell<T>);
#[inline(never)]
fn update<T: Copy>(value: &Scalar<T>, next: T) {
    unsafe {
        *value.0.get() = next;
    }
}
#[inline(never)]
fn returned<T: Copy>(before: T, after: T) -> Scalar<T> {
    let value = Scalar(core::cell::UnsafeCell::new(before));
    update(&value, after);
    value
}
macro_rules! export {
    ($name:ident,$ty:ty) => {
        #[unsafe(no_mangle)]
        pub fn $name(before: $ty, after: $ty) -> $ty {
            returned(before, after).0.into_inner()
        }
    };
}
export!(alias_pointer, *mut u8);
