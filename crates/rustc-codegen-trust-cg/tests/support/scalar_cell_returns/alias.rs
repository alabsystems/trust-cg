#![no_std]
#[repr(transparent)]
struct Scalar<T>(T);
#[inline(never)]
fn update<T: Copy>(value: &mut Scalar<T>, next: T) {
    value.0 = next;
}
#[inline(never)]
fn returned<T: Copy>(before: T, after: T) -> Scalar<T> {
    let mut value = Scalar(before);
    update(&mut value, after);
    value
}
macro_rules! export {
    ($name:ident,$ty:ty) => {
        #[unsafe(no_mangle)]
        pub fn $name(before: $ty, after: $ty) -> $ty {
            returned(before, after).0
        }
    };
}
export!(alias_u64, u64);
export!(alias_i8, i8);
export!(alias_i32, i32);
export!(alias_u128, u128);
export!(alias_bool, bool);
export!(alias_f32, f32);
export!(alias_f64, f64);
export!(alias_pointer, *mut u8);
