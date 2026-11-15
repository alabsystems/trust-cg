#![no_std]
pub struct Wrap<F>(pub F);
#[inline(never)]
pub fn wrap<F>(f: F) -> Wrap<F> {
    Wrap(f)
}
#[unsafe(no_mangle)]
pub extern "C" fn shared(value: &i32) -> i32 {
    let wrapped = wrap(|| *value);
    (wrapped.0)()
}
#[unsafe(no_mangle)]
pub extern "C" fn mutable(value: &mut i32) -> i32 {
    let mut wrapped = wrap(|| {
        *value = value.wrapping_add(7);
        *value
    });
    (wrapped.0)()
}

#[unsafe(no_mangle)]
pub extern "C" fn owned(value: u64) -> u64 {
    let wrapped = wrap(move || value.wrapping_mul(9).wrapping_add(17));
    (wrapped.0)()
}
#[unsafe(no_mangle)]
pub extern "C" fn owned_mut(value: u64) -> u64 {
    let mut value = value;
    let mut wrapped = wrap(move || {
        value = value.wrapping_mul(9).wrapping_add(17);
        value
    });
    (wrapped.0)();
    (wrapped.0)()
}
#[unsafe(no_mangle)]
pub extern "C" fn nested(value: &i32) -> i32 {
    let wrapped = wrap(wrap(|| *value));
    (wrapped.0.0)()
}
#[unsafe(no_mangle)]
pub extern "C" fn nested_mut(value: &mut i32) -> i32 {
    let mut wrapped = wrap(wrap(|| {
        *value = value.wrapping_add(7);
        *value
    }));
    (wrapped.0.0)()
}
