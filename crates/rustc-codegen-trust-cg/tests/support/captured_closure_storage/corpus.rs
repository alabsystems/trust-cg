#![no_std]

#[inline(never)]
fn apply<F: FnMut(u32) -> u64>(mut f: F, x: u32) -> u64 {
    f(x)
}

#[inline(never)]
fn nested<F: FnMut(u32) -> u64>(mut f: F, x: u32) -> u64 {
    apply(|v| f(v), x)
}

#[inline(never)]
fn forwarded<F: FnMut(u32) -> u64>(mut f: F, x: u32) -> u64 {
    nested(|v| f(v), x)
}

#[inline(never)]
fn sequence<F: FnMut(u32) -> u64>(mut f: F, x: u32) -> u64 {
    let first = nested(&mut f, x);
    let second = forwarded(&mut f, x.wrapping_add(1));
    first ^ second.rotate_left(17)
}

#[inline(never)]
fn once<F: FnOnce(u32) -> u64>(f: F, x: u32) -> u64 {
    f(x)
}

#[inline(never)]
fn nested_once<F: FnOnce(u32) -> u64>(f: F, x: u32) -> u64 {
    once(move |v| f(v), x)
}

#[unsafe(no_mangle)]
pub extern "C" fn nested_mut(seed: u64, x: u32) -> u64 {
    let mut value = seed;
    forwarded(
        |v| {
            value = value.wrapping_mul(31).wrapping_add(v as u64);
            value
        },
        x,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn nested_shared(seed: u64, x: u32) -> u64 {
    forwarded(|v| seed.wrapping_mul(31).wrapping_add(v as u64), x)
}

#[unsafe(no_mangle)]
pub extern "C" fn nested_value(seed: u64, x: u32) -> u64 {
    let mut value = seed;
    sequence(
        move |v| {
            value = value.wrapping_mul(31).wrapping_add(v as u64);
            value
        },
        x,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn nested_alias(seed: u64, x: u32) -> u64 {
    let mut value = seed;
    let folded = sequence(
        |v| {
            value = value.wrapping_mul(31).wrapping_add(v as u64);
            value
        },
        x,
    );
    folded ^ value.rotate_left(29)
}

#[unsafe(no_mangle)]
pub extern "C" fn nested_local(seed: u64, x: u32) -> u64 {
    let f = |v: u32| seed.wrapping_mul(31).wrapping_add(v as u64);
    forwarded(|v| f(v), x)
}

#[unsafe(no_mangle)]
pub extern "C" fn nested_multiple(seed: u64, salt: u64, x: u32) -> u64 {
    forwarded(|v| seed.wrapping_mul(31).wrapping_add(v as u64) ^ salt, x)
}

#[unsafe(no_mangle)]
pub extern "C" fn nested_owned_once(seed: u64, x: u32) -> u64 {
    nested_once(move |v| seed.wrapping_mul(31).wrapping_add(v as u64), x)
}

#[unsafe(no_mangle)]
pub extern "C" fn nested_empty(x: u32) -> u64 {
    forwarded(|v| (v as u64).wrapping_mul(31), x)
}
