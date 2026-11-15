#![no_std]

#[unsafe(no_mangle)]
pub fn pow_loop(mut base: u64, mut exp: u32) -> (u64, bool) {
    if exp == 0 {
        return (1, false);
    }
    let mut acc = 1u64;
    let mut overflow = false;
    while exp > 1 {
        if exp & 1 != 0 {
            let (next, flag) = acc.overflowing_mul(base);
            acc = next;
            overflow |= flag;
        }
        exp /= 2;
        let (next, flag) = base.overflowing_mul(base);
        base = next;
        overflow |= flag;
    }
    let (next, flag) = acc.overflowing_mul(base);
    (next, overflow | flag)
}

#[unsafe(no_mangle)]
pub fn triangle_loop(mut a: i64, mut b: i64, mut n: u32) -> i64 {
    while n != 0 {
        let mut next = a;
        if a > b {
            next = a.wrapping_sub(b);
        }
        a = b;
        b = next;
        n = n.wrapping_sub(1);
    }
    a ^ b
}

#[unsafe(no_mangle)]
pub fn overflow_rotate(mut a: u64, mut b: u64, mut n: u32) -> (u64, bool) {
    let mut overflow = false;
    while n != 0 {
        let value;
        if n & 1 != 0 {
            let (next, flag) = a.overflowing_add(b);
            value = next;
            overflow |= flag;
        } else {
            let (next, flag) = a.overflowing_sub(b);
            value = next;
            overflow |= flag;
        }
        a = b;
        b = value;
        n = n.wrapping_sub(1);
    }
    (a ^ b, overflow)
}

#[unsafe(no_mangle)]
pub fn pow_break_loop(mut base: u64, mut exp: u32) -> (u64, bool) {
    if exp == 0 {
        return (1, false);
    }
    let mut acc = 1u64;
    let mut overflow = false;
    loop {
        if exp & 1 != 0 {
            let (next, flag) = acc.overflowing_mul(base);
            acc = next;
            overflow |= flag;
            if exp == 1 {
                return (acc, overflow);
            }
        }
        exp /= 2;
        let (next, flag) = base.overflowing_mul(base);
        base = next;
        overflow |= flag;
    }
}

#[unsafe(no_mangle)]
pub fn pow_loop128(mut base: u128, mut exp: u32) -> (u128, bool) {
    if exp == 0 {
        return (1, false);
    }
    let mut acc = 1u128;
    let mut overflow = false;
    while exp > 1 {
        if exp & 1 != 0 {
            let (next, flag) = acc.overflowing_mul(base);
            acc = next;
            overflow |= flag;
        }
        exp /= 2;
        let (next, flag) = base.overflowing_mul(base);
        base = next;
        overflow |= flag;
    }
    let (next, flag) = acc.overflowing_mul(base);
    (next, overflow | flag)
}

#[unsafe(no_mangle)]
pub fn pow_break_loop128(mut base: u128, mut exp: u32) -> (u128, bool) {
    if exp == 0 {
        return (1, false);
    }
    let mut acc = 1u128;
    let mut overflow = false;
    loop {
        if exp & 1 != 0 {
            let (next, flag) = acc.overflowing_mul(base);
            acc = next;
            overflow |= flag;
            if exp == 1 {
                return (acc, overflow);
            }
        }
        exp /= 2;
        let (next, flag) = base.overflowing_mul(base);
        base = next;
        overflow |= flag;
    }
}
