#![no_std]

#[unsafe(no_mangle)]
pub fn pow_loop(mut base: u128, mut exp: u32) -> (u128, bool) {
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
pub fn triangle_loop(mut a: i128, mut b: i128, mut n: u32) -> i128 {
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
pub fn overflow_rotate(mut a: u128, mut b: u128, mut n: u32) -> (u128, bool) {
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
pub fn pow_break_loop(mut base: u128, mut exp: u32) -> (u128, bool) {
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

#[unsafe(no_mangle)]
pub fn signed_rotate(mut a: i128, mut b: i128, mut n: u32) -> (i128, bool) {
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
pub fn signed_multiply(mut a: i128, mut b: i128, mut n: u32) -> (i128, bool) {
    let mut overflow = false;
    while n != 0 {
        let (next, flag) = a.overflowing_mul(b);
        a = b;
        b = next;
        overflow |= flag;
        n = n.wrapping_sub(1);
    }
    (a ^ b, overflow)
}

#[unsafe(no_mangle)]
pub fn wide_switch(mut a: u128, mut b: u128, mut n: u32) -> u128 {
    while n != 0 {
        let next = match a {
            0x80000000000000000000000000000007 => !b,
            _ => b ^ 0x80000000000000000000000000000009,
        };
        a = b;
        b = next;
        n = n.wrapping_sub(1);
    }
    a ^ b
}

#[unsafe(no_mangle)]
pub fn wide_wrapping(mut a: u128, mut b: u128, mut n: u32) -> u128 {
    while n != 0 {
        let next = a
            .wrapping_add(0x10000000000000003)
            .wrapping_mul(b)
            .wrapping_sub(0x80000000000000000000000000000009);
        a = b;
        b = next;
        n = n.wrapping_sub(1);
    }
    a ^ b
}
