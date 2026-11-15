unsafe extern "Rust" {
    fn pow_loop(base: u128, exp: u32) -> (u128, bool);
    fn pow_break_loop(base: u128, exp: u32) -> (u128, bool);
    fn triangle_loop(a: i128, b: i128, n: u32) -> i128;
    fn overflow_rotate(a: u128, b: u128, n: u32) -> (u128, bool);
    fn signed_rotate(a: i128, b: i128, n: u32) -> (i128, bool);
    fn signed_multiply(a: i128, b: i128, n: u32) -> (i128, bool);
    fn wide_switch(a: u128, b: u128, n: u32) -> u128;
    fn wide_wrapping(a: u128, b: u128, n: u32) -> u128;
}

// Independent base-2^32 schoolbook product. The checked lowering uses a
// division identity for overflow; this oracle computes the full 256-bit result.
fn product(a: u128, b: u128) -> (u128, u128) {
    let mut limbs = [0u128; 8];
    for i in 0..4 {
        for j in 0..4 {
            limbs[i + j] += ((a >> (32 * i)) & 0xffff_ffff) * ((b >> (32 * j)) & 0xffff_ffff);
        }
    }
    for i in 0..7 {
        limbs[i + 1] += limbs[i] >> 32;
        limbs[i] &= 0xffff_ffff;
    }
    assert!(limbs[7] <= 0xffff_ffff);
    let mut low = 0;
    let mut high = 0;
    for i in 0..4 {
        low |= limbs[i] << (32 * i);
        high |= limbs[i + 4] << (32 * i);
    }
    (low, high)
}

fn add(a: u128, b: u128) -> (u128, bool) {
    let lo = (a as u64 as u128) + (b as u64 as u128);
    let hi = (a >> 64) + (b >> 64) + (lo >> 64);
    ((hi << 64) | (lo as u64 as u128), hi >> 64 != 0)
}
fn sub(a: u128, b: u128) -> (u128, bool) {
    let lo = (1u128 << 64) + (a as u64 as u128) - (b as u64 as u128);
    let borrow = u128::from(lo >> 64 == 0);
    let hi = (1u128 << 64) + (a >> 64) - (b >> 64) - borrow;
    ((hi << 64) | (lo as u64 as u128), hi >> 64 == 0)
}
fn power(base: u128, exp: u32) -> (u128, bool) {
    let mut acc = 1;
    let mut overflow = false;
    for _ in 0..exp {
        let (low, high) = product(acc, base);
        acc = low;
        overflow |= high != 0;
    }
    (acc, overflow)
}
fn triangle(mut a: i128, mut b: i128, n: u32) -> i128 {
    for _ in 0..n {
        let next = if a > b {
            sub(a as u128, b as u128).0 as i128
        } else {
            a
        };
        a = b;
        b = next;
    }
    a ^ b
}
fn rotate(mut a: u128, mut b: u128, n: u32, signed: bool) -> (u128, bool) {
    let mut overflow = false;
    for remaining in (1..=n).rev() {
        let (next, unsigned_flag) = if remaining & 1 != 0 {
            add(a, b)
        } else {
            sub(a, b)
        };
        let flag = if signed {
            let a = a as i128;
            let b = b as i128;
            if remaining & 1 != 0 {
                (b > 0 && a > i128::MAX - b) || (b < 0 && a < i128::MIN - b)
            } else {
                (b < 0 && a > i128::MAX + b) || (b > 0 && a < i128::MIN + b)
            }
        } else {
            unsigned_flag
        };
        overflow |= flag;
        a = b;
        b = next;
    }
    (a ^ b, overflow)
}
fn multiply(mut a: i128, mut b: i128, n: u32) -> (i128, bool) {
    let mut overflow = false;
    for _ in 0..n {
        let negative = (a < 0) != (b < 0);
        let magnitude = |x: i128| {
            if x < 0 {
                sub(0, x as u128).0
            } else {
                x as u128
            }
        };
        let (low, high) = product(magnitude(a), magnitude(b));
        let bound = if negative { 1 << 127 } else { (1 << 127) - 1 };
        overflow |= high != 0 || low > bound;
        let next = if negative { sub(0, low).0 } else { low };
        a = b;
        b = next as i128;
    }
    (a ^ b, overflow)
}
fn switch(mut a: u128, mut b: u128, n: u32) -> u128 {
    for _ in 0..n {
        let next = if a == (1 << 127) + 7 {
            !b
        } else {
            b ^ ((1 << 127) + 9)
        };
        a = b;
        b = next;
    }
    a ^ b
}
fn wrapping(mut a: u128, mut b: u128, n: u32) -> u128 {
    for _ in 0..n {
        let next = sub(product(add(a, (1 << 64) + 3).0, b).0, (1 << 127) + 9).0;
        a = b;
        b = next;
    }
    a ^ b
}
fn check(a: u128, b: u128, n: u32) {
    let expected = power(a, n);
    unsafe {
        assert_eq!(pow_loop(a, n), expected, "pow {a:x} {n}");
        assert_eq!(pow_break_loop(a, n), expected, "break {a:x} {n}");
        assert_eq!(
            triangle_loop(a as i128, b as i128, n),
            triangle(a as i128, b as i128, n),
            "triangle {a:x} {b:x} {n}"
        );
        assert_eq!(
            overflow_rotate(a, b, n),
            rotate(a, b, n, false),
            "unsigned {a:x} {b:x} {n}"
        );
        let (value, flag) = rotate(a, b, n, true);
        assert_eq!(
            signed_rotate(a as i128, b as i128, n),
            (value as i128, flag),
            "signed {a:x} {b:x} {n}"
        );
        assert_eq!(
            signed_multiply(a as i128, b as i128, n),
            multiply(a as i128, b as i128, n),
            "multiply {a:x} {b:x} {n}"
        );
        assert_eq!(
            wide_switch(a, b, n),
            switch(a, b, n),
            "switch {a:x} {b:x} {n}"
        );
        assert_eq!(
            wide_wrapping(a, b, n),
            wrapping(a, b, n),
            "wrapping {a:x} {b:x} {n}"
        );
    }
}
fn main() {
    let edges = [
        0,
        1,
        2,
        3,
        (1 << 32) - 1,
        1 << 32,
        (1 << 64) - 1,
        1 << 64,
        (1 << 64) + 1,
        (1 << 127) - 1,
        1 << 127,
        (1 << 127) + 1,
        u128::MAX - 1,
        u128::MAX,
        (1 << 127) + 7,
        7,
    ];
    let mut cases = 0;
    for a in edges {
        for b in edges {
            for n in [0, 1, 2, 3, 64] {
                check(a, b, n);
                cases += 1;
            }
        }
    }
    let mut state = 0x71ac_d903_279b_43af_a189_7311_124f_e159u128;
    for index in 0..4096 {
        state ^= state << 23;
        state ^= state >> 17;
        state ^= state << 26;
        check(state, state.rotate_left(59), index % 65);
        cases += 1;
    }
    assert_eq!(cases, 5376);
    println!("PASS wide_loop_threading checks={}", cases * 8);
}
