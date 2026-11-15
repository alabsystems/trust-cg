unsafe extern "Rust" {
    fn pow_loop128(base: u128, exp: u32) -> (u128, bool);
    fn pow_break_loop128(base: u128, exp: u32) -> (u128, bool);
    fn pow_loop(base: u64, exp: u32) -> (u64, bool);
    fn pow_break_loop(base: u64, exp: u32) -> (u64, bool);
    fn triangle_loop(a: i64, b: i64, n: u32) -> i64;
    fn overflow_rotate(a: u64, b: u64, n: u32) -> (u64, bool);
}

// Repeated full-width multiplication is independent of exponentiation by
// squaring. The high half determines overflow without overflowing_mul.
fn power(base: u64, exp: u32) -> (u64, bool) {
    let mut acc = 1u64;
    let mut overflow = false;
    for _ in 0..exp {
        let product = acc as u128 * base as u128;
        acc = product as u64;
        overflow |= product >> 64 != 0;
    }
    (acc, overflow)
}

fn triangle(mut a: i64, mut b: i64, n: u32) -> i64 {
    for _ in 0..n {
        let next = if a > b { a.wrapping_sub(b) } else { a };
        a = b;
        b = next;
    }
    a ^ b
}

fn rotate(mut a: u64, mut b: u64, n: u32) -> (u64, bool) {
    let mut overflow = false;
    for remaining in (1..=n).rev() {
        let wide = if remaining & 1 != 0 {
            let sum = a as u128 + b as u128;
            overflow |= sum >> 64 != 0;
            sum
        } else {
            overflow |= a < b;
            (1u128 << 64) + a as u128 - b as u128
        };
        a = b;
        b = wide as u64;
    }
    (a ^ b, overflow)
}

// Division gives an independent overflow predicate for a full-width product.
fn power128(base: u128, exp: u32) -> (u128, bool) {
    let mut acc = 1u128;
    let mut overflow = false;
    for _ in 0..exp {
        overflow |= base != 0 && acc > u128::MAX / base;
        acc = acc.wrapping_mul(base);
    }
    (acc, overflow)
}

fn main() {
    let edges = [0, 1, 2, u64::MAX, 1 << 63, (1 << 63) - 1, 0xffffffff];
    let mut random = 0x7ff18120aada3211u64;
    let mut checks = 0;
    for index in 0..4096 {
        random ^= random << 13;
        random ^= random >> 7;
        random ^= random << 17;
        let base = if index < edges.len() * 65 {
            edges[index / 65]
        } else {
            random
        };
        let other = random.rotate_left(29);
        let n = (index % 65) as u32;
        let expected = power(base, n);
        unsafe {
            assert_eq!(pow_loop(base, n), expected, "pow base={base} exp={n}");
            assert_eq!(
                pow_break_loop(base, n),
                expected,
                "break base={base} exp={n}"
            );
            assert_eq!(
                triangle_loop(base as i64, other as i64, n),
                triangle(base as i64, other as i64, n)
            );
            assert_eq!(overflow_rotate(base, other, n), rotate(base, other, n));
        }
        let wide_edges = [0, 1, 2, u128::MAX, 1 << 127, (1 << 127) - 1, (1 << 64) + 1];
        let wide = if index < wide_edges.len() * 65 {
            wide_edges[index / 65]
        } else {
            ((base as u128) << 64) | other as u128
        };
        let expected = power128(wide, n);
        unsafe {
            assert_eq!(
                pow_loop128(wide, n),
                expected,
                "wide pow base={wide} exp={n}"
            );
            assert_eq!(
                pow_break_loop128(wide, n),
                expected,
                "wide break base={wide} exp={n}"
            );
        }
        checks += 6;
    }
    assert_eq!(checks, 24576);
    println!("PASS overflow_loop_threading checks={checks}");
}
