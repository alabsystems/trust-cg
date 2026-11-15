unsafe extern "Rust" {
    fn wide_tuple(a: u128, b: u128, c: u128, d: u128) -> (u128, u128);
    fn wide_low(a: u128, b: u128, c: u128, d: u128) -> u128;
    fn wide_high(a: u128, b: u128, c: u128, d: u128) -> u128;
    fn wide_store(a: u128, b: u128, c: u128, d: u128, out: *mut (u128, u128));
    fn narrow_tuple(a: u64, b: u64, c: u64, d: u64) -> (u64, u64);
}
// Independent base-2^32 schoolbook oracle. The tested lowering uses 64-bit
// partial products; this oracle uses neither that decomposition nor the intrinsic.
fn expected(a: u128, b: u128, c: u128, d: u128) -> (u128, u128) {
    let mut limbs = [0u128; 8];
    for i in 0..4 {
        for j in 0..4 {
            limbs[i + j] += ((a >> (32 * i)) & 0xffff_ffff) * ((b >> (32 * j)) & 0xffff_ffff);
        }
        limbs[i] += (c >> (32 * i)) & 0xffff_ffff;
        limbs[i] += (d >> (32 * i)) & 0xffff_ffff;
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
fn check(a: u128, b: u128, c: u128, d: u128) {
    let e = expected(a, b, c, d);
    unsafe {
        assert_eq!(wide_tuple(a, b, c, d), e, "tuple: {a:x} {b:x} {c:x} {d:x}");
        assert_eq!(wide_low(a, b, c, d), e.0, "low");
        assert_eq!(wide_high(a, b, c, d), e.1, "high");
        let mut storage = [(0x1234u128, 0x5678u128); 3];
        wide_store(a, b, c, d, &mut storage[1]);
        assert_eq!(
            storage,
            [(0x1234, 0x5678), e, (0x1234, 0x5678)],
            "store plus guards"
        );
        let narrow =
            (a as u64 as u128) * (b as u64 as u128) + (c as u64 as u128) + (d as u64 as u128);
        assert_eq!(
            narrow_tuple(a as u64, b as u64, c as u64, d as u64),
            (narrow as u64, (narrow >> 64) as u64)
        );
    }
}
fn next(state: &mut u128) -> u128 {
    *state ^= *state << 23;
    *state ^= *state >> 17;
    *state ^= *state << 26;
    *state
}
fn main() {
    assert_eq!(
        expected(u128::MAX, u128::MAX, u128::MAX, u128::MAX),
        (u128::MAX, u128::MAX)
    );
    let edges = [
        0,
        1,
        2,
        (1u128 << 32) - 1,
        1u128 << 32,
        (1u128 << 64) - 1,
        1u128 << 64,
        (1u128 << 64) + 1,
        (1u128 << 127) - 1,
        1u128 << 127,
        u128::MAX - 1,
        u128::MAX,
    ];
    let mut cases = 0;
    for a in edges {
        for b in edges {
            for c in edges {
                for d in edges {
                    check(a, b, c, d);
                    cases += 1;
                }
            }
        }
    }
    let mut state = 0x71ac_d903_279b_43af_a189_7311_124f_e159;
    for _ in 0..8192 {
        let a = next(&mut state);
        let b = next(&mut state);
        let c = next(&mut state);
        let d = next(&mut state);
        check(a, b, c, d);
        cases += 1;
    }
    assert_eq!(cases, 28928);
    println!("PASS u128_carrying_mul cases={cases} checks={}", cases * 5);
}
