unsafe extern "Rust" {
    fn load_u128_relaxed(p: *const u128) -> u128;
    fn load_u128_acquire(p: *const u128) -> u128;
    fn load_u128_seqcst(p: *const u128) -> u128;
    fn load_i128_relaxed(p: *const i128) -> i128;
    fn load_i128_acquire(p: *const i128) -> i128;
    fn load_i128_seqcst(p: *const i128) -> i128;
}
#[repr(C, align(16))]
struct Slot {
    value: u128,
}
fn main() {
    let mut checks = 0;
    for seed in 0..512u128 {
        let x = seed.wrapping_mul(0xda942042e4dd58b5);
        let values = [
            0,
            1,
            u128::MAX,
            1 << 127,
            (1 << 127) - 1,
            1 << 64,
            (1 << 64) - 1,
            0xaaaaaaaaaaaaaaaa5555555555555555,
            0x5555555555555555aaaaaaaaaaaaaaaa,
            x,
            !x,
            x << 64,
            x | x << 64,
            x.rotate_left(49),
            x.rotate_right(19),
            seed ^ (seed << 121),
        ];
        for value in values {
            let slot = Slot { value };
            let p = &slot.value as *const u128;
            unsafe {
                assert_eq!(load_u128_relaxed(p), value);
                checks += 1;
                assert_eq!(load_u128_acquire(p), value);
                checks += 1;
                assert_eq!(load_u128_seqcst(p), value);
                checks += 1;
                assert_eq!(load_i128_relaxed(p.cast()), value as i128);
                checks += 1;
                assert_eq!(load_i128_acquire(p.cast()), value as i128);
                checks += 1;
                assert_eq!(load_i128_seqcst(p.cast()), value as i128);
                checks += 1;
            }
        }
    }
    assert_eq!(checks, 49152);
    println!("PASS atomic128_load checks={checks}");
}
