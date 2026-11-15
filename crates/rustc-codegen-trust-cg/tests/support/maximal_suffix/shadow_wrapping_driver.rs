unsafe extern "Rust" {
    fn shadow_wrapping(n: u64, a: u64, b: u64) -> (u64, u64);
}

// Independent oracle: the fixture's own `wrapping_add` is `a ^ b`, not core's
// addition, so a backend that gave the shadow core semantics would fail here.
fn oracle(mut n: u64, mut a: u64, mut b: u64) -> (u64, u64) {
    while n != 0 {
        let old_a = a;
        a = b;
        b = old_a ^ b;
        n -= 1;
    }
    (a, b)
}

fn main() {
    let mut checks = 0;
    let seeds = [
        0u64,
        1,
        2,
        u64::MAX,
        1 << 63,
        0x0123_4567_89ab_cdef,
        0xfedc_ba98_7654_3210,
    ];
    for (i, &a) in seeds.iter().enumerate() {
        for &b in &seeds[i..] {
            for n in 0..80u64 {
                assert_eq!(
                    unsafe { shadow_wrapping(n, a, b) },
                    oracle(n, a, b),
                    "{n} {a:#x} {b:#x}"
                );
                checks += 1;
            }
        }
    }
    println!("PASS shadow_wrapping checks={checks}");
}
