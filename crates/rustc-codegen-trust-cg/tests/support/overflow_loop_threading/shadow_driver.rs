unsafe extern "Rust" {
    fn shadow_loop(a: u64, b: u64, n: u32) -> (u64, bool);
}

// Independent oracle: the fixture's own `overflowing_add` is `(a ^ b, true)`,
// not core's addition, so a backend that modeled it as the core method would
// return sums here.
fn oracle(mut a: u64, mut b: u64, n: u32) -> (u64, bool) {
    let mut overflow = false;
    for _ in 0..n {
        let next = a ^ b;
        a = b;
        b = next;
        overflow = true;
    }
    (a ^ b, overflow)
}

fn main() {
    let mut checks = 0;
    let seeds = [
        0u64,
        1,
        2,
        3,
        u64::MAX,
        u64::MAX - 1,
        1 << 63,
        0x0123_4567_89ab_cdef,
        0xfedc_ba98_7654_3210,
    ];
    for (i, &a) in seeds.iter().enumerate() {
        for &b in &seeds[i..] {
            for n in 0..70u32 {
                assert_eq!(
                    unsafe { shadow_loop(a, b, n) },
                    oracle(a, b, n),
                    "{a:#x} {b:#x} {n}"
                );
                checks += 1;
            }
        }
    }
    println!("PASS shadow_loop checks={checks}");
}
