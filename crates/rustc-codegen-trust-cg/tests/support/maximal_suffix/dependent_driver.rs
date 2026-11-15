unsafe extern "Rust" {
    fn read_dependent(data: &[u8], a: u64, b: u64) -> (u64, u64);
}

// Independent oracle: the same rotation written as a plain iterator loop.
fn oracle(data: &[u8], mut a: u64, mut b: u64) -> (u64, u64) {
    for &byte in data {
        let old_a = a;
        a = b;
        b = old_a.wrapping_add(byte as u64);
    }
    (a, b)
}

fn main() {
    let mut checks = 0;
    let mut data = Vec::new();
    for len in 0..64usize {
        data.clear();
        for i in 0..len {
            data.push((i as u8).wrapping_mul(37) ^ (len as u8));
        }
        for (a, b) in [
            (0u64, 0u64),
            (1, 2),
            (u64::MAX, 7),
            (0x0123_4567_89ab_cdef, u64::MAX - 3),
        ] {
            assert_eq!(
                unsafe { read_dependent(&data, a, b) },
                oracle(&data, a, b),
                "{len} {a:#x} {b:#x}"
            );
            checks += 1;
        }
    }
    println!("PASS read_dependent checks={checks}");
}
