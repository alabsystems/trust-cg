use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
fn main() {
    let lim = bb(2_000_000u64);
    let mut total: u64 = 0;
    let mut n = 1u64;
    while n < lim {
        let mut c = n;
        let mut steps = 0u64;
        while c != 1 {
            if c & 1 == 0 { c >>= 1; } else { c = c.wrapping_mul(3).wrapping_add(1); }
            steps += 1;
        }
        total = total.wrapping_add(steps);
        n += 1;
    }
    done(total);
}
