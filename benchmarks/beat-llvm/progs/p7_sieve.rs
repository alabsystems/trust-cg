use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
const M: usize = 1024;
fn main() {
    let reps = bb(60_000u32);
    let mut total: u64 = 0;
    let mut r = 0u32;
    while r < reps {
        let mut comp = [0u8; M];
        let start = 2 + (r as usize % 3);
        let mut p = 2usize;
        while p * p < M {
            if comp[p] == 0 {
                let mut q = p * p;
                while q < M { comp[q] = 1; q += p; }
            }
            p += 1;
        }
        let mut count: u64 = 0;
        let mut i = start;
        while i < M {
            if comp[i] == 0 { count += 1; }
            i += 1;
        }
        total = total.wrapping_add(count);
        r += 1;
    }
    done(total);
}
