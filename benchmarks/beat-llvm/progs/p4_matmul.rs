use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
const N: usize = 24;
fn main() {
    let seed = bb(3u64);
    let mut a = [0i64; N * N];
    let mut b = [0i64; N * N];
    let mut i = 0usize;
    while i < N * N {
        a[i] = ((i as u64).wrapping_mul(seed).wrapping_add(7) % 100) as i64;
        b[i] = ((i as u64).wrapping_mul(seed.wrapping_add(11)).wrapping_add(3) % 100) as i64;
        i += 1;
    }
    let reps = bb(20_000u32);
    let mut acc: i64 = 0;
    let mut r = 0u32;
    while r < reps {
        let mut c = [0i64; N * N];
        let mut i = 0usize;
        while i < N {
            let mut k = 0usize;
            while k < N {
                let aik = a[i * N + k];
                let mut j = 0usize;
                while j < N {
                    c[i * N + j] = c[i * N + j].wrapping_add(aik.wrapping_mul(b[k * N + j]));
                    j += 1;
                }
                k += 1;
            }
            i += 1;
        }
        acc = acc.wrapping_add(c[(r as usize * 37) % (N * N)]);
        a[(r as usize * 13) % (N * N)] = acc & 0xFF;
        r += 1;
    }
    done((acc as u64));
}
