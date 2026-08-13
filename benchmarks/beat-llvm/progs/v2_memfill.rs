// vectorizable: memset-shaped whole-array byte fill per rep; LLVM lowers the fill
// loop to memset. The black_box'd probe index keeps the array observable so the
// whole loop cannot be folded to a closed form.
use std::hint::black_box as bb;
fn done(code: u64) -> ! {
    std::process::exit((code % 126) as i32)
}
const N: usize = 8192;
fn main() {
    let reps = bb(100_000u32);
    let mut a = [0u8; N];
    let mut acc: u64 = 0;
    let mut r = 0u32;
    while r < reps {
        let v = (r as u8) | 1;
        let mut i = 0usize;
        while i < N {
            a[i] = v;
            i += 1;
        }
        let idx = bb((r as usize).wrapping_mul(31)) % N;
        acc = acc.wrapping_add(a[idx] as u64);
        r += 1;
    }
    done(acc);
}
