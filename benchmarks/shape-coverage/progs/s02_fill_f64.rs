use std::hint::black_box as bb;
#[inline(never)] fn fill(dst: *mut f64, n: isize, v: f64) {
    let mut i = 0isize; while i < n { unsafe { *dst.offset(i) = v; } i += 1; } }
fn main() { let n = bb(64isize); let mut b = vec![0.0f64; n as usize]; let v = bb(3.25f64);
    fill(b.as_mut_ptr(), n, v); let s: f64 = b.iter().sum();
    std::process::exit((s as i64 % 126) as i32); }
