// neon_fill: FP transfer register — width AND DUP register-file hazard.
use std::hint::black_box as bb;
#[inline(never)] fn fill(dst: *mut f32, n: isize, v: f32) {
    let mut i = 0isize; while i < n { unsafe { *dst.offset(i) = v; } i += 1; } }
fn main() { let n = bb(64isize); let mut b = vec![0.0f32; n as usize]; let v = bb(2.5f32);
    fill(b.as_mut_ptr(), n, v); let s: f32 = b.iter().sum();
    std::process::exit((s as i64 % 126) as i32); }
