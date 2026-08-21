use std::hint::black_box as bb;
fn main() { const N: usize = 24; let mut a=[0i64;N*N]; let mut b=[0i64;N*N]; let mut c=[0i64;N*N];
    let mut x=bb(0x9E3779B9u32);
    for i in 0..N*N { x^=x<<13; x^=x>>17; x^=x<<5; a[i]=(x%7) as i64; x^=x<<13; x^=x>>17; x^=x<<5; b[i]=(x%5) as i64; }
    let (a,b)=(bb(a),bb(b));
    for i in 0..N { for k in 0..N { let aik=a[i*N+k];
        for j in 0..N { c[i*N+j]=c[i*N+j].wrapping_add(aik.wrapping_mul(b[k*N+j])); } } }
    let s: i64 = c.iter().sum();
    std::process::exit((s.rem_euclid(126)) as i32); }
