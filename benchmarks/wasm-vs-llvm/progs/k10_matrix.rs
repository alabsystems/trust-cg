#![no_std]
#![allow(dead_code)]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[derive(Clone, Copy, PartialEq)]
struct M3([[f32; 3]; 3]);

impl M3 {
    #[inline(never)]
    fn mul(&self, o: &M3) -> M3 {
        let mut r = [[0f32; 3]; 3];
        for i in 0..3 {
            for j in 0..3 {
                let mut s = 0f32;
                for k in 0..3 {
                    s += self.0[i][k] * o.0[k][j];
                }
                r[i][j] = s;
            }
        }
        M3(r)
    }
    #[inline(never)]
    fn det(&self) -> f32 {
        let m = &self.0;
        m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
            - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0])
    }
    #[inline(never)]
    fn transpose(self) -> M3 {
        let mut r = self;
        for i in 0..3 {
            for j in 0..3 {
                r.0[i][j] = self.0[j][i];
            }
        }
        r
    }
}

#[inline(never)]
fn m3_from(a: f32, b: f32) -> M3 {
    M3([[a, b, 1.0], [b, -a, 0.5], [a * b, 2.0, a - b]])
}

#[no_mangle]
pub extern "C" fn mat3_mul(a: f32, b: f32) -> f32 {
    let x = m3_from(a, b);
    let y = x.transpose();
    let z = x.mul(&y).mul(&x);
    z.0[0][0] + z.0[1][2] * 3.0 - z.0[2][1] + z.det()
}

#[no_mangle]
pub extern "C" fn mat3_det(a: f32, b: f32) -> u32 {
    let x = m3_from(a, b);
    let d1 = x.det();
    let d2 = x.transpose().det();
    let e = x == x.transpose();
    let c = |f: f32| if f.is_nan() { 0x7fc0_0000 } else { f.to_bits() };
    c(d1) ^ c(d2).rotate_left(7) ^ e as u32
}

#[inline(never)]
fn matmul4(a: &[f64; 16], b: &[f64; 16], out: &mut [f64; 16]) {
    for i in 0..4 {
        for j in 0..4 {
            let mut s = 0.0;
            for k in 0..4 {
                s += a[i * 4 + k] * b[k * 4 + j];
            }
            out[i * 4 + j] = s;
        }
    }
}

#[no_mangle]
pub extern "C" fn mat4_pow(a: f64, n: u32) -> f64 {
    let mut m = [0f64; 16];
    for i in 0..16 {
        m[i] = if i % 5 == 0 {
            a
        } else {
            (i as f64) * 0.125 - 1.0
        };
    }
    let mut r = [0f64; 16];
    for i in 0..4 {
        r[i * 5] = 1.0;
    }
    for _ in 0..(n % 6) {
        let mut t = [0f64; 16];
        matmul4(&r, &m, &mut t);
        r = t;
    }
    let mut tr = 0.0;
    for i in 0..4 {
        tr += r[i * 5];
    }
    tr + r[3] * 0.5 - r[12]
}

#[inline(never)]
fn gauss_solve(m: &mut [[f64; 4]; 3]) -> Option<[f64; 3]> {
    for c in 0..3 {
        let mut p = c;
        for r in c + 1..3 {
            if m[r][c].abs() > m[p][c].abs() {
                p = r;
            }
        }
        if m[p][c].abs() < 1e-12 {
            return None;
        }
        if p != c {
            for k in 0..4 {
                let t = m[c][k];
                m[c][k] = m[p][k];
                m[p][k] = t;
            }
        }
        for r in 0..3 {
            if r != c {
                let f = m[r][c] / m[c][c];
                for k in c..4 {
                    m[r][k] -= f * m[c][k];
                }
            }
        }
    }
    Some([m[0][3] / m[0][0], m[1][3] / m[1][1], m[2][3] / m[2][2]])
}

#[no_mangle]
pub extern "C" fn gauss(a: f64, b: f64) -> f64 {
    let mut m = [[a, 1.0, 2.0, 3.0], [b, a, -1.0, 0.5], [1.0, b, a + b, -2.0]];
    match gauss_solve(&mut m) {
        Some(x) => x[0] + 10.0 * x[1] + 100.0 * x[2],
        None => -12345.0,
    }
}

// Q16.16 fixed point
#[derive(Clone, Copy)]
struct Fx(i32);

impl Fx {
    #[inline(never)]
    fn mul(self, o: Fx) -> Fx {
        Fx(((self.0 as i64 * o.0 as i64) >> 16) as i32)
    }
    #[inline(never)]
    fn div(self, o: Fx) -> Option<Fx> {
        if o.0 == 0 {
            return None;
        }
        let q = ((self.0 as i64) << 16) / o.0 as i64;
        i32::try_from(q).ok().map(Fx)
    }
    #[inline(never)]
    fn sqrt(self) -> Fx {
        if self.0 <= 0 {
            return Fx(0);
        }
        let v = (self.0 as u64) << 16;
        let mut lo = 0u64;
        let mut hi = 1u64 << 32;
        for _ in 0..40 {
            if lo + 1 >= hi {
                break;
            }
            let mid = (lo + hi) / 2;
            if mid * mid <= v {
                lo = mid;
            } else {
                hi = mid;
            }
        }
        Fx(lo as i32)
    }
}

#[no_mangle]
pub extern "C" fn fixed_ops(a: i32, b: i32) -> i64 {
    let x = Fx(a);
    let y = Fx(b);
    let m = x.mul(y).0 as i64;
    let d = x.div(y).map(|f| f.0 as i64).unwrap_or(-1);
    let s = x.sqrt().0 as i64;
    m ^ (d << 20) ^ (s << 40)
}

#[no_mangle]
pub extern "C" fn fixed_poly(a: i32) -> i32 {
    // evaluate 1 + x/2 + x^2/6 + x^3/24 in Q16.16 with clamp
    let x = Fx(a.clamp(-4 << 16, 4 << 16));
    let c = [Fx(1 << 16), Fx(1 << 15), Fx(10923), Fx(2731)];
    let mut acc = Fx(0);
    for k in (0..4).rev() {
        acc = Fx(acc.mul(x).0 + c[k].0);
    }
    acc.0
}

#[no_mangle]
pub extern "C" fn float_kernels(a: f64, b: f64) -> f64 {
    let h = a * a + b * b;
    let r = a % (if b == 0.0 { 1.0 } else { b });
    let c = a.clamp(-5.0, 5.0);
    let s = a.signum() * b.copysign(a);
    let t =
        ((a * 1e3) as i64) as f64 / 1e3 + ((b * 10.0) as i32) as f64 / 10.0 + a.max(b) - b.min(a);
    let f = (a as f32 as f64)
        + b.abs()
        + a.recip() * (b as u8 as f64)
        + (b as i8 as f64) * (a as u64 as f64);
    h + r * 2.0 + c * 3.0 + s + t + f
}
