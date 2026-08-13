// GOAL-3 perf baseline benchmark.
// Fixed small NxN integer matrix multiply, repeated. Row-major fixed arrays.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

const N: usize = 24;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;
    let mut rep: u32 = 0;
    while rep < 4500 {
        let mut a = [[0i64; N]; N];
        let mut b = [[0i64; N]; N];
        let mut i = 0;
        while i < N {
            let mut j = 0;
            while j < N {
                a[i][j] = ((i * 7 + j * 3 + rep as usize) % 17) as i64;
                b[i][j] = ((i * 5 + j * 11 + rep as usize) % 13) as i64;
                j += 1;
            }
            i += 1;
        }
        let mut c = [[0i64; N]; N];
        let mut r = 0;
        while r < N {
            let mut col = 0;
            while col < N {
                let mut s: i64 = 0;
                let mut k = 0;
                while k < N {
                    s = s.wrapping_add(a[r][k].wrapping_mul(b[k][col]));
                    k += 1;
                }
                c[r][col] = s;
                col += 1;
            }
            r += 1;
        }
        let mut t: i64 = 0;
        let mut d = 0;
        while d < N {
            t = t.wrapping_add(c[d][d]);
            d += 1;
        }
        acc = acc.wrapping_add(t as u64);
        rep += 1;
    }
    (acc & 0xff) as i32
}
