// GOAL-3 perf baseline benchmark.
// Fixed-point (Q16.16 in i64) Mandelbrot escape-iteration over a small grid.
// All-integer (no float) so it isolates integer mul/shift/compare throughput.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

const W: i64 = 48;
const H: i64 = 32;
const SCALE: i64 = 1 << 16;
const MAXIT: i64 = 100;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;
    let mut rep: u32 = 0;
    while rep < 280 {
        let mut count: u64 = 0;
        let mut py: i64 = 0;
        while py < H {
            let mut px: i64 = 0;
            while px < W {
                // map pixel to complex plane in Q16.16
                let cx = (px * 3 * SCALE) / W - 2 * SCALE;
                let cy = (py * 2 * SCALE) / H - SCALE;
                let mut zx: i64 = 0;
                let mut zy: i64 = 0;
                let mut it: i64 = 0;
                while it < MAXIT {
                    let zx2 = (zx * zx) >> 16;
                    let zy2 = (zy * zy) >> 16;
                    if zx2 + zy2 > 4 * SCALE {
                        break;
                    }
                    let xy = (zx * zy) >> 16;
                    zx = zx2 - zy2 + cx;
                    zy = 2 * xy + cy;
                    it += 1;
                }
                count = count.wrapping_add(it as u64);
                px += 1;
            }
            py += 1;
        }
        acc = acc.wrapping_add(count);
        rep += 1;
    }
    (acc & 0xff) as i32
}
