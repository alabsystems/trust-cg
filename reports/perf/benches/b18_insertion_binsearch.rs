// GOAL-3 perf baseline benchmark.
// Insertion sort + binary search probes over a fixed array, repeated.
// Lots of array indexing, comparisons, and inner shifting.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

const N: usize = 300;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut acc: u64 = 0;
    let mut rep: u32 = 0;
    while rep < 1600 {
        let mut arr = [0i32; N];
        let mut i = 0;
        while i < N {
            arr[i] = (((i as i32).wrapping_mul(48271).wrapping_add(rep as i32)) % 1000) - 500;
            i += 1;
        }
        // insertion sort
        let mut a = 1;
        while a < N {
            let key = arr[a];
            let mut b = a;
            while b > 0 && arr[b - 1] > key {
                arr[b] = arr[b - 1];
                b -= 1;
            }
            arr[b] = key;
            a += 1;
        }
        // binary search probes
        let mut found: u64 = 0;
        let mut q = 0;
        while q < N {
            let target = (((q as i32).wrapping_mul(7) + rep as i32) % 1000) - 500;
            let mut lo: isize = 0;
            let mut hi: isize = (N as isize) - 1;
            while lo <= hi {
                let mid = (lo + hi) / 2;
                let v = arr[mid as usize];
                if v == target {
                    found += 1;
                    break;
                } else if v < target {
                    lo = mid + 1;
                } else {
                    hi = mid - 1;
                }
            }
            q += 1;
        }
        acc = acc.wrapping_add(found).wrapping_add(arr[0] as u64 & 0xff);
        rep += 1;
    }
    (acc & 0xff) as i32
}
