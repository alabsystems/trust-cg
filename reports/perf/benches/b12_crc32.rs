// GOAL-3 perf baseline benchmark.
// CRC32 (bitwise, polynomial 0xEDB88320) over a fixed buffer, repeated.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

const N: usize = 512;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let mut buf = [0u8; N];
    let mut i = 0;
    while i < N {
        buf[i] = ((i.wrapping_mul(131).wrapping_add(17)) & 0xff) as u8;
        i += 1;
    }
    let mut acc: u64 = 0;
    let mut rep: u32 = 0;
    while rep < 14000 {
        let mut crc: u32 = 0xffffffff;
        let mut k = 0;
        while k < N {
            crc ^= (buf[k] ^ (rep as u8)) as u32;
            let mut bit = 0;
            while bit < 8 {
                let mask = (crc & 1).wrapping_neg();
                crc = (crc >> 1) ^ (0xEDB88320 & mask);
                bit += 1;
            }
            k += 1;
        }
        acc = acc.wrapping_add((!crc) as u64);
        rep += 1;
    }
    (acc & 0xff) as i32
}
