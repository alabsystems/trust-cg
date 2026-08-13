// CORPUS FIXTURE — FUZZ-3 memory-model / heap differential sweep.
// Two u32 stores through `(*mut u64 as *mut u32)` + `.add(1)` into one u64 stack
// slot, read back as the whole u64 (store-to-load forwarding across narrower
// type-punned writes). Agree O0/O2/O3 -> 33.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
use core::hint::black_box;

#[no_mangle]
pub extern "C" fn main() -> i32 {

    let mut store = black_box(0u64);
    let p = &mut store as *mut u64;
    unsafe {
        *(p as *mut u32) = 0xAABBCCDD;
        *((p as *mut u32).add(1)) = 0x11223344;
    }
    let v = store;
    let r = (v & 0xff) + ((v >> 32) & 0xff);
    (r & 0xff) as i32
}
