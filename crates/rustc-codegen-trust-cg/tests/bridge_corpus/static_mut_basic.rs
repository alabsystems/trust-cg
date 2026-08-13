// Reaudit gap E (d8aed8b): a `static mut` is supported as a writable cross-object
// data global (def emits mutable+External; readers IMPORT the canonical symbol and
// address it via a SIGNED reloc). Pins that a basic write-then-read compiles and
// reads back the UPDATED value (42), never a stale/miscompiled one.
#![no_std]
#![no_main]
use core::hint::black_box;
#[panic_handler] fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }
static mut CTR: u32 = 0;
#[no_mangle] pub extern "C" fn main() -> i32 {
    unsafe { CTR = black_box(40u32); CTR += black_box(2u32); (CTR % 126) as i32 }
}
