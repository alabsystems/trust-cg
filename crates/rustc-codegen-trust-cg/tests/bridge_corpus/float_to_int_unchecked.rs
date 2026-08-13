// In-range oracle for the unsafe, non-saturating float_to_int_unchecked
// intrinsic. Out-of-range values and NaNs are deliberately absent: Rust makes
// those inputs UB, so they cannot serve as a differential oracle.
#![no_std]
#![no_main]

use core::hint::black_box;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    unsafe {
        // f32: narrow/wide, signed/unsigned, and fractional truncation.
        if black_box(-12.75f32).to_int_unchecked::<i8>() != -12 {
            return 1;
        }
        if black_box(250.75f32).to_int_unchecked::<u8>() != 250 {
            return 2;
        }
        if black_box(-123_456.75f32).to_int_unchecked::<i32>() != -123_456 {
            return 3;
        }
        if black_box(4_000_000_000.0f32).to_int_unchecked::<u64>() != 4_000_000_000 {
            return 4;
        }

        // f64: narrow/wide, signed/unsigned, and fractional truncation.
        if black_box(-100.875f64).to_int_unchecked::<i8>() != -100 {
            return 5;
        }
        if black_box(200.875f64).to_int_unchecked::<u8>() != 200 {
            return 6;
        }
        if black_box(-9_000_000_000.75f64).to_int_unchecked::<i64>() != -9_000_000_000 {
            return 7;
        }
        if black_box(9_000_000_000.75f64).to_int_unchecked::<u64>() != 9_000_000_000 {
            return 8;
        }
    }
    145
}
