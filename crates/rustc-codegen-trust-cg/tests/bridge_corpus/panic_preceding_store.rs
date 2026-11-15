use std::hint::black_box;
#[no_mangle]
static mut FLAG: u8 = 0;
unsafe extern "C" {
    fn getenv(name: *const std::ffi::c_char) -> *const std::ffi::c_char;
}
#[inline(never)]
fn fail_literal(value: u8) -> ! {
    unsafe {
        FLAG = value;
    }
    panic!("boom");
}
#[inline(never)]
fn fail_unreachable(value: u8) -> ! {
    unsafe {
        FLAG = value;
    }
    unreachable!();
}
#[inline(never)]
fn fail_formatted(value: u8) -> ! {
    unsafe {
        FLAG = value;
    }
    panic!("boom {value}");
}
#[inline(never)]
fn store_and_return(value: u8) {
    unsafe {
        FLAG = value;
    }
}
fn main() {
    std::panic::set_hook(Box::new(|_| {
        std::process::exit(unsafe { FLAG } as i32);
    }));
    let selector = unsafe { getenv(c"PANIC_SHAPE".as_ptr()) };
    let shape = if selector.is_null() {
        0
    } else {
        (unsafe { *selector }) as u8
    };
    let value = black_box(73u8);
    match shape {
        b'l' => fail_literal(value),
        b'u' => fail_unreachable(value),
        b'f' => fail_formatted(value),
        _ => store_and_return(value),
    }
    std::process::exit(unsafe { FLAG } as i32);
}
