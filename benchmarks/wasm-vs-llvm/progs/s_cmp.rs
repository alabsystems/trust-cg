#![no_std]
#![allow(dead_code)]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[inline(never)]
fn pick(k: u32) -> &'static str {
    match k % 8 {
        0 => "  hello world  ",
        1 => "key=value; other=42",
        2 => "",
        3 => "ÄÖü straße ß",
        4 => "a,b,,c,",
        5 => "line1\nline2\r\nline3",
        6 => "   ",
        _ => "MiXeD CaSe 123",
    }
}

#[no_mangle]
pub extern "C" fn s_cmp(a: u32, b: u32) -> i32 {
    let x = pick(a);
    let y = pick(b);
    let o = x.cmp(y) as i32;
    let e = (x == y) as i32;
    let l = (x < y) as i32;
    o * 100 + e * 10 + l
}
