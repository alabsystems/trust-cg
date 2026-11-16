#[no_mangle]
pub extern "C" fn cap_print(x: u32) {
    println!("{:#x} {:?} {:>5}", x, Some(x), x);
}
