#![no_std]
unsafe extern "C" {
    fn observe(bytes: *const u8);
    fn replace(slot: *mut *const u8, value: *const u8);
}
#[unsafe(no_mangle)]
pub extern "C" fn image_plain(dst: &mut [u8; 8], pointer: *const u8) {
    *dst = pointer.addr().to_ne_bytes();
}
#[unsafe(no_mangle)]
pub extern "C" fn image_observed(dst: &mut [u8; 8], pointer: *const u8) {
    let bytes = pointer.addr().to_ne_bytes();
    unsafe {
        observe(bytes.as_ptr());
    }
    *dst = bytes;
}
#[unsafe(no_mangle)]
pub extern "C" fn image_mutable(dst: &mut [u8; 8], pointer: *mut u8) {
    let bytes = pointer.addr().to_ne_bytes();
    unsafe {
        observe(bytes.as_ptr());
    }
    *dst = bytes;
}
#[unsafe(no_mangle)]
pub extern "C" fn image_replaced(
    dst: &mut [u8; 8],
    mut pointer: *const u8,
    replacement: *const u8,
) {
    unsafe {
        replace(&raw mut pointer, replacement);
    }
    let bytes = pointer.addr().to_ne_bytes();
    unsafe {
        observe(bytes.as_ptr());
    }
    *dst = bytes;
}
#[repr(C)]
pub struct Bytes {
    pub data: [u8; 8],
}
#[unsafe(no_mangle)]
pub extern "C" fn image_return(pointer: *const u8) -> Bytes {
    Bytes {
        data: pointer.addr().to_ne_bytes(),
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn image_pair(dst: &mut [u8; 16], first: *const u8, second: *const u8) {
    for (i, pointer) in [first, second].iter().copied().enumerate() {
        let bytes = pointer.addr().to_ne_bytes();
        let start = i * bytes.len();
        dst[start..start + bytes.len()].copy_from_slice(&bytes);
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn word_to_bytes(dst: &mut [u8; 8], word: usize) {
    *dst = word.to_ne_bytes();
}
#[unsafe(no_mangle)]
pub extern "C" fn bytes_to_word(src: &[u8; 8]) -> usize {
    usize::from_ne_bytes(*src)
}
#[unsafe(no_mangle)]
pub extern "C" fn wide_to_bytes(dst: &mut [u8; 16], word: u128) {
    *dst = word.to_ne_bytes();
}
#[unsafe(no_mangle)]
pub extern "C" fn bytes_to_wide(src: &[u8; 16]) -> u128 {
    u128::from_ne_bytes(*src)
}
