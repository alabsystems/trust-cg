unsafe extern "Rust" {
    #[link_name = "_RNvNtNtCs6JUzFDSTeYc_4core3str5count14do_count_chars"]
    fn count_chars(s: &str) -> usize;

}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn library_count(data: *const u8, n: usize) -> usize {
    unsafe { count_chars(core::str::from_utf8_unchecked(core::slice::from_raw_parts(data, n))) }
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn library_validate(data: *const u8, n: usize, valid: *mut usize, error_len: *mut usize) -> bool {
    match core::str::from_utf8(unsafe {core::slice::from_raw_parts(data, n)}) {
        Ok(value) => { unsafe { *valid = value.len(); *error_len = 0; } true }
        Err(error) => { unsafe { *valid = error.valid_up_to(); *error_len = error.error_len().unwrap_or(0); } false }
    }
}
