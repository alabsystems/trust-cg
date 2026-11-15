#![no_std]

#[repr(C)]
pub struct Record {
    pub tag: u64,
    pub bytes: [u8; 16],
}

#[repr(C)]
pub struct Bytes {
    pub bytes: [u8; 16],
}

unsafe extern "C" {
    fn replace_word<'a>(slot: &mut &'a u64, other: &'a u64);
    fn replace_record<'a>(slot: &mut &'a Record, other: &'a Record);
    fn choose_word<'a>(a: &'a u64, b: &'a u64) -> &'a u64;
    fn observe_word(slot: &mut &u64);
}

#[unsafe(no_mangle)]
pub extern "C" fn word_address<'a>(mut p: &'a u64, other: &'a u64) -> *const u64 {
    unsafe { replace_word(&mut p, other) };
    p as *const u64
}

#[unsafe(no_mangle)]
pub extern "C" fn field_address<'a>(mut p: &'a Record, other: &'a Record) -> *const u8 {
    unsafe { replace_record(&mut p, other) };
    &raw const p.bytes[7]
}

#[unsafe(no_mangle)]
pub extern "C" fn nested_copy<'a>(mut p: &'a Record, other: &'a Record) -> Bytes {
    unsafe { replace_record(&mut p, other) };
    Bytes { bytes: p.bytes }
}

#[unsafe(no_mangle)]
pub extern "C" fn nested_into<'a>(mut p: &'a Record, other: &'a Record, out: &mut Record) {
    unsafe { replace_record(&mut p, other) };
    *out = Record {
        tag: p.tag,
        bytes: p.bytes,
    };
}

#[unsafe(no_mangle)]
pub extern "C" fn local_address(a: &u64, b: &u64) -> *const u64 {
    let mut p = unsafe { choose_word(a, b) };
    unsafe { replace_word(&mut p, b) };
    p as *const u64
}

#[unsafe(no_mangle)]
pub extern "C" fn branch_address<'a>(mut p: &'a u64, other: &'a u64, take: u8) -> *const u64 {
    if take != 0 {
        unsafe { replace_word(&mut p, other) };
    } else {
        unsafe { observe_word(&mut p) };
    }
    p as *const u64
}
