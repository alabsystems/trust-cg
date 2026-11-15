#![no_std]
extern crate alloc;
use alloc::string::String;
use alloc::vec::Vec;

unsafe extern "Rust" {
    fn touch_vec(value: &mut Vec<u8>, seed: u64) -> u64;
}

#[inline(never)]
fn read_bytes(value: &[u8]) -> u64 {
    let mut out = value.len() as u64;
    let mut i = 0;
    while i < value.len() {
        out = out.wrapping_mul(37).wrapping_add(value[i] as u64);
        i += 1;
    }
    out
}

#[unsafe(no_mangle)]
pub fn constant_bytes(which: u32) -> u64 {
    match which {
        0 => read_bytes("".as_bytes()),
        1 => read_bytes("replacement: �".as_bytes()),
        2 => read_bytes("éΣ🙂".as_bytes()),
        _ => read_bytes("\0ab\0".as_bytes()),
    }
}

#[unsafe(no_mangle)]
pub fn const_reinterpret() -> u64 {
    const WORDS: &[u16] = &[0x1234, 0xabcd, 0x8001];
    let bytes: &[u8] = unsafe { core::mem::transmute(WORDS) };
    read_bytes(bytes)
}

#[unsafe(no_mangle)]
pub fn char_indices(text: &str) -> u64 {
    let mut out = 3u64;
    for (i, c) in text.char_indices() {
        out = out
            .wrapping_mul(71)
            .wrapping_add(i as u64)
            .wrapping_add(c as u64);
    }
    out
}

#[unsafe(no_mangle)]
pub fn embedded_vec(value: &mut String, seed: u64) -> u64 {
    let out = unsafe { touch_vec(value.as_mut_vec(), seed) };
    out ^ value.len() as u64
}

#[unsafe(no_mangle)]
pub fn embedded_owned(bytes: Vec<u8>, seed: u64) -> u64 {
    let mut value = unsafe { String::from_utf8_unchecked(bytes) };
    let out = unsafe { touch_vec(value.as_mut_vec(), seed) };
    read_bytes(value.as_bytes()) ^ out ^ value.len() as u64
}
