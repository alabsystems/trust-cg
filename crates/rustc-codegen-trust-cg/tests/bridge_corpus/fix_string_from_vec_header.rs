// Preserve a Vec's complete header through a String construction and return.
// Separate empty String headers must remain independent after MIR CSE.
use std::hint::black_box;

#[inline(never)]
fn convert(bytes: Vec<u8>) -> String {
    unsafe { String::from_utf8_unchecked(bytes) }
}

fn main() {
    for size in [0usize, 1, 5, 17, 128] {
        let size = black_box(size);
        let mut bytes = Vec::with_capacity(size + 16);
        for i in 0..size {
            bytes.push(b'a' + (i % 26) as u8);
        }
        let ptr = bytes.as_ptr();
        let cap = bytes.capacity();
        let s = convert(bytes);
        if s.len() != size || s.as_ptr() != ptr || s.capacity() != cap {
            std::process::exit(71);
        }
        for i in 0..size {
            if s.as_bytes()[i] != b'a' + (i % 26) as u8 {
                std::process::exit(72);
            }
        }
        drop(s);
    }
    let mut first = String::new();
    let mut second = String::new();
    first.push_str(black_box("x"));
    second.push_str(black_box("yz"));
    if first.as_bytes() != b"x" || second.as_bytes() != b"yz" {
        std::process::exit(73);
    }
    drop(first);
    drop(second);
}
