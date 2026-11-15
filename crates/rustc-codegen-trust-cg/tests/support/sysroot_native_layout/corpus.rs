#![no_std]

#[unsafe(no_mangle)]
pub fn native_chars(text: &str, stop: char) -> u64 {
    text.chars()
        .rev()
        .skip_while(|c| *c == stop)
        .fold(1, |acc, c| acc.wrapping_mul(31).wrapping_add(c as u64))
}

#[unsafe(no_mangle)]
pub fn native_utf16(text: &[u16]) -> u64 {
    core::char::decode_utf16(text.iter().copied())
        .map(|r| r.unwrap_or('\u{fffd}'))
        .fold(7, |acc, c| acc.wrapping_mul(37).wrapping_add(c as u64))
}

#[unsafe(no_mangle)]
pub fn native_str_sum(parts: &[&str]) -> usize {
    parts.iter().map(|s| s.len()).sum()
}

#[unsafe(no_mangle)]
pub fn native_array_back(values: [u32; 3]) -> u64 {
    let mut values = values.into_iter();
    let last = values.next_back().unwrap();
    let first = values.next().unwrap();
    let middle = values.next_back().unwrap();
    u64::from(last) + 17 * u64::from(first) + 71 * u64::from(middle)
}

#[unsafe(no_mangle)]
pub fn native_take(values: &[u8]) -> usize {
    let mut it = values.iter();
    let old = core::mem::take(&mut it);
    old.len() * 7 + it.len()
}

#[unsafe(no_mangle)]
pub fn native_chunks(values: &[u64], size: usize) -> u64 {
    let mut chunks = values.chunks(size);
    let mut out = chunks.len() as u64;
    while let Some(chunk) = chunks.next_back() {
        out = out.wrapping_mul(43).wrapping_add(chunk[0]);
    }
    out
}
