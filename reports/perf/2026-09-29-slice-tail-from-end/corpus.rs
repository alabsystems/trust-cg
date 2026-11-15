#![no_std]
#[unsafe(no_mangle)]
pub fn tail_word(words: &[u64]) -> u64 {
    match words { [.., last] => *last, _ => 0 }
}
#[unsafe(no_mangle)]
pub fn end_words(words: &[u64]) -> u64 {
    match words { [first, .., last] => *first ^ *last, _ => 0 }
}
#[unsafe(no_mangle)]
pub fn tail_mut(words: &mut [u64], mask: u64) -> u64 {
    match words { [.., last] => { *last ^= mask; *last }, _ => 0 }
}
