#![no_std]
use core::mem::{MaybeUninit, transmute};

#[derive(Clone, Copy)]
union Words {
    words: [u64; 4],
    bytes: [u8; 32],
}

#[derive(Clone, Copy)]
#[repr(C, packed)]
union Packed {
    words: [u64; 3],
    bytes: [u8; 24],
}

#[unsafe(no_mangle)]
pub extern "C" fn zeroed_four(seed: u64, index: usize) -> u64 {
    let mut words: [u64; 4] = unsafe { core::mem::zeroed() };
    words[index & 3] = seed;
    words[0] ^ words[1].rotate_left(7) ^ words[2].rotate_left(19) ^ words[3].rotate_left(37)
}

#[unsafe(no_mangle)]
pub extern "C" fn assume_four(seed: u64, index: usize) -> u64 {
    let image = MaybeUninit::new([seed, !seed, seed.rotate_left(17), seed.wrapping_add(91)]);
    let words = unsafe { image.assume_init() };
    words[index & 3]
}

#[unsafe(no_mangle)]
pub extern "C" fn union_four(seed: u64, index: usize) -> u64 {
    let words = [seed, !seed, seed.rotate_left(17), seed.wrapping_add(91)];
    let image: Words = unsafe { transmute(words) };
    let restored: [u64; 4] = unsafe { transmute(image) };
    restored[index & 3]
}

#[unsafe(no_mangle)]
pub extern "C" fn packed_three(seed: u64, index: usize) -> u64 {
    let words = [seed, !seed, seed.rotate_left(17)];
    let image: Packed = unsafe { transmute(words) };
    let restored: [u64; 3] = unsafe { transmute(image) };
    restored[index % 3]
}

#[unsafe(no_mangle)]
pub extern "C" fn branch_four(seed: u64, index: usize) -> u64 {
    let image = if index & 4 == 0 {
        MaybeUninit::new([seed, !seed, seed.rotate_left(17), seed.wrapping_add(91)])
    } else {
        MaybeUninit::new([!seed, seed, seed.wrapping_add(91), seed.rotate_left(17)])
    };
    let words = unsafe { image.assume_init() };
    words[index & 3]
}

#[unsafe(no_mangle)]
pub extern "C" fn nested_words(seed: u64, index: usize) -> u64 {
    let image = MaybeUninit::new([[seed, !seed], [seed.rotate_left(17), seed.wrapping_add(91)]]);
    let words = unsafe { image.assume_init() };
    words[(index >> 1) & 1][index & 1]
}

#[unsafe(no_mangle)]
pub extern "C" fn pointer_words(seed: u64, index: usize) -> u64 {
    let a = seed;
    let b = !seed;
    let image = MaybeUninit::new([&a as *const u64, &b as *const u64]);
    let pointers = unsafe { image.assume_init() };
    unsafe { *pointers[index & 1] }
}

#[unsafe(no_mangle)]
pub extern "C" fn float_words(seed: u64, index: usize) -> u64 {
    let image = MaybeUninit::new([seed as f64, (seed as u32) as f64, -1.25, 0.0]);
    let values = unsafe { image.assume_init() };
    values[index & 3].to_bits()
}
