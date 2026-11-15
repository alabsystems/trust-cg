#![no_std]
#[unsafe(no_mangle)]
pub fn zeroed_words() -> u64 {
    let words: [u64; 4] = unsafe { core::mem::zeroed() };
    words[0] | words[1] | words[2] | words[3]
}
#[unsafe(no_mangle)]
pub fn zeroed_option() -> bool {
    let value: Option<core::num::NonZeroU32> = unsafe { core::mem::zeroed() };
    value.is_none()
}
