#![no_std]
#[inline(never)]
fn assembly<const N: bool>(value: u64) -> u64 {
    unsafe { core::arch::asm!("nop", options(nomem, nostack, preserves_flags)) };
    value
}
#[inline(never)]
fn choose<const ENABLED: bool>(value: u64) -> u64 {
    if const { ENABLED } {
        assembly::<ENABLED>(value)
    } else {
        value.wrapping_add(7)
    }
}
#[unsafe(no_mangle)]
pub fn cfg_entry(value: u64, dynamic: bool) -> u64 {
    #[cfg(dead)]
    {
        let _ = dynamic;
        choose::<false>(value)
    }
    #[cfg(live)]
    {
        let _ = dynamic;
        choose::<true>(value)
    }
    #[cfg(dynamic_branch)]
    {
        if dynamic {
            choose::<true>(value)
        } else {
            choose::<false>(value)
        }
    }
}
