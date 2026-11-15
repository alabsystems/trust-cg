#![no_std]
use core::fmt::Debug;
#[inline(never)]
fn choose<'a, T>(flag: bool, left: &'a T, right: &'a T) -> &'a T {
    if flag { left } else { right }
}
#[inline(never)]
fn choose_mut<'a, T>(flag: bool, left: &'a mut T, right: &'a mut T) -> &'a mut T {
    if flag { left } else { right }
}
#[unsafe(no_mangle)]
pub fn pick_slice<'a, 'b>(flag: bool, a: &'a &'b [u64], b: &'a &'b [u64]) -> &'a &'b [u64] {
    choose(flag, a, b)
}
#[unsafe(no_mangle)]
pub fn pick_text<'a, 'b>(flag: bool, a: &'a &'b str, b: &'a &'b str) -> &'a &'b str {
    choose(flag, a, b)
}
#[unsafe(no_mangle)]
pub fn pick_object<'a, 'b>(
    flag: bool,
    a: &'a &'b dyn Debug,
    b: &'a &'b dyn Debug,
) -> &'a &'b dyn Debug {
    choose(flag, a, b)
}
#[unsafe(no_mangle)]
pub fn pick_raw_slice<'a>(
    flag: bool,
    a: &'a *const [u64],
    b: &'a *const [u64],
) -> &'a *const [u64] {
    choose(flag, a, b)
}
#[unsafe(no_mangle)]
pub fn pick_raw_text<'a>(flag: bool, a: &'a *const str, b: &'a *const str) -> &'a *const str {
    choose(flag, a, b)
}
#[unsafe(no_mangle)]
pub fn pick_raw_object<'a>(
    flag: bool,
    a: &'a *const dyn Debug,
    b: &'a *const dyn Debug,
) -> &'a *const dyn Debug {
    choose(flag, a, b)
}
#[unsafe(no_mangle)]
pub fn pick_object_mut<'a, 'b>(
    flag: bool,
    a: &'a mut &'b dyn Debug,
    b: &'a mut &'b dyn Debug,
) -> &'a mut &'b dyn Debug {
    choose_mut(flag, a, b)
}
