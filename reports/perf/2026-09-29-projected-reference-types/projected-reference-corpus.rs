#![no_std]
#[repr(C)]
pub struct Triple {
    pub a: u32,
    pub b: u32,
    pub c: u32,
}
#[unsafe(no_mangle)]
pub fn first_array(value: &[u32; 3]) -> &u32 {
    &value[0]
}
#[unsafe(no_mangle)]
pub fn last_array(value: &[u32; 3]) -> &u32 {
    &value[2]
}
#[unsafe(no_mangle)]
pub fn first_struct(value: &Triple) -> &u32 {
    &value.a
}
#[unsafe(no_mangle)]
pub fn last_struct(value: &Triple) -> &u32 {
    &value.c
}
#[unsafe(no_mangle)]
pub fn mutate_array(value: &mut [u32; 3]) -> &mut u32 {
    &mut value[0]
}
#[unsafe(no_mangle)]
pub fn mutate_struct(value: &mut Triple) -> &mut u32 {
    &mut value.c
}

#[repr(C)]
pub struct Nested {
    pub first: u32,
    pub rest: [u32; 2],
}
pub struct Reordered {
    pub small: u8,
    pub big: u64,
    pub middle: u16,
}
#[unsafe(no_mangle)]
pub fn first_nested(value: &Nested) -> &u32 {
    &value.first
}
#[unsafe(no_mangle)]
pub fn first_nested_mut(value: &mut Nested) -> &mut u32 {
    &mut value.first
}
#[unsafe(no_mangle)]
pub fn first_reordered(value: &Reordered) -> &u64 {
    &value.big
}
#[unsafe(no_mangle)]
pub fn first_reborrow(value: &Triple) -> &u32 {
    let r = &value.a;
    unsafe { &*(r as *const u32) }
}
#[unsafe(no_mangle)]
pub fn last_reborrow(value: &Triple) -> &u32 {
    let r = &value.c;
    unsafe { &*(r as *const u32) }
}

#[unsafe(no_mangle)]
pub fn choose_shared(value: &Triple, first: bool) -> &u32 {
    if first { &value.a } else { &value.c }
}
#[unsafe(no_mangle)]
pub fn choose_mut(value: &mut Triple, first: bool) -> &mut u32 {
    if first { &mut value.a } else { &mut value.c }
}
#[unsafe(no_mangle)]
pub fn call_first(value: &Triple, callback: fn(&u32) -> u32) -> u32 {
    callback(&value.a)
}
#[unsafe(no_mangle)]
pub fn call_last(value: &mut Triple, callback: fn(&mut u32)) {
    callback(&mut value.c);
}
