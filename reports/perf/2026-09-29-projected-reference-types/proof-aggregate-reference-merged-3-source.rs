#![no_std]
#[repr(C)]
pub struct Arrays {
    pub first: [u32; 3],
    pub last: [u32; 3],
}
#[repr(C)]
pub struct Triple {
    pub a: u32,
    pub b: u32,
    pub c: u32,
}
#[repr(C)]
pub struct Records {
    pub tag: u64,
    pub values: [Triple; 3],
}
#[unsafe(no_mangle)]
pub fn first_array_field(v: &Arrays) -> &[u32; 3] {
    &v.first
}
#[unsafe(no_mangle)]
pub fn last_array_field(v: &Arrays) -> &[u32; 3] {
    &v.last
}
#[unsafe(no_mangle)]
pub fn last_array_field_mut(v: &mut Arrays) -> &mut [u32; 3] {
    &mut v.last
}
#[unsafe(no_mangle)]
pub fn indexed_record(v: &Records, i: usize) -> &Triple {
    &v.values[i]
}
#[unsafe(no_mangle)]
pub fn indexed_record_mut(v: &mut Records, i: usize) -> &mut Triple {
    &mut v.values[i]
}
#[unsafe(no_mangle)]
pub fn reborrow_array_field(v: &Arrays) -> &[u32; 3] {
    let raw = &v.last as *const [u32; 3];
    unsafe { &*raw }
}

#[unsafe(no_mangle)]
pub fn shared_from_mut_array(v: &mut Arrays) -> &[u32; 3] {
    let part = &mut v.last;
    &*part
}
#[unsafe(no_mangle)]
pub fn shared_from_mut_record(v: &mut Records, i: usize) -> &Triple {
    let part = &mut v.values[i];
    &*part
}
