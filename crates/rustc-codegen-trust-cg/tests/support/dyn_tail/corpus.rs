#![no_std]
#![feature(ptr_metadata)]
extern crate dyn_tail_types;
use dyn_tail_types::*;

#[unsafe(no_mangle)]
pub fn dyn_identity(p: &mut Outer<dyn Payload>) -> &mut Outer<dyn Payload> {
    p
}
#[unsafe(no_mangle)]
pub fn dyn_tail(p: &Outer<dyn Payload>) -> &dyn Payload {
    &p.nested.node.value
}
#[unsafe(no_mangle)]
pub fn dyn_tail_mut(p: &mut Outer<dyn Payload>) -> &mut dyn Payload {
    &mut p.nested.node.value
}
#[unsafe(no_mangle)]
pub fn dyn_inner(p: &mut Outer<dyn Payload>) -> &mut Inner<dyn Payload> {
    &mut p.nested
}
#[unsafe(no_mangle)]
pub fn dyn_header(p: &mut Outer<dyn Payload>) -> &mut Header<dyn Payload> {
    &mut p.nested.node
}
#[unsafe(no_mangle)]
pub fn dyn_prefix(p: &mut Outer<dyn Payload>) -> &mut u64 {
    &mut p.nested.node.epoch
}
#[unsafe(no_mangle)]
pub fn dyn_size(p: &Outer<dyn Payload>) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn dyn_align(p: &Outer<dyn Payload>) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn dyn_inner_size(p: &Inner<dyn Payload>) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn dyn_inner_align(p: &Inner<dyn Payload>) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn dyn_head(p: &Outer<dyn Payload>) -> u64 {
    p.lead as u64 + p.nested.prefix[2] as u64 + p.nested.node.marker as u64 + p.nested.node.epoch
}
#[unsafe(no_mangle)]
pub fn dyn_update(p: &mut Outer<dyn Payload>, value: u64) -> u64 {
    p.nested.node.epoch = p.nested.node.epoch.wrapping_add(value);
    p.nested.prefix[2] ^= value as u8;
    p.nested.node.value.bump(value)
}
#[unsafe(no_mangle)]
pub fn dyn_unsize_small(p: &mut Outer<Small>) -> &mut Outer<dyn Payload> {
    p
}
#[unsafe(no_mangle)]
pub fn dyn_unsize_word(p: &mut Outer<Word>) -> &mut Outer<dyn Payload> {
    p
}
#[unsafe(no_mangle)]
pub fn dyn_unsize_wide(p: &mut Outer<Wide>) -> &mut Outer<dyn Payload> {
    p
}
#[unsafe(no_mangle)]
pub fn dyn_unsize_empty(p: &mut Outer<Empty>) -> &mut Outer<dyn Payload> {
    p
}
#[unsafe(no_mangle)]
pub fn dyn_transparent(p: &Transparent<dyn Payload>) -> (usize, usize, u64) {
    (
        core::mem::size_of_val(p),
        core::mem::align_of_val(p),
        p.0.nested.node.value.read(),
    )
}
#[unsafe(no_mangle)]
pub fn dyn_rust(p: &RustHeader<dyn Payload>) -> (usize, usize, u128, u64) {
    (
        core::mem::size_of_val(p),
        core::mem::align_of_val(p),
        p.count,
        p.value.read(),
    )
}
#[unsafe(no_mangle)]
pub fn dyn_meta(p: *mut Outer<dyn Payload>) -> core::ptr::DynMetadata<dyn Payload> {
    core::ptr::metadata(p)
}
#[unsafe(no_mangle)]
pub fn dyn_parts(p: *mut (), meta: core::ptr::DynMetadata<dyn Payload>) -> *mut Outer<dyn Payload> {
    core::ptr::from_raw_parts_mut(p, meta)
}
#[unsafe(no_mangle)]
pub fn dyn_spill(
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
    f: u64,
    g: u64,
    p: &Outer<dyn Payload>,
) -> u64 {
    a ^ b ^ c ^ d ^ e ^ f ^ g ^ p.nested.node.value.read()
}

#[unsafe(no_mangle)]
pub fn dyn_upcast(p: &Outer<dyn Payload>) -> &Outer<dyn Right> {
    p
}
#[unsafe(no_mangle)]
pub fn dyn_right(p: &Outer<dyn Right>) -> u64 {
    p.nested.node.value.right()
}
#[unsafe(no_mangle)]
pub fn dyn_choose<'a>(
    a: &'a Outer<dyn Payload>,
    b: &'a Outer<dyn Payload>,
    take_a: bool,
) -> &'a Outer<dyn Payload> {
    if take_a { a } else { b }
}

#[inline(never)]
fn update_local(p: &mut Header<dyn Payload>, by: u64) -> u64 {
    p.epoch ^= by;
    p.value.bump(by)
}

#[unsafe(no_mangle)]
pub fn dyn_local(seed: u64, by: u64) -> (u8, u64, u64, u64) {
    let mut local = Header {
        marker: seed as u8,
        epoch: seed,
        value: Word(!seed),
    };
    let result = update_local(&mut local, by);
    (local.marker, local.epoch, local.value.0, result)
}
