#![no_std]
#![feature(layout_for_ptr)]
extern crate value_layout_types;
use value_layout_types::*;
#[unsafe(no_mangle)]
pub fn byte_size(p: &[u8]) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn byte_align(p: &[u8]) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn byte_mut_size(p: &mut [u8]) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn byte_mut_align(p: &mut [u8]) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn byte_raw_size(p: *const [u8]) -> usize {
    unsafe { core::mem::size_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn byte_raw_align(p: *const [u8]) -> usize {
    unsafe { core::mem::align_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn byte_sized_size(p: &u8) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn byte_sized_align(p: &u8) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn byte_sized_raw_size(p: *const u8) -> usize {
    unsafe { core::mem::size_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn byte_sized_raw_align(p: *const u8) -> usize {
    unsafe { core::mem::align_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn byte_choose(p: &[u8], q: &[u8], first: bool) -> usize {
    core::mem::size_of_val(if first { p } else { q })
}
#[unsafe(no_mangle)]
pub fn byte_field_size(p: &Pair<'_, u8>) -> usize {
    core::mem::size_of_val(p.second)
}
#[unsafe(no_mangle)]
pub fn byte_field_align(p: &Pair<'_, u8>) -> usize {
    core::mem::align_of_val(p.second)
}
#[unsafe(no_mangle)]
pub fn byte_parts(p: *const u8, n: usize) -> usize {
    unsafe { core::mem::size_of_val_raw(core::ptr::slice_from_raw_parts(p, n)) }
}
#[unsafe(no_mangle)]
pub fn byte_sum(p: &[u8], q: &[u8], n: usize) -> usize {
    let mut i = 0usize;
    let mut sum = 0usize;
    while i < n {
        sum = sum.wrapping_add(core::mem::size_of_val(if i & 1 == 0 { p } else { q }));
        i = i.wrapping_add(1);
    }
    sum
}
#[unsafe(no_mangle)]
pub fn word_size(p: &[u16]) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn word_align(p: &[u16]) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn word_mut_size(p: &mut [u16]) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn word_mut_align(p: &mut [u16]) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn word_raw_size(p: *const [u16]) -> usize {
    unsafe { core::mem::size_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn word_raw_align(p: *const [u16]) -> usize {
    unsafe { core::mem::align_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn word_sized_size(p: &u16) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn word_sized_align(p: &u16) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn word_sized_raw_size(p: *const u16) -> usize {
    unsafe { core::mem::size_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn word_sized_raw_align(p: *const u16) -> usize {
    unsafe { core::mem::align_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn word_choose(p: &[u16], q: &[u16], first: bool) -> usize {
    core::mem::size_of_val(if first { p } else { q })
}
#[unsafe(no_mangle)]
pub fn word_field_size(p: &Pair<'_, u16>) -> usize {
    core::mem::size_of_val(p.second)
}
#[unsafe(no_mangle)]
pub fn word_field_align(p: &Pair<'_, u16>) -> usize {
    core::mem::align_of_val(p.second)
}
#[unsafe(no_mangle)]
pub fn word_parts(p: *const u16, n: usize) -> usize {
    unsafe { core::mem::size_of_val_raw(core::ptr::slice_from_raw_parts(p, n)) }
}
#[unsafe(no_mangle)]
pub fn word_sum(p: &[u16], q: &[u16], n: usize) -> usize {
    let mut i = 0usize;
    let mut sum = 0usize;
    while i < n {
        sum = sum.wrapping_add(core::mem::size_of_val(if i & 1 == 0 { p } else { q }));
        i = i.wrapping_add(1);
    }
    sum
}
#[unsafe(no_mangle)]
pub fn quad_size(p: &[u128]) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn quad_align(p: &[u128]) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn quad_mut_size(p: &mut [u128]) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn quad_mut_align(p: &mut [u128]) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn quad_raw_size(p: *const [u128]) -> usize {
    unsafe { core::mem::size_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn quad_raw_align(p: *const [u128]) -> usize {
    unsafe { core::mem::align_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn quad_sized_size(p: &u128) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn quad_sized_align(p: &u128) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn quad_sized_raw_size(p: *const u128) -> usize {
    unsafe { core::mem::size_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn quad_sized_raw_align(p: *const u128) -> usize {
    unsafe { core::mem::align_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn quad_choose(p: &[u128], q: &[u128], first: bool) -> usize {
    core::mem::size_of_val(if first { p } else { q })
}
#[unsafe(no_mangle)]
pub fn quad_field_size(p: &Pair<'_, u128>) -> usize {
    core::mem::size_of_val(p.second)
}
#[unsafe(no_mangle)]
pub fn quad_field_align(p: &Pair<'_, u128>) -> usize {
    core::mem::align_of_val(p.second)
}
#[unsafe(no_mangle)]
pub fn quad_parts(p: *const u128, n: usize) -> usize {
    unsafe { core::mem::size_of_val_raw(core::ptr::slice_from_raw_parts(p, n)) }
}
#[unsafe(no_mangle)]
pub fn quad_sum(p: &[u128], q: &[u128], n: usize) -> usize {
    let mut i = 0usize;
    let mut sum = 0usize;
    while i < n {
        sum = sum.wrapping_add(core::mem::size_of_val(if i & 1 == 0 { p } else { q }));
        i = i.wrapping_add(1);
    }
    sum
}
#[unsafe(no_mangle)]
pub fn pod_size(p: &[Pod]) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn pod_align(p: &[Pod]) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn pod_mut_size(p: &mut [Pod]) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn pod_mut_align(p: &mut [Pod]) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn pod_raw_size(p: *const [Pod]) -> usize {
    unsafe { core::mem::size_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn pod_raw_align(p: *const [Pod]) -> usize {
    unsafe { core::mem::align_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn pod_sized_size(p: &Pod) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn pod_sized_align(p: &Pod) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn pod_sized_raw_size(p: *const Pod) -> usize {
    unsafe { core::mem::size_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn pod_sized_raw_align(p: *const Pod) -> usize {
    unsafe { core::mem::align_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn pod_choose(p: &[Pod], q: &[Pod], first: bool) -> usize {
    core::mem::size_of_val(if first { p } else { q })
}
#[unsafe(no_mangle)]
pub fn pod_field_size(p: &Pair<'_, Pod>) -> usize {
    core::mem::size_of_val(p.second)
}
#[unsafe(no_mangle)]
pub fn pod_field_align(p: &Pair<'_, Pod>) -> usize {
    core::mem::align_of_val(p.second)
}
#[unsafe(no_mangle)]
pub fn pod_parts(p: *const Pod, n: usize) -> usize {
    unsafe { core::mem::size_of_val_raw(core::ptr::slice_from_raw_parts(p, n)) }
}
#[unsafe(no_mangle)]
pub fn pod_sum(p: &[Pod], q: &[Pod], n: usize) -> usize {
    let mut i = 0usize;
    let mut sum = 0usize;
    while i < n {
        sum = sum.wrapping_add(core::mem::size_of_val(if i & 1 == 0 { p } else { q }));
        i = i.wrapping_add(1);
    }
    sum
}
#[unsafe(no_mangle)]
pub fn packed_size(p: &[Packed]) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn packed_align(p: &[Packed]) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn packed_mut_size(p: &mut [Packed]) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn packed_mut_align(p: &mut [Packed]) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn packed_raw_size(p: *const [Packed]) -> usize {
    unsafe { core::mem::size_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn packed_raw_align(p: *const [Packed]) -> usize {
    unsafe { core::mem::align_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn packed_sized_size(p: &Packed) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn packed_sized_align(p: &Packed) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn packed_sized_raw_size(p: *const Packed) -> usize {
    unsafe { core::mem::size_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn packed_sized_raw_align(p: *const Packed) -> usize {
    unsafe { core::mem::align_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn packed_choose(p: &[Packed], q: &[Packed], first: bool) -> usize {
    core::mem::size_of_val(if first { p } else { q })
}
#[unsafe(no_mangle)]
pub fn packed_field_size(p: &Pair<'_, Packed>) -> usize {
    core::mem::size_of_val(p.second)
}
#[unsafe(no_mangle)]
pub fn packed_field_align(p: &Pair<'_, Packed>) -> usize {
    core::mem::align_of_val(p.second)
}
#[unsafe(no_mangle)]
pub fn packed_parts(p: *const Packed, n: usize) -> usize {
    unsafe { core::mem::size_of_val_raw(core::ptr::slice_from_raw_parts(p, n)) }
}
#[unsafe(no_mangle)]
pub fn packed_sum(p: &[Packed], q: &[Packed], n: usize) -> usize {
    let mut i = 0usize;
    let mut sum = 0usize;
    while i < n {
        sum = sum.wrapping_add(core::mem::size_of_val(if i & 1 == 0 { p } else { q }));
        i = i.wrapping_add(1);
    }
    sum
}
#[unsafe(no_mangle)]
pub fn wide_size(p: &[Wide]) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn wide_align(p: &[Wide]) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn wide_mut_size(p: &mut [Wide]) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn wide_mut_align(p: &mut [Wide]) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn wide_raw_size(p: *const [Wide]) -> usize {
    unsafe { core::mem::size_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn wide_raw_align(p: *const [Wide]) -> usize {
    unsafe { core::mem::align_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn wide_sized_size(p: &Wide) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn wide_sized_align(p: &Wide) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn wide_sized_raw_size(p: *const Wide) -> usize {
    unsafe { core::mem::size_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn wide_sized_raw_align(p: *const Wide) -> usize {
    unsafe { core::mem::align_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn wide_choose(p: &[Wide], q: &[Wide], first: bool) -> usize {
    core::mem::size_of_val(if first { p } else { q })
}
#[unsafe(no_mangle)]
pub fn wide_field_size(p: &Pair<'_, Wide>) -> usize {
    core::mem::size_of_val(p.second)
}
#[unsafe(no_mangle)]
pub fn wide_field_align(p: &Pair<'_, Wide>) -> usize {
    core::mem::align_of_val(p.second)
}
#[unsafe(no_mangle)]
pub fn wide_parts(p: *const Wide, n: usize) -> usize {
    unsafe { core::mem::size_of_val_raw(core::ptr::slice_from_raw_parts(p, n)) }
}
#[unsafe(no_mangle)]
pub fn wide_sum(p: &[Wide], q: &[Wide], n: usize) -> usize {
    let mut i = 0usize;
    let mut sum = 0usize;
    while i < n {
        sum = sum.wrapping_add(core::mem::size_of_val(if i & 1 == 0 { p } else { q }));
        i = i.wrapping_add(1);
    }
    sum
}
#[unsafe(no_mangle)]
pub fn empty_size(p: &[Empty]) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn empty_align(p: &[Empty]) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn empty_mut_size(p: &mut [Empty]) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn empty_mut_align(p: &mut [Empty]) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn empty_raw_size(p: *const [Empty]) -> usize {
    unsafe { core::mem::size_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn empty_raw_align(p: *const [Empty]) -> usize {
    unsafe { core::mem::align_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn empty_sized_size(p: &Empty) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn empty_sized_align(p: &Empty) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn empty_sized_raw_size(p: *const Empty) -> usize {
    unsafe { core::mem::size_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn empty_sized_raw_align(p: *const Empty) -> usize {
    unsafe { core::mem::align_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn empty_choose(p: &[Empty], q: &[Empty], first: bool) -> usize {
    core::mem::size_of_val(if first { p } else { q })
}
#[unsafe(no_mangle)]
pub fn empty_field_size(p: &Pair<'_, Empty>) -> usize {
    core::mem::size_of_val(p.second)
}
#[unsafe(no_mangle)]
pub fn empty_field_align(p: &Pair<'_, Empty>) -> usize {
    core::mem::align_of_val(p.second)
}
#[unsafe(no_mangle)]
pub fn empty_parts(p: *const Empty, n: usize) -> usize {
    unsafe { core::mem::size_of_val_raw(core::ptr::slice_from_raw_parts(p, n)) }
}
#[unsafe(no_mangle)]
pub fn empty_sum(p: &[Empty], q: &[Empty], n: usize) -> usize {
    let mut i = 0usize;
    let mut sum = 0usize;
    while i < n {
        sum = sum.wrapping_add(core::mem::size_of_val(if i & 1 == 0 { p } else { q }));
        i = i.wrapping_add(1);
    }
    sum
}
#[unsafe(no_mangle)]
pub fn text_size(p: &str) -> usize {
    core::mem::size_of_val(p)
}
#[unsafe(no_mangle)]
pub fn text_align(p: &str) -> usize {
    core::mem::align_of_val(p)
}
#[unsafe(no_mangle)]
pub fn text_raw_size(p: *const str) -> usize {
    unsafe { core::mem::size_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn text_raw_align(p: *const str) -> usize {
    unsafe { core::mem::align_of_val_raw(p) }
}
#[unsafe(no_mangle)]
pub fn text_choose(p: &str, q: &str, first: bool) -> usize {
    core::mem::size_of_val(if first { p } else { q })
}
#[unsafe(no_mangle)]
pub fn text_field_size(p: &StrPair<'_>) -> usize {
    core::mem::size_of_val(p.second)
}
#[unsafe(no_mangle)]
pub fn text_field_align(p: &StrPair<'_>) -> usize {
    core::mem::align_of_val(p.second)
}
