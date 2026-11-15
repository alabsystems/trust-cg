#![no_std]
pub fn case_plain(_: u32) {}
pub fn case_type<T>(_: T) {}
pub fn case_two_types<T, U>(_: T, _: U) {}
pub fn case_const<const N: usize>(_: &[u8; N]) {}
pub fn case_two_consts<const N: usize, const M: usize>(_: &[u8; N], _: &[u8; M]) {}
pub fn case_region<'a: 'a>(_: &'a str) {}
pub fn case_two_regions<'a: 'a, 'b: 'b>(_: &'a str, _: &'b str) {}
pub fn case_mixed<'a: 'a, T, const N: usize>(_: &'a [T; N]) {}
pub fn case_reference<T>(_: &T) {}
pub fn case_array<T, const N: usize>(_: [T; N]) {}
pub fn case_higher(_: for<'a> fn(&'a u8) -> &'a u8) {}
pub fn case_fn_bound<F: for<'a> Fn(&'a u8) -> &'a u8>(_: F) {}
