#![no_std]
#![feature(f16)]
use core::arch::aarch64::{float16x4_t, float16x8_t, uint16x4_t};

pub fn case_scalar(_: &f16) {}
pub fn case_array_zero(_: &[f16; 0]) {}
pub fn case_array_one(_: &[f16; 1]) {}
pub fn case_array_three(_: &[f16; 3]) {}
pub fn case_array_four(_: &[f16; 4]) {}
pub fn case_array_eight(_: &[f16; 8]) {}
pub fn case_vector_four(_: &float16x4_t) {}
pub fn case_vector_eight(_: &float16x8_t) {}
pub fn case_integer_vector_four(_: &uint16x4_t) {}
pub fn case_uint(_: &u16) {}
pub fn case_raw_vector_four(_: *const float16x4_t) {}
pub fn case_mut_vector_eight(_: *mut float16x8_t) {}
