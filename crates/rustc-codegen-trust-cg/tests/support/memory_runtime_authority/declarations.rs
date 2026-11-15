// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
// Foreign declarations are inspected by the compiler-query driver, never called.

use core::ffi::{c_int, c_void};

unsafe extern "C" {
    pub static NOT_A_FUNCTION: usize;
    pub fn valid_copy(dst: *mut c_void, src: *const c_void, count: usize) -> *mut c_void;
    pub fn valid_move(dst: *mut c_void, src: *const c_void, count: usize) -> *mut c_void;
    pub fn valid_set(dst: *mut c_void, value: c_int, count: usize) -> *mut c_void;
    pub fn too_few(dst: *mut c_void, src: *const c_void) -> *mut c_void;
    pub fn too_many(
        dst: *mut c_void,
        src: *const c_void,
        count: usize,
        extra: usize,
    ) -> *mut c_void;
    pub fn const_destination(dst: *const c_void, src: *const c_void, count: usize)
    -> *const c_void;
    pub fn scalar_destination(dst: usize, src: *const c_void, count: usize) -> usize;
    pub fn mutable_source(dst: *mut c_void, src: *mut c_void, count: usize) -> *mut c_void;
    pub fn scalar_source(dst: *mut c_void, src: usize, count: usize) -> *mut c_void;
    pub fn wide_fill(dst: *mut c_void, value: i64, count: usize) -> *mut c_void;
    pub fn unsigned_fill(dst: *mut c_void, value: u32, count: usize) -> *mut c_void;
    pub fn wrong_length(dst: *mut c_void, src: *const c_void, count: u32) -> *mut c_void;
    pub fn void_result(dst: *mut c_void, src: *const c_void, count: usize);
    pub fn different_result(dst: *mut u8, src: *const u8, count: usize) -> *mut u16;
    pub fn variadic_copy(dst: *mut c_void, src: *const c_void, count: usize, ...) -> *mut c_void;
}

unsafe extern "C-unwind" {
    pub fn unwinding_copy(dst: *mut c_void, src: *const c_void, count: usize) -> *mut c_void;
}

pub unsafe extern "C" fn defined_function(
    dst: *mut c_void,
    _src: *const c_void,
    _count: usize,
) -> *mut c_void {
    dst
}

pub struct NotAFunction {
    pub byte: u8,
}
