// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
// The modern compiler must reject a second canonical symbol before CG can run.
#![no_std]
#![feature(rustc_attrs)]
#![allow(internal_features)]

include!("declarations.rs");

unsafe extern "C" {
    #[rustc_canonical_symbol]
    #[link_name = "memcpy"]
    pub fn conflicting_copy(dst: *mut c_void, src: *const c_void, count: usize) -> *mut c_void;
}
