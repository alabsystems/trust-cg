// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
#![feature(rustc_private)]
#[cfg(rustc_goto_loop_hints)]
extern crate rustc_attr_ir;
extern crate rustc_driver;
extern crate rustc_middle;
#[path = "../../../src/mir_goto.rs"]
mod mir_goto;
