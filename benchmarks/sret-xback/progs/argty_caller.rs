// The CALLER half of the indirect-return cross-boundary gate. Exits 42 when the
// aggregate arrives intact; any other status is an ABI disagreement.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
extern crate sretcallee;
use sretcallee::ArgTy;

fn main() {
    let v = 42i32;
    let code = match sretcallee::probe_make(&v) {
        ArgTy::Placeholder { value, .. } => unsafe { *value.cast::<i32>().as_ptr() },
        ArgTy::Count(n) => n as i32,
    };
    std::process::exit(code);
}
