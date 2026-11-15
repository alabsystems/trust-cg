// CALLER: exits 42 only when BOTH lanes arrive intact — the payload lane
// (`Some(20)`) and the tag lane (`None`, which must not be read as `Some`).
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
extern crate regclassbarg;
fn main() {
    std::process::exit(regclassbarg::take(Some(20)) + regclassbarg::take(None));
}
