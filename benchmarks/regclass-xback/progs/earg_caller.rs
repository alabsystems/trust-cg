// CALLER: exits 42 only when both the payload lane and the tag lane survive.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
extern crate regclassearg;
fn main() {
    std::process::exit(regclassearg::take(Some(20)) + regclassearg::take(None));
}
