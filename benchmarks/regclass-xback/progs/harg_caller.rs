// CALLER: exits 42 when the by-value 16-bit pair arrives in the right order.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
extern crate regclassharg;
fn main() {
    std::process::exit(regclassharg::take((10, 22)));
}
