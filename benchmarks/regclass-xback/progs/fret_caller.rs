// CALLER: exits 42 when the returned float pair arrives intact.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
extern crate regclassfret;
fn main() {
    let p = regclassfret::make(2.0);
    let mut code = 0i32;
    if p.a == 4.0 { code += 2; }
    if p.b == 40.0 { code += 40; }
    std::process::exit(code);
}
