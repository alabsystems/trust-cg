// A field whose element needs drop (`Vec<String>`) is outside the admission
// (`collection_field_header_ty` requires a no-drop element). This two-field
// struct already compiled before it on its scalarized route (measured on the
// base tree); it must match LLVM or refuse by name.
use std::hint::black_box;
struct Names {
    k: u32,
    all: Vec<String>,
}
#[inline(never)]
fn mk(n: u32) -> Names {
    let mut v = Vec::new();
    for _ in 0..n {
        v.push(String::new());
    }
    Names { k: n, all: v }
}
fn main() {
    let x = mk(black_box(3));
    println!("{} {}", x.k, x.all.len());
}
