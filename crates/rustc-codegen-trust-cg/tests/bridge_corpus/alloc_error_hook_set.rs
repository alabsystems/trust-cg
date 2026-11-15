// CORPUS FIXTURE (an rlib, always compiled by LLVM) — installs an
// allocation-error hook that PANICS, so `handle_alloc_error` unwinds instead of
// aborting. `alloc_error_hook_unwind.rs` links it: the bridge's allocation-
// failure call must then honor the source call's unwind edge exactly as LLVM's
// does (run the frame's Drops on a cleanup edge, abort at a terminate edge).
// The hook allocates only through the panic machinery (its message and
// payload), and the fixture's allocator fails a single size that machinery
// never requests.
#![feature(alloc_error_hook)]
#![crate_type = "rlib"]

fn hook(layout: std::alloc::Layout) {
    panic!("hooked {}", layout.size())
}

pub fn install() {
    std::alloc::set_alloc_error_hook(hook);
}
