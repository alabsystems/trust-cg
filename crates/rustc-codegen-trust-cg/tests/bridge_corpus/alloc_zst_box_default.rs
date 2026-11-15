// CORPUS FIXTURE — a `Box` of a zero-sized type with the DEFAULT allocator:
// `Box::new(())`, `Box::new([0u64; 0])` and `Box::<()>::new_uninit()` take
// `layout.dangling()` (the alignment as a pointer) and std's `Box` drop
// deallocates only `if layout.size() != 0`, so nothing is allocated or freed
// and each row prints the dangling address. Before the fix the bridge's drop
// called `__rust_dealloc(align, 0, align)`, which is `free(0x1)` / `free(0x8)`
// and aborts (SIGABRT), and `box_new_uninit` of a zero-size layout was refused
// at -O2/-O3.
//
// `ALLOC_SHAPE` (first byte) selects the row; `z` runs none.
#[inline(never)]
fn box_unit() -> u64 {
    let b = Box::new(());
    let p = &*b as *const () as usize as u64;
    p
}
#[inline(never)]
fn box_empty_array() -> u64 {
    let b = Box::new([0u64; 0]);
    let p = b.as_ptr() as usize as u64;
    p
}
#[inline(never)]
fn box_uninit_zst() -> u64 {
    let b = Box::<()>::new_uninit();
    let p = b.as_ptr() as usize as u64;
    p
}
unsafe extern "C" {
    fn getenv(name: *const u8) -> *const u8;
}
fn shape() -> u8 {
    unsafe {
        let p = getenv(b"ALLOC_SHAPE\0".as_ptr());
        if p.is_null() { 0 } else { *p }
    }
}
fn main() {
    let which = shape();
    let r = match which {
        b'a' => box_unit(),
        b'b' => box_empty_array(),
        b'c' => box_uninit_zst(),
        _ => 0,
    };
    println!("r = {r}");
}
