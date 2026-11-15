#![no_std]
#[repr(C)]
pub struct Words {
    pub a: u64,
    pub b: u64,
    pub c: u64,
    pub d: u64,
}
#[repr(C)]
pub struct Pair {
    pub a: u64,
    pub b: u64,
}
#[repr(C)]
pub struct Floats {
    pub a: f64,
    pub b: f64,
    pub c: f64,
}
unsafe extern "Rust" {
    fn aggregate_rust_pair(cell: &mut u64, v: u64) -> (u64, u64);
    fn aggregate_union(cell: &mut u64, v: u64) -> core::mem::MaybeUninit<u64>;
    fn aggregate_read_union(slot: &mut core::mem::MaybeUninit<u64>) -> u64;
}
unsafe extern "C-unwind" {
    fn aggregate_words(cell: &mut u64, v: u64) -> Words;
    fn aggregate_pair(cell: &mut u64, v: u64) -> Pair;
    fn aggregate_floats(cell: &mut u64, v: u64) -> Floats;
}
unsafe extern "C" {
    fn aggregate_event(kind: u64, value: u64);
}
struct Guard(*const u64);
impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe { aggregate_event(5, *self.0) }
    }
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_rust_pair(v: u64) -> u64 {
    let mut cell = v ^ 0x55;
    let _guard = Guard(&raw const cell);
    let pair = unsafe { aggregate_rust_pair(&mut cell, v) };
    unsafe { aggregate_event(2, cell) }
    pair.0 ^ pair.1 ^ cell
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_words(v: u64) -> u64 {
    let mut cell = v ^ 0x55;
    let _guard = Guard(&raw const cell);
    let words = unsafe { aggregate_words(&mut cell, v) };
    unsafe { aggregate_event(2, cell) }
    words.a ^ words.b ^ words.c ^ words.d ^ cell
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_pair(v: u64) -> u64 {
    let mut cell = v ^ 0x55;
    let _guard = Guard(&raw const cell);
    let pair = unsafe { aggregate_pair(&mut cell, v) };
    unsafe { aggregate_event(2, cell) }
    pair.a ^ pair.b ^ cell
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_floats(v: u64) -> u64 {
    let mut cell = v ^ 0x55;
    let _guard = Guard(&raw const cell);
    let floats = unsafe { aggregate_floats(&mut cell, v) };
    unsafe { aggregate_event(2, cell) }
    floats.a.to_bits() ^ floats.b.to_bits() ^ floats.c.to_bits() ^ cell
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn check_union(v: u64) -> u64 {
    let mut cell = v ^ 0x55;
    let _guard = Guard(&raw const cell);
    let mut storage = unsafe { aggregate_union(&mut cell, v) };
    unsafe { aggregate_event(2, cell) }
    unsafe { aggregate_read_union(&mut storage) ^ cell }
}
