// Guest of `mir_families_aarch64` (ledger L06-P8): `#[link_section]` statics
// in Mach-O `segment,section` form, compiled by the bridge and by LLVM. A
// mutable static in its own `__DATA` section, an immutable table in `__TEXT`,
// an immutable value in `__DATA_CONST`, and a constructor table in
// `__DATA,__mod_init_func` that dyld runs before `main`.
use std::hint::black_box;

#[no_mangle]
#[link_section = "__DATA,__tcg_data"]
pub static mut TCG_COUNTER: u32 = 5;

#[no_mangle]
#[link_section = "__TEXT,__tcg_const"]
pub static TCG_TABLE: [u8; 4] = [1, 2, 3, 4];

#[no_mangle]
#[link_section = "__DATA_CONST,__tcg_ro"]
pub static TCG_RO: u64 = 77;

#[no_mangle]
pub static mut TCG_INIT_RAN: u32 = 0;

extern "C" fn tcg_init() {
    unsafe {
        TCG_INIT_RAN += 40;
    }
}

#[used]
#[link_section = "__DATA,__mod_init_func"]
static TCG_CTOR: extern "C" fn() = tcg_init;

#[inline(never)]
fn bump() -> u32 {
    unsafe {
        TCG_COUNTER += 1;
        TCG_COUNTER
    }
}

fn main() {
    let index = black_box(2usize);
    let table = TCG_TABLE[index] as u32;
    let ro = *black_box(&TCG_RO) as u32;
    let first = bump();
    let second = bump();
    println!("{first} {second} {table} {ro} {}", unsafe { TCG_INIT_RAN });
}
