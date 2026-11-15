#![no_std]
#[no_mangle]
pub extern "C" fn immutable_local_constant_object() -> u64 {
    let table = core::hint::black_box([7_u64, 11_u64]);
    let index = 0_usize;
    table[index].wrapping_add(table[1])
}
