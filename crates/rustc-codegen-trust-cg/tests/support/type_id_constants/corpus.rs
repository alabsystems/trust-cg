#![no_std]
use core::any::TypeId;

#[unsafe(no_mangle)]
#[inline(never)]
pub fn make_id(mode: u32) -> TypeId {
    match mode {
        0 => TypeId::of::<u8>(),
        1 => TypeId::of::<u64>(),
        2 => TypeId::of::<i64>(),
        3 => TypeId::of::<[u8; 3]>(),
        4 => TypeId::of::<()>(),
        5 => TypeId::of::<str>(),
        6 => TypeId::of::<&'static str>(),
        _ => TypeId::of::<Option<u64>>(),
    }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn same_id(a: TypeId, b: TypeId) -> bool {
    a == b
}
#[unsafe(no_mangle)]
pub extern "C" fn compare_ids(a: u32, b: u32) -> u64 {
    let a = make_id(a);
    let b = make_id(b);
    same_id(a, b) as u64
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn id_words(mode: u32, out: *mut u64) {
    let value = make_id(mode);
    unsafe {
        core::ptr::copy_nonoverlapping(
            (&value as *const TypeId).cast::<u8>(),
            out.cast::<u8>(),
            16,
        );
    }
}

#[unsafe(no_mangle)]
pub static U64_ID: TypeId = TypeId::of::<u64>();
#[unsafe(no_mangle)]
pub static VALUE: u64 = 0x9876543210123456;
#[repr(C)]
pub struct Mixed {
    id: TypeId,
    pointer: &'static u64,
}
#[unsafe(no_mangle)]
pub static MIXED: Mixed = Mixed {
    id: TypeId::of::<str>(),
    pointer: &VALUE,
};
const PROMOTED: &Mixed = &Mixed {
    id: TypeId::of::<u8>(),
    pointer: &VALUE,
};
#[unsafe(no_mangle)]
pub extern "C" fn static_check(mode: u32) -> u64 {
    match mode {
        0 => same_id(U64_ID, make_id(1)) as u64,
        1 => same_id(MIXED.id, make_id(5)) as u64,
        2 => same_id(PROMOTED.id, make_id(0)) as u64,
        3 => *MIXED.pointer,
        4 => *PROMOTED.pointer,
        5 => core::ptr::eq(MIXED.pointer, &VALUE) as u64,
        6 => core::ptr::eq(PROMOTED.pointer, &VALUE) as u64,
        _ => same_id(MIXED.id, PROMOTED.id) as u64,
    }
}

#[unsafe(no_mangle)]
pub static PROMOTED_REF: &Mixed = PROMOTED;

#[unsafe(no_mangle)]
pub extern "C" fn low_word() -> *const () {
    const { unsafe { core::mem::transmute::<TypeId, [*const (); 2]>(TypeId::of::<u64>())[0] } }
}
#[unsafe(no_mangle)]
pub extern "C" fn high_word() -> *const () {
    const { unsafe { core::mem::transmute::<TypeId, [*const (); 2]>(TypeId::of::<u64>())[1] } }
}
