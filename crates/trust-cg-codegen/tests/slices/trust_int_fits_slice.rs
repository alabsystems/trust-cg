// VERBATIM transcription of trust-ir `int_value_fits_ty` (crates/trust-ir/src/shape.rs
// :1005) — a NON-closure `match` over a minimal faithful `Ty` (the int arms). This is
// a drift sentinel for the task's named `int_value_fits_ty` additive gate.
#![crate_type = "lib"]

pub enum Ty {
    Bool, I8, I16, I32, I64, I128, U8, U16, U32, U64, U128,
    F32, F64, Ptr, Unit,
}

fn int_value_fits_ty(value: i128, ty: &Ty) -> bool {
    match ty {
        Ty::I8 => value >= i8::MIN as i128 && value <= i8::MAX as i128,
        Ty::I16 => value >= i16::MIN as i128 && value <= i16::MAX as i128,
        Ty::I32 => value >= i32::MIN as i128 && value <= i32::MAX as i128,
        Ty::I64 => value >= i64::MIN as i128 && value <= i64::MAX as i128,
        Ty::I128 => true,
        Ty::U8 => value >= 0 && value <= u8::MAX as i128,
        Ty::U16 => value >= 0 && value <= u16::MAX as i128,
        Ty::U32 => value >= 0 && value <= u32::MAX as i128,
        Ty::U64 => value >= 0 && value <= u64::MAX as i128,
        Ty::U128 => value >= 0,
        _ => false,
    }
}

#[no_mangle]
pub extern "C" fn int_fits_root(value: i128, t: *const Ty) -> bool {
    int_value_fits_ty(value, unsafe { &*t })
}
