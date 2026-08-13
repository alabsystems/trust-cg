// VERBATIM transcription of trust-ir `Ty::bit_width` / `Ty::bit_width_with`'s
// closure-bearing arms (crates/trust-ir/src/ty.rs:153-196), over a FAITHFUL minimal
// `Ty` that preserves the load-bearing shape: a recursive `Vector(Box<Ty>, u32)`
// whose width is `elem.bit_width_with(pb).and_then(|bits| bits.checked_mul(*lanes))`
// — the closure captures `lanes` and is consumed by `Option::and_then` (RUNG 9).
#![crate_type = "lib"]

pub enum Ty {
    Bool,
    U8, U16, U32, U64, U128,
    F32, F64,
    Ptr,
    FatPtr,
    Vector(Box<Ty>, u32),
    Unit,
}

impl Ty {
    // VERBATIM bit_width (the target-independent arms + the Vector closure arm).
    pub fn bit_width(&self) -> Option<u32> {
        match self {
            Ty::Bool => Some(1),
            Ty::U8 => Some(8),
            Ty::U16 => Some(16),
            Ty::U32 => Some(32),
            Ty::U64 => Some(64),
            Ty::U128 => Some(128),
            Ty::F32 => Some(32),
            Ty::F64 => Some(64),
            Ty::Vector(elem, lanes) => elem.bit_width().and_then(|bits| bits.checked_mul(*lanes)),
            Ty::Ptr | Ty::FatPtr => None,
            _ => None,
        }
    }

    // VERBATIM bit_width_with (the pointer-resolving arms + the recursive Vector
    // closure arm capturing `lanes`).
    pub fn bit_width_with(&self, pointer_bits: u32) -> Option<u32> {
        match self {
            Ty::Ptr => Some(pointer_bits),
            Ty::FatPtr => pointer_bits.checked_mul(2),
            Ty::Vector(elem, lanes) => elem
                .bit_width_with(pointer_bits)
                .and_then(|bits| bits.checked_mul(*lanes)),
            _ => self.bit_width(),
        }
    }
}

// Root: a (*const Ty, u32) -> i64 driver, returning the bit_width_with as a signed
// sentinel (-1 for None) so the JIT call ABI is a single scalar.
#[no_mangle]
pub extern "C" fn bitwidth_root(t: *const Ty, pb: u32) -> i64 {
    let ty: &Ty = unsafe { &*t };
    match ty.bit_width_with(pb) {
        Some(w) => w as i64,
        None => -1,
    }
}
