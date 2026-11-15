//! A fat leaf inside a `repr(packed)` container: must refuse by name or match.
#[repr(C, packed)]
pub struct Pk { pub a: u8, pub inner: Box<[u8]> }
#[inline(never)]
pub fn set_packed(t: &mut Pk, b: Box<[u8]>) { t.inner = b; }
