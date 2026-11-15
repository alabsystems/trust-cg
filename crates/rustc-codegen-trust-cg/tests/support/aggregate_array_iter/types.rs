pub type Pair = (f64, f64);
pub type Mixed = (u8, f32, u64);
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Padded {
    pub first: u8,
    pub second: f64,
    pub third: u16,
}
