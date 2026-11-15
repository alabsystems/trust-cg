#![no_std]
use core::mem::MaybeUninit;

macro_rules! store {
    ($case:literal, $name:ident, $ty:ty, $value:expr) => {
        #[unsafe(no_mangle)]
        pub extern "C" fn $name(dst: &mut MaybeUninit<$ty>) {
            *dst = MaybeUninit::new($value);
        }
    };
}
store!("integers", store_u8, u8, 0xb7);
store!("integers", store_u64, u64, 0xfedc_ba98_7654_3210);
store!(
    "integers",
    store_u128,
    u128,
    0xfedc_ba98_7654_3210_0123_4567_89ab_cdef
);
store!(
    "integers",
    store_i128,
    i128,
    -0x1234_5678_9abc_def0_1020_3040_5060_7080
);
store!(
    "floats",
    store_f32,
    f32,
    const { f32::from_bits(0x7f81_2345) }
);
store!(
    "floats",
    store_f64,
    f64,
    const { f64::from_bits(0x7ff0_1234_5678_9abc) }
);
store!("validity", store_bool, bool, true);
store!("validity", store_char, char, '\u{10abcd}');
#[unsafe(no_mangle)]
pub static TARGET: [u64; 4] = [11, 22, 33, 44];
store!("pointers", store_ptr, *const u64, &TARGET[2] as *const u64);
store!("pointers", store_null, *const u64, core::ptr::null());
#[unsafe(no_mangle)]
pub extern "C" fn return_word() -> MaybeUninit<u64> {
    MaybeUninit::new(0xfedc_ba98_7654_3210)
}
#[unsafe(no_mangle)]
pub extern "C" fn return_ptr() -> MaybeUninit<*const u64> {
    MaybeUninit::new(&TARGET[2] as *const u64)
}
#[repr(C)]
pub union Bits {
    pub wide: u64,
    pub narrow: u8,
}
#[unsafe(no_mangle)]
pub extern "C" fn store_partial(dst: &mut Bits) {
    *dst = Bits { narrow: 0xa5 };
}
#[unsafe(no_mangle)]
pub extern "C" fn store_const_ptr(dst: &mut MaybeUninit<*const u64>) {
    *dst = const { MaybeUninit::new(&TARGET[2] as *const u64) };
}
#[unsafe(no_mangle)]
pub extern "C" fn store_const_ref(dst: &mut MaybeUninit<&'static u64>) {
    *dst = const { MaybeUninit::new(&TARGET[1]) };
}
#[unsafe(no_mangle)]
pub extern "C" fn store_offset(dst: &mut MaybeUninit<u64>) {
    const PAIR: (&u64, MaybeUninit<u64>) = (&TARGET[1], MaybeUninit::new(0x9876_5432_10ab_cdef));
    *dst = PAIR.1;
}
#[unsafe(no_mangle)]
pub extern "C" fn return_const_ptr() -> MaybeUninit<*const u64> {
    const { MaybeUninit::new(&TARGET[3] as *const u64) }
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Image {
    pub pointer: *const u64,
    pub function: extern "C" fn(u64) -> u64,
    pub bits: u64,
}
#[repr(C)]
#[derive(Copy, Clone)]
pub struct Outer {
    pub head: u64,
    pub image: Image,
    pub tail: u64,
}
#[unsafe(no_mangle)]
pub extern "C" fn image_function(x: u64) -> u64 {
    x.rotate_left(17) ^ 0x9876_5432_10ab_cdef
}
const IMAGE: Image = Image {
    pointer: &TARGET[2],
    function: image_function,
    bits: 0xfedc_ba98_7654_3210,
};
const OUTER: Outer = Outer {
    head: 0x1234_5678_9abc_def0,
    image: IMAGE,
    tail: 0x0123_4567_89ab_cdef,
};
#[unsafe(no_mangle)]
pub extern "C" fn store_image(dst: &mut Image) {
    *dst = IMAGE;
}
#[unsafe(no_mangle)]
pub extern "C" fn store_image_offset(dst: &mut Image) {
    *dst = OUTER.image;
}
#[unsafe(no_mangle)]
pub extern "C" fn store_outer(dst: &mut Outer) {
    *dst = OUTER;
}

store!(
    "floats",
    store_f32_negative_nan,
    f32,
    const { f32::from_bits(0xff81_2345) }
);
store!(
    "floats",
    store_f32_min_nan,
    f32,
    const { f32::from_bits(0x7f80_0001) }
);
store!(
    "floats",
    store_f32_max_signaling_nan,
    f32,
    const { f32::from_bits(0x7fbf_ffff) }
);
store!(
    "floats",
    store_f32_quiet_nan,
    f32,
    const { f32::from_bits(0x7fc5_4321) }
);
store!(
    "floats",
    store_f32_negative_zero,
    f32,
    const { f32::from_bits(0x8000_0000) }
);
store!(
    "floats",
    store_f32_negative_infinity,
    f32,
    const { f32::from_bits(0xff80_0000) }
);
#[unsafe(no_mangle)]
pub extern "C" fn return_f32_nan() -> f32 {
    const { f32::from_bits(0xff81_2345) }
}
#[unsafe(no_mangle)]
pub extern "C" fn return_f64_nan() -> f64 {
    const { f64::from_bits(0xfff0_1234_5678_9abc) }
}
