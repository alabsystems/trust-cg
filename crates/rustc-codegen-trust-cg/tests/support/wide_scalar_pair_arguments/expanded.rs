#![no_std]
#[unsafe(no_mangle)]
pub fn option128_prefix_0(value: Option<u128>, suffix: u64) -> u128 {
    value.unwrap_or(0x96eec3e112347650aa665588f00dcafeu128) ^ ((suffix as u128).rotate_left(79))
}
unsafe extern "Rust" {
    fn llvm_option128_prefix_0(value: Option<u128>, suffix: u64) -> u128;
}
#[unsafe(no_mangle)]
pub fn option128_outgoing_0(bits: u128, some: bool, suffix: u64) -> u128 {
    unsafe { llvm_option128_prefix_0(if some { Some(bits) } else { None }, suffix) }
}
#[unsafe(no_mangle)]
pub fn option128_prefix_1(p0: u64, value: Option<u128>, suffix: u64) -> u128 {
    value.unwrap_or(0x96eec3e112347650aa665588f00dcafeu128)
        ^ ((p0 as u128).rotate_left(17))
        ^ ((suffix as u128).rotate_left(79))
}
unsafe extern "Rust" {
    fn llvm_option128_prefix_1(p0: u64, value: Option<u128>, suffix: u64) -> u128;
}
#[unsafe(no_mangle)]
pub fn option128_outgoing_1(p0: u64, bits: u128, some: bool, suffix: u64) -> u128 {
    unsafe { llvm_option128_prefix_1(p0, if some { Some(bits) } else { None }, suffix) }
}
#[unsafe(no_mangle)]
pub fn option128_prefix_2(p0: u64, p1: u64, value: Option<u128>, suffix: u64) -> u128 {
    value.unwrap_or(0x96eec3e112347650aa665588f00dcafeu128)
        ^ ((p0 as u128).rotate_left(17))
        ^ ((p1 as u128).rotate_left(30))
        ^ ((suffix as u128).rotate_left(79))
}
unsafe extern "Rust" {
    fn llvm_option128_prefix_2(p0: u64, p1: u64, value: Option<u128>, suffix: u64) -> u128;
}
#[unsafe(no_mangle)]
pub fn option128_outgoing_2(p0: u64, p1: u64, bits: u128, some: bool, suffix: u64) -> u128 {
    unsafe { llvm_option128_prefix_2(p0, p1, if some { Some(bits) } else { None }, suffix) }
}
#[unsafe(no_mangle)]
pub fn option128_prefix_3(p0: u64, p1: u64, p2: u64, value: Option<u128>, suffix: u64) -> u128 {
    value.unwrap_or(0x96eec3e112347650aa665588f00dcafeu128)
        ^ ((p0 as u128).rotate_left(17))
        ^ ((p1 as u128).rotate_left(30))
        ^ ((p2 as u128).rotate_left(43))
        ^ ((suffix as u128).rotate_left(79))
}
unsafe extern "Rust" {
    fn llvm_option128_prefix_3(p0: u64, p1: u64, p2: u64, value: Option<u128>, suffix: u64)
    -> u128;
}
#[unsafe(no_mangle)]
pub fn option128_outgoing_3(
    p0: u64,
    p1: u64,
    p2: u64,
    bits: u128,
    some: bool,
    suffix: u64,
) -> u128 {
    unsafe { llvm_option128_prefix_3(p0, p1, p2, if some { Some(bits) } else { None }, suffix) }
}
#[unsafe(no_mangle)]
pub fn option128_prefix_4(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    value: Option<u128>,
    suffix: u64,
) -> u128 {
    value.unwrap_or(0x96eec3e112347650aa665588f00dcafeu128)
        ^ ((p0 as u128).rotate_left(17))
        ^ ((p1 as u128).rotate_left(30))
        ^ ((p2 as u128).rotate_left(43))
        ^ ((p3 as u128).rotate_left(56))
        ^ ((suffix as u128).rotate_left(79))
}
unsafe extern "Rust" {
    fn llvm_option128_prefix_4(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        value: Option<u128>,
        suffix: u64,
    ) -> u128;
}
#[unsafe(no_mangle)]
pub fn option128_outgoing_4(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    bits: u128,
    some: bool,
    suffix: u64,
) -> u128 {
    unsafe { llvm_option128_prefix_4(p0, p1, p2, p3, if some { Some(bits) } else { None }, suffix) }
}
#[unsafe(no_mangle)]
pub fn option128_prefix_5(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    value: Option<u128>,
    suffix: u64,
) -> u128 {
    value.unwrap_or(0x96eec3e112347650aa665588f00dcafeu128)
        ^ ((p0 as u128).rotate_left(17))
        ^ ((p1 as u128).rotate_left(30))
        ^ ((p2 as u128).rotate_left(43))
        ^ ((p3 as u128).rotate_left(56))
        ^ ((p4 as u128).rotate_left(69))
        ^ ((suffix as u128).rotate_left(79))
}
unsafe extern "Rust" {
    fn llvm_option128_prefix_5(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        value: Option<u128>,
        suffix: u64,
    ) -> u128;
}
#[unsafe(no_mangle)]
pub fn option128_outgoing_5(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    bits: u128,
    some: bool,
    suffix: u64,
) -> u128 {
    unsafe {
        llvm_option128_prefix_5(
            p0,
            p1,
            p2,
            p3,
            p4,
            if some { Some(bits) } else { None },
            suffix,
        )
    }
}
#[unsafe(no_mangle)]
pub fn option128_prefix_6(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    value: Option<u128>,
    suffix: u64,
) -> u128 {
    value.unwrap_or(0x96eec3e112347650aa665588f00dcafeu128)
        ^ ((p0 as u128).rotate_left(17))
        ^ ((p1 as u128).rotate_left(30))
        ^ ((p2 as u128).rotate_left(43))
        ^ ((p3 as u128).rotate_left(56))
        ^ ((p4 as u128).rotate_left(69))
        ^ ((p5 as u128).rotate_left(82))
        ^ ((suffix as u128).rotate_left(79))
}
unsafe extern "Rust" {
    fn llvm_option128_prefix_6(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        p5: u64,
        value: Option<u128>,
        suffix: u64,
    ) -> u128;
}
#[unsafe(no_mangle)]
pub fn option128_outgoing_6(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    bits: u128,
    some: bool,
    suffix: u64,
) -> u128 {
    unsafe {
        llvm_option128_prefix_6(
            p0,
            p1,
            p2,
            p3,
            p4,
            p5,
            if some { Some(bits) } else { None },
            suffix,
        )
    }
}
#[unsafe(no_mangle)]
pub fn option128_prefix_7(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    value: Option<u128>,
    suffix: u64,
) -> u128 {
    value.unwrap_or(0x96eec3e112347650aa665588f00dcafeu128)
        ^ ((p0 as u128).rotate_left(17))
        ^ ((p1 as u128).rotate_left(30))
        ^ ((p2 as u128).rotate_left(43))
        ^ ((p3 as u128).rotate_left(56))
        ^ ((p4 as u128).rotate_left(69))
        ^ ((p5 as u128).rotate_left(82))
        ^ ((p6 as u128).rotate_left(95))
        ^ ((suffix as u128).rotate_left(79))
}
unsafe extern "Rust" {
    fn llvm_option128_prefix_7(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        p5: u64,
        p6: u64,
        value: Option<u128>,
        suffix: u64,
    ) -> u128;
}
#[unsafe(no_mangle)]
pub fn option128_outgoing_7(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    bits: u128,
    some: bool,
    suffix: u64,
) -> u128 {
    unsafe {
        llvm_option128_prefix_7(
            p0,
            p1,
            p2,
            p3,
            p4,
            p5,
            p6,
            if some { Some(bits) } else { None },
            suffix,
        )
    }
}
#[unsafe(no_mangle)]
pub fn option128_prefix_8(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    p7: u64,
    value: Option<u128>,
    suffix: u64,
) -> u128 {
    value.unwrap_or(0x96eec3e112347650aa665588f00dcafeu128)
        ^ ((p0 as u128).rotate_left(17))
        ^ ((p1 as u128).rotate_left(30))
        ^ ((p2 as u128).rotate_left(43))
        ^ ((p3 as u128).rotate_left(56))
        ^ ((p4 as u128).rotate_left(69))
        ^ ((p5 as u128).rotate_left(82))
        ^ ((p6 as u128).rotate_left(95))
        ^ ((p7 as u128).rotate_left(108))
        ^ ((suffix as u128).rotate_left(79))
}
unsafe extern "Rust" {
    fn llvm_option128_prefix_8(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        p5: u64,
        p6: u64,
        p7: u64,
        value: Option<u128>,
        suffix: u64,
    ) -> u128;
}
#[unsafe(no_mangle)]
pub fn option128_outgoing_8(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    p7: u64,
    bits: u128,
    some: bool,
    suffix: u64,
) -> u128 {
    unsafe {
        llvm_option128_prefix_8(
            p0,
            p1,
            p2,
            p3,
            p4,
            p5,
            p6,
            p7,
            if some { Some(bits) } else { None },
            suffix,
        )
    }
}
#[unsafe(no_mangle)]
pub fn option128_prefix_9(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    p7: u64,
    p8: u64,
    value: Option<u128>,
    suffix: u64,
) -> u128 {
    value.unwrap_or(0x96eec3e112347650aa665588f00dcafeu128)
        ^ ((p0 as u128).rotate_left(17))
        ^ ((p1 as u128).rotate_left(30))
        ^ ((p2 as u128).rotate_left(43))
        ^ ((p3 as u128).rotate_left(56))
        ^ ((p4 as u128).rotate_left(69))
        ^ ((p5 as u128).rotate_left(82))
        ^ ((p6 as u128).rotate_left(95))
        ^ ((p7 as u128).rotate_left(108))
        ^ ((p8 as u128).rotate_left(121))
        ^ ((suffix as u128).rotate_left(79))
}
unsafe extern "Rust" {
    fn llvm_option128_prefix_9(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        p5: u64,
        p6: u64,
        p7: u64,
        p8: u64,
        value: Option<u128>,
        suffix: u64,
    ) -> u128;
}
#[unsafe(no_mangle)]
pub fn option128_outgoing_9(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    p7: u64,
    p8: u64,
    bits: u128,
    some: bool,
    suffix: u64,
) -> u128 {
    unsafe {
        llvm_option128_prefix_9(
            p0,
            p1,
            p2,
            p3,
            p4,
            p5,
            p6,
            p7,
            p8,
            if some { Some(bits) } else { None },
            suffix,
        )
    }
}
#[unsafe(no_mangle)]
pub fn signed_prefix_1(p0: u64, value: Option<i128>, suffix: u64) -> u128 {
    (value.unwrap_or(-0x7234123498765555111133336666888i128) as u128)
        ^ ((p0 as u128).rotate_left(3))
        ^ ((suffix as u128).rotate_left(97))
}
unsafe extern "Rust" {
    fn llvm_signed_prefix_1(p0: u64, value: Option<i128>, suffix: u64) -> u128;
}
#[unsafe(no_mangle)]
pub fn outgoing_signed_prefix_1(p0: u64, value: Option<i128>, suffix: u64) -> u128 {
    unsafe { llvm_signed_prefix_1(p0, value, suffix) }
}
#[unsafe(no_mangle)]
pub fn signed_prefix_5(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    value: Option<i128>,
    suffix: u64,
) -> u128 {
    (value.unwrap_or(-0x7234123498765555111133336666888i128) as u128)
        ^ ((p0 as u128).rotate_left(3))
        ^ ((p1 as u128).rotate_left(14))
        ^ ((p2 as u128).rotate_left(25))
        ^ ((p3 as u128).rotate_left(36))
        ^ ((p4 as u128).rotate_left(47))
        ^ ((suffix as u128).rotate_left(97))
}
unsafe extern "Rust" {
    fn llvm_signed_prefix_5(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        value: Option<i128>,
        suffix: u64,
    ) -> u128;
}
#[unsafe(no_mangle)]
pub fn outgoing_signed_prefix_5(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    value: Option<i128>,
    suffix: u64,
) -> u128 {
    unsafe { llvm_signed_prefix_5(p0, p1, p2, p3, p4, value, suffix) }
}
#[unsafe(no_mangle)]
pub fn signed_prefix_7(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    value: Option<i128>,
    suffix: u64,
) -> u128 {
    (value.unwrap_or(-0x7234123498765555111133336666888i128) as u128)
        ^ ((p0 as u128).rotate_left(3))
        ^ ((p1 as u128).rotate_left(14))
        ^ ((p2 as u128).rotate_left(25))
        ^ ((p3 as u128).rotate_left(36))
        ^ ((p4 as u128).rotate_left(47))
        ^ ((p5 as u128).rotate_left(58))
        ^ ((p6 as u128).rotate_left(69))
        ^ ((suffix as u128).rotate_left(97))
}
unsafe extern "Rust" {
    fn llvm_signed_prefix_7(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        p5: u64,
        p6: u64,
        value: Option<i128>,
        suffix: u64,
    ) -> u128;
}
#[unsafe(no_mangle)]
pub fn outgoing_signed_prefix_7(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    value: Option<i128>,
    suffix: u64,
) -> u128 {
    unsafe { llvm_signed_prefix_7(p0, p1, p2, p3, p4, p5, p6, value, suffix) }
}
#[unsafe(no_mangle)]
pub fn signed_prefix_9(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    p7: u64,
    p8: u64,
    value: Option<i128>,
    suffix: u64,
) -> u128 {
    (value.unwrap_or(-0x7234123498765555111133336666888i128) as u128)
        ^ ((p0 as u128).rotate_left(3))
        ^ ((p1 as u128).rotate_left(14))
        ^ ((p2 as u128).rotate_left(25))
        ^ ((p3 as u128).rotate_left(36))
        ^ ((p4 as u128).rotate_left(47))
        ^ ((p5 as u128).rotate_left(58))
        ^ ((p6 as u128).rotate_left(69))
        ^ ((p7 as u128).rotate_left(80))
        ^ ((p8 as u128).rotate_left(91))
        ^ ((suffix as u128).rotate_left(97))
}
unsafe extern "Rust" {
    fn llvm_signed_prefix_9(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        p5: u64,
        p6: u64,
        p7: u64,
        p8: u64,
        value: Option<i128>,
        suffix: u64,
    ) -> u128;
}
#[unsafe(no_mangle)]
pub fn outgoing_signed_prefix_9(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    p7: u64,
    p8: u64,
    value: Option<i128>,
    suffix: u64,
) -> u128 {
    unsafe { llvm_signed_prefix_9(p0, p1, p2, p3, p4, p5, p6, p7, p8, value, suffix) }
}
#[unsafe(no_mangle)]
pub fn pair_wide_prefix_1(p0: u64, value: (u128, u128), suffix: u64) -> u128 {
    (value.0.rotate_left(13) ^ value.1)
        ^ ((p0 as u128).rotate_left(3))
        ^ ((suffix as u128).rotate_left(97))
}
unsafe extern "Rust" {
    fn llvm_pair_wide_prefix_1(p0: u64, value: (u128, u128), suffix: u64) -> u128;
}
#[unsafe(no_mangle)]
pub fn outgoing_pair_wide_prefix_1(p0: u64, value: (u128, u128), suffix: u64) -> u128 {
    unsafe { llvm_pair_wide_prefix_1(p0, value, suffix) }
}
#[unsafe(no_mangle)]
pub fn pair_wide_prefix_5(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    value: (u128, u128),
    suffix: u64,
) -> u128 {
    (value.0.rotate_left(13) ^ value.1)
        ^ ((p0 as u128).rotate_left(3))
        ^ ((p1 as u128).rotate_left(14))
        ^ ((p2 as u128).rotate_left(25))
        ^ ((p3 as u128).rotate_left(36))
        ^ ((p4 as u128).rotate_left(47))
        ^ ((suffix as u128).rotate_left(97))
}
unsafe extern "Rust" {
    fn llvm_pair_wide_prefix_5(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        value: (u128, u128),
        suffix: u64,
    ) -> u128;
}
#[unsafe(no_mangle)]
pub fn outgoing_pair_wide_prefix_5(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    value: (u128, u128),
    suffix: u64,
) -> u128 {
    unsafe { llvm_pair_wide_prefix_5(p0, p1, p2, p3, p4, value, suffix) }
}
#[unsafe(no_mangle)]
pub fn pair_wide_prefix_7(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    value: (u128, u128),
    suffix: u64,
) -> u128 {
    (value.0.rotate_left(13) ^ value.1)
        ^ ((p0 as u128).rotate_left(3))
        ^ ((p1 as u128).rotate_left(14))
        ^ ((p2 as u128).rotate_left(25))
        ^ ((p3 as u128).rotate_left(36))
        ^ ((p4 as u128).rotate_left(47))
        ^ ((p5 as u128).rotate_left(58))
        ^ ((p6 as u128).rotate_left(69))
        ^ ((suffix as u128).rotate_left(97))
}
unsafe extern "Rust" {
    fn llvm_pair_wide_prefix_7(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        p5: u64,
        p6: u64,
        value: (u128, u128),
        suffix: u64,
    ) -> u128;
}
#[unsafe(no_mangle)]
pub fn outgoing_pair_wide_prefix_7(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    value: (u128, u128),
    suffix: u64,
) -> u128 {
    unsafe { llvm_pair_wide_prefix_7(p0, p1, p2, p3, p4, p5, p6, value, suffix) }
}
#[unsafe(no_mangle)]
pub fn pair_wide_prefix_9(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    p7: u64,
    p8: u64,
    value: (u128, u128),
    suffix: u64,
) -> u128 {
    (value.0.rotate_left(13) ^ value.1)
        ^ ((p0 as u128).rotate_left(3))
        ^ ((p1 as u128).rotate_left(14))
        ^ ((p2 as u128).rotate_left(25))
        ^ ((p3 as u128).rotate_left(36))
        ^ ((p4 as u128).rotate_left(47))
        ^ ((p5 as u128).rotate_left(58))
        ^ ((p6 as u128).rotate_left(69))
        ^ ((p7 as u128).rotate_left(80))
        ^ ((p8 as u128).rotate_left(91))
        ^ ((suffix as u128).rotate_left(97))
}
unsafe extern "Rust" {
    fn llvm_pair_wide_prefix_9(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        p5: u64,
        p6: u64,
        p7: u64,
        p8: u64,
        value: (u128, u128),
        suffix: u64,
    ) -> u128;
}
#[unsafe(no_mangle)]
pub fn outgoing_pair_wide_prefix_9(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    p7: u64,
    p8: u64,
    value: (u128, u128),
    suffix: u64,
) -> u128 {
    unsafe { llvm_pair_wide_prefix_9(p0, p1, p2, p3, p4, p5, p6, p7, p8, value, suffix) }
}
#[unsafe(no_mangle)]
pub fn pair_narrow_wide_prefix_1(p0: u64, value: (u64, u128), suffix: u64) -> u128 {
    ((value.0 as u128).rotate_left(17) ^ value.1)
        ^ ((p0 as u128).rotate_left(3))
        ^ ((suffix as u128).rotate_left(97))
}
unsafe extern "Rust" {
    fn llvm_pair_narrow_wide_prefix_1(p0: u64, value: (u64, u128), suffix: u64) -> u128;
}
#[unsafe(no_mangle)]
pub fn outgoing_pair_narrow_wide_prefix_1(p0: u64, value: (u64, u128), suffix: u64) -> u128 {
    unsafe { llvm_pair_narrow_wide_prefix_1(p0, value, suffix) }
}
#[unsafe(no_mangle)]
pub fn pair_narrow_wide_prefix_5(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    value: (u64, u128),
    suffix: u64,
) -> u128 {
    ((value.0 as u128).rotate_left(17) ^ value.1)
        ^ ((p0 as u128).rotate_left(3))
        ^ ((p1 as u128).rotate_left(14))
        ^ ((p2 as u128).rotate_left(25))
        ^ ((p3 as u128).rotate_left(36))
        ^ ((p4 as u128).rotate_left(47))
        ^ ((suffix as u128).rotate_left(97))
}
unsafe extern "Rust" {
    fn llvm_pair_narrow_wide_prefix_5(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        value: (u64, u128),
        suffix: u64,
    ) -> u128;
}
#[unsafe(no_mangle)]
pub fn outgoing_pair_narrow_wide_prefix_5(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    value: (u64, u128),
    suffix: u64,
) -> u128 {
    unsafe { llvm_pair_narrow_wide_prefix_5(p0, p1, p2, p3, p4, value, suffix) }
}
#[unsafe(no_mangle)]
pub fn pair_narrow_wide_prefix_7(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    value: (u64, u128),
    suffix: u64,
) -> u128 {
    ((value.0 as u128).rotate_left(17) ^ value.1)
        ^ ((p0 as u128).rotate_left(3))
        ^ ((p1 as u128).rotate_left(14))
        ^ ((p2 as u128).rotate_left(25))
        ^ ((p3 as u128).rotate_left(36))
        ^ ((p4 as u128).rotate_left(47))
        ^ ((p5 as u128).rotate_left(58))
        ^ ((p6 as u128).rotate_left(69))
        ^ ((suffix as u128).rotate_left(97))
}
unsafe extern "Rust" {
    fn llvm_pair_narrow_wide_prefix_7(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        p5: u64,
        p6: u64,
        value: (u64, u128),
        suffix: u64,
    ) -> u128;
}
#[unsafe(no_mangle)]
pub fn outgoing_pair_narrow_wide_prefix_7(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    value: (u64, u128),
    suffix: u64,
) -> u128 {
    unsafe { llvm_pair_narrow_wide_prefix_7(p0, p1, p2, p3, p4, p5, p6, value, suffix) }
}
#[unsafe(no_mangle)]
pub fn pair_narrow_wide_prefix_9(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    p7: u64,
    p8: u64,
    value: (u64, u128),
    suffix: u64,
) -> u128 {
    ((value.0 as u128).rotate_left(17) ^ value.1)
        ^ ((p0 as u128).rotate_left(3))
        ^ ((p1 as u128).rotate_left(14))
        ^ ((p2 as u128).rotate_left(25))
        ^ ((p3 as u128).rotate_left(36))
        ^ ((p4 as u128).rotate_left(47))
        ^ ((p5 as u128).rotate_left(58))
        ^ ((p6 as u128).rotate_left(69))
        ^ ((p7 as u128).rotate_left(80))
        ^ ((p8 as u128).rotate_left(91))
        ^ ((suffix as u128).rotate_left(97))
}
unsafe extern "Rust" {
    fn llvm_pair_narrow_wide_prefix_9(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        p5: u64,
        p6: u64,
        p7: u64,
        p8: u64,
        value: (u64, u128),
        suffix: u64,
    ) -> u128;
}
#[unsafe(no_mangle)]
pub fn outgoing_pair_narrow_wide_prefix_9(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    p7: u64,
    p8: u64,
    value: (u64, u128),
    suffix: u64,
) -> u128 {
    unsafe { llvm_pair_narrow_wide_prefix_9(p0, p1, p2, p3, p4, p5, p6, p7, p8, value, suffix) }
}
#[unsafe(no_mangle)]
pub fn pair_wide_narrow_prefix_1(p0: u64, value: (u128, u64), suffix: u64) -> u128 {
    (value.0.rotate_left(23) ^ (value.1 as u128))
        ^ ((p0 as u128).rotate_left(3))
        ^ ((suffix as u128).rotate_left(97))
}
unsafe extern "Rust" {
    fn llvm_pair_wide_narrow_prefix_1(p0: u64, value: (u128, u64), suffix: u64) -> u128;
}
#[unsafe(no_mangle)]
pub fn outgoing_pair_wide_narrow_prefix_1(p0: u64, value: (u128, u64), suffix: u64) -> u128 {
    unsafe { llvm_pair_wide_narrow_prefix_1(p0, value, suffix) }
}
#[unsafe(no_mangle)]
pub fn pair_wide_narrow_prefix_5(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    value: (u128, u64),
    suffix: u64,
) -> u128 {
    (value.0.rotate_left(23) ^ (value.1 as u128))
        ^ ((p0 as u128).rotate_left(3))
        ^ ((p1 as u128).rotate_left(14))
        ^ ((p2 as u128).rotate_left(25))
        ^ ((p3 as u128).rotate_left(36))
        ^ ((p4 as u128).rotate_left(47))
        ^ ((suffix as u128).rotate_left(97))
}
unsafe extern "Rust" {
    fn llvm_pair_wide_narrow_prefix_5(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        value: (u128, u64),
        suffix: u64,
    ) -> u128;
}
#[unsafe(no_mangle)]
pub fn outgoing_pair_wide_narrow_prefix_5(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    value: (u128, u64),
    suffix: u64,
) -> u128 {
    unsafe { llvm_pair_wide_narrow_prefix_5(p0, p1, p2, p3, p4, value, suffix) }
}
#[unsafe(no_mangle)]
pub fn pair_wide_narrow_prefix_7(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    value: (u128, u64),
    suffix: u64,
) -> u128 {
    (value.0.rotate_left(23) ^ (value.1 as u128))
        ^ ((p0 as u128).rotate_left(3))
        ^ ((p1 as u128).rotate_left(14))
        ^ ((p2 as u128).rotate_left(25))
        ^ ((p3 as u128).rotate_left(36))
        ^ ((p4 as u128).rotate_left(47))
        ^ ((p5 as u128).rotate_left(58))
        ^ ((p6 as u128).rotate_left(69))
        ^ ((suffix as u128).rotate_left(97))
}
unsafe extern "Rust" {
    fn llvm_pair_wide_narrow_prefix_7(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        p5: u64,
        p6: u64,
        value: (u128, u64),
        suffix: u64,
    ) -> u128;
}
#[unsafe(no_mangle)]
pub fn outgoing_pair_wide_narrow_prefix_7(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    value: (u128, u64),
    suffix: u64,
) -> u128 {
    unsafe { llvm_pair_wide_narrow_prefix_7(p0, p1, p2, p3, p4, p5, p6, value, suffix) }
}
#[unsafe(no_mangle)]
pub fn pair_wide_narrow_prefix_9(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    p7: u64,
    p8: u64,
    value: (u128, u64),
    suffix: u64,
) -> u128 {
    (value.0.rotate_left(23) ^ (value.1 as u128))
        ^ ((p0 as u128).rotate_left(3))
        ^ ((p1 as u128).rotate_left(14))
        ^ ((p2 as u128).rotate_left(25))
        ^ ((p3 as u128).rotate_left(36))
        ^ ((p4 as u128).rotate_left(47))
        ^ ((p5 as u128).rotate_left(58))
        ^ ((p6 as u128).rotate_left(69))
        ^ ((p7 as u128).rotate_left(80))
        ^ ((p8 as u128).rotate_left(91))
        ^ ((suffix as u128).rotate_left(97))
}
unsafe extern "Rust" {
    fn llvm_pair_wide_narrow_prefix_9(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        p5: u64,
        p6: u64,
        p7: u64,
        p8: u64,
        value: (u128, u64),
        suffix: u64,
    ) -> u128;
}
#[unsafe(no_mangle)]
pub fn outgoing_pair_wide_narrow_prefix_9(
    p0: u64,
    p1: u64,
    p2: u64,
    p3: u64,
    p4: u64,
    p5: u64,
    p6: u64,
    p7: u64,
    p8: u64,
    value: (u128, u64),
    suffix: u64,
) -> u128 {
    unsafe { llvm_pair_wide_narrow_prefix_9(p0, p1, p2, p3, p4, p5, p6, p7, p8, value, suffix) }
}
#[unsafe(no_mangle)]
pub fn option128_indirect(
    f: fn(u64, Option<u128>, u64) -> u128,
    p: u64,
    bits: u128,
    some: bool,
    s: u64,
) -> u128 {
    f(p, if some { Some(bits) } else { None }, s)
}
