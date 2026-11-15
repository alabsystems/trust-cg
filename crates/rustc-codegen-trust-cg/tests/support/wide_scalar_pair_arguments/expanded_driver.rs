unsafe extern "Rust" {
    fn option128_prefix_0(value: Option<u128>, suffix: u64) -> u128;
    fn option128_outgoing_0(bits: u128, some: bool, suffix: u64) -> u128;
    fn option128_prefix_1(p0: u64, value: Option<u128>, suffix: u64) -> u128;
    fn option128_outgoing_1(p0: u64, bits: u128, some: bool, suffix: u64) -> u128;
    fn option128_prefix_2(p0: u64, p1: u64, value: Option<u128>, suffix: u64) -> u128;
    fn option128_outgoing_2(p0: u64, p1: u64, bits: u128, some: bool, suffix: u64) -> u128;
    fn option128_prefix_3(p0: u64, p1: u64, p2: u64, value: Option<u128>, suffix: u64) -> u128;
    fn option128_outgoing_3(p0: u64, p1: u64, p2: u64, bits: u128, some: bool, suffix: u64)
    -> u128;
    fn option128_prefix_4(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        value: Option<u128>,
        suffix: u64,
    ) -> u128;
    fn option128_outgoing_4(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        bits: u128,
        some: bool,
        suffix: u64,
    ) -> u128;
    fn option128_prefix_5(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        value: Option<u128>,
        suffix: u64,
    ) -> u128;
    fn option128_outgoing_5(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        bits: u128,
        some: bool,
        suffix: u64,
    ) -> u128;
    fn option128_prefix_6(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        p5: u64,
        value: Option<u128>,
        suffix: u64,
    ) -> u128;
    fn option128_outgoing_6(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        p5: u64,
        bits: u128,
        some: bool,
        suffix: u64,
    ) -> u128;
    fn option128_prefix_7(
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
    fn option128_outgoing_7(
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
    ) -> u128;
    fn option128_prefix_8(
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
    fn option128_outgoing_8(
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
    ) -> u128;
    fn option128_prefix_9(
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
    fn option128_outgoing_9(
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
    ) -> u128;
    fn signed_prefix_1(p0: u64, value: Option<i128>, suffix: u64) -> u128;
    fn outgoing_signed_prefix_1(p0: u64, value: Option<i128>, suffix: u64) -> u128;
    fn signed_prefix_5(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        value: Option<i128>,
        suffix: u64,
    ) -> u128;
    fn outgoing_signed_prefix_5(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        value: Option<i128>,
        suffix: u64,
    ) -> u128;
    fn signed_prefix_7(
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
    fn outgoing_signed_prefix_7(
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
    fn signed_prefix_9(
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
    fn outgoing_signed_prefix_9(
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
    fn pair_wide_prefix_1(p0: u64, value: (u128, u128), suffix: u64) -> u128;
    fn outgoing_pair_wide_prefix_1(p0: u64, value: (u128, u128), suffix: u64) -> u128;
    fn pair_wide_prefix_5(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        value: (u128, u128),
        suffix: u64,
    ) -> u128;
    fn outgoing_pair_wide_prefix_5(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        value: (u128, u128),
        suffix: u64,
    ) -> u128;
    fn pair_wide_prefix_7(
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
    fn outgoing_pair_wide_prefix_7(
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
    fn pair_wide_prefix_9(
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
    fn outgoing_pair_wide_prefix_9(
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
    fn pair_narrow_wide_prefix_1(p0: u64, value: (u64, u128), suffix: u64) -> u128;
    fn outgoing_pair_narrow_wide_prefix_1(p0: u64, value: (u64, u128), suffix: u64) -> u128;
    fn pair_narrow_wide_prefix_5(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        value: (u64, u128),
        suffix: u64,
    ) -> u128;
    fn outgoing_pair_narrow_wide_prefix_5(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        value: (u64, u128),
        suffix: u64,
    ) -> u128;
    fn pair_narrow_wide_prefix_7(
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
    fn outgoing_pair_narrow_wide_prefix_7(
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
    fn pair_narrow_wide_prefix_9(
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
    fn outgoing_pair_narrow_wide_prefix_9(
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
    fn pair_wide_narrow_prefix_1(p0: u64, value: (u128, u64), suffix: u64) -> u128;
    fn outgoing_pair_wide_narrow_prefix_1(p0: u64, value: (u128, u64), suffix: u64) -> u128;
    fn pair_wide_narrow_prefix_5(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        value: (u128, u64),
        suffix: u64,
    ) -> u128;
    fn outgoing_pair_wide_narrow_prefix_5(
        p0: u64,
        p1: u64,
        p2: u64,
        p3: u64,
        p4: u64,
        value: (u128, u64),
        suffix: u64,
    ) -> u128;
    fn pair_wide_narrow_prefix_7(
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
    fn outgoing_pair_wide_narrow_prefix_7(
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
    fn pair_wide_narrow_prefix_9(
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
    fn outgoing_pair_wide_narrow_prefix_9(
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
    fn option128_indirect(
        f: fn(u64, Option<u128>, u64) -> u128,
        p: u64,
        bits: u128,
        some: bool,
        s: u64,
    ) -> u128;
}
#[unsafe(no_mangle)]
pub fn llvm_option128_prefix_0(value: Option<u128>, suffix: u64) -> u128 {
    value.unwrap_or(0x96eec3e112347650aa665588f00dcafeu128) ^ ((suffix as u128).rotate_left(79))
}
#[unsafe(no_mangle)]
pub fn llvm_option128_prefix_1(p0: u64, value: Option<u128>, suffix: u64) -> u128 {
    value.unwrap_or(0x96eec3e112347650aa665588f00dcafeu128)
        ^ ((p0 as u128).rotate_left(17))
        ^ ((suffix as u128).rotate_left(79))
}
#[unsafe(no_mangle)]
pub fn llvm_option128_prefix_2(p0: u64, p1: u64, value: Option<u128>, suffix: u64) -> u128 {
    value.unwrap_or(0x96eec3e112347650aa665588f00dcafeu128)
        ^ ((p0 as u128).rotate_left(17))
        ^ ((p1 as u128).rotate_left(30))
        ^ ((suffix as u128).rotate_left(79))
}
#[unsafe(no_mangle)]
pub fn llvm_option128_prefix_3(
    p0: u64,
    p1: u64,
    p2: u64,
    value: Option<u128>,
    suffix: u64,
) -> u128 {
    value.unwrap_or(0x96eec3e112347650aa665588f00dcafeu128)
        ^ ((p0 as u128).rotate_left(17))
        ^ ((p1 as u128).rotate_left(30))
        ^ ((p2 as u128).rotate_left(43))
        ^ ((suffix as u128).rotate_left(79))
}
#[unsafe(no_mangle)]
pub fn llvm_option128_prefix_4(
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
#[unsafe(no_mangle)]
pub fn llvm_option128_prefix_5(
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
#[unsafe(no_mangle)]
pub fn llvm_option128_prefix_6(
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
#[unsafe(no_mangle)]
pub fn llvm_option128_prefix_7(
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
#[unsafe(no_mangle)]
pub fn llvm_option128_prefix_8(
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
#[unsafe(no_mangle)]
pub fn llvm_option128_prefix_9(
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
#[unsafe(no_mangle)]
pub fn llvm_signed_prefix_1(p0: u64, value: Option<i128>, suffix: u64) -> u128 {
    (value.unwrap_or(-0x7234123498765555111133336666888i128) as u128)
        ^ ((p0 as u128).rotate_left(3))
        ^ ((suffix as u128).rotate_left(97))
}
#[unsafe(no_mangle)]
pub fn llvm_signed_prefix_5(
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
#[unsafe(no_mangle)]
pub fn llvm_signed_prefix_7(
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
#[unsafe(no_mangle)]
pub fn llvm_signed_prefix_9(
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
#[unsafe(no_mangle)]
pub fn llvm_pair_wide_prefix_1(p0: u64, value: (u128, u128), suffix: u64) -> u128 {
    (value.0.rotate_left(13) ^ value.1)
        ^ ((p0 as u128).rotate_left(3))
        ^ ((suffix as u128).rotate_left(97))
}
#[unsafe(no_mangle)]
pub fn llvm_pair_wide_prefix_5(
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
#[unsafe(no_mangle)]
pub fn llvm_pair_wide_prefix_7(
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
#[unsafe(no_mangle)]
pub fn llvm_pair_wide_prefix_9(
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
#[unsafe(no_mangle)]
pub fn llvm_pair_narrow_wide_prefix_1(p0: u64, value: (u64, u128), suffix: u64) -> u128 {
    ((value.0 as u128).rotate_left(17) ^ value.1)
        ^ ((p0 as u128).rotate_left(3))
        ^ ((suffix as u128).rotate_left(97))
}
#[unsafe(no_mangle)]
pub fn llvm_pair_narrow_wide_prefix_5(
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
#[unsafe(no_mangle)]
pub fn llvm_pair_narrow_wide_prefix_7(
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
#[unsafe(no_mangle)]
pub fn llvm_pair_narrow_wide_prefix_9(
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
#[unsafe(no_mangle)]
pub fn llvm_pair_wide_narrow_prefix_1(p0: u64, value: (u128, u64), suffix: u64) -> u128 {
    (value.0.rotate_left(23) ^ (value.1 as u128))
        ^ ((p0 as u128).rotate_left(3))
        ^ ((suffix as u128).rotate_left(97))
}
#[unsafe(no_mangle)]
pub fn llvm_pair_wide_narrow_prefix_5(
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
#[unsafe(no_mangle)]
pub fn llvm_pair_wide_narrow_prefix_7(
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
#[unsafe(no_mangle)]
pub fn llvm_pair_wide_narrow_prefix_9(
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
fn main() {
    let mut checks = 0;
    for i in 0..256u64 {
        let bits = ((i.wrapping_mul(0x9e3779b97f4a7c15) as u128) << 64)
            | (i.wrapping_mul(0xd6e8feb86659fd93) as u128);
        let suffix = i.wrapping_mul(103).wrapping_add(31);
        for some in [false, true] {
            let value = if some { Some(bits) } else { None };
            unsafe {
                assert_eq!(
                    option128_prefix_0(value, suffix),
                    llvm_option128_prefix_0(value, suffix),
                    "incoming prefix 0"
                );
                assert_eq!(
                    option128_outgoing_0(bits, some, suffix),
                    llvm_option128_prefix_0(value, suffix),
                    "outgoing prefix 0"
                );
                assert_eq!(
                    option128_prefix_1(i.wrapping_mul(97u64).wrapping_add(11), value, suffix),
                    llvm_option128_prefix_1(i.wrapping_mul(97u64).wrapping_add(11), value, suffix),
                    "incoming prefix 1"
                );
                assert_eq!(
                    option128_outgoing_1(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        bits,
                        some,
                        suffix
                    ),
                    llvm_option128_prefix_1(i.wrapping_mul(97u64).wrapping_add(11), value, suffix),
                    "outgoing prefix 1"
                );
                assert_eq!(
                    option128_prefix_2(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        value,
                        suffix
                    ),
                    llvm_option128_prefix_2(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        value,
                        suffix
                    ),
                    "incoming prefix 2"
                );
                assert_eq!(
                    option128_outgoing_2(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        bits,
                        some,
                        suffix
                    ),
                    llvm_option128_prefix_2(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        value,
                        suffix
                    ),
                    "outgoing prefix 2"
                );
                assert_eq!(
                    option128_prefix_3(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        value,
                        suffix
                    ),
                    llvm_option128_prefix_3(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        value,
                        suffix
                    ),
                    "incoming prefix 3"
                );
                assert_eq!(
                    option128_outgoing_3(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        bits,
                        some,
                        suffix
                    ),
                    llvm_option128_prefix_3(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        value,
                        suffix
                    ),
                    "outgoing prefix 3"
                );
                assert_eq!(
                    option128_prefix_4(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        value,
                        suffix
                    ),
                    llvm_option128_prefix_4(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        value,
                        suffix
                    ),
                    "incoming prefix 4"
                );
                assert_eq!(
                    option128_outgoing_4(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        bits,
                        some,
                        suffix
                    ),
                    llvm_option128_prefix_4(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        value,
                        suffix
                    ),
                    "outgoing prefix 4"
                );
                assert_eq!(
                    option128_prefix_5(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        value,
                        suffix
                    ),
                    llvm_option128_prefix_5(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        value,
                        suffix
                    ),
                    "incoming prefix 5"
                );
                assert_eq!(
                    option128_outgoing_5(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        bits,
                        some,
                        suffix
                    ),
                    llvm_option128_prefix_5(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        value,
                        suffix
                    ),
                    "outgoing prefix 5"
                );
                assert_eq!(
                    option128_prefix_6(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        i.wrapping_mul(157u64).wrapping_add(16),
                        value,
                        suffix
                    ),
                    llvm_option128_prefix_6(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        i.wrapping_mul(157u64).wrapping_add(16),
                        value,
                        suffix
                    ),
                    "incoming prefix 6"
                );
                assert_eq!(
                    option128_outgoing_6(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        i.wrapping_mul(157u64).wrapping_add(16),
                        bits,
                        some,
                        suffix
                    ),
                    llvm_option128_prefix_6(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        i.wrapping_mul(157u64).wrapping_add(16),
                        value,
                        suffix
                    ),
                    "outgoing prefix 6"
                );
                assert_eq!(
                    option128_prefix_7(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        i.wrapping_mul(157u64).wrapping_add(16),
                        i.wrapping_mul(169u64).wrapping_add(17),
                        value,
                        suffix
                    ),
                    llvm_option128_prefix_7(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        i.wrapping_mul(157u64).wrapping_add(16),
                        i.wrapping_mul(169u64).wrapping_add(17),
                        value,
                        suffix
                    ),
                    "incoming prefix 7"
                );
                assert_eq!(
                    option128_outgoing_7(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        i.wrapping_mul(157u64).wrapping_add(16),
                        i.wrapping_mul(169u64).wrapping_add(17),
                        bits,
                        some,
                        suffix
                    ),
                    llvm_option128_prefix_7(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        i.wrapping_mul(157u64).wrapping_add(16),
                        i.wrapping_mul(169u64).wrapping_add(17),
                        value,
                        suffix
                    ),
                    "outgoing prefix 7"
                );
                assert_eq!(
                    option128_prefix_8(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        i.wrapping_mul(157u64).wrapping_add(16),
                        i.wrapping_mul(169u64).wrapping_add(17),
                        i.wrapping_mul(181u64).wrapping_add(18),
                        value,
                        suffix
                    ),
                    llvm_option128_prefix_8(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        i.wrapping_mul(157u64).wrapping_add(16),
                        i.wrapping_mul(169u64).wrapping_add(17),
                        i.wrapping_mul(181u64).wrapping_add(18),
                        value,
                        suffix
                    ),
                    "incoming prefix 8"
                );
                assert_eq!(
                    option128_outgoing_8(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        i.wrapping_mul(157u64).wrapping_add(16),
                        i.wrapping_mul(169u64).wrapping_add(17),
                        i.wrapping_mul(181u64).wrapping_add(18),
                        bits,
                        some,
                        suffix
                    ),
                    llvm_option128_prefix_8(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        i.wrapping_mul(157u64).wrapping_add(16),
                        i.wrapping_mul(169u64).wrapping_add(17),
                        i.wrapping_mul(181u64).wrapping_add(18),
                        value,
                        suffix
                    ),
                    "outgoing prefix 8"
                );
                assert_eq!(
                    option128_prefix_9(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        i.wrapping_mul(157u64).wrapping_add(16),
                        i.wrapping_mul(169u64).wrapping_add(17),
                        i.wrapping_mul(181u64).wrapping_add(18),
                        i.wrapping_mul(193u64).wrapping_add(19),
                        value,
                        suffix
                    ),
                    llvm_option128_prefix_9(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        i.wrapping_mul(157u64).wrapping_add(16),
                        i.wrapping_mul(169u64).wrapping_add(17),
                        i.wrapping_mul(181u64).wrapping_add(18),
                        i.wrapping_mul(193u64).wrapping_add(19),
                        value,
                        suffix
                    ),
                    "incoming prefix 9"
                );
                assert_eq!(
                    option128_outgoing_9(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        i.wrapping_mul(157u64).wrapping_add(16),
                        i.wrapping_mul(169u64).wrapping_add(17),
                        i.wrapping_mul(181u64).wrapping_add(18),
                        i.wrapping_mul(193u64).wrapping_add(19),
                        bits,
                        some,
                        suffix
                    ),
                    llvm_option128_prefix_9(
                        i.wrapping_mul(97u64).wrapping_add(11),
                        i.wrapping_mul(109u64).wrapping_add(12),
                        i.wrapping_mul(121u64).wrapping_add(13),
                        i.wrapping_mul(133u64).wrapping_add(14),
                        i.wrapping_mul(145u64).wrapping_add(15),
                        i.wrapping_mul(157u64).wrapping_add(16),
                        i.wrapping_mul(169u64).wrapping_add(17),
                        i.wrapping_mul(181u64).wrapping_add(18),
                        i.wrapping_mul(193u64).wrapping_add(19),
                        value,
                        suffix
                    ),
                    "outgoing prefix 9"
                );
                assert_eq!(
                    signed_prefix_1(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        if some { Some(bits as i128) } else { None },
                        suffix
                    ),
                    llvm_signed_prefix_1(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        if some { Some(bits as i128) } else { None },
                        suffix
                    ),
                    "incoming signed prefix 1"
                );
                assert_eq!(
                    outgoing_signed_prefix_1(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        if some { Some(bits as i128) } else { None },
                        suffix
                    ),
                    llvm_signed_prefix_1(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        if some { Some(bits as i128) } else { None },
                        suffix
                    ),
                    "outgoing signed prefix 1"
                );
                assert_eq!(
                    signed_prefix_5(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        if some { Some(bits as i128) } else { None },
                        suffix
                    ),
                    llvm_signed_prefix_5(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        if some { Some(bits as i128) } else { None },
                        suffix
                    ),
                    "incoming signed prefix 5"
                );
                assert_eq!(
                    outgoing_signed_prefix_5(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        if some { Some(bits as i128) } else { None },
                        suffix
                    ),
                    llvm_signed_prefix_5(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        if some { Some(bits as i128) } else { None },
                        suffix
                    ),
                    "outgoing signed prefix 5"
                );
                assert_eq!(
                    signed_prefix_7(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        if some { Some(bits as i128) } else { None },
                        suffix
                    ),
                    llvm_signed_prefix_7(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        if some { Some(bits as i128) } else { None },
                        suffix
                    ),
                    "incoming signed prefix 7"
                );
                assert_eq!(
                    outgoing_signed_prefix_7(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        if some { Some(bits as i128) } else { None },
                        suffix
                    ),
                    llvm_signed_prefix_7(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        if some { Some(bits as i128) } else { None },
                        suffix
                    ),
                    "outgoing signed prefix 7"
                );
                assert_eq!(
                    signed_prefix_9(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        i.wrapping_mul(235u64).wrapping_add(36),
                        i.wrapping_mul(249u64).wrapping_add(37),
                        if some { Some(bits as i128) } else { None },
                        suffix
                    ),
                    llvm_signed_prefix_9(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        i.wrapping_mul(235u64).wrapping_add(36),
                        i.wrapping_mul(249u64).wrapping_add(37),
                        if some { Some(bits as i128) } else { None },
                        suffix
                    ),
                    "incoming signed prefix 9"
                );
                assert_eq!(
                    outgoing_signed_prefix_9(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        i.wrapping_mul(235u64).wrapping_add(36),
                        i.wrapping_mul(249u64).wrapping_add(37),
                        if some { Some(bits as i128) } else { None },
                        suffix
                    ),
                    llvm_signed_prefix_9(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        i.wrapping_mul(235u64).wrapping_add(36),
                        i.wrapping_mul(249u64).wrapping_add(37),
                        if some { Some(bits as i128) } else { None },
                        suffix
                    ),
                    "outgoing signed prefix 9"
                );
                assert_eq!(
                    pair_wide_prefix_1(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        (bits, !bits),
                        suffix
                    ),
                    llvm_pair_wide_prefix_1(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        (bits, !bits),
                        suffix
                    ),
                    "incoming pair_wide prefix 1"
                );
                assert_eq!(
                    outgoing_pair_wide_prefix_1(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        (bits, !bits),
                        suffix
                    ),
                    llvm_pair_wide_prefix_1(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        (bits, !bits),
                        suffix
                    ),
                    "outgoing pair_wide prefix 1"
                );
                assert_eq!(
                    pair_wide_prefix_5(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        (bits, !bits),
                        suffix
                    ),
                    llvm_pair_wide_prefix_5(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        (bits, !bits),
                        suffix
                    ),
                    "incoming pair_wide prefix 5"
                );
                assert_eq!(
                    outgoing_pair_wide_prefix_5(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        (bits, !bits),
                        suffix
                    ),
                    llvm_pair_wide_prefix_5(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        (bits, !bits),
                        suffix
                    ),
                    "outgoing pair_wide prefix 5"
                );
                assert_eq!(
                    pair_wide_prefix_7(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        (bits, !bits),
                        suffix
                    ),
                    llvm_pair_wide_prefix_7(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        (bits, !bits),
                        suffix
                    ),
                    "incoming pair_wide prefix 7"
                );
                assert_eq!(
                    outgoing_pair_wide_prefix_7(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        (bits, !bits),
                        suffix
                    ),
                    llvm_pair_wide_prefix_7(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        (bits, !bits),
                        suffix
                    ),
                    "outgoing pair_wide prefix 7"
                );
                assert_eq!(
                    pair_wide_prefix_9(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        i.wrapping_mul(235u64).wrapping_add(36),
                        i.wrapping_mul(249u64).wrapping_add(37),
                        (bits, !bits),
                        suffix
                    ),
                    llvm_pair_wide_prefix_9(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        i.wrapping_mul(235u64).wrapping_add(36),
                        i.wrapping_mul(249u64).wrapping_add(37),
                        (bits, !bits),
                        suffix
                    ),
                    "incoming pair_wide prefix 9"
                );
                assert_eq!(
                    outgoing_pair_wide_prefix_9(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        i.wrapping_mul(235u64).wrapping_add(36),
                        i.wrapping_mul(249u64).wrapping_add(37),
                        (bits, !bits),
                        suffix
                    ),
                    llvm_pair_wide_prefix_9(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        i.wrapping_mul(235u64).wrapping_add(36),
                        i.wrapping_mul(249u64).wrapping_add(37),
                        (bits, !bits),
                        suffix
                    ),
                    "outgoing pair_wide prefix 9"
                );
                assert_eq!(
                    pair_narrow_wide_prefix_1(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        (i.wrapping_mul(7919), bits),
                        suffix
                    ),
                    llvm_pair_narrow_wide_prefix_1(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        (i.wrapping_mul(7919), bits),
                        suffix
                    ),
                    "incoming pair_narrow_wide prefix 1"
                );
                assert_eq!(
                    outgoing_pair_narrow_wide_prefix_1(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        (i.wrapping_mul(7919), bits),
                        suffix
                    ),
                    llvm_pair_narrow_wide_prefix_1(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        (i.wrapping_mul(7919), bits),
                        suffix
                    ),
                    "outgoing pair_narrow_wide prefix 1"
                );
                assert_eq!(
                    pair_narrow_wide_prefix_5(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        (i.wrapping_mul(7919), bits),
                        suffix
                    ),
                    llvm_pair_narrow_wide_prefix_5(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        (i.wrapping_mul(7919), bits),
                        suffix
                    ),
                    "incoming pair_narrow_wide prefix 5"
                );
                assert_eq!(
                    outgoing_pair_narrow_wide_prefix_5(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        (i.wrapping_mul(7919), bits),
                        suffix
                    ),
                    llvm_pair_narrow_wide_prefix_5(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        (i.wrapping_mul(7919), bits),
                        suffix
                    ),
                    "outgoing pair_narrow_wide prefix 5"
                );
                assert_eq!(
                    pair_narrow_wide_prefix_7(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        (i.wrapping_mul(7919), bits),
                        suffix
                    ),
                    llvm_pair_narrow_wide_prefix_7(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        (i.wrapping_mul(7919), bits),
                        suffix
                    ),
                    "incoming pair_narrow_wide prefix 7"
                );
                assert_eq!(
                    outgoing_pair_narrow_wide_prefix_7(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        (i.wrapping_mul(7919), bits),
                        suffix
                    ),
                    llvm_pair_narrow_wide_prefix_7(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        (i.wrapping_mul(7919), bits),
                        suffix
                    ),
                    "outgoing pair_narrow_wide prefix 7"
                );
                assert_eq!(
                    pair_narrow_wide_prefix_9(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        i.wrapping_mul(235u64).wrapping_add(36),
                        i.wrapping_mul(249u64).wrapping_add(37),
                        (i.wrapping_mul(7919), bits),
                        suffix
                    ),
                    llvm_pair_narrow_wide_prefix_9(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        i.wrapping_mul(235u64).wrapping_add(36),
                        i.wrapping_mul(249u64).wrapping_add(37),
                        (i.wrapping_mul(7919), bits),
                        suffix
                    ),
                    "incoming pair_narrow_wide prefix 9"
                );
                assert_eq!(
                    outgoing_pair_narrow_wide_prefix_9(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        i.wrapping_mul(235u64).wrapping_add(36),
                        i.wrapping_mul(249u64).wrapping_add(37),
                        (i.wrapping_mul(7919), bits),
                        suffix
                    ),
                    llvm_pair_narrow_wide_prefix_9(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        i.wrapping_mul(235u64).wrapping_add(36),
                        i.wrapping_mul(249u64).wrapping_add(37),
                        (i.wrapping_mul(7919), bits),
                        suffix
                    ),
                    "outgoing pair_narrow_wide prefix 9"
                );
                assert_eq!(
                    pair_wide_narrow_prefix_1(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        (bits, i.wrapping_mul(7919)),
                        suffix
                    ),
                    llvm_pair_wide_narrow_prefix_1(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        (bits, i.wrapping_mul(7919)),
                        suffix
                    ),
                    "incoming pair_wide_narrow prefix 1"
                );
                assert_eq!(
                    outgoing_pair_wide_narrow_prefix_1(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        (bits, i.wrapping_mul(7919)),
                        suffix
                    ),
                    llvm_pair_wide_narrow_prefix_1(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        (bits, i.wrapping_mul(7919)),
                        suffix
                    ),
                    "outgoing pair_wide_narrow prefix 1"
                );
                assert_eq!(
                    pair_wide_narrow_prefix_5(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        (bits, i.wrapping_mul(7919)),
                        suffix
                    ),
                    llvm_pair_wide_narrow_prefix_5(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        (bits, i.wrapping_mul(7919)),
                        suffix
                    ),
                    "incoming pair_wide_narrow prefix 5"
                );
                assert_eq!(
                    outgoing_pair_wide_narrow_prefix_5(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        (bits, i.wrapping_mul(7919)),
                        suffix
                    ),
                    llvm_pair_wide_narrow_prefix_5(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        (bits, i.wrapping_mul(7919)),
                        suffix
                    ),
                    "outgoing pair_wide_narrow prefix 5"
                );
                assert_eq!(
                    pair_wide_narrow_prefix_7(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        (bits, i.wrapping_mul(7919)),
                        suffix
                    ),
                    llvm_pair_wide_narrow_prefix_7(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        (bits, i.wrapping_mul(7919)),
                        suffix
                    ),
                    "incoming pair_wide_narrow prefix 7"
                );
                assert_eq!(
                    outgoing_pair_wide_narrow_prefix_7(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        (bits, i.wrapping_mul(7919)),
                        suffix
                    ),
                    llvm_pair_wide_narrow_prefix_7(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        (bits, i.wrapping_mul(7919)),
                        suffix
                    ),
                    "outgoing pair_wide_narrow prefix 7"
                );
                assert_eq!(
                    pair_wide_narrow_prefix_9(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        i.wrapping_mul(235u64).wrapping_add(36),
                        i.wrapping_mul(249u64).wrapping_add(37),
                        (bits, i.wrapping_mul(7919)),
                        suffix
                    ),
                    llvm_pair_wide_narrow_prefix_9(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        i.wrapping_mul(235u64).wrapping_add(36),
                        i.wrapping_mul(249u64).wrapping_add(37),
                        (bits, i.wrapping_mul(7919)),
                        suffix
                    ),
                    "incoming pair_wide_narrow prefix 9"
                );
                assert_eq!(
                    outgoing_pair_wide_narrow_prefix_9(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        i.wrapping_mul(235u64).wrapping_add(36),
                        i.wrapping_mul(249u64).wrapping_add(37),
                        (bits, i.wrapping_mul(7919)),
                        suffix
                    ),
                    llvm_pair_wide_narrow_prefix_9(
                        i.wrapping_mul(137u64).wrapping_add(29),
                        i.wrapping_mul(151u64).wrapping_add(30),
                        i.wrapping_mul(165u64).wrapping_add(31),
                        i.wrapping_mul(179u64).wrapping_add(32),
                        i.wrapping_mul(193u64).wrapping_add(33),
                        i.wrapping_mul(207u64).wrapping_add(34),
                        i.wrapping_mul(221u64).wrapping_add(35),
                        i.wrapping_mul(235u64).wrapping_add(36),
                        i.wrapping_mul(249u64).wrapping_add(37),
                        (bits, i.wrapping_mul(7919)),
                        suffix
                    ),
                    "outgoing pair_wide_narrow prefix 9"
                );
                assert_eq!(
                    option128_indirect(llvm_option128_prefix_1, i, bits, some, suffix),
                    llvm_option128_prefix_1(i, value, suffix),
                    "indirect"
                );
                checks += 53;
            }
        }
    }
    println!("PASS option128_expanded checks={checks}");
}
