// Source of `tail_merged.macho`, a rustc-built arm64 Mach-O object whose
// string table tail-merges symbol names: every `_Sn_..._S1_A` is the tail of
// `_S39_..._S1_A`, so the 42 symbols name 2,937 bytes (terminators included)
// from a 168-byte string table. Regenerate it byte-identically with
//   rustc +nightly-2026-08-06 --target aarch64-apple-darwin --emit obj \
//     -o tail_merged.macho tail_merged.rs
// (`.o` files are git-ignored). MachOParser must parse it.
#![feature(no_core, lang_items)]
#![no_core]
#![crate_type = "lib"]
#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
#[lang = "sync"] pub unsafe trait Sync {}
#[lang = "drop_glue"] pub fn drop_glue<T: ?Sized>(_: *mut T) {}
impl Copy for u8 {}
unsafe impl Sync for u8 {}
#[unsafe(no_mangle)] pub static A: u8 = 0;
#[unsafe(no_mangle)] pub static S1_A: u8 = 1;
#[unsafe(no_mangle)] pub static S2_S1_A: u8 = 2;
#[unsafe(no_mangle)] pub static S3_S2_S1_A: u8 = 3;
#[unsafe(no_mangle)] pub static S4_S3_S2_S1_A: u8 = 4;
#[unsafe(no_mangle)] pub static S5_S4_S3_S2_S1_A: u8 = 5;
#[unsafe(no_mangle)] pub static S6_S5_S4_S3_S2_S1_A: u8 = 6;
#[unsafe(no_mangle)] pub static S7_S6_S5_S4_S3_S2_S1_A: u8 = 7;
#[unsafe(no_mangle)] pub static S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 8;
#[unsafe(no_mangle)] pub static S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 9;
#[unsafe(no_mangle)] pub static S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 10;
#[unsafe(no_mangle)] pub static S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 11;
#[unsafe(no_mangle)] pub static S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 12;
#[unsafe(no_mangle)] pub static S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 13;
#[unsafe(no_mangle)] pub static S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 14;
#[unsafe(no_mangle)] pub static S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 15;
#[unsafe(no_mangle)] pub static S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 16;
#[unsafe(no_mangle)] pub static S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 17;
#[unsafe(no_mangle)] pub static S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 18;
#[unsafe(no_mangle)] pub static S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 19;
#[unsafe(no_mangle)] pub static S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 20;
#[unsafe(no_mangle)] pub static S21_S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 21;
#[unsafe(no_mangle)] pub static S22_S21_S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 22;
#[unsafe(no_mangle)] pub static S23_S22_S21_S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 23;
#[unsafe(no_mangle)] pub static S24_S23_S22_S21_S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 24;
#[unsafe(no_mangle)] pub static S25_S24_S23_S22_S21_S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 25;
#[unsafe(no_mangle)] pub static S26_S25_S24_S23_S22_S21_S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 26;
#[unsafe(no_mangle)] pub static S27_S26_S25_S24_S23_S22_S21_S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 27;
#[unsafe(no_mangle)] pub static S28_S27_S26_S25_S24_S23_S22_S21_S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 28;
#[unsafe(no_mangle)] pub static S29_S28_S27_S26_S25_S24_S23_S22_S21_S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 29;
#[unsafe(no_mangle)] pub static S30_S29_S28_S27_S26_S25_S24_S23_S22_S21_S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 30;
#[unsafe(no_mangle)] pub static S31_S30_S29_S28_S27_S26_S25_S24_S23_S22_S21_S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 31;
#[unsafe(no_mangle)] pub static S32_S31_S30_S29_S28_S27_S26_S25_S24_S23_S22_S21_S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 32;
#[unsafe(no_mangle)] pub static S33_S32_S31_S30_S29_S28_S27_S26_S25_S24_S23_S22_S21_S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 33;
#[unsafe(no_mangle)] pub static S34_S33_S32_S31_S30_S29_S28_S27_S26_S25_S24_S23_S22_S21_S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 34;
#[unsafe(no_mangle)] pub static S35_S34_S33_S32_S31_S30_S29_S28_S27_S26_S25_S24_S23_S22_S21_S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 35;
#[unsafe(no_mangle)] pub static S36_S35_S34_S33_S32_S31_S30_S29_S28_S27_S26_S25_S24_S23_S22_S21_S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 36;
#[unsafe(no_mangle)] pub static S37_S36_S35_S34_S33_S32_S31_S30_S29_S28_S27_S26_S25_S24_S23_S22_S21_S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 37;
#[unsafe(no_mangle)] pub static S38_S37_S36_S35_S34_S33_S32_S31_S30_S29_S28_S27_S26_S25_S24_S23_S22_S21_S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 38;
#[unsafe(no_mangle)] pub static S39_S38_S37_S36_S35_S34_S33_S32_S31_S30_S29_S28_S27_S26_S25_S24_S23_S22_S21_S20_S19_S18_S17_S16_S15_S14_S13_S12_S11_S10_S9_S8_S7_S6_S5_S4_S3_S2_S1_A: u8 = 39;
