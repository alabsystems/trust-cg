// The driver of the float -> integer differential, always built by LLVM. It
// links ONE build of casts.rs (trust-cg's or LLVM's), calls every conversion
// on every input of spec.rs (which the harness appends to this source), and
// prints one line per call:
//
//   <function> <input encoding, hex> <result's bit pattern, hex>[ MISMATCH want <spec>]
//
// `to_int_unchecked` is called only where spec.rs says it is defined. The
// last line is `SUMMARY calls=<n> mismatches=<m>`; the exit code is 0 only when
// every result equals the spec. Equal stdout of the two builds is the
// differential; the spec column holds both to Rust's semantics.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
#![allow(improper_ctypes)]

use std::fmt::Write as _;

trait Float: Copy {
    const EXP_BITS: u32;
    const MAN_BITS: u32;
    fn encoding(self) -> u64;
    fn from_encoding(bits: u64) -> Self;
    fn inputs() -> Vec<u64>;
}

impl Float for f32 {
    const EXP_BITS: u32 = 8;
    const MAN_BITS: u32 = 23;
    fn encoding(self) -> u64 {
        u64::from(self.to_bits())
    }
    fn from_encoding(bits: u64) -> Self {
        f32::from_bits(bits as u32)
    }
    fn inputs() -> Vec<u64> {
        spec_inputs_f32()
    }
}

impl Float for f64 {
    const EXP_BITS: u32 = 11;
    const MAN_BITS: u32 = 52;
    fn encoding(self) -> u64 {
        self.to_bits()
    }
    fn from_encoding(bits: u64) -> Self {
        f64::from_bits(bits)
    }
    fn inputs() -> Vec<u64> {
        spec_inputs_f64()
    }
}

trait Int: Copy {
    const BITS: u32;
    const SIGNED: bool;
    fn pattern(self) -> u128;
}

macro_rules! int {
    ($($int:ty, $unsigned:ty, $signed:expr;)*) => {$(
        impl Int for $int {
            const BITS: u32 = <$int>::BITS;
            const SIGNED: bool = $signed;
            fn pattern(self) -> u128 {
                self as $unsigned as u128
            }
        }
    )*};
}

int! {
    i8, u8, true; i16, u16, true; i32, u32, true; i64, u64, true; i128, u128, true;
    isize, usize, true;
    u8, u8, false; u16, u16, false; u32, u32, false; u64, u64, false; u128, u128, false;
    usize, usize, false;
}

struct Tally {
    out: String,
    calls: u64,
    mismatches: u64,
}

impl Tally {
    fn record(&mut self, function: &str, input: u64, got: u128, want: u128) {
        self.calls += 1;
        let _ = write!(self.out, "{function} {input:016x} {got:032x}");
        if got != want {
            self.mismatches += 1;
            let _ = write!(self.out, " MISMATCH want {want:032x}");
        }
        self.out.push('\n');
    }
}

fn check<F: Float, I: Int>(
    tally: &mut Tally,
    as_name: &str,
    as_cast: unsafe extern "C" fn(F) -> I,
    unchecked_name: &str,
    unchecked: unsafe extern "C" fn(F) -> I,
) {
    for bits in F::inputs() {
        let x = F::from_encoding(bits);
        let truncated = spec_trunc(x.encoding(), F::EXP_BITS, F::MAN_BITS);
        let want = spec_saturating(truncated, I::BITS, I::SIGNED);
        // SAFETY: `as_*` is a safe Rust function exported with the C ABI.
        let got = unsafe { as_cast(std::hint::black_box(x)) }.pattern();
        tally.record(as_name, bits, got, want);
        if spec_unchecked_defined(truncated, I::BITS, I::SIGNED) {
            // SAFETY: spec.rs places `x` inside `to_int_unchecked`'s domain.
            let got = unsafe { unchecked(std::hint::black_box(x)) }.pattern();
            tally.record(unchecked_name, bits, got, want);
        }
    }
}

macro_rules! table {
    ($($float:ty => $int:ty: $as_name:ident, $unchecked_name:ident;)*) => {
        extern "C" {
            $(
                fn $as_name(x: $float) -> $int;
                fn $unchecked_name(x: $float) -> $int;
            )*
        }

        fn run(tally: &mut Tally) {
            $(
                check::<$float, $int>(
                    tally,
                    stringify!($as_name),
                    $as_name,
                    stringify!($unchecked_name),
                    $unchecked_name,
                );
            )*
        }
    };
}

table! {
    f32 => i8: as_f32_i8, unchecked_f32_i8;
    f32 => i16: as_f32_i16, unchecked_f32_i16;
    f32 => i32: as_f32_i32, unchecked_f32_i32;
    f32 => i64: as_f32_i64, unchecked_f32_i64;
    f32 => i128: as_f32_i128, unchecked_f32_i128;
    f32 => isize: as_f32_isize, unchecked_f32_isize;
    f32 => u8: as_f32_u8, unchecked_f32_u8;
    f32 => u16: as_f32_u16, unchecked_f32_u16;
    f32 => u32: as_f32_u32, unchecked_f32_u32;
    f32 => u64: as_f32_u64, unchecked_f32_u64;
    f32 => u128: as_f32_u128, unchecked_f32_u128;
    f32 => usize: as_f32_usize, unchecked_f32_usize;
    f64 => i8: as_f64_i8, unchecked_f64_i8;
    f64 => i16: as_f64_i16, unchecked_f64_i16;
    f64 => i32: as_f64_i32, unchecked_f64_i32;
    f64 => i64: as_f64_i64, unchecked_f64_i64;
    f64 => i128: as_f64_i128, unchecked_f64_i128;
    f64 => isize: as_f64_isize, unchecked_f64_isize;
    f64 => u8: as_f64_u8, unchecked_f64_u8;
    f64 => u16: as_f64_u16, unchecked_f64_u16;
    f64 => u32: as_f64_u32, unchecked_f64_u32;
    f64 => u64: as_f64_u64, unchecked_f64_u64;
    f64 => u128: as_f64_u128, unchecked_f64_u128;
    f64 => usize: as_f64_usize, unchecked_f64_usize;
}

fn main() {
    let mut tally = Tally {
        out: String::new(),
        calls: 0,
        mismatches: 0,
    };
    run(&mut tally);
    print!("{}", tally.out);
    println!(
        "SUMMARY calls={} mismatches={}",
        tally.calls, tally.mismatches
    );
    std::process::exit(i32::from(tally.mismatches != 0));
}

// spec.rs follows (appended by the harness).
