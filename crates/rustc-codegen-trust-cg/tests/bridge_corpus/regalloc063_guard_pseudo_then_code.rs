// CORPUS FIXTURE — [TCG-REGALLOC-063] sub-family A: a TRAP/GUARD PSEUDO
// followed by ordinary code in the SAME machine block.
//
// WHY THIS FILE EXISTS. On aarch64 the guard carriers (`TrapBoundsCheckExact`,
// `TrapDivZeroIfZero`, `TrapShiftRangeIfOOB`, `TrapOverflowExact`) are stamped
// `IS_BRANCH | IS_TERMINATOR` — they flow control by TRAPPING and expand LATE
// into `CMP; B.<cc> +2; BRK`, which FALLS THROUGH. x86-64 and RISC-V stamp the
// same pseudos `IS_PSEUDO | HAS_SIDE_EFFECTS`, so only aarch64 has the problem.
// TV-3's `MachFunction` view read those instance flags through
// `is_terminator() && !is_conditional_branch()` and concluded "unconditional
// terminator", so EVERY real instruction after a guard in the same block was
// reported as "dead/fused code — the switch-BST block-collision signature".
//
// These are the exact `library/core` shapes that were refused: a constant-bound
// table index (`str::validations::utf8_char_width`,
// `unicode_data::white_space::lookup`, `dec2flt::Lemire::pow10_fast_path`), a
// runtime-length slice index, and a runtime divisor / shift / checked add whose
// guard is followed by a CALL (`num::imp::int_log10::u128_impl`).
//
// EVERY result is checked against a literal computed offline from Rust
// semantics, because this class fails by producing a WRONG VALUE silently (a
// clobbered register or a mis-dispatched block), not by crashing.
//
// All correct -> exit 0. Any mismatch -> that check's index.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
use core::hint::black_box;

static WIDTH: [u8; 256] = [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,0,0,0,0,0,0,0,0];
static POW10: [u64; 10] = [1, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000, 1000000000];

/// The `utf8_char_width` shape: constant-bound table index. Guard, then the
/// load, then the return — all one machine block.
#[inline(never)]
fn width(b: u8) -> usize {
    WIDTH[b as usize] as usize
}

/// Two guards and arithmetic between them in one block.
#[inline(never)]
fn width_pair(a: u8, b: u8) -> usize {
    WIDTH[a as usize] as usize * 10 + WIDTH[b as usize] as usize
}

/// Runtime-LENGTH bound (the `GuardBoundsCheckDyn` carrier: the bound slot
/// holds a register, not an immediate).
#[inline(never)]
fn nth(s: &[u64], i: usize) -> u64 {
    s[i]
}

/// Guard followed by a CALL — the `Bl`-after-terminator row.
#[inline(never)]
fn scaled(s: &[u64], i: usize, d: u64) -> u64 {
    let v = s[i];
    black_box(v / d)
}

/// Runtime divisor: `TrapDivZeroIfZero`, then the SDIV/UDIV, then the return.
#[inline(never)]
fn dv(a: u64, b: u64) -> u64 {
    a / b
}

#[inline(never)]
fn rm(a: u64, b: u64) -> u64 {
    a % b
}

/// Runtime shift amount: `TrapShiftRangeIfOOB`, then the LSL, then the return.
#[inline(never)]
fn shl(a: u64, k: u32) -> u64 {
    a << k
}

#[inline(never)]
fn shr(a: u64, k: u32) -> u64 {
    a >> k
}

/// Checked add: `TrapOverflowExact` at `-O0` (debug assertions on), then the
/// ADD, then the return.
#[inline(never)]
fn add(a: i64, b: i64) -> i64 {
    a + b
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    if width(black_box(65u8)) != 1 {
        return 1;
    }
    if width(black_box(226u8)) != 3 {
        return 2;
    }
    if width(black_box(240u8)) != 4 {
        return 3;
    }
    if width_pair(black_box(65u8), black_box(240u8)) != 14 {
        return 4;
    }
    let table: &[u64] = black_box(&POW10[..]);
    if nth(table, black_box(7usize)) != 10000000 {
        return 5;
    }
    if nth(table, black_box(0usize)) != 1 {
        return 6;
    }
    if scaled(table, black_box(9usize), black_box(7u64)) != 142857142 {
        return 7;
    }
    if dv(black_box(1_000_000_007u64), black_box(9973u64)) != 100270 {
        return 8;
    }
    if rm(black_box(1_000_000_007u64), black_box(9973u64)) != 7297 {
        return 9;
    }
    if shl(black_box(0x0123_4567_89ab_cdefu64), black_box(13u32)) != 7542668687916785664 {
        return 10;
    }
    if shr(black_box(0x0123_4567_89ab_cdefu64), black_box(29u32)) != 152709948 {
        return 11;
    }
    if add(black_box(9_000_000_000_000i64), black_box(-123_456_789i64)) != 8999876543211 {
        return 12;
    }
    0
}
