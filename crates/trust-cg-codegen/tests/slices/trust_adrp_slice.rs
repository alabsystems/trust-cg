// Trust-toolchain slice — trust-cg AArch64 PC-RELATIVE ADDRESS encoders + the
// range-check validators (trust-cg/crates/trust-cg-codegen/src/aarch64/
// encoding_mem.rs), transcribed VERBATIM.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 2, thread T4).
//
//   * `EncodeError` (encoding_mem.rs:21-35) — the payload-carrying error enum,
//     VERBATIM variant set/order/payloads. The `#[derive(Error)]` /
//     `#[error(..)]` thiserror attributes are dropped: they only generate
//     `Display`/`Error` impls, which are NOT in the call graph of any function
//     here, and derive macros don't affect the enum's layout.
//   * `check_reg`   (encoding_mem.rs:110-116) — VERBATIM.
//   * `check_imm21` (encoding_mem.rs:142-148) — VERBATIM except
//     `(-1_048_576..=1_048_575).contains(&value)` rewritten as the equivalent
//     explicit comparisons (RangeInclusive::contains does not lower — known
//     frontend limit). MODELED BOUNDARY, checked by the differential against
//     the verbatim-`contains` native oracle.
//   * `encode_adrp` (encoding_mem.rs:420-436) — VERBATIM. The immlo/immhi
//     bit-split of the signed 21-bit page offset: THE relocation-bearing
//     encoder (every global/const-pool access trust-cg emits goes through
//     ADRP+ADD/LDR page addressing).
//   * `encode_adr`  (encoding_mem.rs:447-463) — VERBATIM (op=0 variant).
//
// MODELED BOUNDARY — `?` REWRITTEN AS EXPLICIT MATCH. PINNED FRONTEND LIMIT
// found by this thread: the `?` operator on `Result` lowers to calls to
// EMPTY-BODIED externs `<Result<..> as Try>::branch` and
// `FromResidual::from_residual` (the Result-flavored sibling of handoff owner
// item #4's Option-Try-sret shim gap) — the emitted module would read
// uninitialized memory through the empty callee. The slice therefore spells
// each `check_x(..)?` as `match check_x(..) { Err(e) => return Err(e),
// Ok(()) => {} }`, which is the same control flow (`From::from` on the same
// error type is identity) lowered entirely from real MIR. Checked by the
// differential against the verbatim-`?` production native oracle.
//
// ABI note: `Result<u32, EncodeError>` is an enum-shaped return (Ok payload
// u32 | Err payload EncodeError{u8..i32}); the JIT returns it through the
// out-pointer per the frontend's faithful layout. The test decodes it with a
// layout-identical #[repr] transcription and compares against the REAL
// production `encode_adrp`/`encode_adr` (pub fns) as the native oracle.

#![allow(dead_code)]

// ── EncodeError (encoding_mem.rs:21-35) — VERBATIM variants/payloads;
//    thiserror derive dropped (Display/Error impls not in call graph) ────────
#[derive(Debug, PartialEq, Eq)]
pub enum EncodeError {
    RegisterOutOfRange { reg: u8, max: u8 },
    Imm12OutOfRange { value: u16 },
    Imm9OutOfRange { value: i16 },
    Imm7OutOfRange { value: i8 },
    Imm21OutOfRange { value: i32 },
    InvalidExtend(u8),
}

// ── check_reg (encoding_mem.rs:110-116) — VERBATIM ─────────────────────────
#[inline]
fn check_reg(reg: u8, max: u8) -> Result<(), EncodeError> {
    if reg > max {
        return Err(EncodeError::RegisterOutOfRange { reg, max });
    }
    Ok(())
}

// ── check_imm21 (encoding_mem.rs:142-148) — VERBATIM except the MODELED
//    `contains` rewrite (see header) ─────────────────────────────────────────
#[inline]
fn check_imm21(value: i32) -> Result<(), EncodeError> {
    // MODELED: production `!(-1_048_576..=1_048_575).contains(&value)`.
    if value < -1_048_576 || value > 1_048_575 {
        return Err(EncodeError::Imm21OutOfRange { value });
    }
    Ok(())
}

// ── encode_adrp (encoding_mem.rs:420-436) — VERBATIM except `?` -> match
//    (see header MODELED BOUNDARY) ─────────────────────────────────────────
pub fn encode_adrp(imm21: i32, rd: u8) -> Result<u32, EncodeError> {
    // MODELED: production `check_reg(rd, 31)?;` / `check_imm21(imm21)?;`.
    match check_reg(rd, 31) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match check_imm21(imm21) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }

    let bits = (imm21 as u32) & 0x1F_FFFF; // mask to 21 bits
    let immlo = bits & 0x3;
    let immhi = bits >> 2;

    let mut inst: u32 = 0;
    inst |= 1 << 31; // op = 1 (ADRP)
    inst |= immlo << 29;
    inst |= 0b10000 << 24;
    inst |= immhi << 5;
    inst |= rd as u32;
    Ok(inst)
}

// ── encode_adr (encoding_mem.rs:447-463) — VERBATIM except `?` -> match
//    (see header MODELED BOUNDARY) ─────────────────────────────────────────
pub fn encode_adr(imm21: i32, rd: u8) -> Result<u32, EncodeError> {
    // MODELED: production `check_reg(rd, 31)?;` / `check_imm21(imm21)?;`.
    match check_reg(rd, 31) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match check_imm21(imm21) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }

    let bits = (imm21 as u32) & 0x1F_FFFF; // mask to 21 bits
    let immlo = bits & 0x3;
    let immhi = bits >> 2;

    let mut inst: u32 = 0;
    // op = 0 (ADR, not ADRP) — bit 31 stays clear
    inst |= immlo << 29;
    inst |= 0b10000 << 24;
    inst |= immhi << 5;
    inst |= rd as u32;
    Ok(inst)
}

// ── C-ABI keep-alive entry ──────────────────────────────────────────────────
#[no_mangle]
pub extern "C" fn t4_entry_adrp(imm21: i32, rd: u8, which: u32) -> u32 {
    let r = if which == 0 { encode_adrp(imm21, rd) } else { encode_adr(imm21, rd) };
    match r {
        Ok(w) => w,
        Err(_) => 0,
    }
}

fn main() {
    println!("{:#010X}", t4_entry_adrp(1, 0, 0));
    println!("{:#010X}", t4_entry_adrp(-1, 3, 1));
    println!("{:#010X}", t4_entry_adrp(2_000_000, 3, 0)); // out of range -> 0
}
