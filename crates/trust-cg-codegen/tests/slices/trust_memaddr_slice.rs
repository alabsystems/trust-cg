// Trust-toolchain slice — trust-cg AArch64 ADDRESSING-MODE encoders + their
// range-check validators (trust-cg/crates/trust-cg-codegen/src/aarch64/
// encoding_mem.rs), transcribed VERBATIM. Companion to round 2's
// trust_adrp_slice.rs — these are the LDR/STR/LDP/STP addressing modes round
// 2 did NOT cover (round 2 covered the ADR/ADRP PC-relative cluster +
// check_reg + check_imm21).
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 3, thread R2-B).
//
//   * `EncodeError` (encoding_mem.rs:21-35) — the payload-carrying error enum,
//     VERBATIM variant set/order/payloads. The `#[derive(Error)]` /
//     `#[error(..)]` thiserror attributes are dropped: they only generate
//     `Display`/`Error` impls, which are NOT in the call graph of any function
//     here, and derive macros don't affect the enum's layout.
//   * `LoadStoreSize` / `LoadStoreOp` / `RegExtend` / `PairOp` / `PairSize` /
//     `PairMode` (encoding_mem.rs:41-104) — the operand enums, VERBATIM
//     variant sets/discriminants (derives kept verbatim).
//   * `check_reg`   (encoding_mem.rs:110-116) — VERBATIM (already verified in
//     round 2; re-emitted here because it is in every root's closure).
//   * `check_imm12` (encoding_mem.rs:118-124) — VERBATIM (plain comparison).
//   * `check_imm9`  (encoding_mem.rs:126-132) — VERBATIM except
//     `(-256..=255).contains(&value)` rewritten as the equivalent explicit
//     comparisons (RangeInclusive::contains does not lower — known frontend
//     limit). MODELED BOUNDARY, checked by the differential against the
//     verbatim-`contains` production native oracle.
//   * `check_imm7`  (encoding_mem.rs:134-140) — VERBATIM except the same
//     `(-64..=63).contains(&value)` rewrite. MODELED BOUNDARY, same check.
//   * `encode_ldr_str_unsigned_offset` (encoding_mem.rs:166-188) — VERBATIM.
//   * `encode_ldr_str_pre_index`       (encoding_mem.rs:199-225) — VERBATIM.
//   * `encode_ldr_str_post_index`      (encoding_mem.rs:236-260) — VERBATIM.
//   * `encode_ldr_str_register`        (encoding_mem.rs:274-301) — VERBATIM.
//   * `encode_ldp_stp`                 (encoding_mem.rs:321-349) — VERBATIM.
//   * `encode_ldp_stp_offset`          (encoding_mem.rs:352-371) — VERBATIM.
//   * `encode_ldp_stp_pre_index`       (encoding_mem.rs:374-384) — VERBATIM.
//   * `encode_ldp_stp_post_index`      (encoding_mem.rs:387-406) — VERBATIM.
//   * `encode_ldrsw_register`          (encoding_mem.rs:477-495) — VERBATIM.
//
// MODELED BOUNDARY — `?` REWRITTEN AS EXPLICIT MATCH (same pinned frontend
// limit round 2 documented): the `?` operator on `Result` lowers to calls to
// EMPTY-BODIED externs `<Result<..> as Try>::branch` and
// `FromResidual::from_residual` — the emitted module would read uninitialized
// memory through the empty callee. The slice therefore spells each
// `check_x(..)?` as `match check_x(..) { Err(e) => return Err(e),
// Ok(()) => {} }`, which is the same control flow (`From::from` on the same
// error type is identity) lowered entirely from real MIR. Checked by the
// differential against the verbatim-`?` production native oracles (all pub).
//
// ABI note: `Result<u32, EncodeError>` is an enum-shaped return (Ok payload
// u32 | Err payload EncodeError{u8..i32}); the JIT returns it through the
// out-pointer per the frontend's faithful layout. Operand enums are fieldless
// scalar-tag enums passed BY VALUE. The test decodes the out-buffer at the
// offsets/tags the EMITTED IR itself bakes in and compares against the REAL
// production encoders (all pub) as the native oracle.

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

// ── the operand enums (encoding_mem.rs:41-104) — VERBATIM ───────────────────

/// Data size for scalar load/store instructions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoadStoreSize {
    /// Byte (8-bit) — size field = 0b00
    Byte = 0b00,
    /// Halfword (16-bit) — size field = 0b01
    Half = 0b01,
    /// Word (32-bit) — size field = 0b10
    Word = 0b10,
    /// Doubleword (64-bit) — size field = 0b11
    Double = 0b11,
}

/// Load vs store selector.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoadStoreOp {
    /// Store — opc = 0b00
    Store = 0b00,
    /// Load — opc = 0b01
    Load = 0b01,
}

/// Register extend / index option for register-offset addressing.
///
/// Maps directly to the 3-bit `option` field in the encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegExtend {
    /// UXTW — option = 0b010
    Uxtw = 0b010,
    /// LSL (default, 64-bit) — option = 0b011
    Lsl = 0b011,
    /// SXTW — option = 0b110
    Sxtw = 0b110,
    /// SXTX — option = 0b111
    Sxtx = 0b111,
}

/// Load-pair vs store-pair selector.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PairOp {
    /// Store pair — L = 0
    StorePair = 0,
    /// Load pair — L = 1
    LoadPair = 1,
}

/// Data size for load/store pair instructions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PairSize {
    /// 32-bit (W registers) — opc = 0b00
    W32 = 0b00,
    /// 64-bit (X registers) — opc = 0b10
    X64 = 0b10,
}

/// Addressing mode for load/store pair instructions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PairMode {
    /// Post-index — mode = 0b01
    PostIndex = 0b01,
    /// Signed offset — mode = 0b10
    SignedOffset = 0b10,
    /// Pre-index — mode = 0b11
    PreIndex = 0b11,
}

// ── check_reg (encoding_mem.rs:110-116) — VERBATIM ─────────────────────────
#[inline]
fn check_reg(reg: u8, max: u8) -> Result<(), EncodeError> {
    if reg > max {
        return Err(EncodeError::RegisterOutOfRange { reg, max });
    }
    Ok(())
}

// ── check_imm12 (encoding_mem.rs:118-124) — VERBATIM ───────────────────────
#[inline]
fn check_imm12(value: u16) -> Result<(), EncodeError> {
    if value > 4095 {
        return Err(EncodeError::Imm12OutOfRange { value });
    }
    Ok(())
}

// ── check_imm9 (encoding_mem.rs:126-132) — VERBATIM except the MODELED
//    `contains` rewrite (see header) ─────────────────────────────────────────
#[inline]
fn check_imm9(value: i16) -> Result<(), EncodeError> {
    // MODELED: production `!(-256..=255).contains(&value)`.
    if value < -256 || value > 255 {
        return Err(EncodeError::Imm9OutOfRange { value });
    }
    Ok(())
}

// ── check_imm7 (encoding_mem.rs:134-140) — VERBATIM except the MODELED
//    `contains` rewrite (see header) ─────────────────────────────────────────
#[inline]
fn check_imm7(value: i8) -> Result<(), EncodeError> {
    // MODELED: production `!(-64..=63).contains(&value)`.
    if value < -64 || value > 63 {
        return Err(EncodeError::Imm7OutOfRange { value });
    }
    Ok(())
}

// ── encode_ldr_str_unsigned_offset (encoding_mem.rs:166-188) — VERBATIM
//    except `?` -> match (see header MODELED BOUNDARY) ────────────────────────
pub fn encode_ldr_str_unsigned_offset(
    size: LoadStoreSize,
    v: bool,
    op: LoadStoreOp,
    imm12: u16,
    rn: u8,
    rt: u8,
) -> Result<u32, EncodeError> {
    // MODELED: production `check_reg(rn, 31)?;` etc.
    match check_reg(rn, 31) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match check_reg(rt, 31) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match check_imm12(imm12) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }

    let mut inst: u32 = 0;
    inst |= (size as u32) << 30;
    inst |= 0b111 << 27;
    inst |= (v as u32) << 26;
    inst |= 0b01 << 24;
    inst |= (op as u32) << 22;
    inst |= (imm12 as u32) << 10;
    inst |= (rn as u32) << 5;
    inst |= rt as u32;
    Ok(inst)
}

// ── encode_ldr_str_pre_index (encoding_mem.rs:199-225) — VERBATIM except
//    `?` -> match (see header MODELED BOUNDARY) ─────────────────────────────
pub fn encode_ldr_str_pre_index(
    size: LoadStoreSize,
    v: bool,
    op: LoadStoreOp,
    imm9: i16,
    rn: u8,
    rt: u8,
) -> Result<u32, EncodeError> {
    // MODELED: production `check_reg(rn, 31)?;` etc.
    match check_reg(rn, 31) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match check_reg(rt, 31) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match check_imm9(imm9) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }

    let imm9_bits = (imm9 as u16 & 0x1FF) as u32;

    let mut inst: u32 = 0;
    inst |= (size as u32) << 30;
    inst |= 0b111 << 27;
    inst |= (v as u32) << 26;
    // bits [25:24] = 00 (unscaled/pre/post family)
    inst |= (op as u32) << 22;
    // bit [21] = 0 (not register offset)
    inst |= imm9_bits << 12;
    inst |= 0b11 << 10; // pre-index marker
    inst |= (rn as u32) << 5;
    inst |= rt as u32;
    Ok(inst)
}

// ── encode_ldr_str_post_index (encoding_mem.rs:236-260) — VERBATIM except
//    `?` -> match (see header MODELED BOUNDARY) ─────────────────────────────
pub fn encode_ldr_str_post_index(
    size: LoadStoreSize,
    v: bool,
    op: LoadStoreOp,
    imm9: i16,
    rn: u8,
    rt: u8,
) -> Result<u32, EncodeError> {
    // MODELED: production `check_reg(rn, 31)?;` etc.
    match check_reg(rn, 31) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match check_reg(rt, 31) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match check_imm9(imm9) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }

    let imm9_bits = (imm9 as u16 & 0x1FF) as u32;

    let mut inst: u32 = 0;
    inst |= (size as u32) << 30;
    inst |= 0b111 << 27;
    inst |= (v as u32) << 26;
    inst |= (op as u32) << 22;
    inst |= imm9_bits << 12;
    inst |= 0b01 << 10; // post-index marker
    inst |= (rn as u32) << 5;
    inst |= rt as u32;
    Ok(inst)
}

// ── encode_ldr_str_register (encoding_mem.rs:274-301) — VERBATIM except
//    `?` -> match (see header MODELED BOUNDARY) ─────────────────────────────
pub fn encode_ldr_str_register(
    size: LoadStoreSize,
    v: bool,
    op: LoadStoreOp,
    rm: u8,
    extend: RegExtend,
    shift: bool,
    rn: u8,
    rt: u8,
) -> Result<u32, EncodeError> {
    // MODELED: production `check_reg(rm, 31)?;` etc.
    match check_reg(rm, 31) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match check_reg(rn, 31) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match check_reg(rt, 31) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }

    let mut inst: u32 = 0;
    inst |= (size as u32) << 30;
    inst |= 0b111 << 27;
    inst |= (v as u32) << 26;
    inst |= (op as u32) << 22;
    inst |= 1 << 21; // register-offset marker
    inst |= (rm as u32) << 16;
    inst |= (extend as u32) << 13;
    inst |= (shift as u32) << 12;
    inst |= 0b10 << 10;
    inst |= (rn as u32) << 5;
    inst |= rt as u32;
    Ok(inst)
}

// ── encode_ldp_stp (encoding_mem.rs:321-349) — VERBATIM except `?` -> match
//    (see header MODELED BOUNDARY) ──────────────────────────────────────────
pub fn encode_ldp_stp(
    pair_size: PairSize,
    v: bool,
    pair_op: PairOp,
    mode: PairMode,
    imm7: i8,
    rt2: u8,
    rn: u8,
    rt: u8,
) -> Result<u32, EncodeError> {
    // MODELED: production `check_reg(rt, 31)?;` etc.
    match check_reg(rt, 31) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match check_reg(rt2, 31) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match check_reg(rn, 31) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match check_imm7(imm7) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }

    let imm7_bits = (imm7 as u8 & 0x7F) as u32;

    let mut inst: u32 = 0;
    inst |= (pair_size as u32) << 30;
    inst |= 0b101 << 27;
    inst |= (v as u32) << 26;
    inst |= (mode as u32) << 23;
    inst |= (pair_op as u32) << 22;
    inst |= imm7_bits << 15;
    inst |= (rt2 as u32) << 10;
    inst |= (rn as u32) << 5;
    inst |= rt as u32;
    Ok(inst)
}

// ── encode_ldp_stp_offset (encoding_mem.rs:352-371) — VERBATIM ──────────────
/// Convenience: encode `LDP`/`STP` with signed offset addressing.
pub fn encode_ldp_stp_offset(
    pair_size: PairSize,
    v: bool,
    pair_op: PairOp,
    imm7: i8,
    rt2: u8,
    rn: u8,
    rt: u8,
) -> Result<u32, EncodeError> {
    encode_ldp_stp(
        pair_size,
        v,
        pair_op,
        PairMode::SignedOffset,
        imm7,
        rt2,
        rn,
        rt,
    )
}

// ── encode_ldp_stp_pre_index (encoding_mem.rs:374-384) — VERBATIM ───────────
/// Convenience: encode `LDP`/`STP` with pre-index addressing.
pub fn encode_ldp_stp_pre_index(
    pair_size: PairSize,
    v: bool,
    pair_op: PairOp,
    imm7: i8,
    rt2: u8,
    rn: u8,
    rt: u8,
) -> Result<u32, EncodeError> {
    encode_ldp_stp(pair_size, v, pair_op, PairMode::PreIndex, imm7, rt2, rn, rt)
}

// ── encode_ldp_stp_post_index (encoding_mem.rs:387-406) — VERBATIM ──────────
/// Convenience: encode `LDP`/`STP` with post-index addressing.
pub fn encode_ldp_stp_post_index(
    pair_size: PairSize,
    v: bool,
    pair_op: PairOp,
    imm7: i8,
    rt2: u8,
    rn: u8,
    rt: u8,
) -> Result<u32, EncodeError> {
    encode_ldp_stp(
        pair_size,
        v,
        pair_op,
        PairMode::PostIndex,
        imm7,
        rt2,
        rn,
        rt,
    )
}

// ── encode_ldrsw_register (encoding_mem.rs:477-495) — VERBATIM except
//    `?` -> match (see header MODELED BOUNDARY) ─────────────────────────────
pub fn encode_ldrsw_register(rm: u8, rn: u8, rt: u8) -> Result<u32, EncodeError> {
    // MODELED: production `check_reg(rm, 31)?;` etc.
    match check_reg(rm, 31) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match check_reg(rn, 31) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match check_reg(rt, 31) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }

    let mut inst: u32 = 0;
    inst |= 0b10 << 30; // size = 10 (Word)
    inst |= 0b111 << 27; // load/store register class
    // V = 0 (bit 26 clear — GPR, not SIMD)
    inst |= 0b10 << 22; // opc = 10 (LDRSW)
    inst |= 1 << 21; // register-offset marker
    inst |= (rm as u32) << 16;
    inst |= 0b011 << 13; // option = LSL
    inst |= 1 << 12; // S = 1 (shift by access size = 2)
    inst |= 0b10 << 10;
    inst |= (rn as u32) << 5;
    inst |= rt as u32;
    Ok(inst)
}

// ── C-ABI keep-alive entry (one arm per emit root; the roots themselves are
//    the pub fns above, matched by --mir-emit-closure fnsubstr; bare
//    `encode_ldp_stp` is IN-MODULE in each wrapper's closure) ────────────────
#[no_mangle]
pub extern "C" fn t5_entry_memaddr(sel: u32) -> u32 {
    let r = match sel {
        0 => encode_ldr_str_unsigned_offset(
            LoadStoreSize::Double,
            false,
            LoadStoreOp::Load,
            1,
            1,
            0,
        ),
        1 => encode_ldr_str_pre_index(LoadStoreSize::Double, false, LoadStoreOp::Store, -16, 31, 0),
        2 => encode_ldr_str_post_index(LoadStoreSize::Double, false, LoadStoreOp::Load, 16, 31, 0),
        3 => encode_ldr_str_register(
            LoadStoreSize::Double,
            false,
            LoadStoreOp::Load,
            2,
            RegExtend::Lsl,
            true,
            1,
            0,
        ),
        4 => encode_ldrsw_register(1, 2, 0),
        5 => encode_ldp_stp_offset(PairSize::X64, false, PairOp::StorePair, 2, 1, 31, 0),
        6 => encode_ldp_stp_pre_index(PairSize::X64, false, PairOp::StorePair, -2, 1, 31, 0),
        _ => encode_ldp_stp_post_index(PairSize::X64, false, PairOp::LoadPair, 2, 1, 31, 0),
    };
    match r {
        Ok(w) => w,
        Err(_) => 0,
    }
}

fn main() {
    println!("{:#010X}", t5_entry_memaddr(0)); // 0xF9400420 (LDR X0, [X1, #8])
    println!("{:#010X}", t5_entry_memaddr(5)); // 0xA90107E0 (STP X0, X1, [SP, #16])
}
