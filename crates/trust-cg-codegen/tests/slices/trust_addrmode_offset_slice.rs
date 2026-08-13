// Trust-toolchain slice — the AArch64 ADDRESSING-MODE OFFSET LEGALITY
// deciders, transcribed VERBATIM from
// trust-cg/crates/trust-cg-opt/src/addr_mode.rs (working tree @ 8e48d2e):
//   * `is_encodable_offset`           (163-174, pub)
//   * `is_encodable_pre_post_offset`  (180-182, pub)
//   * `is_encodable_store_pair_offset`(493-495, private)
//   * `is_encodable_generic64_offset` (669-671, private)
//   * `is_foldable_offset` + `OffsetEncoding`  (108-114, 662-667, private)
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 20,
// TRUST BATCH 7, part 2 of 2 — the OPTIMIZATION / ANALYSIS PREDICATE layer).
//
// WHY SOUNDNESS-CRITICAL: the AddrModeFormation pass folds an `ADD base, imm`
// into a following LDR/STR's addressing mode ONLY IF the combined offset is
// encodable in the target's immediate form. These predicates ARE that legality
// gate (`is_foldable_offset` guards `form_base_plus_imm`, addr_mode.rs:707):
//   * `is_encodable_offset(off, sz)` — AArch64 LDR/STR unsigned scaled imm12:
//     `off >= 0`, `off` aligned to the access size, `off/sz <= 4095`. A false
//     positive folds an unencodable offset and emits a WRONG or unassemblable
//     instruction (silent address corruption);
//   * `is_encodable_pre_post_offset(off)` — the signed 9-bit unscaled
//     pre/post-index range -256..=255;
//   * `is_encodable_store_pair_offset(off)` — STP scaled signed imm7
//     (`off%8==0` and `off/8` in -64..=63);
//   * `is_encodable_generic64_offset` / `is_foldable_offset` — the policy
//     dispatch the pass actually calls.
//
// EMIT: stage1 `trust_ir_mir --mir-emit-closure offset_props_root` per the
// README recipe; `-C overflow-checks=off -C debug-assertions=off`.
//
// MODELED BOUNDARIES:
//   [B1] Production `is_encodable_pre_post_offset` is
//        `(-256..=255).contains(&offset)` and `is_encodable_store_pair_offset`
//        uses `(-64..=63).contains(&(offset/8))`. The trust-ir MIR frontend
//        cannot lower `RangeInclusive::contains` — the range literal lowers to
//        a const aggregate and the compare asserts a single scalar ("constant
//        value not a single scalar"; owner-item #6, known-open, re-confirmed
//        this round with a 1-line repro). `(lo..=hi).contains(&x)` is
//        DEFINITIONALLY `x >= lo && x <= hi`, transcribed here as that
//        RESULT-IDENTICAL comparison. The dual oracle links the real
//        `.contains`-based `is_encodable_pre_post_offset` so drift is caught;
//        `is_encodable_store_pair_offset` is private (verified against a naive
//        semantic reference, R16 `require_disp32` discipline).
//   [B2] `is_foldable_offset`'s `OffsetEncoding` is fed to the root as an
//        (enc_tag, access_size) pair and reconstructed in-module; the
//        transcribed predicate body is UNMODIFIED (it DOES construct and match
//        the real `OffsetEncoding::ScaledUnsigned(u8)` payload enum in JIT
//        machine code). `is_encodable_store_pair_offset` /
//        `is_encodable_generic64_offset` / `is_foldable_offset` are private —
//        verified by verbatim transcription + naive reference (no linked
//        dual oracle); `is_encodable_offset` / `is_encodable_pre_post_offset`
//        are pub and dual-oracled.

// ── OffsetEncoding (addr_mode.rs:108-114, VERBATIM) ──────────────────────────
#[derive(Clone, Copy)]
enum OffsetEncoding {
    /// Generic scalar LDR/STR fold policy for existing 64-bit memory ops.
    Generic64,
    /// AArch64 unsigned scaled immediate with this access size in bytes.
    ScaledUnsigned(u8),
}

// ── the legality deciders ────────────────────────────────────────────────────

/// is_encodable_offset (addr_mode.rs:163-174, VERBATIM)
pub fn is_encodable_offset(offset: i64, access_size: u8) -> bool {
    if offset < 0 {
        return false;
    }
    match access_size {
        1 | 2 | 4 | 8 => {
            let scale = access_size as i64;
            offset % scale == 0 && offset / scale <= 4095
        }
        _ => false,
    }
}

/// is_encodable_pre_post_offset (addr_mode.rs:180-182).
/// Production: `(-256..=255).contains(&offset)`. See [B1].
pub fn is_encodable_pre_post_offset(offset: i64) -> bool {
    offset >= -256 && offset <= 255
}

/// is_encodable_store_pair_offset (addr_mode.rs:493-495).
/// Production: `offset % 8 == 0 && (-64..=63).contains(&(offset / 8))`. [B1]
fn is_encodable_store_pair_offset(offset: i64) -> bool {
    offset % 8 == 0 && {
        let q = offset / 8;
        q >= -64 && q <= 63
    }
}

/// is_encodable_generic64_offset (addr_mode.rs:669-671, VERBATIM)
fn is_encodable_generic64_offset(offset: i64) -> bool {
    is_encodable_offset(offset, 8) || is_encodable_pre_post_offset(offset)
}

/// is_foldable_offset (addr_mode.rs:662-667, VERBATIM)
fn is_foldable_offset(offset: i64, encoding: OffsetEncoding) -> bool {
    match encoding {
        OffsetEncoding::Generic64 => is_encodable_generic64_offset(offset),
        OffsetEncoding::ScaledUnsigned(access_size) => is_encodable_offset(offset, access_size),
    }
}

// ── out-POD + #[no_mangle] mono ROOT ─────────────────────────────────────────

#[repr(C)]
pub struct OffsetProps {
    pub enc_offset_1: u32,
    pub enc_offset_2: u32,
    pub enc_offset_4: u32,
    pub enc_offset_8: u32,
    pub enc_offset_as: u32,
    pub pre_post: u32,
    pub store_pair: u32,
    pub generic64: u32,
    pub foldable_generic64: u32,
    pub foldable_scaled_as: u32,
}

/// ROOT: sweep one (offset, access_size) through every offset legality
/// decider. `access_size` is the swept access size (as u8) for the
/// arbitrary-size and ScaledUnsigned paths.
#[no_mangle]
pub fn offset_props_root(offset: i64, access_size: u32, out: &mut OffsetProps) {
    let asz = access_size as u8;
    out.enc_offset_1 = is_encodable_offset(offset, 1) as u32;
    out.enc_offset_2 = is_encodable_offset(offset, 2) as u32;
    out.enc_offset_4 = is_encodable_offset(offset, 4) as u32;
    out.enc_offset_8 = is_encodable_offset(offset, 8) as u32;
    out.enc_offset_as = is_encodable_offset(offset, asz) as u32;
    out.pre_post = is_encodable_pre_post_offset(offset) as u32;
    out.store_pair = is_encodable_store_pair_offset(offset) as u32;
    out.generic64 = is_encodable_generic64_offset(offset) as u32;
    out.foldable_generic64 = is_foldable_offset(offset, OffsetEncoding::Generic64) as u32;
    out.foldable_scaled_as =
        is_foldable_offset(offset, OffsetEncoding::ScaledUnsigned(asz)) as u32;
}
