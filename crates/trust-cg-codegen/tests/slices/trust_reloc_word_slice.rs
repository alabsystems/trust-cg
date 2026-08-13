// Trust-toolchain slice — the Mach-O RELOCATION-RECORD word assembly +
// relocation-kind predicates, transcribed VERBATIM from
//   trust-cg/crates/trust-cg-codegen/src/macho/reloc.rs
//     AArch64RelocKind::is_pc_relative     (reloc.rs:86-94)
//     AArch64RelocKind::default_log2_size  (reloc.rs:100-105)
//     encode_relocation (r_word1 packing)  (reloc.rs:273-296)
//     decode_relocation (field extraction) (reloc.rs:316-350)
//   trust-cg/crates/trust-cg-codegen/src/macho/x86_64_reloc.rs
//     X86_64RelocKind::is_pc_relative      (x86_64_reloc.rs:79-84)
//     X86_64RelocKind::default_log2_size   (x86_64_reloc.rs:90-95)
//     encode_x86_64_relocation             (x86_64_reloc.rs:244-268)
//     decode_x86_64_relocation             (x86_64_reloc.rs:287-...)
//   trust-cg/crates/trust-cg-codegen/src/macho/fixup.rs
//     Fixup::needs_addend_reloc            (fixup.rs:256-262)
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 24, TRUST BATCH
// 11). This is the little-endian `relocation_info` r_word1 BITFIELD the LINKER
// consumes:
//   r_word1 = r_symbolnum[0:23] | r_pcrel[24] | r_length[25:26]
//           | r_extern[27] | r_type[28:31]
// A wrong bit here is a WRONG LINK: the symbol resolves to the wrong slot, the
// field width is wrong, or pc-relative vs absolute is flipped.
//
// EMIT: stage1 `trust_ir_mir --mir-emit-closure reloc_word_root` per the README
// recipe; `-C overflow-checks=off -C debug-assertions=off` (EXTERN-FREE).
//
// MODELED BOUNDARIES:
//   [B-scalarfields] production `encode_relocation` takes `&Relocation` and
//        returns `[u8;8]` via `copy_from_slice`; `decode_relocation` returns
//        `Result<Relocation, RelocDecodeError>`. Both are transcribed to
//        scalar-field-in / scalar-out form: the r_word1 PACKING and the field
//        EXTRACTION are byte-for-byte the production bit arithmetic. The encoded
//        [u8;8] is returned as the u64 `r_word0 | (r_word1 << 32)` — exactly the
//        little-endian byte layout (offset LE ++ r_word1 LE). The native oracle
//        drives the REAL linked `encode_relocation`/`decode_relocation` on real
//        `Relocation` structs and compares the 8 bytes + every decoded field.
//   [B-bool] production stores `pc_relative`/`is_extern` as `bool` and casts
//        `as u32` in the packing; transcribed taking the 0/1 u32 directly (the
//        cast result is bit-identical; the native oracle builds real-bool
//        `Relocation`s). Decode returns them as 0/1 u32 (production: `!= 0`).
//   [F3/const-shift] every shift amount + literal carries its operand type (u32)
//        per the trust-ir lhs==rhs validator rule; value-identical to production.
//   Both `AArch64RelocKind` (12 variants) and `X86_64RelocKind` (10 variants) are
//   `#[repr(u8)]` with < 128 variants, so NOT subject to F5 (the tag reads via
//   bitcast, not sext); `kind as u32` is the production enum->int discriminant.

// ── AArch64RelocKind (reloc.rs:23-79, VERBATIM #[repr(u8)] + discriminants) ────
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum AArch64RelocKind {
    Unsigned = 0,
    Subtractor = 1,
    Branch26 = 2,
    Page21 = 3,
    Pageoff12 = 4,
    GotLoadPage21 = 5,
    GotLoadPageoff12 = 6,
    PointerToGot = 7,
    TlvpLoadPage21 = 8,
    TlvpLoadPageoff12 = 9,
    Addend = 10,
    AuthenticatedPointer = 11,
}

impl AArch64RelocKind {
    // reloc.rs:86-94 VERBATIM
    fn is_pc_relative(self) -> bool {
        matches!(
            self,
            AArch64RelocKind::Branch26
                | AArch64RelocKind::Page21
                | AArch64RelocKind::GotLoadPage21
                | AArch64RelocKind::TlvpLoadPage21
        )
    }
    // reloc.rs:100-105 VERBATIM
    fn default_log2_size(self) -> u32 {
        match self {
            AArch64RelocKind::Unsigned => 3,
            _ => 2,
        }
    }
}

// aa_kind_from_tag: total tag<->variant plumbing (tag == discriminant).
fn aa_kind_from_tag(tag: u32) -> AArch64RelocKind {
    match tag {
        0 => AArch64RelocKind::Unsigned,
        1 => AArch64RelocKind::Subtractor,
        2 => AArch64RelocKind::Branch26,
        3 => AArch64RelocKind::Page21,
        4 => AArch64RelocKind::Pageoff12,
        5 => AArch64RelocKind::GotLoadPage21,
        6 => AArch64RelocKind::GotLoadPageoff12,
        7 => AArch64RelocKind::PointerToGot,
        8 => AArch64RelocKind::TlvpLoadPage21,
        9 => AArch64RelocKind::TlvpLoadPageoff12,
        10 => AArch64RelocKind::Addend,
        _ => AArch64RelocKind::AuthenticatedPointer,
    }
}

// ── X86_64RelocKind (x86_64_reloc.rs:24-72, VERBATIM #[repr(u8)]) ──────────────
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum X86_64RelocKind {
    Unsigned = 0,
    Signed = 1,
    Branch = 2,
    GotLoad = 3,
    Got = 4,
    Subtractor = 5,
    Signed1 = 6,
    Signed2 = 7,
    Signed4 = 8,
    Tlv = 9,
}

impl X86_64RelocKind {
    // x86_64_reloc.rs:79-84 VERBATIM
    fn is_pc_relative(self) -> bool {
        !matches!(
            self,
            X86_64RelocKind::Unsigned | X86_64RelocKind::Subtractor
        )
    }
    // x86_64_reloc.rs:90-95 VERBATIM
    fn default_log2_size(self) -> u32 {
        match self {
            X86_64RelocKind::Unsigned => 3,
            _ => 2,
        }
    }
}

fn x86_kind_from_tag(tag: u32) -> X86_64RelocKind {
    match tag {
        0 => X86_64RelocKind::Unsigned,
        1 => X86_64RelocKind::Signed,
        2 => X86_64RelocKind::Branch,
        3 => X86_64RelocKind::GotLoad,
        4 => X86_64RelocKind::Got,
        5 => X86_64RelocKind::Subtractor,
        6 => X86_64RelocKind::Signed1,
        7 => X86_64RelocKind::Signed2,
        8 => X86_64RelocKind::Signed4,
        _ => X86_64RelocKind::Tlv,
    }
}

// ── Fixup::needs_addend_reloc (fixup.rs:256-262, VERBATIM) ─────────────────────
// addend != 0 && kind in {Branch26, Page21, Pageoff12}.
fn needs_addend_reloc(kind: AArch64RelocKind, addend: i64) -> bool {
    addend != 0i64
        && matches!(
            kind,
            AArch64RelocKind::Branch26 | AArch64RelocKind::Page21 | AArch64RelocKind::Pageoff12
        )
}

// ── r_word1 packing (reloc.rs:285-290 / x86_64_reloc.rs:259-264, VERBATIM) ─────
// Returns the full 8-byte relocation record as the little-endian u64
// `r_word0 | (r_word1 << 32)` (= offset.to_le_bytes() ++ r_word1.to_le_bytes()).
fn pack_reloc_word(offset: u32, symbol_index: u32, pcrel: u32, length: u32, ext: u32, kind_val: u32) -> u64 {
    let r_word0 = offset;
    let r_word1 = (symbol_index & 0x00FF_FFFFu32)
        | (pcrel << 24u32)
        | (length << 25u32)
        | (ext << 27u32)
        | (kind_val << 28u32);
    (r_word0 as u64) | ((r_word1 as u64) << 32u32)
}

// ── POD out-vector ────────────────────────────────────────────────────────────
#[repr(C)]
pub struct RelocWordOut {
    pub enc_lo: u32,       // r_word0 (offset)
    pub enc_hi: u32,       // r_word1 (packed bitfield)
    pub is_pcrel: u32,     // kind.is_pc_relative()
    pub log2sz: u32,       // kind.default_log2_size()
    pub needs_addend: u32, // Fixup::needs_addend_reloc (aarch64) / 0 (x86)
    pub dec_sym: u32,      // decode(decw): symbol_index
    pub dec_pcrel: u32,    // decode: pc_relative (0/1)
    pub dec_len: u32,      // decode: length
    pub dec_ext: u32,      // decode: is_extern (0/1)
    pub dec_type: u32,     // decode: type_val
    pub dec_valid: u32,    // decode: 1 if type_val maps to a known kind else 0
}

// ── #[no_mangle] mono ROOT ────────────────────────────────────────────────────
/// ROOT: one call encodes ONE relocation record + decodes ONE r_word1 + queries
/// the kind predicates, for arch = 0 (aarch64) or 1 (x86-64).
///   (kind,off,sym,pcrel,len,ext) -> pack_reloc_word (enc_lo/enc_hi)
///   kind                         -> is_pc_relative / default_log2_size
///   (kind,addend)                -> needs_addend_reloc (aarch64 only)
///   decw                         -> decode field extraction + validity gate
#[no_mangle]
pub fn reloc_word_root(
    kind: u32,
    off: u32,
    sym: u32,
    pcrel: u32,
    len: u32,
    ext: u32,
    addend: i64,
    decw: u32,
    arch: u32,
    out: &mut RelocWordOut,
) {
    // Shared field extraction (identical bitfield on both arches).
    out.dec_sym = decw & 0x00FF_FFFFu32;
    out.dec_pcrel = (decw >> 24u32) & 1u32;
    out.dec_len = (decw >> 25u32) & 3u32;
    out.dec_ext = (decw >> 27u32) & 1u32;
    let type_val = (decw >> 28u32) & 0xFu32;
    out.dec_type = type_val;

    if arch == 0u32 {
        let k = aa_kind_from_tag(kind);
        out.enc_lo = off;
        out.enc_hi = (pack_reloc_word(off, sym, pcrel, len, ext, k as u32) >> 32u32) as u32;
        out.is_pcrel = if k.is_pc_relative() { 1u32 } else { 0u32 };
        out.log2sz = k.default_log2_size();
        out.needs_addend = if needs_addend_reloc(k, addend) { 1u32 } else { 0u32 };
        // decode validity: type_val in 0..=11 maps to a known AArch64RelocKind.
        out.dec_valid = if type_val <= 11u32 { 1u32 } else { 0u32 };
    } else {
        let k = x86_kind_from_tag(kind);
        out.enc_lo = off;
        out.enc_hi = (pack_reloc_word(off, sym, pcrel, len, ext, k as u32) >> 32u32) as u32;
        out.is_pcrel = if k.is_pc_relative() { 1u32 } else { 0u32 };
        out.log2sz = k.default_log2_size();
        out.needs_addend = 0u32;
        // decode validity: type_val in 0..=9 maps to a known X86_64RelocKind.
        out.dec_valid = if type_val <= 9u32 { 1u32 } else { 0u32 };
    }
}
