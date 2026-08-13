// Trust-toolchain slice — the x86-64 machine-code FIELD BUILDERS: the REX
// prefix, the ModR/M byte, the SIB byte, and the disp32 range gate.
// Transcribed VERBATIM from
// trust-cg/crates/trust-cg-codegen/src/x86_64/encode.rs (working tree @ 58dac2f).
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 16,
// TRUST BATCH 6, part 1 of 3 — the x86-64 encoder core; the aarch64
// encoders were rounds 1/7, x86-64 is UNTOUCHED until now).
//
// WHY SOUNDNESS-CRITICAL: these four builders assemble the actual bytes
// x86-64 machine code is made of. Every register-to-register, register-to-
// memory, and scaled-index instruction the backend emits threads through
// them:
//   * `RexPrefix::encode` sets REX.W (64-bit operand size) and the R/X/B
//     high-register-extension bits — a wrong bit selects the WRONG register
//     (e.g. R8 decoded as RAX) or the wrong operand width;
//   * `ModRM::{reg_reg,ext_reg,indirect,indirect_disp8,indirect_disp32}` +
//     `encode` pack `[mod:2][reg:3][rm:3]` — a wrong field addresses the
//     wrong register or the wrong memory form;
//   * `Sib::{base_only,scaled}` + `encode` pack `[scale:2][index:3][base:3]`
//     for `[base + index*scale + disp]` — a wrong scale corrupts every array
//     access;
//   * `require_disp32` is the range gate that keeps a memory displacement
//     inside the 32-bit field the encoding physically has.
// A single wrong bit here is a silent miscompile of EVERY program the
// backend compiles for x86-64.
//
// TRANSCRIBED FROM (encode.rs; all VERBATIM including the bit constants):
//   * `require_disp32`                                       (67-74)   [B1]
//   * `RexPrefix` struct + `is_needed` + `encode`            (87-122)
//   * `ModRM` struct + 5 ctors + `encode`                    (131-191)
//   * `Sib` struct + `base_only` + `scaled` + `encode`       (203-249)
//
// EMIT: stage1 `trust_ir_mir --mir-emit-closure <root>` per the README
// recipe; `-C overflow-checks=off -C debug-assertions=off` (the shift/or
// field-packs cannot overflow in-domain — mode<=3, fields masked &0x7).
//
// MODELED BOUNDARIES:
//   [B1] `require_disp32` returns `Result<(), X86EncodeError>` in production
//        (the Err carries a `format!`-built diagnostic string). The slice
//        returns `bool` (`true` iff the disp fits disp32) — RESULT-IDENTICAL
//        for the range predicate that gates encoding; the message is
//        diagnostic-only and no encoder decision consumes it. The comparison
//        `disp < i32::MIN as i64 || disp > i32::MAX as i64` is VERBATIM
//        (`i64::from(i32::MIN)` written as `i32::MIN as i64` — the identity
//        widening). Dual-oracled against a naive in-range reference AND (for
//        the pub builders below) the LINKED PRODUCTION functions.
//   [B2] Roots pass the `RexPrefix` bool fields and the ModRM/SIB `u8` fields
//        as `u32` scalars, and dispatch the ctor family by a `form` selector
//        — the round-5 enum<->tag plumbing convention. The transcribed
//        builders themselves are UNMODIFIED.

// ── require_disp32 (encode.rs:67-74) ─────────────────────────────────────────
// [B1]: bool in place of Result<(), X86EncodeError>; true == fits disp32.
fn require_disp32(disp: i64) -> bool {
    if disp < i32::MIN as i64 || disp > i32::MAX as i64 {
        return false;
    }
    true
}

// ── RexPrefix (encode.rs:87-122) ─────────────────────────────────────────────
// REX prefix byte: `0100 WRXB`.
#[derive(Clone, Copy, Default)]
pub struct RexPrefix {
    /// REX.W: 64-bit operand size.
    pub w: bool,
    /// REX.R: ModR/M reg extension.
    pub r: bool,
    /// REX.X: SIB index extension.
    pub x: bool,
    /// REX.B: ModR/M r/m or opcode reg extension.
    pub b: bool,
}

impl RexPrefix {
    /// Returns true if a REX prefix is needed. (encode.rs:101-103, VERBATIM)
    pub fn is_needed(self) -> bool {
        self.w || self.r || self.x || self.b
    }

    /// Encode the REX prefix byte. (encode.rs:106-121, VERBATIM)
    pub fn encode(self) -> u8 {
        let mut byte: u8 = 0x40; // REX base
        if self.w {
            byte |= 0x08;
        }
        if self.r {
            byte |= 0x04;
        }
        if self.x {
            byte |= 0x02;
        }
        if self.b {
            byte |= 0x01;
        }
        byte
    }
}

// ── ModRM (encode.rs:131-191) ────────────────────────────────────────────────
// ModR/M byte layout: `[mod:2][reg:3][rm:3]`.
#[derive(Clone, Copy)]
pub struct ModRM {
    pub mode: u8,
    pub reg: u8,
    pub rm: u8,
}

impl ModRM {
    /// register-register ModR/M (mod=11). (encode.rs:143-149, VERBATIM)
    pub fn reg_reg(reg: u8, rm: u8) -> Self {
        Self {
            mode: 0b11,
            reg: reg & 0x7,
            rm: rm & 0x7,
        }
    }

    /// opcode extension with register operand (mod=11). (encode.rs:152-158)
    pub fn ext_reg(ext: u8, rm: u8) -> Self {
        Self {
            mode: 0b11,
            reg: ext & 0x7,
            rm: rm & 0x7,
        }
    }

    /// [base] addressing (mod=00), no displacement. (encode.rs:161-167)
    pub fn indirect(reg: u8, base: u8) -> Self {
        Self {
            mode: 0b00,
            reg: reg & 0x7,
            rm: base & 0x7,
        }
    }

    /// [base+disp8] addressing (mod=01). (encode.rs:170-176)
    pub fn indirect_disp8(reg: u8, base: u8) -> Self {
        Self {
            mode: 0b01,
            reg: reg & 0x7,
            rm: base & 0x7,
        }
    }

    /// [base+disp32] addressing (mod=10). (encode.rs:179-185)
    pub fn indirect_disp32(reg: u8, base: u8) -> Self {
        Self {
            mode: 0b10,
            reg: reg & 0x7,
            rm: base & 0x7,
        }
    }

    /// Encode the ModR/M byte. (encode.rs:188-190, VERBATIM)
    pub fn encode(self) -> u8 {
        (self.mode << 6) | (self.reg << 3) | self.rm
    }
}

// ── Sib (encode.rs:203-249) ──────────────────────────────────────────────────
// SIB byte layout: `[scale:2][index:3][base:3]`.
#[derive(Clone, Copy)]
pub struct Sib {
    pub scale: u8,
    pub index: u8,
    pub base: u8,
}

impl Sib {
    /// SIB for `[base]` only (no index, scale=0). (encode.rs:218-224, VERBATIM)
    pub fn base_only(base: u8) -> Self {
        Self {
            scale: 0,
            index: 0b100, // no index
            base: base & 0x7,
        }
    }

    /// SIB for `[base + index * scale]`. `scale_factor` in {1,2,4,8}.
    /// (encode.rs:230-243, VERBATIM incl. the fallback-to-scale=1 wildcard)
    pub fn scaled(base: u8, index: u8, scale_factor: u8) -> Self {
        let scale_bits = match scale_factor {
            1 => 0,
            2 => 1,
            4 => 2,
            8 => 3,
            _ => 0, // fallback to scale=1
        };
        Self {
            scale: scale_bits,
            index: index & 0x7,
            base: base & 0x7,
        }
    }

    /// Encode the SIB byte. (encode.rs:246-248, VERBATIM)
    pub fn encode(self) -> u8 {
        (self.scale << 6) | ((self.index & 0x7) << 3) | (self.base & 0x7)
    }
}

// ── out-PODs + #[no_mangle] mono ROOTS ───────────────────────────────────────

/// POD result for one REX field-set (is_needed + encoded byte).
#[repr(C)]
pub struct RexProps {
    pub is_needed: u32,
    pub encode: u32,
}

/// ROOT 1: build a RexPrefix from the four flag bits, return is_needed and
/// the encoded byte. Swept exhaustively over all 16 (w,r,x,b) combinations.
#[no_mangle]
pub fn x86_rex_root(w: u32, r: u32, x: u32, b: u32, out: &mut RexProps) {
    let rex = RexPrefix {
        w: w != 0,
        r: r != 0,
        x: x != 0,
        b: b != 0,
    };
    out.is_needed = rex.is_needed() as u32;
    out.encode = rex.encode() as u32;
}

/// ROOT 2: the ModR/M family. `form` selects the ctor (0=reg_reg,
/// 1=ext_reg, 2=indirect, 3=indirect_disp8, 4=indirect_disp32), then
/// `encode()` — exercising the `& 0x7` field masking and the per-ctor `mode`.
/// `form==5` bypasses the ctors and tests the raw `(mode<<6)|(reg<<3)|rm`
/// pack directly (x0=mode, x1=reg, x2=rm). Wildcard=reg_reg.
#[no_mangle]
pub fn x86_modrm_root(form: u32, x0: u32, x1: u32, x2: u32) -> u32 {
    let m = match form {
        0 => ModRM::reg_reg(x0 as u8, x1 as u8),
        1 => ModRM::ext_reg(x0 as u8, x1 as u8),
        2 => ModRM::indirect(x0 as u8, x1 as u8),
        3 => ModRM::indirect_disp8(x0 as u8, x1 as u8),
        4 => ModRM::indirect_disp32(x0 as u8, x1 as u8),
        5 => ModRM {
            mode: x0 as u8,
            reg: x1 as u8,
            rm: x2 as u8,
        },
        _ => ModRM::reg_reg(x0 as u8, x1 as u8),
    };
    m.encode() as u32
}

/// ROOT 3: the SIB family. `form` selects 0=base_only(x0), 1=scaled(x0,x1,x2)
/// then `encode()` (exercising the scale-factor decode + `& 0x7` masks);
/// `form==2` tests the raw `(scale<<6)|((index&7)<<3)|(base&7)` pack
/// (x0=scale, x1=index, x2=base). Wildcard=scaled.
#[no_mangle]
pub fn x86_sib_root(form: u32, x0: u32, x1: u32, x2: u32) -> u32 {
    let s = match form {
        0 => Sib::base_only(x0 as u8),
        2 => Sib {
            scale: x0 as u8,
            index: x1 as u8,
            base: x2 as u8,
        },
        _ => Sib::scaled(x0 as u8, x1 as u8, x2 as u8),
    };
    s.encode() as u32
}

/// ROOT 4: the disp32 range gate ([B1] bool form).
#[no_mangle]
pub fn x86_require_disp32_root(disp: i64) -> u32 {
    require_disp32(disp) as u32
}
