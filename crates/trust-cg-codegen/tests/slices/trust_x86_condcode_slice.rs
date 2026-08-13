// Trust-toolchain slice — the x86-64 CONDITION-CODE encoder predicates,
// transcribed VERBATIM from
// trust-cg/crates/trust-cg-ir/src/x86_64_ops.rs (working tree @ 58dac2f).
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 16,
// TRUST BATCH 6, part 2 of 3 — the x86-64 encoder core; the aarch64
// encoders were rounds 1/7, x86-64 is UNTOUCHED until now).
//
// WHY SOUNDNESS-CRITICAL: `X86CondCode::encoding` produces the 4-bit `tttn`
// field that is OR'd into every Jcc / SETcc / CMOVcc opcode byte in the
// x86-64 encoder (encode.rs `encode_instruction` Jcc arm: `0x80 | cc.encoding()`).
// A wrong encoding emits the WRONG conditional jump — the compiled program
// branches on the wrong flag and silently computes garbage. `invert` is used
// by branch-layout / if-conversion to flip a taken/not-taken sense
// (x86_if_convert.rs, cmp_branch_fusion): a wrong inversion inverts control
// flow. `is_signed` / `is_unsigned` classify the comparison family that ISel
// must preserve when it picks CMP vs TEST and signed vs unsigned Jcc.
//
// TRANSCRIBED FROM (x86_64_ops.rs; all VERBATIM including the discriminants):
//   * `X86CondCode` enum, O=0x0 .. G=0xF                    (1099-1133)
//   * `encoding`  (`self as u8`)                            (1137-1140)
//   * `invert`    (flip bit 0)                              (1145-1150)
//   * `is_signed`                                           (1175-1178)
//   * `is_unsigned`                                         (1181-1184)
//
// EMIT: stage1 `trust_ir_mir --mir-emit-closure x86_condcode_root` per the
// README recipe; `-C overflow-checks=off -C debug-assertions=off`.
//
// MODELED BOUNDARIES:
//   [B1] `as_str` / `Display` are OUT OF SCOPE (diagnostic-only &'static str;
//        no encoder decision consumes them).
//   [B2] `invert` — production is
//          `let inv = (self as u8) ^ 1;
//           unsafe { core::mem::transmute::<u8, X86CondCode>(inv) }`
//        The slice transcribes it as the RESULT-IDENTICAL 16-arm match
//        (transmute of a u8 in 0x0..=0xF back to the enum is the identity on
//        the discriminant — and the enum HAS a variant at every value
//        0x0..=0xF, so the transmute is total and exactly the bit-0 flip).
//        The equality `encoding(invert(cc)) == encoding(cc) ^ 1` is asserted
//        for all 16 codes against the LINKED PRODUCTION `invert` in the test,
//        so any drift in this modeling is caught by the dual oracle.
//   [B3] Roots expose the enum as a u32 `tag` (its 4-bit encoding) both in
//        and out — the round-5 [B2] enum<->tag plumbing convention. The
//        transcribed methods themselves are UNMODIFIED (modulo [B2]).

// ── X86CondCode (x86_64_ops.rs:1099-1133) ────────────────────────────────────
// repr(u8) with explicit discriminants: the discriminant IS the 4-bit HW code.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum X86CondCode {
    /// Overflow (OF=1)
    O = 0x0,
    /// No overflow (OF=0)
    NO = 0x1,
    /// Below / carry (CF=1) — unsigned less than
    B = 0x2,
    /// Above or equal / no carry (CF=0) — unsigned greater or equal
    AE = 0x3,
    /// Equal / zero (ZF=1)
    E = 0x4,
    /// Not equal / not zero (ZF=0)
    NE = 0x5,
    /// Below or equal (CF=1 or ZF=1) — unsigned less or equal
    BE = 0x6,
    /// Above (CF=0 and ZF=0) — unsigned greater
    A = 0x7,
    /// Sign / negative (SF=1)
    S = 0x8,
    /// No sign / positive (SF=0)
    NS = 0x9,
    /// Parity even (PF=1)
    P = 0xA,
    /// Parity odd (PF=0)
    NP = 0xB,
    /// Less than (SF!=OF) — signed less than
    L = 0xC,
    /// Greater or equal (SF=OF) — signed greater or equal
    GE = 0xD,
    /// Less or equal (ZF=1 or SF!=OF) — signed less or equal
    LE = 0xE,
    /// Greater (ZF=0 and SF=OF) — signed greater than
    G = 0xF,
}

impl X86CondCode {
    /// Return the 4-bit hardware encoding. (x86_64_ops.rs:1137-1140, VERBATIM)
    #[inline]
    pub const fn encoding(self) -> u8 {
        self as u8
    }

    /// Invert the condition (logical negation). Flipping bit 0 of the
    /// encoding inverts the condition. (x86_64_ops.rs:1145-1150 — [B2]:
    /// the production `transmute((self as u8) ^ 1)` written as the identical
    /// 16-arm match.)
    #[inline]
    pub const fn invert(self) -> Self {
        match self {
            Self::O => Self::NO,
            Self::NO => Self::O,
            Self::B => Self::AE,
            Self::AE => Self::B,
            Self::E => Self::NE,
            Self::NE => Self::E,
            Self::BE => Self::A,
            Self::A => Self::BE,
            Self::S => Self::NS,
            Self::NS => Self::S,
            Self::P => Self::NP,
            Self::NP => Self::P,
            Self::L => Self::GE,
            Self::GE => Self::L,
            Self::LE => Self::G,
            Self::G => Self::LE,
        }
    }

    /// Return `true` if this is a signed comparison condition.
    /// (x86_64_ops.rs:1175-1178, VERBATIM)
    #[inline]
    pub const fn is_signed(self) -> bool {
        matches!(self, Self::L | Self::GE | Self::LE | Self::G)
    }

    /// Return `true` if this is an unsigned comparison condition.
    /// (x86_64_ops.rs:1181-1184, VERBATIM)
    #[inline]
    pub const fn is_unsigned(self) -> bool {
        matches!(self, Self::B | Self::AE | Self::BE | Self::A)
    }
}

// ── [B3] enum<->tag plumbing ─────────────────────────────────────────────────

/// Total u8 -> X86CondCode decoder (tags 0x0..=0xF; wildcard is DEAD on the
/// swept 0..16 domain but present for totality — modeled after round-5
/// `class_of_tag`).
fn cc_from_tag(tag: u8) -> X86CondCode {
    match tag {
        0x0 => X86CondCode::O,
        0x1 => X86CondCode::NO,
        0x2 => X86CondCode::B,
        0x3 => X86CondCode::AE,
        0x4 => X86CondCode::E,
        0x5 => X86CondCode::NE,
        0x6 => X86CondCode::BE,
        0x7 => X86CondCode::A,
        0x8 => X86CondCode::S,
        0x9 => X86CondCode::NS,
        0xA => X86CondCode::P,
        0xB => X86CondCode::NP,
        0xC => X86CondCode::L,
        0xD => X86CondCode::GE,
        0xE => X86CondCode::LE,
        _ => X86CondCode::G,
    }
}

// ── out-POD + #[no_mangle] mono ROOT ─────────────────────────────────────────

/// POD result vector for one condition code (all scalar predicates).
#[repr(C)]
pub struct CcProps {
    pub encoding: u32,
    pub invert_tag: u32,
    pub is_signed: u32,
    pub is_unsigned: u32,
}

/// ROOT: the condition-code property vector — encoding, invert (as its
/// resulting 4-bit tag), is_signed, is_unsigned.
#[no_mangle]
pub fn x86_condcode_root(tag: u32, out: &mut CcProps) {
    let cc = cc_from_tag(tag as u8);
    out.encoding = cc.encoding() as u32;
    out.invert_tag = cc.invert().encoding() as u32;
    out.is_signed = cc.is_signed() as u32;
    out.is_unsigned = cc.is_unsigned() as u32;
}
