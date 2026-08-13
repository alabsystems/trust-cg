// Trust-toolchain slice — the x86-64 REGISTER-FILE predicates that DECIDE
// the encoder's register fields, transcribed VERBATIM from
// trust-cg/crates/trust-cg-ir/src/x86_64_regs.rs (working tree @ 58dac2f).
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 16,
// TRUST BATCH 6, part 3 of 3 — the x86-64 register file; the aarch64
// register file was round 5, x86-64 is UNTOUCHED until now).
//
// WHY SOUNDNESS-CRITICAL: these are the register inputs the x86-64 encoder
// and register allocators consult on EVERY instruction:
//   * `x86_hw_encoding` produces the 3-bit ModR/M reg/rm and SIB base/index
//     value AND (via `>= 8`) determines the REX.R/REX.X/REX.B extension bits
//     — a wrong answer emits the wrong physical register;
//   * `needs_rex` forces a bare REX for SPL/BPL/SIL/DIL and R8-R15 aliases —
//     without it AL..BH are selected instead of the intended byte regs;
//   * `x86_preg_class` (+ `size_bits`/`size_bytes`) classifies the operand
//     width the encoder must honour (REX.W / 0x66 prefix);
//   * `x86_is_callee_saved`/`x86_is_caller_saved` are the System V AMD64 ABI
//     clobber constraints;
//   * `x86_regs_overlap` (via `x86_reg_root`) IS the interference-aliasing
//     predicate — a false "no overlap" for RAX/EAX/AX/AL assigns two live
//     values to one physical register and silently corrupts data;
//   * `x86_reg_number` is the logical index within a class.
//
// TRANSCRIBED FROM (x86_64_regs.rs; all VERBATIM including range endpoints):
//   * `X86PReg` newtype + `new`/`encoding`/`is_gpr64..8`/`is_gpr`/`is_xmm`/
//     `is_system`/`hw_enc`/`needs_rex`/`reg_class`         (32-135)
//   * `X86RegClass` enum + `size_bits`/`size_bytes`        (154-189)
//   * `x86_preg_class`                                     (453-464)
//   * `x86_hw_encoding`                                    (470-480)
//   * `x86_is_callee_saved`                                (483-497)
//   * `x86_is_caller_saved`                                (500-515)
//   * `x86_regs_overlap` + `x86_reg_root`                  (542-565)
//   * `x86_reg_number`                                     (638-648)
//
// EMIT: stage1 `trust_ir_mir --mir-emit-closure <root>` per the README
// recipe; `-C overflow-checks=off -C debug-assertions=off` (every add/sub is
// range-guarded by its match arm).
//
// MODELED BOUNDARIES:
//   [B1] `x86_preg_name` + Debug/Display are OUT OF SCOPE (diagnostic-only
//        &'static str; no encoder/allocator decision consumes them).
//   [B2] Roots expose `X86RegClass` as a u32 tag and `Option<u8>` as
//        (present, value) out-params — the round-5 enum<->tag plumbing
//        convention. The transcribed predicates themselves are UNMODIFIED.

// ── X86PReg (x86_64_regs.rs:32-135) ──────────────────────────────────────────
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct X86PReg(u16);

impl X86PReg {
    #[inline]
    pub const fn new(encoding: u16) -> Self {
        Self(encoding)
    }

    #[inline]
    pub const fn encoding(self) -> u16 {
        self.0
    }

    #[inline]
    pub const fn is_gpr64(self) -> bool {
        self.0 <= 15
    }

    #[inline]
    pub const fn is_gpr32(self) -> bool {
        self.0 >= 16 && self.0 <= 31
    }

    #[inline]
    pub const fn is_gpr16(self) -> bool {
        self.0 >= 32 && self.0 <= 47
    }

    #[inline]
    pub const fn is_gpr8(self) -> bool {
        self.0 >= 48 && self.0 <= 63
    }

    #[inline]
    pub const fn is_gpr(self) -> bool {
        self.0 <= 63
    }

    #[inline]
    pub const fn is_xmm(self) -> bool {
        self.0 >= 64 && self.0 <= 79
    }

    #[inline]
    pub const fn is_system(self) -> bool {
        self.0 == 80 || self.0 == 81
    }

    /// Returns the 4-bit hardware encoding for this register.
    #[inline]
    pub fn hw_enc(self) -> u8 {
        x86_hw_encoding(self)
    }

    /// Returns true if accessing this register requires a REX prefix.
    /// (x86_64_regs.rs:113-128, VERBATIM)
    #[inline]
    pub fn needs_rex(self) -> bool {
        let e = self.0;
        match e {
            // GPR64: R8-R15 (encodings 8-15)
            8..=15 => true,
            // GPR32: R8D-R15D (encodings 24-31)
            24..=31 => true,
            // GPR16: R8W-R15W (encodings 40-47)
            40..=47 => true,
            // GPR8: R8B-R15B (encodings 56-63), plus SPL/BPL/SIL/DIL (52-55)
            52..=63 => true,
            // XMM8-XMM15 (encodings 72-79)
            72..=79 => true,
            _ => false,
        }
    }

    #[inline]
    pub fn reg_class(self) -> X86RegClass {
        x86_preg_class(self)
    }
}

// ── X86RegClass (x86_64_regs.rs:154-189) ─────────────────────────────────────
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum X86RegClass {
    Gpr64,
    Gpr32,
    Gpr16,
    Gpr8,
    Xmm128,
    System,
}

impl X86RegClass {
    #[inline]
    pub const fn size_bits(self) -> u32 {
        match self {
            Self::Gpr64 => 64,
            Self::Gpr32 => 32,
            Self::Gpr16 => 16,
            Self::Gpr8 => 8,
            Self::Xmm128 => 128,
            Self::System => 64,
        }
    }

    #[inline]
    pub const fn size_bytes(self) -> u32 {
        self.size_bits() / 8
    }
}

// ── free functions (x86_64_regs.rs) ──────────────────────────────────────────

/// x86_preg_class (453-464, VERBATIM)
pub fn x86_preg_class(reg: X86PReg) -> X86RegClass {
    let e = reg.encoding();
    match e {
        0..=15 => X86RegClass::Gpr64,
        16..=31 => X86RegClass::Gpr32,
        32..=47 => X86RegClass::Gpr16,
        48..=63 => X86RegClass::Gpr8,
        64..=79 => X86RegClass::Xmm128,
        80..=81 => X86RegClass::System,
        _ => X86RegClass::System,
    }
}

/// x86_hw_encoding (470-480, VERBATIM)
pub fn x86_hw_encoding(reg: X86PReg) -> u8 {
    let e = reg.encoding();
    match e {
        0..=15 => e as u8,         // GPR64: RAX=0 .. R15=15
        16..=31 => (e - 16) as u8, // GPR32: same numbering
        32..=47 => (e - 32) as u8, // GPR16: same numbering
        48..=63 => (e - 48) as u8, // GPR8: same numbering
        64..=79 => (e - 64) as u8, // XMM: 0-15
        _ => 0,
    }
}

/// x86_is_callee_saved (483-497, VERBATIM)
pub fn x86_is_callee_saved(reg: X86PReg) -> bool {
    let e = reg.encoding();
    match e {
        // GPR64: RBX=3, RBP=5, R12=12, R13=13, R14=14, R15=15
        3 | 5 | 12..=15 => true,
        // GPR32 aliases: EBX=19, EBP=21, R12D=28..R15D=31
        19 | 21 | 28..=31 => true,
        // GPR16 aliases: BX=35, BP=37, R12W=44..R15W=47
        35 | 37 | 44..=47 => true,
        // GPR8 aliases: BL=51, BPL=53, R12B=60..R15B=63
        51 | 53 | 60..=63 => true,
        // XMM registers are ALL caller-saved in System V (none callee-saved)
        _ => false,
    }
}

/// x86_is_caller_saved (500-515, VERBATIM)
pub fn x86_is_caller_saved(reg: X86PReg) -> bool {
    let e = reg.encoding();
    match e {
        // GPR64: RAX=0, RCX=1, RDX=2, RSI=6, RDI=7, R8-R11=8-11
        0..=2 | 6..=11 => true,
        // GPR32 aliases
        16..=18 | 22..=27 => true,
        // GPR16 aliases
        32..=34 | 38..=43 => true,
        // GPR8 aliases
        48..=50 | 54..=59 => true,
        // All XMM registers are caller-saved in System V
        64..=79 => true,
        _ => false,
    }
}

/// x86_regs_overlap (542-552, VERBATIM)
pub fn x86_regs_overlap(a: X86PReg, b: X86PReg) -> bool {
    if a == b {
        return true;
    }
    let a_root = x86_reg_root(a);
    let b_root = x86_reg_root(b);
    match (a_root, b_root) {
        (Some((num_a, group_a)), Some((num_b, group_b))) => num_a == num_b && group_a == group_b,
        _ => false,
    }
}

/// x86_reg_root (555-565, VERBATIM) — root register number + class group.
fn x86_reg_root(reg: X86PReg) -> Option<(u8, u8)> {
    let e = reg.encoding();
    match e {
        0..=15 => Some((e as u8, 0)),         // GPR64
        16..=31 => Some(((e - 16) as u8, 0)), // GPR32 aliases GPR64
        32..=47 => Some(((e - 32) as u8, 0)), // GPR16 aliases GPR64
        48..=63 => Some(((e - 48) as u8, 0)), // GPR8 aliases GPR64
        64..=79 => Some(((e - 64) as u8, 1)), // XMM
        _ => None,
    }
}

/// x86_reg_number (638-648, VERBATIM)
pub fn x86_reg_number(reg: X86PReg) -> Option<u8> {
    let e = reg.encoding();
    match e {
        0..=15 => Some(e as u8),         // GPR64
        16..=31 => Some((e - 16) as u8), // GPR32
        32..=47 => Some((e - 32) as u8), // GPR16
        48..=63 => Some((e - 48) as u8), // GPR8
        64..=79 => Some((e - 64) as u8), // XMM
        _ => None,
    }
}

// ── [B2] enum -> tag ─────────────────────────────────────────────────────────

fn class_tag(c: X86RegClass) -> u32 {
    match c {
        X86RegClass::Gpr64 => 0,
        X86RegClass::Gpr32 => 1,
        X86RegClass::Gpr16 => 2,
        X86RegClass::Gpr8 => 3,
        X86RegClass::Xmm128 => 4,
        X86RegClass::System => 5,
    }
}

// ── out-POD + #[no_mangle] mono ROOTS ────────────────────────────────────────

/// POD property vector for one x86-64 register encoding.
#[repr(C)]
pub struct X86RegProps {
    pub class_tag: u32,
    pub hw_enc: u32,
    pub needs_rex: u32,
    pub callee_saved: u32,
    pub caller_saved: u32,
    pub is_gpr: u32,
    pub is_xmm: u32,
    pub num_present: u32,
    pub num: u32,
    pub size_bits: u32,
    pub size_bytes: u32,
}

/// ROOT 1: the scalar register-file property vector.
#[no_mangle]
pub fn x86_regprops_root(e: u16, out: &mut X86RegProps) {
    let r = X86PReg::new(e);
    let c = x86_preg_class(r);
    out.class_tag = class_tag(c);
    out.hw_enc = x86_hw_encoding(r) as u32;
    out.needs_rex = r.needs_rex() as u32;
    out.callee_saved = x86_is_callee_saved(r) as u32;
    out.caller_saved = x86_is_caller_saved(r) as u32;
    out.is_gpr = r.is_gpr() as u32;
    out.is_xmm = r.is_xmm() as u32;
    match x86_reg_number(r) {
        Some(n) => {
            out.num_present = 1;
            out.num = n as u32;
        }
        None => {
            out.num_present = 0;
            out.num = 0;
        }
    }
    out.size_bits = c.size_bits();
    out.size_bytes = c.size_bytes();
}

/// ROOT 2: the interference-aliasing predicate (regs_overlap ∘ reg_root,
/// incl. the derived X86PReg PartialEq fast path).
#[no_mangle]
pub fn x86_regoverlap_root(a: u16, b: u16) -> u32 {
    x86_regs_overlap(X86PReg::new(a), X86PReg::new(b)) as u32
}
