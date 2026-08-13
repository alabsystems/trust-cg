// Trust-toolchain slice — the AArch64 REGISTER-FILE predicates that the
// register allocators consult, transcribed from
// trust-cg/crates/trust-cg-ir/src/aarch64_regs.rs (trust-cg rev 00ae28c,
// re-checked against the working tree on 2026-07-03).
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 5:
// regalloc predicates batch, part 1 of 2).
//
// WHY SOUNDNESS-CRITICAL: these are the ground-truth predicates the
// register allocators (greedy.rs, linear_scan.rs) and frame lowering
// consult on EVERY allocation decision:
//   * `regs_overlap` (via greedy.rs:144 `allocator_pregs_overlap`) IS the
//     aarch64 interference-aliasing predicate — if it wrongly reports
//     "no overlap" for X0/W0 or V0/D0/S0, the allocator assigns two live
//     values to the same physical storage and silently corrupts data;
//   * `preg_class` / `hw_encoding` decide the 5-bit register fields that
//     reach machine code (SP and XZR both encode 31 — context decides);
//   * `is_callee_saved` / `is_caller_saved` are the AAPCS64 clobber
//     constraints — a wrong answer either corrupts a caller's live value
//     across a call or breaks the platform ABI;
//   * the width-alias converters (`gpr64_to_gpr32` & co.) implement the
//     X<->W / V<->D<->S<->H<->B aliasing model used when allocating mixed
//     widths onto one register file.
//
// TRANSCRIBED FROM (aarch64_regs.rs; all VERBATIM including range endpoints):
//   * `PReg` newtype + `new`/`encoding`/`is_gpr`/`is_fpr`  (lines 36-78)
//   * `RegClass` enum + `size_bits`/`size_bytes`           (lines 97-138)
//   * consts SP=31, WSP=63, XZR=160, WZR=161               (178/221/339/341)
//   * `preg_class`                                          (587-602)
//   * `hw_encoding`                                         (608-633)
//   * `is_callee_saved`                                     (636-651)
//   * `is_caller_saved`                                     (654-669)
//   * `gpr64_to_gpr32` / `gpr32_to_gpr64`                   (675-702)
//   * `fpr128_to_fpr64` / `_fpr32` / `_fpr16` / `_fpr8`     (705-738)
//   * `fpr64_to_fpr128` / `fpr32_to_fpr128`                 (741-756)
//   * `reg_number`                                          (762-778)
//   * `regs_overlap` + `reg_root`                           (783-813)
//
// EMIT: stage1 `trust_ir_mir --mir-emit-closure <root>` per the README
// recipe; `-C overflow-checks=off -C debug-assertions=off` for parity with
// the other Trust-self slices (no arithmetic here can overflow in-domain:
// every add/sub is range-guarded by its match arm).
//
// MODELED BOUNDARIES:
//   [B1] `preg_name` (and the Debug/Display impls that call it) is OUT OF
//        SCOPE: it returns `&'static str` from const name tables and is
//        diagnostic-only — no allocator decision consumes it. The derives
//        kept on `PReg`/`RegClass` below match production; only the fns in
//        the emit closure are verified.
//   [B2] Roots expose enums as u32 tags (`class_tag`) and Option<PReg> as
//        (present, encoding) out-params — harness plumbing mirrored 1:1 in
//        the test oracles, exactly the established round-2/3/4 convention.
//        The transcribed predicates themselves are UNMODIFIED except [B3].
//   [B3] REWRITE `Some(WSP)`/`Some(SP)`/`Some(WZR)`/`Some(XZR)` ->
//        `Some(PReg(63))`/`Some(PReg(31))`/`Some(PReg(161))`/`Some(PReg(160))`
//        in the two GPR converters: referencing a CONST STRUCT ITEM as an
//        aggregate-field operand does not lower ("aggregate field operand
//        is not a place (constant aggregate field): struct-adt" — the known
//        const-aggregate frontend gap, owner item #6 class; observed on
//        this slice 2026-07-03). The rewrite inlines the const's VALUE
//        (aarch64_regs.rs:178/221/339/341 define SP=PReg(31), WSP=PReg(63),
//        XZR=PReg(160), WZR=PReg(161)) — definitionally identical, and the
//        differential sweeps hit all four arms (e=31, 63, 160, 161).
//
// No other rewrites: every other fn body below is byte-for-byte the
// production text (modulo rustfmt-stable whitespace).

#![allow(dead_code)]
#![allow(clippy::all)]

// ── PReg (aarch64_regs.rs:36-78) ────────────────────────────────────────────

/// aarch64_regs.rs:36-37, VERBATIM (Debug impl dropped — [B1]).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PReg(u16);

impl PReg {
    /// aarch64_regs.rs:42-44, VERBATIM.
    #[inline]
    pub const fn new(encoding: u16) -> Self {
        Self(encoding)
    }

    /// aarch64_regs.rs:48-50, VERBATIM.
    #[inline]
    pub const fn encoding(self) -> u16 {
        self.0
    }

    /// aarch64_regs.rs:54-56, VERBATIM.
    #[inline]
    pub const fn is_gpr(self) -> bool {
        self.0 <= 31
    }

    /// aarch64_regs.rs `PReg::is_fpr`, VERBATIM (re-checked 2026-07-20: the
    /// special registers 160..=164 — XZR/WZR/NZCV/FPCR/FPSR — are NOT FPRs;
    /// the old `>= 64 && <= 228` span misclassified them).
    #[inline]
    pub const fn is_fpr(self) -> bool {
        matches!(self.0, 64..=159 | 165..=228)
    }
}

// ── RegClass (aarch64_regs.rs:97-138) ───────────────────────────────────────

/// aarch64_regs.rs:97-115, VERBATIM variant set + order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum RegClass {
    Gpr64,
    Gpr32,
    Fpr128,
    Fpr64,
    Fpr32,
    Fpr16,
    Fpr8,
    System,
}

impl RegClass {
    /// aarch64_regs.rs:120-131, VERBATIM.
    #[inline]
    pub const fn size_bits(self) -> u32 {
        match self {
            Self::Gpr64 => 64,
            Self::Gpr32 => 32,
            Self::Fpr128 => 128,
            Self::Fpr64 => 64,
            Self::Fpr32 => 32,
            Self::Fpr16 => 16,
            Self::Fpr8 => 8,
            Self::System => 32,
        }
    }

    /// aarch64_regs.rs:135-137, VERBATIM.
    #[inline]
    pub const fn size_bytes(self) -> u32 {
        self.size_bits() / 8
    }
}

// ── the special-register consts the converters return ──────────────────────

pub const SP: PReg = PReg(31); // aarch64_regs.rs:178
pub const WSP: PReg = PReg(63); // aarch64_regs.rs:221
pub const XZR: PReg = PReg(160); // aarch64_regs.rs:339
pub const WZR: PReg = PReg(161); // aarch64_regs.rs:341

// ── the predicates (aarch64_regs.rs:587-813), all VERBATIM ─────────────────

/// aarch64_regs.rs:587-602, VERBATIM.
pub fn preg_class(reg: PReg) -> RegClass {
    let e = reg.encoding();
    match e {
        0..=31 => RegClass::Gpr64,
        32..=63 => RegClass::Gpr32,
        64..=95 => RegClass::Fpr128,
        96..=127 => RegClass::Fpr64,
        128..=159 => RegClass::Fpr32,
        160 => RegClass::Gpr64, // XZR is a GPR64
        161 => RegClass::Gpr32, // WZR is a GPR32
        162..=164 => RegClass::System,
        165..=196 => RegClass::Fpr16,
        197..=228 => RegClass::Fpr8,
        _ => RegClass::System,
    }
}

/// aarch64_regs.rs:608-633, VERBATIM.
pub fn hw_encoding(reg: PReg) -> u8 {
    let e = reg.encoding();
    match e {
        // GPR64: X0-X30 encode as 0-30, SP encodes as 31
        0..=31 => e as u8,
        // GPR32: W0-W30 encode as 0-30, WSP encodes as 31
        32..=63 => (e - 32) as u8,
        // FPR128: V0-V31 encode as 0-31
        64..=95 => (e - 64) as u8,
        // FPR64: D0-D31 encode as 0-31
        96..=127 => (e - 96) as u8,
        // FPR32: S0-S31 encode as 0-31
        128..=159 => (e - 128) as u8,
        // XZR encodes as 31
        160 => 31,
        // WZR encodes as 31
        161 => 31,
        // System regs — not directly encodable in GPR/FPR fields
        162..=164 => 0,
        // FPR16: H0-H31 encode as 0-31
        165..=196 => (e - 165) as u8,
        // FPR8: B0-B31 encode as 0-31
        197..=228 => (e - 197) as u8,
        _ => 0,
    }
}

/// aarch64_regs.rs:636-651, VERBATIM.
pub fn is_callee_saved(reg: PReg) -> bool {
    let e = reg.encoding();
    match e {
        // GPR64: X19-X28 are callee-saved
        19..=28 => true,
        // GPR32: W19-W28 are callee-saved (aliases of X19-X28)
        51..=60 => true,
        // FPR128: V8-V15 are callee-saved (lower 64 bits)
        72..=79 => true,
        // FPR64: D8-D15 are callee-saved
        104..=111 => true,
        // FPR32: S8-S15 are callee-saved (subset of V8-V15)
        136..=143 => true,
        _ => false,
    }
}

/// aarch64_regs.rs:654-669, VERBATIM.
pub fn is_caller_saved(reg: PReg) -> bool {
    let e = reg.encoding();
    match e {
        // GPR64: X0-X15 (excluding X8 IP, X16-X17 are scratch but special)
        0..=7 | 9..=15 => true,
        // GPR32: corresponding W registers
        32..=39 | 41..=47 => true,
        // FPR128: V0-V7, V16-V31
        64..=71 | 80..=95 => true,
        // FPR64: D0-D7, D16-D31
        96..=103 | 112..=127 => true,
        // FPR32: S0-S7, S16-S31
        128..=135 | 144..=159 => true,
        _ => false,
    }
}

/// aarch64_regs.rs:675-686, VERBATIM.
pub fn gpr64_to_gpr32(reg: PReg) -> Option<PReg> {
    let e = reg.encoding();
    match e {
        // X0-X30 → W0-W30
        0..=30 => Some(PReg(e + 32)),
        // SP → WSP
        31 => Some(PReg(63)), // [B3] production: Some(WSP)
        // XZR → WZR
        160 => Some(PReg(161)), // [B3] production: Some(WZR)
        _ => None,
    }
}

/// aarch64_regs.rs:691-702, VERBATIM.
pub fn gpr32_to_gpr64(reg: PReg) -> Option<PReg> {
    let e = reg.encoding();
    match e {
        // W0-W30 → X0-X30
        32..=62 => Some(PReg(e - 32)),
        // WSP → SP
        63 => Some(PReg(31)), // [B3] production: Some(SP)
        // WZR → XZR
        161 => Some(PReg(160)), // [B3] production: Some(XZR)
        _ => None,
    }
}

/// aarch64_regs.rs:705-711, VERBATIM.
pub fn fpr128_to_fpr64(reg: PReg) -> Option<PReg> {
    let e = reg.encoding();
    match e {
        64..=95 => Some(PReg(e + 32)),
        _ => None,
    }
}

/// aarch64_regs.rs:714-720, VERBATIM.
pub fn fpr128_to_fpr32(reg: PReg) -> Option<PReg> {
    let e = reg.encoding();
    match e {
        64..=95 => Some(PReg(e + 64)),
        _ => None,
    }
}

/// aarch64_regs.rs:723-729, VERBATIM.
pub fn fpr128_to_fpr16(reg: PReg) -> Option<PReg> {
    let e = reg.encoding();
    match e {
        64..=95 => Some(PReg(e + 101)),
        _ => None,
    }
}

/// aarch64_regs.rs:732-738, VERBATIM.
pub fn fpr128_to_fpr8(reg: PReg) -> Option<PReg> {
    let e = reg.encoding();
    match e {
        64..=95 => Some(PReg(e + 133)),
        _ => None,
    }
}

/// aarch64_regs.rs:741-747, VERBATIM.
pub fn fpr64_to_fpr128(reg: PReg) -> Option<PReg> {
    let e = reg.encoding();
    match e {
        96..=127 => Some(PReg(e - 32)),
        _ => None,
    }
}

/// aarch64_regs.rs:750-756, VERBATIM.
pub fn fpr32_to_fpr128(reg: PReg) -> Option<PReg> {
    let e = reg.encoding();
    match e {
        128..=159 => Some(PReg(e - 64)),
        _ => None,
    }
}

/// aarch64_regs.rs:762-778, VERBATIM.
pub fn reg_number(reg: PReg) -> Option<u8> {
    let e = reg.encoding();
    match e {
        0..=30 => Some(e as u8),            // X0-X30
        31 => Some(31),                     // SP
        32..=62 => Some((e - 32) as u8),    // W0-W30
        63 => Some(31),                     // WSP
        64..=95 => Some((e - 64) as u8),    // V0-V31
        96..=127 => Some((e - 96) as u8),   // D0-D31
        128..=159 => Some((e - 128) as u8), // S0-S31
        160 => Some(31),                    // XZR
        161 => Some(31),                    // WZR
        165..=196 => Some((e - 165) as u8), // H0-H31
        197..=228 => Some((e - 197) as u8), // B0-B31
        _ => None,
    }
}

/// aarch64_regs.rs:783-796, VERBATIM (incl. the derived `PReg` PartialEq
/// short-circuit — the derive is crate-local and lowers into the module).
pub fn regs_overlap(a: PReg, b: PReg) -> bool {
    if a == b {
        return true;
    }

    // Get the "root" register number and class group for each
    let a_root = reg_root(a);
    let b_root = reg_root(b);

    match (a_root, b_root) {
        (Some((num_a, group_a)), Some((num_b, group_b))) => num_a == num_b && group_a == group_b,
        _ => false,
    }
}

/// aarch64_regs.rs:799-813, VERBATIM.
fn reg_root(reg: PReg) -> Option<(u8, u8)> {
    let e = reg.encoding();
    match e {
        0..=31 => Some((e as u8, 0)),            // GPR64
        32..=63 => Some(((e - 32) as u8, 0)),    // GPR32 aliases GPR64
        64..=95 => Some(((e - 64) as u8, 1)),    // FPR128
        96..=127 => Some(((e - 96) as u8, 1)),   // FPR64 aliases FPR128
        128..=159 => Some(((e - 128) as u8, 1)), // FPR32 aliases FPR128
        160 => Some((31, 0)),                    // XZR aliases GPR group
        161 => Some((31, 0)),                    // WZR aliases GPR group
        165..=196 => Some(((e - 165) as u8, 1)), // FPR16 aliases FPR128
        197..=228 => Some(((e - 197) as u8, 1)), // FPR8 aliases FPR128
        _ => None,
    }
}

// ── [B2] harness plumbing: enum -> tag (mirrored 1:1 in the test oracles) ──

fn class_tag(c: RegClass) -> u32 {
    match c {
        RegClass::Gpr64 => 0,
        RegClass::Gpr32 => 1,
        RegClass::Fpr128 => 2,
        RegClass::Fpr64 => 3,
        RegClass::Fpr32 => 4,
        RegClass::Fpr16 => 5,
        RegClass::Fpr8 => 6,
        RegClass::System => 7,
    }
}

// ── out-POD + #[no_mangle] mono ROOTS ───────────────────────────────────────

/// POD property vector for one register encoding (all scalar predicates).
#[repr(C)]
pub struct RegProps {
    pub class_tag: u32,
    pub hw_enc: u32,
    pub callee_saved: u32,
    pub caller_saved: u32,
    pub is_gpr: u32,
    pub is_fpr: u32,
    pub num_present: u32,
    pub num: u32,
    pub size_bits: u32,
    pub size_bytes: u32,
}

/// ROOT 1: the scalar property vector — preg_class, hw_encoding,
/// is_callee_saved, is_caller_saved, PReg::is_gpr/is_fpr, reg_number,
/// and RegClass::size_bits/size_bytes (of the classified class).
#[no_mangle]
pub fn regfile_props_root(e: u16, out: &mut RegProps) {
    let r = PReg::new(e);
    let c = preg_class(r);
    out.class_tag = class_tag(c);
    out.hw_enc = hw_encoding(r) as u32;
    out.callee_saved = is_callee_saved(r) as u32;
    out.caller_saved = is_caller_saved(r) as u32;
    out.is_gpr = r.is_gpr() as u32;
    out.is_fpr = r.is_fpr() as u32;
    match reg_number(r) {
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

/// ROOT 2: the width-alias converter family, dispatched by `kind`
/// (0=gpr64_to_gpr32, 1=gpr32_to_gpr64, 2=fpr128_to_fpr64, 3=fpr128_to_fpr32,
///  4=fpr128_to_fpr16, 5=fpr128_to_fpr8, 6=fpr64_to_fpr128,
///  wildcard=fpr32_to_fpr128) — the binop_from_u32-style total decoder [B2].
#[no_mangle]
pub fn regfile_alias_root(kind: u32, e: u16, out_present: &mut u32, out_enc: &mut u32) {
    let r = PReg::new(e);
    let res = match kind {
        0 => gpr64_to_gpr32(r),
        1 => gpr32_to_gpr64(r),
        2 => fpr128_to_fpr64(r),
        3 => fpr128_to_fpr32(r),
        4 => fpr128_to_fpr16(r),
        5 => fpr128_to_fpr8(r),
        6 => fpr64_to_fpr128(r),
        _ => fpr32_to_fpr128(r),
    };
    match res {
        Some(p) => {
            *out_present = 1;
            *out_enc = p.encoding() as u32;
        }
        None => {
            *out_present = 0;
            *out_enc = 0;
        }
    }
}

/// ROOT 3: the interference-aliasing predicate (regs_overlap ∘ reg_root,
/// incl. the derived PReg PartialEq fast path).
#[no_mangle]
pub fn regfile_overlap_root(a: u16, b: u16) -> u32 {
    regs_overlap(PReg::new(a), PReg::new(b)) as u32
}

fn main() {}
