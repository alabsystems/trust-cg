// trust-cg-codegen — ENC-3: x86-64 instantiation of the decode-check gate
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// An INDEPENDENT, clean-room x86-64 instruction decoder + a structural
// intent-renderer, wired into the arch-neutral [`crate::decode_check`] gate.
// After the trusted byte emitter (`x86_64/encode.rs`) produces the bytes for a
// function, the pipeline records, per emitted instruction, `(byte-range,
// intended X86Opcode + operands, fixup-hole)` and hands the stream to this
// gate. For each COVERED instruction we:
//
//   1. DECODE the emitted bytes with `decode_one` — a standard SDM prefix / REX
//      / opcode-map / ModR/M / SIB / disp / imm decoder that was written from
//      the Intel SDM byte layout, NOT by reading encode.rs's emit paths, and
//   2. RENDER the intended (X86Opcode, operands) into the same canonical shape
//      with `render_intent`, and
//   3. structurally COMPARE the two (mnemonic, operand kinds, register numbers +
//      widths, immediate/displacement, and fixup-hole placement).
//
// A disagreement, an undecodable byte, or a length drift = fail-closed.
//
// INDEPENDENCE / ANCHORING (honest labeling)
// ------------------------------------------
// This is a fail-closed REDUNDANCY gate, not a proof. Its independence anchor is
// ENC-2: the offline llvm-objdump differential lane
// (`tests/encode_objdump_differential_x86.rs`) pins encode.rs's bytes == an
// external disassembler's rendering for the covered families. This decoder is
// replayed over the SAME instance corpus in `tests/decode_check_x86.rs`; because
// decoder(bytes) == render_intent AND encode.rs(bytes) == llvm-objdump, the
// decoder transitively agrees with the external disassembler. The per-compile
// gate then fires on any FUTURE encoder regression that drifts the bytes away
// from the (externally-pinned-correct) encoding.
//
// COVERAGE
// --------
// COVERED (structurally checked per-compile): the GP-integer families that
// dominate real integer programs and that ENC-2 covers offline — ALU reg/reg,
// reg/imm, reg/mem; MOV (rr/ri/mem loads+stores/SIB/RIP-rel); MOVZX/MOVSX; LEA
// (+SIB, +RIP); shifts; IMUL; unary (NEG/NOT/INC/DEC/MUL/DIV/IDIV/CDQ/CQO);
// branches (RET/CALL/CALL-ind/JMP/Jcc); PUSH/POP; SETcc; CMOVcc; bit-manip
// (BSF/BSR/TZCNT/LZCNT/POPCNT/BT/BSWAP); XCHG/CMPXCHG/MFENCE/UD2/multi-NOP.
//
// ALLOWLISTED (counted-with-reason, never silently skipped): SSE scalar/packed
// FP, SSE2 packed integer, GPR<->XMM transfer, SSE RIP-rel loads, FP converts,
// the fail-closed pseudo carriers (which the emitter rejects before bytes
// exist), and the CAS-loop multi-instruction expansions. These ride ENC-2's
// offline external-disassembler lane; extending the decoder to them is a clean
// follow-on (same shape). The `coverage` classification is an EXHAUSTIVE match
// over X86Opcode, so a NEW opcode cannot appear without a coverage decision.

use trust_cg_ir::x86_64_ops::{X86CondCode, X86Opcode};
use trust_cg_ir::x86_64_regs::{X86PReg, X86RegClass, x86_hw_encoding, x86_preg_class};

use crate::decode_check::{
    DecodeCheck, DecodeCheckError, DecodeCheckOutcome, FixupHole, FixupHoleKind,
};
use crate::x86_64::encode::X86InstOperands;

// ---------------------------------------------------------------------------
// Intent descriptor recorded by the pipeline hook
// ---------------------------------------------------------------------------

/// One intended, post-RA x86 instruction: the resolved opcode + operands the
/// emitter was told to encode.
#[derive(Clone, Debug)]
pub struct X86IntentInst {
    /// The resolved opcode passed to `X86Encoder::encode_instruction`.
    pub opcode: X86Opcode,
    /// The resolved operands passed alongside it.
    pub ops: X86InstOperands,
}

// ---------------------------------------------------------------------------
// Coverage classification (exhaustive — a new opcode needs a decision)
// ---------------------------------------------------------------------------

enum Coverage {
    Covered,
    Allowlisted(&'static str),
}

const SSE_FP: &str = "SSE scalar/packed FP (ENC-2 offline lane; decoder extension is a follow-on)";
const SSE2_PACKED: &str =
    "SSE2 packed integer (ENC-2 offline lane; decoder extension is a follow-on)";
const XMM_XFER: &str = "GPR<->XMM transfer (ENC-2 offline lane; decoder extension is a follow-on)";
const PSEUDO_FAIL_CLOSED: &str =
    "fail-closed pseudo carrier: the emitter rejects it before any bytes exist";
const PSEUDO_EXPANSION: &str = "CAS-loop multi-instruction expansion: component opcodes are covered; sequence lane is a follow-on";
const NARROW_CMPXCHG: &str = "narrow LOCK CMPXCHG (r/m8: F0 0F B0; r/m16: F0 66 0F B1) — AtomicU8/U16 \
     compare-exchange; the decoder round-trip extension for the byte/word forms is a \
     follow-on (32/64-bit CMPXCHG is Covered)";

const JUMP_TABLE: &str = "jump-table dispatch idiom (indirect JMP r64 / MOVSXD r64,[base+idx*4] SIB); the decoder \
     round-trip extension for these forms is a follow-on";

#[allow(clippy::too_many_lines)]
fn coverage(op: X86Opcode) -> Coverage {
    use Coverage::{Allowlisted, Covered};
    use X86Opcode as O;
    match op {
        // ---- covered: GP-integer families ----
        O::AddRR
        | O::SubRR
        | O::AdcRR
        | O::SbbRR
        | O::AndRR
        | O::OrRR
        | O::XorRR
        | O::CmpRR
        | O::TestRR
        | O::MovRR
        | O::MovRR32 => Covered,
        O::AddRI | O::SubRI | O::AndRI | O::OrRI | O::XorRI | O::CmpRI | O::CmpRI8 | O::TestRI => {
            Covered
        }
        O::AddRM | O::SubRM | O::CmpRM | O::TestRM => Covered,
        O::ImulRR | O::ImulRRI | O::ImulRM | O::ImulRMSib => Covered,
        O::Neg | O::Not | O::Inc | O::Dec | O::Idiv | O::Div | O::Mul | O::Cdq | O::Cqo => Covered,
        O::ShlRR | O::ShlRI | O::ShrRR | O::ShrRI | O::SarRR | O::SarRI | O::RolRI => Covered,
        O::MovRI
        | O::MovRM8
        | O::MovRM16
        | O::MovRM32
        | O::MovRM
        | O::MovMR8
        | O::MovMR16
        | O::MovMR32
        | O::MovMR
        | O::VolatileMovRM8
        | O::VolatileMovRM16
        | O::VolatileMovRM32
        | O::VolatileMovRM
        | O::VolatileMovMR8
        | O::VolatileMovMR16
        | O::VolatileMovMR32
        | O::VolatileMovMR
        | O::MovRMSib
        | O::MovMRSib
        | O::MovRM32Sib
        | O::MovMR32Sib
        | O::MovRM8Sib
        | O::MovMR8Sib
        | O::MovRipRel
        | O::MovRipRelTlv => Covered,
        O::Movzx | O::MovzxW | O::MovsxB | O::MovsxW | O::Movsx => Covered,
        O::Lea | O::LeaSib | O::LeaRip => Covered,
        O::Ret | O::Call | O::CallR | O::CallM | O::Jmp | O::Jcc => Covered,
        O::Push | O::Pop => Covered,
        O::Setcc | O::Cmovcc | O::Cmovcc32 => Covered,
        O::Bsf | O::Bsr | O::Tzcnt | O::Lzcnt | O::Popcnt | O::BtRI | O::Bswap => Covered,
        O::Xchg | O::Cmpxchg | O::Mfence | O::Ud2 | O::NopMulti => Covered,

        // ---- allowlisted (counted-with-reason) ----
        O::Addsd
        | O::Subsd
        | O::Mulsd
        | O::Divsd
        | O::Sqrtsd
        | O::Andpd
        | O::MovsdRR
        | O::MovsdRM
        | O::MovsdMR
        // Scaled-index scalar-FP loads: the same SSE_FP family as MovsdRM /
        // MovssRM, differing only in the effective-address form.
        | O::MovsdRMSib
        | O::MovssRMSib
        | O::Ucomisd
        | O::MovdquRM
        | O::MovdquMR
        | O::Addss
        | O::Subss
        | O::Mulss
        | O::Divss
        | O::Sqrtss
        | O::Andps
        | O::MovssRR
        | O::MovssRM
        | O::MovssMR
        // Volatile FP scalar + MOVDQU: byte-identical to the plain forms.
        | O::VolatileMovssRM
        | O::VolatileMovssMR
        | O::VolatileMovsdRM
        | O::VolatileMovsdMR
        | O::VolatileMovdquRM
        | O::VolatileMovdquMR
        | O::Ucomiss
        | O::Roundsd
        | O::Roundss
        | O::Minsd
        | O::Maxsd
        | O::Minss
        | O::Maxss
        | O::Cmpsd
        | O::Cmpss
        | O::MovssRipRel
        | O::MovsdRipRel
        | O::Cvtsi2sd
        | O::Cvtsd2si
        | O::Cvtsi2ss
        | O::Cvtss2si
        | O::Cvtsd2ss
        | O::Cvtss2sd
        | O::Cvttsd2si
        | O::Cvttss2si
        | O::Addps
        | O::Subps
        | O::Mulps
        | O::Divps
        | O::Addpd
        | O::Subpd
        | O::Mulpd
        | O::Divpd => Allowlisted(SSE_FP),
        O::Pand
        | O::Pandn
        | O::Por
        | O::Pxor
        | O::Pcmpeqd
        | O::Pshufd
        | O::Pmovmskb
        | O::MovdqaRR
        | O::Pcmpgtd
        | O::MovdqaRM
        | O::MovdqaMR
        | O::VolatileMovdqaRM
        | O::VolatileMovdqaMR
        | O::Paddd
        | O::Psubd
        | O::Punpckldq
        | O::Punpcklqdq
        | O::Paddq
        | O::Psubq
        | O::Paddb
        | O::Paddw
        | O::Psubb
        | O::Psubw
        | O::Pinsrd
        | O::Pextrd
        | O::Pmulld
        | O::Pcmpeqq
        | O::Pcmpgtq
        | O::Ptest
        | O::Pinsrq
        | O::Pextrq
        | O::Pblendvb
        | O::Pmuludq
        | O::Pmullw
        | O::Pcmpeqb
        | O::Pcmpeqw
        | O::Pcmpgtb
        | O::Pcmpgtw
        | O::Pslld
        | O::Psrld
        | O::Psrad
        | O::Psllq
        | O::Psrlq
        | O::Punpcklbw
        | O::Punpckhbw
        | O::Packuswb
        | O::Psadbw => Allowlisted(SSE2_PACKED),
        O::MovdToXmm | O::MovdFromXmm | O::MovqToXmm | O::MovqFromXmm => Allowlisted(XMM_XFER),
        O::V4I32MaskExtract
        | O::V16I8MaskExtract
        | O::V8I16MaskExtract
        | O::V2I64MaskExtract
        | O::V128BoolSelect
        | O::TrapBoundsCheckExact
        | O::TrapNullIfZeroExact
        | O::TrapDivZeroExact
        | O::TrapShiftRangeExact => Allowlisted(PSEUDO_FAIL_CLOSED),
        O::AtomicRmwCasLoop | O::AtomicRmwCasLoop8 | O::AtomicRmwCasLoop16 => {
            Allowlisted(PSEUDO_EXPANSION)
        }
        O::JmpR | O::MovsxdRMSib => Allowlisted(JUMP_TABLE),
        O::Cmpxchg8 | O::Cmpxchg16 => Allowlisted(NARROW_CMPXCHG),
        // Pseudo (zero bytes) — never recorded, but classify for exhaustiveness.
        O::Phi | O::StackAlloc | O::Nop => Allowlisted(PSEUDO_FAIL_CLOSED),
    }
}

// ---------------------------------------------------------------------------
// Canonical structural form (both decoder + intent render into this)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Mnem {
    Add,
    Or,
    Adc,
    Sbb,
    And,
    Sub,
    Xor,
    Cmp,
    Test,
    Mov,
    Lea,
    Imul,
    Neg,
    Not,
    Inc,
    Dec,
    Mul,
    Div,
    Idiv,
    Shl,
    Shr,
    Sar,
    /// ROL — rotate left. Shares the `C1`/`D3` group with the shifts, at
    /// ModRM extension /0 (SHL is /4). NOT a shift: it wraps bits round rather
    /// than discarding them, and its flag effect differs.
    Rol,
    Push,
    Pop,
    Call,
    CallInd,
    Ret,
    Jmp,
    Jcc,
    Setcc,
    Cmov,
    Movzx,
    Movsx,
    Bsf,
    Bsr,
    Tzcnt,
    Lzcnt,
    Popcnt,
    Bt,
    Bswap,
    Xchg,
    Cmpxchg,
    Cdq,
    Cqo,
    Mfence,
    Ud2,
    Nop,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum COp {
    Reg {
        num: u8,
        bits: u8,
    },
    Mem {
        base: Option<u8>,
        index: Option<u8>,
        scale: u8,
        disp: i64,
        rip: bool,
    },
    Imm(i64),
    /// A branch rel target — its value is never compared (patched post-encode).
    Rel,
}

#[derive(Clone, Debug)]
struct Canon {
    mnem: Mnem,
    bits: u8,
    cc: Option<u8>,
    ops: Vec<COp>,
    /// Offset (from instruction start) of the disp32 field, if present.
    disp_off: Option<usize>,
    /// Offset of the imm field, if present.
    imm_off: Option<usize>,
    /// Offset of the rel32 field, if present.
    rel_off: Option<usize>,
    /// Total decoded length in bytes.
    len: usize,
    /// True for XCHG/CMPXCHG, where the explicit operands are compared as a set.
    unordered: bool,
    /// True for MOV r,imm — comparison uses the width-reduced-value rule to
    /// tolerate the encoder's zero-extend/movabs width auto-selection.
    mov_imm: bool,
}

fn width_bits(reg: X86PReg) -> u8 {
    match x86_preg_class(reg) {
        X86RegClass::Gpr64 => 64,
        X86RegClass::Gpr32 => 32,
        X86RegClass::Gpr16 => 16,
        X86RegClass::Gpr8 => 8,
        X86RegClass::Xmm128 => 128,
        X86RegClass::System => 0,
    }
}

// ---------------------------------------------------------------------------
// Independent SDM decoder: bytes -> Canon
// ---------------------------------------------------------------------------

struct Reader<'a> {
    b: &'a [u8],
    i: usize,
}

impl<'a> Reader<'a> {
    fn u8(&mut self) -> Result<u8, String> {
        let v = *self
            .b
            .get(self.i)
            .ok_or_else(|| "truncated: expected a byte".to_string())?;
        self.i += 1;
        Ok(v)
    }
    fn i8(&mut self) -> Result<i64, String> {
        Ok(self.u8()? as i8 as i64)
    }
    fn i16(&mut self) -> Result<i64, String> {
        let lo = self.u8()? as u16;
        let hi = self.u8()? as u16;
        Ok((lo | (hi << 8)) as i16 as i64)
    }
    fn i32(&mut self) -> Result<i64, String> {
        let mut v: u32 = 0;
        for k in 0..4 {
            v |= (self.u8()? as u32) << (8 * k);
        }
        Ok(v as i32 as i64)
    }
    fn i64(&mut self) -> Result<i64, String> {
        let mut v: u64 = 0;
        for k in 0..8 {
            v |= (self.u8()? as u64) << (8 * k);
        }
        Ok(v as i64)
    }
}

struct Prefixes {
    rex_w: bool,
    rex_r: bool,
    rex_x: bool,
    rex_b: bool,
    opsize: bool,
    rep: bool,   // F3
    repne: bool, // F2
    lock: bool,  // F0
}

struct ModRMDec {
    /// reg field (4-bit, REX.R applied).
    reg: u8,
    /// For mod==3: the rm register (4-bit, REX.B applied).
    rm_reg: Option<u8>,
    /// For mod!=3: the decoded memory operand.
    mem: Option<COp>,
    /// Offset of the disp32 field (from instruction start), if present.
    disp_off: Option<usize>,
    /// Width of the displacement in bytes (0/1/4).
    #[allow(dead_code)]
    disp_bytes: u8,
}

fn read_prefixes(r: &mut Reader<'_>) -> Result<Prefixes, String> {
    let mut p = Prefixes {
        rex_w: false,
        rex_r: false,
        rex_x: false,
        rex_b: false,
        opsize: false,
        rep: false,
        repne: false,
        lock: false,
    };
    loop {
        let byte =
            *r.b.get(r.i)
                .ok_or_else(|| "truncated at prefixes".to_string())?;
        match byte {
            0xF0 => p.lock = true,
            0xF2 => p.repne = true,
            0xF3 => p.rep = true,
            0x66 => p.opsize = true,
            0x67 => {} // address-size override (unused by the emitter)
            0x2E | 0x36 | 0x3E | 0x26 | 0x64 | 0x65 => {} // segment overrides
            _ => break,
        }
        r.i += 1;
    }
    let byte = *r.b.get(r.i).ok_or_else(|| "truncated at REX".to_string())?;
    if (0x40..=0x4F).contains(&byte) {
        p.rex_w = byte & 0x08 != 0;
        p.rex_r = byte & 0x04 != 0;
        p.rex_x = byte & 0x02 != 0;
        p.rex_b = byte & 0x01 != 0;
        r.i += 1;
    }
    Ok(p)
}

/// Parse a ModR/M byte (+ SIB + disp) into registers / a memory operand.
fn read_modrm(r: &mut Reader<'_>, p: &Prefixes) -> Result<ModRMDec, String> {
    let modrm = r.u8()?;
    let mode = modrm >> 6;
    let reg = ((modrm >> 3) & 0x7) | if p.rex_r { 0x8 } else { 0 };
    let rm3 = modrm & 0x7;

    if mode == 0b11 {
        return Ok(ModRMDec {
            reg,
            rm_reg: Some(rm3 | if p.rex_b { 0x8 } else { 0 }),
            mem: None,
            disp_off: None,
            disp_bytes: 0,
        });
    }

    // Memory form.
    let mut base: Option<u8> = None;
    let mut index: Option<u8> = None;
    let mut scale: u8 = 1;
    let mut rip = false;
    let mut disp: i64 = 0;
    let mut disp_off: Option<usize> = None;
    let mut disp_bytes: u8 = 0;

    let mut base_absent = false;
    if rm3 == 0b100 {
        // SIB byte.
        let sib = r.u8()?;
        scale = 1u8 << (sib >> 6);
        let idx3 = (sib >> 3) & 0x7;
        let base3 = sib & 0x7;
        // index==0b100 && !REX.X => no index register.
        if idx3 != 0b100 || p.rex_x {
            index = Some(idx3 | if p.rex_x { 0x8 } else { 0 });
        }
        if base3 == 0b101 && mode == 0 {
            base_absent = true; // disp32, no base
        } else {
            base = Some(base3 | if p.rex_b { 0x8 } else { 0 });
        }
    } else if rm3 == 0b101 && mode == 0 {
        rip = true;
    } else {
        base = Some(rm3 | if p.rex_b { 0x8 } else { 0 });
    }

    // Displacement.
    if rip || base_absent {
        disp_off = Some(r.i);
        disp = r.i32()?;
        disp_bytes = 4;
    } else {
        match mode {
            0 => {}
            1 => {
                disp_off = Some(r.i);
                disp = r.i8()?;
                disp_bytes = 1;
            }
            2 => {
                disp_off = Some(r.i);
                disp = r.i32()?;
                disp_bytes = 4;
            }
            _ => unreachable!(),
        }
    }

    Ok(ModRMDec {
        reg,
        rm_reg: None,
        mem: Some(COp::Mem {
            base,
            index,
            scale,
            disp,
            rip,
        }),
        disp_off,
        disp_bytes,
    })
}

fn opsize_bits(p: &Prefixes) -> u8 {
    if p.rex_w {
        64
    } else if p.opsize {
        16
    } else {
        32
    }
}

/// Decode exactly one instruction from `bytes` (starting at 0) into `Canon`.
#[allow(clippy::too_many_lines)]
fn decode_one(bytes: &[u8]) -> Result<Canon, String> {
    let mut r = Reader { b: bytes, i: 0 };
    let p = read_prefixes(&mut r)?;
    let op0 = r.u8()?;

    // ----- two/three-byte 0F map -----
    if op0 == 0x0F {
        return decode_0f(&mut r, &p, bytes);
    }

    // ----- one-byte map -----
    let bits = opsize_bits(&p);
    let c = |mnem: Mnem| Canon {
        mnem,
        bits,
        cc: None,
        ops: Vec::new(),
        disp_off: None,
        imm_off: None,
        rel_off: None,
        len: 0,
        unordered: false,
        mov_imm: false,
    };

    // ALU r/m, r (reg is source, r/m is dest): 01/29/11/19/21/09/31/39, TEST 85,
    // MOV r/m,r 89, XCHG 87.
    let alu_mr = |op: u8| -> Option<Mnem> {
        Some(match op {
            0x01 => Mnem::Add,
            0x29 => Mnem::Sub,
            0x11 => Mnem::Adc,
            0x19 => Mnem::Sbb,
            0x21 => Mnem::And,
            0x09 => Mnem::Or,
            0x31 => Mnem::Xor,
            0x39 => Mnem::Cmp,
            0x85 => Mnem::Test,
            0x89 => Mnem::Mov,
            0x87 => Mnem::Xchg,
            _ => return None,
        })
    };
    if let Some(mnem) = alu_mr(op0) {
        let m = read_modrm(&mut r, &p)?;
        let dst = modrm_rm_operand(&m, bits)?;
        let src = COp::Reg { num: m.reg, bits };
        let mut inst = c(mnem);
        // canonical order dst, src (for TEST/XCHG order is immaterial).
        inst.ops = vec![dst, src];
        inst.disp_off = m.disp_off;
        inst.unordered = matches!(mnem, Mnem::Xchg | Mnem::Test);
        inst.len = r.i;
        return Ok(inst);
    }

    // ADD/SUB/CMP r, r/m (reg is dest): 03/2B/3B.
    let alu_rm = |op: u8| -> Option<Mnem> {
        Some(match op {
            0x03 => Mnem::Add,
            0x2B => Mnem::Sub,
            0x3B => Mnem::Cmp,
            _ => return None,
        })
    };
    if let Some(mnem) = alu_rm(op0) {
        let m = read_modrm(&mut r, &p)?;
        let dst = COp::Reg { num: m.reg, bits };
        let src = modrm_rm_operand(&m, bits)?;
        let mut inst = c(mnem);
        inst.ops = vec![dst, src];
        inst.disp_off = m.disp_off;
        inst.len = r.i;
        return Ok(inst);
    }

    match op0 {
        // XCHG (E)AX, (E)AX is the canonical one-byte NOP. The encoder also
        // prefixes it with 66 for its canonical two-byte NOP. Although the
        // architectural spelling is XCHG, the operands are the same register,
        // so the observable semantics exactly match the padding intent.
        0x90 => {
            // REX.B changes the implicit accumulator operand to R8, making
            // this XCHG RAX,R8 rather than a NOP.  Other REX bits and
            // repetition/lock prefixes are not emitted by the canonical NOP
            // encoder either; reject them here rather than normalizing a
            // semantically different or invalid spelling into padding.
            if p.rex_w || p.rex_r || p.rex_x || p.rex_b || p.rep || p.repne || p.lock {
                return Err("non-canonical prefixes on 90 NOP".to_string());
            }
            let mut inst = c(Mnem::Nop);
            inst.bits = 0;
            inst.len = r.i;
            Ok(inst)
        }
        // ALU r/m, imm: 81 /ext id, 83 /ext ib (sign-extended).
        0x81 | 0x83 => {
            let m = read_modrm(&mut r, &p)?;
            let ext = m.reg & 0x7;
            let mnem = match ext {
                0 => Mnem::Add,
                1 => Mnem::Or,
                4 => Mnem::And,
                5 => Mnem::Sub,
                6 => Mnem::Xor,
                7 => Mnem::Cmp,
                _ => return Err(format!("group1 /{ext} not modeled")),
            };
            let dst = modrm_rm_operand(&m, bits)?;
            let imm_off = r.i;
            let imm = if op0 == 0x83 { r.i8()? } else { r.i32()? };
            let mut inst = c(mnem);
            inst.ops = vec![dst, COp::Imm(imm)];
            inst.disp_off = m.disp_off;
            inst.imm_off = Some(imm_off);
            inst.len = r.i;
            Ok(inst)
        }
        // F7 /ext: TEST(0) id, NOT(2), NEG(3), MUL(4), DIV(6), IDIV(7).
        0xF7 => {
            let m = read_modrm(&mut r, &p)?;
            let ext = m.reg & 0x7;
            let dst = modrm_rm_operand(&m, bits)?;
            let mut inst;
            match ext {
                0 => {
                    let imm_off = r.i;
                    let imm = r.i32()?;
                    inst = c(Mnem::Test);
                    inst.ops = vec![dst, COp::Imm(imm)];
                    inst.imm_off = Some(imm_off);
                }
                2 => {
                    inst = c(Mnem::Not);
                    inst.ops = vec![dst];
                }
                3 => {
                    inst = c(Mnem::Neg);
                    inst.ops = vec![dst];
                }
                4 => {
                    inst = c(Mnem::Mul);
                    inst.ops = vec![dst];
                }
                6 => {
                    inst = c(Mnem::Div);
                    inst.ops = vec![dst];
                }
                7 => {
                    inst = c(Mnem::Idiv);
                    inst.ops = vec![dst];
                }
                _ => return Err(format!("F7 /{ext} not modeled")),
            }
            inst.disp_off = m.disp_off;
            inst.len = r.i;
            Ok(inst)
        }
        // FF /ext: INC(0), DEC(1), CALL(2 indirect).
        0xFF => {
            let m = read_modrm(&mut r, &p)?;
            let ext = m.reg & 0x7;
            let (mnem, opbits) = match ext {
                0 => (Mnem::Inc, bits),
                1 => (Mnem::Dec, bits),
                2 => (Mnem::CallInd, 64),
                _ => return Err(format!("FF /{ext} not modeled")),
            };
            let dst = modrm_rm_operand(&m, opbits)?;
            let mut inst = c(mnem);
            inst.bits = opbits;
            inst.ops = vec![dst];
            inst.disp_off = m.disp_off;
            inst.len = r.i;
            Ok(inst)
        }
        // C1 /ext ib: shift by imm8. D3 /ext: shift by CL.
        0xC1 | 0xD3 => {
            let m = read_modrm(&mut r, &p)?;
            let ext = m.reg & 0x7;
            let mnem = match ext {
                0 => Mnem::Rol,
                4 => Mnem::Shl,
                5 => Mnem::Shr,
                7 => Mnem::Sar,
                _ => return Err(format!("shift /{ext} not modeled")),
            };
            let dst = modrm_rm_operand(&m, bits)?;
            let mut inst = c(mnem);
            if op0 == 0xC1 {
                let imm_off = r.i;
                let imm = r.i8()?;
                inst.ops = vec![dst, COp::Imm(imm)];
                inst.imm_off = Some(imm_off);
            } else {
                inst.ops = vec![dst];
            }
            inst.disp_off = m.disp_off;
            inst.len = r.i;
            Ok(inst)
        }
        // IMUL r, r/m, imm: 69 /r id, 6B /r ib (reg=dst, r/m=src).
        0x69 | 0x6B => {
            let m = read_modrm(&mut r, &p)?;
            let dst = COp::Reg { num: m.reg, bits };
            let src = modrm_rm_operand(&m, bits)?;
            let imm_off = r.i;
            let imm = if op0 == 0x6B { r.i8()? } else { r.i32()? };
            let mut inst = c(Mnem::Imul);
            inst.ops = vec![dst, src, COp::Imm(imm)];
            inst.disp_off = m.disp_off;
            inst.imm_off = Some(imm_off);
            inst.len = r.i;
            Ok(inst)
        }
        // MOVSXD r64, r/m32: 63 /r.
        0x63 => {
            let m = read_modrm(&mut r, &p)?;
            let dst = COp::Reg { num: m.reg, bits };
            let src = modrm_rm_operand(&m, 32)?;
            let mut inst = c(Mnem::Movsx);
            inst.ops = vec![dst, src];
            inst.disp_off = m.disp_off;
            inst.len = r.i;
            Ok(inst)
        }
        // LEA r, m: 8D /r.
        0x8D => {
            let m = read_modrm(&mut r, &p)?;
            let mem = m
                .mem
                .ok_or_else(|| "LEA requires a memory operand".to_string())?;
            let mut inst = c(Mnem::Lea);
            inst.ops = vec![COp::Reg { num: m.reg, bits }, mem];
            inst.disp_off = m.disp_off;
            inst.len = r.i;
            Ok(inst)
        }
        // MOV r, r/m (loads): 8A (r8), 8B (r16/32/64).
        0x8A | 0x8B => {
            let load_bits = if op0 == 0x8A { 8 } else { bits };
            let m = read_modrm(&mut r, &p)?;
            let dst = COp::Reg {
                num: m.reg,
                bits: load_bits,
            };
            let src = modrm_rm_operand(&m, load_bits)?;
            let mut inst = c(Mnem::Mov);
            inst.bits = load_bits;
            inst.ops = vec![dst, src];
            inst.disp_off = m.disp_off;
            inst.len = r.i;
            Ok(inst)
        }
        // MOV r/m, r (stores): 88 (r8).
        0x88 => {
            let m = read_modrm(&mut r, &p)?;
            let dst = modrm_rm_operand(&m, 8)?;
            let src = COp::Reg {
                num: m.reg,
                bits: 8,
            };
            let mut inst = c(Mnem::Mov);
            inst.bits = 8;
            inst.ops = vec![dst, src];
            inst.disp_off = m.disp_off;
            inst.len = r.i;
            Ok(inst)
        }
        // MOV r, imm: B0+r ib (byte); B8+r iw/id/io.
        0xB0..=0xB7 => {
            let num = (op0 - 0xB0) | if p.rex_b { 0x8 } else { 0 };
            let imm_off = r.i;
            let imm = r.i8()?;
            let mut inst = c(Mnem::Mov);
            inst.bits = 8;
            inst.ops = vec![COp::Reg { num, bits: 8 }, COp::Imm(imm)];
            inst.imm_off = Some(imm_off);
            inst.mov_imm = true;
            inst.len = r.i;
            Ok(inst)
        }
        0xB8..=0xBF => {
            let num = (op0 - 0xB8) | if p.rex_b { 0x8 } else { 0 };
            let imm_off = r.i;
            let (imm, w) = if p.rex_w {
                (r.i64()?, 64)
            } else if p.opsize {
                (r.i16()?, 16)
            } else {
                (r.i32()?, 32)
            };
            let mut inst = c(Mnem::Mov);
            inst.bits = w;
            inst.ops = vec![COp::Reg { num, bits: w }, COp::Imm(imm)];
            inst.imm_off = Some(imm_off);
            inst.mov_imm = true;
            inst.len = r.i;
            Ok(inst)
        }
        // PUSH r: 50+r. POP r: 58+r.
        0x50..=0x57 => {
            let num = (op0 - 0x50) | if p.rex_b { 0x8 } else { 0 };
            let mut inst = c(Mnem::Push);
            inst.bits = 64;
            inst.ops = vec![COp::Reg { num, bits: 64 }];
            inst.len = r.i;
            Ok(inst)
        }
        0x58..=0x5F => {
            let num = (op0 - 0x58) | if p.rex_b { 0x8 } else { 0 };
            let mut inst = c(Mnem::Pop);
            inst.bits = 64;
            inst.ops = vec![COp::Reg { num, bits: 64 }];
            inst.len = r.i;
            Ok(inst)
        }
        // RET.
        0xC3 => {
            let mut inst = c(Mnem::Ret);
            inst.bits = 0;
            inst.len = r.i;
            Ok(inst)
        }
        // CALL rel32.
        0xE8 => {
            let rel_off = r.i;
            let _ = r.i32()?;
            let mut inst = c(Mnem::Call);
            inst.bits = 0;
            inst.ops = vec![COp::Rel];
            inst.rel_off = Some(rel_off);
            inst.len = r.i;
            Ok(inst)
        }
        // JMP rel32.
        0xE9 => {
            let rel_off = r.i;
            let _ = r.i32()?;
            let mut inst = c(Mnem::Jmp);
            inst.bits = 0;
            inst.ops = vec![COp::Rel];
            inst.rel_off = Some(rel_off);
            inst.len = r.i;
            Ok(inst)
        }
        // CDQ / CQO: 99 (REX.W distinguishes).
        0x99 => {
            let mut inst = c(if p.rex_w { Mnem::Cqo } else { Mnem::Cdq });
            inst.bits = if p.rex_w { 64 } else { 32 };
            inst.len = r.i;
            Ok(inst)
        }
        other => Err(format!("one-byte opcode {other:#04x} not modeled")),
    }
}

#[allow(clippy::too_many_lines)]
fn decode_0f(r: &mut Reader<'_>, p: &Prefixes, _bytes: &[u8]) -> Result<Canon, String> {
    let op = r.u8()?;
    let bits = opsize_bits(p);
    let mk = |mnem: Mnem, bits: u8| Canon {
        mnem,
        bits,
        cc: None,
        ops: Vec::new(),
        disp_off: None,
        imm_off: None,
        rel_off: None,
        len: 0,
        unordered: false,
        mov_imm: false,
    };

    // Jcc rel32: 0F 80+cc.
    if (0x80..=0x8F).contains(&op) {
        let cc = op - 0x80;
        let rel_off = r.i;
        let _ = r.i32()?;
        let mut inst = mk(Mnem::Jcc, 0);
        inst.cc = Some(cc);
        inst.ops = vec![COp::Rel];
        inst.rel_off = Some(rel_off);
        inst.len = r.i;
        return Ok(inst);
    }
    // SETcc r/m8: 0F 90+cc /0.
    if (0x90..=0x9F).contains(&op) {
        let cc = op - 0x90;
        let m = read_modrm(r, p)?;
        let dst = modrm_rm_operand(&m, 8)?;
        let mut inst = mk(Mnem::Setcc, 8);
        inst.cc = Some(cc);
        inst.ops = vec![dst];
        inst.disp_off = m.disp_off;
        inst.len = r.i;
        return Ok(inst);
    }
    // CMOVcc r, r/m: 0F 40+cc /r.
    if (0x40..=0x4F).contains(&op) {
        let cc = op - 0x40;
        let m = read_modrm(r, p)?;
        let dst = COp::Reg { num: m.reg, bits };
        let src = modrm_rm_operand(&m, bits)?;
        let mut inst = mk(Mnem::Cmov, bits);
        inst.cc = Some(cc);
        inst.ops = vec![dst, src];
        inst.disp_off = m.disp_off;
        inst.len = r.i;
        return Ok(inst);
    }

    match op {
        // IMUL r, r/m: 0F AF /r.
        0xAF => {
            let m = read_modrm(r, p)?;
            let dst = COp::Reg { num: m.reg, bits };
            let src = modrm_rm_operand(&m, bits)?;
            let mut inst = mk(Mnem::Imul, bits);
            inst.ops = vec![dst, src];
            inst.disp_off = m.disp_off;
            inst.len = r.i;
            Ok(inst)
        }
        // MOVZX 0F B6 (r/m8), 0F B7 (r/m16).
        0xB6 | 0xB7 => {
            let src_bits = if op == 0xB6 { 8 } else { 16 };
            let m = read_modrm(r, p)?;
            let dst = COp::Reg { num: m.reg, bits };
            let src = modrm_rm_operand(&m, src_bits)?;
            let mut inst = mk(Mnem::Movzx, bits);
            inst.ops = vec![dst, src];
            inst.disp_off = m.disp_off;
            inst.len = r.i;
            Ok(inst)
        }
        // MOVSX 0F BE (r/m8), 0F BF (r/m16).
        0xBE | 0xBF => {
            let src_bits = if op == 0xBE { 8 } else { 16 };
            let m = read_modrm(r, p)?;
            let dst = COp::Reg { num: m.reg, bits };
            let src = modrm_rm_operand(&m, src_bits)?;
            let mut inst = mk(Mnem::Movsx, bits);
            inst.ops = vec![dst, src];
            inst.disp_off = m.disp_off;
            inst.len = r.i;
            Ok(inst)
        }
        // BSF/BSR (no F3) or TZCNT/LZCNT (F3): 0F BC/BD.
        0xBC | 0xBD => {
            let mnem = match (op, p.rep) {
                (0xBC, false) => Mnem::Bsf,
                (0xBD, false) => Mnem::Bsr,
                (0xBC, true) => Mnem::Tzcnt,
                (0xBD, true) => Mnem::Lzcnt,
                _ => unreachable!(),
            };
            let m = read_modrm(r, p)?;
            let dst = COp::Reg { num: m.reg, bits };
            let src = modrm_rm_operand(&m, bits)?;
            let mut inst = mk(mnem, bits);
            inst.ops = vec![dst, src];
            inst.disp_off = m.disp_off;
            inst.len = r.i;
            Ok(inst)
        }
        // POPCNT: F3 0F B8 /r.
        0xB8 => {
            if !p.rep {
                return Err("0F B8 without F3 (JMPE) not modeled".to_string());
            }
            let m = read_modrm(r, p)?;
            let dst = COp::Reg { num: m.reg, bits };
            let src = modrm_rm_operand(&m, bits)?;
            let mut inst = mk(Mnem::Popcnt, bits);
            inst.ops = vec![dst, src];
            inst.disp_off = m.disp_off;
            inst.len = r.i;
            Ok(inst)
        }
        // BT r/m, imm8: 0F BA /4 ib.
        0xBA => {
            let m = read_modrm(r, p)?;
            let ext = m.reg & 0x7;
            if ext != 4 {
                return Err(format!("0F BA /{ext} not modeled"));
            }
            let dst = modrm_rm_operand(&m, bits)?;
            let imm_off = r.i;
            let imm = r.i8()?;
            let mut inst = mk(Mnem::Bt, bits);
            inst.ops = vec![dst, COp::Imm(imm)];
            inst.disp_off = m.disp_off;
            inst.imm_off = Some(imm_off);
            inst.len = r.i;
            Ok(inst)
        }
        // BSWAP r: 0F C8+r.
        0xC8..=0xCF => {
            let num = (op - 0xC8) | if p.rex_b { 0x8 } else { 0 };
            let mut inst = mk(Mnem::Bswap, if p.rex_w { 64 } else { 32 });
            inst.ops = vec![COp::Reg {
                num,
                bits: inst.bits,
            }];
            inst.len = r.i;
            Ok(inst)
        }
        // CMPXCHG r/m, r: 0F B1 /r (LOCK optional).
        0xB1 => {
            let m = read_modrm(r, p)?;
            let dst = modrm_rm_operand(&m, bits)?;
            let src = COp::Reg { num: m.reg, bits };
            let mut inst = mk(Mnem::Cmpxchg, bits);
            inst.ops = vec![dst, src];
            inst.disp_off = m.disp_off;
            inst.unordered = true;
            inst.len = r.i;
            Ok(inst)
        }
        // UD2: 0F 0B.
        0x0B => {
            let mut inst = mk(Mnem::Ud2, 0);
            inst.len = r.i;
            Ok(inst)
        }
        // MFENCE: 0F AE F0 (mod=11, reg=6, rm=0). NOP multi: 0F 1F /0.
        0xAE => {
            let m = read_modrm(r, p)?;
            if (m.reg & 0x7) == 6 {
                let mut inst = mk(Mnem::Mfence, 0);
                inst.len = r.i;
                Ok(inst)
            } else {
                Err(format!("0F AE /{} not modeled", m.reg & 0x7))
            }
        }
        0x1F => {
            if p.rex_w || p.rex_r || p.rex_x || p.rex_b || p.rep || p.repne || p.lock {
                return Err("non-canonical prefixes on 0F 1F NOP".to_string());
            }
            let m = read_modrm(r, p)?;
            if (m.reg & 0x7) != 0 {
                return Err(format!("0F 1F /{} is not NOP", m.reg & 0x7));
            }
            let mut inst = mk(Mnem::Nop, 0);
            inst.len = r.i;
            Ok(inst)
        }
        other => Err(format!("0F {other:#04x} not modeled")),
    }
}

fn modrm_rm_operand(m: &ModRMDec, bits: u8) -> Result<COp, String> {
    if let Some(num) = m.rm_reg {
        Ok(COp::Reg { num, bits })
    } else if let Some(mem) = m.mem {
        Ok(mem)
    } else {
        Err("ModR/M has neither a register nor a memory operand".to_string())
    }
}

/// Return the exact Intel-recommended NOP byte string emitted for a supported
/// `NopMulti` size.  This is intentionally a strict allowlist rather than a
/// permissive decoder: accepting an alternative prefix is dangerous because
/// e.g. `41 90` is `XCHG RAX,R8`, and `F3 90` is `PAUSE`, not padding.
fn canonical_nop_padding(size: usize) -> Option<&'static [u8]> {
    match size {
        1 => Some(&[0x90]),
        2 => Some(&[0x66, 0x90]),
        3 => Some(&[0x0F, 0x1F, 0x00]),
        4 => Some(&[0x0F, 0x1F, 0x40, 0x00]),
        5 => Some(&[0x0F, 0x1F, 0x44, 0x00, 0x00]),
        6 => Some(&[0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00]),
        7 => Some(&[0x0F, 0x1F, 0x80, 0x00, 0x00, 0x00, 0x00]),
        8 => Some(&[0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]),
        9 => Some(&[0x66, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]),
        10 => Some(&[0x66, 0x0F, 0x1F, 0x84, 0, 0, 0, 0, 0, 0x90]),
        11 => Some(&[0x66, 0x0F, 0x1F, 0x84, 0, 0, 0, 0, 0, 0x66, 0x90]),
        12 => Some(&[0x66, 0x0F, 0x1F, 0x84, 0, 0, 0, 0, 0, 0x0F, 0x1F, 0]),
        13 => Some(&[0x66, 0x0F, 0x1F, 0x84, 0, 0, 0, 0, 0, 0x0F, 0x1F, 0x40, 0]),
        14 => Some(&[
            0x66, 0x0F, 0x1F, 0x84, 0, 0, 0, 0, 0, 0x0F, 0x1F, 0x44, 0, 0,
        ]),
        15 => Some(&[
            0x66, 0x0F, 0x1F, 0x84, 0, 0, 0, 0, 0, 0x66, 0x0F, 0x1F, 0x44, 0, 0,
        ]),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Intent renderer: (X86Opcode, ops) -> Canon
// ---------------------------------------------------------------------------

/// A register operand at an EXPLICIT width. The register's own class width is
/// deliberately NOT used: several opcodes fix the operand size independently of
/// the operand register's class (e.g. `MovRR32` is 32-bit even when the ISel
/// hands it a 64-bit-class `X86PReg`, using only its number). The decoder always
/// derives operand width from the encoding (REX.W / 0x66 / the opcode), so the
/// intent side must derive it from the instruction's opcode-determined width too.
fn reg_at(reg: X86PReg, bits: u8) -> COp {
    COp::Reg {
        num: x86_hw_encoding(reg),
        bits,
    }
}

fn rr_bits(dst: X86PReg, src: X86PReg) -> u8 {
    // The GP reg-reg forms are 64-bit unless BOTH operands are 32-bit.
    if width_bits(dst) == 32 && width_bits(src) == 32 {
        32
    } else {
        64
    }
}

fn ri_bits(dst: X86PReg) -> u8 {
    if width_bits(dst) == 32 { 32 } else { 64 }
}

/// Render the memory operand carried in `ops` as a [`COp::Mem`].
fn mem_op(ops: &X86InstOperands, rip: bool) -> Result<COp, String> {
    if rip {
        return Ok(COp::Mem {
            base: None,
            index: None,
            scale: 1,
            disp: ops.disp,
            rip: true,
        });
    }
    let base = ops
        .base
        .ok_or_else(|| "intent memory op missing base".to_string())?;
    Ok(COp::Mem {
        base: Some(x86_hw_encoding(base)),
        index: ops.index.map(x86_hw_encoding),
        scale: if ops.index.is_some() { ops.scale } else { 1 },
        disp: ops.disp,
        rip: false,
    })
}

fn base_canon(mnem: Mnem, bits: u8) -> Canon {
    Canon {
        mnem,
        bits,
        cc: None,
        ops: Vec::new(),
        disp_off: None,
        imm_off: None,
        rel_off: None,
        len: 0,
        unordered: false,
        mov_imm: false,
    }
}

#[allow(clippy::too_many_lines)]
fn render_intent(intent: &X86IntentInst) -> Result<Canon, String> {
    use X86Opcode as O;
    let ops = &intent.ops;
    let dst = || ops.dst.ok_or_else(|| "intent missing dst".to_string());
    let src = || ops.src.ok_or_else(|| "intent missing src".to_string());
    let cc = || ops.cc.map(X86CondCode::encoding);

    let alu_rr = |mnem: Mnem, unordered: bool| -> Result<Canon, String> {
        let d = dst()?;
        let s = src()?;
        let mut c = base_canon(mnem, rr_bits(d, s));
        c.ops = vec![reg_at(d, c.bits), reg_at(s, c.bits)];
        c.unordered = unordered;
        Ok(c)
    };
    let alu_ri = |mnem: Mnem| -> Result<Canon, String> {
        let d = dst()?;
        let mut c = base_canon(mnem, ri_bits(d));
        c.ops = vec![reg_at(d, c.bits), COp::Imm(ops.imm)];
        Ok(c)
    };
    let unary = |mnem: Mnem| -> Result<Canon, String> {
        let d = dst()?;
        let mut c = base_canon(mnem, ri_bits(d));
        c.ops = vec![reg_at(d, c.bits)];
        Ok(c)
    };
    let alu_rm = |mnem: Mnem| -> Result<Canon, String> {
        let d = dst()?;
        let mut c = base_canon(mnem, 64);
        c.ops = vec![reg_at(d, c.bits), mem_op(ops, false)?];
        Ok(c)
    };

    let c = match intent.opcode {
        O::AddRR => alu_rr(Mnem::Add, false)?,
        O::SubRR => alu_rr(Mnem::Sub, false)?,
        O::AdcRR => alu_rr(Mnem::Adc, false)?,
        O::SbbRR => alu_rr(Mnem::Sbb, false)?,
        O::AndRR => alu_rr(Mnem::And, false)?,
        O::OrRR => alu_rr(Mnem::Or, false)?,
        O::XorRR => alu_rr(Mnem::Xor, false)?,
        O::CmpRR => alu_rr(Mnem::Cmp, false)?,
        O::TestRR => alu_rr(Mnem::Test, true)?,
        O::MovRR => alu_rr(Mnem::Mov, false)?,
        O::MovRR32 => {
            let d = dst()?;
            let s = src()?;
            let mut c = base_canon(Mnem::Mov, 32);
            c.ops = vec![reg_at(d, c.bits), reg_at(s, c.bits)];
            c
        }

        O::AddRI => alu_ri(Mnem::Add)?,
        O::SubRI => alu_ri(Mnem::Sub)?,
        O::AndRI => alu_ri(Mnem::And)?,
        O::OrRI => alu_ri(Mnem::Or)?,
        O::XorRI => alu_ri(Mnem::Xor)?,
        O::CmpRI | O::CmpRI8 => alu_ri(Mnem::Cmp)?,
        O::TestRI => alu_ri(Mnem::Test)?,

        O::AddRM => alu_rm(Mnem::Add)?,
        O::SubRM => alu_rm(Mnem::Sub)?,
        O::CmpRM => alu_rm(Mnem::Cmp)?,
        O::TestRM => {
            // TEST r64, [mem]: 85 /r — reg is source, r/m is memory. The gate's
            // `unordered` set-compare tolerates operand ordering.
            let d = dst()?;
            let mut c = base_canon(Mnem::Test, 64);
            c.ops = vec![mem_op(ops, false)?, reg_at(d, c.bits)];
            c.unordered = true;
            c
        }

        O::ImulRR => {
            let d = dst()?;
            let s = src()?;
            let mut c = base_canon(Mnem::Imul, rr_bits(d, s));
            c.ops = vec![reg_at(d, c.bits), reg_at(s, c.bits)];
            c
        }
        O::ImulRRI => {
            let d = dst()?;
            let s = src()?;
            let mut c = base_canon(Mnem::Imul, rr_bits(d, s));
            c.ops = vec![reg_at(d, c.bits), reg_at(s, c.bits), COp::Imm(ops.imm)];
            c
        }
        O::ImulRM => {
            let d = dst()?;
            let mut c = base_canon(Mnem::Imul, 64);
            c.ops = vec![reg_at(d, c.bits), mem_op(ops, false)?];
            c
        }
        O::ImulRMSib => {
            // Same canonical form as ImulRM: `mem_op` carries index/scale
            // through generically, so the SIB form canonicalizes identically.
            let d = dst()?;
            let mut c = base_canon(Mnem::Imul, 64);
            c.ops = vec![reg_at(d, c.bits), mem_op(ops, false)?];
            c
        }

        O::Neg => unary(Mnem::Neg)?,
        O::Not => unary(Mnem::Not)?,
        O::Inc => unary(Mnem::Inc)?,
        O::Dec => unary(Mnem::Dec)?,
        O::Idiv => unary(Mnem::Idiv)?,
        O::Div => unary(Mnem::Div)?,
        O::Mul => unary(Mnem::Mul)?,
        O::Cdq => base_canon(Mnem::Cdq, 32),
        O::Cqo => base_canon(Mnem::Cqo, 64),

        O::RolRI => shift_ri(Mnem::Rol, ops)?,
        O::ShlRI => shift_ri(Mnem::Shl, ops)?,
        O::ShrRI => shift_ri(Mnem::Shr, ops)?,
        O::SarRI => shift_ri(Mnem::Sar, ops)?,
        O::ShlRR => shift_rcl(Mnem::Shl, ops)?,
        O::ShrRR => shift_rcl(Mnem::Shr, ops)?,
        O::SarRR => shift_rcl(Mnem::Sar, ops)?,

        O::MovRI => {
            let d = dst()?;
            let mut c = base_canon(Mnem::Mov, width_bits(d));
            c.ops = vec![reg_at(d, c.bits), COp::Imm(ops.imm)];
            c.mov_imm = true;
            c
        }
        O::MovRM8 | O::VolatileMovRM8 => mem_load(Mnem::Mov, 8, ops)?,
        O::MovRM16 | O::VolatileMovRM16 => mem_load(Mnem::Mov, 16, ops)?,
        O::MovRM32 | O::VolatileMovRM32 => mem_load(Mnem::Mov, 32, ops)?,
        O::MovRM | O::VolatileMovRM => mem_load(Mnem::Mov, 64, ops)?,
        O::MovMR8 | O::VolatileMovMR8 => mem_store(Mnem::Mov, 8, ops)?,
        O::MovMR16 | O::VolatileMovMR16 => mem_store(Mnem::Mov, 16, ops)?,
        O::MovMR32 | O::VolatileMovMR32 => mem_store(Mnem::Mov, 32, ops)?,
        O::MovMR | O::VolatileMovMR => mem_store(Mnem::Mov, 64, ops)?,
        O::MovRMSib => mem_load(Mnem::Mov, 64, ops)?,
        O::MovMRSib => mem_store(Mnem::Mov, 64, ops)?,
        O::MovRM32Sib => mem_load(Mnem::Mov, 32, ops)?,
        O::MovMR32Sib => mem_store(Mnem::Mov, 32, ops)?,
        // 8-bit SIB siblings: same shared mem_load/mem_store intent as
        // MovRM8/MovMR8, at the SIB addressing form. The decoder needs no new
        // case — 0x8A/0x88 already route through `read_modrm`, which handles a
        // SIB byte generically (exactly as 0x89 does for MovMR32Sib).
        O::MovRM8Sib => mem_load(Mnem::Mov, 8, ops)?,
        O::MovMR8Sib => mem_store(Mnem::Mov, 8, ops)?,
        O::MovRipRel | O::MovRipRelTlv => {
            let d = dst()?;
            let mut c = base_canon(Mnem::Mov, 64);
            c.ops = vec![reg_at(d, c.bits), mem_op(ops, true)?];
            c
        }

        O::Movzx => movext(Mnem::Movzx, 8, ops)?,
        O::MovzxW => movext(Mnem::Movzx, 16, ops)?,
        O::MovsxB => movext(Mnem::Movsx, 8, ops)?,
        O::MovsxW => movext(Mnem::Movsx, 16, ops)?,
        O::Movsx => movext(Mnem::Movsx, 32, ops)?,

        O::Lea => {
            let d = dst()?;
            let mut c = base_canon(Mnem::Lea, 64);
            c.ops = vec![reg_at(d, c.bits), mem_op(ops, false)?];
            c
        }
        O::LeaSib => {
            let d = dst()?;
            let mut c = base_canon(Mnem::Lea, 64);
            c.ops = vec![reg_at(d, c.bits), mem_op(ops, false)?];
            c
        }
        O::LeaRip => {
            let d = dst()?;
            let mut c = base_canon(Mnem::Lea, 64);
            c.ops = vec![reg_at(d, c.bits), mem_op(ops, true)?];
            c
        }

        O::Ret => base_canon(Mnem::Ret, 0),
        O::Call => {
            let mut c = base_canon(Mnem::Call, 0);
            c.ops = vec![COp::Rel];
            c
        }
        O::CallR => {
            let d = dst()?;
            let mut c = base_canon(Mnem::CallInd, 64);
            c.ops = vec![COp::Reg {
                num: x86_hw_encoding(d),
                bits: 64,
            }];
            c
        }
        O::CallM => {
            let mut c = base_canon(Mnem::CallInd, 64);
            c.ops = vec![mem_op(ops, false)?];
            c
        }
        O::Jmp => {
            let mut c = base_canon(Mnem::Jmp, 0);
            c.ops = vec![COp::Rel];
            c
        }
        O::Jcc => {
            let mut c = base_canon(Mnem::Jcc, 0);
            c.cc = cc();
            c.ops = vec![COp::Rel];
            c
        }

        O::Push => {
            let d = dst()?;
            let mut c = base_canon(Mnem::Push, 64);
            c.ops = vec![COp::Reg {
                num: x86_hw_encoding(d),
                bits: 64,
            }];
            c
        }
        O::Pop => {
            let d = dst()?;
            let mut c = base_canon(Mnem::Pop, 64);
            c.ops = vec![COp::Reg {
                num: x86_hw_encoding(d),
                bits: 64,
            }];
            c
        }

        O::Setcc => {
            let d = dst()?;
            let mut c = base_canon(Mnem::Setcc, 8);
            c.cc = cc();
            c.ops = vec![COp::Reg {
                num: x86_hw_encoding(d),
                bits: 8,
            }];
            c
        }
        O::Cmovcc => {
            let d = dst()?;
            let s = src()?;
            let mut c = base_canon(Mnem::Cmov, 64);
            c.cc = cc();
            c.ops = vec![reg_at(d, c.bits), reg_at(s, c.bits)];
            c
        }
        O::Cmovcc32 => {
            let d = dst()?;
            let s = src()?;
            let mut c = base_canon(Mnem::Cmov, 32);
            c.cc = cc();
            c.ops = vec![
                COp::Reg {
                    num: x86_hw_encoding(d),
                    bits: 32,
                },
                COp::Reg {
                    num: x86_hw_encoding(s),
                    bits: 32,
                },
            ];
            c
        }

        O::Bsf => bitscan(Mnem::Bsf, ops)?,
        O::Bsr => bitscan(Mnem::Bsr, ops)?,
        O::Tzcnt => bitscan(Mnem::Tzcnt, ops)?,
        O::Lzcnt => bitscan(Mnem::Lzcnt, ops)?,
        O::Popcnt => {
            let d = dst()?;
            let s = src()?;
            let mut c = base_canon(Mnem::Popcnt, rr_bits(d, s));
            c.ops = vec![reg_at(d, c.bits), reg_at(s, c.bits)];
            c
        }
        O::BtRI => {
            let d = dst()?;
            let mut c = base_canon(Mnem::Bt, 64);
            c.ops = vec![reg_at(d, c.bits), COp::Imm(ops.imm)];
            c
        }
        O::Bswap => {
            let d = dst()?;
            let mut c = base_canon(Mnem::Bswap, 64);
            c.ops = vec![COp::Reg {
                num: x86_hw_encoding(d),
                bits: 64,
            }];
            c
        }

        O::Xchg => {
            let d = dst()?;
            if let Some(base) = ops.base {
                let mut c = base_canon(Mnem::Xchg, if width_bits(d) == 32 { 32 } else { 64 });
                c.ops = vec![
                    COp::Mem {
                        base: Some(x86_hw_encoding(base)),
                        index: None,
                        scale: 1,
                        disp: ops.disp,
                        rip: false,
                    },
                    reg_at(d, c.bits),
                ];
                c.unordered = true;
                c
            } else {
                let s = src()?;
                let mut c = base_canon(Mnem::Xchg, rr_bits(d, s));
                c.ops = vec![reg_at(d, c.bits), reg_at(s, c.bits)];
                c.unordered = true;
                c
            }
        }
        O::Cmpxchg => {
            let d = dst()?;
            if let Some(base) = ops.base {
                let mut c = base_canon(Mnem::Cmpxchg, if width_bits(d) == 32 { 32 } else { 64 });
                c.ops = vec![
                    COp::Mem {
                        base: Some(x86_hw_encoding(base)),
                        index: None,
                        scale: 1,
                        disp: ops.disp,
                        rip: false,
                    },
                    reg_at(d, c.bits),
                ];
                c.unordered = true;
                c
            } else {
                let s = src()?;
                let mut c = base_canon(Mnem::Cmpxchg, rr_bits(d, s));
                c.ops = vec![reg_at(d, c.bits), reg_at(s, c.bits)];
                c.unordered = true;
                c
            }
        }
        O::Mfence => base_canon(Mnem::Mfence, 0),
        O::Ud2 => base_canon(Mnem::Ud2, 0),
        O::NopMulti => base_canon(Mnem::Nop, 0),

        other => return Err(format!("render_intent: {other:?} is not a covered opcode")),
    };
    Ok(c)
}

fn shift_ri(mnem: Mnem, ops: &X86InstOperands) -> Result<Canon, String> {
    let d = ops.dst.ok_or_else(|| "shift missing dst".to_string())?;
    let mut c = base_canon(mnem, ri_bits(d));
    // The encoder narrows the shift count `ops.imm as i8`; compare on that.
    c.ops = vec![reg_at(d, c.bits), COp::Imm(ops.imm as i8 as i64)];
    Ok(c)
}

fn shift_rcl(mnem: Mnem, ops: &X86InstOperands) -> Result<Canon, String> {
    let d = ops.dst.ok_or_else(|| "shift missing dst".to_string())?;
    let mut c = base_canon(mnem, ri_bits(d));
    c.ops = vec![reg_at(d, c.bits)];
    Ok(c)
}

fn mem_load(mnem: Mnem, bits: u8, ops: &X86InstOperands) -> Result<Canon, String> {
    let d = ops.dst.ok_or_else(|| "mem load missing dst".to_string())?;
    let mut c = base_canon(mnem, bits);
    c.ops = vec![
        COp::Reg {
            num: x86_hw_encoding(d),
            bits,
        },
        mem_op(ops, false)?,
    ];
    Ok(c)
}

fn mem_store(mnem: Mnem, bits: u8, ops: &X86InstOperands) -> Result<Canon, String> {
    // The store's source register is carried in `dst`.
    let s = ops.dst.ok_or_else(|| "mem store missing src".to_string())?;
    let mut c = base_canon(mnem, bits);
    c.ops = vec![
        mem_op(ops, false)?,
        COp::Reg {
            num: x86_hw_encoding(s),
            bits,
        },
    ];
    Ok(c)
}

fn movext(mnem: Mnem, src_bits: u8, ops: &X86InstOperands) -> Result<Canon, String> {
    let d = ops.dst.ok_or_else(|| "movext missing dst".to_string())?;
    let s = ops.src.ok_or_else(|| "movext missing src".to_string())?;
    let mut c = base_canon(mnem, 64);
    c.ops = vec![
        COp::Reg {
            num: x86_hw_encoding(d),
            bits: 64,
        },
        COp::Reg {
            num: x86_hw_encoding(s),
            bits: src_bits,
        },
    ];
    Ok(c)
}

fn bitscan(mnem: Mnem, ops: &X86InstOperands) -> Result<Canon, String> {
    let d = ops.dst.ok_or_else(|| "bitscan missing dst".to_string())?;
    let s = ops.src.ok_or_else(|| "bitscan missing src".to_string())?;
    let mut c = base_canon(mnem, 64);
    c.ops = vec![reg_at(d, c.bits), reg_at(s, c.bits)];
    Ok(c)
}

// ---------------------------------------------------------------------------
// Structural comparison
// ---------------------------------------------------------------------------

fn ops_equal_tolerant(a: &COp, b: &COp, skip_disp: bool) -> bool {
    match (a, b) {
        (
            COp::Mem {
                base: ba,
                index: ia,
                scale: sa,
                disp: da,
                rip: ra,
            },
            COp::Mem {
                base: bb,
                index: ib,
                scale: sb,
                disp: db,
                rip: rb,
            },
        ) => ba == bb && ia == ib && sa == sb && ra == rb && (skip_disp || da == db),
        _ => a == b,
    }
}

/// Compare a decoded Canon against an intended Canon, honoring a fixup hole.
fn compare(intended: &Canon, decoded: &Canon, hole: Option<&FixupHole>) -> Result<(), String> {
    if intended.mnem != decoded.mnem {
        return Err(format!(
            "mnemonic: intended {:?}, decoded {:?}",
            intended.mnem, decoded.mnem
        ));
    }

    // MOV r,imm: the encoder auto-selects the encoding width (zero-extend r32 /
    // movabs r64), so the intended and decoded widths legitimately differ.
    // Compare the destination register NUMBER + the width-reduced immediate
    // instead — handled BEFORE the strict width check below.
    if intended.mov_imm && decoded.mov_imm {
        return compare_mov_imm(intended, decoded);
    }

    if intended.bits != decoded.bits {
        return Err(format!(
            "operand width: intended {}b, decoded {}b",
            intended.bits, decoded.bits
        ));
    }
    if intended.cc != decoded.cc {
        return Err(format!(
            "condition code: intended {:?}, decoded {:?}",
            intended.cc, decoded.cc
        ));
    }

    if intended.ops.len() != decoded.ops.len() {
        return Err(format!(
            "operand count: intended {}, decoded {}",
            intended.ops.len(),
            decoded.ops.len()
        ));
    }

    // Whether disp comparison is skipped: a RIP-relative hole (GlobalRef /
    // ExternRefGot / TlsTlv / ConstPool) leaves a pre-patch sentinel
    // displacement. TlsTlv is the same 4-byte RIP-relative disp32 shape as
    // ExternRefGot (only the emitted relocation kind differs).
    let skip_disp = matches!(
        hole.map(|h| h.kind),
        Some(FixupHoleKind::GlobalRef)
            | Some(FixupHoleKind::ExternRefGot)
            | Some(FixupHoleKind::TlsTlv)
            | Some(FixupHoleKind::ConstPool)
    );

    if intended.unordered || decoded.unordered {
        // Set comparison of explicit operands (XCHG / CMPXCHG / TEST).
        let mut used = vec![false; decoded.ops.len()];
        for want in &intended.ops {
            let mut found = false;
            for (k, got) in decoded.ops.iter().enumerate() {
                if !used[k] && ops_equal_tolerant(want, got, skip_disp) {
                    used[k] = true;
                    found = true;
                    break;
                }
            }
            if !found {
                return Err(format!(
                    "operand {want:?} not found in decoded {:?}",
                    decoded.ops
                ));
            }
        }
    } else {
        for (k, (want, got)) in intended.ops.iter().zip(decoded.ops.iter()).enumerate() {
            if !ops_equal_tolerant(want, got, skip_disp) {
                return Err(format!("operand {k}: intended {want:?}, decoded {got:?}"));
            }
        }
    }

    // Fixup-hole placement: the recorded hole must land on the decoded field.
    if let Some(h) = hole {
        check_hole_placement(decoded, h)?;
    }

    Ok(())
}

fn compare_mov_imm(intended: &Canon, decoded: &Canon) -> Result<(), String> {
    let (COp::Reg { num: dn, .. }, COp::Imm(di)) = (&decoded.ops[0], &decoded.ops[1]) else {
        return Err("decoded MOV r,imm has an unexpected operand shape".to_string());
    };
    let (COp::Reg { num: in_, .. }, COp::Imm(ii)) = (&intended.ops[0], &intended.ops[1]) else {
        return Err("intended MOV r,imm has an unexpected operand shape".to_string());
    };
    if dn != in_ {
        return Err(format!(
            "MOV r,imm destination register: intended r{in_}, decoded r{dn}"
        ));
    }
    // The encoded width may be narrower than the intended width (zero-extend
    // alias). Require the low `enc_bits` of both immediates to agree — a wrong
    // immediate byte or wrong register is caught; the width auto-select is
    // tolerated. `bits` on the decoded side is the encoding width.
    let enc_bits = decoded.bits;
    let mask: i64 = if enc_bits >= 64 {
        -1
    } else {
        (1i64 << enc_bits) - 1
    };
    if (di & mask) != (ii & mask) {
        return Err(format!(
            "MOV r,imm value (low {enc_bits}b): intended {ii:#x}, decoded {di:#x}"
        ));
    }
    Ok(())
}

fn check_hole_placement(decoded: &Canon, hole: &FixupHole) -> Result<(), String> {
    if hole.width != 4 {
        return Err(format!("unexpected fixup hole width {}", hole.width));
    }
    let field_off = match hole.kind {
        FixupHoleKind::Branch | FixupHoleKind::Call => decoded.rel_off,
        FixupHoleKind::GlobalRef
        | FixupHoleKind::ExternRefGot
        | FixupHoleKind::TlsTlv
        | FixupHoleKind::ConstPool => decoded.disp_off,
    };
    match field_off {
        Some(off) if off == hole.offset_in_inst => Ok(()),
        Some(off) => Err(format!(
            "fixup hole ({:?}) placement: recorded offset {}, decoded field at {}",
            hole.kind, hole.offset_in_inst, off
        )),
        None => Err(format!(
            "fixup hole ({:?}) recorded at {} but the decoded instruction has no such field",
            hole.kind, hole.offset_in_inst
        )),
    }
}

// ---------------------------------------------------------------------------
// The DecodeCheck impl
// ---------------------------------------------------------------------------

/// x86-64 instantiation of the arch-neutral decode-check gate.
pub struct X86DecodeCheck;

impl DecodeCheck for X86DecodeCheck {
    type Intent = X86IntentInst;

    fn arch(&self) -> &'static str {
        "x86_64"
    }

    fn label(&self, intent: &Self::Intent) -> String {
        format!("{:?}", intent.opcode)
    }

    fn check_one(
        &self,
        intent: &Self::Intent,
        bytes: &[u8],
        hole: Option<&FixupHole>,
    ) -> DecodeCheckOutcome {
        match coverage(intent.opcode) {
            Coverage::Allowlisted(reason) => return DecodeCheckOutcome::Allowlisted(reason),
            Coverage::Covered => {}
        }

        // NopMulti is the only covered intent that may encode as more than one
        // architectural instruction (sizes 10..=15). Validate its requested
        // aggregate size and every component rather than weakening the general
        // one-intent/one-instruction length invariant below.
        if intent.opcode == X86Opcode::NopMulti {
            let requested = if intent.ops.imm > 0 {
                intent.ops.imm
            } else {
                3
            };
            let expected_len = match usize::try_from(requested) {
                Ok(len) if (1..=15).contains(&len) => len,
                _ => {
                    return DecodeCheckOutcome::Mismatch(DecodeCheckError {
                        message: format!("invalid NopMulti size {requested}"),
                    });
                }
            };
            if bytes.len() != expected_len {
                return DecodeCheckOutcome::Mismatch(DecodeCheckError {
                    message: format!(
                        "NopMulti size drift: requested {expected_len}, emitted {}",
                        bytes.len()
                    ),
                });
            }
            let expected = canonical_nop_padding(expected_len)
                .expect("validated NopMulti size must have a canonical encoding");
            return if bytes == expected {
                DecodeCheckOutcome::Match
            } else {
                DecodeCheckOutcome::Mismatch(DecodeCheckError {
                    message: format!(
                        "non-canonical NopMulti encoding: expected {expected:02x?}, got {bytes:02x?}"
                    ),
                })
            };
        }

        let intended = match render_intent(intent) {
            Ok(c) => c,
            Err(e) => {
                return DecodeCheckOutcome::Mismatch(DecodeCheckError {
                    message: format!("intent-render failed: {e}"),
                });
            }
        };
        let decoded = match decode_one(bytes) {
            Ok(c) => c,
            Err(e) => {
                return DecodeCheckOutcome::Mismatch(DecodeCheckError {
                    message: format!("undecodable ({e})"),
                });
            }
        };
        // Length drift: the decoder must consume exactly the emitted bytes.
        if decoded.len != bytes.len() {
            return DecodeCheckOutcome::Mismatch(DecodeCheckError {
                message: format!(
                    "length drift: emitted {} bytes, decoded consumed {}",
                    bytes.len(),
                    decoded.len
                ),
            });
        }
        match compare(&intended, &decoded, hole) {
            Ok(()) => DecodeCheckOutcome::Match,
            Err(e) => DecodeCheckOutcome::Mismatch(DecodeCheckError { message: e }),
        }
    }
}

// ---------------------------------------------------------------------------
// Test-only helpers (exposed for the tests/decode_check_x86.rs corpus replay)
// ---------------------------------------------------------------------------

/// Test-only: decode `bytes` and structurally compare against `intent`,
/// returning `Ok(true)` on match, `Ok(false)` on allowlist, `Err` on mismatch.
#[doc(hidden)]
pub fn check_one_for_test(
    intent: &X86IntentInst,
    bytes: &[u8],
    hole: Option<&FixupHole>,
) -> Result<bool, String> {
    match X86DecodeCheck.check_one(intent, bytes, hole) {
        DecodeCheckOutcome::Match => Ok(true),
        DecodeCheckOutcome::Allowlisted(_) => Ok(false),
        DecodeCheckOutcome::Mismatch(e) => Err(e.message),
    }
}
