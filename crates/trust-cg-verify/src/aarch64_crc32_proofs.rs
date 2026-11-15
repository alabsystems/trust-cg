// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// Reference: Arm DDI 0487 (L.a), C6.2 CRC32B/CRC32H/CRC32W/CRC32X and
//            CRC32CB/CRC32CH/CRC32CW/CRC32CX, shared pseudocode `BitReverse`
//            and `Poly32Mod2`; C4.1 "Data-processing (2 source)".

//! Decoded-word value obligations for the eight emitted FEAT_CRC32 forms
//! (`CRC32{B,H,W,X}`, `CRC32C{B,H,W,X}`; ledger `L04-P1`).
//!
//! # What is emitted
//!
//! Instruction selection lowers `Opcode::Crc32 { bytes, castagnoli }` (the
//! `llvm.aarch64.crc32*` intrinsics) to one `CRC32*`/`CRC32C*` instruction
//! `[Wd, Wn, Wm|Xm]` when the function admits FEAT_CRC32: the accumulator is
//! `Wn`, the data is the low `8 * bytes` bits of `Wm` (`Xm` for 8 bytes), and
//! `Wd` receives the 32-bit result, `Xd[63:32]` cleared.
//!
//! # The obligation
//!
//! For one instruction, the 64-bit value its WORD leaves in `Xd` equals the
//! value the machine-IR instruction names, for every value of every register:
//!
//! * the word is re-derived from the operands by this module's encoder
//!   ([`crc32_word`], written from the "Data-processing (2 source)" diagram),
//!   and per compile ENC-5 (`trust-cg-codegen` `decode_check`) requires the
//!   emitted word to be exactly that word ([`check_emitted_crc32_word`]);
//! * the word is decoded by an independent field decoder
//!   ([`decode_crc32_word`], which also enforces the `sf`/`sz` UNDEFINED rows)
//!   and given its Arm ARM pseudocode ([`denote_crc32`]): `BitReverse` of the
//!   accumulator and of the data, each padded with zeros, XOR-ed, divided by
//!   the polynomial (`0x04C11DB7` or `0x1EDC6F41`) bit by bit from the top
//!   (`Poly32Mod2`), and bit-reversed back; register 31 reads as zero and a
//!   write to it is discarded;
//! * the intent ([`crc32_intent`]) is the reflected, least-significant-bit-
//!   first shift register the intrinsic is specified by (ACLE): for each data
//!   byte from the lowest, `crc ^= byte`, then eight times
//!   `crc = (crc >> 1) ^ (crc & 1 ? P : 0)` with the bit-reversed polynomial
//!   `P` written as its literal (`0xEDB88320`, `0x82F63B78`), never computed
//!   from the Arm constant.
//!
//! The two sides share no term: the machine side divides from the most
//! significant end of bit-reversed operands, the intent shifts right from the
//! least significant end, so a wrong polynomial, width, byte order, bit order,
//! operand order or a missing data XOR refutes ([`crc32_controls`]).
//!
//! # How it is decided, and what that is worth
//!
//! Both sides are affine over GF(2) in the register bits, and
//! [`crate::gf2_affine_decide`] decides their equality EXACTLY, for every
//! register value, by computing every result bit as an XOR of input bits (the
//! unrolled division shares each remainder by reference, so the 64-step
//! division of `CRC32X` is linear in size). A refutation carries a witness the
//! separate concrete evaluator confirms. This is an in-process decision by
//! unverified Rust code: testing-grade evidence, never proof credit. The
//! function verifier reports a holding instruction unverified
//! ([`CRC32_DECIDED_IS_NOT_CREDIT`]); the coverage gate counts the opcode rows
//! as accepted regression evidence, not as a formal proof.
//!
//! # What it does not establish
//!
//! That instruction selection chose the right intrinsic, operands or
//! registers (a wrong choice encodes and decodes perfectly); that the CPU
//! implements FEAT_CRC32 (the function's feature admission is trusted); any
//! dataflow fact about the registers. The silicon differential
//! (`tests/aarch64_crc32_silicon_differential.rs`) samples the models against
//! this CPU.

use std::collections::HashMap;
use std::sync::{Arc, OnceLock};

use crate::gf2_affine_decide::{self as gf2, Gf2Error, Gf2Exact};
use crate::smt::SmtExpr;
use trust_cg_ir::{AArch64Opcode as O, MachInst, MachOperand, PReg, RegClass, SpecialReg, VReg};

/// The eight emitted CRC32 opcodes, in [`Crc32Form::ALL`] order.
pub const CRC32_OPCODES: [O; 8] = [
    O::Crc32B,
    O::Crc32H,
    O::Crc32W,
    O::Crc32X,
    O::Crc32Cb,
    O::Crc32Ch,
    O::Crc32Cw,
    O::Crc32Cx,
];

/// Reason prefix of a holding CRC32 row the function verifier does not credit.
pub const CRC32_DECIDED_IS_NOT_CREDIT: &str = "CRC32 decoded-word obligation is decided in \
     process (GF(2)-affine, every register value), which is testing-grade evidence, not proof \
     credit";

/// How a holding obligation was decided.
pub const METHOD_GF2: &str =
    "decided in-process for every register value by GF(2)-affine evaluation";

// ===========================================================================
// Forms
// ===========================================================================

/// One emitted CRC32 form: the polynomial and the data width.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Crc32Form {
    /// `C`: the Castagnoli polynomial (`CRC32C*`).
    pub castagnoli: bool,
    /// `sz`: log2 of the data bytes (B=0, H=1, W=2, X=3).
    pub sz: u32,
}

impl Crc32Form {
    /// Every form, in [`CRC32_OPCODES`] order.
    pub const ALL: [Self; 8] = [
        Self::new(false, 0),
        Self::new(false, 1),
        Self::new(false, 2),
        Self::new(false, 3),
        Self::new(true, 0),
        Self::new(true, 1),
        Self::new(true, 2),
        Self::new(true, 3),
    ];

    const fn new(castagnoli: bool, sz: u32) -> Self {
        Self { castagnoli, sz }
    }

    /// The form of a CRC32 opcode.
    pub fn from_opcode(opcode: O) -> Option<Self> {
        CRC32_OPCODES
            .iter()
            .position(|&op| op == opcode)
            .map(|i| Self::ALL[i])
    }

    /// The opcode of this form.
    pub fn opcode(self) -> O {
        CRC32_OPCODES[Self::ALL
            .iter()
            .position(|&form| form == self)
            .expect("every form is in ALL")]
    }

    /// Data bits read from `Rm`.
    pub fn data_bits(self) -> u32 {
        8 << self.sz
    }

    /// `sf`: 1 exactly for the doubleword forms.
    pub fn sf(self) -> u32 {
        u32::from(self.sz == 3)
    }

    /// The Arm mnemonic.
    pub fn mnemonic(self) -> &'static str {
        const NAMES: [&str; 8] = [
            "CRC32B", "CRC32H", "CRC32W", "CRC32X", "CRC32CB", "CRC32CH", "CRC32CW", "CRC32CX",
        ];
        NAMES[usize::from(self.castagnoli) * 4 + self.sz as usize]
    }
}

// ===========================================================================
// Encoder and independent decoder
// ===========================================================================

/// The word of `CRC32{C}{B,H,W,X} Wd, Wn, {W,X}m` from the Arm A64
/// "Data-processing (2 source)" diagram:
/// `sf | op=0 | S=0 | 11010110 | Rm | opcode = 010 C sz | Rn | Rd`.
pub fn crc32_word(form: Crc32Form, rd: u32, rn: u32, rm: u32) -> u32 {
    const DP2_CLASS: u32 = 0b1101_0110; // bits 28:21
    let opcode = (0b010 << 3) | (u32::from(form.castagnoli) << 2) | form.sz;
    (form.sf() << 31)
        | (DP2_CLASS << 21)
        | ((rm & 31) << 16)
        | (opcode << 10)
        | ((rn & 31) << 5)
        | (rd & 31)
}

/// The fields of a decoded CRC32 word.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DecodedCrc32 {
    pub sf: u32,
    pub rm: u32,
    pub c: u32,
    pub sz: u32,
    pub rn: u32,
    pub rd: u32,
}

impl DecodedCrc32 {
    /// The form the word encodes.
    pub fn form(&self) -> Crc32Form {
        Crc32Form {
            castagnoli: self.c == 1,
            sz: self.sz,
        }
    }
}

/// Why a word is not a CRC32 instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Crc32DecodeRefusal {
    /// Not in the "Data-processing (2 source)" class.
    NotDataProcessing2Source,
    /// Another instruction of that class (division, variable shift, PAC...).
    OtherInstruction { s: u32, opcode: u32 },
    /// A CRC32 encoding the architecture leaves UNDEFINED.
    Unallocated(&'static str),
}

const fn bits(word: u32, hi: u32, lo: u32) -> u32 {
    (word >> lo) & ((1 << (hi - lo + 1)) - 1)
}

/// Decode a word as a CRC32 instruction, from the encoding tables.
pub fn decode_crc32_word(word: u32) -> Result<DecodedCrc32, Crc32DecodeRefusal> {
    // op0 (bit 30) = 0, op1 (bit 28) = 1, op2 (bits 24:21) = 0110, and bits
    // 27:25 = 101 for the data-processing (register) group.
    if bits(word, 30, 30) != 0 || bits(word, 28, 21) != 0b1101_0110 {
        return Err(Crc32DecodeRefusal::NotDataProcessing2Source);
    }
    let s = bits(word, 29, 29);
    let opcode = bits(word, 15, 10);
    if s != 0 || opcode >> 3 != 0b010 {
        return Err(Crc32DecodeRefusal::OtherInstruction { s, opcode });
    }
    let decoded = DecodedCrc32 {
        sf: bits(word, 31, 31),
        rm: bits(word, 20, 16),
        c: bits(word, 12, 12),
        sz: bits(word, 11, 10),
        rn: bits(word, 9, 5),
        rd: bits(word, 4, 0),
    };
    // Shared decode: `if sf == '1' && sz != '11' then UNDEFINED;
    // if sf == '0' && sz == '11' then UNDEFINED;`
    if decoded.sf == 1 && decoded.sz != 0b11 {
        return Err(Crc32DecodeRefusal::Unallocated(
            "CRC32 with sf = 1 and a data size other than doubleword",
        ));
    }
    if decoded.sf == 0 && decoded.sz == 0b11 {
        return Err(Crc32DecodeRefusal::Unallocated(
            "CRC32 doubleword data size with sf = 0",
        ));
    }
    Ok(decoded)
}

// ===========================================================================
// Shared-term helpers
// ===========================================================================

fn bv(value: u64, width: u32) -> SmtExpr {
    SmtExpr::bv_const(value, width)
}

/// `X<n>` as a 64-bit state variable (the naming every A64 value obligation
/// in this crate uses).
pub fn xvar(n: u32) -> SmtExpr {
    SmtExpr::var(format!("x{n}"), 64)
}

/// `operand<high:low>` without copying the operand's top node.
fn slice(operand: &Arc<SmtExpr>, high: u32, low: u32) -> SmtExpr {
    SmtExpr::Extract {
        high,
        low,
        operand: Arc::clone(operand),
        width: high - low + 1,
    }
}

// ===========================================================================
// Machine side: the Arm ARM pseudocode of the decoded word
// ===========================================================================

/// `X[n, width]` in a context where register 31 is the zero register.
fn read_zr(n: u32, width: u32) -> SmtExpr {
    if n == 31 {
        bv(0, width)
    } else {
        xvar(n).extract(width - 1, 0)
    }
}

/// `BitReverse(x)`: `result<i> = x<width-1-i>`, as a concatenation of the
/// operand's single bits.
fn bit_reverse(x: SmtExpr) -> SmtExpr {
    let width = x.bv_width();
    let x = Arc::new(x);
    (1..width).fold(slice(&x, 0, 0), |acc, i| acc.concat(slice(&x, i, i)))
}

/// `Poly32Mod2(data, poly)`:
///
/// ```text
/// for i = N-1 downto 32
///     if data<i> == '1' then
///         data<i-1:0> = data<i-1:0> EOR (poly:Zeros(i-32));
/// return data<31:0>;
/// ```
///
/// Each step reads the previous remainder three times by reference.
fn poly32_mod2(data: SmtExpr, poly: u32) -> SmtExpr {
    let n = data.bv_width();
    let mut data = Arc::new(data);
    for i in (32..n).rev() {
        let top = slice(&data, n - 1, i);
        let set = slice(&data, i, i).eq_expr(bv(1, 1));
        let low = Arc::new(slice(&data, i - 1, 0));
        // poly:Zeros(i-32), an i-bit constant.
        let divisor = if i > 32 {
            bv(u64::from(poly), 32).concat(bv(0, i - 32))
        } else {
            bv(u64::from(poly), 32)
        };
        let reduced = SmtExpr::BvXor {
            lhs: Arc::clone(&low),
            rhs: Arc::new(divisor),
            width: i,
        };
        let low = SmtExpr::Ite {
            cond: Arc::new(set),
            then_expr: Arc::new(reduced),
            else_expr: low,
        };
        data = Arc::new(top.concat(low));
    }
    slice(&data, 31, 0)
}

/// What a decoded CRC32 word writes.
///
/// No `PartialEq`, and a `Debug` that omits the term: the value is a shared
/// DAG, and a derived comparison or print walks it as an exponential tree.
#[derive(Clone)]
pub struct Crc32Effect {
    /// The general-purpose register written, or `None` when `Rd` is the zero
    /// register (the write is discarded).
    pub dest: Option<u8>,
    /// The 64-bit value of `X<d>` after the instruction.
    pub value: SmtExpr,
}

/// The Arm ARM pseudocode of a decoded CRC32 word:
///
/// ```text
/// bits(32)      acc     = X[n, 32];
/// bits(size)    val     = X[m, size];
/// bits(32)      poly    = (if crc32c then 0x1EDC6F41 else 0x04C11DB7)<31:0>;
/// bits(32+size) tempacc = BitReverse(acc):Zeros(size);
/// bits(size+32) tempval = BitReverse(val):Zeros(32);
/// X[d, 32] = BitReverse(Poly32Mod2(tempacc EOR tempval, poly));
/// ```
pub fn denote_crc32(decoded: &DecodedCrc32) -> Crc32Effect {
    let size = 8 << decoded.sz;
    let poly: u32 = if decoded.c == 1 {
        0x1EDC_6F41
    } else {
        0x04C1_1DB7
    };
    let acc = read_zr(decoded.rn, 32);
    let val = read_zr(decoded.rm, size);
    let tempacc = bit_reverse(acc).concat(bv(0, size));
    let tempval = bit_reverse(val).concat(bv(0, 32));
    let result = bit_reverse(poly32_mod2(tempacc.bvxor(tempval), poly));
    // A 32-bit general-purpose write zeroes Xd[63:32].
    Crc32Effect {
        dest: (decoded.rd != 31).then_some(decoded.rd as u8),
        value: result.zero_ext(32),
    }
}

// ===========================================================================
// Intent: the machine-IR instruction and the reflected shift register
// ===========================================================================

/// The bit-reversed IEEE 802.3 polynomial, as the ACLE intrinsic's reference
/// algorithm spells it.
pub const REFLECTED_IEEE: u32 = 0xEDB8_8320;
/// The bit-reversed Castagnoli polynomial.
pub const REFLECTED_CASTAGNOLI: u32 = 0x82F6_3B78;

/// The CRC update the intrinsic specifies, over a 32-bit accumulator term and
/// a data term of the form's width: bytes from the lowest, each XOR-ed into
/// the low byte and shifted out bit by bit through the reflected polynomial.
pub fn reflected_crc(crc: SmtExpr, data: SmtExpr, reflected_poly: u32) -> SmtExpr {
    let data = Arc::new(data);
    let mut crc = Arc::new(crc);
    for byte in 0..data.bv_width() / 8 {
        let lane = slice(&data, 8 * byte + 7, 8 * byte).zero_ext(24);
        crc = Arc::new(SmtExpr::BvXor {
            lhs: crc,
            rhs: Arc::new(lane),
            width: 32,
        });
        crc = shift_out(crc, 8, reflected_poly);
    }
    (*crc).clone()
}

/// `steps` iterations of `crc = (crc >> 1) ^ (crc & 1 ? poly : 0)`.
fn shift_out(mut crc: Arc<SmtExpr>, steps: u32, reflected_poly: u32) -> Arc<SmtExpr> {
    for _ in 0..steps {
        let lsb = slice(&crc, 0, 0).eq_expr(bv(1, 1));
        let shifted = Arc::new(SmtExpr::BvLshr {
            lhs: crc,
            rhs: Arc::new(bv(1, 32)),
            width: 32,
        });
        crc = Arc::new(SmtExpr::Ite {
            cond: Arc::new(lsb),
            then_expr: Arc::new(SmtExpr::BvXor {
                lhs: Arc::clone(&shifted),
                rhs: Arc::new(bv(u64::from(reflected_poly), 32)),
                width: 32,
            }),
            else_expr: shifted,
        });
    }
    crc
}

/// A general-purpose operand of a CRC32 instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Gpr {
    /// `W<n>`/`X<n>` with its view width.
    Reg { n: u8, width: u32 },
    /// `WZR`/`XZR` with its view width.
    Zero { width: u32 },
}

impl Gpr {
    fn field(self) -> u32 {
        match self {
            Self::Reg { n, .. } => u32::from(n),
            Self::Zero { .. } => 31,
        }
    }

    fn width(self) -> u32 {
        match self {
            Self::Reg { width, .. } | Self::Zero { width } => width,
        }
    }

    /// The low `width` bits the operand names.
    fn value(self, width: u32) -> SmtExpr {
        match self {
            Self::Reg { n, .. } => xvar(u32::from(n)).extract(width - 1, 0),
            Self::Zero { .. } => bv(0, width),
        }
    }
}

fn gpr(op: &MachOperand) -> Result<Gpr, Crc32CheckError> {
    match op {
        MachOperand::PReg(p) => match p.encoding() {
            e @ 0..=30 => Ok(Gpr::Reg {
                n: e as u8,
                width: 64,
            }),
            e @ 32..=62 => Ok(Gpr::Reg {
                n: (e - 32) as u8,
                width: 32,
            }),
            160 => Ok(Gpr::Zero { width: 64 }),
            161 => Ok(Gpr::Zero { width: 32 }),
            31 | 63 => Err(Crc32CheckError::IllFormed(
                "the stack pointer is not a CRC32 operand (register 31 is ZR)".into(),
            )),
            e => Err(Crc32CheckError::IllFormed(format!(
                "physical register encoding {e} is not a general-purpose register"
            ))),
        },
        MachOperand::Special(SpecialReg::XZR) => Ok(Gpr::Zero { width: 64 }),
        MachOperand::Special(SpecialReg::WZR) => Ok(Gpr::Zero { width: 32 }),
        MachOperand::Special(SpecialReg::SP) => Err(Crc32CheckError::IllFormed(
            "the stack pointer is not a CRC32 operand (register 31 is ZR)".into(),
        )),
        other => Err(Crc32CheckError::OutOfModel(format!(
            "unmodeled CRC32 operand {other:?}"
        ))),
    }
}

/// The machine-IR intent of a CRC32 instruction, with the register fields
/// its word must carry. Like [`Crc32Effect`], neither compared nor printed
/// through its term.
#[derive(Clone)]
pub struct Crc32Intent {
    pub form: Crc32Form,
    pub rd: u32,
    pub rn: u32,
    pub rm: u32,
    /// The register written, `None` for the zero register.
    pub dest: Option<u8>,
    /// The 64-bit value of `X<d>` after the instruction.
    pub value: SmtExpr,
}

impl std::fmt::Debug for Crc32Effect {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Crc32Effect")
            .field("dest", &self.dest)
            .finish_non_exhaustive()
    }
}

impl std::fmt::Debug for Crc32Intent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Crc32Intent")
            .field("form", &self.form)
            .field("rd", &self.rd)
            .field("rn", &self.rn)
            .field("rm", &self.rm)
            .field("dest", &self.dest)
            .finish_non_exhaustive()
    }
}

/// Number virtual registers as distinct physical ones (each class keeps its
/// view), avoiding the physical registers the instruction already names, so a
/// pre-allocation instruction is judged with the aliasing it states.
fn with_virtual_registers_numbered(inst: &MachInst) -> Result<MachInst, Crc32CheckError> {
    let mut used: Vec<u16> = inst
        .operands
        .iter()
        .filter_map(|op| match op {
            MachOperand::PReg(p) if matches!(p.encoding(), 0..=30 | 32..=62) => {
                Some(p.encoding() % 32)
            }
            _ => None,
        })
        .collect();
    let mut seen: Vec<(VReg, u16)> = Vec::new();
    let mut operands = Vec::with_capacity(inst.operands.len());
    for op in &inst.operands {
        let MachOperand::VReg(v) = op else {
            operands.push(op.clone());
            continue;
        };
        let base = match v.class {
            RegClass::Gpr64 => 0,
            RegClass::Gpr32 => 32,
            other => {
                return Err(Crc32CheckError::IllFormed(format!(
                    "virtual register class {other:?} is not a general-purpose register"
                )));
            }
        };
        let n = match seen.iter().find(|(known, _)| known == v) {
            Some(&(_, n)) => n,
            None => {
                let n = (0..31u16)
                    .find(|n| !used.contains(n))
                    .ok_or_else(|| Crc32CheckError::OutOfModel("too many registers".into()))?;
                used.push(n);
                seen.push((*v, n));
                n
            }
        };
        operands.push(MachOperand::PReg(PReg::new(base + n)));
    }
    Ok(MachInst::new(inst.opcode, operands))
}

/// The intent of a CRC32 instruction `[Wd, Wn, Wm|Xm]`: `Xd` receives the
/// reflected CRC of `Wn` over the low data bits of `Rm`, zero-extended.
///
/// The destination and accumulator must be W views and the data a W view (an
/// X view for the doubleword forms), as instruction selection emits them;
/// any other view is outside the model (no claim either way). A virtual
/// register is numbered apart from every other register.
pub fn crc32_intent(inst: &MachInst) -> Result<Crc32Intent, Crc32CheckError> {
    let form = Crc32Form::from_opcode(inst.opcode).ok_or_else(|| {
        Crc32CheckError::OutOfModel(format!("{:?} is not a CRC32 opcode", inst.opcode))
    })?;
    if inst.operands.len() != 3 {
        return Err(Crc32CheckError::IllFormed(format!(
            "{:?} with {} operands (CRC32 takes [Wd, Wn, Wm|Xm])",
            inst.opcode,
            inst.operands.len()
        )));
    }
    let inst = with_virtual_registers_numbered(inst)?;
    let [d, n, m] = [0, 1, 2].map(|i| gpr(&inst.operands[i]));
    let (d, n, m) = (d?, n?, m?);
    let data_view = if form.sz == 3 { 64 } else { 32 };
    if d.width() != 32 || n.width() != 32 || m.width() != data_view {
        return Err(Crc32CheckError::OutOfModel(format!(
            "{} with register views W{}/W{}/{} (expected Wd, Wn, {}m)",
            form.mnemonic(),
            d.width(),
            n.width(),
            m.width(),
            if data_view == 64 { "X" } else { "W" }
        )));
    }
    let reflected = if form.castagnoli {
        REFLECTED_CASTAGNOLI
    } else {
        REFLECTED_IEEE
    };
    let crc = reflected_crc(n.value(32), m.value(form.data_bits()), reflected);
    Ok(Crc32Intent {
        form,
        rd: d.field(),
        rn: n.field(),
        rm: m.field(),
        dest: match d {
            Gpr::Reg { n, .. } => Some(n),
            Gpr::Zero { .. } => None,
        },
        value: bv(0, 32).concat(crc),
    })
}

// ===========================================================================
// The per-word check
// ===========================================================================

/// The reason class of a refutation; each control names the class it must be
/// refuted for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Crc32RefusalClass {
    /// Not a CRC32 word at all.
    NotDecoded,
    /// A CRC32 encoding the architecture leaves UNDEFINED.
    Unallocated,
    /// The word writes another register (or discards the write).
    Destination,
    /// The written value differs for some register state.
    Value,
}

/// Why a word was not accepted for an instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Crc32CheckError {
    /// The instruction's shape is outside the model: no claim either way.
    OutOfModel(String),
    /// The instruction names something no CRC32 word does. Fails closed.
    IllFormed(String),
    /// The word does not denote the intent. Fails closed.
    Refuted {
        class: Crc32RefusalClass,
        detail: String,
    },
    /// The decision procedure refused the terms.
    Undecided(String),
}

impl std::fmt::Display for Crc32CheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfModel(why) => write!(f, "outside the CRC32 model: {why}"),
            Self::IllFormed(why) => write!(f, "ill-formed CRC32 instruction: {why}"),
            Self::Refuted { class, detail } => write!(f, "refuted ({class:?}): {detail}"),
            Self::Undecided(why) => write!(f, "undecided: {why}"),
        }
    }
}

fn refuted(class: Crc32RefusalClass, detail: impl Into<String>) -> Crc32CheckError {
    Crc32CheckError::Refuted {
        class,
        detail: detail.into(),
    }
}

/// Decide whether `word` performs `intent` for every register value.
pub fn check_word_against_intent(intent: &Crc32Intent, word: u32) -> Result<(), Crc32CheckError> {
    let decoded = decode_crc32_word(word).map_err(|refusal| match refusal {
        Crc32DecodeRefusal::Unallocated(why) => refuted(Crc32RefusalClass::Unallocated, why),
        other => refuted(
            Crc32RefusalClass::NotDecoded,
            format!("{word:#010x} is not a CRC32 word: {other:?}"),
        ),
    })?;
    let effect = denote_crc32(&decoded);
    if effect.dest != intent.dest {
        return Err(refuted(
            Crc32RefusalClass::Destination,
            format!(
                "{word:#010x} writes {:?}, the instruction writes {:?}",
                effect.dest, intent.dest
            ),
        ));
    }
    if effect.dest.is_none() {
        // Both discard the write: no register changes.
        return Ok(());
    }
    match gf2::decide_equal(&effect.value, &intent.value) {
        Ok(Gf2Exact::Holds) => Ok(()),
        Ok(Gf2Exact::Refuted(witness)) => Err(refuted(
            Crc32RefusalClass::Value,
            format!(
                "{word:#010x} ({}) differs from the {} intent at {}",
                decoded.form().mnemonic(),
                intent.form.mnemonic(),
                witness
                    .iter()
                    .map(|(name, value)| format!("{name}={value:#x}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        )),
        Err(error @ (Gf2Error::Unsupported(_) | Gf2Error::Disagreement(_))) => {
            Err(Crc32CheckError::Undecided(error.to_string()))
        }
    }
}

/// The word this module re-derives for an instruction, with its intent.
pub fn crc32_instance(inst: &MachInst) -> Result<(Crc32Intent, u32), Crc32CheckError> {
    let intent = crc32_intent(inst)?;
    let word = crc32_word(intent.form, intent.rd, intent.rn, intent.rm);
    Ok((intent, word))
}

/// The walk's verdict for one CRC32 instruction: the re-derived word decided
/// against the operands' intent. `None` for every other opcode.
pub fn crc32_verdict(inst: &MachInst) -> Option<Result<u32, Crc32CheckError>> {
    Crc32Form::from_opcode(inst.opcode)?;
    Some(
        crc32_instance(inst)
            .and_then(|(intent, word)| check_word_against_intent(&intent, word).map(|()| word)),
    )
}

/// ENC-5's per-compile binding: for an admitted CRC32 instruction the emitted
/// word must be exactly the re-derived word and hold against the intent.
/// `None` for other opcodes and for shapes outside the model (no claim);
/// `Some(Err)` names the mismatch, refutation or ill-formed operand.
pub fn check_emitted_crc32_word(inst: &MachInst, emitted: u32) -> Option<Result<(), String>> {
    Crc32Form::from_opcode(inst.opcode)?;
    let (intent, word) = match crc32_instance(inst) {
        Ok(instance) => instance,
        Err(Crc32CheckError::OutOfModel(_)) => return None,
        Err(error) => return Some(Err(error.to_string())),
    };
    if emitted != word {
        return Some(Err(format!(
            "emitted {} word {emitted:#010x} is not the verified word {word:#010x}",
            intent.form.mnemonic()
        )));
    }
    Some(check_word_against_intent(&intent, emitted).map_err(|error| error.to_string()))
}

// ===========================================================================
// Controls
// ===========================================================================

/// A deliberately wrong intent, each of which must be refuted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Crc32IntentMutation {
    /// The non-reflected (most-significant-bit-first) shift register with the
    /// normal polynomial, on the same operands.
    MsbFirst,
    /// The right-shifting register with the NORMAL (unreflected) polynomial.
    UnreflectedConstant,
    /// The other polynomial's reflected constant.
    OtherPolynomial,
    /// Data bytes processed from the highest (multi-byte forms only).
    HighByteFirst,
    /// The data XOR dropped (the accumulator shifted alone).
    DroppedData,
    /// Only the low byte of the data read (multi-byte forms only).
    TruncatedData,
    /// zlib-style complement before and after (not part of the instruction).
    Complemented,
    /// Accumulator and data registers exchanged.
    SwappedOperands,
}

impl Crc32IntentMutation {
    /// Every mutation.
    pub const ALL: [Self; 8] = [
        Self::MsbFirst,
        Self::UnreflectedConstant,
        Self::OtherPolynomial,
        Self::HighByteFirst,
        Self::DroppedData,
        Self::TruncatedData,
        Self::Complemented,
        Self::SwappedOperands,
    ];

    /// Whether the mutation changes the meaning of this form's intent.
    ///
    /// Byte order and truncation mean nothing for one data byte. Exchanging
    /// the operands means nothing for the word forms: `CRC32W`/`CRC32CW` pad
    /// the accumulator and the 32-bit data identically (`BitReverse(x):Zeros(32)`)
    /// before XOR-ing them, so their result is a function of `acc XOR data`
    /// alone and is symmetric in the two registers (the GF(2) decision proves
    /// the exchanged forms equal).
    pub fn applies_to(self, form: Crc32Form) -> bool {
        match self {
            Self::HighByteFirst | Self::TruncatedData => form.sz > 0,
            Self::SwappedOperands => form.sz != 2,
            _ => true,
        }
    }
}

/// The non-reflected (MSB-first) CRC with the normal polynomial: each data
/// byte, lowest first, XOR-ed into the TOP byte, then eight times
/// `crc = (crc << 1) ^ (crc<31> ? poly : 0)`. Only the byte order agrees with
/// the intent.
fn msb_first_crc(crc: SmtExpr, data: SmtExpr, poly: u32) -> SmtExpr {
    let data = Arc::new(data);
    let mut crc = Arc::new(crc);
    for byte in 0..data.bv_width() / 8 {
        let lane = slice(&data, 8 * byte + 7, 8 * byte).concat(bv(0, 24));
        crc = Arc::new(SmtExpr::BvXor {
            lhs: crc,
            rhs: Arc::new(lane),
            width: 32,
        });
        for _ in 0..8 {
            let msb = slice(&crc, 31, 31).eq_expr(bv(1, 1));
            let shifted = Arc::new(SmtExpr::BvShl {
                lhs: crc,
                rhs: Arc::new(bv(1, 32)),
                width: 32,
            });
            crc = Arc::new(SmtExpr::Ite {
                cond: Arc::new(msb),
                then_expr: Arc::new(SmtExpr::BvXor {
                    lhs: Arc::clone(&shifted),
                    rhs: Arc::new(bv(u64::from(poly), 32)),
                    width: 32,
                }),
                else_expr: shifted,
            });
        }
    }
    (*crc).clone()
}

/// The intent of `inst` under `mutation`, or `None` when it does not apply.
pub fn mutated_intent(
    inst: &MachInst,
    mutation: Crc32IntentMutation,
) -> Option<Result<Crc32Intent, Crc32CheckError>> {
    let intent = match crc32_intent(inst) {
        Ok(intent) => intent,
        Err(error) => return Some(Err(error)),
    };
    let form = intent.form;
    if !mutation.applies_to(form) {
        return None;
    }
    let size = form.data_bits();
    let read = |field: u32, width: u32| read_zr(field, width);
    let (acc, data) = (read(intent.rn, 32), read(intent.rm, size));
    let (reflected, other, normal) = if form.castagnoli {
        (REFLECTED_CASTAGNOLI, REFLECTED_IEEE, 0x1EDC_6F41)
    } else {
        (REFLECTED_IEEE, REFLECTED_CASTAGNOLI, 0x04C1_1DB7)
    };
    let crc = match mutation {
        Crc32IntentMutation::MsbFirst => msb_first_crc(acc, data, normal),
        Crc32IntentMutation::UnreflectedConstant => reflected_crc(acc, data, normal),
        Crc32IntentMutation::OtherPolynomial => reflected_crc(acc, data, other),
        Crc32IntentMutation::HighByteFirst => {
            let data = Arc::new(data);
            let reversed = (1..size / 8).fold(slice(&data, 7, 0), |acc, byte| {
                acc.concat(slice(&data, 8 * byte + 7, 8 * byte))
            });
            reflected_crc(acc, reversed, reflected)
        }
        Crc32IntentMutation::DroppedData => (*shift_out(Arc::new(acc), size, reflected)).clone(),
        Crc32IntentMutation::TruncatedData => {
            reflected_crc(acc, data.extract(7, 0).zero_ext(size - 8), reflected)
        }
        Crc32IntentMutation::Complemented => {
            let all = bv(u64::from(u32::MAX), 32);
            reflected_crc(acc.bvxor(all.clone()), data, reflected).bvxor(all)
        }
        Crc32IntentMutation::SwappedOperands => {
            // The data register's low 32 bits as the accumulator, the
            // accumulator register (zero-extended) as the data.
            let swapped_acc = read(intent.rm, 32);
            let swapped_data = read(intent.rn, 32);
            let swapped_data = if size >= 32 {
                swapped_data.zero_ext(size - 32)
            } else {
                swapped_data.extract(size - 1, 0)
            };
            reflected_crc(swapped_acc, swapped_data, reflected)
        }
    };
    Some(Ok(Crc32Intent {
        value: bv(0, 32).concat(crc),
        ..intent
    }))
}

/// One negative control: a word or intent that must be refuted for `class`
/// (or for any reason, when `class` is `None`).
#[derive(Debug, Clone)]
pub struct Crc32Control {
    pub form: Crc32Form,
    pub label: String,
    pub word: u32,
    pub intent: Crc32Intent,
    pub class: Option<Crc32RefusalClass>,
}

/// The canonical instruction of a form after register allocation:
/// `CRC32* W0, W1, W2|X2`.
pub fn representative_instruction(form: Crc32Form, rd: u32, rn: u32, rm: u32) -> MachInst {
    let w = |n: u32| {
        if n == 31 {
            MachOperand::Special(SpecialReg::WZR)
        } else {
            MachOperand::PReg(PReg::new(32 + n as u16))
        }
    };
    let data = if form.sz == 3 {
        if rm == 31 {
            MachOperand::Special(SpecialReg::XZR)
        } else {
            MachOperand::PReg(PReg::new(rm as u16))
        }
    } else {
        w(rm)
    };
    MachInst::new(form.opcode(), vec![w(rd), w(rn), data])
}

/// The register assignments every form is decided over: distinct registers,
/// destination aliasing either source, both sources equal, the zero register
/// in each position, and the highest registers.
pub const REGISTER_BATTERY: [(u32, u32, u32); 8] = [
    (0, 1, 2),
    (3, 3, 4),
    (5, 6, 5),
    (7, 8, 8),
    (9, 31, 10),
    (11, 12, 31),
    (31, 13, 14),
    (30, 29, 28),
];

/// Every negative control: for each form, every single-bit flip of its
/// canonical word, the neighbouring width and polynomial words, the
/// swapped-operand word, a wrong destination, and every applicable intent
/// mutation.
pub fn crc32_controls() -> Vec<Crc32Control> {
    use Crc32RefusalClass as C;
    let mut out = Vec::new();
    for form in Crc32Form::ALL {
        let inst = representative_instruction(form, 0, 1, 2);
        let intent = crc32_intent(&inst).expect("the representative is in the model");
        let word = crc32_word(form, 0, 1, 2);
        for bit in 0..32 {
            out.push(Crc32Control {
                form,
                label: format!("{} word bit {bit} flipped", form.mnemonic()),
                word: word ^ (1 << bit),
                intent: intent.clone(),
                class: None,
            });
        }
        // The neighbouring widths keep a legal sf, so they refute on value.
        for sz in (0..4).filter(|&sz| sz != form.sz) {
            let other = Crc32Form { sz, ..form };
            out.push(Crc32Control {
                form,
                label: format!("{} word for {}", other.mnemonic(), form.mnemonic()),
                word: crc32_word(other, 0, 1, 2),
                intent: intent.clone(),
                class: Some(C::Value),
            });
        }
        let other_poly = Crc32Form {
            castagnoli: !form.castagnoli,
            ..form
        };
        out.push(Crc32Control {
            form,
            label: format!("{} word for {}", other_poly.mnemonic(), form.mnemonic()),
            word: crc32_word(other_poly, 0, 1, 2),
            intent: intent.clone(),
            class: Some(C::Value),
        });
        // The word forms are symmetric in Rn and Rm (see
        // `Crc32IntentMutation::applies_to`), so the exchanged word is a
        // control only for the other widths.
        if form.sz != 2 {
            out.push(Crc32Control {
                form,
                label: format!("{} with Rn and Rm swapped", form.mnemonic()),
                word: crc32_word(form, 0, 2, 1),
                intent: intent.clone(),
                class: Some(C::Value),
            });
        }
        out.push(Crc32Control {
            form,
            label: format!("{} writing W3", form.mnemonic()),
            word: crc32_word(form, 3, 1, 2),
            intent: intent.clone(),
            class: Some(C::Destination),
        });
        out.push(Crc32Control {
            form,
            label: format!("{} with the wrong sf", form.mnemonic()),
            word: word ^ (1 << 31),
            intent: intent.clone(),
            class: Some(C::Unallocated),
        });
        for mutation in Crc32IntentMutation::ALL {
            let Some(mutated) = mutated_intent(&inst, mutation) else {
                continue;
            };
            out.push(Crc32Control {
                form,
                label: format!("{} intent {mutation:?}", form.mnemonic()),
                word,
                intent: mutated.expect("the representative is in the model"),
                class: Some(C::Value),
            });
        }
    }
    out
}

// ===========================================================================
// Gate credit
// ===========================================================================

/// What the coverage gate's CRC32 rows rest on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Crc32Credit {
    /// Forms decided to hold.
    pub forms: usize,
    /// Instances (form x register assignment) decided to hold.
    pub instances: usize,
    /// Negative controls refuted for their stated reason.
    pub controls_refuted: usize,
}

/// The family's credit: every form holds over [`REGISTER_BATTERY`] and every
/// control in [`crc32_controls`] is refuted for its stated reason. Memoized
/// for the process (deterministic).
pub fn crc32_credit() -> Result<Crc32Credit, String> {
    static MEMO: OnceLock<Result<Crc32Credit, String>> = OnceLock::new();
    MEMO.get_or_init(compute_credit).clone()
}

fn compute_credit() -> Result<Crc32Credit, String> {
    let mut instances = 0;
    for form in Crc32Form::ALL {
        for (rd, rn, rm) in REGISTER_BATTERY {
            let inst = representative_instruction(form, rd, rn, rm);
            match crc32_verdict(&inst) {
                Some(Ok(_)) => instances += 1,
                other => {
                    return Err(format!(
                        "{} {rd}/{rn}/{rm} does not hold: {other:?}",
                        form.mnemonic()
                    ));
                }
            }
        }
    }
    let controls = crc32_controls();
    let mut refuted_count = 0;
    let mut by_label: HashMap<String, String> = HashMap::new();
    for control in &controls {
        match check_word_against_intent(&control.intent, control.word) {
            Err(Crc32CheckError::Refuted { class, .. })
                if control.class.is_none_or(|want| want == class) =>
            {
                refuted_count += 1;
            }
            other => {
                by_label.insert(control.label.clone(), format!("{other:?}"));
            }
        }
    }
    if !by_label.is_empty() {
        let mut failures: Vec<_> = by_label.into_iter().collect();
        failures.sort();
        return Err(format!(
            "{} CRC32 control(s) not refuted for their reason: {failures:?}",
            failures.len()
        ));
    }
    Ok(Crc32Credit {
        forms: Crc32Form::ALL.len(),
        instances,
        controls_refuted: refuted_count,
    })
}

#[cfg(test)]
#[path = "aarch64_crc32_proofs_tests.rs"]
mod tests;
