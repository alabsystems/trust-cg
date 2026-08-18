#![allow(dead_code)]
// a64_interp.rs — a host-independent, integer+FP AArch64 machine-code interpreter
// for the on-host AArch64 CORRECTNESS harness.
//
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// # Why this exists
//
// trust-cg's AArch64 backend is the primary target, but this developer box is an
// Intel x86 machine, so native AArch64 EXECUTION is hardware-blocked. Every
// AArch64 e2e test therefore link-and-runs only on an `aarch64-apple-darwin`
// host and SILENTLY SKIPS on x86 (`return;` when not aarch64) — a fail-OPEN hole
// that lets an AArch64 miscompile pass green on this box.
//
// Correctness, unlike execution, does NOT need the hardware: the emitted machine
// code is just bytes, and those bytes can be DECODED and INTERPRETED on any host.
// This module reuses the repository's real leaf disassembler
// (`trust_cg_lift::disasm::aarch64::decode`) to decode each 4-byte instruction
// word of the emitted `__TEXT,__text`, then interprets the integer / bitfield /
// compare / conditional-select / FP-compare subset the codegen actually emits,
// with an AAPCS64 calling convention (integer args x0-x7, FP args d0-d7, integer
// return x0). This converts the fail-OPEN skips into fail-CLOSED on-host
// assertions: an AArch64 miscompile now FAILS the test on x86.
//
// # Fail-closed / decode-or-reject
//
// Per the repo's DECODE-OR-REJECT mandate this interpreter NEVER silently skips
// an instruction it does not model: `decode()` already fails closed on any
// unknown 32-bit word, and every `Instruction` variant this interpreter does not
// implement returns `Err(A64Error::Unsupported)`. It cannot give a false PASS by
// ignoring the instruction under test.
//
// # Modeled subset (exactly what the O0/O2 narrow-cmp + FP-compare corpus emits)
//
//   MoveWide           : MOVZ / MOVN / MOVK
//   LogicalShiftedReg  : AND/ORR/EOR/ANDS (+ BIC/ORN/EON/BICS via the N bit), with
//                        LSL/LSR/ASR/ROR shift of the second operand
//   AddSubShiftedReg   : ADD/SUB/ADDS/SUBS (register, shifted)
//   AddSubImm          : ADD/SUB/ADDS/SUBS (immediate)  — e.g. CMP Xn,#0
//   BitfieldMove       : SBFM/UBFM/BFM  — SXTB/UXTB/SXTH/UXTH/SXTW, LSL/LSR/ASR imm
//   ConditionalSelect  : CSEL / CSINC (CSET) / CSINV / CSNEG
//   FpUnary            : FMOV / FABS / FNEG / FSQRT (scalar)
//   FpCompare          : FCMP / FCMPE (register and #0.0), setting NZCV per the
//                        AArch64 FP-compare rules — the CORE of the NaN test.
//   Branches           : RET, B, B.cond, CBZ/CBNZ, TBZ/TBNZ (PC-relative)
//
// Flag semantics use the ARM `AddWithCarry` / `ConditionHolds` pseudocode so the
// signed/unsigned/overflow/NaN edge cases are modeled exactly, not approximated.

use std::collections::HashMap;

use trust_cg_lift::disasm::aarch64::{
    DecodeError, Instruction, LoadStoreIndexMode, LoadStorePairAddressMode, decode,
};

/// A typed failure. Any word the interpreter cannot model fails CLOSED here — it
/// is never skipped or treated as a NOP.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum A64Error {
    /// The leaf disassembler rejected the 32-bit word.
    Decode(DecodeError),
    /// A decoded instruction variant / form this interpreter does not model.
    Unsupported(String),
    /// PC ran past the end of the text without a RET.
    RanOff { pc: usize, len: usize },
    /// Step cap hit (a corrupted control flow / nonterminating loop).
    StepLimit,
    /// A named symbol was not found in the object's symbol table.
    SymbolNotFound(String),
}

impl From<DecodeError> for A64Error {
    fn from(e: DecodeError) -> Self {
        A64Error::Decode(e)
    }
}

const STEP_LIMIT: usize = 100_000;

/// Sign-extend the low `bits` of `v` to a full i128.
fn sext(v: u64, bits: u32) -> i128 {
    if bits >= 64 {
        return v as i64 as i128;
    }
    let shift = 64 - bits;
    (((v << shift) as i64) >> shift) as i128
}

/// Mask covering `bits` low bits.
fn mask_of(bits: u32) -> u64 {
    if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}

/// The ARM `AddWithCarry(x, y, carry_in)` primitive over `bits` bits.
/// Returns `(result_masked, N, Z, C, V)`.
fn add_with_carry(x: u64, y: u64, carry: u64, bits: u32) -> (u64, bool, bool, bool, bool) {
    let m = mask_of(bits);
    let x = x & m;
    let y = y & m;
    let usum = (x as u128) + (y as u128) + (carry as u128);
    let result = (usum as u64) & m;
    // Carry out of the top modeled bit.
    let c = (usum >> bits) & 1 == 1;
    let ssum = sext(x, bits) + sext(y, bits) + carry as i128;
    let v = sext(result, bits) != ssum;
    let msb = 1u64 << (bits - 1);
    let n = result & msb != 0;
    let z = result == 0;
    (result, n, z, c, v)
}

/// Shift the second operand of a shifted-register data-processing instruction.
fn shift_reg(val: u64, shift_type: u8, amount: u32, bits: u32) -> u64 {
    let m = mask_of(bits);
    let val = val & m;
    let amount = amount % bits.max(1);
    match shift_type {
        0 => (val << amount) & m, // LSL
        1 => (val >> amount) & m, // LSR (unsigned)
        2 => {
            // ASR: arithmetic (sign-propagating) within `bits`.
            let s = sext(val, bits) >> amount;
            (s as u64) & m
        }
        _ => {
            // ROR
            if amount == 0 {
                val
            } else {
                ((val >> amount) | (val << (bits - amount))) & m
            }
        }
    }
}

/// Rotate-right within `bits`.
fn ror(val: u64, amount: u32, bits: u32) -> u64 {
    shift_reg(val, 3, amount % bits.max(1), bits)
}

/// ARM `VFPExpandImm(imm8, 32)` — the single-precision FMOV-immediate encoding.
/// imm8 = a:b:c:d:e:f:g:h → sign a, exponent NOT(b):b^4:cd... per the spec.
fn vfp_expand_imm_single(imm8: u8) -> u32 {
    let a = ((imm8 >> 7) & 1) as u32;
    let b = ((imm8 >> 6) & 1) as u32;
    let cdefgh = (imm8 & 0x3f) as u32;
    // exp (8 bits) = NOT(b) : b : b : b : b : b : b(rep to fill) ... For single:
    // exp = NOT(b):Replicate(b,5) then the low bits from B. Standard formula:
    //   exp<7> = NOT(b); exp<6:2> = Replicate(b,5)? No — exp = NOT(b):b:b:b:b:b:b
    // Concretely (Arm ARM): imm32 = a:NOT(b):Replicate(b,5):b? Use the widely
    // used construction for 32-bit:
    //   sign(1) | (NOT(b)<<30) | (rep(b,5)<<25) | (b?..). We build via f64 route.
    // Simplest exact route: expand to double then narrow (same value set).
    let d = vfp_expand_imm_double(imm8);
    let val = f64::from_bits(d) as f32;
    let _ = (a, b, cdefgh);
    val.to_bits()
}

/// ARM `VFPExpandImm(imm8, 64)` — the double-precision FMOV-immediate encoding.
fn vfp_expand_imm_double(imm8: u8) -> u64 {
    let a = ((imm8 >> 7) & 1) as u64; // sign
    let b = ((imm8 >> 6) & 1) as u64;
    let cdefgh = (imm8 & 0x3f) as u64;
    // exponent (11 bits) = NOT(b) : Replicate(b, 8) : ... actually
    // exp<10> = NOT(b); exp<9:2> = Replicate(b,8); exp<1:0> = top two of the
    // mantissa selector. Per the Arm ARM for 64-bit:
    //   exp = NOT(b):b:b:b:b:b:b:b:b:b  (i.e. NOT(b) followed by 9 copies of b)
    // giving an 11-bit exponent, and the 4-bit cdef go to the top of the 52-bit
    // fraction.
    let not_b = b ^ 1;
    let exp = (not_b << 10) | (if b == 1 { 0x3FF } else { 0 }); // NOT(b):b*10
    let frac = cdefgh << 48; // cdefgh occupy fraction<51:46>
    (a << 63) | (exp << 52) | frac
}

/// ARM `DecodeBitMasks(immN, imms, immr, immediate=false)` → (wmask, tmask) for a
/// `bits`-wide datasize. Used for SBFM/UBFM/BFM.
fn decode_bit_masks(immn: u8, imms: u8, immr: u8, bits: u32) -> Option<(u64, u64)> {
    // len = HighestSetBit(immN : NOT(imms))  over 7 bits.
    let concat: u32 = ((immn as u32 & 1) << 6) | ((!(imms as u32)) & 0x3f);
    if concat == 0 {
        return None;
    }
    let len = 31 - concat.leading_zeros(); // HighestSetBit
    if len < 1 {
        return None;
    }
    let levels: u32 = (1u32 << len) - 1;
    let s = (imms as u32) & levels;
    let r = (immr as u32) & levels;
    let diff = s.wrapping_sub(r) & levels;
    let esize = 1u32 << len;
    let d = diff & ((1u32 << len) - 1);
    // welem = Ones(S+1), telem = Ones(d+1), each within esize.
    let welem = ones_u64(s + 1);
    let telem = ones_u64(d + 1);
    // wmask = Replicate(ROR(welem, R)) ; tmask = Replicate(telem)
    let w_rot = ror(welem, r, esize);
    let wmask = replicate(w_rot, esize, bits);
    let tmask = replicate(telem, esize, bits);
    Some((wmask, tmask))
}

fn ones_u64(n: u32) -> u64 {
    if n >= 64 { u64::MAX } else { (1u64 << n) - 1 }
}

/// Replicate the low `elem_bits` of `elem` to fill `total_bits`.
fn replicate(elem: u64, elem_bits: u32, total_bits: u32) -> u64 {
    let elem = elem & mask_of(elem_bits);
    if elem_bits == 0 {
        return 0;
    }
    let mut out = 0u64;
    let mut pos = 0u32;
    while pos < total_bits {
        out |= elem << pos;
        pos += elem_bits;
    }
    out & mask_of(total_bits)
}

/// Top of the modeled stack. 16-byte aligned, far above any `__text` offset and
/// below the reserved sentinel range so a stack address never aliases either.
const STACK_TOP: u64 = 0x0010_0000;
/// Return-address sentinel installed in the link register (x30) at the top-level
/// entry: a `RET` to this value ends interpretation (return to the harness).
const RET_SENTINEL: u64 = 0xFFFF_FFFF_FFFF_FFF0;

/// AAPCS64 register file + NZCV flags + a flat little-endian memory (stack) and
/// the read-only `__text` image (so jump-table data embedded in `__text` reads
/// back as data). Calls are modeled with a real link register and a `__text`
/// branch-relocation map, so recursion and cross-function calls execute.
pub struct A64Interp {
    /// X0..X30 general registers. Index 31 is XZR (reads 0, writes discarded) in
    /// data-processing contexts; the stack pointer is a separate field selected
    /// only by add/sub-immediate and load/store base operands.
    pub x: [u64; 32],
    /// The architectural stack pointer (SP / register-31 in SP contexts).
    pub sp: u64,
    /// V0..V31, low 64 bits (the D registers) as raw bit patterns.
    pub v: [u64; 32],
    /// V0..V31, high 64 bits (bits [127:64]). Only touched by 128-bit (Q)
    /// SIMD&FP loads/stores and V128 argument setup; scalar S/D operations keep
    /// this zero (an FP write zeroes the upper lanes of the destination V reg).
    pub v_hi: [u64; 32],
    pub n: bool,
    pub z: bool,
    pub c: bool,
    pub v_flag: bool,
    pub text: Vec<u8>,
    /// Writable data memory (stack + spill slots), keyed by byte address. Reads
    /// of `__text`-range addresses fall through to `text`; everything else is 0
    /// until written.
    pub mem: HashMap<u64, u8>,
    /// `__text` byte-offset of each `BL` site → resolved callee byte-offset
    /// (from the object's ARM64_RELOC_BRANCH26 relocations). A `BL` whose site
    /// is absent falls back to its baked `imm26` (intra-function calls, if any).
    pub branch_relocs: HashMap<usize, usize>,
    /// Ordered decoded-instruction trace (for debugging a mismatch).
    pub trace: Vec<String>,
}

impl A64Interp {
    pub fn new(text: Vec<u8>) -> Self {
        Self {
            x: [0; 32],
            sp: STACK_TOP,
            v: [0; 32],
            v_hi: [0; 32],
            n: false,
            z: false,
            c: false,
            v_flag: false,
            text,
            mem: HashMap::new(),
            branch_relocs: HashMap::new(),
            trace: Vec::new(),
        }
    }

    /// Install the `__text` branch-relocation map (BL-site → callee offset).
    pub fn with_branch_relocs(mut self, relocs: HashMap<usize, usize>) -> Self {
        self.branch_relocs = relocs;
        self
    }

    /// Set an integer argument register (x0..x30).
    pub fn set_x(&mut self, i: usize, val: u64) {
        if i < 31 {
            self.x[i] = val;
        }
    }

    /// Set an FP argument register (d0..d31) from an f64.
    pub fn set_d(&mut self, i: usize, val: f64) {
        self.v[i] = val.to_bits();
        self.v_hi[i] = 0;
    }

    /// Set an FP argument register (s0..s31) from an f32. Per AArch64, writing a
    /// 32-bit S register zero-extends into the full V register.
    pub fn set_s(&mut self, i: usize, val: f32) {
        self.v[i] = val.to_bits() as u64;
        self.v_hi[i] = 0;
    }

    /// Set an FP argument register (h0..h31) from a raw 16-bit half-float bit
    /// pattern, zero-extended into the V register.
    pub fn set_h_bits(&mut self, i: usize, bits: u16) {
        self.v[i] = bits as u64;
        self.v_hi[i] = 0;
    }

    /// Set a full 128-bit V register (q0..q31) from lo/hi 64-bit halves.
    pub fn set_q(&mut self, i: usize, lo: u64, hi: u64) {
        self.v[i] = lo;
        self.v_hi[i] = hi;
    }

    /// Set an FP register from a raw D-width (64-bit) bit pattern.
    pub fn set_d_bits(&mut self, i: usize, bits: u64) {
        self.v[i] = bits;
        self.v_hi[i] = 0;
    }

    /// Read the low 32 bits of Vn as an f32 (the S-register view).
    pub fn read_s(&self, i: usize) -> f32 {
        f32::from_bits(self.v[i] as u32)
    }

    fn read_x(&self, i: u8, bits: u32) -> u64 {
        let raw = if i == 31 { 0 } else { self.x[i as usize] };
        raw & mask_of(bits)
    }

    fn write_x(&mut self, i: u8, bits: u32, val: u64) {
        if i == 31 {
            return; // XZR
        }
        // A 32-bit write zero-extends into the full X register.
        self.x[i as usize] = val & mask_of(bits);
    }

    /// Read a register in an SP-context operand (add/sub-immediate Rn, load/store
    /// base Rn): register 31 selects the stack pointer, not XZR.
    fn read_sp(&self, i: u8, bits: u32) -> u64 {
        let raw = if i == 31 { self.sp } else { self.x[i as usize] };
        raw & mask_of(bits)
    }

    /// Write a register in an SP-context destination: register 31 writes SP.
    fn write_sp(&mut self, i: u8, bits: u32, val: u64) {
        if i == 31 {
            self.sp = val & mask_of(bits);
        } else {
            self.x[i as usize] = val & mask_of(bits);
        }
    }

    /// Read `n` bytes little-endian from `addr`. `__text`-range addresses read
    /// the read-only code/jump-table image; all other addresses read the
    /// writable `mem` map (0 until written).
    fn load_bytes(&self, addr: u64, n: u32) -> u64 {
        let mut val = 0u64;
        for k in 0..n as u64 {
            let a = addr.wrapping_add(k);
            let byte = if (a as usize) < self.text.len() {
                self.text[a as usize]
            } else {
                self.mem.get(&a).copied().unwrap_or(0)
            };
            val |= (byte as u64) << (8 * k);
        }
        val
    }

    /// Write the low `n` bytes of `val` little-endian to `mem` at `addr`.
    fn store_bytes(&mut self, addr: u64, n: u32, val: u64) {
        for k in 0..n as u64 {
            let a = addr.wrapping_add(k);
            self.mem.insert(a, (val >> (8 * k)) as u8);
        }
    }

    /// Shared integer load/store body for the four addressing forms.
    ///
    /// `size` is log2(bytes) (0=B,1=H,2=W,3=X); `opc` selects store (0b00),
    /// zero-extending load (0b01), sign-extend-to-64 load (0b10), or
    /// sign-extend-to-32 load (0b11). `writeback` optionally updates a base
    /// register (register 31 = SP) after the access.
    fn exec_load_store(
        &mut self,
        size: u8,
        opc: u8,
        vector: bool,
        rt: u8,
        addr: u64,
        writeback: Option<(u8, u64)>,
    ) -> Result<(), A64Error> {
        if vector {
            return Err(A64Error::Unsupported("vector load/store".into()));
        }
        let nbytes = 1u32 << size;
        let width_bits = 8 * nbytes;
        match opc {
            0b00 => {
                // Store the low `nbytes` of Rt.
                let v = self.read_x(rt, width_bits);
                self.store_bytes(addr, nbytes, v);
            }
            0b01 => {
                // Zero-extending load.
                let v = self.load_bytes(addr, nbytes);
                self.write_x(rt, 64, v);
            }
            // PRFM / PRFUM — (V=0, size=0b11, opc=0b10) is PREFETCH, not a load.
            //
            // This arm must precede the sign-extending one. `opc=0b10` means
            // "sign-extend to 64" in every OTHER size row, but at `size=0b11`
            // the triple is the prefetch encoding, and there `Rt` is not a
            // register at all — it is the prefetch operation `<prfop>`
            // (type:target:policy). The instruction reads no data and writes no
            // register.
            //
            // Executing it as a load did BOTH of the things it must not: an
            // 8-byte memory read at the computed address (fault-capable, and
            // able to diverge from hardware on an unmapped page), and a write to
            // X<prfop> — clobbering whichever register the prfop bits happen to
            // name. The decoder ACCEPTS these words on purpose
            // (`still_accepts_real_prfm`, `still_accepts_prefetch_without_writeback`
            // in trust-cg-lift/tests/aarch64_allocation.rs: "must still decode,
            // in every form"), so the fidelity gap was here, in the consumer,
            // not in the acceptance set.
            //
            // A prefetch is architecturally a hint: no observable state change.
            // Falling through leaves the base-register writeback below intact —
            // it is `None` for these words in any case, because PRFM has no
            // base-writeback form and `validate_scalar_load_store` refuses that
            // row.
            0b10 if size == 0b11 => {}
            0b10 => {
                // Sign-extend to 64.
                let raw = self.load_bytes(addr, nbytes);
                self.write_x(rt, 64, sext(raw, width_bits) as u64);
            }
            0b11 => {
                // Sign-extend to 32 (then zero-extended into X by write_x).
                let raw = self.load_bytes(addr, nbytes);
                let s32 = (sext(raw, width_bits) as i32) as u32 as u64;
                self.write_x(rt, 64, s32);
            }
            other => {
                return Err(A64Error::Unsupported(format!("load/store opc {other:#b}")));
            }
        }
        if let Some((rn, wb)) = writeback {
            self.write_sp(rn, 64, wb);
        }
        Ok(())
    }

    fn read_d(&self, i: u8) -> f64 {
        f64::from_bits(self.v[i as usize])
    }

    /// Read a scalar FP register as an f64 value (single is widened exactly).
    fn read_fp_scalar(&self, ftype: u8, rn: u8) -> Result<f64, A64Error> {
        match ftype {
            0 => Ok(f32::from_bits(self.v[rn as usize] as u32) as f64),
            1 => Ok(f64::from_bits(self.v[rn as usize])),
            other => Err(A64Error::Unsupported(format!("fp scalar ftype {other}"))),
        }
    }

    /// Write an f64 value into a scalar FP register (single is rounded to f32).
    fn write_fp_scalar(&mut self, ftype: u8, rd: u8, val: f64) -> Result<(), A64Error> {
        match ftype {
            0 => self.v[rd as usize] = (val as f32).to_bits() as u64,
            1 => self.v[rd as usize] = val.to_bits(),
            other => return Err(A64Error::Unsupported(format!("fp scalar ftype {other}"))),
        }
        self.v_hi[rd as usize] = 0;
        Ok(())
    }

    /// SIMD&FP load/store access size in log2(bytes), from the `size` (bits
    /// 31:30) and `opc` (bits 23:22) fields. The high bit of `opc` extends the
    /// size to reach the 128-bit (Q) form: (opc<1> << 2) | size.
    ///   size/opc<1>:  00/0=B(1) 01/0=H(2) 10/0=S(4) 11/0=D(8) 00/1=Q(16)
    fn fp_access_log2(size: u8, opc: u8) -> u32 {
        ((((opc >> 1) & 1) as u32) << 2) | (size as u32)
    }

    /// Execute a SIMD&FP load (`is_load`) or store into/from Vt. Writes zero the
    /// upper lanes of Vt (AArch64 scalar-FP-write semantics); a Q access uses
    /// both 64-bit lanes.
    fn exec_fp_load_store(
        &mut self,
        log2: u32,
        is_load: bool,
        rt: u8,
        addr: u64,
    ) -> Result<(), A64Error> {
        let t = rt as usize;
        match log2 {
            0..=3 => {
                // B/H/S/D: a single lane of up to 8 bytes.
                let nbytes = 1u32 << log2;
                if is_load {
                    let lo = self.load_bytes(addr, nbytes);
                    self.v[t] = lo;
                    self.v_hi[t] = 0;
                } else {
                    self.store_bytes(addr, nbytes, self.v[t]);
                }
            }
            4 => {
                // Q: 16 bytes across both lanes.
                if is_load {
                    self.v[t] = self.load_bytes(addr, 8);
                    self.v_hi[t] = self.load_bytes(addr.wrapping_add(8), 8);
                } else {
                    let (lo, hi) = (self.v[t], self.v_hi[t]);
                    self.store_bytes(addr, 8, lo);
                    self.store_bytes(addr.wrapping_add(8), 8, hi);
                }
            }
            other => return Err(A64Error::Unsupported(format!("fp load/store log2 {other}"))),
        }
        Ok(())
    }

    /// `ConditionHolds(cond)` per the ARM pseudocode, over the current NZCV.
    fn cond_holds(&self, cond: u8) -> bool {
        let (n, z, c, v) = (self.n, self.z, self.c, self.v_flag);
        let base = match cond >> 1 {
            0b000 => z,              // EQ / NE
            0b001 => c,              // CS / CC
            0b010 => n,              // MI / PL
            0b011 => v,              // VS / VC
            0b100 => c && !z,        // HI / LS
            0b101 => n == v,         // GE / LT
            0b110 => (n == v) && !z, // GT / LE
            _ => true,               // AL / NV
        };
        if (cond & 1) == 1 && cond != 0b1111 {
            !base
        } else {
            base
        }
    }

    /// Run from byte offset `entry` until RET (or a fail-closed error).
    /// Returns the integer result in X0.
    pub fn run(&mut self, entry: usize) -> Result<u64, A64Error> {
        // A top-level frame: SP at the modeled stack top and a link register that
        // ends interpretation when the entry function returns.
        self.sp = STACK_TOP;
        self.x[30] = RET_SENTINEL;
        let mut pc = entry;
        for _ in 0..STEP_LIMIT {
            if pc + 4 > self.text.len() {
                return Err(A64Error::RanOff {
                    pc,
                    len: self.text.len(),
                });
            }
            let word = u32::from_le_bytes([
                self.text[pc],
                self.text[pc + 1],
                self.text[pc + 2],
                self.text[pc + 3],
            ]);
            let ins = decode(word)?;
            self.trace.push(format!("{pc:#06x}: {ins:?}"));
            match self.exec(&ins, pc)? {
                Flow::Next => pc += 4,
                Flow::Branch(target) => pc = target,
                Flow::Ret => return Ok(self.x[0]),
            }
        }
        Err(A64Error::StepLimit)
    }

    fn exec(&mut self, ins: &Instruction, pc: usize) -> Result<Flow, A64Error> {
        match ins {
            // Architectural NOP (HINT #0). Optimized code may contain these as
            // alignment padding; executing one advances to the next word and
            // changes no architectural state.
            Instruction::Nop => Ok(Flow::Next),
            Instruction::MoveWide(m) => {
                let bits = if m.sf == 1 { 64 } else { 32 };
                let sh = (m.hw as u32) * 16;
                let imm = (m.imm16 as u64) << sh;
                let result = match m.opc {
                    0b10 => imm,  // MOVZ
                    0b00 => !imm, // MOVN
                    0b11 => {
                        // MOVK: keep other bits of Rd.
                        let cur = self.read_x(m.rd, 64);
                        (cur & !(0xFFFFu64 << sh)) | imm
                    }
                    other => return Err(A64Error::Unsupported(format!("MoveWide opc {other:#b}"))),
                };
                self.write_x(m.rd, bits, result);
                Ok(Flow::Next)
            }
            Instruction::LogicalShiftedReg(l) => {
                let bits = if l.sf == 1 { 64 } else { 32 };
                let rn = self.read_x(l.rn, bits);
                let mut op2 = shift_reg(self.read_x(l.rm, bits), l.shift, l.imm6 as u32, bits);
                if l.n {
                    op2 = (!op2) & mask_of(bits);
                }
                let result = match l.opc {
                    0b00 => rn & op2, // AND / BIC
                    0b01 => rn | op2, // ORR / ORN
                    0b10 => rn ^ op2, // EOR / EON
                    0b11 => rn & op2, // ANDS / BICS
                    _ => unreachable!(),
                } & mask_of(bits);
                if l.opc == 0b11 {
                    self.n = result & (1u64 << (bits - 1)) != 0;
                    self.z = result == 0;
                    self.c = false;
                    self.v_flag = false;
                }
                self.write_x(l.rd, bits, result);
                Ok(Flow::Next)
            }
            Instruction::AddSubShiftedReg(a) => {
                let bits = if a.sf == 1 { 64 } else { 32 };
                let rn = self.read_x(a.rn, bits);
                let op2 = shift_reg(self.read_x(a.rm, bits), a.shift, a.imm6 as u32, bits);
                let (result, n, z, c, v) = if a.op == 0 {
                    add_with_carry(rn, op2, 0, bits) // ADD
                } else {
                    add_with_carry(rn, (!op2) & mask_of(bits), 1, bits) // SUB
                };
                if a.set_flags {
                    self.n = n;
                    self.z = z;
                    self.c = c;
                    self.v_flag = v;
                }
                self.write_x(a.rd, bits, result);
                Ok(Flow::Next)
            }
            Instruction::AddSubImm(a) => {
                let bits = if a.sf == 1 { 64 } else { 32 };
                // Add/sub-immediate Rn is an SP-context operand: register 31 is
                // the stack pointer (e.g. `add x29, sp, #0`, `sub sp, sp, #N`).
                let rn = self.read_sp(a.rn, bits);
                let imm = if a.shift12 {
                    (a.imm12 as u64) << 12
                } else {
                    a.imm12 as u64
                };
                let (result, n, z, c, v) = if a.op == 0 {
                    add_with_carry(rn, imm, 0, bits)
                } else {
                    add_with_carry(rn, (!imm) & mask_of(bits), 1, bits)
                };
                if a.set_flags {
                    self.n = n;
                    self.z = z;
                    self.c = c;
                    self.v_flag = v;
                    // ADDS/SUBS with Rd=31 (e.g. `cmp`) write XZR, not SP.
                    if a.rd != 31 {
                        self.write_x(a.rd, bits, result);
                    }
                } else {
                    // Non-flag ADD/SUB with Rd=31 writes SP.
                    self.write_sp(a.rd, bits, result);
                }
                Ok(Flow::Next)
            }
            Instruction::AddSubCarry(a) => {
                // ADC/SBC (+ optional flags). SBC computes Rn + NOT(Rm) + C.
                let bits = if a.sf == 1 { 64 } else { 32 };
                let rn = self.read_x(a.rn, bits);
                let rm = self.read_x(a.rm, bits);
                let carry = u64::from(self.c);
                let (result, n, z, c, v) = if a.op == 0 {
                    add_with_carry(rn, rm, carry, bits)
                } else {
                    add_with_carry(rn, (!rm) & mask_of(bits), carry, bits)
                };
                if a.set_flags {
                    self.n = n;
                    self.z = z;
                    self.c = c;
                    self.v_flag = v;
                }
                self.write_x(a.rd, bits, result);
                Ok(Flow::Next)
            }
            Instruction::LogicalImm(l) => {
                let bits = if l.sf == 1 { 64 } else { 32 };
                let rn = self.read_x(l.rn, bits);
                let (imm, _) =
                    decode_bit_masks(u8::from(l.n), l.imms, l.immr, bits).ok_or_else(|| {
                        A64Error::Unsupported("LogicalImm: unallocated bitmask".into())
                    })?;
                let result = match l.opc {
                    0b00 => rn & imm, // AND
                    0b01 => rn | imm, // ORR
                    0b10 => rn ^ imm, // EOR
                    0b11 => rn & imm, // ANDS
                    _ => unreachable!(),
                } & mask_of(bits);
                if l.opc == 0b11 {
                    self.n = result & (1u64 << (bits - 1)) != 0;
                    self.z = result == 0;
                    self.c = false;
                    self.v_flag = false;
                }
                // ANDS with Rd=31 (`tst`) discards the result; AND/ORR/EOR to a
                // logical Rd=31 is XZR anyway, so a plain write_x is correct.
                self.write_x(l.rd, bits, result);
                Ok(Flow::Next)
            }
            Instruction::DataProcessing2Source(d) => {
                let bits = if d.sf == 1 { 64 } else { 32 };
                let n = self.read_x(d.rn, bits);
                let m = self.read_x(d.rm, bits);
                let result = match d.opcode {
                    0b000010 => {
                        // UDIV: division by zero yields 0 (no trap).
                        n.checked_div(m).unwrap_or(0)
                    }
                    0b000011 => {
                        // SDIV: signed, truncating toward zero. /0 → 0; the
                        // INT_MIN/-1 case does not trap and yields INT_MIN.
                        let sn = sext(n, bits);
                        let sm = sext(m, bits);
                        sn.checked_div(sm).unwrap_or(if sm == 0 { 0 } else { sn }) as u64
                            & mask_of(bits)
                    }
                    0b001000 => shift_reg(n, 0, (m % bits as u64) as u32, bits), // LSLV
                    0b001001 => shift_reg(n, 1, (m % bits as u64) as u32, bits), // LSRV
                    0b001010 => shift_reg(n, 2, (m % bits as u64) as u32, bits), // ASRV
                    0b001011 => shift_reg(n, 3, (m % bits as u64) as u32, bits), // RORV
                    other => {
                        return Err(A64Error::Unsupported(format!(
                            "DataProcessing2Source opcode {other:#08b}"
                        )));
                    }
                };
                self.write_x(d.rd, bits, result);
                Ok(Flow::Next)
            }
            Instruction::DataProcessing3Source(d) => {
                let bits = if d.sf == 1 { 64 } else { 32 };
                let result = match d.op31 {
                    0b000 => {
                        // MADD/MSUB (MUL/MNEG when Ra=XZR). Low `bits` of the
                        // product; ± the addend.
                        let n = self.read_x(d.rn, bits);
                        let m = self.read_x(d.rm, bits);
                        let a = self.read_x(d.ra, bits);
                        let prod = n.wrapping_mul(m);
                        if d.o0 {
                            a.wrapping_sub(prod)
                        } else {
                            a.wrapping_add(prod)
                        }
                    }
                    0b001 => {
                        // SMADDL/SMSUBL/SMULL: signed 32×32→64 + 64-bit addend.
                        let n = self.read_x(d.rn, 32) as u32 as i32 as i64;
                        let m = self.read_x(d.rm, 32) as u32 as i32 as i64;
                        let a = self.read_x(d.ra, 64) as i64;
                        let prod = n.wrapping_mul(m);
                        (if d.o0 {
                            a.wrapping_sub(prod)
                        } else {
                            a.wrapping_add(prod)
                        }) as u64
                    }
                    0b101 => {
                        // UMADDL/UMSUBL/UMULL: unsigned 32×32→64 + 64-bit addend.
                        let n = self.read_x(d.rn, 32) as u32 as u64;
                        let m = self.read_x(d.rm, 32) as u32 as u64;
                        let a = self.read_x(d.ra, 64);
                        if d.o0 {
                            a.wrapping_sub(n.wrapping_mul(m))
                        } else {
                            a.wrapping_add(n.wrapping_mul(m))
                        }
                    }
                    0b010 => {
                        // SMULH: high 64 bits of the signed 64×64 product.
                        let n = self.read_x(d.rn, 64) as i64 as i128;
                        let m = self.read_x(d.rm, 64) as i64 as i128;
                        ((n * m) >> 64) as u64
                    }
                    0b110 => {
                        // UMULH: high 64 bits of the unsigned 64×64 product.
                        let n = self.read_x(d.rn, 64) as u128;
                        let m = self.read_x(d.rm, 64) as u128;
                        ((n * m) >> 64) as u64
                    }
                    other => {
                        return Err(A64Error::Unsupported(format!(
                            "DataProcessing3Source op31 {other:#b}"
                        )));
                    }
                };
                // The long/high multiplies always write a full X register.
                let dst_bits = if d.op31 == 0b000 { bits } else { 64 };
                self.write_x(d.rd, dst_bits, result);
                Ok(Flow::Next)
            }
            Instruction::PcRelAddress(p) => {
                // ADR: Rd = PC + imm21. ADRP: Rd = (PC & ~0xFFF) + (imm21 << 12).
                // The interpreter runs in `__text`-offset space (section addr 0),
                // so `pc` is the runtime address and PC-relative displacements are
                // identical.
                let result = if p.page {
                    ((pc as u64) & !0xFFF).wrapping_add((p.imm21 as i64 as u64) << 12)
                } else {
                    (pc as i64).wrapping_add(p.imm21 as i64) as u64
                };
                self.write_x(p.rd, 64, result);
                Ok(Flow::Next)
            }
            Instruction::LoadStorePair(lsp) if lsp.vector => {
                // SIMD&FP STP/LDP. opc selects the element width:
                //   00 = S (4 bytes), 01 = D (8 bytes), 10 = Q (16 bytes).
                let elem = match lsp.opc {
                    0b00 => 4u32,
                    0b01 => 8u32,
                    0b10 => 16u32,
                    other => {
                        return Err(A64Error::Unsupported(format!(
                            "LoadStorePair vector opc {other:#b}"
                        )));
                    }
                };
                let base = self.read_sp(lsp.rn, 64);
                let offset = (sext(lsp.imm7 as u64, 7) as i64).wrapping_mul(elem as i64) as u64;
                let (addr, writeback) = match lsp.mode {
                    LoadStorePairAddressMode::SignedOffset => (base.wrapping_add(offset), None),
                    LoadStorePairAddressMode::PreIndex => {
                        let a = base.wrapping_add(offset);
                        (a, Some(a))
                    }
                    LoadStorePairAddressMode::PostIndex => (base, Some(base.wrapping_add(offset))),
                };
                let log2 = elem.trailing_zeros();
                self.exec_fp_load_store(log2, lsp.load, lsp.rt, addr)?;
                self.exec_fp_load_store(log2, lsp.load, lsp.rt2, addr.wrapping_add(elem as u64))?;
                if let Some(wb) = writeback {
                    self.write_sp(lsp.rn, 64, wb);
                }
                Ok(Flow::Next)
            }
            Instruction::LoadStorePair(lsp) => {
                let (scale, sign_extend) = match lsp.opc {
                    0b00 => (4u32, false), // 32-bit
                    0b01 => (4u32, true),  // LDPSW (signed word → 64)
                    0b10 => (8u32, false), // 64-bit
                    other => {
                        return Err(A64Error::Unsupported(format!(
                            "LoadStorePair opc {other:#b}"
                        )));
                    }
                };
                let base = self.read_sp(lsp.rn, 64);
                let offset = (sext(lsp.imm7 as u64, 7) as i64).wrapping_mul(scale as i64) as u64;
                let (addr, writeback) = match lsp.mode {
                    LoadStorePairAddressMode::SignedOffset => (base.wrapping_add(offset), None),
                    LoadStorePairAddressMode::PreIndex => {
                        let a = base.wrapping_add(offset);
                        (a, Some(a))
                    }
                    LoadStorePairAddressMode::PostIndex => (base, Some(base.wrapping_add(offset))),
                };
                if lsp.load {
                    let raw1 = self.load_bytes(addr, scale);
                    let raw2 = self.load_bytes(addr.wrapping_add(scale as u64), scale);
                    let (v1, v2) = if sign_extend {
                        (sext(raw1, 8 * scale) as u64, sext(raw2, 8 * scale) as u64)
                    } else {
                        (raw1, raw2)
                    };
                    self.write_x(lsp.rt, 64, v1);
                    self.write_x(lsp.rt2, 64, v2);
                } else {
                    let v1 = self.read_x(lsp.rt, 8 * scale);
                    let v2 = self.read_x(lsp.rt2, 8 * scale);
                    self.store_bytes(addr, scale, v1);
                    self.store_bytes(addr.wrapping_add(scale as u64), scale, v2);
                }
                if let Some(wb) = writeback {
                    self.write_sp(lsp.rn, 64, wb);
                }
                Ok(Flow::Next)
            }
            Instruction::LoadStoreUnsignedImm(ls) => {
                let base = self.read_sp(ls.rn, 64);
                if ls.vector {
                    let log2 = Self::fp_access_log2(ls.size, ls.opc);
                    let addr = base.wrapping_add((ls.imm12 as u64) << log2);
                    self.exec_fp_load_store(log2, (ls.opc & 1) == 1, ls.rt, addr)?;
                } else {
                    let addr = base.wrapping_add((ls.imm12 as u64) << ls.size);
                    self.exec_load_store(ls.size, ls.opc, ls.vector, ls.rt, addr, None)?;
                }
                Ok(Flow::Next)
            }
            Instruction::LoadStoreUnscaled(ls) => {
                let base = self.read_sp(ls.rn, 64);
                let addr = (base as i64).wrapping_add(ls.imm9 as i64) as u64;
                if ls.vector {
                    let log2 = Self::fp_access_log2(ls.size, ls.opc);
                    self.exec_fp_load_store(log2, (ls.opc & 1) == 1, ls.rt, addr)?;
                } else {
                    self.exec_load_store(ls.size, ls.opc, ls.vector, ls.rt, addr, None)?;
                }
                Ok(Flow::Next)
            }
            Instruction::LoadStoreIndexed(ls) => {
                let base = self.read_sp(ls.rn, 64);
                let after = (base as i64).wrapping_add(ls.imm9 as i64) as u64;
                let (addr, wb) = match ls.mode {
                    LoadStoreIndexMode::PreIndex => (after, after),
                    LoadStoreIndexMode::PostIndex => (base, after),
                };
                if ls.vector {
                    let log2 = Self::fp_access_log2(ls.size, ls.opc);
                    self.exec_fp_load_store(log2, (ls.opc & 1) == 1, ls.rt, addr)?;
                    self.write_sp(ls.rn, 64, wb);
                } else {
                    self.exec_load_store(
                        ls.size,
                        ls.opc,
                        ls.vector,
                        ls.rt,
                        addr,
                        Some((ls.rn, wb)),
                    )?;
                }
                Ok(Flow::Next)
            }
            Instruction::LoadStoreRegister(ls) => {
                let base = self.read_sp(ls.rn, 64);
                // Extend/shift the index register per `option`; the jump-table
                // load uses option=3 (LSL/UXTX) with shift = log2(size).
                let raw = self.x[ls.rm as usize];
                let index = match ls.option {
                    0b010 => raw as u32 as u64,               // UXTW
                    0b011 => raw,                             // LSL / UXTX
                    0b110 => raw as u32 as i32 as i64 as u64, // SXTW
                    0b111 => raw,                             // SXTX
                    other => {
                        return Err(A64Error::Unsupported(format!(
                            "LoadStoreRegister option {other:#b}"
                        )));
                    }
                };
                if ls.vector {
                    let log2 = Self::fp_access_log2(ls.size, ls.opc);
                    let amount = if ls.shift { log2 } else { 0 };
                    let addr = base.wrapping_add(index << amount);
                    self.exec_fp_load_store(log2, (ls.opc & 1) == 1, ls.rt, addr)?;
                } else {
                    let amount = if ls.shift { ls.size as u32 } else { 0 };
                    let addr = base.wrapping_add(index << amount);
                    self.exec_load_store(ls.size, ls.opc, ls.vector, ls.rt, addr, None)?;
                }
                Ok(Flow::Next)
            }
            Instruction::BitfieldMove(b) => {
                let bits = if b.sf == 1 { 64 } else { 32 };
                let (wmask, tmask) = decode_bit_masks(b.sf, b.imms, b.immr, bits)
                    .ok_or_else(|| A64Error::Unsupported("BFM: unallocated bitmask".into()))?;
                let src = self.read_x(b.rn, bits);
                // dst / top selection: SBFM(opc=0) sign-extend, UBFM(opc=2) zero,
                // BFM(opc=1) keep Rd.
                let dst = if b.opc == 0b01 {
                    self.read_x(b.rd, bits)
                } else {
                    0
                };
                let bot = (dst & !wmask) | (ror(src, b.immr as u32, bits) & wmask);
                let top = match b.opc {
                    0b00 => {
                        // SBFM: replicate sign bit src<imms>
                        let sign = (src >> b.imms) & 1;
                        if sign == 1 { mask_of(bits) } else { 0 }
                    }
                    0b10 => 0,                       // UBFM
                    0b01 => self.read_x(b.rd, bits), // BFM
                    _ => unreachable!(),
                };
                let result = ((top & !tmask) | (bot & tmask)) & mask_of(bits);
                self.write_x(b.rd, bits, result);
                Ok(Flow::Next)
            }
            Instruction::ConditionalSelect(cs) => {
                let bits = if cs.sf == 1 { 64 } else { 32 };
                let rn = self.read_x(cs.rn, bits);
                let rm = self.read_x(cs.rm, bits);
                let hold = self.cond_holds(cs.cond);
                let result = if hold {
                    rn
                } else {
                    match (cs.op, cs.o2) {
                        (false, false) => rm,                                // CSEL
                        (false, true) => rm.wrapping_add(1) & mask_of(bits), // CSINC
                        (true, false) => (!rm) & mask_of(bits),              // CSINV
                        (true, true) => rm.wrapping_neg() & mask_of(bits),   // CSNEG
                    }
                };
                self.write_x(cs.rd, bits, result);
                Ok(Flow::Next)
            }
            Instruction::FpUnary(f) => {
                // Scalar double / single. opcode: 0=FMOV,1=FABS,2=FNEG,3=FSQRT.
                if f.ftype != 1 && f.ftype != 0 {
                    return Err(A64Error::Unsupported(format!("FpUnary ftype {}", f.ftype)));
                }
                let is_double = f.ftype == 1;
                let src_bits = self.v[f.rn as usize];
                let out = match f.opcode {
                    0 => src_bits, // FMOV
                    1 => {
                        // FABS: clear sign bit.
                        if is_double {
                            src_bits & !(1u64 << 63)
                        } else {
                            src_bits & !(1u64 << 31)
                        }
                    }
                    2 => {
                        // FNEG: flip sign bit.
                        if is_double {
                            src_bits ^ (1u64 << 63)
                        } else {
                            src_bits ^ (1u64 << 31)
                        }
                    }
                    3 => {
                        // FSQRT
                        if is_double {
                            f64::from_bits(src_bits).sqrt().to_bits()
                        } else {
                            (f32::from_bits(src_bits as u32).sqrt().to_bits()) as u64
                        }
                    }
                    other => return Err(A64Error::Unsupported(format!("FpUnary opcode {other}"))),
                };
                self.v[f.rd as usize] = out;
                Ok(Flow::Next)
            }
            Instruction::FpCompare(f) => {
                // opc<3> = with-zero form; opc<4>=1 => FCMPE (signaling; same NZCV
                // for the quiet subset we model). ftype 1 = double, 0 = single.
                let with_zero = (f.opc & 0b01000) != 0;
                let (a, b) = if f.ftype == 1 {
                    let a = self.read_d(f.rn);
                    let b = if with_zero { 0.0 } else { self.read_d(f.rm) };
                    (a, b)
                } else {
                    let a = f32::from_bits(self.v[f.rn as usize] as u32) as f64;
                    let b = if with_zero {
                        0.0
                    } else {
                        f32::from_bits(self.v[f.rm as usize] as u32) as f64
                    };
                    (a, b)
                };
                // AArch64 FP compare NZCV:
                //   unordered (NaN) : N=0 Z=0 C=1 V=1
                //   equal           : N=0 Z=1 C=1 V=0
                //   less than       : N=1 Z=0 C=0 V=0
                //   greater than    : N=0 Z=0 C=1 V=0
                let (n, z, c, v) = if a.is_nan() || b.is_nan() {
                    (false, false, true, true)
                } else if a == b {
                    (false, true, true, false)
                } else if a < b {
                    (true, false, false, false)
                } else {
                    (false, false, true, false)
                };
                self.n = n;
                self.z = z;
                self.c = c;
                self.v_flag = v;
                Ok(Flow::Next)
            }
            Instruction::FpArith(f) => {
                // ftype: 00=single, 01=double. opcode: 0=FMUL,1=FDIV,2=FADD,3=FSUB.
                let double = match f.ftype {
                    0 => false,
                    1 => true,
                    other => return Err(A64Error::Unsupported(format!("FpArith ftype {other}"))),
                };
                if double {
                    let a = f64::from_bits(self.v[f.rn as usize]);
                    let b = f64::from_bits(self.v[f.rm as usize]);
                    let r = match f.opcode {
                        0 => a * b,
                        1 => a / b,
                        2 => a + b,
                        3 => a - b,
                        other => {
                            return Err(A64Error::Unsupported(format!("FpArith opcode {other}")));
                        }
                    };
                    self.v[f.rd as usize] = r.to_bits();
                } else {
                    let a = f32::from_bits(self.v[f.rn as usize] as u32);
                    let b = f32::from_bits(self.v[f.rm as usize] as u32);
                    let r = match f.opcode {
                        0 => a * b,
                        1 => a / b,
                        2 => a + b,
                        3 => a - b,
                        other => {
                            return Err(A64Error::Unsupported(format!("FpArith opcode {other}")));
                        }
                    };
                    self.v[f.rd as usize] = r.to_bits() as u64;
                }
                self.v_hi[f.rd as usize] = 0;
                Ok(Flow::Next)
            }
            Instruction::FpPrecisionConvert(f) => {
                // FCVT between single/double (half unsupported).
                let src = match f.src_ftype {
                    0 => f32::from_bits(self.v[f.rn as usize] as u32) as f64,
                    1 => f64::from_bits(self.v[f.rn as usize]),
                    other => return Err(A64Error::Unsupported(format!("FCVT src ftype {other}"))),
                };
                match f.dst_ftype {
                    0 => self.v[f.rd as usize] = (src as f32).to_bits() as u64,
                    1 => self.v[f.rd as usize] = src.to_bits(),
                    other => return Err(A64Error::Unsupported(format!("FCVT dst ftype {other}"))),
                }
                self.v_hi[f.rd as usize] = 0;
                Ok(Flow::Next)
            }
            Instruction::FpImmediate(f) => {
                // FMOV Sn/Dn, #imm8 — VFP expand the 8-bit immediate.
                match f.ftype {
                    0 => {
                        let bits = vfp_expand_imm_single(f.imm8);
                        self.v[f.rd as usize] = bits as u64;
                    }
                    1 => {
                        let bits = vfp_expand_imm_double(f.imm8);
                        self.v[f.rd as usize] = bits;
                    }
                    other => {
                        return Err(A64Error::Unsupported(format!("FpImmediate ftype {other}")));
                    }
                }
                self.v_hi[f.rd as usize] = 0;
                Ok(Flow::Next)
            }
            Instruction::FpIntConversion(f) => {
                let dst64 = f.sf64;
                match (f.rmode, f.opcode) {
                    // FCVTZS: float -> signed int, round toward zero (saturating,
                    // matching AArch64 hardware and Rust's `as` cast).
                    (0b11, 0b000) => {
                        let val = self.read_fp_scalar(f.ftype, f.rn)?;
                        let out = if dst64 {
                            (val as i64) as u64
                        } else {
                            (val as i32) as u32 as u64
                        };
                        self.write_x(f.rd, 64, out);
                    }
                    // FCVTZU: float -> unsigned int, round toward zero (saturating).
                    (0b11, 0b001) => {
                        let val = self.read_fp_scalar(f.ftype, f.rn)?;
                        let out = if dst64 {
                            val as u64
                        } else {
                            (val as u32) as u64
                        };
                        self.write_x(f.rd, 64, out);
                    }
                    // SCVTF: signed int -> float.
                    (0b00, 0b010) => {
                        let raw = self.read_x(f.rn, if dst64 { 64 } else { 32 });
                        let val = if dst64 {
                            raw as i64 as f64
                        } else {
                            raw as u32 as i32 as f64
                        };
                        self.write_fp_scalar(f.ftype, f.rd, val)?;
                    }
                    // UCVTF: unsigned int -> float.
                    (0b00, 0b011) => {
                        let raw = self.read_x(f.rn, if dst64 { 64 } else { 32 });
                        let val = if dst64 { raw as f64 } else { raw as u32 as f64 };
                        self.write_fp_scalar(f.ftype, f.rd, val)?;
                    }
                    // FMOV float -> GPR (bit reinterpret).
                    (0b00, 0b110) => {
                        let bits = match f.ftype {
                            0 => self.v[f.rn as usize] & 0xFFFF_FFFF,
                            1 => self.v[f.rn as usize],
                            other => {
                                return Err(A64Error::Unsupported(format!(
                                    "FMOV f->gpr ftype {other}"
                                )));
                            }
                        };
                        self.write_x(f.rd, 64, bits);
                    }
                    // FMOV GPR -> float (bit reinterpret).
                    (0b00, 0b111) => {
                        let raw = self.read_x(f.rn, if f.ftype == 1 { 64 } else { 32 });
                        self.v[f.rd as usize] = raw;
                        self.v_hi[f.rd as usize] = 0;
                    }
                    (r, o) => {
                        return Err(A64Error::Unsupported(format!(
                            "FpIntConversion rmode {r:#b} opcode {o:#b}"
                        )));
                    }
                }
                Ok(Flow::Next)
            }
            Instruction::BranchReg(b) => {
                // opc 2 = RET, 0 = BR (indirect, e.g. jump-table dispatch),
                // 1 = BLR (indirect call).
                match b.opc {
                    0b0010 => {
                        // RET to the top-level sentinel ends interpretation;
                        // otherwise return to the caller's saved address.
                        let target = self.x[b.rn as usize];
                        if target == RET_SENTINEL {
                            Ok(Flow::Ret)
                        } else {
                            Ok(Flow::Branch(target as usize))
                        }
                    }
                    0b0000 => Ok(Flow::Branch(self.x[b.rn as usize] as usize)),
                    0b0001 => {
                        self.x[30] = (pc + 4) as u64;
                        Ok(Flow::Branch(self.x[b.rn as usize] as usize))
                    }
                    other => Err(A64Error::Unsupported(format!("BranchReg opc {other}"))),
                }
            }
            Instruction::UncondBranch(u) => {
                // Direct calls (`bl`) and tail-calls (`b` to another function)
                // are both emitted as `imm26 = 0` plus an ARM64_RELOC_BRANCH26
                // relocation, so a relocation at THIS site — whether or not the
                // branch links — names the real target. Intra-function branches
                // (loop edges) carry no relocation and use their baked `imm26`.
                if u.link {
                    // A call links the return address regardless of resolution.
                    self.x[30] = (pc + 4) as u64;
                }
                let target = if let Some(&t) = self.branch_relocs.get(&pc) {
                    t
                } else {
                    let off = sext(u.imm26 as u64, 26) * 4;
                    (pc as i128 + off) as usize
                };
                Ok(Flow::Branch(target))
            }
            Instruction::CondBranch(cb) => {
                if self.cond_holds(cb.cond) {
                    let off = sext(cb.imm19 as u64, 19) * 4;
                    Ok(Flow::Branch((pc as i128 + off) as usize))
                } else {
                    Ok(Flow::Next)
                }
            }
            Instruction::CompareBranch(cb) => {
                let bits = if cb.sf == 1 { 64 } else { 32 };
                let val = self.read_x(cb.rt, bits);
                let is_zero = val == 0;
                let take = if cb.nonzero { !is_zero } else { is_zero };
                if take {
                    let off = sext(cb.imm19 as u64, 19) * 4;
                    Ok(Flow::Branch((pc as i128 + off) as usize))
                } else {
                    Ok(Flow::Next)
                }
            }
            Instruction::TestBranch(tb) => {
                let bit = (self.read_x(tb.rt, 64) >> tb.bit) & 1 == 1;
                let take = if tb.nonzero { bit } else { !bit };
                if take {
                    let off = sext(tb.imm14 as u64, 14) * 4;
                    Ok(Flow::Branch((pc as i128 + off) as usize))
                } else {
                    Ok(Flow::Next)
                }
            }
            other => Err(A64Error::Unsupported(format!("{other:?}"))),
        }
    }
}

enum Flow {
    Next,
    Branch(usize),
    Ret,
}

// ===========================================================================
// Mach-O parsing: __TEXT,__text bytes + symbol offsets
// ===========================================================================

fn read_u32_le(b: &[u8], off: usize) -> u32 {
    u32::from_le_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]])
}

const MH_MAGIC_64: u32 = 0xFEED_FACF;
const LC_SEGMENT_64: u32 = 0x19;
const LC_SYMTAB: u32 = 0x2;

/// The `__text` section: its bytes, its virtual `addr`, and its file offset.
pub struct MachoText {
    pub bytes: Vec<u8>,
    pub addr: u64,
}

/// Extract the `__TEXT,__text` section (bytes + section addr) of an emitted
/// AArch64 Mach-O object. The `section_64` layout is arch-agnostic, so this is
/// the same parse the x86 harness uses.
pub fn extract_text(obj: &[u8]) -> MachoText {
    assert!(obj.len() >= 32, "object too small for Mach-O header");
    assert_eq!(read_u32_le(obj, 0), MH_MAGIC_64, "not a 64-bit LE Mach-O");
    let ncmds = read_u32_le(obj, 16) as usize;
    let mut off = 32usize;
    for _ in 0..ncmds {
        let cmd = read_u32_le(obj, off);
        let cmdsize = read_u32_le(obj, off + 4) as usize;
        if cmd == LC_SEGMENT_64 {
            let nsects = read_u32_le(obj, off + 64) as usize;
            let mut sec = off + 72;
            for _ in 0..nsects {
                let name_end = obj[sec..sec + 16]
                    .iter()
                    .position(|&c| c == 0)
                    .unwrap_or(16);
                if &obj[sec..sec + name_end] == b"__text" {
                    let addr = u64::from_le_bytes(obj[sec + 32..sec + 40].try_into().unwrap());
                    let size =
                        u64::from_le_bytes(obj[sec + 40..sec + 48].try_into().unwrap()) as usize;
                    let fo = read_u32_le(obj, sec + 48) as usize;
                    return MachoText {
                        bytes: obj[fo..fo + size].to_vec(),
                        addr,
                    };
                }
                sec += 80;
            }
        }
        off += cmdsize;
    }
    panic!("__text section not found");
}

/// Map every defined symbol name to its `n_value` (virtual address) via LC_SYMTAB.
pub fn symbol_addrs(obj: &[u8]) -> HashMap<String, u64> {
    let mut out = HashMap::new();
    let ncmds = read_u32_le(obj, 16) as usize;
    let mut off = 32usize;
    for _ in 0..ncmds {
        let cmd = read_u32_le(obj, off);
        let cmdsize = read_u32_le(obj, off + 4) as usize;
        if cmd == LC_SYMTAB {
            let symoff = read_u32_le(obj, off + 8) as usize;
            let nsyms = read_u32_le(obj, off + 12) as usize;
            let stroff = read_u32_le(obj, off + 16) as usize;
            for i in 0..nsyms {
                let e = symoff + i * 16;
                let strx = read_u32_le(obj, e) as usize;
                let n_value = u64::from_le_bytes(obj[e + 8..e + 16].try_into().unwrap());
                let ns = stroff + strx;
                let ne = obj[ns..].iter().position(|&c| c == 0).unwrap_or(0) + ns;
                let name = String::from_utf8_lossy(&obj[ns..ne]).to_string();
                if !name.is_empty() {
                    out.insert(name, n_value);
                }
            }
        }
        off += cmdsize;
    }
    out
}

/// The ARM64 relocation type for a 26-bit branch (`bl`/`b`) displacement.
const ARM64_RELOC_BRANCH26: u32 = 2;

/// Ordered `n_value` of every LC_SYMTAB symbol, indexed by symbol-table position
/// (the index space that relocation `r_symbolnum` refers to). Empty-name entries
/// are retained so the indices line up.
fn ordered_symbol_values(obj: &[u8]) -> Vec<u64> {
    let mut out = Vec::new();
    let ncmds = read_u32_le(obj, 16) as usize;
    let mut off = 32usize;
    for _ in 0..ncmds {
        let cmd = read_u32_le(obj, off);
        let cmdsize = read_u32_le(obj, off + 4) as usize;
        if cmd == LC_SYMTAB {
            let symoff = read_u32_le(obj, off + 8) as usize;
            let nsyms = read_u32_le(obj, off + 12) as usize;
            for i in 0..nsyms {
                let e = symoff + i * 16;
                let n_value = u64::from_le_bytes(obj[e + 8..e + 16].try_into().unwrap());
                out.push(n_value);
            }
        }
        off += cmdsize;
    }
    out
}

/// Parse the `__TEXT,__text` external BRANCH26 relocations into a map from the
/// `__text` byte-offset of each `bl` site to the resolved callee `__text`
/// byte-offset. Trust Codegen emits direct calls as `bl 0` plus one of these
/// relocations, so this is what lets the interpreter follow calls/recursion.
pub fn text_branch_relocs(obj: &[u8]) -> HashMap<usize, usize> {
    let mut out = HashMap::new();
    let sym_values = ordered_symbol_values(obj);
    let ncmds = read_u32_le(obj, 16) as usize;
    let mut off = 32usize;
    for _ in 0..ncmds {
        let cmd = read_u32_le(obj, off);
        let cmdsize = read_u32_le(obj, off + 4) as usize;
        if cmd == LC_SEGMENT_64 {
            let nsects = read_u32_le(obj, off + 64) as usize;
            let mut sec = off + 72;
            for _ in 0..nsects {
                let name_end = obj[sec..sec + 16]
                    .iter()
                    .position(|&c| c == 0)
                    .unwrap_or(16);
                if &obj[sec..sec + name_end] == b"__text" {
                    let addr = u64::from_le_bytes(obj[sec + 32..sec + 40].try_into().unwrap());
                    let reloff = read_u32_le(obj, sec + 56) as usize;
                    let nreloc = read_u32_le(obj, sec + 60) as usize;
                    for i in 0..nreloc {
                        let e = reloff + i * 8;
                        let r_address = read_u32_le(obj, e) as usize;
                        let info = read_u32_le(obj, e + 4);
                        let r_symbolnum = (info & 0x00FF_FFFF) as usize;
                        let r_extern = (info >> 27) & 1;
                        let r_type = (info >> 28) & 0xF;
                        if r_type == ARM64_RELOC_BRANCH26
                            && r_extern == 1
                            && let Some(&n_value) = sym_values.get(r_symbolnum)
                        {
                            let target = (n_value - addr) as usize;
                            out.insert(r_address, target);
                        }
                    }
                }
                sec += 80;
            }
        }
        off += cmdsize;
    }
    out
}

/// Convenience: interpret function `sym` of a compiled AArch64 object with the
/// given AAPCS64 register setup, returning the i32 value of the low 32 bits of X0.
///
/// `setup` receives a fresh interpreter (already loaded with `__text`) so the
/// caller can place integer args in x0.. and/or FP args in d0.. .
pub fn run_func<F>(obj: &[u8], sym: &str, setup: F) -> Result<u64, A64Error>
where
    F: FnOnce(&mut A64Interp),
{
    let text = extract_text(obj);
    let addrs = symbol_addrs(obj);
    let n_value = *addrs
        .get(sym)
        .ok_or_else(|| A64Error::SymbolNotFound(sym.to_string()))?;
    let entry = (n_value - text.addr) as usize;
    let relocs = text_branch_relocs(obj);
    let mut interp = A64Interp::new(text.bytes).with_branch_relocs(relocs);
    setup(&mut interp);
    interp.run(entry)
}

/// Interpret `sym` and return the low 32 bits sign-interpreted as i32.
pub fn run_i32<F>(obj: &[u8], sym: &str, setup: F) -> Result<i32, A64Error>
where
    F: FnOnce(&mut A64Interp),
{
    run_func(obj, sym, setup).map(|x0| x0 as u32 as i32)
}
