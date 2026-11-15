// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! An independent A64 word classifier for the frame-state analysis.
//!
//! Written from the Arm ARM (DDI 0487) top-level and group encoding tables,
//! not from trust-cg's encoder or its decode checks. It models exactly the
//! instructions a frame description depends on (calls and branches, SP/FP
//! arithmetic, immediate-addressed loads and stores, the jump-table
//! dispatch sequence) and, for every other word, which general-purpose and
//! SIMD&FP registers it may write. A word in a class it does not know (SVE,
//! SME, pointer authentication, memory tagging, system calls) is
//! `Unknown`: the analysis refuses it rather than assuming no effect.

/// A memory access's addressing mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Mode {
    /// `[base, #imm]`: no writeback.
    Offset,
    /// `[base, #imm]!`: access at base+imm, then base = base+imm.
    Pre,
    /// `[base], #imm`: access at base, then base = base+imm.
    Post,
}

/// An immediate-addressed load or store of one or two registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Access {
    pub(crate) load: bool,
    /// SIMD&FP registers (`V` bit) rather than general-purpose ones.
    pub(crate) vector: bool,
    /// Bytes per register.
    pub(crate) size: u8,
    pub(crate) rt: u8,
    /// The second register of a pair.
    pub(crate) rt2: Option<u8>,
    /// Base register (31 is SP).
    pub(crate) rn: u8,
    pub(crate) imm: i64,
    pub(crate) mode: Mode,
    /// A general-purpose load sign-extends or narrows (the value is not the
    /// 8-byte slot verbatim).
    pub(crate) transforms: bool,
}

/// The memory a word that is not an `Access` may write: a release,
/// exclusive, compare-and-swap, atomic, unprivileged, unscaled-RCpc,
/// register-offset or SIMD structure store.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Store {
    /// Base register (31 is SP).
    pub(crate) base: u8,
    /// `(offset, bytes)`: the written bytes start `offset` bytes from the
    /// base and span at most `bytes`. `None` when an index register offsets
    /// the address (the store-alias boundary `flow` states).
    pub(crate) range: Option<(i64, i64)>,
}

impl Store {
    fn at(base: u8, offset: i64, bytes: i64) -> Self {
        Self {
            base,
            range: Some((offset, bytes)),
        }
    }
}

/// Registers a word may write, for words the analysis does not model.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) struct Effects {
    /// Bit n: general-purpose register Xn (n < 31) may be written.
    pub(crate) gpr: u32,
    /// SP may be written (to an unknown value).
    pub(crate) sp: bool,
    /// Bit n: SIMD&FP register Vn may be written.
    pub(crate) vector: u32,
    /// The memory the word may write, if it is a store.
    pub(crate) store: Option<Store>,
}

impl Effects {
    fn gpr(rd: u8) -> Self {
        let mut effects = Self::default();
        effects.add_gpr(rd);
        effects
    }

    fn gpr_or_sp(rd: u8) -> Self {
        if rd == 31 {
            Self {
                sp: true,
                ..Self::default()
            }
        } else {
            Self::gpr(rd)
        }
    }

    fn vector(rd: u8) -> Self {
        Self {
            vector: 1 << rd,
            ..Self::default()
        }
    }

    fn add_gpr(&mut self, rd: u8) {
        if rd < 31 {
            self.gpr |= 1 << rd;
        }
    }

    fn add_base_writeback(&mut self, rn: u8) {
        if rn == 31 {
            self.sp = true;
        } else {
            self.gpr |= 1 << rn;
        }
    }
}

/// One decoded word.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Word {
    /// `BL` (direct, PC-relative word displacement) or `BLR Xn`.
    Call { indirect: bool, displacement: i64 },
    /// `B` with its PC-relative byte displacement.
    Branch { displacement: i64 },
    /// `B.cond`, `CBZ`, `CBNZ`, `TBZ`, `TBNZ`.
    CondBranch { displacement: i64 },
    /// `RET Xn`.
    Return,
    /// `BR Xn`.
    IndirectBranch { rn: u8 },
    /// `BRK`, `HLT`, `UDF`: no successor.
    Trap,
    /// 64-bit `ADD`/`SUB` (immediate): `rd = rn + delta`. 31 is SP for both
    /// unless the form sets flags (then rd 31 is XZR: no write).
    AddImm {
        rd: u8,
        rn: u8,
        delta: i64,
        setflags: bool,
    },
    /// 64-bit `ADD Xd, Xn, Xm` (shifted register, LSL #0, no flags).
    AddReg { rd: u8, rn: u8, rm: u8 },
    /// `ADR Xd, label`: byte displacement from this word.
    Adr { rd: u8, displacement: i64 },
    /// `MOV Xd, Xm` (`ORR Xd, XZR, Xm`).
    MovReg { rd: u8, rm: u8 },
    /// `LDRSW Xt, [Xn, Xm, LSL #2]`.
    LdrswScaled { rt: u8, rn: u8, rm: u8 },
    /// An immediate-addressed load/store (single or pair).
    Access(Access),
    /// Any other known word.
    Other(Effects),
    /// A word outside the classes this classifier knows.
    Unknown,
}

fn bits(word: u32, hi: u32, lo: u32) -> u32 {
    (word >> lo) & ((1u32 << (hi - lo + 1)) - 1)
}

fn sign_extend(value: u32, width: u32) -> i64 {
    let shift = 64 - width;
    (i64::from(value) << shift) >> shift
}

fn rd(word: u32) -> u8 {
    (word & 31) as u8
}

fn rn(word: u32) -> u8 {
    bits(word, 9, 5) as u8
}

/// Classify one little-endian A64 word.
pub(crate) fn decode(word: u32) -> Word {
    // Branches, exception generation and system (op0 = x101).
    if bits(word, 28, 26) == 0b101 {
        return decode_branch_system(word);
    }
    // Data processing - immediate (op0 = 100x).
    if bits(word, 28, 26) == 0b100 {
        return decode_dp_immediate(word);
    }
    // Loads and stores (op0 = x1x0).
    if bits(word, 27, 27) == 1 && bits(word, 25, 25) == 0 {
        return decode_load_store(word);
    }
    // Data processing - register (op0 = x101).
    if bits(word, 27, 25) == 0b101 {
        return decode_dp_register(word);
    }
    // Data processing - SIMD and floating point (op0 = x111).
    if bits(word, 27, 25) == 0b111 {
        return decode_simd_fp(word);
    }
    // op0 = 0000: UDF (bit 31 clear) is the only admitted word.
    if word & 0xffff_0000 == 0 {
        return Word::Trap;
    }
    Word::Unknown
}

fn decode_branch_system(word: u32) -> Word {
    if word & 0x7c00_0000 == 0x1400_0000 {
        let displacement = sign_extend(bits(word, 25, 0), 26) * 4;
        return if word & 0x8000_0000 != 0 {
            Word::Call {
                indirect: false,
                displacement,
            }
        } else {
            Word::Branch { displacement }
        };
    }
    if word & 0xff00_0010 == 0x5400_0000 {
        return Word::CondBranch {
            displacement: sign_extend(bits(word, 23, 5), 19) * 4,
        };
    }
    if word & 0x7e00_0000 == 0x3400_0000 {
        return Word::CondBranch {
            displacement: sign_extend(bits(word, 23, 5), 19) * 4,
        };
    }
    if word & 0x7e00_0000 == 0x3600_0000 {
        return Word::CondBranch {
            displacement: sign_extend(bits(word, 18, 5), 14) * 4,
        };
    }
    match word & 0xffff_fc1f {
        0xd61f_0000 => return Word::IndirectBranch { rn: rn(word) },
        0xd63f_0000 => {
            return Word::Call {
                indirect: true,
                displacement: 0,
            };
        }
        0xd65f_0000 => return Word::Return,
        _ => {}
    }
    // BRK / HLT.
    if word & 0xffe0_001f == 0xd420_0000 || word & 0xffe0_001f == 0xd440_0000 {
        return Word::Trap;
    }
    // Hints (NOP, BTI, ...), barriers, PSTATE writes, MSR, SYS: no
    // general-purpose destination.
    if word & 0xffff_f01f == 0xd503_201f
        || word & 0xffff_f01f == 0xd503_301f
        || word & 0xfff8_f01f == 0xd500_401f
        || word & 0xfff0_0000 == 0xd510_0000
        || word & 0xfff8_0000 == 0xd508_0000
    {
        // DC ZVA / DC GVA / DC GZVA (SYS #3, C7, C4) zero a whole block at
        // Xt: a store the analysis does not bound.
        if word & 0xffff_ff00 == 0xd50b_7400 {
            return Word::Unknown;
        }
        // Pointer-authentication hints rewrite X17 or X30 implicitly.
        if word & 0xffff_f01f == 0xd503_201f {
            let crm_op2 = bits(word, 11, 5);
            // HINT #7 (XPACLRI), #8-#15 (the 1716 forms) and #24-#31 (the Z
            // and SP forms).
            let pointer_auth = matches!(crm_op2, 7 | 8..=15 | 24..=31);
            if pointer_auth {
                return Word::Unknown;
            }
        }
        return Word::Other(Effects::default());
    }
    // MRS / SYSL: write Rt.
    if word & 0xfff0_0000 == 0xd530_0000 || word & 0xfff8_0000 == 0xd528_0000 {
        return Word::Other(Effects::gpr(rd(word)));
    }
    Word::Unknown
}

fn decode_dp_immediate(word: u32) -> Word {
    let rd_field = rd(word);
    match bits(word, 25, 23) {
        0b000 | 0b001 => {
            if word & 0x8000_0000 == 0 {
                let immlo = bits(word, 30, 29);
                let immhi = bits(word, 23, 5);
                Word::Adr {
                    rd: rd_field,
                    displacement: sign_extend((immhi << 2) | immlo, 21),
                }
            } else {
                Word::Other(Effects::gpr(rd_field))
            }
        }
        0b010 => {
            let sf = bits(word, 31, 31) == 1;
            let sub = bits(word, 30, 30) == 1;
            let setflags = bits(word, 29, 29) == 1;
            let shift = if bits(word, 22, 22) == 1 { 12 } else { 0 };
            let imm = i64::from(bits(word, 21, 10)) << shift;
            if !sf {
                return Word::Other(if setflags {
                    Effects::gpr(rd_field)
                } else {
                    Effects::gpr_or_sp(rd_field)
                });
            }
            Word::AddImm {
                rd: rd_field,
                rn: rn(word),
                delta: if sub { -imm } else { imm },
                setflags,
            }
        }
        0b011 => Word::Unknown, // add/sub immediate with tags (MTE)
        0b100 => {
            let opc = bits(word, 30, 29);
            Word::Other(if opc == 0b11 {
                Effects::gpr(rd_field)
            } else {
                Effects::gpr_or_sp(rd_field)
            })
        }
        _ => Word::Other(Effects::gpr(rd_field)),
    }
}

fn decode_dp_register(word: u32) -> Word {
    let rd_field = rd(word);
    let op1 = bits(word, 28, 28);
    let op2 = bits(word, 24, 21);
    if op1 == 0 {
        if op2 & 0b1000 == 0 {
            // Logical (shifted register). MOV Xd, Xm is ORR Xd, XZR, Xm.
            if word & 0xffe0_ffe0 == 0xaa00_03e0 {
                return Word::MovReg {
                    rd: rd_field,
                    rm: bits(word, 20, 16) as u8,
                };
            }
            return Word::Other(Effects::gpr(rd_field));
        }
        if op2 & 0b0001 == 0 {
            // Add/subtract (shifted register): Rd 31 is XZR.
            if word & 0xffe0_fc00 == 0x8b00_0000 {
                return Word::AddReg {
                    rd: rd_field,
                    rn: rn(word),
                    rm: bits(word, 20, 16) as u8,
                };
            }
            return Word::Other(Effects::gpr(rd_field));
        }
        // Add/subtract (extended register): Rd 31 is SP unless S.
        let setflags = bits(word, 29, 29) == 1;
        return Word::Other(if setflags {
            Effects::gpr(rd_field)
        } else {
            Effects::gpr_or_sp(rd_field)
        });
    }
    match op2 {
        0b0000 => {
            let op3 = bits(word, 15, 10);
            if op3 == 0 {
                // ADC/SBC(S).
                Word::Other(Effects::gpr(rd_field))
            } else {
                // RMIF / SETF8 / SETF16 write flags only.
                Word::Other(Effects::default())
            }
        }
        // Conditional compare (register / immediate): flags only.
        0b0010 => Word::Other(Effects::default()),
        0b0100 | 0b0110 => Word::Other(Effects::gpr(rd_field)),
        _ if op2 & 0b1000 != 0 => Word::Other(Effects::gpr(rd_field)),
        _ => Word::Unknown,
    }
}

fn decode_simd_fp(word: u32) -> Word {
    let rd_field = rd(word);
    // SVE and SME share no encodings with this group; bit 28 = 1 with bits
    // 27:25 = 111 is scalar FP / AdvSIMD scalar, bit 28 = 0 AdvSIMD vector.
    // Conversion between floating point and integer.
    if word & 0x5f20_fc00 == 0x1e20_0000 {
        let opcode = bits(word, 18, 16);
        return Word::Other(if matches!(opcode, 0 | 1 | 4 | 5 | 6) {
            Effects::gpr(rd_field)
        } else {
            Effects::vector(rd_field)
        });
    }
    // Conversion between floating point and fixed point.
    if word & 0x5f20_0000 == 0x1e00_0000 {
        let opcode = bits(word, 18, 16);
        return Word::Other(if matches!(opcode, 0 | 1) {
            Effects::gpr(rd_field)
        } else {
            Effects::vector(rd_field)
        });
    }
    // Floating-point compare and conditional compare: flags only.
    if word & 0x5f20_3c00 == 0x1e20_2000 || word & 0x5f20_0c00 == 0x1e20_0400 {
        return Word::Other(Effects::default());
    }
    // AdvSIMD copy: SMOV / UMOV write a general-purpose register.
    if word & 0x9fe0_8400 == 0x0e00_0400 {
        let imm4 = bits(word, 14, 11);
        let op = bits(word, 29, 29);
        if op == 0 && (imm4 == 0b0101 || imm4 == 0b0111) {
            return Word::Other(Effects::gpr(rd_field));
        }
        return Word::Other(Effects::vector(rd_field));
    }
    // Every other AdvSIMD / FP data-processing word writes Vd.
    Word::Other(Effects::vector(rd_field))
}

fn decode_load_store(word: u32) -> Word {
    let op0 = bits(word, 31, 28);
    let vector = bits(word, 26, 26) == 1;
    let op2 = bits(word, 24, 23);
    let op3 = bits(word, 21, 16);
    let op4 = bits(word, 11, 10);
    let rt = rd(word);
    let base = rn(word);

    // AdvSIMD load/store multiple or single structures.
    if op0 & 0b1011 == 0 && vector {
        return decode_simd_structures(word);
    }
    if op0 & 0b0011 == 0b0000 && !vector && op2 & 0b10 == 0 {
        return decode_exclusive(word);
    }
    if op0 & 0b0011 == 0b0001 {
        if op2 & 0b10 == 0 {
            // Load register (literal): writes Rt unless PRFM.
            let opc = bits(word, 31, 30);
            if !vector && opc == 0b11 {
                return Word::Other(Effects::default());
            }
            return Word::Other(if vector {
                Effects::vector(rt)
            } else {
                Effects::gpr(rt)
            });
        }
        // LDAPUR/STLUR (unscaled immediate), RCpc; memory tagging (vector
        // clear, op3 bit 5).
        if !vector && op3 & 0b10_0000 == 0 && op4 == 0 {
            let opc = bits(word, 23, 22);
            return Word::Other(if opc == 0 {
                Effects {
                    store: Some(Store::at(
                        base,
                        sign_extend(bits(word, 20, 12), 9),
                        1 << bits(word, 31, 30),
                    )),
                    ..Effects::default()
                }
            } else {
                Effects::gpr(rt)
            });
        }
        return Word::Unknown;
    }
    if op0 & 0b0011 == 0b0010 {
        return decode_pair(word, vector, op2);
    }
    if op0 & 0b0011 == 0b0011 {
        if op2 & 0b10 == 0b10 {
            return decode_single(word, vector, Mode::Offset, true);
        }
        if op3 & 0b10_0000 == 0 {
            return match op4 {
                0b00 => decode_single(word, vector, Mode::Offset, false),
                0b01 => decode_single(word, vector, Mode::Post, false),
                0b11 => decode_single(word, vector, Mode::Pre, false),
                // Unprivileged LDTR/STTR.
                _ => match single_kind(word, vector) {
                    Some((true, _, _)) => Word::Other(Effects::gpr(rt)),
                    Some((false, size, _)) => Word::Other(Effects {
                        store: Some(Store::at(
                            base,
                            sign_extend(bits(word, 20, 12), 9),
                            i64::from(size),
                        )),
                        ..Effects::default()
                    }),
                    None => Word::Unknown,
                },
            };
        }
        return match op4 {
            0b00 => match (vector, bits(word, 15, 15), bits(word, 14, 12)) {
                // LDAPR: an acquire load.
                (false, 1, 0b100) => Word::Other(Effects::gpr(rt)),
                // LD<op> (ST<op> aliases write XZR) and SWP: a
                // read-modify-write of `size` bytes at the base.
                (false, 0, _) | (false, 1, 0b000) => Word::Other(Effects {
                    store: Some(Store::at(base, 0, 1 << bits(word, 31, 30))),
                    ..Effects::gpr(rt)
                }),
                // The 64-byte LS64 transfers, the read-check-write forms
                // (whose size field does not give the bytes written) and
                // the floating-point atomics.
                _ => Word::Unknown,
            },
            0b10 => {
                // Register offset.
                if word & 0xffe0_fc00 == 0xb8a0_7800 {
                    return Word::LdrswScaled {
                        rt,
                        rn: base,
                        rm: bits(word, 20, 16) as u8,
                    };
                }
                match single_kind(word, vector) {
                    Some((true, _, _)) => Word::Other(if vector {
                        Effects::vector(rt)
                    } else {
                        Effects::gpr(rt)
                    }),
                    Some((false, _, prefetch)) => Word::Other(if prefetch {
                        Effects::default()
                    } else {
                        Effects {
                            store: Some(Store { base, range: None }),
                            ..Effects::default()
                        }
                    }),
                    None => Word::Unknown,
                }
            }
            // Pointer-authenticated loads.
            _ => Word::Unknown,
        };
    }
    Word::Unknown
}

/// `(load, bytes, prefetch)` of a single-register load/store from its
/// size/V/opc fields, `None` for an unallocated combination.
fn single_kind(word: u32, vector: bool) -> Option<(bool, u8, bool)> {
    let size = bits(word, 31, 30);
    let opc = bits(word, 23, 22);
    if vector {
        return match (opc, size) {
            (0b00, _) => Some((false, 1 << size, false)),
            (0b01, _) => Some((true, 1 << size, false)),
            (0b10, 0b00) => Some((false, 16, false)),
            (0b11, 0b00) => Some((true, 16, false)),
            _ => None,
        };
    }
    match (opc, size) {
        (0b00, _) => Some((false, 1 << size, false)),
        (0b01, _) => Some((true, 1 << size, false)),
        (0b10, 0b11) => Some((false, 8, true)),
        (0b10, _) => Some((true, 1 << size, false)),
        (0b11, 0b00 | 0b01) => Some((true, 1 << size, false)),
        _ => None,
    }
}

fn decode_single(word: u32, vector: bool, mode: Mode, unsigned_offset: bool) -> Word {
    let Some((load, size, prefetch)) = single_kind(word, vector) else {
        return Word::Unknown;
    };
    if prefetch {
        return Word::Other(Effects::default());
    }
    let imm = if unsigned_offset {
        i64::from(bits(word, 21, 10)) * i64::from(size)
    } else {
        sign_extend(bits(word, 20, 12), 9)
    };
    let opc = bits(word, 23, 22);
    Word::Access(Access {
        load,
        vector,
        size,
        rt: rd(word),
        rt2: None,
        rn: rn(word),
        imm,
        mode,
        transforms: !vector && load && (size != 8 || opc & 0b10 != 0),
    })
}

fn decode_pair(word: u32, vector: bool, op2: u32) -> Word {
    let opc = bits(word, 31, 30);
    let load = bits(word, 22, 22) == 1;
    let size: u8 = match (vector, opc) {
        (false, 0b00) => 4,
        (false, 0b01) => {
            if !load {
                // STGP (memory tagging).
                return Word::Unknown;
            }
            4 // LDPSW
        }
        (false, 0b10) => 8,
        (true, 0b00) => 4,
        (true, 0b01) => 8,
        (true, 0b10) => 16,
        _ => return Word::Unknown,
    };
    let mode = match op2 {
        0b00 | 0b10 => Mode::Offset,
        0b01 => Mode::Post,
        _ => Mode::Pre,
    };
    Word::Access(Access {
        load,
        vector,
        size,
        rt: rd(word),
        rt2: Some(bits(word, 14, 10) as u8),
        rn: rn(word),
        imm: sign_extend(bits(word, 21, 15), 7) * i64::from(size),
        mode,
        transforms: !vector && load && (size != 8),
    })
}

fn decode_exclusive(word: u32) -> Word {
    let size = bits(word, 31, 30);
    let o2 = bits(word, 23, 23);
    let load = bits(word, 22, 22) == 1;
    let o1 = bits(word, 21, 21);
    let rs = bits(word, 20, 16) as u8;
    let rt2 = bits(word, 14, 10) as u8;
    let rt = rd(word);
    let base = rn(word);
    // Bytes of one register: `size` for the single-register forms; bit 30
    // selects 32- or 64-bit registers for the pair forms.
    let single = 1i64 << size;
    let pair = 2 * (4i64 << (size & 1));
    let mut effects = Effects::default();
    let store = |bytes: i64| Some(Store::at(base, 0, bytes));
    match (o2, o1, load) {
        (0, 0, false) => {
            // STXR / STLXR.
            effects.add_gpr(rs);
            effects.store = store(single);
        }
        (0, 0, true) => effects.add_gpr(rt),
        (0, 1, false) if size & 0b10 != 0 => {
            // STXP / STLXP.
            effects.add_gpr(rs);
            effects.store = store(pair);
        }
        (0, 1, true) if size & 0b10 != 0 => {
            effects.add_gpr(rt);
            effects.add_gpr(rt2);
        }
        (0, 1, _) => {
            // CASP: the even/odd pair Rs, Rs+1.
            effects.add_gpr(rs);
            effects.add_gpr(rs.saturating_add(1));
            effects.store = store(pair);
        }
        (1, 0, false) => effects.store = store(single), // STLR / STLLR
        (1, 0, true) => effects.add_gpr(rt),
        _ => {
            // CAS.
            effects.add_gpr(rs);
            effects.store = store(single);
        }
    }
    Word::Other(effects)
}

fn decode_simd_structures(word: u32) -> Word {
    let load = bits(word, 22, 22) == 1;
    let post = bits(word, 23, 23) == 1;
    let single = bits(word, 24, 24) == 1;
    let rt = rd(word);
    let base = rn(word);
    // Registers transferred, and the bytes a store writes from the base.
    let (count, bytes): (u8, i64) = if single {
        let r = bits(word, 21, 21);
        let opcode_hi = bits(word, 15, 13);
        // selem = ((opcode<0> << 1) | R) + 1
        let selem = ((opcode_hi & 1) << 1 | r) + 1;
        // One element per register: B, H, S or D by opcode<2:1> and size.
        let element = match opcode_hi >> 1 {
            0b00 => 1,
            0b01 => 2,
            0b10 if bits(word, 10, 10) == 0 => 4,
            _ => 8,
        };
        (selem as u8, i64::from(selem) * element)
    } else {
        let count = match bits(word, 15, 12) {
            0b0000 | 0b0010 => 4,
            0b0100 | 0b0110 => 3,
            0b0111 => 1,
            0b1000 | 0b1010 => 2,
            _ => return Word::Unknown,
        };
        // Q selects 8- or 16-byte registers.
        (count, i64::from(count) * (8 << bits(word, 30, 30)))
    };
    let mut effects = Effects::default();
    if load {
        for i in 0..count {
            effects.vector |= 1 << ((rt + i) % 32);
        }
    } else {
        effects.store = Some(Store::at(base, 0, bytes));
    }
    if post {
        effects.add_base_writeback(base);
    }
    Word::Other(effects)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frame_words_decode_to_their_fields() {
        // stp x29, x30, [sp, #-16]!
        assert_eq!(
            decode(0xa9bf_7bfd),
            Word::Access(Access {
                load: false,
                vector: false,
                size: 8,
                rt: 29,
                rt2: Some(30),
                rn: 31,
                imm: -16,
                mode: Mode::Pre,
                transforms: false,
            })
        );
        // mov x29, sp (add x29, sp, #0)
        assert_eq!(
            decode(0x9100_03fd),
            Word::AddImm {
                rd: 29,
                rn: 31,
                delta: 0,
                setflags: false
            }
        );
        // sub sp, sp, #32
        assert_eq!(
            decode(0xd100_83ff),
            Word::AddImm {
                rd: 31,
                rn: 31,
                delta: -32,
                setflags: false
            }
        );
        // ldp x29, x30, [sp], #16
        assert_eq!(
            decode(0xa8c1_7bfd),
            Word::Access(Access {
                load: true,
                vector: false,
                size: 8,
                rt: 29,
                rt2: Some(30),
                rn: 31,
                imm: 16,
                mode: Mode::Post,
                transforms: false,
            })
        );
        // stp d9, d8, [sp, #16]
        assert_eq!(
            decode(0x6d01_23e9),
            Word::Access(Access {
                load: false,
                vector: true,
                size: 8,
                rt: 9,
                rt2: Some(8),
                rn: 31,
                imm: 16,
                mode: Mode::Offset,
                transforms: false,
            })
        );
        // str x19, [sp, #8]
        assert_eq!(
            decode(0xf900_07f3),
            Word::Access(Access {
                load: false,
                vector: false,
                size: 8,
                rt: 19,
                rt2: None,
                rn: 31,
                imm: 8,
                mode: Mode::Offset,
                transforms: false,
            })
        );
    }

    #[test]
    fn control_words_decode() {
        assert_eq!(
            decode(0x9400_0000),
            Word::Call {
                indirect: false,
                displacement: 0
            }
        );
        assert_eq!(
            decode(0xd63f_0100),
            Word::Call {
                indirect: true,
                displacement: 0
            }
        );
        assert_eq!(decode(0xd65f_03c0), Word::Return);
        assert_eq!(decode(0xd61f_0100), Word::IndirectBranch { rn: 8 });
        assert_eq!(decode(0x17ff_ffff), Word::Branch { displacement: -4 });
        assert_eq!(decode(0x5400_0040), Word::CondBranch { displacement: 8 });
        assert_eq!(decode(0xb400_0040), Word::CondBranch { displacement: 8 });
        assert_eq!(decode(0x3608_0040), Word::CondBranch { displacement: 8 });
        assert_eq!(decode(0xd420_0020), Word::Trap);
        assert_eq!(decode(0x0000_0000), Word::Trap);
    }

    #[test]
    fn register_writes_are_classified() {
        // add x19, x0, x1 (shifted register).
        assert_eq!(
            decode(0x8b01_0013),
            Word::AddReg {
                rd: 19,
                rn: 0,
                rm: 1
            }
        );
        // mov x19, x0
        assert_eq!(decode(0xaa00_03f3), Word::MovReg { rd: 19, rm: 0 });
        // cmp x0, x1 (subs xzr): no write.
        assert_eq!(decode(0xeb01_001f), Word::Other(Effects::default()));
        // fcmp d8, d9: no write even though Rd holds opcode2 bits.
        assert_eq!(decode(0x1e69_2100), Word::Other(Effects::default()));
        // fadd d8, d0, d1 writes v8.
        assert_eq!(decode(0x1e61_2808), Word::Other(Effects::vector(8)));
        // fmov x19, d0 writes x19.
        assert_eq!(decode(0x9e66_0013), Word::Other(Effects::gpr(19)));
        // sub sp, sp, x8 (extended register) writes SP.
        assert_eq!(
            decode(0xcb28_63ff),
            Word::Other(Effects {
                sp: true,
                ..Effects::default()
            })
        );
        // ldrsw x9, [x8, x9, lsl #2]
        assert_eq!(
            decode(0xb8a9_7909),
            Word::LdrswScaled {
                rt: 9,
                rn: 8,
                rm: 9
            }
        );
        // adr x8, #+64
        assert_eq!(
            decode(0x1000_0208),
            Word::Adr {
                rd: 8,
                displacement: 64
            }
        );
        // An SVE word is unknown.
        assert_eq!(decode(0x0420_0000), Word::Unknown);
    }

    #[test]
    fn stores_carry_the_bytes_they_write() {
        let store = |word: u32| match decode(word) {
            Word::Other(effects) => effects.store,
            other => panic!("{word:#010x} decoded to {other:?}"),
        };
        // stlr xzr, [x29]; stxr w0, xzr, [x29]; stxp w0, x1, x2, [x29]
        assert_eq!(store(0xc89f_ffbf), Some(Store::at(29, 0, 8)));
        assert_eq!(store(0xc800_7fbf), Some(Store::at(29, 0, 8)));
        assert_eq!(store(0xc820_0ba1), Some(Store::at(29, 0, 16)));
        // ldadd x0, x1, [x29]; stlur xzr, [x29, #8]; sttr xzr, [x29]
        assert_eq!(store(0xf820_03a1), Some(Store::at(29, 0, 8)));
        assert_eq!(store(0xd900_83bf), Some(Store::at(29, 8, 8)));
        assert_eq!(store(0xf800_0bbf), Some(Store::at(29, 0, 8)));
        // st1 {v0.2d}, [x29]; st1 {v0.d}[1], [x29]
        assert_eq!(store(0x4c00_7fa0), Some(Store::at(29, 0, 16)));
        assert_eq!(store(0x4d00_87a0), Some(Store::at(29, 0, 8)));
        // str x0, [x29, x1]: an index register (the stated boundary).
        assert_eq!(
            store(0xf821_6ba0),
            Some(Store {
                base: 29,
                range: None
            })
        );
        // ldar x0, [x29] and ldapr x0, [x1] are loads.
        assert_eq!(store(0xc8df_ffa0), None);
        assert_eq!(store(0xf8bf_c020), None);
        // st64b x0, [x1] and dc zva, x0 are refused.
        assert_eq!(decode(0xf83f_9020), Word::Unknown);
        assert_eq!(decode(0xd50b_7420), Word::Unknown);
    }
}
