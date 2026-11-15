// trust-cg-verify/src/x86_volatile_trace.rs - the volatile ACCESS TRACE obligation for x86-64
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Every volatile access the SOURCE asks for is emitted exactly once, at the
//! same width and in the same direction.
//!
//! # What this is for
//!
//! The sixteen `Volatile*` coverage rows are RED with a stated reason: they
//! stay RED "until one obligation covers both the value/effect and the
//! optimizer observation/ordering boundary". Their VALUE/EFFECT is already
//! covered — a volatile MOV is byte-identical to the plain form, so
//! `x86_addressing_proofs` carries its address and the reconstruction carries
//! its value. What no obligation covered is the thing that actually makes a
//! volatile access different from a plain one: that the compiler emits exactly
//! the accesses the program asked for, no more and no fewer.
//!
//! # Why the two sides are independent
//!
//! SOURCE is `trust_ir`: `Inst::Load { volatile: true, ty, .. }` and
//! `Inst::Store { volatile: true, ty, .. }`. The flag is a fact about the
//! PROGRAM, set by the frontend, and the width comes from the trust_ir type.
//!
//! MACHINE is the emitted opcode: `VolatileMovRM8`, `VolatileMovMR32`,
//! `VolatileMovsdRM` and their siblings. The width and direction come from the
//! OPCODE, and the opcode is what the backend chose.
//!
//! Neither side is computed from the other. That is the difference between this
//! obligation and `x86_reconstruct_effective_address`, which built both of its
//! halves from the same machine operand and so could refute nothing (see
//! `report_which_credited_opcodes_have_no_address_teeth`).
//!
//! # The six ways a compiler breaks volatile, and which are caught here
//!
//! | hazard | caught by |
//! |---|---|
//! | ELIDE a volatile access | the multiset: the machine is missing one |
//! | DUPLICATE it | the multiset: the machine has one too many |
//! | WIDEN it (`i8` store becomes `i32`) | the multiset: the widths differ |
//! | NARROW it | the multiset: the widths differ |
//! | change its DIRECTION (load for store) | the multiset: the directions differ |
//! | REORDER two of them | the per-block SEQUENCE |
//!
//! MERGING two accesses into one is elision plus widening and is caught twice.
//!
//! # Why the function-level check is a MULTISET and not a flat sequence
//!
//! A flat sequence over `block_order` would be wrong, not stricter. Block
//! layout is free to permute `block_order` (`X86BranchLayout`'s cold-arm sink
//! does exactly that) without changing execution order at all, so a flat
//! comparison would report a violation for a transformation that is correct.
//! The multiset is invariant under block permutation and still catches every
//! hazard that changes WHAT is emitted. Ordering is then checked WITHIN each
//! block, where program order is genuine and no layout pass may permute it.

use std::collections::BTreeMap;

use trust_cg_ir::X86Opcode;
use trust_cg_lower::x86_64_isel::X86ISelFunction;

/// Which register file a volatile access moves through.
///
/// Part of the comparison because a backend that lowered a volatile `f64` load
/// to a GPR load would move the same bytes and still be wrong: the access must
/// be the one the source asked for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AccessClass {
    /// A general-purpose register access.
    Gpr,
    /// A scalar floating-point (XMM) access.
    Fp,
    /// A 128-bit packed (XMM) access.
    V128,
}

/// One volatile access, as either side describes it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VolatileAccess {
    /// Width of the access in bits.
    pub width_bits: u32,
    /// True when memory is written.
    pub is_store: bool,
    /// Which register file the access moves through.
    pub class: AccessClass,
}

impl std::fmt::Display for VolatileAccess {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {:?}{}",
            if self.is_store { "store" } else { "load" },
            self.class,
            self.width_bits
        )
    }
}

/// The volatile opcode's access, or `None` when the opcode is not a volatile
/// memory access.
///
/// This is the MACHINE side of the obligation: the width and direction are read
/// from the OPCODE the backend chose, never from the source.
#[must_use]
pub fn volatile_access_of_opcode(opcode: X86Opcode) -> Option<VolatileAccess> {
    use X86Opcode as O;
    let gpr = |width_bits, is_store| {
        Some(VolatileAccess {
            width_bits,
            is_store,
            class: AccessClass::Gpr,
        })
    };
    let fp = |width_bits, is_store| {
        Some(VolatileAccess {
            width_bits,
            is_store,
            class: AccessClass::Fp,
        })
    };
    let v128 = |is_store| {
        Some(VolatileAccess {
            width_bits: 128,
            is_store,
            class: AccessClass::V128,
        })
    };
    match opcode {
        // The zero-extending volatile loads read the same one byte / word:
        // what they leave in the register is the value leg's business, the
        // ACCESS is the same.
        O::VolatileMovRM8 | O::VolatileMovzxRM8 => gpr(8, false),
        O::VolatileMovRM16 | O::VolatileMovzxRM16 => gpr(16, false),
        O::VolatileMovRM32 => gpr(32, false),
        O::VolatileMovRM => gpr(64, false),
        O::VolatileMovMR8 => gpr(8, true),
        O::VolatileMovMR16 => gpr(16, true),
        O::VolatileMovMR32 => gpr(32, true),
        O::VolatileMovMR => gpr(64, true),
        O::VolatileMovssRM => fp(32, false),
        O::VolatileMovsdRM => fp(64, false),
        O::VolatileMovssMR => fp(32, true),
        O::VolatileMovsdMR => fp(64, true),
        O::VolatileMovdquRM | O::VolatileMovdqaRM => v128(false),
        O::VolatileMovdquMR | O::VolatileMovdqaMR => v128(true),
        _ => None,
    }
}

/// Every volatile opcode this obligation knows how to read.
///
/// Published so a gate can assert the set is COMPLETE against the coverage
/// gate's own volatile row set — an opcode that the backend emits but this
/// module does not recognise would be invisible to the trace, which is the one
/// way this check could pass while missing an access.
pub const RECOGNISED_VOLATILE_OPCODES: &[X86Opcode] = &[
    X86Opcode::VolatileMovRM8,
    X86Opcode::VolatileMovRM16,
    X86Opcode::VolatileMovRM32,
    X86Opcode::VolatileMovRM,
    X86Opcode::VolatileMovMR8,
    X86Opcode::VolatileMovMR16,
    X86Opcode::VolatileMovMR32,
    X86Opcode::VolatileMovMR,
    X86Opcode::VolatileMovssRM,
    X86Opcode::VolatileMovsdRM,
    X86Opcode::VolatileMovssMR,
    X86Opcode::VolatileMovsdMR,
    X86Opcode::VolatileMovdquRM,
    X86Opcode::VolatileMovdqaRM,
    X86Opcode::VolatileMovdquMR,
    X86Opcode::VolatileMovdqaMR,
    X86Opcode::VolatileMovzxRM8,
    X86Opcode::VolatileMovzxRM16,
];

/// A function's volatile accesses: the flat multiset, and the sequence WITHIN
/// each block.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct VolatileTrace {
    /// Per-block sequences, keyed by the block's position in `block_order`.
    /// Program order within a block is genuine and no layout pass may permute
    /// it, so this is where ordering is checked.
    pub per_block: Vec<Vec<VolatileAccess>>,
}

impl VolatileTrace {
    /// The flat multiset, invariant under block permutation.
    #[must_use]
    pub fn multiset(&self) -> BTreeMap<VolatileAccess, usize> {
        let mut out = BTreeMap::new();
        for block in &self.per_block {
            for access in block {
                *out.entry(*access).or_insert(0) += 1;
            }
        }
        out
    }

    /// Total accesses.
    #[must_use]
    pub fn len(&self) -> usize {
        self.per_block.iter().map(Vec::len).sum()
    }

    /// Whether the function performs no volatile access at all.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// Width in bits of a LIR type, for the SOURCE side of the obligation.
///
/// Returns `None` for a type this lane does not model, which fails closed
/// rather than guessing a width — a width guessed here would compare against
/// the machine side and could make a genuine widening look correct.
#[must_use]
fn lir_type_width_bits(ty: &trust_cg_lower::Type) -> Option<(u32, AccessClass)> {
    use trust_cg_lower::Type as T;
    match ty {
        T::I8 => Some((8, AccessClass::Gpr)),
        T::I16 => Some((16, AccessClass::Gpr)),
        T::I32 => Some((32, AccessClass::Gpr)),
        T::I64 => Some((64, AccessClass::Gpr)),
        T::F32 => Some((32, AccessClass::Fp)),
        T::F64 => Some((64, AccessClass::Fp)),
        _ => None,
    }
}

/// Read the SOURCE trace off the LIR function ISel consumes.
///
/// This is the INDEPENDENT side of the lowering half of the obligation: the
/// LIR carries `Opcode::VolatileLoad`/`VolatileStore` with a trust-ir-derived
/// TYPE, placed there by the adapter, while the machine side carries a
/// `Volatile*` OPCODE chosen by instruction selection. Comparing them checks
/// that ISel emitted exactly the accesses the program asked for — the half the
/// optimizer bracket cannot see, because it starts AFTER selection.
///
/// An access whose LIR type this lane does not model is reported through
/// `unmodelled`, and a caller that cannot account for it must fail closed
/// rather than compare a partial trace.
#[must_use]
pub fn lir_volatile_trace(func: &trust_cg_lower::function::Function) -> (VolatileTrace, usize) {
    use trust_cg_lower::instructions::Opcode;

    let mut per_block = Vec::new();
    let mut unmodelled = 0usize;
    let order: Vec<_> = if func.block_order.is_empty() {
        let mut ids: Vec<_> = func.blocks.keys().copied().collect();
        ids.sort_by_key(|b| b.0);
        ids
    } else {
        func.block_order.clone()
    };
    for block_id in order {
        let Some(block) = func.blocks.get(&block_id) else {
            continue;
        };
        let mut seq = Vec::new();
        for inst in &block.instructions {
            let (ty, is_store) = match &inst.opcode {
                Opcode::VolatileLoad { ty, .. } => (ty, false),
                Opcode::VolatileStore { ty, .. } => (ty, true),
                _ => continue,
            };
            match lir_type_width_bits(ty) {
                Some((width_bits, class)) => seq.push(VolatileAccess {
                    width_bits,
                    is_store,
                    class,
                }),
                None => unmodelled += 1,
            }
        }
        per_block.push(seq);
    }
    (VolatileTrace { per_block }, unmodelled)
}

/// Read the MACHINE trace off an emitted x86 function.
#[must_use]
pub fn machine_volatile_trace(func: &X86ISelFunction) -> VolatileTrace {
    let mut per_block = Vec::new();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        let seq: Vec<VolatileAccess> = block
            .insts
            .iter()
            .filter_map(|inst| volatile_access_of_opcode(inst.opcode))
            .collect();
        per_block.push(seq);
    }
    VolatileTrace { per_block }
}

/// Why a volatile trace was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VolatileTraceViolation {
    /// The machine performs FEWER of some access than the source asked for.
    /// Elision, or the elision half of a merge.
    Elided {
        access: VolatileAccess,
        source: usize,
        machine: usize,
    },
    /// The machine performs MORE of some access than the source asked for.
    /// Duplication, as an unrolling or rematerialising pass would produce.
    Duplicated {
        access: VolatileAccess,
        source: usize,
        machine: usize,
    },
    /// The machine emits an access the source never asked for at all — a width
    /// or direction or register file that appears nowhere in the source. This
    /// is what WIDENING and NARROWING look like from the multiset.
    Unasked {
        access: VolatileAccess,
        count: usize,
    },
    /// Two accesses within one block are in a different order than the source
    /// put them.
    Reordered {
        block: usize,
        position: usize,
        source: VolatileAccess,
        machine: VolatileAccess,
    },
    /// A block's access COUNT differs, which is elision or duplication localised
    /// to one block even when the function-wide multiset happens to balance.
    BlockCountMismatch {
        block: usize,
        source: usize,
        machine: usize,
    },
    /// The source and machine have different numbers of blocks, so a per-block
    /// comparison is not meaningful and the check fails closed rather than
    /// guessing a correspondence.
    BlockStructureChanged { source: usize, machine: usize },
}

impl std::fmt::Display for VolatileTraceViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VolatileTraceViolation::Elided {
                access,
                source,
                machine,
            } => write!(
                f,
                "VOLATILE ELIDED: the source performs {source} x `{access}` but the machine \
                 performs only {machine}"
            ),
            VolatileTraceViolation::Duplicated {
                access,
                source,
                machine,
            } => write!(
                f,
                "VOLATILE DUPLICATED: the source performs {source} x `{access}` but the machine \
                 performs {machine}"
            ),
            VolatileTraceViolation::Unasked { access, count } => write!(
                f,
                "VOLATILE UNASKED: the machine performs {count} x `{access}`, which the source \
                 never asks for — a widened, narrowed or redirected access"
            ),
            VolatileTraceViolation::Reordered {
                block,
                position,
                source,
                machine,
            } => write!(
                f,
                "VOLATILE REORDERED: block {block} position {position} is `{machine}` but the \
                 source has `{source}` there"
            ),
            VolatileTraceViolation::BlockCountMismatch {
                block,
                source,
                machine,
            } => write!(
                f,
                "VOLATILE COUNT CHANGED in block {block}: source {source}, machine {machine}"
            ),
            VolatileTraceViolation::BlockStructureChanged { source, machine } => write!(
                f,
                "block structure changed ({source} -> {machine} blocks), so the volatile trace \
                 cannot be compared per block and fails closed"
            ),
        }
    }
}

/// What a discharged trace establishes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VolatileTraceHolds {
    /// Volatile accesses compared.
    pub accesses: usize,
    /// Distinct (width, direction, class) shapes seen.
    pub shapes: usize,
    /// Blocks whose sequence was compared position by position.
    pub blocks_ordered: usize,
}

/// THE OBLIGATION. Every volatile access the source asks for is emitted exactly
/// once, at the same width, in the same direction, through the same register
/// file, and in the same order within each block.
///
/// `compare_order` selects whether the per-block sequences are compared. It is
/// only meaningful when the two traces describe the SAME block structure — an
/// ISel-output-vs-optimized-output comparison does, a source-vs-machine one may
/// not, and passing `false` there is honest rather than a weakening: the
/// multiset still catches every hazard except reordering.
pub fn volatile_trace_holds(
    source: &VolatileTrace,
    machine: &VolatileTrace,
    compare_order: bool,
) -> Result<VolatileTraceHolds, VolatileTraceViolation> {
    let source_set = source.multiset();
    let machine_set = machine.multiset();

    // (1) Nothing elided, nothing duplicated, nothing widened or narrowed.
    for (access, &source_count) in &source_set {
        let machine_count = machine_set.get(access).copied().unwrap_or(0);
        if machine_count < source_count {
            return Err(VolatileTraceViolation::Elided {
                access: *access,
                source: source_count,
                machine: machine_count,
            });
        }
        if machine_count > source_count {
            return Err(VolatileTraceViolation::Duplicated {
                access: *access,
                source: source_count,
                machine: machine_count,
            });
        }
    }
    // (2) And nothing the source never asked for. A widened store shows up here
    //     as an access of a width the source has none of, while its original
    //     width shows up above as elided — the hazard is caught twice, which is
    //     what makes a width change impossible to miss.
    for (access, &machine_count) in &machine_set {
        if !source_set.contains_key(access) {
            return Err(VolatileTraceViolation::Unasked {
                access: *access,
                count: machine_count,
            });
        }
    }

    // (3) Order, within each block.
    let mut blocks_ordered = 0usize;
    if compare_order {
        if source.per_block.len() != machine.per_block.len() {
            return Err(VolatileTraceViolation::BlockStructureChanged {
                source: source.per_block.len(),
                machine: machine.per_block.len(),
            });
        }
        for (index, (src_block, mach_block)) in source
            .per_block
            .iter()
            .zip(machine.per_block.iter())
            .enumerate()
        {
            if src_block.len() != mach_block.len() {
                return Err(VolatileTraceViolation::BlockCountMismatch {
                    block: index,
                    source: src_block.len(),
                    machine: mach_block.len(),
                });
            }
            for (position, (s, m)) in src_block.iter().zip(mach_block.iter()).enumerate() {
                if s != m {
                    return Err(VolatileTraceViolation::Reordered {
                        block: index,
                        position,
                        source: *s,
                        machine: *m,
                    });
                }
            }
            if !src_block.is_empty() {
                blocks_ordered += 1;
            }
        }
    }

    Ok(VolatileTraceHolds {
        accesses: source.len(),
        shapes: source_set.len(),
        blocks_ordered,
    })
}

// ===========================================================================
// The credit hook
// ===========================================================================

/// What a discharged volatile-trace credit establishes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VolatileTraceCredit {
    /// Volatile opcodes the trace recognises.
    pub opcodes: usize,
    /// Hazard controls refuted inside this hook.
    pub hazards_refuted: usize,
    /// Controls that must NOT refute, and did not.
    pub benign_accepted: usize,
}

/// THE CREDIT HOOK for the volatile observation/ordering boundary.
///
/// Returns `Ok` only when the obligation still has teeth. As with the
/// addressing lane, the controls run INSIDE the hook: a battery that lives
/// outside the credit path cannot withhold a credit when it stops refuting,
/// and that is the exact failure mode this tree has hit repeatedly.
///
/// This hook does NOT credit a row by itself, and the coverage gate must not
/// treat it as if it did. The sixteen volatile rows are deferred for a reason
/// that demands a JOINT obligation — "the complete load/store value or memory
/// effect AND preservation of the observable volatile access/optimizer-ordering
/// boundary" — so `coverage_gate::x86_volatile_joint_audit_row` credits a row
/// only when this hook, the byte-level address credit AND the row's value
/// reconstruction all discharge, and makes it RED otherwise. The address and
/// value legs without this one are exactly the "byte-identical plain MOV proof"
/// the deferral reason calls insufficient.
pub fn volatile_trace_credit() -> Result<VolatileTraceCredit, String> {
    // (1) The opcode table reads back the access each name states. A
    //     copy-paste error here would make a widened access compare as
    //     correct.
    let expected: &[(X86Opcode, u32, bool, AccessClass)] = &[
        (X86Opcode::VolatileMovRM8, 8, false, AccessClass::Gpr),
        (X86Opcode::VolatileMovRM16, 16, false, AccessClass::Gpr),
        (X86Opcode::VolatileMovRM32, 32, false, AccessClass::Gpr),
        (X86Opcode::VolatileMovRM, 64, false, AccessClass::Gpr),
        (X86Opcode::VolatileMovMR8, 8, true, AccessClass::Gpr),
        (X86Opcode::VolatileMovMR16, 16, true, AccessClass::Gpr),
        (X86Opcode::VolatileMovMR32, 32, true, AccessClass::Gpr),
        (X86Opcode::VolatileMovMR, 64, true, AccessClass::Gpr),
        (X86Opcode::VolatileMovssRM, 32, false, AccessClass::Fp),
        (X86Opcode::VolatileMovsdRM, 64, false, AccessClass::Fp),
        (X86Opcode::VolatileMovssMR, 32, true, AccessClass::Fp),
        (X86Opcode::VolatileMovsdMR, 64, true, AccessClass::Fp),
        (X86Opcode::VolatileMovdquRM, 128, false, AccessClass::V128),
        (X86Opcode::VolatileMovdqaRM, 128, false, AccessClass::V128),
        (X86Opcode::VolatileMovdquMR, 128, true, AccessClass::V128),
        (X86Opcode::VolatileMovdqaMR, 128, true, AccessClass::V128),
        (X86Opcode::VolatileMovzxRM8, 8, false, AccessClass::Gpr),
        (X86Opcode::VolatileMovzxRM16, 16, false, AccessClass::Gpr),
    ];
    if expected.len() != RECOGNISED_VOLATILE_OPCODES.len() {
        return Err(format!(
            "VOL: the recognised set has {} opcodes but the credit checks {}",
            RECOGNISED_VOLATILE_OPCODES.len(),
            expected.len()
        ));
    }
    for &(opcode, width_bits, is_store, class) in expected {
        let want = VolatileAccess {
            width_bits,
            is_store,
            class,
        };
        match volatile_access_of_opcode(opcode) {
            Some(got) if got == want => {}
            other => {
                return Err(format!(
                    "VOL: {opcode:?} reads back {other:?}, not the access its name states ({want})"
                ));
            }
        }
    }

    // (2) A PLAIN opcode must not enter the trace. If it did, the counts would
    //     not describe volatile accesses at all.
    for plain in [
        X86Opcode::MovRM,
        X86Opcode::MovzxRM8,
        X86Opcode::MovMR8,
        X86Opcode::MovsdRM,
        X86Opcode::MovdquMR,
        X86Opcode::Lea,
    ] {
        if volatile_access_of_opcode(plain).is_some() {
            return Err(format!(
                "VOL: the plain opcode {plain:?} enters the volatile trace"
            ));
        }
    }

    // (3) EVERY hazard refutes. These are the six ways a compiler breaks a
    //     volatile access, plus a register-file change.
    let base = VolatileTrace {
        per_block: vec![
            vec![
                VolatileAccess {
                    width_bits: 8,
                    is_store: false,
                    class: AccessClass::Gpr,
                },
                VolatileAccess {
                    width_bits: 32,
                    is_store: true,
                    class: AccessClass::Gpr,
                },
            ],
            vec![VolatileAccess {
                width_bits: 64,
                is_store: false,
                class: AccessClass::Fp,
            }],
        ],
    };
    let mut hazards_refuted = 0usize;
    let mut hazard = |label: &str, mutated: VolatileTrace| -> Result<(), String> {
        if volatile_trace_holds(&base, &mutated, true).is_ok() {
            return Err(format!(
                "VOL: the `{label}` hazard SURVIVED — a trace comparison that cannot refute it \
                 is not evidence"
            ));
        }
        hazards_refuted += 1;
        Ok(())
    };

    let mut elided = base.clone();
    elided.per_block[0].remove(1);
    hazard("elide", elided)?;

    let mut duplicated = base.clone();
    duplicated.per_block[1].push(base.per_block[1][0]);
    hazard("duplicate", duplicated)?;

    let mut widened = base.clone();
    widened.per_block[0][0].width_bits = 32;
    hazard("widen", widened)?;

    let mut narrowed = base.clone();
    narrowed.per_block[0][1].width_bits = 8;
    hazard("narrow", narrowed)?;

    let mut redirected = base.clone();
    redirected.per_block[0][1].is_store = false;
    hazard("redirect", redirected)?;

    let mut reclassed = base.clone();
    reclassed.per_block[1][0].class = AccessClass::Gpr;
    hazard("reclass", reclassed)?;

    let mut reordered = base.clone();
    reordered.per_block[0].swap(0, 1);
    if reordered.multiset() != base.multiset() {
        return Err(
            "VOL: the reorder control changed the multiset, so it tests the wrong thing"
                .to_string(),
        );
    }
    hazard("reorder", reordered)?;

    // (4) AND a benign transformation must NOT refute. A check that refuses
    //     everything is worth no more than one that refuses nothing: block
    //     LAYOUT may permute freely without changing execution order.
    let permuted = VolatileTrace {
        per_block: vec![base.per_block[1].clone(), base.per_block[0].clone()],
    };
    if volatile_trace_holds(&base, &permuted, false).is_err() {
        return Err(
            "VOL: a pure block-layout permutation was reported as a violation; the obligation \
             is over-strict and would refuse correct code"
                .to_string(),
        );
    }

    Ok(VolatileTraceCredit {
        opcodes: RECOGNISED_VOLATILE_OPCODES.len(),
        hazards_refuted,
        benign_accepted: 1,
    })
}
