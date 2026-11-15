// trust-cg-verify/aarch64_memory_order.rs - C11/Rust -> AArch64 memory-order
// mapping obligations, checked on emitted instruction words
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Memory-order obligations for the AArch64 atomic and fence lowerings
//! (ledger L03-P3).
//!
//! The atomic SMT obligations in [`crate::atomic_proofs`] check VALUES (the
//! loaded value, the old value an RMW returns, the memory an RMW leaves). They
//! say nothing about ORDERING. This module states, for every atomic form the
//! backend emits, which C11/Rust orderings it implements, and checks that
//! against the C11/Rust -> AArch64 mapping by decoding the emitted words.
//!
//! # The mapping (what each C11/Rust ordering requires of the words)
//!
//! A C11/Rust atomic operation lowers to one *core access* (a load, a store, a
//! single-instruction read-modify-write, or a load-exclusive/store-exclusive
//! loop) with optional `DMB` barriers before (leading) or after (trailing) it.
//! The ARMv8 ordering rules (ARM DDI 0487, B2.3, "Barrier-ordered-before")
//! give each piece a fixed contribution:
//!
//! * A load-acquire (`LDAR*`, `LDAXR*`, `LDAXP`, the `A` forms of `LD<op>`,
//!   `SWP` and `CAS`) orders its read before every later access. It is RCsc:
//!   it is also ordered after every earlier store-release. `LDAPR*` is RCpc:
//!   acquire without that second property.
//! * A store-release (`STLR*`, `STLXR*`, `STLXP`, the `L` forms) orders every
//!   earlier access before its write.
//! * `DMB <dom><type>` orders, for the access pairs its type names
//!   (`LD`: R->R and R->W; `ST`: W->W; full: all four, W->R included), every
//!   earlier access before every later one, provided its domain reaches the
//!   other threads (inner shareable, outer shareable or full system; never
//!   non-shareable).
//! * An `LD<op>`/`SWP` whose destination is `XZR`/`WZR` does NOT load with
//!   acquire semantics even with `A` set (DDI 0487, the `LDADD` and `SWP`
//!   descriptions). The same conservative rule is applied to `CAS`.
//!
//! The C11/Rust requirements, per operation:
//!
//! | operation      | acquire (read)            | release (write)       | SeqCst                |
//! |----------------|---------------------------|-----------------------|-----------------------|
//! | load           | Acquire, SeqCst           | -                     | SeqCst: entry         |
//! | store          | -                         | Release, SeqCst       | SeqCst: exit          |
//! | RMW            | Acquire, AcqRel, SeqCst   | Release, AcqRel, SeqCst | SeqCst: entry + exit |
//! | cmpxchg(S, F)  | S in {Acq,AcqRel,SC} or F in {Acq,SC} | S in {Rel,AcqRel,SC} | entry if S or F is SC, exit if S is SC |
//! | fence          | Acquire: R->R, R->W; Release: R->W, W->W; AcqRel: R->R, R->W, W->W; SeqCst: all four | | |
//!
//! "Acquire" is met by a load-acquire (either kind) or by a trailing barrier
//! covering R->R and R->W. "Release" is met by a store-release or by a leading
//! barrier covering R->W and W->W.
//!
//! SeqCst additionally needs every SeqCst write to be ordered before every
//! later SeqCst read of the same thread (the store-buffering shape). The two
//! ways AArch64 provides that are an RCsc pair (a store-release, then a
//! load-acquire RCsc) and a full barrier between them. So a SeqCst READ needs
//! an *entry* that is either an RCsc load-acquire or a leading full barrier,
//! and a SeqCst WRITE needs an *exit* that is either a store-release or a
//! trailing full barrier. [`seq_cst_pair_ordered`] is the pairwise rule, and
//! every (exit, entry) pair this module admits satisfies it, so per-operation
//! admission is enough for any mix of SeqCst operations (pinned exhaustively
//! by `every_admitted_seq_cst_exit_entry_pair_is_ordered`). A plain `LDP`
//! followed by `DMB ISH` (LLVM's FEAT_LSE2 SeqCst 128-bit load) has NO entry:
//! it is ordered after an earlier SeqCst store only when that store ends in a
//! trailing full barrier, which `STLR` and the 128-bit `STLXP` loop do not.
//! It is refused as [`MemoryOrderRefusal::MissingSeqCstEntry`].
//!
//! Relaxed operations need only single-copy atomicity at the access width:
//! every single-register access here is naturally aligned and single-copy
//! atomic; a plain 128-bit `LDP`/`STP` is single-copy atomic only under
//! FEAT_LSE2 (and natural alignment, a precondition the words cannot show).
//!
//! # Evidence strength
//!
//! MAPPING CONFORMANCE, decided from the words. `check_lowering` decodes the
//! words a compile emitted for one operation with this module's own decoder
//! (not the encoder's tables), classifies the form, and refuses by name any
//! form that is unmapped or weaker than the requirement above.
//! `trust-cg-codegen/tests/aarch64_memory_order_obligations.rs` drives it over
//! every (operation, width, ordering[, failure ordering]) the AArch64 selector
//! admits, on the Darwin AOT profile (LSE, LSE2) and the baseline LL/SC
//! profile, at O0-O3: exhaustive over that finite request space.
//!
//! It is NOT a memory-model proof. The ordering contribution of each
//! instruction above is the ARM architecture specification, delegated exactly
//! as the existing `LDAR`/`DMB` obligations delegate it; that this per-operation
//! mapping implements the C11/Rust model for whole programs is the published
//! compilation-correctness result for this mapping (for example the IMM
//! mapping of Podkopaev, Lahav and Vafeiadis, POPL 2019), which this
//! repository does not re-check. No Clean certificate covers any part of it.
//! The native litmus harness
//! (`trust-cg-codegen/tests/e2e_aarch64_memory_order_litmus.rs`) is testing
//! evidence over finite runs on one host.

use std::fmt;

use trust_cg_lower::instructions::AtomicOrdering;

/// Greppable tag on every refusal this module issues.
pub const MEMORY_ORDER_TAG: &str = "[TCG-MEMORY-ORDER]";

// ---------------------------------------------------------------------------
// Requests
// ---------------------------------------------------------------------------

/// The C11/Rust atomic operation kind a lowering implements.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum AtomicKind {
    /// `atomic load`.
    Load,
    /// `atomic store`.
    Store,
    /// Atomic read-modify-write (`fetch_*`, `swap`).
    Rmw,
    /// Compare-exchange (strong or weak).
    CmpXchg,
    /// `fence` (and `compiler_fence`, which trust-ir lowers to the same
    /// instruction).
    Fence,
}

/// One requested atomic operation: kind, access width and ordering(s).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AtomicRequest {
    /// The operation kind.
    pub kind: AtomicKind,
    /// The ordering (the SUCCESS ordering of a compare-exchange).
    pub ordering: AtomicOrdering,
    /// The FAILURE ordering of a compare-exchange; `None` for every other kind.
    pub failure: Option<AtomicOrdering>,
    /// Memory access width in bytes (1, 2, 4, 8 or 16); 0 for a fence.
    pub bytes: u32,
}

impl AtomicRequest {
    /// An atomic load of `bytes`.
    #[must_use]
    pub const fn load(bytes: u32, ordering: AtomicOrdering) -> Self {
        Self {
            kind: AtomicKind::Load,
            ordering,
            failure: None,
            bytes,
        }
    }

    /// An atomic store of `bytes`.
    #[must_use]
    pub const fn store(bytes: u32, ordering: AtomicOrdering) -> Self {
        Self {
            kind: AtomicKind::Store,
            ordering,
            failure: None,
            bytes,
        }
    }

    /// An atomic read-modify-write of `bytes`.
    #[must_use]
    pub const fn rmw(bytes: u32, ordering: AtomicOrdering) -> Self {
        Self {
            kind: AtomicKind::Rmw,
            ordering,
            failure: None,
            bytes,
        }
    }

    /// A compare-exchange of `bytes` with success and failure orderings.
    #[must_use]
    pub const fn cmpxchg(bytes: u32, success: AtomicOrdering, failure: AtomicOrdering) -> Self {
        Self {
            kind: AtomicKind::CmpXchg,
            ordering: success,
            failure: Some(failure),
            bytes,
        }
    }

    /// A fence.
    #[must_use]
    pub const fn fence(ordering: AtomicOrdering) -> Self {
        Self {
            kind: AtomicKind::Fence,
            ordering,
            failure: None,
            bytes: 0,
        }
    }
}

impl fmt::Display for AtomicRequest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let kind = match self.kind {
            AtomicKind::Load => "load",
            AtomicKind::Store => "store",
            AtomicKind::Rmw => "rmw",
            AtomicKind::CmpXchg => "cmpxchg",
            AtomicKind::Fence => "fence",
        };
        write!(f, "{kind}.{:?}", self.ordering)?;
        if let Some(failure) = self.failure {
            write!(f, "/{failure:?}")?;
        }
        if self.kind != AtomicKind::Fence {
            write!(f, " i{}", self.bytes * 8)?;
        }
        Ok(())
    }
}

/// Target features the mapping depends on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct OrderingTarget {
    /// FEAT_LSE2: an aligned 128-bit `LDP`/`STP` is single-copy atomic.
    pub lse2: bool,
}

// ---------------------------------------------------------------------------
// Independent word decoder
// ---------------------------------------------------------------------------

/// Which accesses of the same thread a barrier orders, as (earlier, later)
/// pairs: R = read, W = write.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct AccessOrders {
    /// Earlier reads before later reads.
    pub rr: bool,
    /// Earlier reads before later writes.
    pub rw: bool,
    /// Earlier writes before later reads.
    pub wr: bool,
    /// Earlier writes before later writes.
    pub ww: bool,
}

impl AccessOrders {
    /// Orders nothing.
    pub const NONE: Self = Self {
        rr: false,
        rw: false,
        wr: false,
        ww: false,
    };
    /// A full barrier (`DMB ISH`, `DMB SY`, ...).
    pub const FULL: Self = Self {
        rr: true,
        rw: true,
        wr: true,
        ww: true,
    };
    /// A load barrier (`DMB ISHLD`, `DMB LD`, ...): R->R and R->W.
    pub const LOAD: Self = Self {
        rr: true,
        rw: true,
        wr: false,
        ww: false,
    };
    /// A store barrier (`DMB ISHST`, `DMB ST`, ...): W->W only.
    pub const STORE: Self = Self {
        rr: false,
        rw: false,
        wr: false,
        ww: true,
    };
    /// What an Acquire fence must order.
    pub const ACQUIRE_FENCE: Self = Self::LOAD;
    /// What a Release fence must order: every earlier access before every
    /// later write.
    pub const RELEASE_FENCE: Self = Self {
        rr: false,
        rw: true,
        wr: false,
        ww: true,
    };
    /// What an AcqRel fence must order.
    pub const ACQ_REL_FENCE: Self = Self {
        rr: true,
        rw: true,
        wr: false,
        ww: true,
    };

    /// The pairs either set orders.
    #[must_use]
    pub const fn union(self, other: Self) -> Self {
        Self {
            rr: self.rr || other.rr,
            rw: self.rw || other.rw,
            wr: self.wr || other.wr,
            ww: self.ww || other.ww,
        }
    }

    /// Whether every pair `required` names is ordered here.
    #[must_use]
    pub const fn covers(self, required: Self) -> bool {
        (self.rr || !required.rr)
            && (self.rw || !required.rw)
            && (self.wr || !required.wr)
            && (self.ww || !required.ww)
    }

    /// The pairs `required` names that are not ordered here.
    #[must_use]
    pub fn missing(self, required: Self) -> Vec<&'static str> {
        let mut missing = Vec::new();
        for (have, need, name) in [
            (self.rr, required.rr, "R->R"),
            (self.rw, required.rw, "R->W"),
            (self.wr, required.wr, "W->R"),
            (self.ww, required.ww, "W->W"),
        ] {
            if need && !have {
                missing.push(name);
            }
        }
        missing
    }
}

/// The shareability domain of a barrier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BarrierDomain {
    /// `NSH`: the executing PE only. Orders nothing another thread observes.
    NonShareable,
    /// `ISH`: every PE of the inner shareable domain (every core a user-space
    /// thread can run on).
    InnerShareable,
    /// `OSH`.
    OuterShareable,
    /// `SY` (and the bare `LD`/`ST` forms).
    FullSystem,
}

impl BarrierDomain {
    /// Whether the domain reaches every other thread of the process.
    #[must_use]
    pub const fn reaches_other_threads(self) -> bool {
        !matches!(self, Self::NonShareable)
    }
}

/// A decoded `DMB`/`DSB`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Barrier {
    /// `true` for `DSB`, which orders at least what the same `DMB` does.
    pub dsb: bool,
    /// The 4-bit `CRm` option.
    pub option: u8,
    /// The shareability domain.
    pub domain: BarrierDomain,
    /// The access pairs ordered (within the domain).
    pub orders: AccessOrders,
}

impl Barrier {
    /// The pairs this barrier orders between threads: none when its domain
    /// does not reach the other threads.
    #[must_use]
    pub const fn thread_orders(&self) -> AccessOrders {
        if self.domain.reaches_other_threads() {
            self.orders
        } else {
            AccessOrders::NONE
        }
    }

    /// Assembler spelling (`DMB ISH`, `DMB ISHLD`, ...).
    #[must_use]
    pub fn mnemonic(&self) -> String {
        let option = match self.option {
            0x1 => "OSHLD",
            0x2 => "OSHST",
            0x3 => "OSH",
            0x5 => "NSHLD",
            0x6 => "NSHST",
            0x7 => "NSH",
            0x9 => "ISHLD",
            0xA => "ISHST",
            0xB => "ISH",
            0xD => "LD",
            0xE => "ST",
            0xF => "SY",
            _ => "?",
        };
        format!("{} {option}", if self.dsb { "DSB" } else { "DMB" })
    }
}

/// The acquire kind of a load-acquire.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AcquireKind {
    /// RCsc (`LDAR*`, the `A` exclusives and LSE forms): also ordered after
    /// every earlier store-release.
    Rcsc,
    /// RCpc (`LDAPR*`): acquire only.
    Rcpc,
}

/// The read-modify-write operation of an LSE atomic memory instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LseOp {
    /// `LDADD`.
    Add,
    /// `LDCLR`.
    Clr,
    /// `LDEOR`.
    Eor,
    /// `LDSET`.
    Set,
    /// `LDSMAX`.
    Smax,
    /// `LDSMIN`.
    Smin,
    /// `LDUMAX`.
    Umax,
    /// `LDUMIN`.
    Umin,
    /// `SWP`.
    Swp,
}

impl LseOp {
    const fn stem(self) -> &'static str {
        match self {
            Self::Add => "LDADD",
            Self::Clr => "LDCLR",
            Self::Eor => "LDEOR",
            Self::Set => "LDSET",
            Self::Smax => "LDSMAX",
            Self::Smin => "LDSMIN",
            Self::Umax => "LDUMAX",
            Self::Umin => "LDUMIN",
            Self::Swp => "SWP",
        }
    }
}

/// One instruction word, classified for memory ordering.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderingWord {
    /// `LDAR{B,H,}` (RCsc) or `LDAPR{B,H,}` (RCpc).
    LoadAcquire {
        /// Access width in bytes.
        bytes: u32,
        /// RCsc or RCpc.
        kind: AcquireKind,
        /// The destination is `XZR`/`WZR`.
        rt_zero: bool,
    },
    /// `STLR{B,H,}`.
    StoreRelease {
        /// Access width in bytes.
        bytes: u32,
    },
    /// `LD{A}XR{B,H,}` / `LD{A}XP`.
    LoadExclusive {
        /// Total access width in bytes (both registers of a pair).
        bytes: u32,
        /// The pair form.
        pair: bool,
        /// `LDAXR`/`LDAXP`.
        acquire: bool,
    },
    /// `ST{L}XR{B,H,}` / `ST{L}XP`.
    StoreExclusive {
        /// Total access width in bytes.
        bytes: u32,
        /// The pair form.
        pair: bool,
        /// `STLXR`/`STLXP`.
        release: bool,
    },
    /// `LD<op>{A}{L}{B,H,}` / `SWP{A}{L}{B,H,}`.
    LseRmw {
        /// Access width in bytes.
        bytes: u32,
        /// The operation.
        op: LseOp,
        /// The `A` bit as encoded.
        acquire_bit: bool,
        /// The `R` bit (release).
        release: bool,
        /// The destination is `XZR`/`WZR` (acquire semantics then dropped).
        rt_zero: bool,
    },
    /// `CAS{A}{L}{B,H,}` / `CASP{A}{L}`.
    Cas {
        /// Total access width in bytes.
        bytes: u32,
        /// The pair form.
        pair: bool,
        /// The `L` bit (acquire) as encoded.
        acquire_bit: bool,
        /// The `o0` bit (release).
        release: bool,
        /// The compare/result register is `XZR`/`WZR`.
        rs_zero: bool,
    },
    /// A plain (unordered) load from a non-frame base register.
    PlainLoad {
        /// Total access width in bytes.
        bytes: u32,
        /// `LDP`.
        pair: bool,
    },
    /// A plain (unordered) store to a non-frame base register.
    PlainStore {
        /// Total access width in bytes.
        bytes: u32,
        /// `STP`.
        pair: bool,
    },
    /// `DMB` / `DSB`.
    Barrier(Barrier),
    /// `CLREX`: clears the exclusive monitor; no memory access.
    ClearExclusive,
    /// A plain access through `SP` or `X29`, or a PC-relative literal load:
    /// thread-private frame or constant data.
    Private,
    /// Not a memory access or barrier.
    NonMemory,
    /// A load/store-class word this decoder does not model, on a shared base
    /// register (`LDLAR`/`STLLR`, `LDAPUR`, SIMD structure loads, `LDNP`, ...).
    Unclassified,
}

/// Is `rn` a frame base (`SP` = 31 in a base field, or the frame pointer
/// `X29`)?
const fn is_frame_base(rn: u32) -> bool {
    rn == 31 || rn == 29
}

fn decode_barrier(word: u32, dsb: bool) -> OrderingWord {
    let option = ((word >> 8) & 0xF) as u8;
    let domain = match option >> 2 {
        0 => BarrierDomain::OuterShareable,
        1 => BarrierDomain::NonShareable,
        2 => BarrierDomain::InnerShareable,
        _ => BarrierDomain::FullSystem,
    };
    let orders = match option & 3 {
        1 => AccessOrders::LOAD,
        2 => AccessOrders::STORE,
        3 => AccessOrders::FULL,
        // CRm<1:0> == 00: reserved for DMB, speculation barriers for DSB.
        _ => return OrderingWord::Unclassified,
    };
    OrderingWord::Barrier(Barrier {
        dsb,
        option,
        domain,
        orders,
    })
}

/// Classify one AArch64 instruction word for memory ordering.
///
/// The field layouts are transcribed from ARM DDI 0487 (the
/// "Loads and Stores" encoding index and the `DMB`/`DSB`/`CLREX` system
/// forms); this decoder shares no table with the encoder.
#[must_use]
pub fn decode_ordering_word(word: u32) -> OrderingWord {
    // Barriers and CLREX: 1101 0101 0000 0011 0011 CRm op2 11111.
    match word & 0xFFFF_F0FF {
        0xD503_30BF => return decode_barrier(word, false),
        0xD503_309F => return decode_barrier(word, true),
        0xD503_305F => return OrderingWord::ClearExclusive,
        _ => {}
    }
    // The load/store class: op0 (bits 28:25) = x1x0.
    if (word >> 25) & 0b101 != 0b100 {
        return OrderingWord::NonMemory;
    }
    let size = word >> 30;
    let rn = (word >> 5) & 31;
    let rt = word & 31;

    // Exclusive, ordered and compare-and-swap: bits 29:24 = 001000,
    // `size 001000 o2 L o1 Rs o0 Rt2 Rn Rt`.
    if (word >> 24) & 0x3F == 0b00_1000 {
        let o2 = (word >> 23) & 1;
        let l = (word >> 22) & 1 == 1;
        let o1 = (word >> 21) & 1;
        let o0 = (word >> 15) & 1 == 1;
        let rs = (word >> 16) & 31;
        let rt2 = (word >> 10) & 31;
        return match (o2, o1) {
            // LD{A}XR / ST{L}XR (single register).
            (0, 0) => {
                if rt2 != 31 || (l && rs != 31) {
                    return OrderingWord::Unclassified;
                }
                let bytes = 1 << size;
                if l {
                    OrderingWord::LoadExclusive {
                        bytes,
                        pair: false,
                        acquire: o0,
                    }
                } else {
                    OrderingWord::StoreExclusive {
                        bytes,
                        pair: false,
                        release: o0,
                    }
                }
            }
            // Bit 31 set: LD{A}XP / ST{L}XP (sz = bit 30). Clear: CASP{A}{L}.
            (0, 1) => {
                let bytes = if size & 1 == 1 { 16 } else { 8 };
                if size & 2 != 0 {
                    if l && rs != 31 {
                        return OrderingWord::Unclassified;
                    }
                    if l {
                        OrderingWord::LoadExclusive {
                            bytes,
                            pair: true,
                            acquire: o0,
                        }
                    } else {
                        OrderingWord::StoreExclusive {
                            bytes,
                            pair: true,
                            release: o0,
                        }
                    }
                } else if rt2 != 31 {
                    OrderingWord::Unclassified
                } else {
                    OrderingWord::Cas {
                        bytes,
                        pair: true,
                        acquire_bit: l,
                        release: o0,
                        rs_zero: rs == 31,
                    }
                }
            }
            // LDAR / STLR (o0 = 1); LDLAR / STLLR (o0 = 0, LORegions) are not
            // part of any mapping.
            (1, 0) => {
                if rt2 != 31 || rs != 31 {
                    return OrderingWord::Unclassified;
                }
                let bytes = 1 << size;
                match (l, o0) {
                    (true, true) => OrderingWord::LoadAcquire {
                        bytes,
                        kind: AcquireKind::Rcsc,
                        rt_zero: rt == 31,
                    },
                    (false, true) => OrderingWord::StoreRelease { bytes },
                    _ => OrderingWord::Unclassified,
                }
            }
            // CAS{A}{L}{B,H,}: L = acquire, o0 = release.
            _ => {
                if rt2 != 31 {
                    return OrderingWord::Unclassified;
                }
                OrderingWord::Cas {
                    bytes: 1 << size,
                    pair: false,
                    acquire_bit: l,
                    release: o0,
                    rs_zero: rs == 31,
                }
            }
        };
    }

    // LSE atomic memory operations and LDAPR:
    // `size 111 0 00 A R 1 Rs o3 opc 00 Rn Rt`.
    if word & 0x3F20_0C00 == 0x3820_0000 {
        let a = (word >> 23) & 1 == 1;
        let r = (word >> 22) & 1 == 1;
        let o3 = (word >> 15) & 1;
        let opc = (word >> 12) & 7;
        let rs = (word >> 16) & 31;
        let bytes = 1 << size;
        if o3 == 1 && opc == 0b100 {
            return if a && !r && rs == 31 {
                OrderingWord::LoadAcquire {
                    bytes,
                    kind: AcquireKind::Rcpc,
                    rt_zero: rt == 31,
                }
            } else {
                OrderingWord::Unclassified
            };
        }
        let op = match (o3, opc) {
            (0, 0) => LseOp::Add,
            (0, 1) => LseOp::Clr,
            (0, 2) => LseOp::Eor,
            (0, 3) => LseOp::Set,
            (0, 4) => LseOp::Smax,
            (0, 5) => LseOp::Smin,
            (0, 6) => LseOp::Umax,
            (0, 7) => LseOp::Umin,
            (1, 0) => LseOp::Swp,
            _ => return OrderingWord::Unclassified,
        };
        return OrderingWord::LseRmw {
            bytes,
            op,
            acquire_bit: a,
            release: r,
            rt_zero: rt == 31,
        };
    }

    // Load/store pair: `opc 101 V idx L imm7 Rt2 Rn Rt`.
    if (word >> 27) & 7 == 0b101 {
        if is_frame_base(rn) {
            return OrderingWord::Private;
        }
        let v = (word >> 26) & 1;
        let idx = (word >> 23) & 3;
        let load = (word >> 22) & 1 == 1;
        // The X-register pair in its offset, pre- and post-index forms (the
        // FEAT_LSE2 single-copy-atomic shape). LDNP/STNP, W pairs, LDPSW and
        // SIMD pairs are not part of any mapping.
        if v == 0 && size == 0b10 && idx != 0 {
            return if load {
                OrderingWord::PlainLoad {
                    bytes: 16,
                    pair: true,
                }
            } else {
                OrderingWord::PlainStore {
                    bytes: 16,
                    pair: true,
                }
            };
        }
        return OrderingWord::Unclassified;
    }

    // Single register: `size 111 V 0 op opc ...` (unsigned offset, or the
    // imm9 / register-offset forms).
    if (word >> 27) & 7 == 0b111 {
        let v = (word >> 26) & 1;
        let opc = (word >> 22) & 3;
        let unsigned_offset = (word >> 24) & 3 == 0b01;
        let imm9_or_register =
            (word >> 24) & 3 == 0b00 && ((word >> 21) & 1 == 0 || (word >> 10) & 3 == 0b10);
        if !(unsigned_offset || imm9_or_register) {
            return if is_frame_base(rn) {
                OrderingWord::Private
            } else {
                OrderingWord::Unclassified
            };
        }
        if v == 0 && size == 3 && opc == 0b10 {
            // PRFM / PRFUM: a hint, not an access.
            return OrderingWord::NonMemory;
        }
        if is_frame_base(rn) {
            return OrderingWord::Private;
        }
        let (bytes, load) = if v == 0 {
            (1 << size, opc != 0)
        } else if size == 0 && opc & 2 != 0 {
            (16, opc & 1 == 1)
        } else {
            (1 << size, opc & 1 == 1)
        };
        return if load {
            OrderingWord::PlainLoad { bytes, pair: false }
        } else {
            OrderingWord::PlainStore { bytes, pair: false }
        };
    }

    // PC-relative literal loads: `opc 011 V 00 imm19 Rt` (constant data).
    if (word >> 27) & 7 == 0b011 && (word >> 24) & 3 == 0 {
        return OrderingWord::Private;
    }

    if is_frame_base(rn) {
        OrderingWord::Private
    } else {
        OrderingWord::Unclassified
    }
}

// ---------------------------------------------------------------------------
// Emitted forms
// ---------------------------------------------------------------------------

/// The shape of the core access of an emitted form.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FormShape {
    /// Barriers only (a fence).
    FenceOnly,
    /// One `LDAR`/`LDAPR`.
    OrderedLoad,
    /// One `STLR`.
    OrderedStore,
    /// One plain load (`LDR`/`LDP`).
    PlainLoad,
    /// One plain store (`STR`/`STP`).
    PlainStore,
    /// One LSE `LD<op>`/`SWP`.
    LseRmw,
    /// One LSE `CAS`/`CASP`.
    LseCas,
    /// A load-exclusive / store-exclusive loop.
    ExclusiveLoop,
}

/// How the read of a form is acquire-ordered.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AcquireVia {
    /// It is not.
    None,
    /// An RCsc load-acquire.
    AcquireRcsc,
    /// An RCpc load-acquire (`LDAPR`).
    AcquireRcpc,
    /// A trailing barrier covering R->R and R->W.
    TrailingBarrier,
}

/// How the read of a form is ordered after earlier SeqCst writes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SeqCstEntry {
    /// It is not (only an earlier trailing full barrier could order it).
    None,
    /// An RCsc load-acquire: ordered after every earlier store-release.
    AcquireRcsc,
    /// A leading full barrier: ordered after every earlier access.
    LeadingFullBarrier,
}

/// How the write of a form is release-ordered.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReleaseVia {
    /// It is not.
    None,
    /// A store-release.
    StoreRelease,
    /// A leading barrier covering R->W and W->W.
    LeadingBarrier,
}

/// How the write of a form is ordered before later SeqCst reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SeqCstExit {
    /// It is not (only a later leading full barrier could order it).
    None,
    /// A store-release: ordered before every later RCsc load-acquire.
    StoreRelease,
    /// A trailing full barrier: ordered before every later access.
    TrailingFullBarrier,
}

/// Whether a SeqCst write with `exit` is ordered before a later SeqCst read
/// with `entry` of the same thread (the store-buffering pair).
#[must_use]
pub const fn seq_cst_pair_ordered(exit: SeqCstExit, entry: SeqCstEntry) -> bool {
    matches!(exit, SeqCstExit::TrailingFullBarrier)
        || matches!(entry, SeqCstEntry::LeadingFullBarrier)
        || (matches!(exit, SeqCstExit::StoreRelease) && matches!(entry, SeqCstEntry::AcquireRcsc))
}

/// The ordering of a form's read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReadOrdering {
    /// Acquire ordering of the read.
    pub acquire: AcquireVia,
    /// SeqCst entry of the read.
    pub sc_entry: SeqCstEntry,
}

/// The ordering of a form's write.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WriteOrdering {
    /// Release ordering of the write.
    pub release: ReleaseVia,
    /// SeqCst exit of the write.
    pub sc_exit: SeqCstExit,
}

/// One emitted form, classified from its words.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EmittedForm {
    /// The core access shape.
    pub shape: FormShape,
    /// Access width in bytes (0 for a fence).
    pub bytes: u32,
    /// The read, when the core access reads.
    pub read: Option<ReadOrdering>,
    /// The write, when the core access writes.
    pub write: Option<WriteOrdering>,
    /// The pairs the form's barriers order between threads.
    pub barrier_orders: AccessOrders,
    /// Barriers whose domain does not reach other threads.
    pub local_only_barriers: usize,
    /// The ordering-relevant instructions in program order.
    pub mnemonic: String,
}

fn core_mnemonic(word: &OrderingWord) -> String {
    let suffix = |bytes: u32| match bytes {
        1 => "B",
        2 => "H",
        _ => "",
    };
    match *word {
        OrderingWord::LoadAcquire { bytes, kind, .. } => format!(
            "{}{} ({bytes} B)",
            if kind == AcquireKind::Rcsc {
                "LDAR"
            } else {
                "LDAPR"
            },
            suffix(bytes)
        ),
        OrderingWord::StoreRelease { bytes } => format!("STLR{} ({bytes} B)", suffix(bytes)),
        OrderingWord::LoadExclusive {
            bytes,
            pair,
            acquire,
        } => format!(
            "LD{}X{}{}",
            if acquire { "A" } else { "" },
            if pair { "P" } else { "R" },
            if pair { "" } else { suffix(bytes) }
        ),
        OrderingWord::StoreExclusive {
            bytes,
            pair,
            release,
        } => format!(
            "ST{}X{}{} ({bytes} B)",
            if release { "L" } else { "" },
            if pair { "P" } else { "R" },
            if pair { "" } else { suffix(bytes) }
        ),
        OrderingWord::LseRmw {
            bytes,
            op,
            acquire_bit,
            release,
            rt_zero,
        } => format!(
            "{}{}{}{} ({bytes} B{})",
            op.stem(),
            if acquire_bit { "A" } else { "" },
            if release { "L" } else { "" },
            suffix(bytes),
            if rt_zero { ", Rt=ZR" } else { "" }
        ),
        OrderingWord::Cas {
            bytes,
            pair,
            acquire_bit,
            release,
            ..
        } => format!(
            "CAS{}{}{}{} ({bytes} B)",
            if pair { "P" } else { "" },
            if acquire_bit { "A" } else { "" },
            if release { "L" } else { "" },
            if pair { "" } else { suffix(bytes) }
        ),
        OrderingWord::PlainLoad { bytes, pair } => {
            format!("{} ({bytes} B)", if pair { "LDP" } else { "LDR" })
        }
        OrderingWord::PlainStore { bytes, pair } => {
            format!("{} ({bytes} B)", if pair { "STP" } else { "STR" })
        }
        OrderingWord::Barrier(barrier) => barrier.mnemonic(),
        OrderingWord::ClearExclusive => "CLREX".to_string(),
        OrderingWord::Private | OrderingWord::NonMemory | OrderingWord::Unclassified => {
            String::new()
        }
    }
}

/// Classify the ordering-relevant words of ONE lowered atomic operation.
///
/// `words` is the code of a function whose only shared-memory effect is that
/// operation (frame accesses through `SP`/`X29` and non-memory instructions
/// are ignored). Fails closed on any word it cannot classify and on any
/// combination of core accesses that is not one of the shapes above.
pub fn analyze_form(words: &[u32]) -> Result<EmittedForm, MemoryOrderRefusal> {
    let mut items: Vec<(usize, OrderingWord)> = Vec::new();
    for (index, &word) in words.iter().enumerate() {
        match decode_ordering_word(word) {
            OrderingWord::Private | OrderingWord::NonMemory => {}
            OrderingWord::Unclassified => {
                return Err(MemoryOrderRefusal::UnclassifiedAccess { index, word });
            }
            decoded => items.push((index, decoded)),
        }
    }
    let is_core = |word: &OrderingWord| {
        !matches!(
            word,
            OrderingWord::Barrier(_) | OrderingWord::ClearExclusive
        )
    };
    let core: Vec<(usize, OrderingWord)> = items
        .iter()
        .copied()
        .filter(|(_, word)| is_core(word))
        .collect();
    let mnemonic = items
        .iter()
        .map(|(_, word)| core_mnemonic(word))
        .collect::<Vec<_>>()
        .join("; ");
    let first = core.first().map(|(index, _)| *index);
    let last = core.last().map(|(index, _)| *index);
    let mut leading = AccessOrders::NONE;
    let mut trailing = AccessOrders::NONE;
    let mut all = AccessOrders::NONE;
    let mut local_only_barriers = 0;
    for (index, word) in &items {
        let OrderingWord::Barrier(barrier) = word else {
            continue;
        };
        if !barrier.domain.reaches_other_threads() {
            local_only_barriers += 1;
        }
        let orders = barrier.thread_orders();
        all = all.union(orders);
        let (Some(first), Some(last)) = (first, last) else {
            // A fence: every barrier is the fence.
            continue;
        };
        if *index < first {
            leading = leading.union(orders);
        } else if *index > last {
            trailing = trailing.union(orders);
        } else {
            return Err(MemoryOrderRefusal::Unmapped {
                form: mnemonic,
                reason: "a barrier inside the core access sequence",
            });
        }
    }

    let acquire_of = |read: &OrderingWord| -> AcquireVia {
        let architectural = match *read {
            OrderingWord::LoadAcquire { kind, rt_zero, .. } if !rt_zero => Some(kind),
            OrderingWord::LoadExclusive { acquire: true, .. } => Some(AcquireKind::Rcsc),
            OrderingWord::LseRmw {
                acquire_bit: true,
                rt_zero: false,
                ..
            }
            | OrderingWord::Cas {
                acquire_bit: true,
                rs_zero: false,
                ..
            } => Some(AcquireKind::Rcsc),
            _ => None,
        };
        match architectural {
            Some(AcquireKind::Rcsc) => AcquireVia::AcquireRcsc,
            Some(AcquireKind::Rcpc) => AcquireVia::AcquireRcpc,
            None if trailing.covers(AccessOrders::LOAD) => AcquireVia::TrailingBarrier,
            None => AcquireVia::None,
        }
    };
    let read_of = |read: &OrderingWord| -> ReadOrdering {
        let acquire = acquire_of(read);
        let sc_entry = if acquire == AcquireVia::AcquireRcsc {
            SeqCstEntry::AcquireRcsc
        } else if leading.covers(AccessOrders::FULL) {
            SeqCstEntry::LeadingFullBarrier
        } else {
            SeqCstEntry::None
        };
        ReadOrdering { acquire, sc_entry }
    };
    let write_of = |write: &OrderingWord| -> WriteOrdering {
        let release_bit = matches!(
            *write,
            OrderingWord::StoreRelease { .. }
                | OrderingWord::StoreExclusive { release: true, .. }
                | OrderingWord::LseRmw { release: true, .. }
                | OrderingWord::Cas { release: true, .. }
        );
        let release = if release_bit {
            ReleaseVia::StoreRelease
        } else if leading.covers(AccessOrders::RELEASE_FENCE) {
            ReleaseVia::LeadingBarrier
        } else {
            ReleaseVia::None
        };
        let sc_exit = if release_bit {
            SeqCstExit::StoreRelease
        } else if trailing.covers(AccessOrders::FULL) {
            SeqCstExit::TrailingFullBarrier
        } else {
            SeqCstExit::None
        };
        WriteOrdering { release, sc_exit }
    };

    let (shape, bytes, read, write) = match core.as_slice() {
        [] => (FormShape::FenceOnly, 0, None, None),
        [(_, word)] => match *word {
            OrderingWord::LoadAcquire { bytes, .. } => {
                (FormShape::OrderedLoad, bytes, Some(read_of(word)), None)
            }
            OrderingWord::StoreRelease { bytes } => {
                (FormShape::OrderedStore, bytes, None, Some(write_of(word)))
            }
            OrderingWord::PlainLoad { bytes, .. } => {
                (FormShape::PlainLoad, bytes, Some(read_of(word)), None)
            }
            OrderingWord::PlainStore { bytes, .. } => {
                (FormShape::PlainStore, bytes, None, Some(write_of(word)))
            }
            OrderingWord::LseRmw { bytes, .. } => (
                FormShape::LseRmw,
                bytes,
                Some(read_of(word)),
                Some(write_of(word)),
            ),
            OrderingWord::Cas { bytes, .. } => (
                FormShape::LseCas,
                bytes,
                Some(read_of(word)),
                Some(write_of(word)),
            ),
            _ => {
                return Err(MemoryOrderRefusal::Unmapped {
                    form: mnemonic,
                    reason: "a lone load-exclusive or store-exclusive",
                });
            }
        },
        // One load-exclusive, then the store-exclusive(s) of its alternative
        // paths (the 128-bit compare-exchange stores the old value back on
        // failure): every store-exclusive must match the load's width, and
        // the write is only as ordered as the weakest of them.
        [
            (_, load @ OrderingWord::LoadExclusive { bytes, pair, .. }),
            stores @ ..,
        ] if stores.iter().all(|(_, store)| {
            matches!(
                store,
                OrderingWord::StoreExclusive {
                    bytes: store_bytes,
                    pair: store_pair,
                    ..
                } if store_bytes == bytes && store_pair == pair
            )
        }) =>
        {
            let mut writes = stores.iter().map(|(_, store)| write_of(store));
            let Some(mut write) = writes.next() else {
                return Err(MemoryOrderRefusal::Unmapped {
                    form: mnemonic,
                    reason: "a lone load-exclusive or store-exclusive",
                });
            };
            for other in writes {
                if other.release == ReleaseVia::None {
                    write.release = ReleaseVia::None;
                } else if other.release == ReleaseVia::LeadingBarrier
                    && write.release == ReleaseVia::StoreRelease
                {
                    write.release = ReleaseVia::LeadingBarrier;
                }
                if other.sc_exit == SeqCstExit::None {
                    write.sc_exit = SeqCstExit::None;
                } else if other.sc_exit == SeqCstExit::TrailingFullBarrier
                    && write.sc_exit == SeqCstExit::StoreRelease
                {
                    write.sc_exit = SeqCstExit::TrailingFullBarrier;
                }
            }
            (
                FormShape::ExclusiveLoop,
                *bytes,
                Some(read_of(load)),
                Some(write),
            )
        }
        [_, _, ..] => {
            return Err(MemoryOrderRefusal::Unmapped {
                form: mnemonic,
                reason: "more than one shared access that is not one exclusive loop",
            });
        }
    };
    Ok(EmittedForm {
        shape,
        bytes,
        read,
        write,
        barrier_orders: all,
        local_only_barriers,
        mnemonic,
    })
}

// ---------------------------------------------------------------------------
// Requirements
// ---------------------------------------------------------------------------

/// What a request requires of its emitted form.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OrderingRequirement {
    /// The read must be acquire-ordered.
    pub acquire: bool,
    /// The write must be release-ordered.
    pub release: bool,
    /// The read must have a SeqCst entry.
    pub sc_entry: bool,
    /// The write must have a SeqCst exit.
    pub sc_exit: bool,
    /// The pairs a fence must order.
    pub fence: AccessOrders,
}

const fn acquires(ordering: AtomicOrdering) -> bool {
    matches!(
        ordering,
        AtomicOrdering::Acquire | AtomicOrdering::AcqRel | AtomicOrdering::SeqCst
    )
}

const fn releases(ordering: AtomicOrdering) -> bool {
    matches!(
        ordering,
        AtomicOrdering::Release | AtomicOrdering::AcqRel | AtomicOrdering::SeqCst
    )
}

const fn seq_cst(ordering: AtomicOrdering) -> bool {
    matches!(ordering, AtomicOrdering::SeqCst)
}

/// The C11/Rust requirement for `request`, or the named refusal of an
/// ordering that has no mapping row (a Release load, an Acquire store, a
/// Release/AcqRel compare-exchange failure ordering).
pub fn requirement(request: &AtomicRequest) -> Result<OrderingRequirement, MemoryOrderRefusal> {
    let ordering = request.ordering;
    let invalid = |reason| MemoryOrderRefusal::NoMappingRow {
        request: *request,
        reason,
    };
    let none = OrderingRequirement {
        acquire: false,
        release: false,
        sc_entry: false,
        sc_exit: false,
        fence: AccessOrders::NONE,
    };
    if request.kind != AtomicKind::CmpXchg && request.failure.is_some() {
        return Err(invalid(
            "only a compare-exchange carries a failure ordering",
        ));
    }
    if request.kind == AtomicKind::Fence {
        if request.bytes != 0 {
            return Err(invalid("a fence has no access width"));
        }
    } else if !matches!(request.bytes, 1 | 2 | 4 | 8 | 16) {
        return Err(invalid("access width must be 1, 2, 4, 8 or 16 bytes"));
    }
    Ok(match request.kind {
        AtomicKind::Load => {
            if !ordering.is_legal_for_load() {
                return Err(invalid("a load cannot release (Release/AcqRel)"));
            }
            OrderingRequirement {
                acquire: acquires(ordering),
                sc_entry: seq_cst(ordering),
                ..none
            }
        }
        AtomicKind::Store => {
            if !ordering.is_legal_for_store() {
                return Err(invalid("a store cannot acquire (Acquire/AcqRel)"));
            }
            OrderingRequirement {
                release: releases(ordering),
                sc_exit: seq_cst(ordering),
                ..none
            }
        }
        AtomicKind::Rmw => OrderingRequirement {
            acquire: acquires(ordering),
            release: releases(ordering),
            sc_entry: seq_cst(ordering),
            sc_exit: seq_cst(ordering),
            ..none
        },
        AtomicKind::CmpXchg => {
            let Some(failure) = request.failure else {
                return Err(invalid("a compare-exchange needs a failure ordering"));
            };
            if !failure.is_valid_cmpxchg_failure() {
                return Err(invalid(
                    "a compare-exchange failure ordering cannot release (Release/AcqRel)",
                ));
            }
            OrderingRequirement {
                acquire: acquires(ordering) || acquires(failure),
                release: releases(ordering),
                sc_entry: seq_cst(ordering) || seq_cst(failure),
                sc_exit: seq_cst(ordering),
                ..none
            }
        }
        AtomicKind::Fence => OrderingRequirement {
            fence: match ordering {
                AtomicOrdering::Relaxed => AccessOrders::NONE,
                AtomicOrdering::Acquire => AccessOrders::ACQUIRE_FENCE,
                AtomicOrdering::Release => AccessOrders::RELEASE_FENCE,
                AtomicOrdering::AcqRel => AccessOrders::ACQ_REL_FENCE,
                AtomicOrdering::SeqCst => AccessOrders::FULL,
            },
            ..none
        },
    })
}

// ---------------------------------------------------------------------------
// Refusals
// ---------------------------------------------------------------------------

/// A named refusal: the form is unmapped, or weaker than the mapping requires.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MemoryOrderRefusal {
    /// The requested ordering has no C11/Rust -> AArch64 mapping row.
    NoMappingRow {
        /// The request.
        request: AtomicRequest,
        /// Why.
        reason: &'static str,
    },
    /// A load/store-class word this decoder does not model, on a shared base.
    UnclassifiedAccess {
        /// Word index in the function.
        index: usize,
        /// The word.
        word: u32,
    },
    /// The emitted words are not one of the mapped shapes.
    Unmapped {
        /// The ordering-relevant instructions.
        form: String,
        /// Why.
        reason: &'static str,
    },
    /// The form's shape does not implement the request's kind.
    WrongShape {
        /// The request.
        request: AtomicRequest,
        /// The form.
        form: String,
    },
    /// The access width differs from the request's.
    WidthMismatch {
        /// The request.
        request: AtomicRequest,
        /// The form.
        form: String,
        /// The emitted width in bytes.
        emitted_bytes: u32,
    },
    /// A plain 128-bit pair access without FEAT_LSE2 is not single-copy atomic.
    NotSingleCopyAtomic {
        /// The request.
        request: AtomicRequest,
        /// The form.
        form: String,
    },
    /// The read is not acquire-ordered.
    MissingAcquire {
        /// The request.
        request: AtomicRequest,
        /// The form.
        form: String,
    },
    /// The write is not release-ordered.
    MissingRelease {
        /// The request.
        request: AtomicRequest,
        /// The form.
        form: String,
    },
    /// A SeqCst read is neither an RCsc load-acquire nor behind a full
    /// barrier, so an earlier SeqCst store-release is not ordered before it.
    MissingSeqCstEntry {
        /// The request.
        request: AtomicRequest,
        /// The form.
        form: String,
    },
    /// A SeqCst write is neither a store-release nor followed by a full
    /// barrier.
    MissingSeqCstExit {
        /// The request.
        request: AtomicRequest,
        /// The form.
        form: String,
    },
    /// A fence's barriers do not order every pair the fence orders.
    WeakerFence {
        /// The request.
        request: AtomicRequest,
        /// The form.
        form: String,
        /// The unordered pairs.
        missing: Vec<&'static str>,
        /// Barriers present whose domain does not reach other threads.
        local_only_barriers: usize,
    },
    /// `lift_for_cmpxchg_failure` returned an ordering weaker than both the
    /// success and the failure ordering need.
    WeakerCmpXchgLift {
        /// Success ordering.
        success: AtomicOrdering,
        /// Failure ordering.
        failure: AtomicOrdering,
        /// The lifted ordering.
        lifted: AtomicOrdering,
    },
}

impl fmt::Display for MemoryOrderRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{MEMORY_ORDER_TAG} ")?;
        match self {
            Self::NoMappingRow { request, reason } => {
                write!(f, "NoMappingRow: {request}: {reason}")
            }
            Self::UnclassifiedAccess { index, word } => write!(
                f,
                "UnclassifiedAccess: word {index} ({word:#010x}) is a load/store this \
                 decoder does not model"
            ),
            Self::Unmapped { form, reason } => write!(f, "Unmapped: `{form}`: {reason}"),
            Self::WrongShape { request, form } => {
                write!(f, "WrongShape: {request} is not implemented by `{form}`")
            }
            Self::WidthMismatch {
                request,
                form,
                emitted_bytes,
            } => write!(
                f,
                "WidthMismatch: {request} emitted a {emitted_bytes}-byte access `{form}`"
            ),
            Self::NotSingleCopyAtomic { request, form } => write!(
                f,
                "NotSingleCopyAtomic: {request}: `{form}` is a plain 128-bit pair access \
                 without FEAT_LSE2"
            ),
            Self::MissingAcquire { request, form } => write!(
                f,
                "MissingAcquire: {request}: the read of `{form}` is neither a load-acquire \
                 nor followed by a barrier ordering R->R and R->W"
            ),
            Self::MissingRelease { request, form } => write!(
                f,
                "MissingRelease: {request}: the write of `{form}` is neither a store-release \
                 nor preceded by a barrier ordering R->W and W->W"
            ),
            Self::MissingSeqCstEntry { request, form } => write!(
                f,
                "MissingSeqCstEntry: {request}: the read of `{form}` is neither an RCsc \
                 load-acquire nor preceded by a full barrier, so an earlier SeqCst \
                 store-release is not ordered before it"
            ),
            Self::MissingSeqCstExit { request, form } => write!(
                f,
                "MissingSeqCstExit: {request}: the write of `{form}` is neither a \
                 store-release nor followed by a full barrier"
            ),
            Self::WeakerFence {
                request,
                form,
                missing,
                local_only_barriers,
            } => write!(
                f,
                "WeakerFence: {request}: `{form}` does not order {}{}",
                missing.join(", "),
                if *local_only_barriers > 0 {
                    " (a non-shareable barrier orders nothing between threads)"
                } else {
                    ""
                }
            ),
            Self::WeakerCmpXchgLift {
                success,
                failure,
                lifted,
            } => write!(
                f,
                "WeakerCmpXchgLift: ({success:?}, {failure:?}) lifted to {lifted:?}, which \
                 does not cover both orderings"
            ),
        }
    }
}

impl std::error::Error for MemoryOrderRefusal {}

// ---------------------------------------------------------------------------
// The check
// ---------------------------------------------------------------------------

/// One admitted row: a request, the form its words implement, and what the
/// form provides beyond the requirement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConformanceRow {
    /// The request.
    pub request: AtomicRequest,
    /// The emitted form.
    pub form: EmittedForm,
    /// The requirement it meets.
    pub required: OrderingRequirement,
    /// Orderings the form provides that the request does not need (the form
    /// is stronger than required there; never weaker anywhere).
    pub stronger_than_required: Vec<&'static str>,
}

fn shape_implements(kind: AtomicKind, form: &EmittedForm) -> bool {
    match kind {
        AtomicKind::Load => match form.shape {
            FormShape::OrderedLoad | FormShape::PlainLoad => true,
            // The 128-bit LL/SC load writes the value it read back.
            FormShape::ExclusiveLoop => form.bytes == 16,
            _ => false,
        },
        AtomicKind::Store => match form.shape {
            FormShape::OrderedStore | FormShape::PlainStore => true,
            FormShape::ExclusiveLoop => form.bytes == 16,
            _ => false,
        },
        AtomicKind::Rmw => matches!(form.shape, FormShape::LseRmw | FormShape::ExclusiveLoop),
        AtomicKind::CmpXchg => matches!(form.shape, FormShape::LseCas | FormShape::ExclusiveLoop),
        AtomicKind::Fence => form.shape == FormShape::FenceOnly,
    }
}

/// Check the words emitted for ONE atomic operation against the C11/Rust ->
/// AArch64 mapping. `Ok` means mapped and at least as strong as required;
/// every other outcome is a named [`MemoryOrderRefusal`].
pub fn check_lowering(
    request: &AtomicRequest,
    target: OrderingTarget,
    words: &[u32],
) -> Result<ConformanceRow, MemoryOrderRefusal> {
    let required = requirement(request)?;
    let form = analyze_form(words)?;
    check_form(request, target, required, form)
}

fn check_form(
    request: &AtomicRequest,
    target: OrderingTarget,
    required: OrderingRequirement,
    form: EmittedForm,
) -> Result<ConformanceRow, MemoryOrderRefusal> {
    let name = || form.mnemonic.clone();
    if !shape_implements(request.kind, &form) {
        return Err(MemoryOrderRefusal::WrongShape {
            request: *request,
            form: name(),
        });
    }
    if request.kind != AtomicKind::Fence && form.bytes != request.bytes {
        return Err(MemoryOrderRefusal::WidthMismatch {
            request: *request,
            form: name(),
            emitted_bytes: form.bytes,
        });
    }
    if matches!(form.shape, FormShape::PlainLoad | FormShape::PlainStore)
        && form.bytes == 16
        && !target.lse2
    {
        return Err(MemoryOrderRefusal::NotSingleCopyAtomic {
            request: *request,
            form: name(),
        });
    }

    let mut stronger = Vec::new();
    if let Some(read) = form.read {
        let acquired = read.acquire != AcquireVia::None;
        if required.acquire && !acquired {
            return Err(MemoryOrderRefusal::MissingAcquire {
                request: *request,
                form: name(),
            });
        }
        if !required.acquire && acquired {
            stronger.push("acquire");
        }
        let entered = read.sc_entry != SeqCstEntry::None;
        if required.sc_entry && !entered {
            return Err(MemoryOrderRefusal::MissingSeqCstEntry {
                request: *request,
                form: name(),
            });
        }
        // An RCsc load-acquire is its own SeqCst entry, so only a leading
        // full barrier is extra strength of its own.
        if !required.sc_entry && read.sc_entry == SeqCstEntry::LeadingFullBarrier {
            stronger.push("seq-cst entry");
        }
    } else if required.acquire || required.sc_entry {
        return Err(MemoryOrderRefusal::WrongShape {
            request: *request,
            form: name(),
        });
    }
    if let Some(write) = form.write {
        let released = write.release != ReleaseVia::None;
        if required.release && !released {
            return Err(MemoryOrderRefusal::MissingRelease {
                request: *request,
                form: name(),
            });
        }
        if !required.release && released {
            stronger.push("release");
        }
        let exited = write.sc_exit != SeqCstExit::None;
        if required.sc_exit && !exited {
            return Err(MemoryOrderRefusal::MissingSeqCstExit {
                request: *request,
                form: name(),
            });
        }
        // A store-release is its own SeqCst exit, so only a trailing full
        // barrier is extra strength of its own.
        if !required.sc_exit && write.sc_exit == SeqCstExit::TrailingFullBarrier {
            stronger.push("seq-cst exit");
        }
    } else if required.release || required.sc_exit {
        return Err(MemoryOrderRefusal::WrongShape {
            request: *request,
            form: name(),
        });
    }
    if request.kind == AtomicKind::Fence {
        if !form.barrier_orders.covers(required.fence) {
            return Err(MemoryOrderRefusal::WeakerFence {
                request: *request,
                form: name(),
                missing: form.barrier_orders.missing(required.fence),
                local_only_barriers: form.local_only_barriers,
            });
        }
        if form.barrier_orders != required.fence && form.barrier_orders != AccessOrders::NONE {
            stronger.push("barrier orders more pairs than the fence needs");
        }
    }
    Ok(ConformanceRow {
        request: *request,
        form,
        required,
        stronger_than_required: stronger,
    })
}

// ---------------------------------------------------------------------------
// cmpxchg failure-ordering lifting
// ---------------------------------------------------------------------------

/// Every ordering, weakest first along each chain of the lattice
/// `Relaxed < {Acquire, Release} < AcqRel < SeqCst`.
pub const ALL_ORDERINGS: [AtomicOrdering; 5] = [
    AtomicOrdering::Relaxed,
    AtomicOrdering::Acquire,
    AtomicOrdering::Release,
    AtomicOrdering::AcqRel,
    AtomicOrdering::SeqCst,
];

/// `(acquire, release, seq_cst)` of an ordering used as an RMW ordering.
const fn components(ordering: AtomicOrdering) -> (bool, bool, bool) {
    (acquires(ordering), releases(ordering), seq_cst(ordering))
}

const fn at_least(have: (bool, bool, bool), need: (bool, bool, bool)) -> bool {
    (have.0 || !need.0) && (have.1 || !need.1) && (have.2 || !need.2)
}

/// One row of the cmpxchg failure-lifting table.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CmpXchgLiftRow {
    /// Success ordering.
    pub success: AtomicOrdering,
    /// Failure ordering.
    pub failure: AtomicOrdering,
    /// `None` when the failure ordering is invalid (the selector refuses);
    /// otherwise the ordering the selector emits for the pair.
    pub lifted: Option<AtomicOrdering>,
    /// Whether no strictly weaker ordering also covers both.
    pub minimal: bool,
}

/// Check `AtomicOrdering::lift_for_cmpxchg_failure` for one (success,
/// failure) pair: the lifted ordering must acquire when either ordering
/// acquires, release when the success releases, and be SeqCst when either is
/// SeqCst. An invalid failure ordering yields a row with `lifted: None`.
pub fn check_cmpxchg_failure_lift(
    success: AtomicOrdering,
    failure: AtomicOrdering,
) -> Result<CmpXchgLiftRow, MemoryOrderRefusal> {
    if !failure.is_valid_cmpxchg_failure() {
        return Ok(CmpXchgLiftRow {
            success,
            failure,
            lifted: None,
            minimal: true,
        });
    }
    let lifted = success.lift_for_cmpxchg_failure(failure);
    let need = (
        acquires(success) || acquires(failure),
        releases(success),
        seq_cst(success) || seq_cst(failure),
    );
    if !at_least(components(lifted), need) {
        return Err(MemoryOrderRefusal::WeakerCmpXchgLift {
            success,
            failure,
            lifted,
        });
    }
    let minimal = ALL_ORDERINGS.iter().all(|&other| {
        !at_least(components(other), need) || at_least(components(other), components(lifted))
    });
    Ok(CmpXchgLiftRow {
        success,
        failure,
        lifted: Some(lifted),
        minimal,
    })
}

/// The lifting table over all 25 (success, failure) pairs.
pub fn cmpxchg_failure_lift_table() -> Result<Vec<CmpXchgLiftRow>, MemoryOrderRefusal> {
    let mut rows = Vec::with_capacity(25);
    for success in ALL_ORDERINGS {
        for failure in ALL_ORDERINGS {
            rows.push(check_cmpxchg_failure_lift(success, failure)?);
        }
    }
    Ok(rows)
}

// ---------------------------------------------------------------------------
// The LLVM reference mapping (documentation and the rendered table)
// ---------------------------------------------------------------------------

/// The sequence LLVM selects for `request` on an Apple M-series target
/// (LSE, LSE2, RCPC), measured with Apple clang 21 (`-O2 -arch arm64`), and
/// LLVM's armv8.0 exclusive-loop expansion for `lse = false`. Documentation
/// only: conformance is decided by [`check_lowering`], never by comparison
/// with this text.
#[must_use]
pub fn llvm_reference(request: &AtomicRequest, lse: bool) -> &'static str {
    use AtomicOrdering::{AcqRel, Acquire, Relaxed, Release, SeqCst};
    let wide = request.bytes == 16;
    let lifted = request.failure.map_or(request.ordering, |failure| {
        request.ordering.lift_for_cmpxchg_failure(failure)
    });
    match request.kind {
        AtomicKind::Fence => match request.ordering {
            Relaxed => "(none)",
            Acquire => "DMB ISHLD",
            Release | AcqRel | SeqCst => "DMB ISH",
        },
        AtomicKind::Load if wide => match request.ordering {
            Relaxed => "LDP",
            Acquire => "LDP; DMB ISHLD",
            _ => "LDP; DMB ISH",
        },
        AtomicKind::Load => match request.ordering {
            Relaxed => "LDR",
            Acquire => "LDAPR",
            _ => "LDAR",
        },
        AtomicKind::Store if wide => match request.ordering {
            Relaxed => "STP",
            Release => "DMB ISH; STP",
            _ => "DMB ISH; STP; DMB ISH",
        },
        AtomicKind::Store => match request.ordering {
            Relaxed => "STR",
            _ => "STLR",
        },
        AtomicKind::Rmw | AtomicKind::CmpXchg if !lse => match (wide, lifted) {
            (false, Relaxed) => "LDXR/STXR loop",
            (false, Acquire) => "LDAXR/STXR loop",
            (false, Release) => "LDXR/STLXR loop",
            (false, AcqRel | SeqCst) => "LDAXR/STLXR loop",
            (true, Relaxed) => "LDXP/STXP loop",
            (true, Acquire) => "LDAXP/STXP loop",
            (true, Release) => "LDXP/STLXP loop",
            (true, AcqRel | SeqCst) => "LDAXP/STLXP loop",
        },
        AtomicKind::Rmw if wide => match lifted {
            Relaxed => "LDP; CASP loop",
            Acquire => "LDP; CASPA loop",
            Release => "LDP; CASPL loop",
            AcqRel | SeqCst => "LDP; CASPAL loop",
        },
        AtomicKind::CmpXchg if wide => match lifted {
            Relaxed => "CASP",
            Acquire => "CASPA",
            Release => "CASPL",
            AcqRel | SeqCst => "CASPAL",
        },
        AtomicKind::Rmw => match lifted {
            Relaxed => "LD<op>",
            Acquire => "LD<op>A",
            Release => "LD<op>L",
            AcqRel | SeqCst => "LD<op>AL",
        },
        AtomicKind::CmpXchg => match lifted {
            Relaxed => "CAS",
            Acquire => "CASA",
            Release => "CASL",
            AcqRel | SeqCst => "CASAL",
        },
    }
}

/// The inverse view of the mapping: every C11/Rust ordering (a
/// `(success, Some(failure))` pair for a compare-exchange) that the form in
/// `words` implements as an operation of `kind` and width `bytes`, i.e. every
/// request [`check_lowering`] admits for those words. An empty result means
/// the form implements no ordering of that kind (a store barrier as a fence,
/// a lone exclusive, ...).
#[must_use]
pub fn orderings_implemented(
    kind: AtomicKind,
    bytes: u32,
    target: OrderingTarget,
    words: &[u32],
) -> Vec<(AtomicOrdering, Option<AtomicOrdering>)> {
    let mut out = Vec::new();
    for ordering in ALL_ORDERINGS {
        let failures: Vec<Option<AtomicOrdering>> = if kind == AtomicKind::CmpXchg {
            ALL_ORDERINGS.iter().copied().map(Some).collect()
        } else {
            vec![None]
        };
        for failure in failures {
            let request = AtomicRequest {
                kind,
                ordering,
                failure,
                bytes: if kind == AtomicKind::Fence { 0 } else { bytes },
            };
            if check_lowering(&request, target, words).is_ok() {
                out.push((ordering, failure));
            }
        }
    }
    out
}

/// Render admitted rows as a text table: request, emitted form, LLVM's form,
/// and what the emitted form provides beyond the requirement.
#[must_use]
pub fn render_table(rows: &[(ConformanceRow, &'static str)]) -> String {
    let mut out = String::from("request | trust-cg form | LLVM form | stronger than required\n");
    for (row, llvm) in rows {
        out.push_str(&format!(
            "{} | {} | {} | {}\n",
            row.request,
            row.form.mnemonic,
            llvm,
            if row.stronger_than_required.is_empty() {
                "-".to_string()
            } else {
                row.stronger_than_required.join(", ")
            }
        ));
    }
    out
}

#[cfg(test)]
#[path = "aarch64_memory_order_tests.rs"]
mod tests;
