// trust-cg-verify/aarch64_memory_order_tests.rs - unit tests for the
// C11/Rust -> AArch64 memory-order mapping obligations
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Every word below was assembled by Apple clang 21 (`clang -c -arch arm64
// -mcpu=apple-m4`) and read back with `otool -tvj`, so the decoder is checked
// against the platform assembler, not against this crate's encoder.

use super::*;
use AtomicOrdering::{AcqRel, Acquire, Relaxed, Release, SeqCst};

const LDAR_X: u32 = 0xC8DF_FC01;
const LDAR_W: u32 = 0x88DF_FC01;
const LDARH: u32 = 0x48DF_FC01;
const LDARB: u32 = 0x08DF_FC01;
const LDAPR_X: u32 = 0xF8BF_C001;
const LDAPRB: u32 = 0x38BF_C001;
const STLR_X: u32 = 0xC89F_FC01;
const STLRB: u32 = 0x089F_FC01;
const LDXR_X: u32 = 0xC85F_7C01;
const LDAXR_W: u32 = 0x885F_FC01;
const STXR_X: u32 = 0xC802_7C01;
const STLXR_X: u32 = 0xC802_FC01;
const LDXP: u32 = 0xC87F_0C01;
const LDAXP: u32 = 0xC87F_8C01;
const STXP: u32 = 0xC822_0C01;
const STLXP: u32 = 0xC822_8C01;
const LDADD: u32 = 0xF821_0002;
const LDADDA: u32 = 0xF8A1_0002;
const LDADDL: u32 = 0xF861_0002;
const LDADDAL: u32 = 0xF8E1_0002;
const LDADDAL_XZR: u32 = 0xF8E1_001F;
const LDCLRALB: u32 = 0x38E1_1002;
const SWPAL: u32 = 0xF8E1_8002;
const SWPA_W: u32 = 0xB8A1_8002;
const SWPL: u32 = 0xF861_8002;
const LDUMAXAH: u32 = 0x78A1_6002;
const CAS: u32 = 0xC8A1_7C02;
const CASA: u32 = 0xC8E1_7C02;
const CASL: u32 = 0xC8A1_FC02;
const CASAL: u32 = 0xC8E1_FC02;
const CASALB: u32 = 0x08E1_FC02;
const CASPAL: u32 = 0x4862_FC04;
const DMB_ISH: u32 = 0xD503_3BBF;
const DMB_ISHLD: u32 = 0xD503_39BF;
const DMB_ISHST: u32 = 0xD503_3ABF;
const DMB_SY: u32 = 0xD503_3FBF;
const DMB_NSH: u32 = 0xD503_37BF;
const DMB_OSH: u32 = 0xD503_33BF;
const DMB_LD: u32 = 0xD503_3DBF;
const DSB_ISH: u32 = 0xD503_3B9F;
const CLREX: u32 = 0xD503_3F5F;
const LDP_X: u32 = 0xA940_0801;
const STP_X: u32 = 0xA900_0801;
const LDP_FRAME: u32 = 0xA8C1_7BFD;
const STP_FRAME: u32 = 0xA9BF_7BFD;
const LDR_X: u32 = 0xF940_0001;
const STR_X: u32 = 0xF900_0401;
const LDR_SP: u32 = 0xF940_07E1;
const LDR_FP: u32 = 0xF940_0BA1;
const LDUR_X: u32 = 0xF85F_8001;
const LDR_REG: u32 = 0xF863_6801;
const LDRB: u32 = 0x3940_0001;
const LDR_Q: u32 = 0x3DC0_0000;
const LDNP: u32 = 0xA840_0801;
const LDLAR: u32 = 0xC8DF_7C01;
const STLLR: u32 = 0xC89F_7C01;
const LDAPUR: u32 = 0xD940_0001;
const LD1: u32 = 0x4C40_7000;
const PRFM: u32 = 0xF980_0000;
const LDR_LITERAL: u32 = 0x5800_0021;
const RET: u32 = 0xD65F_03C0;
const ADD: u32 = 0x8B02_0020;
const MOV_X0_X8: u32 = 0xAA08_03E0;

/// `ldaxr x8; add; stlxr w10; cbnz` (an AcqRel/SeqCst 64-bit RMW loop).
const RMW_LOOP_ACQ_REL: [u32; 6] = [
    0xC85F_FC08,
    0x8B01_0109,
    0xC80A_FC09,
    0x35FF_FFAA,
    MOV_X0_X8,
    RET,
];
/// `ldaxrb; uxtb; cmp; b.ne; stlxrb; cbnz; b.eq; clrex; ret` (byte CAS).
const CAS_LOOP_ACQ_REL_B: [u32; 9] = [
    0x085F_FC08,
    0x5300_1C2A,
    0x6B0A_011F,
    0x5400_0081,
    0x080A_FC02,
    0x35FF_FF6A,
    0x5400_0040,
    CLREX,
    RET,
];
/// A framed function around one `ldar x0, [x8]` (O0 shape: spill and reload
/// of the pointer through SP).
const FRAMED_LDAR: [u32; 7] = [
    STP_FRAME,
    0x9100_03FD,
    0xF900_07E0,
    0xF940_07E8,
    0xC8DF_FD00,
    LDP_FRAME,
    RET,
];

const NO_LSE2: OrderingTarget = OrderingTarget { lse2: false };
const LSE2: OrderingTarget = OrderingTarget { lse2: true };

fn ok(request: AtomicRequest, words: &[u32]) -> ConformanceRow {
    check_lowering(&request, LSE2, words).unwrap_or_else(|refusal| panic!("{request}: {refusal}"))
}

fn refused(request: AtomicRequest, target: OrderingTarget, words: &[u32]) -> MemoryOrderRefusal {
    match check_lowering(&request, target, words) {
        Ok(row) => panic!("{request}: `{}` must be refused", row.form.mnemonic),
        Err(refusal) => {
            assert!(
                refusal.to_string().starts_with(MEMORY_ORDER_TAG),
                "{refusal}"
            );
            refusal
        }
    }
}

// ---------------------------------------------------------------------------
// Decoder
// ---------------------------------------------------------------------------

#[test]
fn decoder_classifies_every_assembled_ordering_form() {
    use OrderingWord as W;
    let rcsc = |bytes| W::LoadAcquire {
        bytes,
        kind: AcquireKind::Rcsc,
        rt_zero: false,
    };
    let rcpc = |bytes| W::LoadAcquire {
        bytes,
        kind: AcquireKind::Rcpc,
        rt_zero: false,
    };
    let rmw = |bytes, op, acquire_bit, release, rt_zero| W::LseRmw {
        bytes,
        op,
        acquire_bit,
        release,
        rt_zero,
    };
    let cas = |bytes, pair, acquire_bit, release| W::Cas {
        bytes,
        pair,
        acquire_bit,
        release,
        rs_zero: false,
    };
    let cases: Vec<(u32, OrderingWord)> = vec![
        (LDAR_X, rcsc(8)),
        (LDAR_W, rcsc(4)),
        (LDARH, rcsc(2)),
        (LDARB, rcsc(1)),
        (LDAPR_X, rcpc(8)),
        (LDAPRB, rcpc(1)),
        (STLR_X, W::StoreRelease { bytes: 8 }),
        (STLRB, W::StoreRelease { bytes: 1 }),
        (
            LDXR_X,
            W::LoadExclusive {
                bytes: 8,
                pair: false,
                acquire: false,
            },
        ),
        (
            LDAXR_W,
            W::LoadExclusive {
                bytes: 4,
                pair: false,
                acquire: true,
            },
        ),
        (
            STXR_X,
            W::StoreExclusive {
                bytes: 8,
                pair: false,
                release: false,
            },
        ),
        (
            STLXR_X,
            W::StoreExclusive {
                bytes: 8,
                pair: false,
                release: true,
            },
        ),
        (
            LDXP,
            W::LoadExclusive {
                bytes: 16,
                pair: true,
                acquire: false,
            },
        ),
        (
            LDAXP,
            W::LoadExclusive {
                bytes: 16,
                pair: true,
                acquire: true,
            },
        ),
        (
            STXP,
            W::StoreExclusive {
                bytes: 16,
                pair: true,
                release: false,
            },
        ),
        (
            STLXP,
            W::StoreExclusive {
                bytes: 16,
                pair: true,
                release: true,
            },
        ),
        (LDADD, rmw(8, LseOp::Add, false, false, false)),
        (LDADDA, rmw(8, LseOp::Add, true, false, false)),
        (LDADDL, rmw(8, LseOp::Add, false, true, false)),
        (LDADDAL, rmw(8, LseOp::Add, true, true, false)),
        (LDADDAL_XZR, rmw(8, LseOp::Add, true, true, true)),
        (LDCLRALB, rmw(1, LseOp::Clr, true, true, false)),
        (SWPAL, rmw(8, LseOp::Swp, true, true, false)),
        (SWPA_W, rmw(4, LseOp::Swp, true, false, false)),
        (SWPL, rmw(8, LseOp::Swp, false, true, false)),
        (LDUMAXAH, rmw(2, LseOp::Umax, true, false, false)),
        (CAS, cas(8, false, false, false)),
        (CASA, cas(8, false, true, false)),
        (CASL, cas(8, false, false, true)),
        (CASAL, cas(8, false, true, true)),
        (CASALB, cas(1, false, true, true)),
        (CASPAL, cas(16, true, true, true)),
        (CLREX, W::ClearExclusive),
        (
            LDP_X,
            W::PlainLoad {
                bytes: 16,
                pair: true,
            },
        ),
        (
            STP_X,
            W::PlainStore {
                bytes: 16,
                pair: true,
            },
        ),
        (LDP_FRAME, W::Private),
        (STP_FRAME, W::Private),
        (
            LDR_X,
            W::PlainLoad {
                bytes: 8,
                pair: false,
            },
        ),
        (
            STR_X,
            W::PlainStore {
                bytes: 8,
                pair: false,
            },
        ),
        (LDR_SP, W::Private),
        (LDR_FP, W::Private),
        (
            LDUR_X,
            W::PlainLoad {
                bytes: 8,
                pair: false,
            },
        ),
        (
            LDR_REG,
            W::PlainLoad {
                bytes: 8,
                pair: false,
            },
        ),
        (
            LDRB,
            W::PlainLoad {
                bytes: 1,
                pair: false,
            },
        ),
        (
            LDR_Q,
            W::PlainLoad {
                bytes: 16,
                pair: false,
            },
        ),
        (LDNP, W::Unclassified),
        (LDLAR, W::Unclassified),
        (STLLR, W::Unclassified),
        (LDAPUR, W::Unclassified),
        (LD1, W::Unclassified),
        (PRFM, W::NonMemory),
        (LDR_LITERAL, W::Private),
        (RET, W::NonMemory),
        (ADD, W::NonMemory),
    ];
    for (word, want) in cases {
        assert_eq!(decode_ordering_word(word), want, "{word:#010x}");
    }
}

#[test]
fn decoder_reads_barrier_kind_and_domain_from_crm() {
    let barrier = |word| match decode_ordering_word(word) {
        OrderingWord::Barrier(barrier) => barrier,
        other => panic!("{word:#010x}: {other:?}"),
    };
    let ish = barrier(DMB_ISH);
    assert_eq!(
        (ish.domain, ish.orders, ish.mnemonic().as_str()),
        (BarrierDomain::InnerShareable, AccessOrders::FULL, "DMB ISH")
    );
    let ishld = barrier(DMB_ISHLD);
    assert_eq!(
        (ishld.domain, ishld.orders),
        (BarrierDomain::InnerShareable, AccessOrders::LOAD)
    );
    let ishst = barrier(DMB_ISHST);
    assert_eq!(
        (ishst.domain, ishst.orders),
        (BarrierDomain::InnerShareable, AccessOrders::STORE)
    );
    assert_eq!(barrier(DMB_SY).domain, BarrierDomain::FullSystem);
    assert_eq!(barrier(DMB_OSH).domain, BarrierDomain::OuterShareable);
    assert_eq!(barrier(DMB_LD).orders, AccessOrders::LOAD);
    let nsh = barrier(DMB_NSH);
    assert_eq!(nsh.domain, BarrierDomain::NonShareable);
    assert_eq!(nsh.thread_orders(), AccessOrders::NONE);
    assert!(barrier(DSB_ISH).dsb);
    // CRm<1:0> = 00 is reserved for DMB: refused, never read as a barrier.
    assert_eq!(
        decode_ordering_word(0xD503_30BF | (0x8 << 8)),
        OrderingWord::Unclassified
    );
}

// ---------------------------------------------------------------------------
// The mapping, positive rows
// ---------------------------------------------------------------------------

#[test]
fn fences_map_to_the_llvm_barriers() {
    assert!(
        ok(AtomicRequest::fence(Relaxed), &[RET])
            .stronger_than_required
            .is_empty()
    );
    let acquire = ok(AtomicRequest::fence(Acquire), &[DMB_ISHLD, RET]);
    assert!(acquire.stronger_than_required.is_empty());
    for ordering in [Release, AcqRel] {
        let row = ok(AtomicRequest::fence(ordering), &[DMB_ISH, RET]);
        assert_eq!(row.form.mnemonic, "DMB ISH");
        // A full barrier also orders W->R, which neither fence needs.
        assert!(!row.stronger_than_required.is_empty());
    }
    assert!(
        ok(AtomicRequest::fence(SeqCst), &[DMB_ISH, RET])
            .stronger_than_required
            .is_empty()
    );
    // Wider domains are at least as strong.
    ok(AtomicRequest::fence(SeqCst), &[DMB_SY]);
    ok(AtomicRequest::fence(SeqCst), &[DMB_OSH]);
    ok(AtomicRequest::fence(Acquire), &[DMB_LD]);
}

#[test]
fn ldar_stlr_and_lse_forms_meet_every_ordering_they_are_selected_for() {
    for (bytes, load) in [(8, LDAR_X), (4, LDAR_W), (2, LDARH), (1, LDARB)] {
        for ordering in [Relaxed, Acquire, SeqCst] {
            ok(AtomicRequest::load(bytes, ordering), &[load, RET]);
        }
    }
    // LDAR for a Relaxed load is stronger than required (LLVM: LDR).
    assert_eq!(
        ok(AtomicRequest::load(8, Relaxed), &[LDAR_X]).stronger_than_required,
        vec!["acquire"]
    );
    for ordering in [Relaxed, Release, SeqCst] {
        ok(AtomicRequest::store(8, ordering), &[STLR_X, RET]);
        ok(AtomicRequest::store(1, ordering), &[STLRB, RET]);
    }
    for (ordering, word) in [
        (Relaxed, LDADD),
        (Acquire, LDADDA),
        (Release, LDADDL),
        (AcqRel, LDADDAL),
        (SeqCst, LDADDAL),
    ] {
        let row = ok(AtomicRequest::rmw(8, ordering), &[word, RET]);
        assert!(
            row.stronger_than_required.is_empty(),
            "{ordering:?}: {row:?}"
        );
    }
    ok(AtomicRequest::rmw(1, SeqCst), &[LDCLRALB]);
    ok(AtomicRequest::rmw(2, Acquire), &[LDUMAXAH]);
    ok(AtomicRequest::rmw(8, SeqCst), &[SWPAL]);
    ok(AtomicRequest::rmw(4, Acquire), &[SWPA_W]);
    ok(AtomicRequest::rmw(8, Release), &[SWPL]);
    for (success, failure, word) in [
        (Relaxed, Relaxed, CAS),
        (Acquire, Relaxed, CASA),
        (Relaxed, Acquire, CASA),
        (Release, Relaxed, CASL),
        (Release, Acquire, CASAL),
        (AcqRel, Acquire, CASAL),
        (SeqCst, SeqCst, CASAL),
        (Relaxed, SeqCst, CASAL),
    ] {
        ok(AtomicRequest::cmpxchg(8, success, failure), &[word, RET]);
    }
    ok(AtomicRequest::cmpxchg(1, SeqCst, Relaxed), &[CASALB]);
    ok(AtomicRequest::cmpxchg(16, SeqCst, SeqCst), &[CASPAL]);
}

#[test]
fn exclusive_loops_take_their_ordering_from_the_exclusive_pair() {
    ok(AtomicRequest::rmw(8, SeqCst), &RMW_LOOP_ACQ_REL);
    ok(
        AtomicRequest::cmpxchg(1, SeqCst, SeqCst),
        &CAS_LOOP_ACQ_REL_B,
    );
    ok(AtomicRequest::rmw(8, Relaxed), &[LDXR_X, ADD, STXR_X, RET]);
    ok(AtomicRequest::rmw(8, Release), &[LDXR_X, ADD, STLXR_X, RET]);
    // 128-bit load, store, RMW through the pair exclusives.
    ok(AtomicRequest::load(16, SeqCst), &[LDAXP, STLXP, RET]);
    ok(AtomicRequest::load(16, Acquire), &[LDAXP, STXP, RET]);
    ok(AtomicRequest::store(16, Release), &[LDXP, STLXP, RET]);
    ok(AtomicRequest::rmw(16, AcqRel), &[LDAXP, ADD, STLXP, RET]);
    // A single-register exclusive loop is not a load or store form.
    assert!(matches!(
        refused(AtomicRequest::load(8, Relaxed), LSE2, &[LDXR_X, STXR_X]),
        MemoryOrderRefusal::WrongShape { .. }
    ));
}

#[test]
fn frame_accesses_are_ignored_and_the_atomic_is_still_found() {
    let row = ok(AtomicRequest::load(8, SeqCst), &FRAMED_LDAR);
    assert_eq!(row.form.mnemonic, "LDAR (8 B)");
}

#[test]
fn lse2_128_bit_forms_need_the_entry_barrier_for_seq_cst() {
    ok(AtomicRequest::load(16, Relaxed), &[LDP_X, RET]);
    ok(AtomicRequest::load(16, Acquire), &[LDP_X, DMB_ISHLD, RET]);
    let fixed = ok(
        AtomicRequest::load(16, SeqCst),
        &[DMB_ISH, LDP_X, DMB_ISH, RET],
    );
    assert_eq!(fixed.form.mnemonic, "DMB ISH; LDP (16 B); DMB ISH");
    // LLVM's FEAT_LSE2 SeqCst load (`ldp; dmb ish`): acquire through the
    // trailing barrier, but NO SeqCst entry, so an earlier STLR or STLXP
    // SeqCst store is not ordered before it.
    assert!(matches!(
        refused(
            AtomicRequest::load(16, SeqCst),
            LSE2,
            &[LDP_X, DMB_ISH, RET]
        ),
        MemoryOrderRefusal::MissingSeqCstEntry { .. }
    ));
    // LLVM's stores: the leading full barrier releases, the trailing one is
    // the SeqCst exit.
    ok(AtomicRequest::store(16, Release), &[DMB_ISH, STP_X, RET]);
    ok(
        AtomicRequest::store(16, SeqCst),
        &[DMB_ISH, STP_X, DMB_ISH, RET],
    );
    assert!(matches!(
        refused(AtomicRequest::store(16, SeqCst), LSE2, &[DMB_ISH, STP_X]),
        MemoryOrderRefusal::MissingSeqCstExit { .. }
    ));
    // Without FEAT_LSE2 the plain pair can tear.
    assert!(matches!(
        refused(AtomicRequest::load(16, Relaxed), NO_LSE2, &[LDP_X]),
        MemoryOrderRefusal::NotSingleCopyAtomic { .. }
    ));
}

// ---------------------------------------------------------------------------
// Negative controls: each weaker form is refused by name
// ---------------------------------------------------------------------------

#[test]
fn the_old_release_fence_selection_is_refused_as_weaker() {
    // The pre-L03-P3 selector emitted DMB ISHST for fence(Release): it orders
    // W->W only, so an earlier LOAD may be satisfied after a later store.
    let refusal = refused(AtomicRequest::fence(Release), LSE2, &[DMB_ISHST, RET]);
    assert_eq!(
        refusal,
        MemoryOrderRefusal::WeakerFence {
            request: AtomicRequest::fence(Release),
            form: "DMB ISHST".to_string(),
            missing: vec!["R->W"],
            local_only_barriers: 0,
        }
    );
    assert!(refusal.to_string().contains("WeakerFence"), "{refusal}");
    // And for every other fence that needs more than W->W.
    for ordering in [Acquire, AcqRel, SeqCst] {
        assert!(matches!(
            refused(AtomicRequest::fence(ordering), LSE2, &[DMB_ISHST]),
            MemoryOrderRefusal::WeakerFence { .. }
        ));
    }
    // An acquire barrier is not a release barrier, nor a SeqCst one.
    assert!(matches!(
        refused(AtomicRequest::fence(Release), LSE2, &[DMB_ISHLD]),
        MemoryOrderRefusal::WeakerFence { .. }
    ));
    assert!(matches!(
        refused(AtomicRequest::fence(SeqCst), LSE2, &[DMB_ISHLD]),
        MemoryOrderRefusal::WeakerFence { .. }
    ));
    // A missing barrier.
    assert!(matches!(
        refused(AtomicRequest::fence(Acquire), LSE2, &[RET]),
        MemoryOrderRefusal::WeakerFence { .. }
    ));
    // A non-shareable barrier orders nothing another thread observes.
    let nsh = refused(AtomicRequest::fence(SeqCst), LSE2, &[DMB_NSH]);
    assert!(
        matches!(
            nsh,
            MemoryOrderRefusal::WeakerFence {
                local_only_barriers: 1,
                ..
            }
        ),
        "{nsh}"
    );
}

/// A weakened form, and the refusal it must earn.
type LossCase = (AtomicRequest, Vec<u32>, fn(&MemoryOrderRefusal) -> bool);

#[test]
fn every_ordering_bit_loss_is_refused_by_name() {
    use MemoryOrderRefusal as R;
    let cases: Vec<LossCase> = vec![
        // LDAR -> LDR.
        (AtomicRequest::load(8, Acquire), vec![LDR_X], |r| {
            matches!(r, R::MissingAcquire { .. })
        }),
        // LDAR -> LDAPR for SeqCst (RCpc has no SeqCst entry).
        (AtomicRequest::load(8, SeqCst), vec![LDAPR_X], |r| {
            matches!(r, R::MissingSeqCstEntry { .. })
        }),
        // STLR -> STR.
        (AtomicRequest::store(8, Release), vec![STR_X], |r| {
            matches!(r, R::MissingRelease { .. })
        }),
        // A store barrier does not release earlier loads.
        (
            AtomicRequest::store(8, Release),
            vec![DMB_ISHST, STR_X],
            |r| matches!(r, R::MissingRelease { .. }),
        ),
        // A SeqCst plain store behind a full barrier has no exit.
        (AtomicRequest::store(8, SeqCst), vec![DMB_ISH, STR_X], |r| {
            matches!(r, R::MissingSeqCstExit { .. })
        }),
        // LDADDAL -> LDADDL / LDADDA.
        (AtomicRequest::rmw(8, SeqCst), vec![LDADDL], |r| {
            matches!(r, R::MissingAcquire { .. })
        }),
        (AtomicRequest::rmw(8, AcqRel), vec![LDADDA], |r| {
            matches!(r, R::MissingRelease { .. })
        }),
        // A = 1 with Rt = XZR: acquire semantics dropped.
        (AtomicRequest::rmw(8, SeqCst), vec![LDADDAL_XZR], |r| {
            matches!(r, R::MissingAcquire { .. })
        }),
        // CASAL -> CASL for (Release, Acquire): the failure acquire is lost.
        (
            AtomicRequest::cmpxchg(8, Release, Acquire),
            vec![CASL],
            |r| matches!(r, R::MissingAcquire { .. }),
        ),
        // A plain CAS for (Relaxed, SeqCst): the SeqCst failure needs an
        // acquiring (RCsc) read.
        (AtomicRequest::cmpxchg(8, Relaxed, SeqCst), vec![CAS], |r| {
            matches!(r, R::MissingAcquire { .. })
        }),
        // LDAXR -> LDXR in an acquiring loop; STLXR -> STXR in a releasing one.
        (
            AtomicRequest::rmw(8, Acquire),
            vec![LDXR_X, ADD, STXR_X],
            |r| matches!(r, R::MissingAcquire { .. }),
        ),
        (
            AtomicRequest::rmw(8, Release),
            vec![LDXR_X, ADD, STXR_X],
            |r| matches!(r, R::MissingRelease { .. }),
        ),
        // Width.
        (AtomicRequest::load(4, Acquire), vec![LDAR_X], |r| {
            matches!(r, R::WidthMismatch { .. })
        }),
        // Shape: an RMW is not a CAS, a fence has no access.
        (
            AtomicRequest::cmpxchg(8, SeqCst, SeqCst),
            vec![LDADDAL],
            |r| matches!(r, R::WrongShape { .. }),
        ),
        (AtomicRequest::fence(SeqCst), vec![LDAR_X, DMB_ISH], |r| {
            matches!(r, R::WrongShape { .. })
        }),
        // Unmodeled access forms fail closed.
        (AtomicRequest::load(8, Acquire), vec![LDLAR], |r| {
            matches!(r, R::UnclassifiedAccess { index: 0, .. })
        }),
        (AtomicRequest::load(8, Acquire), vec![LDAPUR], |r| {
            matches!(r, R::UnclassifiedAccess { .. })
        }),
        (AtomicRequest::store(8, Release), vec![STLLR], |r| {
            matches!(r, R::UnclassifiedAccess { .. })
        }),
        // Two accesses are not one atomic operation.
        (AtomicRequest::load(8, Acquire), vec![LDAR_X, LDAR_X], |r| {
            matches!(r, R::Unmapped { .. })
        }),
        (AtomicRequest::rmw(8, SeqCst), vec![LDAXR_W], |r| {
            matches!(r, R::Unmapped { .. })
        }),
        // A barrier between the exclusives.
        (
            AtomicRequest::rmw(8, SeqCst),
            vec![0xC85F_FC08, DMB_ISH, 0xC80A_FC09],
            |r| matches!(r, R::Unmapped { .. }),
        ),
    ];
    for (request, words, expected) in cases {
        let refusal = refused(request, LSE2, &words);
        assert!(expected(&refusal), "{request}: {refusal}");
    }
    // CASA meets (Relaxed, SeqCst): its read is an RCsc acquire, the SeqCst
    // failure's whole need (the selector lifts the pair to CASAL anyway).
    ok(AtomicRequest::cmpxchg(8, Relaxed, SeqCst), &[CASA]);
}

#[test]
fn orderings_without_a_mapping_row_are_refused_before_decoding() {
    for (request, reason) in [
        (AtomicRequest::load(8, Release), "cannot release"),
        (AtomicRequest::load(8, AcqRel), "cannot release"),
        (AtomicRequest::store(8, Acquire), "cannot acquire"),
        (AtomicRequest::store(8, AcqRel), "cannot acquire"),
        (
            AtomicRequest::cmpxchg(8, SeqCst, Release),
            "failure ordering",
        ),
        (
            AtomicRequest::cmpxchg(8, SeqCst, AcqRel),
            "failure ordering",
        ),
        (AtomicRequest::load(3, Relaxed), "access width"),
    ] {
        let refusal = refused(request, LSE2, &[LDAR_X, STLR_X]);
        assert!(
            matches!(refusal, MemoryOrderRefusal::NoMappingRow { .. })
                && refusal.to_string().contains(reason),
            "{request}: {refusal}"
        );
    }
}

// ---------------------------------------------------------------------------
// SeqCst pairing and cmpxchg lifting
// ---------------------------------------------------------------------------

#[test]
fn every_admitted_seq_cst_exit_entry_pair_is_ordered() {
    // Admission requires exit in {StoreRelease, TrailingFullBarrier} and
    // entry in {AcquireRcsc, LeadingFullBarrier}; every such pair is ordered,
    // so per-operation admission composes for any mix of SeqCst operations.
    for exit in [SeqCstExit::StoreRelease, SeqCstExit::TrailingFullBarrier] {
        for entry in [SeqCstEntry::AcquireRcsc, SeqCstEntry::LeadingFullBarrier] {
            assert!(seq_cst_pair_ordered(exit, entry), "{exit:?} {entry:?}");
        }
    }
    // The refused entry: LLVM's `ldp; dmb ish` after a store-release.
    assert!(!seq_cst_pair_ordered(
        SeqCstExit::StoreRelease,
        SeqCstEntry::None
    ));
    // It is ordered only after a trailing-barrier store, which neither STLR
    // nor the 128-bit STLXP loop has.
    assert!(seq_cst_pair_ordered(
        SeqCstExit::TrailingFullBarrier,
        SeqCstEntry::None
    ));
    // And the refused exit: a plain store behind a leading barrier.
    assert!(!seq_cst_pair_ordered(
        SeqCstExit::None,
        SeqCstEntry::AcquireRcsc
    ));
}

#[test]
fn cmpxchg_failure_lifting_covers_both_orderings_minimally() {
    let table = cmpxchg_failure_lift_table().unwrap_or_else(|refusal| panic!("{refusal}"));
    assert_eq!(table.len(), 25);
    let mut valid = 0;
    for row in &table {
        let failure_valid = matches!(row.failure, Relaxed | Acquire | SeqCst);
        assert_eq!(row.lifted.is_some(), failure_valid, "{row:?}");
        if let Some(lifted) = row.lifted {
            valid += 1;
            assert!(row.minimal, "{row:?}: the lift is not minimal");
            // The emitted CAS for the pair meets the cmpxchg requirement.
            let word = match lifted {
                Relaxed => CAS,
                Acquire => CASA,
                Release => CASL,
                AcqRel | SeqCst => CASAL,
            };
            ok(AtomicRequest::cmpxchg(8, row.success, row.failure), &[word]);
        }
    }
    assert_eq!(valid, 15);
    let lifted = |success, failure| {
        check_cmpxchg_failure_lift(success, failure)
            .unwrap()
            .lifted
            .unwrap()
    };
    assert_eq!(lifted(Release, Acquire), AcqRel);
    assert_eq!(lifted(Relaxed, Acquire), Acquire);
    assert_eq!(lifted(Relaxed, SeqCst), SeqCst);
    assert_eq!(lifted(AcqRel, SeqCst), SeqCst);
    assert_eq!(lifted(SeqCst, Relaxed), SeqCst);
}

#[test]
fn llvm_reference_and_table_rendering() {
    assert_eq!(
        llvm_reference(&AtomicRequest::fence(Release), true),
        "DMB ISH"
    );
    assert_eq!(
        llvm_reference(&AtomicRequest::load(16, SeqCst), true),
        "LDP; DMB ISH"
    );
    assert_eq!(
        llvm_reference(&AtomicRequest::cmpxchg(4, Release, Acquire), true),
        "CASAL"
    );
    assert_eq!(
        llvm_reference(&AtomicRequest::rmw(8, Release), false),
        "LDXR/STLXR loop"
    );
    let row = ok(AtomicRequest::fence(Release), &[DMB_ISH]);
    let table = render_table(&[(row, "DMB ISH")]);
    assert!(
        table.contains("fence.Release | DMB ISH | DMB ISH |"),
        "{table}"
    );
}

#[test]
fn a_128_bit_compare_exchange_loop_is_as_ordered_as_its_weakest_store_exclusive() {
    // The LL/SC 128-bit compare-exchange: one LDAXP, the success STLXP and the
    // failure write-back STLXP.
    let row = ok(
        AtomicRequest::cmpxchg(16, SeqCst, SeqCst),
        &[LDAXP, STLXP, STLXP, RET],
    );
    assert_eq!(row.form.mnemonic, "LDAXP; STLXP (16 B); STLXP (16 B)");
    // One unordered store-exclusive is enough to lose the release.
    assert!(matches!(
        refused(
            AtomicRequest::cmpxchg(16, SeqCst, SeqCst),
            LSE2,
            &[LDAXP, STLXP, STXP]
        ),
        MemoryOrderRefusal::MissingRelease { .. }
    ));
    // A store-exclusive of another width is not part of the loop.
    assert!(matches!(
        refused(AtomicRequest::rmw(16, SeqCst), LSE2, &[LDAXP, STLXR_X]),
        MemoryOrderRefusal::Unmapped { .. }
    ));
}

/// The inverse table: which C11/Rust orderings each decoded form implements.
#[test]
fn each_decoded_form_implements_exactly_these_orderings() {
    let plain = |orderings: &[AtomicOrdering]| -> Vec<(AtomicOrdering, Option<AtomicOrdering>)> {
        orderings.iter().map(|&ordering| (ordering, None)).collect()
    };
    let implemented = |kind, bytes, words: &[u32]| orderings_implemented(kind, bytes, LSE2, words);
    use AtomicKind::{CmpXchg, Fence, Load, Rmw, Store};
    // Loads: LDAR is RCsc (every load ordering); LDAPR is RCpc (no SeqCst);
    // a plain load is Relaxed only.
    assert_eq!(
        implemented(Load, 8, &[LDAR_X]),
        plain(&[Relaxed, Acquire, SeqCst])
    );
    assert_eq!(implemented(Load, 8, &[LDAPR_X]), plain(&[Relaxed, Acquire]));
    assert_eq!(implemented(Load, 8, &[LDR_X]), plain(&[Relaxed]));
    // Stores.
    assert_eq!(
        implemented(Store, 8, &[STLR_X]),
        plain(&[Relaxed, Release, SeqCst])
    );
    assert_eq!(implemented(Store, 8, &[STR_X]), plain(&[Relaxed]));
    // LSE RMWs by their A/R bits, and the exclusive loops by theirs.
    assert_eq!(implemented(Rmw, 8, &[LDADD]), plain(&[Relaxed]));
    assert_eq!(implemented(Rmw, 8, &[LDADDA]), plain(&[Relaxed, Acquire]));
    assert_eq!(implemented(Rmw, 8, &[LDADDL]), plain(&[Relaxed, Release]));
    assert_eq!(
        implemented(Rmw, 8, &[LDADDAL]),
        plain(&[Relaxed, Acquire, Release, AcqRel, SeqCst])
    );
    assert_eq!(
        implemented(Rmw, 8, &[LDADDAL_XZR]),
        plain(&[Relaxed, Release])
    );
    assert_eq!(implemented(Rmw, 8, &[LDXR_X, STXR_X]), plain(&[Relaxed]));
    assert_eq!(
        implemented(Rmw, 8, &[LDXR_X, STLXR_X]),
        plain(&[Relaxed, Release])
    );
    assert_eq!(
        implemented(Rmw, 8, &RMW_LOOP_ACQ_REL),
        plain(&[Relaxed, Acquire, Release, AcqRel, SeqCst])
    );
    // Fences: ISHLD is the Acquire fence, ISH every fence, ISHST none but the
    // (empty) Relaxed one.
    assert_eq!(
        implemented(Fence, 0, &[DMB_ISHLD]),
        plain(&[Relaxed, Acquire])
    );
    assert_eq!(
        implemented(Fence, 0, &[DMB_ISH]),
        plain(&[Relaxed, Acquire, Release, AcqRel, SeqCst])
    );
    assert_eq!(implemented(Fence, 0, &[DMB_ISHST]), plain(&[Relaxed]));
    // CAS: the (success, failure) pairs; the failure ordering is never
    // Release/AcqRel. CASL implements only the pairs whose failure is Relaxed
    // and whose success needs no acquire.
    assert_eq!(
        implemented(CmpXchg, 8, &[CASL]),
        vec![(Relaxed, Some(Relaxed)), (Release, Some(Relaxed))]
    );
    assert_eq!(
        implemented(CmpXchg, 8, &[CAS]),
        vec![(Relaxed, Some(Relaxed))]
    );
    assert_eq!(implemented(CmpXchg, 8, &[CASAL]).len(), 15);
    // CASA: every pair without a release, the SeqCst failures included (its
    // read is an RCsc acquire, all a SeqCst failure needs).
    assert_eq!(
        implemented(CmpXchg, 8, &[CASA]),
        vec![
            (Relaxed, Some(Relaxed)),
            (Relaxed, Some(Acquire)),
            (Relaxed, Some(SeqCst)),
            (Acquire, Some(Relaxed)),
            (Acquire, Some(Acquire)),
            (Acquire, Some(SeqCst)),
        ]
    );
}
