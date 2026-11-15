// cegis_cache_codec - acceptance gate for the in-tree CEGIS cache wire format
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// `cegis_cache_codec` replaced `rmp-serde` as the CEGIS cache payload format so
// that no third-party serializer sits on a shipping path. `rmp-serde` is
// retained as a DEV dependency for exactly this file: while both codecs exist,
// the incumbent is the oracle.
//
// What is being defended. A cache MISS is free — the pass re-runs CEGIS
// enumeration. A wrong cache HIT is a miscompile: the hit path replays recorded
// rewrites into a machine function without a solver in the loop. So the tests
// below are weighted toward rejection, not acceptance:
//
//   G-B1  round-trip over a generated corpus and over every enum variant
//   G-B2  differential vs. the incumbent, both directions of cross-rejection
//   G-B3  the version gate, including a genuine v5 MessagePack blob
//   plus   adversarial/truncation cases that must decode to a miss, not a panic
//
// Every assertion here was seen to FAIL under a deliberate mutation before it
// was trusted; the mutations are recorded in the slot report.

use rmp_serde as incumbent;
use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand, PReg, RegClass, SpecialReg, VReg};
use trust_cg_verify::CacheCodecError;
use trust_cg_verify::cegis_pass::{
    CegisCacheEntry, CegisSearchCompletion, MachInstBlob, MachOperandBlob, ProvenRewrite,
    RegClassBlob, RewriteLayer, SpecialRegBlob,
};

// ---------------------------------------------------------------------------
// Deterministic generation (no third-party RNG; the point of this work is that
// the shipping graph shrinks, and a dev-dep RNG would be a poor advertisement)
// ---------------------------------------------------------------------------

/// SplitMix64. Fixed seed: a failure here must be reproducible from the message
/// alone.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn gen_operand(rng: &mut Rng) -> MachOperandBlob {
    match rng.below(12) {
        0 => MachOperandBlob::VReg {
            id: rng.next() as u32,
            class: gen_reg_class(rng),
        },
        1 => MachOperandBlob::PReg {
            encoding: rng.next() as u16,
        },
        2 => MachOperandBlob::Imm(rng.next() as i64),
        3 => MachOperandBlob::FImmBits(rng.next()),
        4 => MachOperandBlob::Block(rng.next() as u32),
        5 => MachOperandBlob::StackSlot(rng.next() as u32),
        6 => MachOperandBlob::FrameIndex(rng.next() as i32),
        7 => MachOperandBlob::MemOp {
            base_encoding: rng.next() as u16,
            offset: rng.next() as i64,
        },
        8 => MachOperandBlob::Special(gen_special(rng)),
        9 => MachOperandBlob::Symbol(gen_symbol(rng)),
        10 => MachOperandBlob::JumpTableIndex(rng.next() as u32),
        _ => MachOperandBlob::IncomingArg(rng.next() as i64),
    }
}

fn gen_reg_class(rng: &mut Rng) -> RegClassBlob {
    match rng.below(8) {
        0 => RegClassBlob::Gpr64,
        1 => RegClassBlob::Gpr32,
        2 => RegClassBlob::Fpr128,
        3 => RegClassBlob::Fpr64,
        4 => RegClassBlob::Fpr32,
        5 => RegClassBlob::Fpr16,
        6 => RegClassBlob::Fpr8,
        _ => RegClassBlob::System,
    }
}

fn gen_special(rng: &mut Rng) -> SpecialRegBlob {
    match rng.below(3) {
        0 => SpecialRegBlob::SP,
        1 => SpecialRegBlob::XZR,
        _ => SpecialRegBlob::WZR,
    }
}

/// Symbols are attacker-adjacent data: they come from object files. Include the
/// empty string, Unicode, and bytes that would break a naive length-prefixed
/// reader.
fn gen_symbol(rng: &mut Rng) -> String {
    const SAMPLES: &[&str] = &[
        "",
        "_main",
        "core::ptr::drop_in_place",
        "l_anon.0",
        "ünïcödé_symbol",
        "日本語",
        "with\0embedded\0nul",
        "with\"quotes\"and\\backslashes",
        "\u{1F600}",
    ];
    let mut s = SAMPLES[rng.below(SAMPLES.len() as u64) as usize].to_string();
    if rng.below(4) == 0 {
        s.push_str(&format!(".{}", rng.next()));
    }
    s
}

fn gen_inst(rng: &mut Rng) -> MachInstBlob {
    let n = rng.below(4);
    MachInstBlob {
        opcode: ["AddRI", "AndRI", "Movz", "NotAnOpcode", ""][rng.below(5) as usize].to_string(),
        operands: (0..n).map(|_| gen_operand(rng)).collect(),
    }
}

fn gen_rewrite(rng: &mut Rng) -> ProvenRewrite {
    let n = rng.below(3);
    ProvenRewrite {
        inst_index: rng.next() as u32,
        proof_hash: rng.next(),
        iterations: rng.next() as u32,
        window_len: rng.next() as u32,
        replacement: (0..n).map(|_| gen_inst(rng)).collect(),
        layer: match rng.below(3) {
            0 => RewriteLayer::A,
            1 => RewriteLayer::B,
            _ => RewriteLayer::C,
        },
    }
}

fn gen_entry(rng: &mut Rng) -> CegisCacheEntry {
    let n = rng.below(5);
    CegisCacheEntry {
        version: CegisCacheEntry::VERSION,
        completion: CegisSearchCompletion::Complete,
        proven_rewrites: (0..n).map(|_| gen_rewrite(rng)).collect(),
        attempted: rng.next(),
        verified: rng.next(),
        rejected: rng.next(),
    }
}

fn corpus(n: usize) -> Vec<CegisCacheEntry> {
    let mut rng = Rng(0x0BAD_C0DE_D15E_A5E5);
    (0..n).map(|_| gen_entry(&mut rng)).collect()
}

/// One entry that names every operand variant, every register class, every
/// special register and every layer, plus the numeric extremes. Generation is
/// random; this is the part that is guaranteed to be exhaustive.
fn every_variant_entry() -> CegisCacheEntry {
    let operands = vec![
        MachOperandBlob::VReg {
            id: 0,
            class: RegClassBlob::Gpr64,
        },
        MachOperandBlob::VReg {
            id: u32::MAX,
            class: RegClassBlob::Gpr32,
        },
        MachOperandBlob::VReg {
            id: 1,
            class: RegClassBlob::Fpr128,
        },
        MachOperandBlob::VReg {
            id: 2,
            class: RegClassBlob::Fpr64,
        },
        MachOperandBlob::VReg {
            id: 3,
            class: RegClassBlob::Fpr32,
        },
        MachOperandBlob::VReg {
            id: 4,
            class: RegClassBlob::Fpr16,
        },
        MachOperandBlob::VReg {
            id: 5,
            class: RegClassBlob::Fpr8,
        },
        MachOperandBlob::VReg {
            id: 6,
            class: RegClassBlob::System,
        },
        MachOperandBlob::PReg { encoding: 0 },
        MachOperandBlob::PReg { encoding: u16::MAX },
        MachOperandBlob::ExactModuleSymbol("exact_callback".into()),
        MachOperandBlob::Symbol("exact_callback".into()),
        MachOperandBlob::Imm(i64::MIN),
        MachOperandBlob::Imm(i64::MAX),
        MachOperandBlob::Imm(-1),
        // Bit patterns that a round-trip through `f64` would destroy: a
        // signalling NaN payload, and negative zero.
        MachOperandBlob::FImmBits(f64::NAN.to_bits()),
        MachOperandBlob::FImmBits(0x7FF0_0000_0000_0001),
        MachOperandBlob::FImmBits((-0.0f64).to_bits()),
        MachOperandBlob::FImmBits(u64::MAX),
        MachOperandBlob::Block(u32::MAX),
        MachOperandBlob::StackSlot(u32::MAX),
        MachOperandBlob::FrameIndex(i32::MIN),
        MachOperandBlob::FrameIndex(i32::MAX),
        MachOperandBlob::MemOp {
            base_encoding: 31,
            offset: i64::MIN,
        },
        MachOperandBlob::Special(SpecialRegBlob::SP),
        MachOperandBlob::Special(SpecialRegBlob::XZR),
        MachOperandBlob::Special(SpecialRegBlob::WZR),
        MachOperandBlob::Symbol(String::new()),
        MachOperandBlob::Symbol("日本語\u{1F600}".to_string()),
        MachOperandBlob::JumpTableIndex(u32::MAX),
        MachOperandBlob::IncomingArg(i64::MIN),
    ];
    CegisCacheEntry {
        version: CegisCacheEntry::VERSION,
        completion: CegisSearchCompletion::Complete,
        proven_rewrites: vec![
            ProvenRewrite {
                inst_index: u32::MAX,
                proof_hash: u64::MAX,
                iterations: u32::MAX,
                window_len: u32::MAX,
                replacement: vec![MachInstBlob {
                    opcode: "Movz".to_string(),
                    operands,
                }],
                layer: RewriteLayer::A,
            },
            ProvenRewrite {
                inst_index: 0,
                proof_hash: 0,
                iterations: 0,
                window_len: 0,
                // Empty replacement body: the degenerate sequence.
                replacement: Vec::new(),
                layer: RewriteLayer::B,
            },
            ProvenRewrite {
                inst_index: 7,
                proof_hash: 0xDEAD_BEEF,
                iterations: 1,
                window_len: 2,
                replacement: vec![MachInstBlob {
                    opcode: String::new(),
                    operands: Vec::new(),
                }],
                layer: RewriteLayer::C,
            },
        ],
        attempted: u64::MAX,
        verified: 0,
        rejected: 1,
    }
}

// ---------------------------------------------------------------------------
// G-B1 — round-trip
// ---------------------------------------------------------------------------

#[test]
fn every_variant_round_trips() {
    let entry = every_variant_entry();
    let bytes = entry.encode().expect("encode");
    assert_eq!(
        CegisCacheEntry::decode(&bytes),
        Some(entry),
        "the exhaustive-variant entry must survive a round trip"
    );
}

#[test]
fn generated_corpus_round_trips() {
    let entries = corpus(512);
    assert_eq!(entries.len(), 512);
    for (i, entry) in entries.iter().enumerate() {
        let bytes = entry.encode().expect("encode");
        assert_eq!(
            CegisCacheEntry::decode(&bytes).as_ref(),
            Some(entry),
            "corpus entry {i} failed to round-trip"
        );
    }
}

#[test]
fn the_empty_entry_round_trips() {
    let entry = CegisCacheEntry::empty();
    let bytes = entry.encode().expect("encode");
    assert_eq!(CegisCacheEntry::decode(&bytes), Some(entry));
}

#[test]
fn encoding_is_deterministic() {
    // The cache key is content-derived and the value is compared by nobody, but
    // a nondeterministic encoder would make two hosts disagree about a blob
    // that means the same thing, and would make any future byte-level gate
    // untestable.
    for entry in corpus(64) {
        let a = entry.encode().expect("encode");
        let b = entry.encode().expect("encode");
        assert_eq!(a, b);
    }
}

#[test]
fn a_real_machinst_projection_round_trips() {
    // Guards the projection seam as well as the codec: `MachInstBlob` is built
    // from a real `MachInst` here, the way the pass builds it.
    let inst = MachInst::new(
        AArch64Opcode::Movz,
        vec![
            MachOperand::VReg(VReg::new(7, RegClass::Gpr32)),
            MachOperand::Imm(0),
            MachOperand::PReg(PReg::new(3)),
            MachOperand::Special(SpecialReg::XZR),
            MachOperand::Symbol("_main".to_string()),
        ],
    );
    let entry = CegisCacheEntry {
        version: CegisCacheEntry::VERSION,
        completion: CegisSearchCompletion::Complete,
        proven_rewrites: vec![ProvenRewrite {
            inst_index: 3,
            proof_hash: 0xDEAD_BEEF,
            iterations: 1,
            window_len: 1,
            replacement: vec![blob_of(&inst)],
            layer: RewriteLayer::A,
        }],
        attempted: 10,
        verified: 1,
        rejected: 9,
    };
    let bytes = entry.encode().expect("encode");
    assert_eq!(CegisCacheEntry::decode(&bytes), Some(entry));
}

/// `MachInstBlob::from_inst` is private to the pass; rebuild the same
/// projection here so this test does not depend on visibility changes.
fn blob_of(inst: &MachInst) -> MachInstBlob {
    MachInstBlob {
        opcode: format!("{:?}", inst.opcode),
        operands: inst
            .operands
            .iter()
            .map(|operand| match operand {
                MachOperand::VReg(v) => MachOperandBlob::VReg {
                    id: v.id,
                    class: match v.class {
                        RegClass::Gpr64 => RegClassBlob::Gpr64,
                        RegClass::Gpr32 => RegClassBlob::Gpr32,
                        RegClass::Fpr128 => RegClassBlob::Fpr128,
                        RegClass::Fpr64 => RegClassBlob::Fpr64,
                        RegClass::Fpr32 => RegClassBlob::Fpr32,
                        RegClass::Fpr16 => RegClassBlob::Fpr16,
                        RegClass::Fpr8 => RegClassBlob::Fpr8,
                        RegClass::System => RegClassBlob::System,
                    },
                },
                MachOperand::PReg(p) => MachOperandBlob::PReg {
                    encoding: p.encoding(),
                },
                MachOperand::Imm(v) => MachOperandBlob::Imm(*v),
                MachOperand::Special(SpecialReg::SP) => {
                    MachOperandBlob::Special(SpecialRegBlob::SP)
                }
                MachOperand::Special(SpecialReg::XZR) => {
                    MachOperandBlob::Special(SpecialRegBlob::XZR)
                }
                MachOperand::Special(SpecialReg::WZR) => {
                    MachOperandBlob::Special(SpecialRegBlob::WZR)
                }
                MachOperand::Symbol(s) => MachOperandBlob::Symbol(s.clone()),
                MachOperand::ExactModuleSymbol(s) => MachOperandBlob::ExactModuleSymbol(s.clone()),
                other => panic!("extend blob_of for {other:?}"),
            })
            .collect(),
    }
}

// ---------------------------------------------------------------------------
// G-B2 — differential against the incumbent, while both exist
// ---------------------------------------------------------------------------

#[test]
fn the_in_tree_codec_round_trips_exactly_what_messagepack_round_trips() {
    // THE ACCEPTANCE GATE. Semantic equality, not byte equality: the two wire
    // formats are deliberately different, which is why VERSION moved 5 -> 6.
    let entries = corpus(512);
    for (i, entry) in entries.iter().enumerate() {
        let mp_bytes = incumbent::to_vec(entry).expect("incumbent encode");
        let mp_back: CegisCacheEntry = incumbent::from_slice(&mp_bytes).expect("incumbent decode");
        assert_eq!(&mp_back, entry, "incumbent failed to round-trip entry {i}");

        let ours = entry.encode().expect("encode");
        let ours_back = CegisCacheEntry::decode(&ours).expect("decode");

        assert_eq!(
            ours_back, mp_back,
            "codec and incumbent disagree on entry {i}"
        );
        assert_ne!(
            ours, mp_bytes,
            "entry {i}: the two formats are supposed to produce different bytes"
        );
    }
}

#[test]
fn the_exhaustive_variant_entry_agrees_with_the_incumbent() {
    let entry = every_variant_entry();
    let mp_back: CegisCacheEntry =
        incumbent::from_slice(&incumbent::to_vec(&entry).expect("mp encode")).expect("mp decode");
    let ours_back = CegisCacheEntry::decode(&entry.encode().expect("encode")).expect("decode");
    assert_eq!(ours_back, mp_back);
    assert_eq!(ours_back, entry);
}

#[test]
fn neither_format_accepts_the_others_bytes() {
    // Cross-rejection is what makes the version bump safe: the shared on-disk
    // cache root can hold blobs written by either build.
    for entry in corpus(64) {
        let ours = entry.encode().expect("encode");
        let theirs = incumbent::to_vec(&entry).expect("incumbent encode");

        assert_eq!(
            CegisCacheEntry::decode(&theirs),
            None,
            "a MessagePack blob must be a miss, never a hit"
        );
        assert!(
            incumbent::from_slice::<CegisCacheEntry>(&ours).is_err(),
            "MessagePack must not find a plausible entry in our bytes"
        );
    }
}

#[test]
fn the_incumbent_ignores_trailing_bytes_and_we_do_not() {
    // A stated deviation, measured rather than assumed. Ours is the stricter
    // direction, which is the safe one for a read that carries proof authority.
    let entry = CegisCacheEntry::empty();

    let mut ours = entry.encode().expect("encode");
    ours.push(0);
    assert_eq!(
        CegisCacheEntry::decode(&ours),
        None,
        "trailing bytes must be rejected"
    );

    let mut theirs = incumbent::to_vec(&entry).expect("incumbent encode");
    theirs.push(0);
    let incumbent_verdict = incumbent::from_slice::<CegisCacheEntry>(&theirs);
    assert!(
        incumbent_verdict.is_ok(),
        "documented deviation: rmp-serde was expected to ignore trailing bytes, \
         but it returned {incumbent_verdict:?}. Update the module docs."
    );
}

// ---------------------------------------------------------------------------
// G-B3 — the version gate
// ---------------------------------------------------------------------------

#[test]
fn a_real_v5_messagepack_blob_is_a_miss() {
    // The actual upgrade scenario: a v5 entry written by the previous build,
    // sitting in the host-shared cache root. It must be a MISS — not a panic,
    // and above all not a hit that replays rewrites at v5 indices.
    #[derive(serde::Serialize)]
    struct V5Entry {
        version: u32,
        proven_rewrites: Vec<ProvenRewrite>,
        attempted: u64,
        verified: u64,
        rejected: u64,
    }
    let v5 = V5Entry {
        version: 5,
        proven_rewrites: vec![ProvenRewrite {
            inst_index: 3,
            proof_hash: 0xDEAD_BEEF,
            iterations: 1,
            window_len: 1,
            replacement: vec![MachInstBlob {
                opcode: "Movz".to_string(),
                operands: vec![MachOperandBlob::Imm(0)],
            }],
            layer: RewriteLayer::A,
        }],
        attempted: 10,
        verified: 1,
        rejected: 9,
    };
    let bytes = incumbent::to_vec(&v5).expect("v5 encode");
    assert_eq!(CegisCacheEntry::decode(&bytes), None);
    // The codec docs claim a v5 blob is caught on the magic because it starts
    // with a MessagePack 5-element fixarray header. Measure the claim rather
    // than repeating it: 0x90 | 5.
    assert_eq!(
        bytes[0], 0x95,
        "a v5 entry no longer starts with a fixarray header; the \
         'caught on the magic' reasoning in cegis_cache_codec's docs needs rechecking"
    );
}

#[test]
fn a_current_format_blob_carrying_the_wrong_version_is_a_miss() {
    let entry = CegisCacheEntry {
        version: CegisCacheEntry::VERSION + 1,
        completion: CegisSearchCompletion::Complete,
        ..Default::default()
    };
    let bytes = entry.encode().expect("encode");
    assert_eq!(CegisCacheEntry::decode(&bytes), None);
}

#[test]
fn the_version_is_seven() {
    // Pins the bump itself. If someone reverts the codec without reverting the
    // version, or vice versa, exactly one of the two lands and this fires.
    assert_eq!(CegisCacheEntry::VERSION, 7);
}

#[test]
fn incomplete_entries_cannot_be_published_or_replayed() {
    let complete_bytes = CegisCacheEntry::empty().encode().expect("complete encode");
    // magic (4) + version (4) puts the completion tag at byte 8.
    assert_eq!(
        complete_bytes[8], 1,
        "completion tag moved; update this test"
    );

    for (completion, wire_tag) in [
        (CegisSearchCompletion::NotCompleted, 0),
        (CegisSearchCompletion::DeadlineExceeded, 2),
        (CegisSearchCompletion::QueryIncomplete, 3),
        (CegisSearchCompletion::VerifierError, 4),
        (CegisSearchCompletion::VerifierPanicked, 5),
    ] {
        let mut entry = CegisCacheEntry::empty();
        entry.completion = completion;
        assert_eq!(
            entry.encode(),
            Err(CacheCodecError::IncompleteSearch { completion }),
            "{completion:?} must fail closed at publication"
        );

        // Model bytes written by a buggy/older internal producer. Even a
        // structurally valid current-format entry must miss unless it records
        // a complete search.
        let mut incomplete_bytes = complete_bytes.clone();
        incomplete_bytes[8] = wire_tag;
        assert_eq!(
            CegisCacheEntry::decode(&incomplete_bytes),
            None,
            "{completion:?} must fail closed at replay"
        );
    }
}

#[test]
fn an_unknown_completion_tag_is_a_miss() {
    let mut bytes = CegisCacheEntry::empty().encode().expect("encode");
    assert_eq!(bytes[8], 1, "completion tag moved; update this test");
    bytes[8] = u8::MAX;
    assert_eq!(CegisCacheEntry::decode(&bytes), None);
}

// ---------------------------------------------------------------------------
// Adversarial input — a miss, never a panic
// ---------------------------------------------------------------------------

#[test]
fn every_truncation_of_a_valid_blob_is_a_miss() {
    let bytes = every_variant_entry().encode().expect("encode");
    assert!(bytes.len() > 64);
    for cut in 0..bytes.len() {
        assert_eq!(
            CegisCacheEntry::decode(&bytes[..cut]),
            None,
            "truncation to {cut} bytes decoded as a hit"
        );
    }
}

#[test]
fn every_single_byte_corruption_is_a_miss_or_an_exact_round_trip() {
    // A flipped byte may land in a value field, where any value is legal — that
    // is fine, because the cache key already binds the entry to a function. The
    // property that matters is that no corruption produces a panic, an
    // allocation blow-up, or a decode that disagrees with a re-encode.
    let original = every_variant_entry().encode().expect("encode");
    for i in 0..original.len() {
        for delta in [1u8, 0x80, 0xFF] {
            let mut bytes = original.clone();
            bytes[i] = bytes[i].wrapping_add(delta);
            if let Some(decoded) = CegisCacheEntry::decode(&bytes) {
                assert_eq!(
                    decoded.encode().expect("re-encode"),
                    bytes,
                    "byte {i} (+{delta}): decode accepted bytes it does not reproduce"
                );
            }
        }
    }
}

#[test]
fn a_corrupt_length_prefix_is_a_miss() {
    // A 4-billion-element count in a 32-byte buffer. It must fail on the short
    // read.
    //
    // READ THIS BEFORE TRUSTING THE NAME. This test does NOT prove the
    // companion property that `Reader::seq` refuses to `reserve` from an
    // untrusted count. Measured 2026-08-23: mutating `Vec::new()` to
    // `Vec::with_capacity(n as usize)` — a ~240 GB request for this element
    // type — left all 18 tests in this file green, because macOS reserves that
    // address space lazily. The no-reserve rule is therefore enforced by
    // review, not by this suite. If you are tempted to "simplify" it back,
    // nothing here will stop you.
    let mut bytes = Vec::new();
    bytes.extend_from_slice(b"TCGC");
    bytes.extend_from_slice(&CegisCacheEntry::VERSION.to_le_bytes());
    bytes.push(1); // completion = Complete
    bytes.extend_from_slice(&0u64.to_le_bytes()); // attempted
    bytes.extend_from_slice(&0u64.to_le_bytes()); // verified
    bytes.extend_from_slice(&0u64.to_le_bytes()); // rejected
    bytes.extend_from_slice(&u32::MAX.to_le_bytes()); // proven_rewrites count
    assert_eq!(CegisCacheEntry::decode(&bytes), None);
}

#[test]
fn foreign_bytes_are_a_miss() {
    for blob in [
        &b""[..],
        &b"TCG"[..],
        &b"TCGD"[..],
        &b"\x95\x05\x90\x00\x00\x00"[..], // a MessagePack 5-array
        &b"{\"version\":7}"[..],
        &[0xFFu8; 256][..],
        &[0x00u8; 256][..],
    ] {
        assert_eq!(
            CegisCacheEntry::decode(blob),
            None,
            "foreign blob {blob:?} decoded as a hit"
        );
    }
}

#[test]
fn the_magic_is_load_bearing_on_its_own() {
    // Isolates the magic from the version gate. Measured 2026-08-23: deleting
    // the magic check alone did NOT fail `foreign_bytes_are_a_miss`,
    // `a_real_v5_messagepack_blob_is_a_miss` or
    // `neither_format_accepts_the_others_bytes` — in every one of those the
    // *version* gate happened to catch the blob first, because bytes 4..8 of a
    // MessagePack entry are not the little-endian VERSION. So those three do
    // not witness the magic at all.
    //
    // This one does: a body that is byte-for-byte a valid entry, with only the
    // four magic bytes replaced. The version gate cannot see it.
    let good = every_variant_entry().encode().expect("encode");
    assert_eq!(&good[..4], b"TCGC", "magic moved; update this test");
    let mut wrong_magic = good.clone();
    wrong_magic[..4].copy_from_slice(b"XXXX");
    assert_eq!(
        CegisCacheEntry::decode(&wrong_magic),
        None,
        "a correctly-versioned body under foreign magic must be a miss"
    );
    // Control: the same bytes with the magic restored are a hit, so the test
    // above is not passing for some unrelated reason.
    assert!(CegisCacheEntry::decode(&good).is_some());
}

#[test]
fn an_unknown_operand_tag_is_a_miss() {
    // The tag byte is the one place where a future format could be mistaken for
    // this one. Rebuild a valid blob and push the operand tag past the highest
    // known value.
    let entry = CegisCacheEntry {
        version: CegisCacheEntry::VERSION,
        completion: CegisSearchCompletion::Complete,
        proven_rewrites: vec![ProvenRewrite {
            inst_index: 0,
            proof_hash: 0,
            iterations: 0,
            window_len: 0,
            replacement: vec![MachInstBlob {
                opcode: "Movz".to_string(),
                operands: vec![MachOperandBlob::Imm(0)],
            }],
            layer: RewriteLayer::A,
        }],
        attempted: 0,
        verified: 0,
        rejected: 0,
    };
    let good = entry.encode().expect("encode");
    // `Imm` is tag 2 and is the only operand present; locate it as the byte
    // immediately preceding the 8-byte immediate at the end of the buffer.
    let tag_pos = good.len() - 9;
    assert_eq!(good[tag_pos], 2, "operand tag moved; update this test");
    let mut bad = good;
    bad[tag_pos] = 200;
    assert_eq!(CegisCacheEntry::decode(&bad), None);
}

#[test]
fn a_non_utf8_symbol_is_a_miss() {
    let entry = CegisCacheEntry {
        version: CegisCacheEntry::VERSION,
        completion: CegisSearchCompletion::Complete,
        proven_rewrites: vec![ProvenRewrite {
            inst_index: 0,
            proof_hash: 0,
            iterations: 0,
            window_len: 0,
            replacement: vec![MachInstBlob {
                opcode: "Movz".to_string(),
                operands: vec![MachOperandBlob::Symbol("AAAA".to_string())],
            }],
            layer: RewriteLayer::A,
        }],
        attempted: 0,
        verified: 0,
        rejected: 0,
    };
    let mut bytes = entry.encode().expect("encode");
    // The symbol payload is the last 4 bytes.
    let n = bytes.len();
    bytes[n - 1] = 0xFF;
    assert_eq!(CegisCacheEntry::decode(&bytes), None);
}
