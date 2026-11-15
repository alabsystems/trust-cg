// trust-cg-verify/tests/x86_encoding_gate.rs - the MOV-immediate family against the LIVE encoder
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The live half of the x86-64 MOV-immediate encoding family.
//!
//! `src/x86_encoding_proofs.rs` holds the independent SDM-derived decoder, the
//! register-write denotation, the typed obligation, the negative-control
//! battery and the coverage-gate credit hook — all of which take BYTES and none
//! of which can call the encoder (`trust-cg-codegen` depends on this crate, so
//! it can only be a DEV-dependency here). This file supplies the bytes by
//! running the REAL x86-64 encoder.
//!
//! What happens here that cannot happen inside the library:
//!
//!   1. the captured corpus the credit hook stands on is RE-ENCODED through the
//!      live encoder and asserted byte-identical, so the gate row can never rest
//!      on a stale capture;
//!   2. the obligation and its whole negative-control battery are run over LIVE
//!      bytes, and every control must be refuted FOR ITS STATED REASON CLASS;
//!   3. the SDM register tables are anchored against `trust-cg-ir`'s `hw_enc`,
//!      the table the encoder really uses;
//!   4. a stratified sweep puts every register at every width through the live
//!      encoder across the alias threshold and the sign edges.
//!
//! A control that survives, or refutes for the wrong reason, means the
//! obligation is not faithful: fix the obligation, never the control.

use std::collections::{BTreeMap, BTreeSet};

use trust_cg_codegen::x86_64::decode_check::{X86IntentInst, check_one_for_test};
use trust_cg_codegen::x86_64::{X86Encoder, X86InstOperands};
use trust_cg_ir::{X86Opcode, X86PReg};
use trust_cg_verify::x86_encoding_proofs as enc;

use enc::{
    EMITTED_X86_MOV_IMMEDIATES, MovImmForm, MovImmFormClass, MovImmRefutation, RefutationClass,
    RegWrite, X86_MOV_IMM_DEFERRALS,
};

// ---------------------------------------------------------------------------
// Live-encoder plumbing
// ---------------------------------------------------------------------------

/// The `trust-cg-ir` physical register whose DISPLAY NAME is `name`. The scan is
/// over `trust-cg-ir`'s own name table — never over `hw_enc`.
fn preg_named(name: &str) -> X86PReg {
    (0u16..64)
        .map(X86PReg::new)
        .find(|r| r.to_string() == name)
        .unwrap_or_else(|| panic!("trust-cg-ir has no GPR named `{name}`"))
}

/// The bytes the REAL encoder emits for `MovRI reg, imm`.
fn live_encode(reg: X86PReg, imm: i64) -> Vec<u8> {
    let mut encoder = X86Encoder::new();
    encoder
        .encode_instruction(X86Opcode::MovRI, &X86InstOperands::ri(reg, imm))
        .unwrap_or_else(|e| panic!("live encoder refused MovRI {reg},{imm:#x}: {e:?}"));
    encoder.finish()
}

fn live_encode_named(name: &str, imm: i64) -> Vec<u8> {
    live_encode(preg_named(name), imm)
}

// ---------------------------------------------------------------------------
// 1. Freshness: the capture is what the live encoder emits today
// ---------------------------------------------------------------------------

/// FRESHNESS. The credit hook runs over a CAPTURE, because `coverage_gate.rs`
/// cannot run the encoder. Every captured entry is re-encoded through the live
/// encoder here and must be byte-identical, so an encoder change that alters
/// these bytes turns THIS test red instead of leaving a green row standing on a
/// fiction.
#[test]
fn corpus_is_what_the_live_encoder_emits_today() {
    let mut checked = 0usize;
    let mut seen = BTreeSet::new();
    for &(name, imm, captured) in EMITTED_X86_MOV_IMMEDIATES {
        assert!(
            seen.insert((name, imm)),
            "corpus lists MOV {name},{imm:#x} twice"
        );
        let live = live_encode_named(name, imm);
        assert_eq!(
            live.as_slice(),
            captured,
            "MOV {name},{imm:#x}: the live encoder emits {live:02x?} but the captured corpus says \
             {captured:02x?} — the corpus has rotted, or the encoder changed"
        );
        checked += 1;
    }
    assert_eq!(checked, EMITTED_X86_MOV_IMMEDIATES.len());
    assert!(checked >= 150, "corpus shrank to {checked} entries");
    eprintln!(
        "corpus_is_what_the_live_encoder_emits_today: {checked}/{} captured encodings re-derived \
         from the LIVE encoder, all byte-identical",
        EMITTED_X86_MOV_IMMEDIATES.len()
    );
}

/// NOT AN INDEPENDENT WITNESS. These eleven anchors are the same vectors as
/// `encode.rs`'s own MovRI unit tests (`test_movri_*`, `test_movabs_*`: RAX 42,
/// RAX 0x8000_0001, R8 42, R8 0x1_0000_0000, RAX -1, RAX 0x1234_5678_9ABC_DEF0,
/// AL 7, R8B 7, SIL 7, AX 0x1234, R14W 0x1234). An earlier doc comment called
/// them "typed by hand from the SDM, not copied from the capture printer".
/// That claimed independence they do not have. All this test pins is that the
/// capture contains those exact entries and that each one holds. The
/// independence of the credit rests on the SDM-derived decoder and its controls,
/// not on these vectors.
#[test]
fn encoder_unit_test_vectors_appear_verbatim_in_the_corpus() {
    let anchors: &[(&str, i64, &[u8])] = &[
        ("rax", 42, &[0xB8, 0x2A, 0x00, 0x00, 0x00]),
        ("rax", 0x8000_0001, &[0xB8, 0x01, 0x00, 0x00, 0x80]),
        ("r8", 42, &[0x41, 0xB8, 0x2A, 0x00, 0x00, 0x00]),
        (
            "r8",
            0x1_0000_0000,
            &[0x49, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00],
        ),
        (
            "rax",
            -1,
            &[0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
        ),
        (
            "rax",
            0x1234_5678_9ABC_DEF0,
            &[0x48, 0xB8, 0xF0, 0xDE, 0xBC, 0x9A, 0x78, 0x56, 0x34, 0x12],
        ),
        ("al", 7, &[0xB0, 0x07]),
        ("r8b", 7, &[0x41, 0xB0, 0x07]),
        ("sil", 7, &[0x40, 0xB6, 0x07]),
        ("ax", 0x1234, &[0x66, 0xB8, 0x34, 0x12]),
        ("r14w", 0x1234, &[0x66, 0x41, 0xBE, 0x34, 0x12]),
    ];
    for &(name, imm, bytes) in anchors {
        assert!(
            EMITTED_X86_MOV_IMMEDIATES
                .iter()
                .any(|&(n, i, b)| n == name && i == imm && b == bytes),
            "encoder unit-test vector MOV {name},{imm:#x} = {bytes:02x?} is not in the corpus verbatim"
        );
        enc::mov_imm_check(name, imm, bytes)
            .unwrap_or_else(|r| panic!("anchor MOV {name},{imm:#x} = {bytes:02x?} refuted: {r}"));
    }
}

// ---------------------------------------------------------------------------
// 2. The obligation over LIVE bytes
// ---------------------------------------------------------------------------

/// The obligation over LIVE bytes (not the capture): every corpus intent is
/// encoded by the real encoder and the emitted bytes must denote the intended
/// 64-bit register write.
#[test]
fn live_mov_immediates_denote_their_intent() {
    let mut proven = 0usize;
    let mut truncating = 0usize;
    let mut classes: BTreeMap<MovImmFormClass, usize> = BTreeMap::new();
    for &(name, imm, _) in EMITTED_X86_MOV_IMMEDIATES {
        let live = live_encode_named(name, imm);
        let ob = enc::mov_imm_obligation(name, imm, &live);
        let holds = match &ob.outcome {
            Ok(h) => *h,
            Err(r) => panic!("REFUTED on live bytes — {}: {r}", ob.name),
        };
        let bits = enc::sdm_reg(name).expect("corpus names a GPR").bits;
        let class = enc::form_class(bits, &holds.decoded)
            .unwrap_or_else(|| panic!("{}: not a form the encoder is known to emit", ob.name));
        *classes.entry(class).or_default() += 1;
        truncating += usize::from(holds.truncating_intent);
        proven += 1;
    }
    for required in enc::REQUIRED_FORM_CLASSES {
        assert!(
            classes.contains_key(&required),
            "no live encoding exercised the {required:?} form class"
        );
    }
    assert_eq!(proven, EMITTED_X86_MOV_IMMEDIATES.len());
    // The corpus deliberately carries out-of-width intents (0x1_0000_0001 into a
    // 32-bit register, 0x1_2345 into a 16-bit one, 0x1FF into an 8-bit one) so
    // the `truncating` report is exercised rather than dead.
    assert!(truncating >= 6, "only {truncating} truncating intents");
    eprintln!(
        "live_mov_immediates_denote_their_intent: {proven} proven / 0 refuted; {truncating} \
         truncating intents (counted, not refuted); form classes: {classes:?}"
    );
}

// ---------------------------------------------------------------------------
// 3. NEGATIVE CONTROLS over LIVE bytes — each must refute for its stated reason
// ---------------------------------------------------------------------------

/// ANTI-TAUTOLOGY, against LIVE bytes. Every control — machine side moved
/// (M1..M10) and source side moved (S1..S4) — must be REFUTED, and refuted for
/// the reason class it states. A control that is merely "rejected somehow" does
/// not count: M3 in particular must refute on VALUE, which it can only do
/// because the decoder genuinely models `C7 /0` and the 32-bit zero-extension
/// rule.
#[test]
fn live_mov_immediate_mutants_are_refuted() {
    let mut by_label: BTreeMap<&str, usize> = BTreeMap::new();
    let mut by_class: BTreeMap<String, usize> = BTreeMap::new();
    let mut failures = Vec::new();
    let mut total = 0usize;
    for &(name, imm, _) in EMITTED_X86_MOV_IMMEDIATES {
        let live = live_encode_named(name, imm);
        let battery = enc::mov_imm_mutants(name, imm, &live);
        assert!(
            !battery.is_empty(),
            "MOV {name},{imm:#x}: no negative controls were built"
        );
        for m in battery {
            total += 1;
            *by_label.entry(m.label).or_default() += 1;
            match enc::mov_imm_check(&m.dst_name, m.imm, &m.bytes) {
                Ok(_) => failures.push(format!(
                    "SURVIVED `{}`: MOV {},{:#x} vs {:02x?} (original MOV {name},{imm:#x} = \
                     {live:02x?})",
                    m.label, m.dst_name, m.imm, m.bytes
                )),
                Err(r) if r.class() != m.expect => failures.push(format!(
                    "WRONG REASON `{}`: MOV {},{:#x} vs {:02x?} must refute as {:?}, refuted as \
                     {:?} ({r})",
                    m.label,
                    m.dst_name,
                    m.imm,
                    m.bytes,
                    m.expect,
                    r.class()
                )),
                Err(r) => *by_class.entry(format!("{:?}", r.class())).or_default() += 1,
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {total} negative control(s) FAILED — the obligation is not faithful:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    for &label in enc::REQUIRED_MUTANT_LABELS {
        assert!(
            by_label.get(label).copied().unwrap_or(0) > 0,
            "negative control `{label}` never fired over the live corpus"
        );
    }
    eprintln!(
        "live_mov_immediate_mutants_are_refuted: {total} controls over LIVE bytes, all REFUTED \
         for their stated reason class"
    );
    for (label, n) in &by_label {
        eprintln!("  {n:>5}  {label}");
    }
    eprintln!("  by refutation class: {by_class:?}");
}

/// THE SINGLE MOST IMPORTANT ASSERTION IN THE LANE, spelled out on its own so it
/// cannot hide inside a battery: the sign-/zero-extension hazard, in BOTH
/// directions, refutes on VALUE with the exact values the SDM predicts.
#[test]
fn sign_versus_zero_extension_refutes_on_value_in_both_directions() {
    // (a) MOV RAX,-1 squeezed into the zero-extending 5-byte form. The live
    // encoder emits the 10-byte movabs; the mis-aliased bytes are its first
    // opcode byte and low immediate half.
    let live = live_encode_named("rax", -1);
    assert_eq!(
        live,
        [0x48, 0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]
    );
    let mis_aliased = [live[1], live[2], live[3], live[4], live[5]];
    assert_eq!(
        enc::mov_imm_check("rax", -1, &mis_aliased),
        Err(MovImmRefutation::Value {
            intended: 0xFFFF_FFFF_FFFF_FFFF,
            decoded: 0x0000_0000_FFFF_FFFF,
        })
    );
    // (b) MOV RAX,0x80000000 moved to the SIGN-extending REX.W C7 /0 id. The
    // live encoder emits the zero-extending alias.
    let live = live_encode_named("rax", 0x8000_0000);
    assert_eq!(live, [0xB8, 0x00, 0x00, 0x00, 0x80]);
    let sign_extending = [0x48, 0xC7, 0xC0, live[1], live[2], live[3], live[4]];
    assert_eq!(
        enc::mov_imm_check("rax", 0x8000_0000, &sign_extending),
        Err(MovImmRefutation::Value {
            intended: 0x0000_0000_8000_0000,
            decoded: 0xFFFF_FFFF_8000_0000,
        })
    );
    // The SAME sign-extending form is CORRECT for a negative intent — so the
    // refutation above is about the value, not about the opcode being unknown.
    enc::mov_imm_check("rax", i64::from(i32::MIN), &sign_extending)
        .expect("REX.W C7 /0 0x80000000 IS mov rax,-0x80000000");
    // And with bit 31 clear the two extensions agree, so both forms HOLD.
    enc::mov_imm_check(
        "rax",
        0x7FFF_FFFF,
        &[0x48, 0xC7, 0xC0, 0xFF, 0xFF, 0xFF, 0x7F],
    )
    .expect("sign- and zero-extension agree when bit 31 is clear");
    enc::mov_imm_check("rax", 0x7FFF_FFFF, &live_encode_named("rax", 0x7FFF_FFFF))
        .expect("the live alias holds");
}

/// DELIBERATELY NOT A CONTROL. `mov eax,42` IS `mov rax,42`: the encoder's alias
/// re-targets a small 64-bit intent to the 32-bit register, and the two intents
/// denote the same write. Re-claiming one for the other's bytes must HOLD — the
/// comparison is on DENOTATION, not on spelling. The pair stops holding exactly
/// when the immediate's upper 32 bits are non-zero.
#[test]
fn width_reclaims_that_denote_the_same_write_hold() {
    let mut held = 0usize;
    for &(name, imm, _) in EMITTED_X86_MOV_IMMEDIATES {
        let reg = enc::sdm_reg(name).expect("GPR");
        let other_bits = match reg.bits {
            64 => 32,
            32 => 64,
            _ => continue,
        };
        let other = enc::sdm_name(reg.root, other_bits).expect("sibling width");
        let live = live_encode_named(name, imm);
        let reclaimed = enc::mov_imm_check(other, imm, &live);
        if (imm as u64) >> 32 == 0 {
            reclaimed.unwrap_or_else(|r| {
                panic!("MOV {other},{imm:#x} denotes the same write as MOV {name},{imm:#x}: {r}")
            });
            held += 1;
        } else {
            assert_eq!(
                reclaimed.map_err(|r| r.class()).err(),
                Some(RefutationClass::Value),
                "MOV {other},{imm:#x} vs the bytes of MOV {name},{imm:#x}"
            );
        }
    }
    assert!(
        held >= 20,
        "only {held} same-denotation re-claims exercised"
    );
}

// ---------------------------------------------------------------------------
// 4. The decoder was NOT derived from encode.rs
// ---------------------------------------------------------------------------

/// Encodings the live encoder NEVER emits, typed from the SDM. An inversion of
/// `encode.rs`'s four-way ladder knows nothing of group 11, of AH..BH or of the
/// sign-extending imm32, so it could satisfy none of these.
#[test]
fn sdm_hand_vectors_decode() {
    for &(why, name, imm, bytes) in enc::SDM_HAND_VECTORS_HOLD {
        let holds = enc::mov_imm_check(name, imm, bytes)
            .unwrap_or_else(|r| panic!("`{why}`: MOV {name},{imm:#x} = {bytes:02x?} refuted: {r}"));
        // None of these is something the live encoder produces for that intent
        // (where the intent is expressible at all: trust-cg-ir has no AH..BH).
        if !enc::sdm_reg(name).expect("GPR").high_byte {
            assert_ne!(
                live_encode_named(name, imm).as_slice(),
                bytes,
                "`{why}` is supposed to be a form the encoder never emits"
            );
        }
        assert_eq!(holds.decoded.len_consumed, bytes.len());
    }
    // Spot-check the decode itself, field by field, against the manual.
    let d = enc::sdm_decode_mov_imm(&[0x48, 0xC7, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF]).expect("decodes");
    assert_eq!(d.form, MovImmForm::C7Slash0);
    assert_eq!((d.operand_bits, d.imm_len), (64, 4));
    assert_eq!(d.extension, enc::ImmExtension::SignExtend32To64);
    assert_eq!(d.reg_write().value, u64::MAX);
    let d = enc::sdm_decode_mov_imm(&[0xB4, 0x07]).expect("decodes");
    assert!(d.high_byte);
    assert_eq!(d.reg_name(), "ah");
    assert_eq!(
        d.reg_write(),
        RegWrite {
            root: 0,
            written_mask: 0xFF00,
            value: 0x0700,
        }
    );
    // The same opcode byte under a bare REX is SPL, a different ROOT register.
    let d = enc::sdm_decode_mov_imm(&[0x40, 0xB4, 0x07]).expect("decodes");
    assert!(!d.high_byte);
    assert_eq!(d.reg_name(), "spl");
    assert_eq!(d.reg_write().root, 4);
    // 66h and REX.W together: REX.W takes precedence (SDM Vol 2A §2.2.1.2), so
    // the instruction is a 10-byte movabs — and then the 66h is not load-bearing.
    let both = [0x66, 0x48, 0xB8, 1, 2, 3, 4, 5, 6, 7, 8];
    let d = enc::sdm_decode_mov_imm(&both).expect("decodes");
    assert_eq!((d.operand_bits, d.imm_len, d.len_consumed), (64, 8, 11));
    assert_eq!(
        enc::mov_imm_check("rax", 0x0807_0605_0403_0201, &both).map_err(|r| r.class()),
        Err(RefutationClass::NonCanonical)
    );

    for &(why, name, imm, bytes, expect) in enc::SDM_HAND_VECTORS_REFUTE {
        match enc::mov_imm_check(name, imm, bytes) {
            Ok(_) => panic!("`{why}`: MOV {name},{imm:#x} = {bytes:02x?} must REFUTE but held"),
            Err(r) => assert_eq!(
                r.class(),
                expect,
                "`{why}`: refuted for the wrong reason ({r})"
            ),
        }
    }
    eprintln!(
        "sdm_hand_vectors_decode: {} never-emitted SDM forms HOLD, {} hand-written wrong pairings \
         REFUTE for their stated reason",
        enc::SDM_HAND_VECTORS_HOLD.len(),
        enc::SDM_HAND_VECTORS_REFUTE.len()
    );
}

/// The SDM tables in `x86_encoding_proofs` are an INDEPENDENT transcription.
/// This pins them against the table the encoder really uses — `hw_enc` — for
/// all 64 GPR physical registers, entering ours by NAME.
#[test]
fn sdm_register_names_anchor_trust_cg_ir() {
    let mut checked = 0usize;
    for encoding in 0u16..64 {
        let reg = X86PReg::new(encoding);
        let sdm = enc::sdm_reg(&reg.to_string())
            .unwrap_or_else(|| panic!("the SDM tables do not know `{reg}`"));
        assert_eq!(
            sdm.root,
            reg.hw_enc(),
            "`{reg}`: SDM number {} vs trust-cg-ir hw_enc {}",
            sdm.root,
            reg.hw_enc()
        );
        let want_bits = if reg.is_gpr64() {
            64
        } else if reg.is_gpr32() {
            32
        } else if reg.is_gpr16() {
            16
        } else {
            assert!(reg.is_gpr8(), "`{reg}` is not a GPR");
            8
        };
        assert_eq!(sdm.bits, want_bits, "`{reg}` width class");
        assert!(
            !sdm.high_byte,
            "trust-cg-ir cannot name a high-byte register"
        );
        checked += 1;
    }
    assert_eq!(checked, 64);
    // Non-GPRs fail closed on the source side.
    for encoding in 64u16..82 {
        assert_eq!(enc::sdm_reg(&X86PReg::new(encoding).to_string()), None);
    }
    assert_eq!(
        enc::mov_imm_check_for_preg(X86PReg::new(64), 0, &[0xB8, 0, 0, 0, 0])
            .map_err(|r| r.class()),
        Err(RefutationClass::UnknownIntentRegister)
    );
}

// ---------------------------------------------------------------------------
// 5. The comparison is an exact decision, and canonicality means what it says
// ---------------------------------------------------------------------------

/// THE LEMMA behind the comparison: two register writes on the same root denote
/// the same `u64 -> u64` function IFF their `(mask, value)` pairs are equal. For
/// every distinct pair a WITNESS prior value is exhibited; for every equal pair
/// the functions agree on a spread of prior values.
#[test]
fn regwrite_equality_is_functional_equality() {
    let masks = [0xFFu64, 0xFF00, 0xFFFF, u64::MAX];
    let raws = [
        0u64,
        1,
        0x7F,
        0x80,
        0xFF,
        0x1234,
        0x8000,
        0xFFFF,
        0x8000_0000,
        0xFFFF_FFFF,
        0x0123_4567_89AB_CDEF,
        u64::MAX,
    ];
    let mut writes = Vec::new();
    for mask in masks {
        for raw in raws {
            let value = if mask == 0xFF00 {
                (raw << 8) & mask
            } else {
                raw & mask
            };
            let w = RegWrite {
                root: 0,
                written_mask: mask,
                value,
            };
            if !writes.contains(&w) {
                writes.push(w);
            }
        }
    }
    let olds = [
        0u64,
        u64::MAX,
        0xAAAA_AAAA_AAAA_AAAA,
        0x5555_5555_5555_5555,
        0x0123_4567_89AB_CDEF,
    ];
    let (mut distinct, mut equal) = (0usize, 0usize);
    for a in &writes {
        for b in &writes {
            match a.distinguishing_old(b) {
                Some(old) => {
                    assert_ne!(a, b);
                    assert_ne!(
                        a.apply(old),
                        b.apply(old),
                        "{a:?} vs {b:?}: witness {old:#x} does not distinguish them"
                    );
                    distinct += 1;
                }
                None => {
                    assert_eq!(a, b, "no witness, so the triples must be equal");
                    for old in olds {
                        assert_eq!(a.apply(old), b.apply(old));
                    }
                    equal += 1;
                }
            }
        }
    }
    assert!(distinct > 1000 && equal == writes.len());
    eprintln!(
        "regwrite_equality_is_functional_equality: {distinct} distinct pairs each with a \
         distinguishing prior value; {equal} equal pairs"
    );
}

/// What the bytes MEAN, by decode and framing alone — deliberately WITHOUT the
/// canonicality rule list, so the property below ties that list to its semantic
/// definition instead of restating it.
fn meaning(bytes: &[u8]) -> Option<RegWrite> {
    let d = enc::sdm_decode_mov_imm(bytes).ok()?;
    (d.len_consumed == bytes.len()).then(|| d.reg_write())
}

/// Every way of deleting one prefix byte or clearing one set REX bit.
fn prefix_reductions(bytes: &[u8]) -> Vec<Vec<u8>> {
    let d = enc::sdm_decode_mov_imm(bytes).expect("decodable");
    let mut out = Vec::new();
    for at in 0..d.opcode_at {
        let mut m = bytes.to_vec();
        m.remove(at);
        out.push(m);
    }
    if let Some(rex) = d.rex {
        let rex_at = d.opcode_at - 1;
        for bit in [0x08u8, 0x04, 0x02, 0x01] {
            if rex & bit != 0 {
                let mut m = bytes.to_vec();
                m[rex_at] = rex & !bit;
                out.push(m);
            }
        }
    }
    out
}

/// CANONICAL means: every prefix byte and every REX bit present is LOAD-BEARING
/// — removing it changes (or destroys) the meaning. The rule list in
/// `canonicality` is checked against that definition in BOTH directions: every
/// live encoding is canonical and every reduction of it changes its meaning;
/// every control the battery expects to refute as `NonCanonical` has a reduction
/// that PRESERVES its meaning.
#[test]
fn canonical_means_every_prefix_is_load_bearing() {
    let (mut reductions, mut padded) = (0usize, 0usize);
    for &(name, imm, _) in EMITTED_X86_MOV_IMMEDIATES {
        let live = live_encode_named(name, imm);
        let original = meaning(&live).expect("live bytes have a meaning");
        let d = enc::sdm_decode_mov_imm(&live).expect("decodable");
        assert_eq!(
            enc::canonicality(&d),
            Ok(()),
            "MOV {name},{imm:#x} = {live:02x?}"
        );
        for reduced in prefix_reductions(&live) {
            assert_ne!(
                meaning(&reduced),
                Some(original),
                "MOV {name},{imm:#x} = {live:02x?}: {reduced:02x?} means the same thing, so a \
                 prefix byte or REX bit was NOT load-bearing yet the encoding passed as canonical"
            );
            reductions += 1;
        }
        for m in enc::mov_imm_mutants(name, imm, &live) {
            if m.expect != RefutationClass::NonCanonical {
                continue;
            }
            let padded_meaning = meaning(&m.bytes).expect("a padded encoding still decodes");
            assert_eq!(
                padded_meaning, original,
                "`{}` is value-neutral padding by construction",
                m.label
            );
            assert!(
                prefix_reductions(&m.bytes)
                    .iter()
                    .any(|r| meaning(r) == Some(padded_meaning)),
                "`{}` = {:02x?} was refuted as NonCanonical, but no single prefix byte or REX \
                 bit can be removed without changing its meaning",
                m.label,
                m.bytes
            );
            padded += 1;
        }
    }
    assert!(reductions > 100 && padded > 300);
    eprintln!(
        "canonical_means_every_prefix_is_load_bearing: {reductions} reductions of live encodings \
         all change the meaning; {padded} padded controls each have a meaning-preserving reduction"
    );
}

// ---------------------------------------------------------------------------
// 6. Stratified live sweep
// ---------------------------------------------------------------------------

fn sweep_values(window: i64) -> Vec<i64> {
    let mut v: Vec<i64> = vec![
        0,
        1,
        -1,
        i64::MIN,
        i64::MAX,
        i64::from(i32::MIN),
        i64::from(i32::MAX),
        i64::from(u32::MAX),
        i64::from(u32::MAX) + 1,
        0x0123_4567_89AB_CDEF,
        0xFEDC_BA98_7654_3210u64 as i64,
    ];
    for k in 0..64 {
        v.push((1u64 << k) as i64);
        v.push(!(1u64 << k) as i64);
    }
    let centers: [i64; 11] = [
        0,
        1 << 7,
        -(1 << 7),
        1 << 8,
        1 << 15,
        -(1 << 15),
        1 << 16,
        1 << 31,
        -(1 << 31),
        1 << 32,
        -(1 << 32),
    ];
    for c in centers {
        for d in -window..=window {
            v.push(c + d);
        }
    }
    v
}

/// STRATIFIED, not exhaustive: all 16 registers at all 4 widths through the
/// LIVE encoder, over the boundary set, a walking one and a walking zero across
/// all 64 bit positions, and contiguous windows around 0, ±2^7, 2^8, ±2^15,
/// 2^16, ±2^31 and ±2^32 — which straddle the zero-extending-alias threshold
/// (`u32::MAX` / `u32::MAX + 1`) and every sign edge. Two registers per width
/// (one legacy, one REX.B) get ±2^12 windows; the rest get ±2^8.
#[test]
fn live_encoder_stratified_sweep() {
    let wide = sweep_values(1 << 12);
    let narrow = sweep_values(1 << 8);
    let wide_regs = ["rax", "r9", "eax", "r9d", "ax", "r14w", "al", "sil", "r9b"];
    let (mut held, mut truncating) = (0u64, 0u64);
    for encoding in 0u16..64 {
        let reg = X86PReg::new(encoding);
        let name = reg.to_string();
        let values = if wide_regs.contains(&name.as_str()) {
            &wide
        } else {
            &narrow
        };
        for &imm in values {
            let live = live_encode(reg, imm);
            match enc::mov_imm_check_for_preg(reg, imm, &live) {
                Ok(h) => {
                    held += 1;
                    truncating += u64::from(h.truncating_intent);
                }
                Err(r) => panic!("MOV {name},{imm:#x} = {live:02x?} REFUTED on live bytes: {r}"),
            }
        }
    }
    assert!(held > 1_000_000, "sweep shrank to {held}");
    eprintln!(
        "live_encoder_stratified_sweep: {held} live encodings HOLD / 0 refuted ({truncating} \
         truncating intents). STRATIFIED over 64 registers, not exhaustive over i64."
    );
}

// ---------------------------------------------------------------------------
// 7. The credit hook fails closed
// ---------------------------------------------------------------------------

/// The hook the coverage gate calls returns `Ok`, and says what it established.
#[test]
fn credit_hook_discharges_over_the_captured_corpus() {
    let credit = enc::mov_imm_discharges_valid().expect("the MovRI credit hook must discharge");
    assert_eq!(credit.entries, EMITTED_X86_MOV_IMMEDIATES.len());
    assert_eq!(credit.forms_seen, enc::REQUIRED_FORM_CLASSES.len());
    assert_eq!(credit.hand_vectors_held, enc::SDM_HAND_VECTORS_HOLD.len());
    assert!(credit.mutants_refuted > 5000, "{credit:?}");
    eprintln!("credit_hook_discharges_over_the_captured_corpus: {credit:?}");
}

/// The hook FAILS CLOSED: an empty corpus, a corpus too narrow to cover the 11
/// emitted form classes, a corpus carrying one wrong encoding, and a corpus
/// carrying a hand-made form the encoder does not emit are each refused.
#[test]
fn credit_hook_fails_closed() {
    let err = enc::mov_imm_credit_over(&[]).expect_err("empty corpus");
    assert!(err.contains("empty"), "{err}");

    let only_rax: Vec<_> = EMITTED_X86_MOV_IMMEDIATES
        .iter()
        .copied()
        .filter(|&(name, _, _)| name == "rax")
        .collect();
    assert!(only_rax.len() > 10);
    let err = enc::mov_imm_credit_over(&only_rax).expect_err("narrow corpus");
    assert!(err.contains("form coverage"), "{err}");

    // Every class but one: still refused, and the missing class is named.
    let no_bare_rex: Vec<_> = EMITTED_X86_MOV_IMMEDIATES
        .iter()
        .copied()
        .filter(|&(name, _, _)| !["spl", "bpl", "sil", "dil"].contains(&name))
        .collect();
    let err = enc::mov_imm_credit_over(&no_bare_rex).expect_err("no bare-REX entries");
    assert!(err.contains("ByteBareRex"), "{err}");

    let mut poisoned = EMITTED_X86_MOV_IMMEDIATES.to_vec();
    poisoned.push(("rax", -1, &[0xB8, 0xFF, 0xFF, 0xFF, 0xFF]));
    let err = enc::mov_imm_credit_over(&poisoned).expect_err("one wrong encoding");
    assert!(err.contains("REFUTED"), "{err}");

    let mut hand_made = EMITTED_X86_MOV_IMMEDIATES.to_vec();
    hand_made.push(("rax", -1, &[0x48, 0xC7, 0xC0, 0xFF, 0xFF, 0xFF, 0xFF]));
    let err = enc::mov_imm_credit_over(&hand_made).expect_err("a never-emitted form");
    assert!(err.contains("not known to emit"), "{err}");
}

/// THE HOOK'S OWN TEETH. `live_mov_immediate_mutants_are_refuted` shows that
/// today's controls refute. It cannot show that the HOOK refuses when a control
/// does not refute: a hook whose control check was forced to `Ok` passed every
/// test. Here the hook is handed each kind of bad control through
/// `mov_imm_credit_over_with`, and it must REFUSE, naming why:
///
///   * a control that SURVIVES (the holding original, relabelled as a mutant);
///   * a control that refutes for the WRONG REASON (the row's named hazard,
///     M3a, whose stated class is moved from Value to Register);
///   * a battery in which a required label never fires;
///   * a decoder control that holds, and one that refutes for the wrong reason;
///   * a hold vector that refutes;
///   * no decoder controls, or a decoder-control set missing the group-11 or
///     the memory-form family.
///
/// The real ingredients must still discharge, so each refusal is caused by the
/// one bad control and not by the seam.
#[test]
fn credit_hook_refuses_surviving_or_misattributed_controls() {
    let corpus = EMITTED_X86_MOV_IMMEDIATES;
    let real_decoder = enc::sdm_decoder_controls();
    let real = enc::mov_imm_credit_over_with(
        corpus,
        &enc::mov_imm_mutants,
        &real_decoder,
        enc::SDM_HAND_VECTORS_HOLD,
    )
    .expect("the real ingredients discharge through the seam");
    assert_eq!(
        real,
        enc::mov_imm_discharges_valid().expect("hook discharges")
    );

    // (1) A SURVIVING control.
    let with_survivor = |name: &str, imm: i64, bytes: &[u8]| {
        let mut battery = enc::mov_imm_mutants(name, imm, bytes);
        battery.push(enc::MovImmMutant {
            label: enc::M1_WRONG_REG_LOW3,
            side: enc::MutantSide::Machine,
            dst_name: name.to_string(),
            imm,
            bytes: bytes.to_vec(),
            expect: RefutationClass::Register,
        });
        battery
    };
    let err = enc::mov_imm_credit_over_with(
        corpus,
        &with_survivor,
        &real_decoder,
        enc::SDM_HAND_VECTORS_HOLD,
    )
    .expect_err("a surviving control must withhold the credit");
    assert!(err.contains("SURVIVED"), "{err}");

    // (2) A control refuted for the WRONG REASON.
    let misattributed = |name: &str, imm: i64, bytes: &[u8]| {
        let mut battery = enc::mov_imm_mutants(name, imm, bytes);
        for m in &mut battery {
            if m.label == enc::M3A_ZERO_FOR_SIGN {
                m.expect = RefutationClass::Register;
            }
        }
        battery
    };
    let err = enc::mov_imm_credit_over_with(
        corpus,
        &misattributed,
        &real_decoder,
        enc::SDM_HAND_VECTORS_HOLD,
    )
    .expect_err("a control refuted for the wrong reason must withhold the credit");
    assert!(err.contains("WRONG REASON"), "{err}");

    // (3) A required label that never fires.
    let no_m8 = |name: &str, imm: i64, bytes: &[u8]| -> Vec<enc::MovImmMutant> {
        enc::mov_imm_mutants(name, imm, bytes)
            .into_iter()
            .filter(|m| m.label != enc::M8_DROPPED_FORCED_REX)
            .collect()
    };
    let err =
        enc::mov_imm_credit_over_with(corpus, &no_m8, &real_decoder, enc::SDM_HAND_VECTORS_HOLD)
            .expect_err("an unexercised facet must withhold the credit");
    assert!(err.contains("never fired"), "{err}");

    // (4) A decoder control that HOLDS: `C7 C0 id` IS mov eax,imm32.
    let mut holding_decoder = real_decoder.clone();
    holding_decoder.push(enc::MovImmMutant {
        label: enc::D1_GROUP11_EXTENSION,
        side: enc::MutantSide::Machine,
        dst_name: "eax".to_string(),
        imm: 0x2A,
        bytes: vec![0xC7, 0xC0, 0x2A, 0x00, 0x00, 0x00],
        expect: RefutationClass::DecodeGroup11,
    });
    let err = enc::mov_imm_credit_over_with(
        corpus,
        &enc::mov_imm_mutants,
        &holding_decoder,
        enc::SDM_HAND_VECTORS_HOLD,
    )
    .expect_err("a holding decoder control must withhold the credit");
    assert!(err.contains("SURVIVED"), "{err}");

    // (5) A decoder control stated with the wrong class.
    let mut wrong_class_decoder = real_decoder.clone();
    for m in &mut wrong_class_decoder {
        if m.label == enc::D2_MEMORY_DESTINATION {
            m.expect = RefutationClass::DecodeGroup11;
        }
    }
    let err = enc::mov_imm_credit_over_with(
        corpus,
        &enc::mov_imm_mutants,
        &wrong_class_decoder,
        enc::SDM_HAND_VECTORS_HOLD,
    )
    .expect_err("a misattributed decoder control must withhold the credit");
    assert!(err.contains("WRONG REASON"), "{err}");

    // (6) Missing decoder-control families, and none at all.
    for dropped in [enc::D1_GROUP11_EXTENSION, enc::D2_MEMORY_DESTINATION] {
        let partial: Vec<_> = real_decoder
            .iter()
            .filter(|m| m.label != dropped)
            .cloned()
            .collect();
        let err = enc::mov_imm_credit_over_with(
            corpus,
            &enc::mov_imm_mutants,
            &partial,
            enc::SDM_HAND_VECTORS_HOLD,
        )
        .expect_err("a missing decoder-control family must withhold the credit");
        assert!(err.contains(dropped), "{err}");
    }
    let err = enc::mov_imm_credit_over_with(
        corpus,
        &enc::mov_imm_mutants,
        &[],
        enc::SDM_HAND_VECTORS_HOLD,
    )
    .expect_err("no decoder controls must withhold the credit");
    assert!(err.contains("no decoder controls"), "{err}");

    // (7) A hold vector that REFUTES: DH claimed for CH's opcode.
    let mut bad_hold = enc::SDM_HAND_VECTORS_HOLD.to_vec();
    bad_hold.push(("CH's opcode claimed as DH", "dh", 7, &[0xB5, 0x07]));
    let err =
        enc::mov_imm_credit_over_with(corpus, &enc::mov_imm_mutants, &real_decoder, &bad_hold)
            .expect_err("a refuting hold vector must withhold the credit");
    assert!(err.contains("must HOLD"), "{err}");

    // And the unit the hook is built from says what it says.
    let survivor = enc::MovImmMutant {
        label: "survivor",
        side: enc::MutantSide::Machine,
        dst_name: "al".to_string(),
        imm: 7,
        bytes: vec![0xB0, 0x07],
        expect: RefutationClass::Value,
    };
    assert!(
        enc::control_is_refuted_as_stated(&survivor)
            .expect_err("survives")
            .contains("SURVIVED")
    );
    let wrong_reason = enc::MovImmMutant {
        bytes: vec![0xB1, 0x07],
        ..survivor.clone()
    };
    assert!(
        enc::control_is_refuted_as_stated(&wrong_reason)
            .expect_err("refutes as Register, stated Value")
            .contains("WRONG REASON")
    );
    let right_reason = enc::MovImmMutant {
        expect: RefutationClass::Register,
        ..wrong_reason
    };
    assert_eq!(enc::control_is_refuted_as_stated(&right_reason), Ok(()));
}

/// THE DECODER'S NEVER-EMITTED BRANCHES. The corpus mutants mutate `+r`-form
/// bytes and cannot reach the ModR/M-level decisions of `C6`/`C7`. Two decoder
/// mutations survived the whole suite before these controls existed: accepting
/// group-11 `/1` as MOV, and letting ModR/M mod 01/10 through as a register
/// destination. Every opcode extension `/1..=/7` and every memory mod/rm shape
/// is now a control the credit hook requires to refute for its stated class.
/// The counts are pinned so the families cannot quietly shrink.
#[test]
fn sdm_decoder_controls_refute_for_their_stated_reason() {
    let controls = enc::sdm_decoder_controls();
    let count = |label: &str| controls.iter().filter(|m| m.label == label).count();
    // 4 spellings (C6, C7, 66 C7, REX.W C7) x 7 extensions.
    assert_eq!(count(enc::D1_GROUP11_EXTENSION), 28);
    // 4 spellings x mod {00, 01, 10} x rm {0, 4, 5}.
    assert_eq!(count(enc::D2_MEMORY_DESTINATION), 36);
    for &(why, ..) in enc::SDM_HAND_VECTORS_REFUTE {
        assert_eq!(
            count(why),
            1,
            "hand refute vector `{why}` is not a decoder control"
        );
    }
    for m in &controls {
        enc::control_is_refuted_as_stated(m).unwrap_or_else(|e| panic!("{e}"));
    }
    // The skeptic's two concrete misreadings, spelled out.
    for (name, bytes) in [
        ("eax", vec![0xC7, 0xC8, 0x2A, 0x00, 0x00, 0x00]),
        ("al", vec![0xC6, 0xC8, 0x2A]),
    ] {
        assert!(
            controls
                .iter()
                .any(|m| m.dst_name == name && m.bytes == bytes),
            "group-11 /1 control {bytes:02x?} is missing"
        );
        assert_eq!(
            enc::mov_imm_check(name, 0x2A, &bytes)
                .map_err(|r| r.class())
                .err(),
            Some(RefutationClass::DecodeGroup11)
        );
    }
    for bytes in [
        vec![0xC7, 0x40, 0x2A, 0x00, 0x00, 0x00],
        vec![0xC7, 0x80, 0x2A, 0x00, 0x00, 0x00],
    ] {
        assert!(
            controls
                .iter()
                .any(|m| m.dst_name == "eax" && m.bytes == bytes)
        );
        assert_eq!(
            enc::mov_imm_check("eax", 0x2A, &bytes)
                .map_err(|r| r.class())
                .err(),
            Some(RefutationClass::DecodeMemoryForm)
        );
    }
}

/// THE HIGH-BYTE TABLE. The decoder derives an AH..BH root arithmetically
/// (`number - 4`), while the source side looks the name up in `SDM_R8_LEGACY`.
/// Swapping CH and DH in that table used to pass every test, because only AH
/// and BH were exercised. Now all four are hold vectors the hook requires.
/// The table must also agree letter by letter with the low-byte names (`?h`
/// aliases bits 15:8 of the same root as `?l`), and each name, decoded from
/// its SDM opcode, must write exactly `0xFF00` of the root with that number.
#[test]
fn sdm_high_byte_table_is_faithful() {
    for i in 0..4usize {
        let high = enc::SDM_R8_LEGACY[4 + i];
        let low = enc::SDM_R8_LEGACY[i];
        assert_eq!(high.len(), 2);
        assert_eq!(
            (high.as_bytes()[0], high.as_bytes()[1], low.as_bytes()[1]),
            (low.as_bytes()[0], b'h', b'l'),
            "`{high}` must be the high byte of the register `{low}` is the low byte of"
        );
        let reg = enc::sdm_reg(high).expect("high-byte register");
        assert_eq!((reg.root, reg.bits, reg.high_byte), (i as u8, 8, true));
        assert_eq!(enc::sdm_reg(low).expect("low byte").root, i as u8);
        assert_eq!(
            enc::sdm_reg(enc::SDM_R16[i]).expect("16-bit").root,
            i as u8,
            "`{}` and `{high}` must alias the same root",
            enc::SDM_R16[i]
        );
        let opcode = 0xB4 + i as u8;
        let holds = enc::mov_imm_check(high, 0x5A, &[opcode, 0x5A])
            .unwrap_or_else(|r| panic!("MOV {high},0x5a = {opcode:02x} 5a refuted: {r}"));
        assert_eq!(
            holds.write,
            RegWrite {
                root: i as u8,
                written_mask: 0xFF00,
                value: 0x5A00,
            }
        );
        for (j, other) in enc::SDM_R8_LEGACY[4..].iter().enumerate() {
            if j != i {
                assert_eq!(
                    enc::mov_imm_check(other, 0x5A, &[opcode, 0x5A])
                        .map_err(|r| r.class())
                        .err(),
                    Some(RefutationClass::Register),
                    "`{other}` claimed for {high}'s opcode {opcode:02x}"
                );
            }
        }
        let name_in_hold_vectors = enc::SDM_HAND_VECTORS_HOLD
            .iter()
            .any(|&(_, n, _, _)| n == high);
        assert!(
            name_in_hold_vectors,
            "no hook hold vector exercises `{high}`"
        );
    }
}

// ---------------------------------------------------------------------------
// 8. The per-compile decode-check runs the obligation
// ---------------------------------------------------------------------------

/// Run trust-cg-codegen's ENC-3 per-compile decode-check on one MovRI.
fn enc3_check(name: &str, imm: i64, bytes: &[u8]) -> Result<bool, String> {
    let intent = X86IntentInst {
        opcode: X86Opcode::MovRI,
        ops: X86InstOperands::ri(preg_named(name), imm),
    };
    check_one_for_test(&intent, bytes, None)
}

/// PER-COMPILE, NOT ONLY CORPUS. `function_verifier::is_covered_elsewhere_indirect_branch`
/// grants every compiled MovRI a `covered_elsewhere` certificate and names
/// `x86_encoding_proofs` as the encoding evidence. That is only honest if a
/// compile actually runs the obligation. ENC-3's own structural comparison was
/// MEASURED BLIND to the row's named hazard: it matches the register number and
/// the low `enc_bits` of the immediate, so it accepted `B8 FF FF FF FF` for
/// `MOV RAX,-1`. ENC-3 now also runs `mov_imm_check_for_preg` on every MovRI,
/// and each wrong pairing below must be REJECTED by the per-compile check, not
/// merely by this crate. The zero-extending alias and the non-canonical padding
/// pass the structural comparison, so the obligation is what rejects them, and
/// the message names it.
#[test]
fn per_compile_decode_check_runs_the_mov_imm_obligation() {
    // (intent register, intent immediate, wrong bytes, must the obligation's
    // message appear). The last column is true where the structural comparison
    // alone accepts the bytes.
    let attacks: &[(&str, i64, &[u8], bool)] = &[
        // Zero-extending alias where a negative imm64 was meant.
        ("rax", -1, &[0xB8, 0xFF, 0xFF, 0xFF, 0xFF], true),
        ("r9", -2, &[0x41, 0xB9, 0xFE, 0xFF, 0xFF, 0xFF], true),
        // A redundant bare REX: same value, non-canonical.
        ("eax", 42, &[0x40, 0xB8, 0x2A, 0x00, 0x00, 0x00], true),
        // A flag-clobbering zeroing idiom where MOV EAX,0 was meant.
        ("eax", 0, &[0x31, 0xC0], false),
        // A wrong register.
        ("rcx", 42, &[0xB8, 0x2A, 0x00, 0x00, 0x00], false),
    ];
    for &(name, imm, bytes, names_obligation) in attacks {
        let err = enc3_check(name, imm, bytes).expect_err(&format!(
            "ENC-3 must REJECT MOV {name},{imm:#x} = {bytes:02x?} per compile"
        ));
        if names_obligation {
            assert!(
                err.contains("x86_encoding_proofs REFUTED"),
                "MOV {name},{imm:#x} = {bytes:02x?}: the structural comparison accepts these \
                 bytes, so the rejection must come from the obligation: {err}"
            );
        }
        // The same pairing refutes in this crate too.
        assert!(enc::mov_imm_check(name, imm, bytes).is_err());
    }
    let alias_err = enc3_check("rax", -1, &[0xB8, 0xFF, 0xFF, 0xFF, 0xFF]).unwrap_err();
    assert!(alias_err.contains("Value"), "{alias_err}");

    // And the per-compile check must not reject REAL output: every corpus intent
    // and a stratified sweep of every register, through the live encoder.
    let mut accepted = 0usize;
    for &(name, imm, _) in EMITTED_X86_MOV_IMMEDIATES {
        let live = live_encode_named(name, imm);
        assert_eq!(
            enc3_check(name, imm, &live),
            Ok(true),
            "ENC-3 rejected the live bytes of MOV {name},{imm:#x}"
        );
        accepted += 1;
    }
    let values = sweep_values(1 << 6);
    for encoding in 0u16..64 {
        let reg = X86PReg::new(encoding);
        for &imm in &values {
            let live = live_encode(reg, imm);
            let intent = X86IntentInst {
                opcode: X86Opcode::MovRI,
                ops: X86InstOperands::ri(reg, imm),
            };
            assert_eq!(
                check_one_for_test(&intent, &live, None),
                Ok(true),
                "ENC-3 rejected the live bytes of MOV {reg},{imm:#x} = {live:02x?}"
            );
            accepted += 1;
        }
    }
    assert!(
        accepted > 50_000,
        "per-compile acceptance sweep shrank to {accepted}"
    );
    eprintln!(
        "per_compile_decode_check_runs_the_mov_imm_obligation: {} wrong pairings REJECTED per \
         compile; {accepted} live encodings ACCEPTED",
        attacks.len()
    );
}

// ---------------------------------------------------------------------------
// 9. Named deferrals and the tally
// ---------------------------------------------------------------------------

/// The non-claims are DATA, and pinned: removing one requires landing its
/// evidence; adding one is a deliberate admission.
#[test]
fn the_named_deferrals_are_pinned() {
    let names: Vec<&str> = X86_MOV_IMM_DEFERRALS.iter().map(|d| d.name).collect();
    assert_eq!(names.len(), 10, "{names:#?}");
    for needle in [
        "RIGHT constant",
        "out-of-width immediate",
        "shortest",
        "PLACEMENT",
        "trampolines",
        "ISA semantics",
        "FRAME facet",
        "every i64 immediate",
        "general x86 decoder",
        "other 28 x86-64 RED rows",
    ] {
        assert!(
            names.iter().any(|n| n.contains(needle)),
            "the `{needle}` non-claim is no longer named"
        );
    }
    for d in X86_MOV_IMM_DEFERRALS {
        assert!(!d.owner.trim().is_empty() && !d.reason.trim().is_empty());
    }
}

/// A real proven / refuted tally over LIVE bytes — never a bare headline count.
#[test]
fn x86_encoding_gate_tally() {
    let (mut proven, mut refuted) = (0usize, 0usize);
    for &(name, imm, _) in EMITTED_X86_MOV_IMMEDIATES {
        let live = live_encode_named(name, imm);
        if enc::mov_imm_obligation(name, imm, &live).is_holding() {
            proven += 1;
        } else {
            refuted += 1;
        }
    }
    let mut controls = 0usize;
    for &(name, imm, _) in EMITTED_X86_MOV_IMMEDIATES {
        let live = live_encode_named(name, imm);
        for m in enc::mov_imm_mutants(name, imm, &live) {
            let ob = enc::mov_imm_obligation(&m.dst_name, m.imm, &m.bytes);
            assert_eq!(ob.refutation_class(), Some(m.expect), "{}", ob.name);
            controls += 1;
        }
    }
    eprintln!(
        "x86_encoding_gate: {proven} proven / {refuted} refuted over LIVE MOV r,imm encodings; \
         {controls} negative controls all REFUTED for their stated reason; {} named non-claims",
        X86_MOV_IMM_DEFERRALS.len()
    );
    assert_eq!(refuted, 0);
    assert_eq!(proven, EMITTED_X86_MOV_IMMEDIATES.len());
}

// ---------------------------------------------------------------------------
// NARROW LOCK CMPXCHG — the encoder refusals the reconstruction ASSUMES
// ---------------------------------------------------------------------------

/// `x86_cmpxchg_narrow_prestate` models the implicit AL/AX accumulator, the
/// source register and the address base as INDEPENDENT symbolic leaves. Its
/// own RAX-alias guard can only fire on a `PReg` operand, and every instruction
/// `select_cmpxchg` actually emits — and every representative the coverage gate
/// discharges — carries `VReg`s, whose assignment the verifier cannot see. So
/// on the shapes that EARN the credit, independence is enforced DOWNSTREAM, by
/// the encoder's hard refusal of a source or base overlapping the accumulator.
///
/// That refusal was an assertion in a doc comment. This runs it against the
/// LIVE encoder, in both the source and the base position, at both widths.
#[test]
fn narrow_cas_encoder_refuses_an_accumulator_aliased_operand() {
    let rax = preg_named("rax");
    let eax = preg_named("eax");
    let rbx = preg_named("rbx");
    let ecx = preg_named("ecx");

    let try_encode = |op: X86Opcode, src: X86PReg, base: X86PReg| {
        let mut encoder = X86Encoder::new();
        encoder
            .encode_instruction(op, &X86InstOperands::rm(src, base, 0))
            .map(|_| encoder.finish())
    };

    for op in [X86Opcode::Cmpxchg8, X86Opcode::Cmpxchg16] {
        // A non-aliased pair encodes — so the refusals below are about the
        // ALIAS, not about the shape.
        try_encode(op, ecx, rbx).unwrap_or_else(|e| panic!("{op:?} ecx,[rbx] must encode: {e:?}"));

        assert!(
            try_encode(op, eax, rbx).is_err(),
            "{op:?} with an RAX-aliased SOURCE must be refused by the encoder — the \
             narrow-CAS reconstruction models the accumulator and the source as \
             independent leaves and nothing else enforces it for a VReg operand"
        );
        assert!(
            try_encode(op, ecx, rax).is_err(),
            "{op:?} with an RAX BASE must be refused by the encoder, for the same \
             reason"
        );
    }
}

/// The byte strings the narrow-CAS credit's documentation quotes are the ones
/// the LIVE encoder emits. The reconstruction is keyed on the `X86Opcode` enum
/// and cannot check this; ENC-3's decode-check checks it per compile; this
/// pins the two canonical strings here, next to the claim.
#[test]
fn narrow_cas_live_encoder_emits_the_documented_byte_strings() {
    let rbx = preg_named("rbx");
    let ecx = preg_named("ecx");
    let encode = |op: X86Opcode| {
        let mut encoder = X86Encoder::new();
        encoder
            .encode_instruction(op, &X86InstOperands::rm(ecx, rbx, 0))
            .unwrap_or_else(|e| panic!("live encoder refused {op:?}: {e:?}"));
        encoder.finish()
    };
    // F0 0F B0 /r — LOCK CMPXCHG r/m8, r8.
    assert_eq!(
        encode(X86Opcode::Cmpxchg8),
        vec![0xF0, 0x0F, 0xB0, 0x0B],
        "LOCK CMPXCHG byte ptr [rbx], cl"
    );
    // F0 66 0F B1 /r — LOCK CMPXCHG r/m16, r16.
    assert_eq!(
        encode(X86Opcode::Cmpxchg16),
        vec![0xF0, 0x66, 0x0F, 0xB1, 0x0B],
        "LOCK CMPXCHG word ptr [rbx], cx"
    );
}

/// ENC-3 COVERS the narrow CAS: the per-compile decode-check accepts live
/// output and REFUTES the width drift that the `NARROW_CMPXCHG` allowlist used
/// to swallow. This is the trust-cg-verify-side pin of that coverage decision,
/// so the allowlist cannot quietly come back while the credit's non-claims say
/// it is gone.
#[test]
fn narrow_cas_per_compile_decode_check_rejects_the_width_drift() {
    let rbx = preg_named("rbx");
    let ecx = preg_named("ecx");
    let ops = X86InstOperands::rm(ecx, rbx, 0);
    let mut encoder = X86Encoder::new();
    encoder
        .encode_instruction(X86Opcode::Cmpxchg8, &ops)
        .expect("live encoder must emit the byte CAS");
    let mut bytes = encoder.finish();
    let intent = X86IntentInst {
        opcode: X86Opcode::Cmpxchg8,
        ops,
    };
    let checked = check_one_for_test(&intent, &bytes, None)
        .expect("ENC-3 must ACCEPT live narrow-CAS output");
    assert!(
        checked,
        "ENC-3 reports the narrow CAS as ALLOWLISTED (Ok(false)) — the credit's          non-claims say the opcode-to-bytes link is carried by this decoder, so          the allowlist must stay gone"
    );

    assert_eq!(bytes[2], 0xB0);
    bytes[2] = 0xB1; // the byte CAS becomes a 32-bit one
    let err = check_one_for_test(&intent, &bytes, None)
        .expect_err("ENC-3 must REFUSE a byte CAS emitted as `0F B1`");
    assert!(
        err.contains("operand width"),
        "the refutation must name the WIDTH, got: {err}"
    );
}

// ---------------------------------------------------------------------------
// (CAS-x86-128) The 128-bit atomic-load pseudo's zero comparand, per compile.
//
// `AtomicLoadCmpxchg16b` is `XOR EAX,EAX; XOR EDX,EDX; XOR EBX,EBX;
// XOR ECX,ECX; LOCK CMPXCHG16B m128`. The zeros make the compare-exchange a
// load: with a non-zero RDX:RAX, a cell equal to it is overwritten with
// RCX:RBX. The reconstruction is keyed on the opcode and never sees a byte, so
// that the emitted bytes really are the four bare zero-extending XORs is
// carried by ENC-3's `check_atomic_load_cmpxchg16b` alone. These two tests are
// the gated pins of that per-compile check and of the encoder refusal the
// reconstruction's prestate assumes (a VReg base independent of the four zeroed
// registers). trust-cg-codegen's `decode_check_x86` holds a longer battery, but
// no gated target runs it.
// ---------------------------------------------------------------------------

fn cmpxchg16b_live(base: &str, disp: i64) -> (X86IntentInst, Vec<u8>) {
    let ops = X86InstOperands {
        base: Some(preg_named(base)),
        disp,
        ..X86InstOperands::none()
    };
    let mut encoder = X86Encoder::new();
    encoder
        .encode_instruction(X86Opcode::AtomicLoadCmpxchg16b, &ops)
        .unwrap_or_else(|e| panic!("live encoder refused CMPXCHG16B [{base}{disp:+}]: {e:?}"));
    let intent = X86IntentInst {
        opcode: X86Opcode::AtomicLoadCmpxchg16b,
        ops,
    };
    (intent, encoder.finish())
}

/// `xor eax,eax; xor edx,edx; xor ebx,ebx; xor ecx,ecx` as the host assembler
/// encodes them (`31 /r`, ModR/M `11 rrr rrr`).
const CMPXCHG16B_ZEROING: [u8; 8] = [0x31, 0xC0, 0x31, 0xD2, 0x31, 0xDB, 0x31, 0xC9];

/// ENC-3 ACCEPTS live pseudo bytes as a CHECKED row and REFUSES every drift of
/// one of the four zeroing XORs: dropped, retargeted at another of the four
/// registers, retargeted at a register pair that is not a zeroing, NARROWED to
/// the 8-bit (`30 /r`) or 16-bit (`66 31 /r`) form, which leave the upper bits
/// of the incoming value in the comparand, and a REX-prefixed form (a correct
/// zeroing, but not the bare form the check pins; refused fail-closed). It also
/// refuses the two CMPXCHG16B drifts whose effect is invisible to the operand
/// comparison: a dropped REX.W (CMPXCHG8B, 8 bytes) and a dropped LOCK.
#[test]
fn cmpxchg16b_per_compile_decode_check_rejects_every_zeroing_drift() {
    let names = ["EAX", "EDX", "EBX", "ECX"];
    for (base, disp) in [("rdi", 0i64), ("rsi", 16), ("r9", -24)] {
        let (intent, bytes) = cmpxchg16b_live(base, disp);
        assert_eq!(
            &bytes[..8],
            &CMPXCHG16B_ZEROING,
            "the pseudo must begin with the four zeroing XORs"
        );
        assert_eq!(
            check_one_for_test(&intent, &bytes, None),
            Ok(true),
            "ENC-3 must ACCEPT live CMPXCHG16B pseudo bytes as a CHECKED row, not an \
             allowlisted one"
        );
        let refused = |mutated: &[u8], what: &str| {
            assert!(
                check_one_for_test(&intent, mutated, None).is_err(),
                "[{base}{disp:+}] ENC-3 must REFUSE {what}: {mutated:02x?}"
            );
        };
        for k in 0..4 {
            let at = 2 * k;
            let reg = names[k];

            let mut dropped = bytes.clone();
            dropped.drain(at..at + 2);
            refused(&dropped, &format!("a dropped `XOR {reg},{reg}`"));

            for other in (0..4).filter(|&o| o != k) {
                let mut retargeted = bytes.clone();
                retargeted[at + 1] = CMPXCHG16B_ZEROING[2 * other + 1];
                refused(
                    &retargeted,
                    &format!("`XOR {reg},{reg}` retargeted at {}", names[other]),
                );
            }

            // ModR/M 11 reg rm with reg != rm: an XOR that zeroes nothing.
            let mut cross = bytes.clone();
            cross[at + 1] ^= 0x08;
            refused(
                &cross,
                &format!("`XOR {reg},{reg}` with mismatched operands"),
            );

            let mut narrow8 = bytes.clone();
            narrow8[at] = 0x30; // XOR r/m8, r8: clears only the low byte
            refused(&narrow8, &format!("`XOR {reg},{reg}` narrowed to 8 bits"));

            let mut narrow16 = bytes.clone();
            narrow16.insert(at, 0x66); // XOR r/m16, r16: clears only the low word
            refused(&narrow16, &format!("`XOR {reg},{reg}` narrowed to 16 bits"));

            let mut rex = bytes.clone();
            rex.insert(at, 0x48);
            refused(&rex, &format!("a REX.W-prefixed `XOR {reg},{reg}`"));
        }

        let cas = 8;
        assert_eq!(bytes[cas], 0xF0, "LOCK");
        assert_eq!(bytes[cas + 1] & 0xF8, 0x48, "REX.W");
        let mut no_rex_w = bytes.clone();
        no_rex_w[cas + 1] &= !0x08;
        if no_rex_w[cas + 1] == 0x40 {
            no_rex_w.remove(cas + 1);
        }
        refused(&no_rex_w, "CMPXCHG8B (a dropped REX.W)");
        let mut unlocked = bytes.clone();
        unlocked.remove(cas);
        refused(&unlocked, "an unlocked CMPXCHG16B");
    }
}

/// The reconstruction's prestate treats a VReg base as independent of RAX,
/// RDX, RBX and RCX: the pseudo zeroes all four before CMPXCHG16B reads its
/// address. That independence is enforced by the LIVE encoder, which refuses a
/// base in any of them (each one would make the CMPXCHG16B read address 0).
#[test]
fn cmpxchg16b_encoder_refuses_a_zeroed_register_base() {
    let try_encode = |base: &str| {
        let ops = X86InstOperands {
            base: Some(preg_named(base)),
            disp: 0,
            ..X86InstOperands::none()
        };
        let mut encoder = X86Encoder::new();
        encoder
            .encode_instruction(X86Opcode::AtomicLoadCmpxchg16b, &ops)
            .map(|_| encoder.finish())
    };
    // Non-aliased bases encode, so the refusals below are about the ALIAS.
    for base in ["rsi", "rdi", "rsp", "rbp", "r8", "r15"] {
        try_encode(base).unwrap_or_else(|e| panic!("CMPXCHG16B [{base}] must encode: {e:?}"));
    }
    for base in ["rax", "rdx", "rbx", "rcx"] {
        assert!(
            try_encode(base).is_err(),
            "CMPXCHG16B with a {base} base must be refused by the encoder: the pseudo \
             zeroes {base} before the CMPXCHG16B reads its address"
        );
    }
}
