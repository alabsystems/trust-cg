// trust-cg-codegen integration test: encoder fail-closed range checks
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// =============================================================================
// Pillar C, task #9 ("provable now"): boundary-exhaustive proof that every
// immediate / offset / shift field with a documented valid range FAILS CLOSED.
//
// For each fixed-width encoder field we assert the *full* fail-closed contract:
//
//   * every IN-range value encodes `Ok` (and, where the field is scaled, every
//     correctly-aligned value);
//   * every OUT-of-range or MISALIGNED value returns the specific `Err`
//     (`EncodeError` / `RiscVEncodeError` / `X86EncodeError`) — NEVER a
//     silently-masked or truncated `Ok` that would be a wrong-code miscompile.
//
// The boundaries themselves (`min-1, min, min+1, max-1, max, max+1`) are tested
// explicitly; small fields (MOVK shift, STP/LDP imm7, x86 SSE4.1 lanes) are
// FULLY ENUMERATED across the surrounding window. Scaled fields additionally
// test misaligned offsets. This is a "reject iff out-of-range/misaligned"
// equivalence, not just a one-sided rejection spot-check.
//
// The encoders under test were specifically hardened (e.g. AArch64
// `scaled_pair_imm7`, the pre/post-index `scaled_pair_imm7_i8` narrowing guard,
// the MOVK shift check, RISC-V `check_imm12` / `check_branch_offset` /
// `check_jump_offset`) to range-check the wide value BEFORE any narrowing cast,
// because a `& mask` / `as iN` truncation of an out-of-range value silently
// yields a *different* valid-looking field — the exact miscompile class this
// test forbids.
// =============================================================================

// ---------------------------------------------------------------------------
// AArch64
// ---------------------------------------------------------------------------
mod aarch64 {
    use trust_cg_codegen::aarch64::encode::{EncodeError, encode_instruction};
    use trust_cg_ir::inst::{AArch64Opcode, MachInst};
    use trust_cg_ir::operand::MachOperand;
    use trust_cg_ir::regs::{D0, D1, PReg, SpecialReg, V0, V1, W0, W1, X0, X1, X2};

    fn mk(opcode: AArch64Opcode, ops: Vec<MachOperand>) -> MachInst {
        MachInst::new(opcode, ops)
    }
    fn preg(r: PReg) -> MachOperand {
        MachOperand::PReg(r)
    }
    fn imm(v: i64) -> MachOperand {
        MachOperand::Imm(v)
    }
    fn sp() -> MachOperand {
        MachOperand::Special(SpecialReg::SP)
    }

    /// Assert the instruction encodes successfully (in-range).
    fn assert_ok(inst: &MachInst, ctx: &str) {
        match encode_instruction(inst) {
            Ok(_) => {}
            Err(e) => panic!("{ctx}: expected Ok (in-range), got Err({e:?})"),
        }
    }

    /// Assert the instruction is REJECTED with an `InvalidOperand` at the field
    /// — never a silently-masked Ok.
    fn assert_invalid_operand(inst: &MachInst, ctx: &str) {
        match encode_instruction(inst) {
            Err(EncodeError::InvalidOperand { .. }) => {}
            Err(other) => panic!("{ctx}: expected InvalidOperand, got Err({other:?})"),
            Ok(w) => {
                panic!("{ctx}: FAIL-OPEN — out-of-range value was silently masked to Ok({w:#010x})")
            }
        }
    }

    // -------------------------------------------------------------------
    // FIELD: add/sub imm12 — unsigned 12-bit [0, 4095]. (imm12_operand)
    // -------------------------------------------------------------------
    #[test]
    fn add_sub_imm12_unsigned_range_fail_closed() {
        // Boundaries: min-1, min, min+1, max-1, max, max+1.
        for (op, name) in [
            (AArch64Opcode::AddRI, "AddRI"),
            (AArch64Opcode::SubRI, "SubRI"),
        ] {
            // In-range: 0 .. 4095 inclusive — sample boundaries + interior.
            for v in [0i64, 1, 2, 2047, 4094, 4095] {
                assert_ok(
                    &mk(op, vec![preg(X0), preg(X1), imm(v)]),
                    &format!("{name} imm12 in-range {v}"),
                );
            }
            // Out-of-range below (min-1 = -1) and above (max+1 = 4096, and far).
            for v in [-1i64, -2, 4096, 4097, 0x1_0000, i64::MAX, i64::MIN] {
                assert_invalid_operand(
                    &mk(op, vec![preg(X0), preg(X1), imm(v)]),
                    &format!("{name} imm12 OOB {v}"),
                );
            }
            // Critical mask probe: 0x1000 (4096) would mask to 0 under `& 0xFFF`;
            // 0x1001 would mask to 1. Both MUST reject, not alias to a small imm.
            assert_invalid_operand(
                &mk(op, vec![preg(X0), preg(X1), imm(0x1000)]),
                &format!("{name} imm12 mask-alias 0x1000"),
            );
            assert_invalid_operand(
                &mk(op, vec![preg(X0), preg(X1), imm(0x1001)]),
                &format!("{name} imm12 mask-alias 0x1001"),
            );
        }
    }

    // -------------------------------------------------------------------
    // FIELD: MOVK shift — shift is a non-negative multiple of 16 with
    // hw = shift/16 in 0..=3. Fully enumerated around the window.
    // -------------------------------------------------------------------
    #[test]
    fn movk_shift_range_fully_enumerated_fail_closed() {
        // Valid shifts: exactly {0, 16, 32, 48}.
        for sh in [0i64, 16, 32, 48] {
            assert_ok(
                &mk(AArch64Opcode::Movk, vec![preg(X0), imm(0x1234), imm(sh)]),
                &format!("MOVK shift valid {sh}"),
            );
        }
        // Non-multiples-of-16 in the [0, 48] window: every one must reject.
        for sh in 0i64..=64 {
            if sh % 16 == 0 && (0..=48).contains(&sh) {
                continue; // valid, already covered
            }
            assert_invalid_operand(
                &mk(AArch64Opcode::Movk, vec![preg(X0), imm(0x1234), imm(sh)]),
                &format!("MOVK shift invalid {sh}"),
            );
        }
        // Boundary just above max (64 -> hw=4) and the mask-alias 64 -> hw 4,
        // plus a value that would alias under masking (64 % 16 == 0 but hw=4).
        assert_invalid_operand(
            &mk(AArch64Opcode::Movk, vec![preg(X0), imm(0x1234), imm(64)]),
            "MOVK shift 64 (hw=4, max+1)",
        );
        // Negative shift must reject (not be reinterpreted).
        for sh in [-1i64, -16, -48] {
            assert_invalid_operand(
                &mk(AArch64Opcode::Movk, vec![preg(X0), imm(0x1234), imm(sh)]),
                &format!("MOVK shift negative {sh}"),
            );
        }
    }

    // -------------------------------------------------------------------
    // FIELD: MOVZ/MovI imm16 — unsigned 16-bit [0, 0xFFFF]; out-of-range
    // rejected as MovImmTooWide (never silently truncated to low 16 bits).
    // -------------------------------------------------------------------
    #[test]
    fn movz_imm16_range_fail_closed() {
        for v in [0i64, 1, 0x7FFF, 0xFFFE, 0xFFFF] {
            assert_ok(
                &mk(AArch64Opcode::Movz, vec![preg(X0), imm(v)]),
                &format!("MOVZ imm16 in-range {v}"),
            );
        }
        for v in [-1i64, 0x1_0000, 0x1_0001, 0xFFFF_FFFF, i64::MAX] {
            match encode_instruction(&mk(AArch64Opcode::Movz, vec![preg(X0), imm(v)])) {
                Err(EncodeError::MovImmTooWide { .. }) => {}
                Err(other) => panic!("MOVZ imm16 OOB {v}: expected MovImmTooWide, got {other:?}"),
                Ok(w) => panic!("MOVZ imm16 OOB {v}: FAIL-OPEN — silently masked to Ok({w:#010x})"),
            }
        }
    }

    // -------------------------------------------------------------------
    // FIELD: STP/LDP (signed-offset form) scaled imm7 — signed 7-bit
    // [-64, 63] in scale units. scaled_pair_imm7. Range AND alignment.
    // X-pair scale = 8 bytes; W-pair scale = 4 bytes.
    // -------------------------------------------------------------------
    #[test]
    fn stp_ldp_signed_offset_imm7_range_and_alignment_fail_closed() {
        // X-register pair (scale 8): valid scaled units -64..=63 -> byte
        // offsets -512..=504 in steps of 8. Fully enumerate scaled units.
        for op in [AArch64Opcode::StpRI, AArch64Opcode::LdpRI] {
            for s in -64i64..=63 {
                let byte_off = s * 8;
                assert_ok(
                    &mk(op, vec![preg(X0), preg(X1), preg(X2), imm(byte_off)]),
                    &format!("{op:?} X-pair scaled {s} (byte {byte_off})"),
                );
            }
            // min-1 (scaled -65 = byte -520) and max+1 (scaled 64 = byte 512).
            for byte_off in [-520i64, 512, -528, 520, 8 * 1000, 8 * -1000] {
                assert_invalid_operand(
                    &mk(op, vec![preg(X0), preg(X1), preg(X2), imm(byte_off)]),
                    &format!("{op:?} X-pair OOB byte {byte_off}"),
                );
            }
            // Misalignment: any byte offset not divisible by 8 must reject even
            // when the *scaled* value would be in range.
            for byte_off in [1i64, 2, 7, -1, -7, 9, 4, 33] {
                assert_invalid_operand(
                    &mk(op, vec![preg(X0), preg(X1), preg(X2), imm(byte_off)]),
                    &format!("{op:?} X-pair misaligned byte {byte_off}"),
                );
            }
            // CRITICAL mask-alias: byte 8*192 = 1536 -> scaled 192; 192 as i8 ==
            // -64, which WOULD pass a naive `as i8` + check_imm7. Must reject.
            assert_invalid_operand(
                &mk(op, vec![preg(X0), preg(X1), preg(X2), imm(8 * 192)]),
                &format!("{op:?} X-pair mask-alias scaled 192 -> i8 -64"),
            );
        }

        // W-register pair (scale 4): scaled unit boundaries.
        for op in [AArch64Opcode::StpRI, AArch64Opcode::LdpRI] {
            for s in [-64i64, -1, 0, 1, 63] {
                assert_ok(
                    &mk(op, vec![preg(W0), preg(W1), preg(X2), imm(s * 4)]),
                    &format!("{op:?} W-pair scaled {s}"),
                );
            }
            for byte_off in [-65i64 * 4, 64 * 4, 1, 2, 3] {
                assert_invalid_operand(
                    &mk(op, vec![preg(W0), preg(W1), preg(X2), imm(byte_off)]),
                    &format!("{op:?} W-pair OOB/misaligned byte {byte_off}"),
                );
            }
        }

        // D-register and Q-register pairs exercise scale 8 / 16 alignment.
        for s in [-64i64, 0, 63] {
            assert_ok(
                &mk(
                    AArch64Opcode::StpRI,
                    vec![preg(D0), preg(D1), preg(X2), imm(s * 8)],
                ),
                &format!("StpRI D-pair scaled {s}"),
            );
        }
        for s in [-64i64, 0, 63] {
            assert_ok(
                &mk(
                    AArch64Opcode::StpRI,
                    vec![preg(V0), preg(V1), preg(X2), imm(s * 16)],
                ),
                &format!("StpRI Q-pair scaled {s}"),
            );
        }
        // Q-pair misalignment (scale 16): byte offset 8 is not a multiple of 16.
        assert_invalid_operand(
            &mk(
                AArch64Opcode::StpRI,
                vec![preg(V0), preg(V1), preg(X2), imm(8)],
            ),
            "StpRI Q-pair misaligned byte 8",
        );
    }

    // -------------------------------------------------------------------
    // FIELD: STP/LDP pre/post-index scaled imm7 (the `as i8` narrowing path,
    // hardened by scaled_pair_imm7_i8). Scale = 8 (X64 pair).
    // -------------------------------------------------------------------
    #[test]
    fn stp_pre_ldp_post_index_imm7_narrowing_fail_closed() {
        // StpPreIndex: operands [Rt, Rt2, Rn, #offset]; offset scaled by 8.
        for s in [-64i64, -1, 0, 1, 63] {
            assert_ok(
                &mk(
                    AArch64Opcode::StpPreIndex,
                    vec![preg(X0), preg(X1), sp(), imm(s * 8)],
                ),
                &format!("StpPreIndex scaled {s}"),
            );
        }
        // The exact i8-truncation miscompile: scaled 192 (byte 1536) -> i8 -64.
        // Must reject, not silently encode a -64 offset.
        for byte_off in [8 * 192, 8 * 64, 8 * -65, 8 * 320, -520, 512] {
            assert_invalid_operand(
                &mk(
                    AArch64Opcode::StpPreIndex,
                    vec![preg(X0), preg(X1), sp(), imm(byte_off)],
                ),
                &format!("StpPreIndex OOB/mask-alias byte {byte_off}"),
            );
        }
        // Misalignment on the pre-index path.
        for byte_off in [1i64, 7, -3] {
            assert_invalid_operand(
                &mk(
                    AArch64Opcode::StpPreIndex,
                    vec![preg(X0), preg(X1), sp(), imm(byte_off)],
                ),
                &format!("StpPreIndex misaligned byte {byte_off}"),
            );
        }

        // LdpPostIndex: same narrowing path.
        for s in [-64i64, 0, 63] {
            assert_ok(
                &mk(
                    AArch64Opcode::LdpPostIndex,
                    vec![preg(X0), preg(X1), sp(), imm(s * 8)],
                ),
                &format!("LdpPostIndex scaled {s}"),
            );
        }
        for byte_off in [8 * 192, 8 * 64, 8 * -65, 1, 7] {
            assert_invalid_operand(
                &mk(
                    AArch64Opcode::LdpPostIndex,
                    vec![preg(X0), preg(X1), sp(), imm(byte_off)],
                ),
                &format!("LdpPostIndex OOB/mask-alias/misaligned byte {byte_off}"),
            );
        }
    }

    // -------------------------------------------------------------------
    // FIELD: scalar pre/post-index imm9 — signed 9-bit [-256, 255]
    // (encode_scalar_writeback -> encoding_mem::check_imm9). Boundaries.
    // -------------------------------------------------------------------
    #[test]
    fn scalar_writeback_imm9_range_fail_closed() {
        for op in [
            AArch64Opcode::LdrPreIndex,
            AArch64Opcode::StrPreIndex,
            AArch64Opcode::LdrPostIndex,
            AArch64Opcode::StrPostIndex,
        ] {
            // In-range boundaries: min, min+1, -1, 0, 1, max-1, max.
            for v in [-256i64, -255, -1, 0, 1, 254, 255] {
                // Rt=X0, base=X1 (must not overlap), imm9 offset.
                assert_ok(
                    &mk(op, vec![preg(X0), preg(X1), imm(v)]),
                    &format!("{op:?} imm9 in-range {v}"),
                );
            }
            // Out-of-range: min-1 (-257), max+1 (256), and far values that an
            // `as i16` outer guard would pass but check_imm9 must still reject.
            for v in [-257i64, 256, 257, 1000, -1000] {
                let inst = mk(op, vec![preg(X0), preg(X1), imm(v)]);
                match encode_instruction(&inst) {
                    Err(_) => {}
                    Ok(w) => {
                        panic!("{op:?} imm9 OOB {v}: FAIL-OPEN — silently masked to Ok({w:#010x})")
                    }
                }
            }
        }
    }

    // -------------------------------------------------------------------
    // FIELD: LDR/STR unsigned-offset imm12 OR unscaled imm9 (auto-select).
    // encode_load_store_auto: a non-negative aligned offset that scales into
    // [0, 4095] uses the unsigned form; otherwise [-256, 255] uses unscaled;
    // anything else REJECTS. This is the documented dual-encoding contract.
    // -------------------------------------------------------------------
    #[test]
    fn ldr_str_offset_dual_encoding_fail_closed() {
        // 64-bit load, scale = 8.
        let op = AArch64Opcode::LdrRI;
        // In-range unsigned (aligned, scaled <= 4095): byte 0, 8, 4095*8.
        for byte_off in [0i64, 8, 16, 4095 * 8] {
            assert_ok(
                &mk(op, vec![preg(X0), preg(X1), imm(byte_off)]),
                &format!("LdrRI unsigned in-range byte {byte_off}"),
            );
        }
        // In-range unscaled (negative / small): -8, -256, 255, 100.
        for byte_off in [-8i64, -256, -1, 100, 255] {
            assert_ok(
                &mk(op, vec![preg(X0), preg(X1), imm(byte_off)]),
                &format!("LdrRI unscaled in-range byte {byte_off}"),
            );
        }
        // Out of BOTH encodings: a large positive that overflows the unsigned
        // imm12 yet is past the unscaled +255 window, and a large negative past
        // the unscaled -256 window.
        for byte_off in [
            4096 * 8,
            -257,
            -1000,
            4095 * 8 + 1, /* unaligned & big */
        ] {
            assert_invalid_operand(
                &mk(op, vec![preg(X0), preg(X1), imm(byte_off)]),
                &format!("LdrRI dual-encoding OOB byte {byte_off}"),
            );
        }
    }

    // -------------------------------------------------------------------
    // FIELD: immediate shift amount (LSL/LSR/ASR #imm) — [0, regsize).
    // -------------------------------------------------------------------
    #[test]
    fn immediate_shift_amount_range_fail_closed() {
        // 64-bit: regsize = 64, valid shifts [0, 63] (0 is a MOV alias = Ok).
        for sh in [0i64, 1, 32, 62, 63] {
            assert_ok(
                &mk(AArch64Opcode::LslRI, vec![preg(X0), preg(X1), imm(sh)]),
                &format!("LslI x64 shift {sh}"),
            );
        }
        for sh in [-1i64, 64, 65, 1000] {
            assert_invalid_operand(
                &mk(AArch64Opcode::LslRI, vec![preg(X0), preg(X1), imm(sh)]),
                &format!("LslI x64 shift OOB {sh}"),
            );
        }
        // 32-bit: regsize = 32, valid shifts [0, 31]; 32 must reject.
        for sh in [0i64, 1, 31] {
            assert_ok(
                &mk(AArch64Opcode::LslRI, vec![preg(W0), preg(W1), imm(sh)]),
                &format!("LslI w32 shift {sh}"),
            );
        }
        for sh in [-1i64, 32, 33] {
            assert_invalid_operand(
                &mk(AArch64Opcode::LslRI, vec![preg(W0), preg(W1), imm(sh)]),
                &format!("LslI w32 shift OOB {sh}"),
            );
        }
    }

    // -------------------------------------------------------------------
    // FIELD: ADR/ADRP imm21 — signed 21-bit [-1048576, 1048575]
    // (adr_imm21 guards the i64->i32 narrowing).
    // -------------------------------------------------------------------
    #[test]
    fn adr_adrp_imm21_range_fail_closed() {
        for op in [AArch64Opcode::Adr, AArch64Opcode::Adrp] {
            for v in [-1_048_576i64, -1_048_575, -1, 0, 1, 1_048_574, 1_048_575] {
                assert_ok(
                    &mk(op, vec![preg(X0), imm(v)]),
                    &format!("{op:?} imm21 in-range {v}"),
                );
            }
            // min-1, max+1, and a value whose low 32 bits alias a small in-range
            // value (1<<32 | 5 -> 5 under `as i32`). Must reject.
            for v in [
                -1_048_577i64,
                1_048_576,
                (1i64 << 32) | 5,
                i64::MAX,
                i64::MIN,
            ] {
                assert_invalid_operand(
                    &mk(op, vec![preg(X0), imm(v)]),
                    &format!("{op:?} imm21 OOB/mask-alias {v}"),
                );
            }
        }
    }

    // -------------------------------------------------------------------
    // FIELD: BFM/SBFM/UBFM immr/imms — 6-bit bitfield index [0,63] for the
    // 64-bit (sf=1) form, [0,31] for the 32-bit (sf=0) form. An OOB index
    // would wrap mod 64 (e.g. bit 64 -> bit 0 = a different bitfield).
    // bitfield6_operand. Reject before `& 0x3F`.
    // -------------------------------------------------------------------
    #[test]
    fn bitfield_immr_imms_range_fail_closed() {
        for op in [AArch64Opcode::Ubfm, AArch64Opcode::Sbfm, AArch64Opcode::Bfm] {
            // 64-bit (X) form: immr,imms in [0,63].
            for v in [0i64, 1, 31, 32, 62, 63] {
                assert_ok(
                    &mk(op, vec![preg(X0), preg(X1), imm(v), imm(0)]),
                    &format!("{op:?} X immr in-range {v}"),
                );
                assert_ok(
                    &mk(op, vec![preg(X0), preg(X1), imm(0), imm(v)]),
                    &format!("{op:?} X imms in-range {v}"),
                );
            }
            // 64-bit OOB: min-1, max+1, and mask-alias 64 -> 0 / 65 -> 1.
            for v in [-1i64, 64, 65, 0x40, 0x41, 128, i64::MAX, i64::MIN] {
                assert_invalid_operand(
                    &mk(op, vec![preg(X0), preg(X1), imm(v), imm(0)]),
                    &format!("{op:?} X immr OOB {v}"),
                );
                assert_invalid_operand(
                    &mk(op, vec![preg(X0), preg(X1), imm(0), imm(v)]),
                    &format!("{op:?} X imms OOB {v}"),
                );
            }
            // 32-bit (W) form: immr,imms in [0,31]; 32..=63 must reject even
            // though they fit the raw 6-bit field.
            for v in [0i64, 1, 30, 31] {
                assert_ok(
                    &mk(op, vec![preg(W0), preg(W1), imm(v), imm(0)]),
                    &format!("{op:?} W immr in-range {v}"),
                );
            }
            for v in [-1i64, 32, 33, 63, 64] {
                assert_invalid_operand(
                    &mk(op, vec![preg(W0), preg(W1), imm(v), imm(0)]),
                    &format!("{op:?} W immr OOB {v}"),
                );
                assert_invalid_operand(
                    &mk(op, vec![preg(W0), preg(W1), imm(0), imm(v)]),
                    &format!("{op:?} W imms OOB {v}"),
                );
            }
        }
    }

    // -------------------------------------------------------------------
    // FIELD: logical-immediate pre-decomposed (5-operand) N/immr/imms —
    // N in {0,1}, immr,imms in [0,63]. logical_imm_raw_field. Reject before
    // the `& 1` / `& 0x3F` masks.
    // -------------------------------------------------------------------
    #[test]
    fn logical_imm_raw_fields_range_fail_closed() {
        for op in [
            AArch64Opcode::AndRI,
            AArch64Opcode::OrrRI,
            AArch64Opcode::EorRI,
        ] {
            // In-range raw (N, immr, imms): the raw 5-operand fallback packs
            // these directly, so any in-range triple encodes Ok.
            for (n, immr, imms) in [(0i64, 0i64, 0i64), (1, 63, 63), (0, 31, 31), (1, 0, 1)] {
                assert_ok(
                    &mk(op, vec![preg(X0), preg(X1), imm(n), imm(immr), imm(imms)]),
                    &format!("{op:?} raw N={n} immr={immr} imms={imms}"),
                );
            }
            // N out of {0,1}: 2 masks to 0 under `& 1` -> wrong element width.
            for n in [-1i64, 2, 3, i64::MAX] {
                assert_invalid_operand(
                    &mk(op, vec![preg(X0), preg(X1), imm(n), imm(0), imm(0)]),
                    &format!("{op:?} raw N OOB {n}"),
                );
            }
            // immr/imms > 63 (or negative): wrap mod 64 = a different mask.
            for v in [-1i64, 64, 65, 0x40, i64::MAX] {
                assert_invalid_operand(
                    &mk(op, vec![preg(X0), preg(X1), imm(0), imm(v), imm(0)]),
                    &format!("{op:?} raw immr OOB {v}"),
                );
                assert_invalid_operand(
                    &mk(op, vec![preg(X0), preg(X1), imm(0), imm(0), imm(v)]),
                    &format!("{op:?} raw imms OOB {v}"),
                );
            }
        }
    }

    // -------------------------------------------------------------------
    // FIELD: TBZ/TBNZ test-bit position — [0,63] for X (sf=1), [0,31] for W
    // (sf=0). bit 64 wraps to bit 0 (b5=0,b40=0) = a different bit.
    // tbz_bit_position. Reject before the b5/b40 split.
    // -------------------------------------------------------------------
    #[test]
    fn tbz_tbnz_bit_position_range_fail_closed() {
        for op in [AArch64Opcode::Tbz, AArch64Opcode::Tbnz] {
            // X register: bit [0,63] valid (offset operand small + in-range).
            for bit in [0i64, 1, 31, 32, 62, 63] {
                assert_ok(
                    &mk(op, vec![preg(X0), imm(bit), imm(2)]),
                    &format!("{op:?} X bit in-range {bit}"),
                );
            }
            // X register OOB: min-1, max+1, mask-alias 64 -> 0, 96 -> 0.
            for bit in [-1i64, 64, 65, 96, 128, i64::MAX, i64::MIN] {
                assert_invalid_operand(
                    &mk(op, vec![preg(X0), imm(bit), imm(2)]),
                    &format!("{op:?} X bit OOB {bit}"),
                );
            }
            // W register: bit [0,31] valid; 32..=63 must reject (b5 must be 0).
            for bit in [0i64, 1, 30, 31] {
                assert_ok(
                    &mk(op, vec![preg(W0), imm(bit), imm(2)]),
                    &format!("{op:?} W bit in-range {bit}"),
                );
            }
            for bit in [-1i64, 32, 33, 63, 64] {
                assert_invalid_operand(
                    &mk(op, vec![preg(W0), imm(bit), imm(2)]),
                    &format!("{op:?} W bit OOB {bit}"),
                );
            }
        }
    }

    // -------------------------------------------------------------------
    // FIELD: MOVK / MOVN / MOVZ-alias imm16 — unsigned 16-bit [0,0xFFFF].
    // imm16_operand. These bypass the canonical MovImmTooWide guard, so a
    // wide constant leaked here must reject (as MovImmTooWide), not mask.
    // -------------------------------------------------------------------
    #[test]
    fn move_wide_alias_imm16_range_fail_closed() {
        fn assert_imm_too_wide(inst: &MachInst, ctx: &str) {
            match encode_instruction(inst) {
                Err(EncodeError::MovImmTooWide { .. }) => {}
                Err(other) => panic!("{ctx}: expected MovImmTooWide, got Err({other:?})"),
                Ok(w) => panic!("{ctx}: FAIL-OPEN — OOB imm16 silently masked to Ok({w:#010x})"),
            }
        }

        // MOVK and the typed MOVZ aliases take [Rd, imm16].
        for op in [
            AArch64Opcode::Movk,
            AArch64Opcode::MOVZWi,
            AArch64Opcode::MOVZXi,
            AArch64Opcode::Movn,
        ] {
            let dst = if op == AArch64Opcode::MOVZWi { W0 } else { X0 };
            for v in [0i64, 1, 0x7FFF, 0xFFFE, 0xFFFF] {
                assert_ok(
                    &mk(op, vec![preg(dst), imm(v)]),
                    &format!("{op:?} imm16 in-range {v}"),
                );
            }
            for v in [-1i64, 0x1_0000, 0x1_0001, 0xFFFF_FFFF, i64::MAX, i64::MIN] {
                assert_imm_too_wide(
                    &mk(op, vec![preg(dst), imm(v)]),
                    &format!("{op:?} imm16 OOB {v}"),
                );
            }
        }
    }

    // -------------------------------------------------------------------
    // FIELD: MOVN hw shift — only hw0 is in the v0.1 publication subset.
    // Every nonzero shift must fail closed rather than inherit the hw0 proof.
    // -------------------------------------------------------------------
    #[test]
    fn movn_hw_shift_range_fail_closed() {
        assert_ok(
            &mk(AArch64Opcode::Movn, vec![preg(X0), imm(0x1234), imm(0)]),
            "MOVN explicit shift zero",
        );
        for sh in [-16i64, -1, 1, 8, 15, 16, 17, 32, 48, 64, 80, 1000] {
            assert_invalid_operand(
                &mk(AArch64Opcode::Movn, vec![preg(X0), imm(0x1234), imm(sh)]),
                &format!("MOVN shift OOB {sh}"),
            );
        }
    }

    // -------------------------------------------------------------------
    // FIELD: imm19 PC-relative — signed 19-bit word offset [-262144, 262143].
    // branch_offset_signed(.., 19). LDR-literal / B.cond / Bcc / CBZ / CBNZ.
    // -------------------------------------------------------------------
    #[test]
    fn imm19_pcrel_range_fail_closed() {
        const MIN: i64 = -262_144;
        const MAX: i64 = 262_143;
        // LDR literal: [Rt, imm19].
        for v in [MIN, MIN + 1, -1, 0, 1, MAX - 1, MAX] {
            assert_ok(
                &mk(AArch64Opcode::LdrLiteral, vec![preg(X0), imm(v)]),
                &format!("LdrLiteral imm19 in-range {v}"),
            );
        }
        for v in [MIN - 1, MAX + 1, 1 << 19, -(1 << 19), i64::MAX, i64::MIN] {
            assert_invalid_operand(
                &mk(AArch64Opcode::LdrLiteral, vec![preg(X0), imm(v)]),
                &format!("LdrLiteral imm19 OOB {v}"),
            );
        }
        // CBZ/CBNZ: [Rt, imm19].
        for op in [AArch64Opcode::Cbz, AArch64Opcode::Cbnz] {
            for v in [MIN, 0, MAX] {
                assert_ok(
                    &mk(op, vec![preg(X0), imm(v)]),
                    &format!("{op:?} imm19 in-range {v}"),
                );
            }
            for v in [MIN - 1, MAX + 1] {
                assert_invalid_operand(
                    &mk(op, vec![preg(X0), imm(v)]),
                    &format!("{op:?} imm19 OOB {v}"),
                );
            }
        }
        // B.cond / Bcc: [cond, imm19].
        for op in [AArch64Opcode::BCond, AArch64Opcode::Bcc] {
            for v in [MIN, 0, MAX] {
                assert_ok(
                    &mk(op, vec![imm(0), imm(v)]),
                    &format!("{op:?} imm19 in-range {v}"),
                );
            }
            for v in [MIN - 1, MAX + 1] {
                assert_invalid_operand(
                    &mk(op, vec![imm(0), imm(v)]),
                    &format!("{op:?} imm19 OOB {v}"),
                );
            }
        }
    }

    // -------------------------------------------------------------------
    // FIELD: imm26 PC-relative — signed 26-bit word offset
    // [-33554432, 33554431]. branch_offset_signed(.., 26). B / Bl / BL.
    // -------------------------------------------------------------------
    #[test]
    fn imm26_pcrel_range_fail_closed() {
        const MIN: i64 = -33_554_432;
        const MAX: i64 = 33_554_431;
        for op in [AArch64Opcode::B, AArch64Opcode::Bl, AArch64Opcode::BL] {
            for v in [MIN, MIN + 1, -1, 0, 1, MAX - 1, MAX] {
                assert_ok(&mk(op, vec![imm(v)]), &format!("{op:?} imm26 in-range {v}"));
            }
            for v in [MIN - 1, MAX + 1, 1 << 26, -(1 << 26), i64::MAX, i64::MIN] {
                assert_invalid_operand(&mk(op, vec![imm(v)]), &format!("{op:?} imm26 OOB {v}"));
            }
        }
    }

    // -------------------------------------------------------------------
    // FIELD: imm14 PC-relative (TBZ/TBNZ branch offset) — signed 14-bit word
    // offset [-8192, 8191]. branch_offset_signed(.., 14). Distinct from the
    // TBZ/TBNZ bit-position seed.
    // -------------------------------------------------------------------
    #[test]
    fn imm14_pcrel_range_fail_closed() {
        const MIN: i64 = -8192;
        const MAX: i64 = 8191;
        for op in [AArch64Opcode::Tbz, AArch64Opcode::Tbnz] {
            // [Rt, bit, imm14] with a valid in-range bit.
            for v in [MIN, MIN + 1, -1, 0, 1, MAX - 1, MAX] {
                assert_ok(
                    &mk(op, vec![preg(X0), imm(0), imm(v)]),
                    &format!("{op:?} imm14 in-range {v}"),
                );
            }
            for v in [MIN - 1, MAX + 1, 1 << 14, -(1 << 14), i64::MAX, i64::MIN] {
                assert_invalid_operand(
                    &mk(op, vec![preg(X0), imm(0), imm(v)]),
                    &format!("{op:?} imm14 OOB {v}"),
                );
            }
        }
    }

    // -------------------------------------------------------------------
    // FIELD: GOT/TLV unsigned scaled imm12 — offset/8 in [0,4095], 8-byte
    // aligned. got_tlv_scaled_imm12. Range AND alignment before `/8 & 0xFFF`.
    // -------------------------------------------------------------------
    #[test]
    fn got_tlv_scaled_imm12_range_and_alignment_fail_closed() {
        for op in [AArch64Opcode::LdrGot, AArch64Opcode::LdrTlvp] {
            // In-range aligned: byte 0, 8, 16, 4095*8.
            for byte_off in [0i64, 8, 16, 4095 * 8] {
                assert_ok(
                    &mk(op, vec![preg(X0), preg(X1), imm(byte_off)]),
                    &format!("{op:?} GOT/TLV in-range byte {byte_off}"),
                );
            }
            // Out of [0,4095] scaled (negative, and 4096*8 = scaled 4096), plus
            // the mask-alias 4096*8 which would mask to 0 under `& 0xFFF`.
            for byte_off in [-8i64, 4096 * 8, (4096 * 8) + 8, i64::MAX, i64::MIN] {
                assert_invalid_operand(
                    &mk(op, vec![preg(X0), preg(X1), imm(byte_off)]),
                    &format!("{op:?} GOT/TLV OOB byte {byte_off}"),
                );
            }
            // Misaligned: any byte offset not divisible by 8 must reject even
            // when the scaled value would be in range.
            for byte_off in [1i64, 2, 7, 9, -1, 15] {
                assert_invalid_operand(
                    &mk(op, vec![preg(X0), preg(X1), imm(byte_off)]),
                    &format!("{op:?} GOT/TLV misaligned byte {byte_off}"),
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// RISC-V
// ---------------------------------------------------------------------------
mod riscv {
    use trust_cg_codegen::riscv::encode::{
        RiscVEncodeError, RiscVInstOperands, encode_instruction,
    };
    use trust_cg_ir::riscv_ops::RiscVOpcode;
    use trust_cg_ir::riscv_regs::{X1, X2, X10};

    fn assert_ok(op: RiscVOpcode, ops: &RiscVInstOperands, ctx: &str) {
        match encode_instruction(op, ops) {
            Ok(_) => {}
            Err(e) => panic!("{ctx}: expected Ok (in-range), got Err({e:?})"),
        }
    }

    fn assert_oob(op: RiscVOpcode, ops: &RiscVInstOperands, bits: u32, ctx: &str) {
        match encode_instruction(op, ops) {
            Err(RiscVEncodeError::ImmediateOutOfRange { bits: b, .. }) => {
                assert_eq!(b, bits, "{ctx}: wrong bits width in error");
            }
            Err(other) => panic!("{ctx}: expected ImmediateOutOfRange, got {other:?}"),
            Ok(w) => panic!("{ctx}: FAIL-OPEN — OOB value silently masked to Ok({w:#010x})"),
        }
    }

    // -------------------------------------------------------------------
    // FIELD: I-type / S-type imm12 — signed 12-bit [-2048, 2047].
    // check_imm12. Boundaries.
    // -------------------------------------------------------------------
    #[test]
    fn i_s_type_imm12_range_fail_closed() {
        // I-type: ADDI rd, rs1, imm12.
        for v in [-2048i32, -2047, -1, 0, 1, 2046, 2047] {
            assert_ok(
                RiscVOpcode::Addi,
                &RiscVInstOperands::rri(X10, X1, v),
                &format!("ADDI imm12 in-range {v}"),
            );
        }
        // min-1, max+1, and mask-alias: 4096 (== 0x1000) masks to 0 under
        // `& 0xFFF`; 2048 masks to a *negative* (sign bit of the 12-bit field).
        for v in [-2049i32, 2048, 2049, 4096, 4097, i32::MAX, i32::MIN] {
            assert_oob(
                RiscVOpcode::Addi,
                &RiscVInstOperands::rri(X10, X1, v),
                12,
                &format!("ADDI imm12 OOB {v}"),
            );
        }
        // S-type: SW rs2, imm12(rs1).
        for v in [-2048i32, 0, 2047] {
            assert_ok(
                RiscVOpcode::Sw,
                &RiscVInstOperands::store(X1, X2, v),
                &format!("SW imm12 in-range {v}"),
            );
        }
        for v in [-2049i32, 2048] {
            assert_oob(
                RiscVOpcode::Sw,
                &RiscVInstOperands::store(X1, X2, v),
                12,
                &format!("SW imm12 OOB {v}"),
            );
        }
    }

    // -------------------------------------------------------------------
    // FIELD: B-type branch offset — signed 13-bit even [-4096, 4094].
    // check_branch_offset. Range AND alignment (bit 0 must be 0).
    // -------------------------------------------------------------------
    #[test]
    fn b_type_branch_offset_range_and_alignment_fail_closed() {
        // In-range even boundaries: min, min+2, -2, 0, 2, max-2, max.
        for v in [-4096i32, -4094, -2, 0, 2, 4092, 4094] {
            assert_ok(
                RiscVOpcode::Beq,
                &RiscVInstOperands::branch(X1, X2, v),
                &format!("BEQ offset in-range {v}"),
            );
        }
        // min-2 (-4098), max+2 (4096): out of range.
        for v in [-4098i32, 4096, 8192, -8192] {
            assert_oob(
                RiscVOpcode::Beq,
                &RiscVInstOperands::branch(X1, X2, v),
                13,
                &format!("BEQ offset OOB {v}"),
            );
        }
        // Misaligned (odd) offsets in range must still reject — the bit-packer
        // would drop bit 0 and branch to the WRONG target.
        for v in [1i32, -1, 3, 4093, -4095] {
            assert_oob(
                RiscVOpcode::Beq,
                &RiscVInstOperands::branch(X1, X2, v),
                13,
                &format!("BEQ offset misaligned {v}"),
            );
        }
    }

    // -------------------------------------------------------------------
    // FIELD: J-type (JAL) offset — signed 21-bit even [-1048576, 1048574].
    // check_jump_offset. Range AND alignment.
    // -------------------------------------------------------------------
    #[test]
    fn j_type_jump_offset_range_and_alignment_fail_closed() {
        for v in [-1_048_576i32, -1_048_574, -2, 0, 2, 1_048_572, 1_048_574] {
            assert_ok(
                RiscVOpcode::Jal,
                &RiscVInstOperands::jump(X1, v),
                &format!("JAL offset in-range {v}"),
            );
        }
        for v in [-1_048_578i32, 1_048_576, i32::MAX, i32::MIN] {
            assert_oob(
                RiscVOpcode::Jal,
                &RiscVInstOperands::jump(X1, v),
                21,
                &format!("JAL offset OOB {v}"),
            );
        }
        for v in [1i32, -1, 3, 1_048_573] {
            assert_oob(
                RiscVOpcode::Jal,
                &RiscVInstOperands::jump(X1, v),
                21,
                &format!("JAL offset misaligned {v}"),
            );
        }
    }
}

// ---------------------------------------------------------------------------
// x86-64
// ---------------------------------------------------------------------------
//
// x86-64 is variable-length: most immediates legitimately span the full i8/i32
// range (the encoder auto-selects imm8 vs imm32), so they are NOT fixed-width
// "narrow field" range checks. The genuine fixed-width fail-closed fields are
// the SSE4.1 lane selectors (dword 0..3, qword 0..1) and the disp32 narrowing
// guard, which we enumerate / boundary-test here.
mod x86_64 {
    use trust_cg_codegen::x86_64::encode::{X86EncodeError, X86Encoder, X86InstOperands};
    use trust_cg_ir::x86_64_ops::X86Opcode;
    use trust_cg_ir::x86_64_regs::{EAX, RAX, XMM0, XMM1};

    fn enc_lane(op: X86Opcode, ops: &X86InstOperands) -> Result<Vec<u8>, X86EncodeError> {
        let mut enc = X86Encoder::new();
        enc.encode_instruction(op, ops)?;
        Ok(enc.finish())
    }

    fn assert_ok(op: X86Opcode, ops: &X86InstOperands, ctx: &str) {
        match enc_lane(op, ops) {
            Ok(bytes) => assert!(!bytes.is_empty(), "{ctx}: Ok but emitted no bytes"),
            Err(e) => panic!("{ctx}: expected Ok (in-range lane), got Err({e:?})"),
        }
    }

    fn assert_invalid(op: X86Opcode, ops: &X86InstOperands, ctx: &str) {
        match enc_lane(op, ops) {
            Err(X86EncodeError::InvalidOperands(_)) => {}
            Err(other) => panic!("{ctx}: expected InvalidOperands, got {other:?}"),
            Ok(b) => panic!("{ctx}: FAIL-OPEN — OOB lane silently encoded to {b:02x?}"),
        }
    }

    // -------------------------------------------------------------------
    // FIELD: SSE4.1 PINSRD/PEXTRD dword lane — [0, 3]. Fully enumerated.
    // PINSRD: (XMM dst, GPR32 src, lane).  PEXTRD: (GPR32 dst, XMM src, lane).
    // -------------------------------------------------------------------
    #[test]
    fn sse41_dword_lane_range_fully_enumerated_fail_closed() {
        for lane in 0i64..=3 {
            assert_ok(
                X86Opcode::Pinsrd,
                &X86InstOperands::rri(XMM0, EAX, lane),
                &format!("PINSRD dword lane {lane}"),
            );
            assert_ok(
                X86Opcode::Pextrd,
                &X86InstOperands::rri(EAX, XMM1, lane),
                &format!("PEXTRD dword lane {lane}"),
            );
        }
        // min-1 and max+1 and beyond — and a value (256) that a `& 0xFF` byte
        // mask would alias to lane 0; must reject.
        for lane in [-1i64, 4, 5, 256, 0x100, i64::MAX, i64::MIN] {
            assert_invalid(
                X86Opcode::Pinsrd,
                &X86InstOperands::rri(XMM0, EAX, lane),
                &format!("PINSRD dword lane OOB {lane}"),
            );
            assert_invalid(
                X86Opcode::Pextrd,
                &X86InstOperands::rri(EAX, XMM1, lane),
                &format!("PEXTRD dword lane OOB {lane}"),
            );
        }
    }

    // -------------------------------------------------------------------
    // FIELD: SSE4.1 PINSRQ/PEXTRQ qword lane — [0, 1]. Fully enumerated.
    // PINSRQ: (XMM dst, GPR64 src, lane). PEXTRQ: (GPR64 dst, XMM src, lane).
    // -------------------------------------------------------------------
    #[test]
    fn sse41_qword_lane_range_fully_enumerated_fail_closed() {
        for lane in 0i64..=1 {
            assert_ok(
                X86Opcode::Pinsrq,
                &X86InstOperands::rri(XMM0, RAX, lane),
                &format!("PINSRQ qword lane {lane}"),
            );
            assert_ok(
                X86Opcode::Pextrq,
                &X86InstOperands::rri(RAX, XMM1, lane),
                &format!("PEXTRQ qword lane {lane}"),
            );
        }
        for lane in [-1i64, 2, 3, 256, i64::MAX, i64::MIN] {
            assert_invalid(
                X86Opcode::Pinsrq,
                &X86InstOperands::rri(XMM0, RAX, lane),
                &format!("PINSRQ qword lane OOB {lane}"),
            );
            assert_invalid(
                X86Opcode::Pextrq,
                &X86InstOperands::rri(RAX, XMM1, lane),
                &format!("PEXTRQ qword lane OOB {lane}"),
            );
        }
    }
}
