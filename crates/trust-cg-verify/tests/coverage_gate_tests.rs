// trust-cg-verify/tests/coverage_gate_tests.rs — P1.1 coverage-gate test suite
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// This is the BUILD GATE for the emittable-opcode evidence inventory. Accepted,
// explicitly deferred RED, pseudo/trap, and justified exclusion classifications
// are pinned; unknown evidence/classification drift fails the suite.
//
// Every test states the historical bug or invariant it locks in.
//
// `ProofDatabase::new()` materializes the whole proof registry and is
// stack-heavy in debug builds (see proof_database.rs issue #205), so the audit
// runs on a 64 MiB scratch thread, matching `with_large_stack` in
// proof_database.rs / the big-stack spawns in x86_64 proof tests.

use trust_cg_ir::{AArch64Opcode, RiscVOpcode, WasmOpcode, X86Opcode};
use trust_cg_verify::coverage_gate::{
    ALL_AARCH64_OPCODES, ALL_RISCV_OPCODES, ALL_WASM_OPCODES, ALL_X86_OPCODES, CoverageFinding,
    CoverageGate, GateArch, OpcodeClass, aarch64_deferred_value_op_reason,
    aarch64_width_polymorphic_proofs, classify_aarch64, classify_riscv, classify_wasm,
    classify_x86, x86_width_polymorphic_proofs,
};
use trust_cg_verify::proof_database::ProofDatabase;

/// Run `f` on a 64 MiB stack so `ProofDatabase::new()` does not overflow the
/// default 8 MiB test-thread stack (proof_database.rs #205).
fn on_large_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .name("coverage-gate".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn large-stack coverage-gate thread")
        .join()
        .expect("coverage-gate thread panicked")
}

/// Read the fieldless variants from an opcode enum's owning Rust source.
///
/// `std::mem::variant_count` is unstable on the pinned toolchain and a
/// hand-pinned `ALL_*` length only checks the array against itself. Reading the
/// declaration gives the build gate an independent inventory: adding an enum
/// variant while omitting it from `ALL_*` now fails even if nobody updates the
/// numeric pin. The four opcode enums are deliberately fieldless; fail loudly
/// if their declaration stops having one comma-terminated identifier per line.
fn declared_unit_variant_names(
    source: &str,
    enum_name: &str,
) -> std::collections::BTreeSet<String> {
    let marker = format!("pub enum {enum_name} {{");
    let (_, after_marker) = source
        .split_once(&marker)
        .unwrap_or_else(|| panic!("could not find `{marker}` in owning source"));

    let mut names = std::collections::BTreeSet::new();
    let mut found_close = false;
    for (line_index, line) in after_marker.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed == "}" {
            found_close = true;
            break;
        }

        // All documentation in these declarations is line-comment based.
        let code = line.split("//").next().unwrap_or("").trim();
        if code.is_empty() || code.starts_with("#[") {
            continue;
        }

        let declaration = code.strip_suffix(',').unwrap_or_else(|| {
            panic!(
                "{enum_name} source line {} is not a comma-terminated unit variant: `{code}`",
                line_index + 1
            )
        });
        let variant = declaration
            .split_once('=')
            .map_or(declaration, |(name, _)| name)
            .trim();
        let mut chars = variant.chars();
        let valid_identifier = chars
            .next()
            .is_some_and(|first| first == '_' || first.is_ascii_alphabetic())
            && chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric());
        assert!(
            valid_identifier,
            "{enum_name} source line {} is not a fieldless variant declaration: `{code}`",
            line_index + 1
        );
        assert!(
            names.insert(variant.to_string()),
            "{enum_name} declares duplicate variant `{variant}`"
        );
    }
    assert!(
        found_close,
        "could not find the closing brace for `{enum_name}`"
    );
    assert!(!names.is_empty(), "`{enum_name}` declaration was empty");
    names
}

fn assert_inventory_matches_enum_source<T: std::fmt::Debug>(
    architecture: &str,
    enum_name: &str,
    source: &str,
    inventory: &[T],
) {
    let declared = declared_unit_variant_names(source, enum_name);
    let mut inventoried = std::collections::BTreeSet::new();
    for opcode in inventory {
        let name = format!("{opcode:?}");
        assert!(
            inventoried.insert(name.clone()),
            "{architecture} ALL_* inventory contains duplicate `{name}`"
        );
    }
    assert_eq!(
        inventoried, declared,
        "{architecture} ALL_* inventory must exactly match every variant in the owning enum \
         declaration; a missing opcode would otherwise escape the coverage audit"
    );
}

// ===========================================================================
// 1. THE GATE — AArch64
// ===========================================================================

/// STRICT proven-honesty (task #61) + RECONSTRUCTION CREDIT (task #63 Step 4):
/// the HONEST AArch64 emittable coverage.
///
/// Under the STRICT structural rule (`is_genuinely_proven` <=> trust_ir_expr !=
/// aarch64_expr), an opcode whose ONLY *static-DB* covering proof is a
/// structurally degenerate `X == X` self-equality is NOT covered. Task #63 Step 4
/// adds a SECOND, GENUINE crediting path: an opcode that is RECONSTRUCTABLE (in
/// `opcode_to_source_op`) and whose representative reconstructed obligation
/// discharges `Valid` is credited COVERED — its machine side was rebuilt from the
/// REAL opcode+operands, so a wrong isel choice would have refuted (NOT an X==X).
///
/// That reconstruction credit RAISED AArch64 emittable coverage from the honest
/// static-DB 23/55 to 46/63 (73.0%) in the integer-ALU rollout, the FP / div /
/// madd extension then took it to 61/63 (96.8%), the FP-FORMAT-cast extension
/// completed it at 63/63 (100%), the ADRP/ADD address-mode credit took it to
/// 65/65, the direct-branch BRANCH26 credit took it to 68/68, and the i128
/// carry-chain (ADDS;ADC / SUBS;SBC) credit took it to 70/70, the TLVP
/// TLS-descriptor-load credit took it to 71/71, the UBFM/SBFM bitfield-
/// extract-ENCODING credit took it to 73/73, the NEON BITWISE
/// (AND/ORR/EOR/BIC/NOT) per-lane-intent credit brought the denominator to
/// 78/78, and the scalar-FP gap closure (Fcmp FCMP→NZCV+CSET flag model +
/// FmovImm VFPExpandImm encoding promoted out of the allowlist; FRINT{M,P,Z}
/// moved to per-instruction reconstruction) took it to 81/81, and the dense-
/// `match` / fieldless-enum JUMP-TABLE dispatch credit (ADR PC-relative base +
/// LDRSW scaled table-entry effective address) brings it to 83/83 (100%):
///   * +23 opcodes credited via the integer-ALU rollout: the pilot ALU
///     (Add/Sub/Mul/Neg ×{RR,RI}), bitwise (And/Orr/Eor ×{RR,RI}, Bic, Orn),
///     shifts (Lsl/Lsr/Asr ×{RR,RI}), and extends (Sxtb/Sxth/Sxtw; Uxt* were
///     already covered).
///   * +8 to the denominator: Orn/Bic + the 6 shift opcodes moved off the
///     fail-closed allowlist into EmittableNeedsProof now that they reconstruct.
///   * +15 opcodes credited via the FP/div/madd extension: the FP value ops
///     (Fadd/Fsub/Fmul/Fdiv/Fneg/Fabs/Fsqrt), the FP↔int conversions
///     (Fcvtzs/Fcvtzu/Scvtf/Ucvtf), integer division (SDiv/UDiv), and the FUSED
///     multiply-add/sub (Madd/Msub). FP value ops use FP-typed leaves verified by
///     the WIRING-PRESERVING FP evaluator (so a swapped Fsub/Fdiv refutes); div
///     carries a LOAD-BEARING divisor!=0 precond; madd/msub use a COMPOUND source
///     (a*b+c / c-a*b) over the ternary [dst,rn,rm,ra] schema.
///   * +2 opcodes credited via the FP-FORMAT-cast extension: FcvtSD (f32→f64
///     widen / Fpromote) and FcvtDS (f64→f32 narrow / Fdemote). These are
///     width-CHANGING FP↔FP casts reconstructed over a single FP leaf via the
///     WIRING-PRESERVING FP evaluator (the source side is keyed on the DEST
///     format, so a wrong DIRECTION — FcvtSD↔FcvtDS — refutes for a value that
///     does not round-trip through binary32).
///   * +2 opcodes credited via the ADRP/ADD address-mode extension: Adrp and
///     AddPCRel, the PC-relative page+offset address-materialization pair, are
///     bound to the AY-discharged MachO data-relocation proofs (PAGE21
///     `ADRP == page(S+A)`, PAGEOFF12 `ADRP+ADD == S+A`). FAITHFUL — the machine
///     side is the page+offset reconstruction vs. the S+A target, so a broken
///     page/offset split refutes; NOT the retracted const==const X==X. These two
///     moved off the fail-closed address-materialization allowlist into
///     EmittableNeedsProof, so they are per-compile promotable.
///   * +3 opcodes credited via the direct-branch BRANCH26 extension: B, Bl, and
///     BL, the direct PC-relative branch/call forms, are bound to the
///     AY-discharged call-relocation proof (proof_branch26_call_target:
///     `B/BL == S+A`). FAITHFUL (machine = P+offset vs spec = S+A), NOT X==X. The
///     indirect Br/Blr/BLR are CoveredElsewhere (register target established by
///     the surrounding proofs). This closes the instruction-coverage blocker;
///     linker-visible relocation rows remain separate production blockers.
///   * +2 opcodes credited via the i128 carry-chain extension: Adc and Sbc, the
///     i128 add/sub HIGH limbs, are bound to the FAITHFUL whole-chain composition
///     proofs (proof_iadd/isub_i128_whole_chain: the ADDS;ADC / SUBS;SBC pair
///     reconstructs the native 128-bit value — a root BvAdd/BvSub vs a Concat,
///     structurally distinct, NOT X==X; cf. the landed x86 i128 proofs). The
///     shared low-limb ADDS/SUBS is re-routed to the same proof block-aware
///     (next==Adc/Sbc), preserving the i64 checked-add path.
///   * +1 opcode credited via the TLVP extension: LdrTlvp, the TLS-descriptor
///     load (ADRP+LDR via TLVP relocations), is bound to the AY-discharged
///     proof_tlvp_pageoff12_ldr_full (TLVP_LOAD_PAGEOFF12 ADRP+LDR == D+A).
///     FAITHFUL (machine = page(D+A)+offset vs spec = D+A), NOT X==X.
///   * +1 opcode credited via the GOT extension: LdrGot, the fn-pointer / extern-
///     symbol GOT load, is bound to proof_got_load_pageoff12 (GOT_LOAD_PAGEOFF12
///     ADRP+LDR == G+A), the GOT analogue of the TLVP proof. This clears the
///     instruction gate only. The object-relocation inventory deliberately does
///     not convert these AY-backed obligations into production Certified
///     authority, so a fn-pointer object remains fail-closed.
///   * +2 opcodes credited via the dense-`match` / fieldless-enum JUMP-TABLE
///     extension: Adr and LdrswRO, the two address-computation opcodes the
///     JumpTable dispatch emits. Adr (the PC-relative jump-table base) is bound
///     to proof_adr_jumptable_pcrel (`ADR Xd == table_base`, the ring identity
///     `P + (T - P) == T`, MachOEmission) — the byte-granular sibling of the
///     BRANCH26 call target. LdrswRO (`LDRSW Xt,[Xn,Xm,LSL#2]`) is bound to the
///     FAITHFUL scaled-EFFECTIVE-ADDRESS proof proof_ldrsw_ro_scaled_addr
///     (`base + (index<<2) == base + 4*index`, bvshl vs bvmul, AddressMode) — a
///     wrong scale (LSL#3) REFUTES. HONEST SCOPE: the LdrswRO credit is the
///     address-mode scaling only — strictly stronger than the degenerate
///     `("load", Memory)` query but NOT a full memory-load proof (the dereference
///     + i32->i64 sext loaded VALUE remains the shared Ldr* unfaithful-load debt).
///       Closing these two opcodes closes BOTH match shapes (the >=6-variant
///       fieldless-enum match emits the same JumpTable and needs no extra work).
///   * +2 opcodes credited via the bitfield-extract-ENCODING extension: Ubfm
///     (unsigned) and Sbfm (signed), the bitfield EXTRACT forms, are bound to the
///     FAITHFUL extract-ENCODING proofs (proof_ubfm/sbfm_extract_w{32,64}). The
///     machine side is the ARM hardware UBFM/SBFM DECODE of the isel ENCODING
///     `immr=lsb, imms=lsb+width-1` (mask width `imms-immr+1`), the source side is
///     the trust_ir ExtractBits/SextractBits (mask width `width`) — STRUCTURALLY
///     DISTINCT, so a wrong immr/imms formula REFUTES (NOT the degenerate X==X
///     that reusing the structurally-identical encode_ubfm_extract would be). Both
///     are emitted at the 32-bit AND 64-bit register forms, so the
///     width-polymorphic gate requires the w32 AND w64 proofs (both discharge
///     Statistical). Bfm (insert), RorRI (not isel-emitted), Rbit stay fail-closed.
///   * +5 opcodes credited via the NEON BITWISE per-lane-intent extension:
///     NeonAndV, NeonOrrV, NeonEorV, NeonBicV, and NeonNotV — the V128 bitwise
///     vector ops — are bound to the FAITHFUL per-lane-intent == whole-register
///     proofs (proof_neon_{andv,orrv,eorv,bicv,notv}_lanewise_16b). The SOURCE is
///     the trust_ir per-LANE op (split the V128 into the 16 `.16B` byte lanes,
///     apply the lane bitwise op, concat back); the MACHINE is the single
///     whole-128-bit-register op the lowerer emits (encode_neon_*). STRUCTURALLY
///     DISTINCT (a 16-lane concat tree vs one whole-register op), so a wrong
///     machine op (ORR for AND, or BIC without the `~vm` complement) REFUTES — NOT
///     the degenerate X==X the OLD same-shape proof_vector_* proofs are. ONE
///     128-bit obligation per opcode suffices (bitwise ops are lane-width-
///     INDEPENDENT over the register); all 5 discharge Statistical. The NEON
///     arith/compare/shift/fp/perm/memory ops STAY fail-closed.
///
///   * +15 opcodes credited via the NEON LANE-WISE COMPUTE extension (this change):
///     the integer arith (NeonAddV/SubV/MulV), compares (Cmeq/Cmge/Cmgt/Cmhi/Cmhs),
///     immediate shifts (ShlVImm/UshrVImm/SshrVImm), and lane-wise min/max
///     (Smax/Smin/Umax/Umin) are bound to the FAITHFUL per-lane D-REGISTER-PAIR
///     obligations (proof_neon_*_lanewise_4s). The SOURCE slices each lane DIRECTLY
///     from the two 64-bit D-halves of the Q register; the MACHINE is the real
///     `encode_neon_*` encoder over the reassembled `Concat(hi, lo)`. STRUCTURALLY
///     DISTINCT (raw-half Var leaf vs an Extract-of-Concat), so a wrong op /
///     signedness / direction / lane width REFUTES (see
///     `neon_lanewise_compute_wrong_encodings_refute`); all 15 discharge Statistical
///     AND ay-formal. +4 to the denominator: NeonSmaxV/SminV/UmaxV/UminV were
///     emittable-but-UNAUDITED (absent from ALL_AARCH64_OPCODES) and are now audited.
///     The NEON FP-arith / horizontal-reduce / permute / load-store ops STAY
///     fail-closed (honest reasons in classify_aarch64).
///
/// * NEON FP VECTOR ARITH/COMPARE (task: FP elementwise un-forfeit): the FP
///   vector ops NeonFaddV/FsubV/FmulV/FdivV + the NEW NeonFcmgtV (emitted by
///   the elementwise-FP vectorizer neon_fmap) are bound to the FAITHFUL
///   per-lane D-REGISTER-PAIR FP obligations (all_neon_fp_lanewise_proofs, 30:
///   one per op x arrangement x lane, both `.4S` and `.2D` demanded via
///   `aarch64_width_polymorphic_proofs`). HONESTY: both sides share the SMT FP
///   model, so these certify LANE PLUMBING (bits -> op -> lane; wrong-lane-wiring
///   and op-confusion controls REFUTE under real z3), NOT independent symbolic
///   FP-circuit semantics — the FP semantic weight rests on the shared QF_FP
///   model + the silicon-validated NEON-FP differential bridge. +5 covered
///   (+1 to the denominator: NeonFcmgtV is a NEW opcode).
///
/// AArch64 accepted-obligation coverage is 155/246. The 91 RED rows are all
/// explicit `DeferredUnfaithfulModel` findings. This ratio inventories evidence
/// acceptance for emitted value/effect opcodes; it is not a formal-correctness
/// percentage.
#[test]
fn aarch64_emittable_coverage_is_honest_under_strict() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::AArch64));
    // Always print the full audit so the allowlist + degenerate-backed rows stay
    // visible in CI logs (honest gate, not silently truncated).
    eprintln!("{}", report.audit_log());

    assert!(
        report.emittable_count() > 0,
        "AArch64 audit found zero emittable opcodes — classifier is mis-wired"
    );

    // HONEST NUMBERS (task #61 STRICT + #63 integer-ALU + FP/div/madd + FP-format
    // cast + ADRP/ADD address-mode + direct-branch BRANCH26 + i128 carry-chain +
    // TLVP + LdrGot GOT + UBFM/SBFM bitfield-extract + NEON bitwise per-lane-intent
    // + the scalar-FP gap closure (Fcmp + FmovImm) + the dense-`match` JUMP-TABLE
    // dispatch (Adr base + LdrswRO scaled address) + the NEON LANE-WISE COMPUTE
    // extension + the NEON POPCOUNT-FOLD ops CntV/UaddlpV + the NEON SIGNED-ABS op
    // AbsV + the NEON DOT-PRODUCT-ACCUMULATE op UdotV + the NEON BYTE-WINDOW
    // EXTRACT op ExtV + the NEON SIGNED add-long-pairwise op SaddlpV + the NEON
    // BITWISE-INSERT op BitV + the NEON FP LANE ops FaddV/FsubV/FmulV/FdivV and
    // the NEW FP-compare op NeonFcmgtV, credited by the 30 per-lane FP
    // LANE-PLUMBING obligations — see the honesty note above) + the scalar FUSED
    // multiply-add FMADD (single-rounding `fp.fma` reconstruction): the prior
    // pinned state was ALL 112 of 112 emittable opcodes genuinely covered — 64
    // via the static DB (the prior 42 + 15 NEON lane-wise D-pair compute proofs
    // + 2 NEON popcount-fold D-pair proofs + 1 NEON signed-abs D-pair proof + 1
    // NEON dot-product-accumulate D-pair proof + 1 NEON byte-window extract op,
    // credited by its 3 per-immediate D-pair proofs, + 1 NEON signed
    // add-long-pairwise op NeonSaddlpV, credited by its 2 per-arrangement D-pair
    // proofs with the sign-confusion SADDLP-as-UADDLP refute control, + 1 NEON
    // bitwise insert-if-true op NeonBitV, credited by its per-byte-lane
    // obligation with the BSL/BIT/BIF wiring-confusion refute controls) and 41
    // via operand reconstruction (23 integer ALU + 15 FP/div/madd + 2 FP-format
    // casts + FmovImm VFPExpandImm encoding).
    //
    // UNIVERSE BACKFILL (112/112 -> 117/122): 28 enum variants existed OUTSIDE
    // `ALL_AARCH64_OPCODES` — emittable-but-UNAUDITED blind spots (the classifier
    // match is compiler-checked-total, but the AUDIT only iterates the array).
    // Backfilling them:
    //   * 18 exact-ordering LSE/CAS/SWP forms (A-form acquire-only, L-form
    //     release-only, Casl/Swpa/Swpl) -> FailClosedAllowlisted with the same
    //     AtomicOperations reason as their base/AL siblings (not in the
    //     denominator);
    //   * FmaxnmRR/FminnmRR (IEEE minNum/maxNum) -> +2 emittable, COVERED via
    //     operand reconstruction (FpBinary Fmax/Fmin; the representative-inst
    //     table previously fell through to GPR operands, silently failing to
    //     reconstruct — fixed alongside the backfill);
    //   * FrintmRR/FrintpRR/FrintzRR -> +3 emittable, COVERED via the unary-FP
    //     operand reconstruction (floor/ceil/trunc rounding directions refute);
    //   * NeonFmlaV/NeonFmlsV/NeonScvtfV/NeonUcvtfV/NeonDupScalarD -> +5
    //     emittable, NOW COVERED: their FAITHFUL per-lane obligations landed
    //     (`all_neon_fpred_proofs`, both `.2D` lanes per op, real-solver
    //     discharged with wrong-encoding refute controls), moving them from the
    //     honest `DeferredUnfaithfulModel` deferral to covered and emptying the
    //     deferral table — exactly the handoff the universe backfill documented.
    // 122/122 -> 124/124 (two independent landings): (a) UMOV EXTRACT —
    // NeonUmovGen moved from FailClosedAllowlisted (out of the denominator) to
    // EmittableNeedsProof, NOW COVERED via its FAITHFUL per-(size,lane) matrix
    // (all_neon_umov_proofs — 30 obligations: `.16B` 16 lanes + `.8H` 8 + `.4S`
    // 4 + `.2D` 2, real-solver discharged with wrong-lane / wrong-size refute
    // controls); (b) TLS GOT-TPREL — LdrGottprel moved to EmittableNeedsProof,
    // COVERED via aarch64_elf_tls_reloc_proofs (also +1 to the universe). Each
    // is +1 emittable AND +1 covered — the gate stays covered == emittable,
    // fully clean.
    // 124/124 -> 126/126 (one landing, TWO opcodes): FCVTL/FCVTL2 — the vector
    // `f32 -> f64` widening convert (NeonFcvtlV / NeonFcvtl2V) emitted by the FP
    // array-reduction vectorizer (neon_farray) for the widening dot. Both moved
    // to EmittableNeedsProof and are COVERED via their FAITHFUL per-lane
    // obligations (all_neon_fcvtl_proofs — 4: {FCVTL low half, FCVTL2 high half}
    // x `.2D` 2 lanes, real-solver discharged with wrong-half / wrong-lane refute
    // controls). Widening `f32 -> f64` is EXACT (fpext, no rounding). Each is +1
    // emittable AND +1 covered — the gate stays covered == emittable, fully clean.
    // 126/126 -> 127/127 (EorRRShift): the EOR with a ROR-shifted second source
    // (EOR Rd, Rn, Rm, ROR #k) emitted by the rotate-fusion peephole
    // (eor_rotate_fuse) for the ARX `x ^= ROTL(v, r)` idiom. Moved to
    // EmittableNeedsProof and COVERED via its FAITHFUL rotate-XOR obligations
    // (all_eor_ror_shift_proofs — the SOURCE is the frontend ROTL-XOR idiom, the
    // MACHINE is the shifted-register EOR-ROR model, structurally distinct /
    // provably equal; wrong-amount / wrong-shift-kind / operand-swap refute
    // controls; both W and X forms bound via aarch64_width_polymorphic_proofs).
    // +1 emittable AND +1 covered — the gate stays covered == emittable, clean.
    // 127/127 -> 128/128 (FcselRR): the scalar FP conditional select (FCSEL
    // Sd/Dd,Sn,Sm,cc) emitted by the FP-`Select` isel path (CMP cond,#0 + FCSEL)
    // in place of the FMOV(FPR->GPR)x2 + CSEL + FMOV(GPR->FPR) cross-bank route.
    // Moved to EmittableNeedsProof and COVERED via its FAITHFUL bit-preserving-mux
    // obligations (all_fcsel_proofs — the SOURCE is `ite(trust_ir icmp(cond,sel,0),
    // a, b)` over RAW FPR bits, the MACHINE is `ite(eval_condition(from_intcc(cond),
    // CMP(sel,0)), a, b)`, structurally distinct / provably equal; inverted-cond /
    // operand-swap refute controls; both S and D forms bound via
    // aarch64_width_polymorphic_proofs). +1 emittable AND +1 covered — the gate
    // stays covered == emittable, clean.
    // 128/128 -> 129/129 (NeonFmlaLaneV): the NEON FP fused multiply-accumulate
    // BY ELEMENT (FMLA Vd.T, Vn.T, Vm.Ts[lane]) emitted by the elementwise-FP
    // vectorizer (neon_fmap) for `y[i] += da*x[i]` — the scalar invariant `da`
    // kept in a vector lane and broadcast as the multiplier (no DUP), clang's
    // daxpy shape. Moved to EmittableNeedsProof and COVERED via its FAITHFUL
    // per-(arrangement, dest lane, selector) obligations (all_neon_fmla_lane_proofs
    // — {.4S selector 0..3 x dest 0..3 = 16} + {.2D selector 0..1 x dest 0..1 = 4}
    // = 20; the SOURCE slices Vn[dest]/Vm[selector]/Vd[dest] from the raw D-halves
    // and applies the SINGLE-rounding fp.fma, the MACHINE is the real
    // encode_neon_fmla_lane over the reassembled register, structurally distinct /
    // provably equal; wrong-lane-selector / FMLA<->FMLS polarity / accumulator-
    // miswire refute controls; both .4S and .2D forms bound via
    // aarch64_width_polymorphic_proofs). +1 emittable AND +1 covered — the gate
    // stays covered == emittable, clean.
    // 129/129 -> 131/131 (AddRRShift, SubRRShift): ADD/SUB with an LSL-shifted
    // second source (ADD/SUB Rd, Rn, Rm, LSL #k) emitted by the shift-ALU fusion
    // peephole (shift_alu_fuse) for an explicit `y + (x<<k)` / `y - (x<<k)` and
    // the mul-by-constant strength reduction (LslRI + AddRR). Each moved to
    // EmittableNeedsProof and COVERED via its FAITHFUL ring obligations
    // (all_add_sub_lsl_shift_proofs — the SOURCE is `base +/- src*2^k` (bvmul),
    // the MACHINE is `base +/- (src<<k)` (bvshl), structurally distinct / provably
    // equal — the bvmul-vs-bvshl shape of proof_ldrsw_ro_scaled_addr; wrong-amount
    // / ADD-vs-SUB / SUB operand-swap refute controls; both W and X forms bound
    // via aarch64_width_polymorphic_proofs). +2 emittable AND +2 covered — the
    // gate stays covered == emittable, clean.
    // 131/131 -> 135/135 (NeonSmlalV/NeonSmlal2V/NeonUmlalV/NeonUmlal2V): the NEON
    // widening multiply-accumulate-long (SMLAL/SMLAL2/UMLAL/UMLAL2 .4S -> .2D) the
    // neon_array widening-dot vectorizer emits for `s(i64) += ext(a_i32[i]) *
    // ext(b_i32[i])`. Each moved to EmittableNeedsProof and COVERED via its FAITHFUL
    // D-pair accumulate obligation (all_neon_smlal_proofs — SOURCE `acc_j +
    // EXT64(n_s)*EXT64(m_s)` from raw D-halves, MACHINE encode_neon_smlal over the
    // reassembled register, structurally distinct; sign-confusion / no-accumulate /
    // wrong-half / truncating-mul refute controls). +4 emittable AND +4 covered —
    // the gate stays covered == emittable, clean.
    // 135/135 -> 137/137 (NeonUaddwV/NeonUaddw2V): the NEON widening add-wide
    // (UADDW/UADDW2 .4S -> .2D) the neon_array widening abs-sum vectorizer
    // (TRACK D) emits for `s(i64) += zext64(abs_bits(a_i32[i] [+ inv]))`,
    // replacing the UMLAL-by-ones MAC (per lane `acc_j + zext64(u_s)` ==
    // `acc_j + zext64(u_s)*1`). Each moved to EmittableNeedsProof and COVERED via
    // its FAITHFUL D-pair obligation (all_neon_uaddw_proofs — SOURCE `addend_j +
    // zext64(m_s)` from raw D-halves, MACHINE encode_neon_uaddw over the
    // reassembled register, structurally distinct; sign-confusion / no-addend /
    // wrong-half / truncating-add refute controls). +2 emittable AND +2 covered —
    // the gate stays covered == emittable, clean.
    // 137/137 -> 139/139 (NeonSaddwV/NeonSaddw2V): the NEON SIGNED widening
    // add-wide (SADDW/SADDW2 .4S -> .2D) the neon_predsum widening i64-acc
    // condsum emits for `s(i64) += (a_i32[iv] as i64) [if pred]`, replacing the
    // SMLAL-by-ones MAC (per lane `acc_j + sext64(masked_s)` ==
    // `acc_j + sext64(masked_s)*sext64(1)`). Each moved to EmittableNeedsProof
    // and COVERED via its FAITHFUL D-pair obligation (all_neon_saddw_proofs —
    // SOURCE `addend_j + sext64(m_s)` from raw D-halves, MACHINE
    // encode_neon_saddw over the reassembled register, structurally distinct;
    // zext-confusion [SADDW-as-UADDW] / no-addend / wrong-half / truncating-add
    // refute controls). +2 emittable AND +2 covered — the gate stays
    // covered == emittable, clean.
    // 139/139 -> 140/140 (AddRRShiftLsr): ADD with an LSR-shifted second source
    // (ADD Rd, Rn, Rm, LSR #k) emitted by the shift-ALU fusion peephole
    // (shift_alu_fuse) for the srem/sdiv-by-constant magic sign-bit correction
    // (`lsr t, x, #31; add r, r, t`) and the udiv magic add-back. Moved to
    // EmittableNeedsProof and COVERED via its FAITHFUL obligations
    // (all_add_lsr_shift_proofs — the SOURCE is `base + src/2^k` (bvudiv), the
    // MACHINE is `base + (src>>u k)` (bvlshr), structurally distinct / provably
    // equal — the LSR analogue of the bvmul-vs-bvshl ring shape; wrong-amount /
    // ASR-not-LSR / LSL-not-LSR / SUB-not-ADD refute controls; both W and X forms
    // bound via aarch64_width_polymorphic_proofs). +1 emittable AND +1 covered —
    // the gate stays covered == emittable, clean.
    // The shifted-source EOR fusion adds EorRRLsl/EorRRLsr to the publication
    // inventory. Both are reconstructed from their real opcode, register width,
    // operands, and shift amount; the AY suite refutes wrong shift kinds and
    // amounts. +2 emittable AND +2 covered. Complete packed-NZCV TST authority
    // later moves one existing row from deferred to covered; combined with the
    // independent UMULL discharge below, this leaves 91 named RED rows.
    // 140/140 -> 141/141 (NeonRev64V): the NEON 32-bit pair swap (REV64 Vd.4S)
    // the AoS complex-butterfly vectorizer (neon_butterfly) emits to swap each
    // {rp, ip} pair in-register before the twiddle multiply. Moved from the
    // fail-closed permute allowlist to EmittableNeedsProof and COVERED via its
    // FAITHFUL D-pair obligation (proof_neon_rev64v_4s -- the SOURCE selects each
    // output lane from the raw D-halves at the swapped index j^1, the MACHINE is
    // the real encode_neon_rev64_4s whole-register shift/mask form; identity /
    // doubleword-swap / half-lane-smear refute controls). +1 emittable AND +1
    // covered -- the gate stays covered == emittable, clean.
    // 141/141 -> 143/143 (NeonMlaV + NeonUadalpV): the NEON vector
    // multiply-accumulate (MLA.4S — the neon_predsum MLA-by-mask condsum
    // accumulate for the Gpr32 masked-add, replacing AND + ADD.4S with one op;
    // the accumulators hold the NEGATED sum, folded by one wrapping SubRR)
    // and the NEON pairwise widening accumulate (UADALP .4S -> .2D — the
    // neon_array TRACK D abs-sum accumulate, replacing the UADDW/UADDW2 pair;
    // adjacent-pair grouping is a pure mod-2^64 reassociation under the
    // both-lanes drain). Each moved to EmittableNeedsProof and COVERED via
    // its FAITHFUL D-pair obligation (all_neon_mla_proofs — SOURCE
    // `acc_i + n_i*m_i` mod 2^32 from raw D-halves, MACHINE encode_neon_mla;
    // MLS-confusion / MUL-no-accumulate / lane-swap refute controls;
    // all_neon_uadalp_proofs — SOURCE `acc_j + zext64(n_2j) + zext64(n_2j+1)`
    // from raw D-halves, MACHINE encode_neon_uadalp; SADALP-sign-confusion /
    // UADDLP-no-accumulate / wrong-pairing refute controls). +2 emittable AND
    // +2 covered — the gate stays covered == emittable, clean.
    // 143/143 -> 144 covered of 144 at that stage (NeonRbitV): the NEON
    // per-byte 8-bit reverse (RBIT
    // Vd.16B) the neon-bitrev vectorizer emits for `out[i] = a[i].reverse_bits()`
    // over a `[u8; N]` — the EXACT instruction LLVM -O3 emits for that loop
    // (k4_bitrev). Moved from the fail-closed permute allowlist to
    // EmittableNeedsProof and COVERED via its FAITHFUL D-pair obligation
    // (proof_neon_rbitv_16b -- the SOURCE selects every output bit from the raw
    // D-halves at the mirrored within-byte index 8k+7-p, the MACHINE is the real
    // encode_neon_rbit_16b within-byte SWAR shift/mask form; identity /
    // byte-swap [REV16.8B] / 16-bit-lane-reverse [wrong-width] refute controls).
    // +1 emittable AND +1 covered -- the gate stays covered == emittable, clean.
    //
    // 153/246 -> 154/246 (Umull): the 32->64 UNSIGNED widening multiply (UMULL
    // Xd, Wn, Wm — the UMADDL-with-XZR alias, emitted by the W32 magic-division
    // isel path). UMULL has EXACTLY ONE legal form (sf=1 hardwired, W sources,
    // X destination), so the opcode-level binding is faithful. Left the
    // deferred RED table and became COVERED via its FAITHFUL widening
    // obligation (lowering_proof::proof_umull_rr — SOURCE the Concat-zext ring
    // form `concat(0,a)*concat(0,b)`, MACHINE the encoder-faithful
    // `0 + ZeroExtend(a)*ZeroExtend(b)`, structurally distinct / provably equal
    // over BV64; the SMULL sext confusion — exactly what separates UMULL from
    // SMULL — and the truncating-MUL confusion REFUTE, umull_wrong_controls).
    // SMULL deliberately stays a named RED row: the signed sibling must not
    // inherit the unsigned zext proof. +1 covered, denominator unchanged;
    // 93 -> 92 named RED rows. The complete packed-NZCV TST W/X pair then
    // removes one more RED row, yielding the current 155/246 with 91 RED rows.
    //
    // PUBLICATION HONESTY: the emitted value/effect denominator includes the 94
    // forms previously hidden in the historical fail-closed/covered-elsewhere
    // bucket (memory effects, atomics, value copies/selects/conversions, and
    // emitted NEON permute/reduce/memory forms). Existing non-degenerate accepted
    // obligations still earn evidence credit; every unfaithfully modeled form is
    // a named DeferredUnfaithfulModel RED row. This is accepted-obligation
    // evidence coverage, not a formal-correctness percentage.
    assert_eq!(
        report.emittable_count(),
        246,
        "AArch64 emitted value/effect denominator changed; update the pin deliberately"
    );
    assert_eq!(
        report.covered_count(),
        155,
        "AArch64 accepted-obligation count changed; do not re-admit X==X identities or hide \
         emitted value/effect debt outside the denominator:\n{}",
        report.audit_log()
    );
    assert!(
        (report.coverage_percent() - (155.0 / 246.0 * 100.0)).abs() < f64::EPSILON,
        "AArch64 accepted-obligation ratio drifted from the honest 155/246"
    );

    // All 91 uncovered rows must be explicitly named model debt. A generic
    // mapping/discharge failure is a new wiring regression, while moving a row
    // back to the exclusion bucket is denominator shrinkage.
    assert!(
        !report.is_clean(),
        "AArch64 must honestly retain the pinned emitted value/effect model gaps"
    );
    let failures = report.failures();
    assert_eq!(
        failures.len(),
        91,
        "AArch64 must have exactly the 91 pinned deferred rows:\n{}",
        report.failure_summary()
    );
    assert!(
        failures.iter().all(|row| matches!(
            &row.finding,
            Some(CoverageFinding::DeferredUnfaithfulModel { .. })
        )),
        "every AArch64 RED row must be a known DeferredUnfaithfulModel, not a generic wiring gap:\n{}",
        report.failure_summary()
    );
    let expected_red: std::collections::HashSet<_> = ALL_AARCH64_OPCODES
        .iter()
        .copied()
        .filter(|&op| aarch64_deferred_value_op_reason(op).is_some())
        .map(|op| format!("AArch64::{op:?}"))
        .collect();
    let actual_red: std::collections::HashSet<_> = failures
        .iter()
        .map(|row| row.opcode_display.clone())
        .collect();
    assert_eq!(
        actual_red, expected_red,
        "AArch64 RED rows must be exactly the named deferred debt table; unknown drift fails"
    );

    // The six volatile forms added after the original 93-row publication audit
    // are emitted effects, not structural exclusions. Their byte-identical plain
    // load/store encoding does not establish the volatile observation/ordering
    // boundary, so all six must be explicit deferred RED denominator rows.
    for op in [
        AArch64Opcode::VolatileLdrRI,
        AArch64Opcode::VolatileLdrbRI,
        AArch64Opcode::VolatileLdrhRI,
        AArch64Opcode::VolatileStrRI,
        AArch64Opcode::VolatileStrbRI,
        AArch64Opcode::VolatileStrhRI,
    ] {
        assert!(
            matches!(classify_aarch64(op), OpcodeClass::EmittableNeedsProof),
            "AArch64::{op:?} must stay in the emitted value/effect denominator"
        );
        let row = report
            .rows
            .iter()
            .find(|row| row.opcode_display == format!("AArch64::{op:?}"))
            .unwrap_or_else(|| panic!("AArch64::{op:?} missing from audit universe"));
        assert!(
            matches!(
                row.finding,
                Some(CoverageFinding::DeferredUnfaithfulModel { .. })
            ),
            "AArch64::{op:?} must be explicit volatile-boundary RED debt: {row:?}"
        );
    }
}

/// TST produces the complete NZCV state, so opcode coverage must require both
/// packed W/X theorems and the row must no longer be deferred on the strength
/// of a single condition-code observation.
#[test]
fn aarch64_tst_is_covered_by_complete_width_pair() {
    let proofs = aarch64_width_polymorphic_proofs(AArch64Opcode::Tst)
        .expect("TST must be width-complete gated");
    assert_eq!(proofs.len(), 2);
    assert!(proofs.iter().any(|p| p.encoded_width_bits == 32));
    assert!(proofs.iter().any(|p| p.encoded_width_bits == 64));
    assert!(
        proofs.iter().all(|p| p.query.contains("packed nzcv")),
        "TST authority must certify the complete flag state"
    );
    assert!(aarch64_deferred_value_op_reason(AArch64Opcode::Tst).is_none());

    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::AArch64));
    let row = report
        .rows
        .iter()
        .find(|row| row.opcode_display == "AArch64::Tst")
        .expect("TST must be in the emitted value/effect denominator");
    assert!(
        row.finding.is_none(),
        "TST must be covered by both packed-NZCV theorems: {}",
        row.note
    );
}

/// The by-element FMLA opcode has an immediate selector and two emitted vector
/// arrangements. Its coverage credit therefore depends on the complete
/// selector-by-destination matrix, not one representative lane at each width.
#[test]
fn aarch64_fmla_lane_gate_requires_full_selector_destination_matrix() {
    use trust_cg_verify::coverage_gate::aarch64_width_polymorphic_proofs;

    let proofs = aarch64_width_polymorphic_proofs(AArch64Opcode::NeonFmlaLaneV)
        .expect("NeonFmlaLaneV must have matrix-bound coverage proofs");
    assert_eq!(proofs.len(), 20, "expected 16 .4S + 4 .2D proof rows");

    let queries: std::collections::HashSet<_> = proofs.iter().map(|p| p.query).collect();
    assert_eq!(queries.len(), 20, "matrix proof queries must be unique");
    for (arr, lanes, width) in [("4s", 4, 32), ("2d", 2, 64)] {
        for selector in 0..lanes {
            for dest in 0..lanes {
                let query = format!("fmlalanev.{arr} sel{selector} dest{dest} fused-fp-intent");
                let proof = proofs
                    .iter()
                    .find(|p| p.query == query)
                    .unwrap_or_else(|| panic!("coverage gate omitted {query}"));
                assert_eq!(proof.encoded_width_bits, width);
            }
        }
    }
}

// ===========================================================================
// 2. THE GATE — x86-64
// ===========================================================================

/// STRICT proven-honesty (task #61): the HONEST x86-64 emittable coverage.
///
/// Same STRICT rule as the AArch64 sibling: an opcode whose only covering proof
/// is a structurally degenerate `X == X` does NOT count as covered. This dropped
/// x86-64 emittable coverage from the old (inflated) 100% to the honest 36/137
/// (26.28%) post-#61.
///
/// HONESTY (task #66, x86-64): the ALU/bitwise/shift/extend families are
/// CREDITED via OPERAND RECONSTRUCTION (mirroring the proven AArch64/RISC-V
/// pattern). Their static "x86_64: …" proofs are degenerate X==X self-equalities
/// that prove NOTHING; the gate no longer relies on them. Instead `audit_x86`
/// rebuilds the machine side FROM THE REAL EMITTED OPCODE+OPERANDS, so a wrong
/// isel choice (ADD-as-SUB, SHL-as-SHR, MOVZX-for-Sextend) or wrong non-
/// commutative wiring REFUTES. The first rollout (#66) raised the genuine surface
/// from 36 (post-#61) to 60 via the 24 integer ALU/bitwise/shift/extend opcodes.
///
/// The SCALAR-REMAINDER extension then took it to 89/139 by reconstructing the
/// register copies (MovRR/MovRR32/MovssRR/MovsdRR as bit-identity), the
/// 3-operand IMUL-imm (ImulRRI), the LEA effective-address forms (plain Lea
/// base+disp and SIB LeaSib base+index*scale+disp, moved out of the allowlist —
/// +2 denominator), and the SSE4.1 mode-poly ROUNDSD/ROUNDSS (floor/ceil/trunc,
/// faithfully modeled by the native FP round-to-integral evaluator). HONESTLY
/// DEFERRED (left RED, not credited): MovRI (const==const, no independent
/// constant model in the single instruction), Idiv/Div (the dividend is the
/// implicit RDX:RAX pair set up by a separate CDQ/CQO+MOV sequence, not an
/// operand of the single instruction), Cmovcc/Cmovcc32 (the select condition is
/// the implicit RFLAGS state of a prior CMP, not an operand) — a single-
/// instruction reconstruction cannot faithfully model those implicit inputs.
///
/// The FP-SCALAR + BIT-MANIP extension first took it to 80/137 by reconstructing
/// the SSE/SSE2 scalar-FP and BMI/SSE4.2 bit-count families:
///   * FP binary value ops Addsd/ss, Subsd/ss, Mulsd/ss, Divsd/ss; unary Sqrtsd/ss;
///     hardware Minsd/ss, Maxsd/ss; UNORD compare-to-mask Cmpsd/ss; FP<->FP casts
///     Cvtsd2ss/Cvtss2sd; truncating FP->int Cvttsd2si/Cvttss2si; int->FP
///     Cvtsi2sd/Cvtsi2ss. FP value ops use FP-typed leaves verified by the
///     WIRING-PRESERVING FP evaluator (swapped Subsd/Divsd refute; commutative
///     Addsd/Mulsd/Min/Max swaps correctly do NOT refute).
///   * Bit-manip Popcnt, Tzcnt, Lzcnt, Bsf, Bsr (Bsf/Bsr carry a load-bearing
///     src != 0 precondition; a Popcnt-for-Tzcnt bug refutes).
///   * The NON-truncating CVTSD2SI/CVTSS2SI (RNE) are deliberately NOT
///     reconstructed: they are not ISel-emitted AND the native FP evaluator does
///     not model RNE rounding, so crediting them would be dishonest.
///
/// The publication audit pins the current result at 158 accepted of 187 emitted
/// value/effect rows. Its 29 named gaps are explicit `DeferredUnfaithfulModel`
/// debt; any generic mapping/discharge failure remains a regression.
#[test]
fn x86_emittable_coverage_is_honest_under_strict() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::X86_64));
    eprintln!("{}", report.audit_log());

    assert!(
        report.emittable_count() > 0,
        "x86-64 audit found zero emittable opcodes — classifier is mis-wired"
    );

    // HISTORICAL ACCEPTED-EVIDENCE GROWTH: 148 rows had genuinely
    // non-degenerate / reconstructed discharged evidence before later additions
    // and the publication denominator audit. The accepted set grew
    // 123 -> 139 (MEMORY tier) -> 144 (IMPLICIT-OPERAND tier) -> 148 (PACKED
    // 128-bit MOVE tier, this stage).
    //
    // PACKED 128-bit MOVE tier (144 -> 148, this stage): the whole-XMM memory
    // moves MOVDQU{RM,MR} (unaligned) and MOVDQA{RM,MR} (aligned), emitted for
    // Fpr128 spill/reload, are GENUINELY RECONSTRUCTED as TWO 64-bit halves at
    // effective addresses `ea` (low 64 bits) and `ea+8` (high 64 bits),
    // little-endian, reusing the PROVEN scalar effective-address machinery
    // (`x86_reconstruct_effective_address`): SOURCE addresses via trust_ir
    // `encode_trust_ir_binop`, MACHINE addresses via the INDEPENDENT x86
    // `encode_lea_*`. A wrong base/index/scale/disp (EA), a SWAPPED half, a wrong
    // half OFFSET (`ea+16` for `ea+8`), a wrong access WIDTH, or (store) a
    // wrong/dropped value half REFUTES. MOVDQA carries the HONEST `ea % 16 == 0`
    // precondition (SSE MOVDQA #GP-faults on a non-16-aligned address); MOVDQU does
    // not — and the alignment assumption NEVER weakens the value equality (see the
    // `movdqa_*_alignment_*` refutations in tests/reconstruction_x86.rs). The
    // reg-reg form MOVDQARR stays separate explicit deferred denominator debt.
    //
    // MEMORY tier (123 -> 139): GENUINE effective-address reconstruction of the
    // load/store, memory-ALU, and in-place inc/dec families. The deterministic
    // `SmtExpr::MemLoad` memory model treats `load(ea)` as a deterministic function
    // of the (effective-address, width, signedness) triple, so a wrong EA reads a
    // DIFFERENT value ⇒ REFUTE. The MACHINE EA is the INDEPENDENT x86 `encode_lea_*`
    // encoder; the SOURCE EA is the trust_ir Iadd/Imul composition.
    //
    // IMPLICIT-OPERAND tier (139 -> 144, this stage): the last 5 rows, whose
    // operative inputs are IMPLICIT (not explicit operands), reconstructed
    // genuinely:
    //   * ImulRM (`dst = reg * load(ea)`): the register-memory signed multiply,
    //     reconstructed via the memory-ALU family (Imul over reg and load(ea)); a
    //     wrong op or wrong EA REFUTES.
    //   * Idiv / Div: the IMPLICIT double-width RDX:RAX dividend. The machine side
    //     is the genuine x86 IDIV/DIV double-width arithmetic — dividend =
    //     sext(rax, 2W) (IDIV, the CDQ/CQO step) or zext(rax, 2W) (DIV); quotient =
    //     trunc(sdiv/udiv(dividend_2W, divisor_2W), W); remainder = trunc(srem/urem).
    //     The source is the trust_ir single-width Sdiv/Srem (or Udiv/Urem). PRECOND:
    //     divisor != 0 AND no signed overflow (!(rax==INT_MIN && divisor==-1)). An
    //     IDIV-as-DIV (sext-vs-zext / sdiv-vs-udiv) bug DIVERGES on a negative
    //     dividend ⇒ REFUTE. The evaluator's BvSDiv/BvUDiv gained 128-bit support so
    //     the 64-bit divide's 128-bit dividend is modeled exactly (no truncation).
    //   * Cmovcc / Cmovcc32: the IMPLICIT RFLAGS condition, reconstructed as a
    //     genuine CMP+CMOV PAIR — machine = ite(eval_int_condition(cc,
    //     flags_of(a,b)), src, dst); source = ite(icmp(intcc_for(cc), a, b), src,
    //     dst). Each condition code is a DISTINCT boolean formula over the genuine
    //     ZF/SF/CF/OF/PF flags (`encode_int_cmp_flags`), so a WRONG cc (E-for-NE,
    //     L-for-GE) gives the complementary boolean ⇒ REFUTE. The gate requires ALL
    //     ten value-select condition codes to discharge (not just one).
    //
    // HONEST-DEFERRED packed ops (NO faithful complete model, NOT credited,
    // denominator RED): PSHUFD (imm8 shuffle), PBLENDVB (mask reg),
    // PTEST/PMOVMSKB (cross-lane flag/sign reductions), PINSR*/PEXTR* (imm8 lane
    // insert/extract), PUNPCK*/PACKUSWB (interleave/narrow shuffles), PMULUDQ
    // (even-lane widening), MOVDQARR (128-bit register-register move, structural —
    // the MOVDQA/MOVDQU MEMORY forms RM/MR are now reconstructed + covered).
    // (148 -> 149). The prior 148 pin was STALE + RED on main, and this commit
    // both corrects a slice-3 misclassification and adds slice 4:
    //   (1) MFENCE (SeqCst fence, slice 3) is a NO-OP on single-thread data
    //       state, so its only faithful value proof is structurally X==X. Slice 3
    //       wrongly marked it EmittableNeedsProof -> the strict gate credits an
    //       X==X ZERO -> Mfence was emittable-but-uncoverable -> the clean-tree
    //       gate was actually RED at 148/149 vs the pinned 148/148. This commit
    //       reclassifies Mfence FailClosedAllowlisted (coverage NOT claimed, same
    //       disposition as RET/CALL/integer-loads); soundness is unchanged (the
    //       identity is registered + witnessed by two refuting negative controls
    //       under proof_gate_strict; ordering is the Intel-SDM axiom). With Mfence
    //       allowlisted the base returns to a clean 148/148.
    //   (2) CMPXCHG (compare_exchange, slice 4) flips FailClosedAllowlisted ->
    //       EmittableNeedsProof (+1 emittable AND +1 covered), COVERED by the six
    //       width-polymorphic conditional-data-flow proofs (Cmpxchg_I{32,64}
    //       returns-old + conditional-store + success-flag), which
    //       `x86_width_polymorphic_proofs` requires to ALL discharge -- genuine
    //       (non-X==X) obligations over symbolic (mem, expected, desired) state;
    //       the negative controls REFUTE. -> 149/149.
    // Net: 149/149 = 100%, genuinely clean (no RED rows, NO X==X credited).
    //
    // (149 -> 151, OPT-7 / LEVER 1): the scaled-index 64-bit memory MOVs
    // MovRMSib (`mov r64, [base+index*scale+disp]`) and MovMRSib
    // (`mov [base+index*scale+disp], r64`) flip FailClosedAllowlisted ->
    // EmittableNeedsProof (+2 emittable AND +2 covered). They are the SIB
    // address-mode fold's outputs (`x86_peephole::sib_addr_fold_run_on_block`),
    // and they reconstruct via the SAME `x86_reconstruct_effective_address`
    // machinery as MovRM/MovMR: the shared encoder already models the
    // `SibMemAddr` EA (`base + index*scale + disp`) on both the trust_ir and the
    // INDEPENDENT x86 `encode_lea_base_index_scale_disp` sides, so they route to
    // the genuine Load_I64 / Store_I64 memory proofs (NOT X==X) — a wrong
    // base/index/scale/disp REFUTES, and the store's value half ties the stored
    // register to the IR store value. -> 151/151.
    //
    // (151 -> 154, OPT-12 / VEC-Q): the packed 64-bit multiply compose the SSE2
    // vectorizer emits for i64 saxpy-accumulate loops:
    //   (1) PSLLQ/PSRLQ (NEW opcodes, +2 emittable AND +2 covered) — the i64x2
    //       uniform-IMMEDIATE shifts, static-DB proofs exactly parallel to the
    //       PSLLD/PSRLD dword forms (group-13 0x73 encoding vs group-12 0x72;
    //       the wrong-lane-width negative control REFUTES a dword-model swap).
    //   (2) PMULUDQ flips FailClosedAllowlisted -> EmittableNeedsProof
    //       (+1 emittable AND +1 covered): its even-dword widening multiply IS
    //       the same-width i64x2 lane op `lo32(a)*lo32(b)` (each qword lane's
    //       result depends only on that lane's low dword), now backed by the
    //       static-DB proof `V2I64 even-dword widening Umul -> PMULUDQ` whose
    //       machine side is the INDEPENDENT SDM-structural even-dword-extract/
    //       zext/mul model; odd-lane, sign-extending, and low-half-only wrong
    //       models all REFUTE (negative controls). -> 154/154.
    // (3) ImulRMSib (X9 slice 3, the RM-fusion producer) joins the
    //     memory-ALU family as the SIB sibling of ImulRM: same Imul value
    //     semantics, EA covered by the SAME `x86_reconstruct_effective_address`
    //     SibMemAddr model as MovRMSib (a wrong base/index/scale/disp REFUTES).
    //     +1 emittable AND +1 covered -> 155/155.
    // (4) X10: the 32-bit SIB MOV pair MovRM32Sib/MovMR32Sib (the b06/b18
    //     u32-array class) joins the memory tier — same shared SibMemAddr EA
    //     reconstruction at Load_I32/Store_I32 width. +2 emittable AND
    //     +2 covered -> 157/157.
    // (5) Psadbw (horizontal byte SAD, the byte-sum vectorizer tier) joins via
    //     the PsadbwByteSad reconstruction (encode_psadbw vs the independent
    //     encode_trust_ir_byte_sad; a wrong lane-wise opcode REFUTES).
    //     +1 emittable AND +1 covered -> 158/158.
    // Publication audit: 13 actively emitted rows formerly hidden by the
    // exclusion bucket (MOV r,imm, narrow CMPXCHG, ten packed ops) and all 16
    // volatile memory opcodes are denominator-bearing RED debt. The accepted
    // obligation count remains 158; the honest denominator is 187.
    // The 158/187 -> 160/189 net: MovsdRMSib/MovssRMSib, the scaled-index
    // scalar-FP loads. +2 emittable AND +2 covered, so coverage is not diluted —
    // each is the COMPOSITION of two already-proven families (the shared
    // SibMemAddr `x86_reconstruct_effective_address` that proves MovRMSib, and
    // the MemLoad obligation that proves MovsdRM/MovssRM at opcode-fixed width).
    // A wrong base/index/scale/disp refutes via the EA half; a wrong width or
    // lane refutes via the FP-load half. No new trust root.
    // The 160/189 -> 162/191 net: MovRM8Sib/MovMR8Sib extend the same
    // independently reconstructed SIB load/store family to I8 width.
    // The 162/191 -> 163/192 net: RolRI is inventoried and covered by the
    // existing RotL_I operand reconstruction; wrong direction/count refutes.
    assert_eq!(
        report.emittable_count(),
        192,
        "x86-64 emitted value/effect denominator changed; update the pin deliberately"
    );
    assert_eq!(
        report.covered_count(),
        163,
        "x86-64 GENUINE (non-degenerate / reconstructed-Valid) emittable coverage changed; \
         update the pinned numbers deliberately — do NOT re-admit X==X identities to inflate this, \
         do NOT credit a memory op without a faithful independent effective-address encoder, and \
         do NOT credit a division/cmov without the genuine double-width / per-cc flag model:\n{}",
        report.audit_log()
    );
    assert!(
        (report.coverage_percent() - (163.0 / 192.0 * 100.0)).abs() < f64::EPSILON,
        "x86-64 accepted-obligation ratio drifted from the honest 163/192"
    );

    let expected_red: std::collections::HashSet<_> = [
        X86Opcode::MovRI,
        X86Opcode::Cmpxchg8,
        X86Opcode::Cmpxchg16,
        X86Opcode::Pshufd,
        X86Opcode::Pmovmskb,
        X86Opcode::MovdqaRR,
        X86Opcode::Punpckldq,
        X86Opcode::Punpcklqdq,
        X86Opcode::Ptest,
        X86Opcode::Pblendvb,
        X86Opcode::Punpcklbw,
        X86Opcode::Punpckhbw,
        X86Opcode::Packuswb,
        X86Opcode::VolatileMovRM8,
        X86Opcode::VolatileMovRM16,
        X86Opcode::VolatileMovRM32,
        X86Opcode::VolatileMovRM,
        X86Opcode::VolatileMovMR8,
        X86Opcode::VolatileMovMR16,
        X86Opcode::VolatileMovMR32,
        X86Opcode::VolatileMovMR,
        X86Opcode::VolatileMovssRM,
        X86Opcode::VolatileMovssMR,
        X86Opcode::VolatileMovsdRM,
        X86Opcode::VolatileMovsdMR,
        X86Opcode::VolatileMovdquRM,
        X86Opcode::VolatileMovdquMR,
        X86Opcode::VolatileMovdqaRM,
        X86Opcode::VolatileMovdqaMR,
    ]
    .into_iter()
    .map(|op| format!("x86_64::{op:?}"))
    .collect();
    let failures = report.failures();
    let actual_red: std::collections::HashSet<_> = failures
        .iter()
        .map(|row| row.opcode_display.clone())
        .collect();
    assert_eq!(
        actual_red,
        expected_red,
        "x86-64 RED debt changed; unknown drift must fail the inventory:\n{}",
        report.failure_summary()
    );
    assert!(
        failures.iter().all(|row| matches!(
            &row.finding,
            Some(CoverageFinding::DeferredUnfaithfulModel { .. })
        )),
        "every x86-64 RED row must be explicit DeferredUnfaithfulModel debt:\n{}",
        report.failure_summary()
    );
}

// ===========================================================================
// 3. The allowlist is HONEST, not a silent truncation
// ===========================================================================

/// LOCKS IN the allowlist-mechanism invariant: every fail-closed allowlist
/// entry carries a non-empty human reason. An empty reason would let a real gap
/// be hidden behind a rubber-stamp; this asserts the gate's exceptions are
/// always auditable.
#[test]
fn allowlist_entries_all_carry_a_reason() {
    for &op in ALL_AARCH64_OPCODES {
        if let OpcodeClass::FailClosedAllowlisted { reason } = classify_aarch64(op) {
            assert!(
                !reason.trim().is_empty(),
                "AArch64::{op:?} is allowlisted with an empty reason"
            );
        }
    }
    for &op in ALL_X86_OPCODES {
        if let OpcodeClass::FailClosedAllowlisted { reason } = classify_x86(op) {
            assert!(
                !reason.trim().is_empty(),
                "x86_64::{op:?} is allowlisted with an empty reason"
            );
        }
    }
    for &op in ALL_RISCV_OPCODES {
        if let OpcodeClass::FailClosedAllowlisted { reason } = classify_riscv(op) {
            assert!(
                !reason.trim().is_empty(),
                "riscv::{op:?} is allowlisted with an empty reason"
            );
        }
    }
}

/// LOCKS IN the "encoder-rejected ⇒ allowlisted (never EmittableNeedsProof)"
/// invariant for the x86 vector pseudos. The encoder returns
/// `EncodeError::UnsupportedOpcode` for these (x86_64/encode.rs ~line 1218), so
/// no compiled program can contain them; they must be allowlisted, not demanded
/// to have a proof. If someone reclassifies one as EmittableNeedsProof without
/// adding a proof, the main gate would fail — this test additionally pins the
/// intended class so the reason is captured.
#[test]
fn x86_unsupported_vector_pseudos_are_allowlisted_not_proof_required() {
    for op in [
        X86Opcode::V4I32MaskExtract,
        X86Opcode::V16I8MaskExtract,
        X86Opcode::V8I16MaskExtract,
        X86Opcode::V2I64MaskExtract,
        X86Opcode::V128BoolSelect,
    ] {
        assert!(
            matches!(classify_x86(op), OpcodeClass::FailClosedAllowlisted { .. }),
            "{op:?} encoder-rejects (UnsupportedOpcode); it must be fail-closed allowlisted"
        );
    }
}

// ===========================================================================
// 4. The emittable universe is COMPLETE (can't silently drop an opcode)
// ===========================================================================

/// LOCKS IN universe completeness for AArch64. The classifier `match` is
/// wildcard-free, so it covers every variant at compile time — but the AUDIT
/// iterates `ALL_AARCH64_OPCODES`. This test independently parses the owning
/// enum declaration and compares every variant name with the array's `Debug`
/// names, while also rejecting duplicates. A newly classified variant omitted
/// from the array therefore fails without relying on a maintainer to update the
/// numeric release pin.
#[test]
fn aarch64_universe_has_no_duplicates_and_matches_pinned_count() {
    assert_inventory_matches_enum_source(
        "AArch64",
        "AArch64Opcode",
        include_str!("../../trust-cg-ir/src/inst.rs"),
        ALL_AARCH64_OPCODES,
    );
    // Release-baseline pin: bump intentionally after the source-vs-inventory
    // comparison has forced the new opcode into the audit.
    assert_eq!(
        ALL_AARCH64_OPCODES.len(),
        290,
        "AArch64 opcode count changed — a variant was added/removed. Update the array AND this \
         pinned count, and classify the new opcode in classify_aarch64 (the build already forced \
         that). (261 = 232 + the UNIVERSE BACKFILL of 28 opcodes that existed in the enum but \
         were absent from the audit array — compiler-checked classifier totality is NOT the \
         same as audit coverage: the 15 exact-ordering LSE RMW forms (A-form acquire-only \
         Ldclra/Ldeora/Ldseta/Ldsmaxa/Ldsmina/Ldumaxa/Ldumina and L-form release-only \
         Ldaddl/Ldclrl/Ldeorl/Ldsetl/Ldsmaxl/Ldsminl/Ldumaxl/Lduminl), the 3 exact-ordering \
         CAS/SWP forms (Casl/Swpa/Swpl) — all allowlisted with the same AtomicOperations \
         reason as their base/AL siblings, + the 5 scalar FP ops FmaxnmRR/FminnmRR (IEEE \
         minNum/maxNum) and FrintmRR/FrintpRR/FrintzRR (floor/ceil/trunc rounding), credited \
         via operand reconstruction, + the 5 `.2D` FP-vectorizer NEON ops \
         NeonFmlaV/NeonFmlsV/NeonScvtfV/NeonUcvtfV/NeonDupScalarD, credited via their 10 \
         FAITHFUL per-lane obligations (all_neon_fpred_proofs, real-solver discharged with \
         FMLA<->FMLS / accumulator-miswire / sign-confusion / wrong-lane refute controls). \
         NeonUmovGen (the lane->GPR extract) then moved from FailClosedAllowlisted to \
         EmittableNeedsProof, credited via its 30 FAITHFUL per-(size,lane) obligations \
         (all_neon_umov_proofs: `.16B`/`.8H`/`.4S`/`.2D`, wrong-lane / wrong-size refute \
         controls) — this does NOT change the universe LENGTH (it was already in the array), \
         only its class. The +1 to 261 is LdrGottprel (TLS GOT-TPREL), a NEW array member \
         classified EmittableNeedsProof and covered via aarch64_elf_tls_reloc_proofs. The \
         +2 to 263 are NeonFcvtlV/NeonFcvtl2V (vector f32->f64 widen low/high), NEW array \
         members covered via their 4 faithful per-lane fpext obligations \
         (all_neon_fcvtl_proofs; wrong-half / wrong-lane refute controls). The +1 to 264 is \
         EorRRShift (EOR Rd,Rn,Rm,ROR #k — the rotate-fusion peephole's shifted-register EOR), \
         a NEW array member classified EmittableNeedsProof and covered via its faithful \
         rotate-XOR obligations (all_eor_ror_shift_proofs, W+X; wrong-amount / wrong-shift-kind / \
         operand-swap refute controls). The +1 to 265 is FcselRR (FCSEL Sd/Dd,Sn,Sm,cc — the \
         FP-Select isel path's scalar FP conditional select), a NEW array member classified \
         EmittableNeedsProof and covered via its faithful bit-preserving-mux obligations \
         (all_fcsel_proofs, S+D; inverted-cond / operand-swap refute controls). The \
         +1 to 266 is NeonFmlaLaneV (FMLA Vd.T,Vn.T,Vm.Ts[lane] — the FP fused \
         multiply-accumulate BY ELEMENT the elementwise-FP vectorizer emits for \
         y[i]+=da*x[i], the scalar invariant da broadcast from a lane, no DUP), a NEW \
         array member classified EmittableNeedsProof and covered via its 20 faithful \
         per-(arrangement,dest,selector) obligations (all_neon_fmla_lane_proofs, .4S+.2D; \
         wrong-lane-selector / FMLA<->FMLS polarity / accumulator-miswire refute controls). \
         The +2 to 268 are AddRRShift/SubRRShift (ADD/SUB Rd,Rn,Rm,LSL #k — the shift-ALU \
         fusion peephole's shifted-register ADD/SUB), NEW array members classified \
         EmittableNeedsProof and covered via their faithful ring obligations \
         (all_add_sub_lsl_shift_proofs, W+X; wrong-amount / ADD-vs-SUB / SUB operand-swap \
         refute controls). \
         The +4 to 272 are NeonSmlalV/NeonSmlal2V/NeonUmlalV/NeonUmlal2V (SMLAL/SMLAL2/UMLAL/ \
         UMLAL2 .4S -> .2D — the widening multiply-accumulate-long the neon_array widening-dot \
         vectorizer emits for `s(i64) += ext(a_i32[i])*ext(b_i32[i])`), NEW array members \
         classified EmittableNeedsProof and covered via their 4 faithful D-pair accumulate \
         obligations (all_neon_smlal_proofs; sign-confusion / no-accumulate / wrong-half / \
         truncating-mul refute controls). \
         The +2 to 274 are NeonUaddwV/NeonUaddw2V (UADDW/UADDW2 .4S -> .2D — the widening \
         add-wide the neon_array widening abs-sum vectorizer TRACK D emits for \
         `s(i64) += zext64(abs_bits(a_i32[i] [+ inv]))`, replacing the UMLAL-by-ones MAC), \
         NEW array members classified EmittableNeedsProof and covered via their 2 faithful \
         D-pair obligations (all_neon_uaddw_proofs; sign-confusion / no-addend / wrong-half / \
         truncating-add refute controls). \
         The +2 to 276 are NeonSaddwV/NeonSaddw2V (SADDW/SADDW2 .4S -> .2D — the SIGNED \
         widening add-wide the neon_predsum widening i64-acc condsum emits for \
         `s(i64) += (a_i32[iv] as i64) [if pred]`, replacing the SMLAL-by-ones MAC), \
         NEW array members classified EmittableNeedsProof and covered via their 2 faithful \
         D-pair obligations (all_neon_saddw_proofs; zext-confusion [SADDW-as-UADDW] / \
         no-addend / wrong-half / truncating-add refute controls). \
         The +1 to 277 is AddRRShiftLsr (ADD Rd,Rn,Rm,LSR #k — the shift-ALU fusion \
         peephole's LSR sibling, the srem/sdiv magic sign-bit correction), a NEW array \
         entry covered via all_add_lsr_shift_proofs. \
         The +2 to 279 are NeonMlaV (MLA.4S — the same-width tied-accumulator MAC the \
         neon_predsum MLA-by-mask condsum accumulate emits for the Gpr32 masked-add, \
         replacing AND + ADD.4S; NEGATED-sum accumulators folded by one wrapping SubRR) and \
         NeonUadalpV (UADALP .4S -> .2D — the tied-accumulator pairwise widen the neon_array \
         TRACK D abs-sum accumulate emits, replacing the UADDW/UADDW2 pair; adjacent-pair \
         grouping is a pure mod-2^64 reassociation under the both-lanes drain), NEW array \
         members classified EmittableNeedsProof and covered via their faithful D-pair \
         obligations (all_neon_mla_proofs: MLS-confusion / MUL-no-accumulate / lane-swap \
         refutes; all_neon_uadalp_proofs: SADALP-sign-confusion / UADDLP-no-accumulate / \
         wrong-pairing refutes). \
         The +6 to 285 are the volatile LDR/STR forms; all are denominator-bearing \
         DeferredUnfaithfulModel RED rows because plain load/store evidence does not \
         cover the volatile observation/ordering boundary. The +2 to 287 are the \
         relocation-owned AddTprelHi12/AddTprelLo12 TLSLE skeletons, classified as \
         explicit structural exclusions; the enum-source comparison caught that these \
         classified variants were still missing from the audit array. \
         The +1 to 288 is AlignNop (emission-time loop-head alignment padding \
         that encodes to the architectural NOP 0xD503201F), a NEW array member \
         classified FailClosedAllowlisted: it carries no value/memory/branch \
         semantics to prove, its byte-exactness is enforced by the A64 \
         decode-check arm (word must equal 0xD503201F) and its offset integrity \
         by the EH `encoder offset == re-derived offset` cross-check; it is \
         created only at emission by loop_align, never selected by the lowerer. \
         The enum-source comparison caught that this classified variant was \
         still missing from the audit array. \
         The +2 to 290 are EorRRLsl/EorRRLsr (EOR Rd,Rn,Rm,LSL/LSR #k), \
         the shifted-source EOR fusion forms; both are classified \
         EmittableNeedsProof and covered through operand reconstruction with \
         W/X and wrong-kind/wrong-amount real-solver refute controls. \
         The accepted/emitted-value-effect headline is 155/246 with 91 explicit \
         DeferredUnfaithfulModel RED rows; see \
         aarch64_emittable_coverage_is_honest_under_strict.)"
    );
}

/// LOCKS IN universe completeness for x86-64, same rationale as the AArch64
/// counterpart. Source of truth: crates/trust-cg-ir/src/x86_64_ops.rs.
#[test]
fn x86_universe_has_no_duplicates_and_matches_pinned_count() {
    assert_inventory_matches_enum_source(
        "x86-64",
        "X86Opcode",
        include_str!("../../trust-cg-ir/src/x86_64_ops.rs"),
        ALL_X86_OPCODES,
    );
    assert_eq!(
        ALL_X86_OPCODES.len(),
        225,
        "x86-64 opcode count changed — a variant was added/removed. Update the array AND this \
         pinned count, and classify the new opcode in classify_x86 (the build already forced that). \
         (197 = 191 + the 2026-07-18 UNIVERSE BACKFILL of 6 opcodes that existed in the enum but \
         were missing from the array: JmpR, MovsxdRMSib, MovRipRelTlv, Cmpxchg8, Cmpxchg16, \
         Psadbw — the audit had been silently skipping them. The +16 to 216 are the \
         volatile scalar/GPR/XMM memory forms; all are inventoried denominator rows. \
         The +4 to 220 are the exact bounds/null/div-zero/shift-range proof carriers, \
         classified as explicit pre-encoding exclusions; the enum-source comparison \
         caught that they were still absent from the audit array. The +2 to 222 are \
         MovsdRMSib/MovssRMSib, the scaled-index scalar-FP loads: EmittableNeedsProof, \
         mapped by opcode_to_proof_query to the same MemLoad obligation as \
         MovsdRM/MovssRM over the same shared SibMemAddr effective-address \
         reconstruction that already proves MovRMSib — a composition of two proven \
         families, adding no new trust root. The +2 to 224 are the 8-bit SIB load/store \
         pair MovRM8Sib/MovMR8Sib; the +1 to 225 is RolRI. All three have real encoder, \
         decoder, differential, and reconstructed-proof coverage.)"
    );
}

// ===========================================================================
// 4b. THE GATE — RISC-V (RV64)
// ===========================================================================

/// Pins the RISC-V accepted/deferred/excluded inventory. Known named RED debt is
/// permitted; an unknown finding or denominator drift fails.
///
/// HONESTY (task #63, RISC-V): the 14 RISC-V dataflow ALU/shift/compare ops
/// (ADD/SUB/MUL/AND/OR/XOR/SLL/SRL/SRA, SLLI/SRLI, ADDI, SLT/SLTU) are now
/// CREDITED via OPERAND RECONSTRUCTION (mirroring the proven AArch64 pattern).
/// Their static "riscv: …" proofs are degenerate X==X self-equalities that prove
/// NOTHING; the gate no longer relies on them. Instead `audit_riscv` rebuilds the
/// machine side FROM THE REAL EMITTED OPCODE+OPERANDS, so a wrong isel choice
/// (ADD-as-SUB, SLL-as-SRL) or wrong non-commutative wiring REFUTES. The genuine
/// emittable surface therefore includes those 14 reconstructed opcodes plus
/// emitted LUI/XORI/SLTIU as three explicit RED rows until they gain individual
/// reconstruction bindings.
#[test]
fn riscv_inventory_pins_accepted_and_deferred_rows() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::RiscV));
    // Always print the full audit so the allowlist stays visible in CI logs.
    eprintln!("{}", report.audit_log());
    assert_eq!(
        report.emittable_count(),
        17,
        "RISC-V emitted value/effect denominator changed from 14 accepted + 3 deferred"
    );
    assert_eq!(
        report.covered_count(),
        14,
        "RISC-V accepted reconstruction count changed:\n{}",
        report.audit_log()
    );
    let failures = report.failures();
    assert_eq!(failures.len(), 3, "{}", report.failure_summary());
    let actual: std::collections::HashSet<_> = failures
        .iter()
        .map(|row| row.opcode_display.as_str())
        .collect();
    assert_eq!(
        actual,
        std::collections::HashSet::from(["riscv::Lui", "riscv::Xori", "riscv::Sltiu"]),
        "RISC-V RED debt changed; unknown drift must fail the inventory"
    );
    assert!(
        failures.iter().all(|row| matches!(
            &row.finding,
            Some(CoverageFinding::DeferredUnfaithfulModel { .. })
        )),
        "RISC-V expected debt must be explicitly deferred:\n{}",
        report.failure_summary()
    );
}

/// LOCKS IN universe completeness for RISC-V, same rationale as the AArch64 /
/// x86-64 counterparts. Source of truth: crates/trust-cg-ir/src/riscv_ops.rs.
#[test]
fn riscv_universe_has_no_duplicates_and_matches_pinned_count() {
    assert_inventory_matches_enum_source(
        "RISC-V",
        "RiscVOpcode",
        include_str!("../../trust-cg-ir/src/riscv_ops.rs"),
        ALL_RISCV_OPCODES,
    );
    // Release-baseline pin; the source comparison above is the systemic
    // completeness check. The RiscVOpcode::tests::opcode_count test pins 83 too.
    assert_eq!(
        ALL_RISCV_OPCODES.len(),
        83,
        "RISC-V opcode count changed — a variant was added/removed. Update the array AND this \
         pinned count, and classify the new opcode in classify_riscv (the build already forced \
         that)."
    );
}

/// LOCKS IN the f81e45b NON-DEGENERACY guard for the RISC-V comparison IDIOMS:
/// each idiom proof's machine side is a genuinely composed multi-instruction
/// sequence (SUB+SLTIU, SUB+SLTU, SLT+XORI, swapped SLT/SLTU, ...) STRUCTURALLY
/// distinct from the trust_ir spec predicate. A degenerate `X == X` proof (the
/// f81e45b lie, where the machine side was built to mirror the spec) would
/// discharge trivially and prove nothing; this asserts the two sides differ for
/// every wired idiom binding. (The clean 1:1 ALU lowerings are deliberately NOT
/// asserted non-degenerate: their honest identity — both sides independently
/// computing the same bitvector op — is meaningful and pins the emitted opcode,
/// exactly as the existing gate does for plain AArch64/x86 ALU.)
#[test]
fn riscv_idiom_bindings_are_non_degenerate() {
    use trust_cg_verify::riscv_lowering_proofs::riscv_idiom_proofs;
    let idioms = riscv_idiom_proofs();
    assert!(
        !idioms.is_empty(),
        "expected RISC-V comparison-idiom proofs to be registered"
    );
    for p in &idioms {
        assert_ne!(
            p.trust_ir_expr, p.aarch64_expr,
            "RISC-V idiom proof '{}' has identical spec and machine sides (degenerate f81e45b X==X)",
            p.name
        );
    }
}

// ===========================================================================
// 4b. THE GATE — WebAssembly (stack machine, task #71)
// ===========================================================================

/// Pins the WebAssembly accepted/deferred/excluded inventory. Known named RED
/// debt is permitted; an unknown finding or denominator drift fails.
///
/// HONESTY (task #71): wasm was the 4th backend but OUTSIDE the gate (GateArch had
/// only AArch64/X86_64/RiscV). Its static lowering proofs were never strict-gated;
/// the int-ALU / div-rem / bitwise / FP-arith ones were degenerate X==X
/// self-equalities (`bvadd == bvadd`) that prove nothing. They are now SUPERSEDED
/// by STACK-MACHINE OPERAND RECONSTRUCTION: `audit_wasm` rebuilds the machine side
/// by DECODING the REAL emitted opcode BYTE over fresh symbolic value-stack
/// operands (`wasm_function_verifier`), so a wrong opcode byte (`i32.sub` for an
/// intended add) or a swapped non-commutative stack wiring REFUTES.
///
/// DENOMINATOR-HONESTY: all 29 value-bearing ops are `EmittableNeedsProof` (IN the
/// denominator). popcnt (×2, faithful ctpop), reinterpret (×4, width-preserving
/// bit-identity), and — after the FAITHFUL-CONVERSION fix — the 16 float<->int
/// conversions (8 int->FP convert + 8 saturating FP->int trunc_sat) are GENUINELY
/// RECONSTRUCTED and credited: the native evaluator now models rounding mode,
/// source signedness (zero-ext unsigned vs sign-ext signed) and saturation (clamp
/// to int range + NaN->0), so a signed-for-unsigned / saturating-for-wrapping /
/// NaN-mishandling lowering REFUTES. Only the 7 SIMD/v128 ops remain HONESTLY
/// DEFERRED — left RED — pending lane-vector semantics.
///
/// TRUE HONEST HEADLINE: 109 / 111 of the value-equivalence denominator. The two
/// emitted scalar constant forms remain explicit RED until their signed-LEB
/// immediates are independently decoded. The three reserved v128 load/store/const
/// forms are never selected and remain outside the denominator.
/// The four LANE-WISE v128 value ops (i32x4.add/mul, f32x4.add/mul) are now
/// faithfully reconstructed lane-wise (a wrong sub-opcode / lane width REFUTES).
#[test]
fn wasm_inventory_pins_accepted_and_deferred_rows() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::Wasm));
    // Always print the full audit so the allowlist stays visible in CI logs.
    eprintln!("{}", report.audit_log());

    // The denominator is the 111 value-bearing ops: 83 reconstructable scalar + 2
    // popcnt + 4 reinterpret + 8 int->FP convert + 8 saturating trunc + 4 SIMD
    // lane-wise value ops + 2 emitted scalar constants. The 3 reserved v128
    // forms (load/store/const) are never selected.
    assert_eq!(
        report.emittable_count(),
        111,
        "wasm emittable (value-equivalence denominator) count changed — it must include the 4 \
         SIMD lane-wise value ops and scalar constants but NOT the 3 never-selected v128 forms; update \
         deliberately. Re-check classify_wasm and wasm_function_verifier::opcode_to_source_op."
    );
    // COVERED = 83 scalar + 2 popcnt + 4 reinterpret + 16 conversion + 4 SIMD = 109,
    // all via reconstruction.
    assert_eq!(
        report.covered_count(),
        109,
        "wasm GENUINE covered count changed — must be 109 (83 scalar + 2 popcnt + 4 reinterpret + \
         16 conversions + 4 SIMD lane-wise), ALL credited via stack-machine reconstruction. Do NOT \
         inflate by crediting an op the evaluator cannot faithfully model.\n{}",
        report.audit_log()
    );
    assert!(
        (report.coverage_percent() - (109.0 / 111.0 * 100.0)).abs() < f64::EPSILON,
        "wasm coverage_percent must be the honest 109/111"
    );

    let failures = report.failures();
    assert_eq!(
        failures.len(),
        2,
        "wasm must have exactly the two scalar-constant RED rows:\n{}",
        report.failure_summary()
    );
    let actual: std::collections::HashSet<_> = failures
        .iter()
        .map(|row| row.opcode_display.as_str())
        .collect();
    assert_eq!(
        actual,
        std::collections::HashSet::from(["wasm::I32Const", "wasm::I64Const"])
    );
    assert!(
        failures.iter().all(|row| matches!(
            &row.finding,
            Some(CoverageFinding::DeferredUnfaithfulModel { .. })
        )),
        "wasm scalar constants must be explicit DeferredUnfaithfulModel debt"
    );
}

/// LOCKS IN universe completeness for WebAssembly, same rationale as the
/// AArch64 / x86-64 / RISC-V counterparts. Source of truth:
/// crates/trust-cg-ir/src/wasm_ops.rs (the `WasmOpcode::tests::opcode_count` pin).
#[test]
fn wasm_universe_has_no_duplicates_and_matches_pinned_count() {
    assert_inventory_matches_enum_source(
        "WebAssembly",
        "WasmOpcode",
        include_str!("../../trust-cg-ir/src/wasm_ops.rs"),
        ALL_WASM_OPCODES,
    );
    // Release-baseline pin; the source comparison above is the systemic
    // completeness check. The WasmOpcode::tests::opcode_count test pins 141 too.
    assert_eq!(
        ALL_WASM_OPCODES.len(),
        141,
        "wasm opcode count changed — a variant was added/removed. Update the array AND this \
         pinned count, and classify the new opcode in classify_wasm (the build already forced \
         that)."
    );
}

/// LOCKS IN the DENOMINATOR-HONEST wasm partition.
///
/// The value-equivalence denominator (classify_wasm EmittableNeedsProof) is now
/// exactly 111 opcodes: the 83 reconstructable scalar value ops + the value-
/// bearing ops that were wrongly allowlisted-out by the #71 bring-up (popcnt ×2,
/// reinterpret ×4, int->FP convert ×8, saturating trunc ×8, SIMD lane ops ×4)
/// plus the two emitted scalar constants. Only the
/// GENUINELY STRUCTURAL ops (locals/globals, memory, control flow,
/// calls) and the never-selected f.min/f.max are fail-closed-allowlisted with TRUE
/// reasons; nop/unreachable are pseudo. This pins the partition so a value-bearing
/// op can never again be silently allowlisted OUT of the denominator to inflate
/// the headline.
#[test]
fn wasm_classifier_partition_is_honest() {
    let mut emittable = 0usize;
    let mut allowlisted = 0usize;
    let mut pseudo = 0usize;
    for &op in ALL_WASM_OPCODES {
        match classify_wasm(op) {
            OpcodeClass::EmittableNeedsProof => emittable += 1,
            OpcodeClass::PseudoOrTrap => pseudo += 1,
            OpcodeClass::FailClosedAllowlisted { reason } => {
                assert!(
                    !reason.is_empty(),
                    "wasm::{op:?} allowlisted with an empty reason"
                );
                allowlisted += 1;
            }
        }
    }
    assert_eq!(
        emittable, 111,
        "the value-equivalence denominator is 109 accepted rows plus two emitted scalar constants; \
         the 3 reserved v128 load/store/const forms are never selected"
    );
    assert_eq!(
        pseudo, 2,
        "nop + unreachable are the only pseudo/trap wasm opcodes"
    );
    assert_eq!(
        allowlisted,
        ALL_WASM_OPCODES.len() - 111 - 2,
        "only GENUINELY-structural opcodes are fail-closed-allowlisted (no value-bearing op may \
         be allowlisted-out of the denominator); only the reserved never-selected v128 forms \
         stay excluded"
    );
}

/// LOCKS IN the v128 partition after lane-wise reconstruction:
///   * the 4 LANE-WISE value ops (i32x4.add/mul, f32x4.add/mul) are IN the
///     value-equivalence denominator (`EmittableNeedsProof`) and are GENUINELY
///     COVERED via reconstruction (no fake-cover, no deferral);
///   * the 3 reserved forms (v128.load/store/const) are never selected and are
///     allowlisted-OUT for that reason. Scalar constants are emitted and therefore
///     do not share this classification.
///     A regression that fake-covers a structural form, or fails to reconstruct a lane
///     op, breaks this pin.
#[test]
fn wasm_v128_lanewise_reconstructed_structural_allowlisted() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::Wasm));

    // (a) The 4 lane-wise value ops are EmittableNeedsProof AND COVERED via
    //     reconstruction (no finding).
    for op in [
        WasmOpcode::I32x4Add,
        WasmOpcode::I32x4Mul,
        WasmOpcode::F32x4Add,
        WasmOpcode::F32x4Mul,
    ] {
        assert!(
            matches!(classify_wasm(op), OpcodeClass::EmittableNeedsProof),
            "wasm::{op:?} v128 lane op must be EmittableNeedsProof (IN the denominator), got {:?}",
            classify_wasm(op)
        );
        let row = report
            .rows
            .iter()
            .find(|r| r.opcode_display == format!("wasm::{op:?}"))
            .unwrap_or_else(|| panic!("wasm::{op:?} must appear in the audit"));
        assert!(
            row.finding.is_none(),
            "wasm::{op:?} v128 lane op must be COVERED via reconstruction (no finding), got {:?}",
            row.finding
        );
        assert!(
            row.note.contains("RECONSTRUCTED"),
            "wasm::{op:?} must be credited via reconstruction: {}",
            row.note
        );
    }

    // (b) The 3 reserved v128 forms are allowlisted only because the current
    //     lowerer never selects V128 values.
    for op in [
        WasmOpcode::V128Load,
        WasmOpcode::V128Store,
        WasmOpcode::V128Const,
    ] {
        match classify_wasm(op) {
            OpcodeClass::FailClosedAllowlisted { reason } => assert!(
                reason.contains("never selected") && reason.contains("V128"),
                "wasm::{op:?} must disclose its never-selected V128 status: {reason}"
            ),
            other => panic!("wasm::{op:?} must be never-selected, got {other:?}"),
        }
    }

    for op in [WasmOpcode::I32Const, WasmOpcode::I64Const] {
        assert!(
            matches!(classify_wasm(op), OpcodeClass::EmittableNeedsProof),
            "wasm::{op:?} is emitted value materialization and must stay in the denominator"
        );
        let row = report
            .rows
            .iter()
            .find(|row| row.opcode_display == format!("wasm::{op:?}"))
            .unwrap_or_else(|| panic!("wasm::{op:?} missing from audit"));
        assert!(
            matches!(
                &row.finding,
                Some(CoverageFinding::DeferredUnfaithfulModel { .. })
            ),
            "wasm::{op:?} must remain explicit scalar-constant RED debt"
        );
    }
}

/// LOCKS IN that the wasm scalar value opcodes are EmittableNeedsProof
/// (reconstruction-credited, task #71) — they must never silently slip onto the
/// allowlist (which would drop them from the value-equivalence denominator).
#[test]
fn wasm_scalar_value_ops_are_emittable_needs_proof() {
    for op in [
        WasmOpcode::I32Add,
        WasmOpcode::I64Sub,
        WasmOpcode::I32DivS,
        WasmOpcode::I32Shl,
        WasmOpcode::I32LtS,
        WasmOpcode::F32Add,
        WasmOpcode::F64Div,
        WasmOpcode::F32Neg,
        WasmOpcode::F64Sqrt,
        WasmOpcode::F32Eq,
        WasmOpcode::I32WrapI64,
        WasmOpcode::I64ExtendI32S,
        WasmOpcode::F32DemoteF64,
    ] {
        assert!(
            matches!(classify_wasm(op), OpcodeClass::EmittableNeedsProof),
            "wasm::{op:?} must be EmittableNeedsProof (reconstruction-credited, task #71), got {:?}",
            classify_wasm(op)
        );
    }
}

/// LOCKS IN that popcnt + reinterpret are GENUINELY RECONSTRUCTED value-bearing
/// ops (EmittableNeedsProof, credited COVERED via stack-machine reconstruction) —
/// the denominator-honesty fix moved them OFF the allowlist and they now genuinely
/// discharge Valid (popcnt: faithful ctpop; reinterpret: width-preserving bit-
/// identity, wrong width refutes). They must never slip back onto the allowlist
/// (which would drop them from the denominator and inflate the headline).
#[test]
fn wasm_popcnt_and_reinterpret_are_reconstructed_covered() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::Wasm));
    for op in [
        WasmOpcode::I32Popcnt,
        WasmOpcode::I64Popcnt,
        WasmOpcode::I32ReinterpretF32,
        WasmOpcode::I64ReinterpretF64,
        WasmOpcode::F32ReinterpretI32,
        WasmOpcode::F64ReinterpretI64,
    ] {
        assert!(
            matches!(classify_wasm(op), OpcodeClass::EmittableNeedsProof),
            "wasm::{op:?} must be EmittableNeedsProof (value-bearing, in the denominator), got {:?}",
            classify_wasm(op)
        );
        let row = report
            .rows
            .iter()
            .find(|r| r.opcode_display == format!("wasm::{op:?}"))
            .unwrap_or_else(|| panic!("wasm::{op:?} must appear in the audit"));
        assert!(
            row.finding.is_none(),
            "wasm::{op:?} must be COVERED (reconstructed-Valid), got finding {:?}: {}",
            row.finding,
            row.note
        );
        assert!(
            row.note.contains("RECONSTRUCTED"),
            "wasm::{op:?} must be credited via reconstruction, got note: {}",
            row.note
        );
    }
}

/// LOCKS IN that the float<->int conversions + saturating truncations are now
/// FAITHFULLY DISCHARGED + COVERED (the deferred-conversion fix): value-bearing
/// ops kept IN the denominator (EmittableNeedsProof) and credited COVERED via
/// stack-machine reconstruction. The native evaluator now models rounding, source
/// signedness (zero-ext unsigned vs sign-ext signed) and saturation (clamp + NaN->0),
/// so a signed-for-unsigned / saturating-for-wrapping / NaN-mishandling lowering
/// REFUTES (proven by the reconstruction_wasm refutation tests). They must never
/// slip back to a DeferredUnfaithfulModel RED row nor onto the allowlist.
#[test]
fn wasm_conversions_are_reconstructed_covered() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::Wasm));
    for op in [
        // int->FP convert (signed + unsigned, i32/i64 source, f32/f64 dest).
        WasmOpcode::F32ConvertI32S,
        WasmOpcode::F32ConvertI32U,
        WasmOpcode::F32ConvertI64S,
        WasmOpcode::F32ConvertI64U,
        WasmOpcode::F64ConvertI32S,
        WasmOpcode::F64ConvertI32U,
        WasmOpcode::F64ConvertI64S,
        WasmOpcode::F64ConvertI64U,
        // saturating FP->int trunc_sat (signed + unsigned, f32/f64 source, i32/i64 dest).
        WasmOpcode::I32TruncSatF32S,
        WasmOpcode::I32TruncSatF32U,
        WasmOpcode::I32TruncSatF64S,
        WasmOpcode::I32TruncSatF64U,
        WasmOpcode::I64TruncSatF32S,
        WasmOpcode::I64TruncSatF32U,
        WasmOpcode::I64TruncSatF64S,
        WasmOpcode::I64TruncSatF64U,
    ] {
        // In the denominator, never allowlisted-out.
        assert!(
            matches!(classify_wasm(op), OpcodeClass::EmittableNeedsProof),
            "wasm::{op:?} conversion must be EmittableNeedsProof (in the denominator), got {:?}",
            classify_wasm(op)
        );
        let row = report
            .rows
            .iter()
            .find(|r| r.opcode_display == format!("wasm::{op:?}"))
            .unwrap_or_else(|| panic!("wasm::{op:?} must appear in the audit"));
        assert!(
            row.finding.is_none(),
            "wasm::{op:?} conversion must be COVERED (reconstructed-Valid), got finding {:?}: {}",
            row.finding,
            row.note
        );
        assert!(
            row.note.contains("RECONSTRUCTED"),
            "wasm::{op:?} conversion must be credited via reconstruction, got note: {}",
            row.note
        );
    }
}

/// LOCKS IN that the WasmLowering registered proofs are all GENUINELY
/// non-degenerate (the strict-gate honesty invariant for the registered witness
/// set): the 54 shift/comparison/float-comparison/negate/cast obligations whose
/// two sides are structurally distinct. No X==X self-equality may sneak back in.
#[test]
fn wasm_registered_proofs_are_non_degenerate() {
    use trust_cg_verify::proof_database::ProofCategory;
    let proofs = on_large_stack(|| {
        let db = ProofDatabase::new();
        db.by_category(ProofCategory::WasmLowering)
            .into_iter()
            .map(|p| {
                (
                    p.obligation.name.clone(),
                    p.obligation.is_genuinely_proven(),
                )
            })
            .collect::<Vec<_>>()
    });
    assert_eq!(
        proofs.len(),
        54,
        "the 54 genuine wasm refinement witnesses are registered"
    );
    for (name, genuine) in &proofs {
        assert!(
            genuine,
            "registered wasm proof '{name}' is degenerate (X==X)"
        );
    }
}

// ===========================================================================
// 5. The gate actually FAILS on a synthetic uncovered opcode (negative test)
// ===========================================================================

/// LOCKS IN that the gate is not vacuously green — it has teeth and would have
/// caught #68-fneg. We construct, by hand, the exact report row the gate emits
/// for "an emittable opcode with no proof mapping" (the #68-fneg shape: the
/// lowerer can emit `FnegRR`, but `opcode_to_proof_query` returns `None` and so
/// no proof is ever demanded), and assert the report machinery flags it as a
/// failure with an actionable summary.
#[test]
fn gate_reports_failure_for_an_emittable_opcode_with_no_proof() {
    use trust_cg_verify::coverage_gate::{
        CoverageFinding, CoverageReport, OpcodeAuditRow, OpcodeClass,
    };

    // The #68-fneg situation, reconstructed: an emittable opcode whose proof
    // query resolved to nothing.
    let bad_row = OpcodeAuditRow {
        opcode_display: "x86_64::SelectFneg(synthetic)".to_string(),
        class: OpcodeClass::EmittableNeedsProof,
        finding: Some(CoverageFinding::NoProofMapping),
        note: "no opcode_to_proof_query mapping".to_string(),
    };
    assert!(
        bad_row.is_failure(),
        "a NoProofMapping row must be a failure"
    );

    let report = CoverageReport {
        arch: GateArch::X86_64,
        rows: vec![bad_row],
    };
    assert!(
        !report.is_clean(),
        "a report with a NoProofMapping row must not be clean"
    );
    assert_eq!(report.failures().len(), 1);
    assert_eq!(report.coverage_percent(), 0.0);

    let summary = report.failure_summary();
    assert!(
        summary.contains("evidence inventory"),
        "failure summary must announce the RED evidence inventory: {summary}"
    );
    assert!(
        summary.contains("NO proof mapping") && summary.contains("#68-fneg"),
        "failure summary must name the #68-fneg class for the maintainer: {summary}"
    );
    assert!(
        summary.contains("Only encoder-rejected"),
        "failure summary must state the narrow exclusion policy: {summary}"
    );

    // And confirm the live mapping really does decline to cover the shape the
    // gate keys on: `FunctionVerifier::opcode_to_proof_query(Csinv)` is `None`.
    // CSINV is encoder-supported but never selected, so it remains excluded;
    // emitted CSEL/CSINC/CSNEG stay in the denominator as explicit RED debt
    // after their degenerate IfConversion obligations were retracted.
    assert!(
        trust_cg_verify::function_verifier::FunctionVerifier::opcode_to_proof_query(
            AArch64Opcode::Csinv,
        )
        .is_none(),
        "Csinv unexpectedly gained a value-proof mapping; revisit its allowlist rationale"
    );
}

// ===========================================================================
// 6. Coverage percentage is a meaningful, monotone signal
// ===========================================================================

/// LOCKS IN the HONEST STRICT emittable coverage (task #61, STRICT decision).
///
/// The ratio is computed over emitted value/effect forms (not the whole enum,
/// which includes pseudos and structural exclusions). Under STRICT, an opcode
/// counts as accepted ONLY when its obligation is structurally non-degenerate
/// (`trust_ir_expr != aarch64_expr`). The formerly-"genuine" 1:1 identities
/// (Iadd->ADD etc.) are X==X model-consistency checks and credit ZERO — so the
/// honest within-emittable coverage is NO LONGER 100%. Reconstruction credit
/// still requires the machine side to be rebuilt from the real opcode and
/// operands. The publication inventory pins:
///   * AArch64: 155/246 accepted, with 91 named RED rows.
///   * x86-64: 163/192 accepted, with 29 named RED rows.
///   * RISC-V: 14/17 accepted, with 3 named RED rows.
///   * WebAssembly: 109/111 accepted, with 2 named RED rows.
///     Re-admitting an X==X identity, fake-covering a non-reconstructable opcode, or
///     moving emitted value/effect debt out of the denominator trips this test.
#[test]
fn clean_tree_reports_honest_strict_emittable_coverage() {
    let (aa_cov, aa_em, x86_cov, x86_em, rv_cov, rv_em, wasm_cov, wasm_em) = on_large_stack(|| {
        let gate = CoverageGate::new();
        let aa = gate.audit(GateArch::AArch64);
        let x86 = gate.audit(GateArch::X86_64);
        let rv = gate.audit(GateArch::RiscV);
        let wasm = gate.audit(GateArch::Wasm);
        (
            aa.covered_count(),
            aa.emittable_count(),
            x86.covered_count(),
            x86.emittable_count(),
            rv.covered_count(),
            rv.emittable_count(),
            wasm.covered_count(),
            wasm.emittable_count(),
        )
    });
    // HONEST NUMBERS — genuine (non-degenerate / reconstructed-Valid) covered /
    // emittable. AArch64 = 42 static-DB (23 + ADRP/AddPCRel reloc + B/Bl/BL
    // branch26 + Adc/Sbc i128-carry-chain + LdrTlvp TLVP-PAGEOFF12 + LdrGot
    // GOT_LOAD-PAGEOFF12 + Adr jump-table PC-relative base + LdrswRO jump-table
    // scaled effective-address (AddressMode) + Ubfm/Sbfm bitfield-extract-ENCODING
    // + 5 NEON bitwise per-lane-intent proofs + the Fcmp FCMP→NZCV+CSET flag-model
    // proof + 15 NEON lane-wise D-pair compute proofs + 2 NEON popcount-fold D-pair
    // proofs (CntV + UaddlpV) + 1 NEON signed-abs D-pair proof (AbsV) + 1 NEON
    // dot-product-accumulate D-pair proof (UdotV) + 1 NEON byte-window extract op
    // (ExtV, credited by its 5 per-immediate D-pair proofs #1/#4/#8/#12/#15) + 2 NEON signed
    // add-long-pairwise D-pair proofs (SaddlpV) + 1 NEON bitwise insert-if-true
    // proof (BitV) + 5 NEON FP vector ops FaddV/FsubV/FmulV/FdivV/FcmgtV, credited
    // by the 30 per-lane FP LANE-PLUMBING obligations, both arrangements demanded)
    // + 41
    // reconstructed (23 integer ALU + 15 FP/div/madd + 2 FP-format casts + FmovImm
    // VFPExpandImm encoding) = 104/104 (FULL, gate is clean). The +1 vs the prior 103
    // is the signed add-long-pairwise op NeonSaddlpV, emitted by the widening
    // sext(i8/i16)->i32 reduction lowering (+1 to the denominator).
    // 111 -> 112 reconstructed: + the scalar FUSED multiply-add FMADD (the
    // llvm.fmuladd/fma lowering, credited by its single-rounding `fp.fma`
    // reconstruction; round-once vs round-twice refutes).
    // 112/112 -> 122/122 (UNIVERSE BACKFILL + neon_fpred lane proofs): +10
    // covered (FmaxnmRR/FminnmRR via the FpBinary Fmax/Fmin reconstruction +
    // FrintmRR/FrintpRR/FrintzRR via the unary-FP reconstruction + the 5
    // `.2D`-vectorizer NEON ops NeonFmlaV/FmlsV/ScvtfV/UcvtfV/DupScalarD via
    // their 10 faithful per-lane obligations, all_neon_fpred_proofs) and +10
    // emittable — back to covered == emittable, fully clean.
    // 122/122 -> 124/124 (two independent landings): UMOV EXTRACT — NeonUmovGen
    // moved allowlisted -> emittable, covered via its 30 faithful per-(size,lane)
    // obligations (all_neon_umov_proofs); and TLS GOT-TPREL — LdrGottprel ->
    // emittable, covered via aarch64_elf_tls_reloc_proofs (+1 universe too).
    // +2 covered, +2 emittable, still clean.
    // 124/124 -> 126/126 (FCVTL): NeonFcvtlV/NeonFcvtl2V — vector f32->f64
    // widen (low/high halves), covered via 4 faithful per-lane fpext
    // obligations (all_neon_fcvtl_proofs; wrong-half/wrong-lane refutes);
    // +2 universe, +2 covered, +2 emittable, still clean.
    // 126/126 -> 127/127 (EorRRShift): the rotate-fusion peephole's shifted-
    // register EOR-ROR, covered via its faithful rotate-XOR obligations
    // (all_eor_ror_shift_proofs, W+X; wrong-amount/wrong-shift-kind/operand-swap
    // refutes); +1 universe, +1 covered, +1 emittable, still clean.
    // 127/127 -> 128/128 (FcselRR): the FP-Select isel path's scalar FP
    // conditional select, covered via its faithful bit-preserving-mux obligations
    // (all_fcsel_proofs, S+D; inverted-cond/operand-swap refutes); +1 universe,
    // +1 covered, +1 emittable, still clean.
    // 128/128 -> 129/129 (NeonFmlaLaneV): the NEON FP fused multiply-accumulate
    // BY ELEMENT (FMLA Vd.T,Vn.T,Vm.Ts[lane]) the elementwise-FP vectorizer emits
    // for y[i]+=da*x[i] (da broadcast from a lane, no DUP), covered via its 20
    // faithful per-(arrangement,dest,selector) obligations (all_neon_fmla_lane_proofs,
    // .4S+.2D; wrong-lane-selector/FMLA<->FMLS polarity/accumulator-miswire refutes);
    // +1 universe, +1 covered, +1 emittable, still clean.
    // 129/129 -> 131/131 (AddRRShift, SubRRShift): the shift-ALU fusion peephole's
    // shifted-register ADD/SUB (ADD/SUB Rd,Rn,Rm,LSL #k), each covered via its
    // faithful ring obligations (all_add_sub_lsl_shift_proofs, W+X; wrong-amount /
    // ADD-vs-SUB / SUB operand-swap refutes); +2 universe, +2 covered, +2 emittable,
    // still clean.
    // 131/131 -> 135/135 (NeonSmlalV/NeonSmlal2V/NeonUmlalV/NeonUmlal2V): the NEON
    // widening multiply-accumulate-long (SMLAL/SMLAL2/UMLAL/UMLAL2 .4S -> .2D) the
    // neon_array widening-dot vectorizer emits for `s(i64) += ext(a_i32[i]) *
    // ext(b_i32[i])`, each covered via its faithful D-pair accumulate obligation
    // (all_neon_smlal_proofs; sign-confusion / no-accumulate / wrong-half /
    // truncating-mul refutes); +4 universe, +4 covered, +4 emittable, still clean.
    // 135/135 -> 137/137 (NeonUaddwV/NeonUaddw2V): the NEON widening add-wide
    // (UADDW/UADDW2 .4S -> .2D) the neon_array widening abs-sum vectorizer
    // (TRACK D) emits for `s(i64) += zext64(abs_bits(a_i32[i] [+ inv]))`,
    // each covered via its faithful D-pair obligation (all_neon_uaddw_proofs;
    // sign-confusion / no-addend / wrong-half / truncating-add refutes);
    // +2 universe, +2 covered, +2 emittable, still clean.
    // 137/137 -> 139/139 (NeonSaddwV/NeonSaddw2V): the NEON SIGNED widening
    // add-wide (SADDW/SADDW2 .4S -> .2D) the neon_predsum widening i64-acc
    // condsum emits for `s(i64) += (a_i32[iv] as i64) [if pred]`, each covered
    // via its faithful D-pair obligation (all_neon_saddw_proofs; zext-confusion
    // [SADDW-as-UADDW] / no-addend / wrong-half / truncating-add refutes);
    // +2 universe, +2 covered, +2 emittable, still clean.
    // 139/139 -> 140/140 (AddRRShiftLsr): the shift-ALU fusion peephole's
    // LSR-shifted ADD (ADD Rd,Rn,Rm,LSR #k — the srem/sdiv magic sign-bit
    // correction), covered via its faithful obligations (all_add_lsr_shift_proofs,
    // W+X; wrong-amount / ASR-not-LSR / LSL-not-LSR / SUB-not-ADD refutes);
    // +1 universe, +1 covered, +1 emittable, still clean.
    // 141/141 -> 143/143 (NeonMlaV + NeonUadalpV): the NEON vector
    // multiply-accumulate (MLA.4S, the neon_predsum MLA-by-mask condsum
    // accumulate) and pairwise widening accumulate (UADALP .4S -> .2D, the
    // neon_array TRACK D abs-sum accumulate), each covered via its faithful
    // D-pair obligation (all_neon_mla_proofs: MLS-confusion /
    // MUL-no-accumulate / lane-swap refutes; all_neon_uadalp_proofs:
    // SADALP-sign-confusion / UADDLP-no-accumulate / wrong-pairing refutes);
    // +2 universe, +2 covered, +2 emittable, still clean.
    // 143/143 -> 144 covered of 144 at that stage (NeonRbitV): the NEON
    // per-byte 8-bit reverse (RBIT.16B,
    // the neon-bitrev vectorizer's `a[i].reverse_bits()` over `[u8; N]`), covered
    // via its faithful D-pair obligation (proof_neon_rbitv_16b: identity /
    // byte-swap [REV16.8B] / 16-bit-lane-reverse [wrong-width] refutes); +1
    // universe, +1 covered, +1 emittable. Publication re-audit then withdrew
    // opcode-wide MOVN/MOVK credit. The publication audit then restored all
    // emitted value/effect forms to the denominator, producing 145/238. The six
    // volatile forms subsequently added to the enum are explicit RED rows,
    // yielding the 151/244 inventory. NeonRev32V then left the deferred set
    // (faithful per-byte within-32-bit-word reverse obligations at both emitted
    // arrangements, .16B and .8B), giving 151/244. EorRRLsl/EorRRLsr then add
    // two reconstructed shifted-source forms, giving 153/246. Umull then left
    // the deferred set via its faithful widening obligation, giving 154/246;
    // complete packed-NZCV TST authority removes another RED row. The combined
    // current inventory is therefore 155/246 with 91 explicit RED rows.
    assert_eq!(
        (aa_cov, aa_em),
        (155, 246),
        "AArch64 accepted-obligation inventory changed; update the pins deliberately \
         — do NOT re-admit X==X identities NOR fake-cover a non-reconstructable opcode"
    );
    assert_eq!(
        (x86_cov, x86_em),
        (163, 192),
        "x86-64 strict emittable coverage changed; update the pinned honest numbers deliberately \
         — do NOT re-admit X==X identities NOR fake-cover a non-reconstructable opcode. x86-64 is \
         now at honest 163/192: 13 actively emitted former exclusions and 16 volatile memory \
         forms are explicit DeferredUnfaithfulModel RED rows. The 155 -> 157 net (X10): the 32-bit \
         SIB MOV pair MovRM32Sib/MovMR32Sib joins the memory tier via the SAME SibMemAddr EA \
         reconstruction at I32 width (wrong base/index/scale/disp/width REFUTES). The \
         154 -> 155 net (X9 slice 3): \
         ImulRMSib, the scaled-index sibling of ImulRM produced by the RM-fusion peephole, joins \
         the memory-ALU family — same Imul low-half value proof, SIB EA covered by the SAME \
         independent `x86_reconstruct_effective_address` SibMemAddr encoders as MovRMSib (wrong \
         base/index/scale/disp REFUTES). The 151 -> 154 net (OPT-12 / VEC-Q): \
         PSLLQ/PSRLQ (new i64x2 uniform-immediate shifts, static-DB proofs parallel to \
         PSLLD/PSRLD) +2/+2, and PMULUDQ FailClosedAllowlisted -> EmittableNeedsProof +1/+1 \
         (faithful same-width i64x2 lane model `lo32(a)*lo32(b)` vs the INDEPENDENT SDM \
         even-dword-extract/zext/mul machine model; odd-lane / sign-extend / low-half wrong \
         models REFUTE). The 149 -> 151 net (OPT-7): the scaled- \
         index 64-bit memory MOVs MovRMSib/MovMRSib flip FailClosedAllowlisted -> EmittableNeedsProof \
         (+2/+2), COVERED by the SAME Load_I64/Store_I64 effective-address memory proofs as \
         MovRM/MovMR (`x86_reconstruct_effective_address` already models the SibMemAddr \
         `base+index*scale+disp` EA on both the trust_ir and INDEPENDENT machine encoders; a wrong \
         base/index/scale/disp REFUTES). The earlier 148 -> 149 net: MFENCE (SeqCst \
         fence, slice 3) is a single-thread no-op whose only faithful value proof is X==X, so it is \
         correctly FailClosedAllowlisted (coverage NOT claimed, like RET/CALL) — slice 3 had wrongly \
         marked it EmittableNeedsProof, leaving it emittable-but-uncoverable (the clean-tree gate was \
         actually RED at 148/149); with Mfence allowlisted the base is a clean 148/148, and (+1) \
         CMPXCHG (compare_exchange, slice 4) flips FailClosedAllowlisted -> EmittableNeedsProof, \
         covered by the width-polymorphic Cmpxchg i32/i64 conditional-data-flow proofs (returns-old + \
         conditional-store + success-flag; the negative controls REFUTE). The growth 123 -> 139 is the MEMORY \
         tier (task #76): GENUINE effective-address reconstruction of loads/stores \
         (MovRM*/MovMR*/MovsdRM/MovssRM/MovsdMR/MovssMR), memory-ALU (AddRM/SubRM/CmpRM = reg OP \
         load(ea)), and in-place Inc/Dec, via the deterministic `SmtExpr::MemLoad` memory model. \
         The growth 139 -> 144 is the IMPLICIT-OPERAND tier: ImulRM (reg-mem multiply via the \
         memory-ALU family), Idiv/Div (the genuine double-width sext/zext RDX:RAX dividend with \
         sdiv/udiv quotient+remainder, precond divisor!=0 & no-overflow; IDIV-as-DIV refutes on a \
         negative dividend), and Cmovcc/Cmovcc32 (a genuine CMP+CMOV pair with a per-cc boolean \
         over the real ZF/SF/CF/OF/PF flags; a wrong cc refutes). The growth 144 -> 148 is the \
         PACKED 128-bit MOVE tier: MOVDQU/MOVDQA RM+MR whole-XMM spill/reload moves, \
         reconstructed as two 64-bit halves at ea/ea+8 (little-endian) via the same independent \
         effective-address encoders (MOVDQA carries the honest ea%16==0 precondition; a wrong \
         EA/half/offset/width/value refutes). NO X==X anywhere"
    );
    assert_eq!(
        (rv_cov, rv_em),
        (14, 17),
        "RISC-V accepted/deferred inventory changed from 14/17; LUI/XORI/SLTIU must remain \
         denominator-bearing RED until individually reconstructed"
    );
    // wasm (task #71 + denominator-honesty + faithful-conversion + v128 lane-wise):
    // the 4th backend, a STACK MACHINE. COVERED = 83 scalar + 2 popcnt + 4
    // reinterpret + 16 conversion + 4 SIMD lane-wise = 109 (all via stack-machine
    // reconstruction; wrong byte / width / wiring / signedness / saturation / NaN /
    // SIMD sub-opcode / lane-width REFUTES). The 3 STRUCTURAL v128 forms
    // (load/store/const) are never-selected and allowlisted-OUT, while scalar
    // constants add two denominator-bearing RED rows. TRUE HONEST
    // HEADLINE: 109/111.
    assert_eq!(
        (wasm_cov, wasm_em),
        (109, 111),
        "wasm emittable coverage changed from the honest 109/111 — a reconstructable opcode stopped \
         discharging Valid (bad), or a value-bearing op was allowlisted-OUT of the denominator to \
         inflate the headline (forbidden), or a structural v128 form was wrongly put back IN the \
         denominator. Update deliberately."
    );
}

/// LOCKS IN the task #61 honesty fix at the DISCHARGE layer: a degenerate proof
/// (`trust_ir_expr == aarch64_expr`, an X==X self-equality not on
/// GENUINE_IDENTITY_ALLOWLIST) must NOT count as coverage even though it
/// evaluates `Valid` trivially. We reconstruct exactly the row the gate emits
/// when an EmittableNeedsProof opcode's matched proof is degenerate and assert
/// the report machinery flags it as a NON-covered failure (the honest signal).
/// This is the negative test that locks in: a future degenerate proof bound to
/// an emittable opcode can never inflate the covered count.
#[test]
fn degenerate_backed_opcode_does_not_count_as_coverage() {
    use trust_cg_verify::coverage_gate::{
        CoverageFinding, CoverageReport, OpcodeAuditRow, OpcodeClass,
    };

    let degen_row = OpcodeAuditRow {
        opcode_display: "riscv::Add(synthetic)".to_string(),
        class: OpcodeClass::EmittableNeedsProof,
        finding: Some(CoverageFinding::DegenerateProof {
            proof_name: "riscv: Iadd_I64 -> ADD".to_string(),
        }),
        note: "DEGENERATE (X==X, not genuine)".to_string(),
    };
    assert!(
        degen_row.is_failure(),
        "a DegenerateProof row must be a failure (NOT coverage)"
    );

    let report = CoverageReport {
        arch: GateArch::RiscV,
        rows: vec![degen_row],
    };
    // The degenerate-backed opcode is NOT counted as covered.
    assert_eq!(
        report.covered_count(),
        0,
        "a degenerate proof must not count as covered"
    );
    assert_eq!(report.coverage_percent(), 0.0);
    assert!(
        !report.is_clean(),
        "a report with a degenerate-backed row is not clean"
    );

    let summary = report.failure_summary();
    assert!(
        summary.contains("DEGENERATE") && summary.contains("proves NOTHING"),
        "failure summary must name the degeneracy and that it proves nothing: {summary}"
    );
}

/// LOCKS IN that emitted value/effect opcodes whose old model was a degenerate
/// X==X remain in the denominator as explicit RED rows. Only typed aliases and
/// structural control forms may remain excluded.
#[test]
fn degenerate_backed_opcodes_are_honestly_allowlisted_with_disclosing_reason() {
    // AArch64 canonical emitted value/effect forms stay proof-required.
    let aarch64_degen = [
        AArch64Opcode::MovR,
        AArch64Opcode::FmovFprFpr,
        AArch64Opcode::Csel,
        AArch64Opcode::Csinc,
        AArch64Opcode::Csneg,
        AArch64Opcode::LdrRI,
        AArch64Opcode::LdrbRI,
        AArch64Opcode::LdrhRI,
        AArch64Opcode::LdrsbRI,
        AArch64Opcode::LdrshRI,
        AArch64Opcode::LdrRO,
        AArch64Opcode::StrRI,
        AArch64Opcode::StrbRI,
        AArch64Opcode::StrhRI,
        AArch64Opcode::StrRO,
    ];
    for op in aarch64_degen {
        assert!(
            matches!(classify_aarch64(op), OpcodeClass::EmittableNeedsProof),
            "AArch64::{op:?} is emitted value/effect debt and must stay in the denominator"
        );
    }

    // Typed aliases are never selected, and RET is a structural control edge.
    for op in [
        AArch64Opcode::MOVWrr,
        AArch64Opcode::MOVXrr,
        AArch64Opcode::STRWui,
        AArch64Opcode::STRXui,
        AArch64Opcode::STRSui,
        AArch64Opcode::STRDui,
        AArch64Opcode::Ret,
    ] {
        match classify_aarch64(op) {
            OpcodeClass::FailClosedAllowlisted { reason } => {
                assert!(
                    !reason.trim().is_empty(),
                    "AArch64::{op:?}: empty exclusion reason"
                )
            }
            other => panic!("AArch64::{op:?} should be explicitly excluded, got {other:?}"),
        }
    }

    // x86: MovRI is emitted value materialization and therefore remains explicit
    // RED denominator debt. Jmp/Call/Ret are structural control edges. (Lea /
    // LeaSib are NO LONGER in this list — they
    // are now CREDITED via operand reconstruction: the machine side is rebuilt
    // from the real effective-address encoder over fresh symbolic base/index, and
    // a wrong scale/disp refutes. MovRI stays HONESTLY DEFERRED — const==const
    // with no independent constant model in the single instruction.)
    assert!(
        matches!(
            classify_x86(X86Opcode::MovRI),
            OpcodeClass::EmittableNeedsProof
        ),
        "x86_64::MovRI is emitted value materialization and must stay in the denominator"
    );
    for op in [X86Opcode::Jmp, X86Opcode::Call, X86Opcode::Ret] {
        match classify_x86(op) {
            OpcodeClass::FailClosedAllowlisted { reason } => assert!(
                reason.contains("KNOWN_DEGENERATE") && reason.contains("coverage NOT claimed"),
                "x86_64::{op:?}: allowlist reason must disclose the degeneracy, got: {reason}"
            ),
            other => panic!(
                "x86_64::{op:?} is degenerate-backed (task #61) and must be FailClosedAllowlisted, \
                 got {other:?}"
            ),
        }
    }

    // RISC-V (task #63): the 14 dataflow ALU/shift/compare ops are NO LONGER in
    // this degenerate-allowlist list — they are now CREDITED via operand
    // reconstruction (machine side rebuilt from the REAL emitted opcode+operands,
    // shifts hardware-amount-masked under a load-bearing amount<width precond), so
    // they are EmittableNeedsProof + COVERED rather than degenerate-allowlisted.
    // Assert exactly that reclassification so a regression to the degenerate
    // allowlist is caught.
    for op in [
        RiscVOpcode::Add,
        RiscVOpcode::Sub,
        RiscVOpcode::Mul,
        RiscVOpcode::And,
        RiscVOpcode::Or,
        RiscVOpcode::Xor,
        RiscVOpcode::Sll,
        RiscVOpcode::Srl,
        RiscVOpcode::Sra,
        RiscVOpcode::Slli,
        RiscVOpcode::Srli,
        RiscVOpcode::Addi,
        RiscVOpcode::Slt,
        RiscVOpcode::Sltu,
    ] {
        assert!(
            matches!(classify_riscv(op), OpcodeClass::EmittableNeedsProof),
            "riscv::{op:?} must be EmittableNeedsProof (reconstruction-credited, task #63), \
             got {:?}",
            classify_riscv(op)
        );
    }
}

// ===========================================================================
// 7. Width-polymorphic opcodes demand BOTH widths, width-correctly
// ===========================================================================

/// Extract the encoded destination width (32 or 64) a proof name represents.
///
/// All width-polymorphic proofs encode the width in their trust_ir op name:
/// `..._to_I32` / `..._to_I64` for extensions, `Imul_I32_Imm` / `Imul_I64_Imm`
/// for the 3-operand IMUL. (The byte/word MOVSX/MOVZX proofs — now ALL under
/// X8664Lowering for both widths — additionally carry an `r32`/`r64` mnemonic,
/// but the `_I{n}` token is the robust, category-independent width signal.)
fn encoded_width_of(proof_name: &str) -> Option<u32> {
    for (token, width) in [
        ("_to_I64", 64u32),
        ("_to_I32", 32),
        ("_I64_Imm", 64),
        ("_I32_Imm", 32),
    ] {
        if proof_name.contains(token) {
            return Some(width);
        }
    }
    None
}

/// LOCKS IN the reviewer's SOUNDNESS finding: the byte/word MOVSX/MOVZX opcodes
/// ENCODE i*->i64 (REX.W; encode.rs ~1910) and the GEP-path 3-operand IMUL
/// encodes i64, yet the verifier/gate previously bound only the i32 proof — so
/// an i64-MOVSX/MOVZX/IMUL bug would have passed against a DIFFERENT-width proof.
///
/// This asserts the gate now requires BOTH widths, and — crucially — that the
/// matched proof's ENCODED width equals the width the `WidthProof` table claims,
/// so neither width is silently bound to the wrong-width proof. Before the fix
/// `x86_width_polymorphic_proofs` did not exist and the gate matched a single
/// (i32) proof; this test fails to compile/pass without the fix.
#[test]
fn width_polymorphic_opcodes_require_both_widths_width_correctly() {
    let db = on_large_stack(ProofDatabase::new);

    for opcode in [
        X86Opcode::Movzx,
        X86Opcode::MovzxW,
        X86Opcode::MovsxB,
        X86Opcode::MovsxW,
        X86Opcode::ImulRRI,
    ] {
        let proofs = x86_width_polymorphic_proofs(opcode).unwrap_or_else(|| {
            panic!("{opcode:?} must be width-polymorphic (require both widths)")
        });

        // Both an i32 and an i64 obligation must be demanded.
        let widths: Vec<u32> = proofs.iter().map(|p| p.encoded_width_bits).collect();
        assert!(
            widths.contains(&32) && widths.contains(&64),
            "{opcode:?} must require BOTH i32 and i64 proofs, got widths {widths:?}"
        );

        for wp in proofs {
            let candidates = db.by_category(wp.category);
            let matched = candidates
                .iter()
                .find(|p| p.obligation.name.contains(wp.query))
                .unwrap_or_else(|| {
                    panic!(
                        "{opcode:?}: required proof {:?} not found in {:?}",
                        wp.query, wp.category
                    )
                });

            // The matched proof's ENCODED width must equal the width the gate
            // claims this query represents — this is the exact soundness check:
            // an i64 query must match a proof that models the i64 operation.
            let matched_width = encoded_width_of(&matched.obligation.name).unwrap_or_else(|| {
                panic!(
                    "{opcode:?}: cannot parse encoded width from matched proof {:?}",
                    matched.obligation.name
                )
            });
            assert_eq!(
                matched_width, wp.encoded_width_bits,
                "{opcode:?}: query {:?} matched proof {:?} whose encoded width {} != claimed {}",
                wp.query, matched.obligation.name, matched_width, wp.encoded_width_bits
            );
        }
    }
}

/// RESIDUAL B: the i64 byte/word MOVSX/MOVZX coverage is now attributed to
/// x86-SPECIFIC proofs (REX.W `MOVSX/MOVZX r64`) under `X8664Lowering`, NOT to
/// the AArch64-mnemonic `ExtensionTruncation` (SXTB/UXTH) rows it borrowed
/// before. This pins, for each i64 byte/word extend, that the gate demands the
/// proof from the x86 registry AND that the matched proof is the x86 one (its
/// name carries the `MOVSX r64`/`MOVZX r64` mnemonic) and DISCHARGES.
#[test]
fn i64_byte_word_extends_are_x86_specific_proofs_and_discharge() {
    use trust_cg_verify::lowering_proof::verify_by_evaluation;
    use trust_cg_verify::proof_database::ProofCategory;
    use trust_cg_verify::verify::VerificationResult;

    let db = on_large_stack(ProofDatabase::new);

    // (opcode, expected i64 query, expected x86 mnemonic in the proof name).
    let cases = [
        (X86Opcode::Movzx, "Uextend_I8_to_I64", "MOVZX r64,r/m8"),
        (X86Opcode::MovzxW, "Uextend_I16_to_I64", "MOVZX r64,r/m16"),
        (X86Opcode::MovsxB, "Sextend_I8_to_I64", "MOVSX r64,r/m8"),
        (X86Opcode::MovsxW, "Sextend_I16_to_I64", "MOVSX r64,r/m16"),
    ];

    for (opcode, i64_query, mnemonic) in cases {
        let proofs = x86_width_polymorphic_proofs(opcode)
            .unwrap_or_else(|| panic!("{opcode:?} must be width-polymorphic"));
        let i64_entry = proofs
            .iter()
            .find(|p| p.encoded_width_bits == 64)
            .unwrap_or_else(|| panic!("{opcode:?} must demand an i64 proof"));

        // The i64 entry must route to the x86 registry, NOT ExtensionTruncation.
        assert_eq!(
            i64_entry.category,
            ProofCategory::X8664Lowering,
            "{opcode:?}: i64 byte/word extend must bind an X8664Lowering proof, not {:?}",
            i64_entry.category
        );
        assert_eq!(i64_entry.query, i64_query, "{opcode:?}: wrong i64 query");

        // The matched proof must be the x86-specific REX.W r64 proof and discharge.
        let candidates = db.by_category(ProofCategory::X8664Lowering);
        let matched = candidates
            .iter()
            .find(|p| p.obligation.name.contains(i64_query))
            .unwrap_or_else(|| {
                panic!("{opcode:?}: x86 proof {i64_query:?} not registered in X8664Lowering")
            });
        assert!(
            matched.obligation.name.contains(mnemonic),
            "{opcode:?}: matched proof {:?} is not the x86 REX.W form ({mnemonic})",
            matched.obligation.name
        );
        assert!(
            matches!(
                verify_by_evaluation(&matched.obligation),
                VerificationResult::Valid
            ),
            "{opcode:?}: x86 i64 extend proof {:?} must DISCHARGE",
            matched.obligation.name
        );
    }
}

// ===========================================================================
// 6. Newly-wired SSE2/SSE4.1 packed-integer opcodes (#1111) — each resolves to
//    a REGISTERED, DISCHARGING proof of the CORRECT width/lane.
// ===========================================================================

/// LOCKS IN the iron rule for the wired x86 packed family: every newly-wired
/// packed opcode (PAND/POR, PADD/PSUB{B,W,D,Q}, PCMPEQ/PCMPGT{B,W,D},
/// PSLLD/PSRLD/PSRAD) is classified `EmittableNeedsProof`, resolves through the
/// SAME `X86FunctionVerifier::opcode_to_proof_query` the verifier uses, and the
/// matched proof both (a) carries the EXACT lane/width mnemonic the opcode
/// encodes and (b) DISCHARGES. A wrong-width / wrong-lane / vacuous binding —
/// the cardinal sin — is exactly what (a) catches.
#[test]
fn x86_wired_packed_opcodes_resolve_to_width_lane_exact_discharging_proofs() {
    use trust_cg_verify::lowering_proof::verify_by_evaluation;
    use trust_cg_verify::proof_database::ProofCategory;
    use trust_cg_verify::verify::VerificationResult;
    use trust_cg_verify::x86_64_function_verifier::X86FunctionVerifier;

    // (opcode, expected query substring, a UNIQUE lane/width discriminator that
    // must appear in the matched proof name). The discriminator pins the lane
    // width so a same-category-wrong-width binding cannot pass.
    let cases = [
        // Full-width bitwise.
        (X86Opcode::Pand, "V128 Band -> PAND xmm,xmm", "PAND"),
        (X86Opcode::Por, "V128 Bor -> POR xmm,xmm", "POR"),
        // Lane-exact add / sub — the PADD?/PSUB? mnemonic IS the lane width.
        (X86Opcode::Paddb, "V16I8Add -> PADDB", "PADDB"),
        (X86Opcode::Paddw, "V8I16Add -> PADDW", "PADDW"),
        (X86Opcode::Paddd, "V4I32Add -> PADDD", "PADDD"),
        (X86Opcode::Paddq, "V2I64Add -> PADDQ", "PADDQ"),
        (X86Opcode::Psubb, "V16I8Sub -> PSUBB", "PSUBB"),
        (X86Opcode::Psubw, "V8I16Sub -> PSUBW", "PSUBW"),
        (X86Opcode::Psubd, "V4I32Sub -> PSUBD", "PSUBD"),
        (X86Opcode::Psubq, "V2I64Sub -> PSUBQ", "PSUBQ"),
        // Lane-exact equal / signed-greater compare masks (Eq / Sgt are the only
        // single-instruction conditions).
        (
            X86Opcode::Pcmpeqb,
            "V16I8Icmp_Eq -> PCMPEQB",
            "V16I8Icmp_Eq",
        ),
        (
            X86Opcode::Pcmpeqw,
            "V8I16Icmp_Eq -> PCMPEQW",
            "V8I16Icmp_Eq",
        ),
        (
            X86Opcode::Pcmpeqd,
            "V4I32Icmp_Eq -> PCMPEQD",
            "V4I32Icmp_Eq",
        ),
        (
            X86Opcode::Pcmpgtb,
            "V16I8Icmp_Sgt -> PCMPGTB",
            "V16I8Icmp_Sgt",
        ),
        (
            X86Opcode::Pcmpgtw,
            "V8I16Icmp_Sgt -> PCMPGTW",
            "V8I16Icmp_Sgt",
        ),
        (
            X86Opcode::Pcmpgtd,
            "V4I32Icmp_Sgt -> PCMPGTD",
            "V4I32Icmp_Sgt",
        ),
        // Uniform-immediate dword shifts.
        (
            X86Opcode::Pslld,
            "V4I32 Ishl uniform immediate -> PSLLD",
            "PSLLD",
        ),
        (
            X86Opcode::Psrld,
            "V4I32 Ushr uniform immediate -> PSRLD",
            "PSRLD",
        ),
        (
            X86Opcode::Psrad,
            "V4I32 Sshr uniform immediate -> PSRAD",
            "PSRAD",
        ),
        // Uniform-immediate qword shifts + the PMULUDQ faithful i64x2 lane
        // model (the SSE2 vectorizer's packed 64-bit multiply compose).
        (
            X86Opcode::Psllq,
            "V2I64 Ishl uniform immediate -> PSLLQ",
            "PSLLQ",
        ),
        (
            X86Opcode::Psrlq,
            "V2I64 Ushr uniform immediate -> PSRLQ",
            "PSRLQ",
        ),
        (
            X86Opcode::Pmuludq,
            "V2I64 even-dword widening Umul -> PMULUDQ",
            "PMULUDQ",
        ),
    ];

    let db = on_large_stack(ProofDatabase::new);
    let candidates = db.by_category(ProofCategory::X8664Lowering);

    for (opcode, expected_query, discriminator) in cases {
        // Must be classified emittable-needs-proof (not allowlisted).
        assert!(
            matches!(classify_x86(opcode), OpcodeClass::EmittableNeedsProof),
            "{opcode:?} must be EmittableNeedsProof after wiring"
        );

        // Must resolve through the SAME mapping the verifier uses.
        let query = X86FunctionVerifier::opcode_to_proof_query(opcode)
            .unwrap_or_else(|| panic!("{opcode:?}: opcode_to_proof_query returned None"));
        assert_eq!(
            query, expected_query,
            "{opcode:?}: wired query changed (soundness anchor)"
        );

        // x86 verifier matches case-SENSITIVE `contains`.
        let matched = candidates
            .iter()
            .find(|p| p.obligation.name.contains(query))
            .unwrap_or_else(|| {
                panic!("{opcode:?}: no registered X8664Lowering proof matching {query:?}")
            });

        // The matched proof must carry the EXACT lane/width discriminator — this
        // is the width/lane-exactness check that rejects a wrong-width binding.
        assert!(
            matched.obligation.name.contains(discriminator),
            "{opcode:?}: matched proof {:?} lacks lane/width discriminator {discriminator:?}",
            matched.obligation.name
        );

        // And it must DISCHARGE.
        assert!(
            matches!(
                verify_by_evaluation(&matched.obligation),
                VerificationResult::Valid
            ),
            "{opcode:?}: bound packed proof {:?} must DISCHARGE",
            matched.obligation.name
        );
    }
}

/// LOCKS IN that the actively emitted packed opcodes without faithful models stay
/// in the denominator as explicit RED rows. These cannot be reconstructed as a
/// clean per-lane scalar op:
/// PSHUFD (imm8 shuffle), PBLENDVB (mask reg), PTEST/PMOVMSKB (cross-lane flag/
/// sign reductions), PUNPCK*/PACKUSWB (interleave/narrow shuffles), and MOVDQA
/// register copy. PINSR*/PEXTR* remain excluded because they are never selected.
///
/// NOTE: PANDN, PCMPEQQ, PCMPGTQ, PMULLW, PMULLD were PROMOTED out of this list —
/// they are now GENUINELY RECONSTRUCTED lane-wise (see
/// `x86_packed_value_ops_are_lanewise_reconstructed`). PMULUDQ was likewise
/// PROMOTED OUT — it is a same-width i64x2 lane op on the qword lanes' low
/// dwords, backed by the refutable static-DB proof
/// `V2I64 even-dword widening Umul -> PMULUDQ` (see
/// `x86_wired_packed_opcodes_resolve_to_width_lane_exact_discharging_proofs`).
/// Do NOT re-add any of them here.
#[test]
fn x86_emitted_deferred_packed_opcodes_stay_red() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::X86_64));
    for op in [
        X86Opcode::Pshufd,
        X86Opcode::Pmovmskb,
        // MovdqaRR (register-register) stays separate explicit RED debt; the MEMORY forms
        // MovdqaRM/MovdqaMR (and MovdquRM/MovdquMR) are PROMOTED OUT — they are now
        // genuinely reconstructed as two 64-bit halves at ea/ea+8 (see
        // `x86_packed_128bit_moves_are_reconstructed`). Do NOT re-add RM/MR here.
        X86Opcode::MovdqaRR,
        X86Opcode::Punpckldq,
        X86Opcode::Punpcklqdq,
        X86Opcode::Punpcklbw,
        X86Opcode::Punpckhbw,
        X86Opcode::Pblendvb,
        X86Opcode::Ptest,
        X86Opcode::Packuswb,
    ] {
        assert!(
            matches!(classify_x86(op), OpcodeClass::EmittableNeedsProof),
            "{op:?} is actively emitted value/effect debt and must stay in the denominator"
        );
        let row = report
            .rows
            .iter()
            .find(|row| row.opcode_display == format!("x86_64::{op:?}"))
            .unwrap_or_else(|| panic!("x86_64::{op:?} missing from audit"));
        assert!(
            matches!(
                &row.finding,
                Some(CoverageFinding::DeferredUnfaithfulModel { .. })
            ),
            "x86_64::{op:?} must be explicit deferred RED debt: {row:?}"
        );
    }

    // These lane insert/extract opcodes are encodable but have no current
    // producer; they remain excluded with an exact never-selected reason.
    for op in [
        X86Opcode::Pinsrd,
        X86Opcode::Pextrd,
        X86Opcode::Pinsrq,
        X86Opcode::Pextrq,
    ] {
        match classify_x86(op) {
            OpcodeClass::FailClosedAllowlisted { reason } => {
                assert!(reason.contains("never selected"), "{op:?}: {reason}")
            }
            other => panic!("{op:?} is never selected and should be excluded, got {other:?}"),
        }
    }
}

/// LOCKS IN that the whole-XMM 128-bit MEMORY moves MOVDQU{RM,MR} (unaligned) and
/// MOVDQA{RM,MR} (aligned) are EmittableNeedsProof AND credited COVERED via GENUINE
/// two-64-bit-halves-at-ea/ea+8 reconstruction — NEVER an X==X vacuous vouch. The
/// machine addresses come from the INDEPENDENT x86 `encode_lea_*` encoder; a wrong
/// EA / swapped half / wrong offset / wrong width / (store) wrong value REFUTES
/// (see tests/reconstruction_x86.rs). MOVDQARR (register-register) is a separate
/// emitted value row and remains explicit deferred RED debt. This pins the honest
/// credit so a regression that drops the reconstruction (or re-defers the memory
/// forms) is caught.
#[test]
fn x86_packed_128bit_moves_are_reconstructed() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::X86_64));
    for op in [
        X86Opcode::MovdquRM,
        X86Opcode::MovdquMR,
        X86Opcode::MovdqaRM,
        X86Opcode::MovdqaMR,
    ] {
        assert!(
            matches!(classify_x86(op), OpcodeClass::EmittableNeedsProof),
            "{op:?} must be EmittableNeedsProof (IN the value denominator), got {:?}",
            classify_x86(op)
        );
        let row = report
            .rows
            .iter()
            .find(|r| r.opcode_display == format!("x86_64::{op:?}"))
            .unwrap_or_else(|| panic!("x86_64::{op:?} must appear in the audit"));
        assert!(
            row.finding.is_none() && row.note.contains("RECONSTRUCTED"),
            "x86_64::{op:?} must be COVERED via genuine two-halves reconstruction (never X==X): \
             finding={:?}, note={}",
            row.finding,
            row.note
        );
    }
    // MOVDQARR (register-register copy) is emitted and must stay denominator RED
    // until an independent 128-bit copy obligation lands.
    assert!(
        matches!(
            classify_x86(X86Opcode::MovdqaRR),
            OpcodeClass::EmittableNeedsProof
        ),
        "MovdqaRR (reg-reg copy) must stay in the emitted value denominator"
    );
    let row = report
        .rows
        .iter()
        .find(|row| row.opcode_display == "x86_64::MovdqaRR")
        .expect("MovdqaRR must appear in the audit");
    assert!(matches!(
        &row.finding,
        Some(CoverageFinding::DeferredUnfaithfulModel { .. })
    ));
}

/// LOCKS IN that the GENUINELY-RECONSTRUCTED packed value ops are
/// EmittableNeedsProof AND credited COVERED via lane-wise reconstruction — the
/// MACHINE side rebuilt from the real packed encoder, the SOURCE side the trust_ir
/// scalar op `map_lanes`-applied at the matching arrangement. A wrong lane op /
/// width / predicate REFUTES (see tests/reconstruction_x86.rs). This pins the
/// honest credit so a regression that drops the reconstruction is caught.
#[test]
fn x86_packed_value_ops_are_lanewise_reconstructed() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::X86_64));
    for op in [
        // packed integer arithmetic
        X86Opcode::Paddb,
        X86Opcode::Paddw,
        X86Opcode::Paddd,
        X86Opcode::Paddq,
        X86Opcode::Psubb,
        X86Opcode::Psubw,
        X86Opcode::Psubd,
        X86Opcode::Psubq,
        X86Opcode::Pmullw,
        X86Opcode::Pmulld,
        // packed integer compare-mask (incl. q-lane)
        X86Opcode::Pcmpeqb,
        X86Opcode::Pcmpeqw,
        X86Opcode::Pcmpeqd,
        X86Opcode::Pcmpeqq,
        X86Opcode::Pcmpgtb,
        X86Opcode::Pcmpgtw,
        X86Opcode::Pcmpgtd,
        X86Opcode::Pcmpgtq,
        // full-width bitwise
        X86Opcode::Pand,
        X86Opcode::Por,
        X86Opcode::Pxor,
        X86Opcode::Pandn,
        X86Opcode::Andps,
        X86Opcode::Andpd,
        // packed FP
        X86Opcode::Addps,
        X86Opcode::Subps,
        X86Opcode::Mulps,
        X86Opcode::Divps,
        X86Opcode::Addpd,
        X86Opcode::Subpd,
        X86Opcode::Mulpd,
        X86Opcode::Divpd,
    ] {
        assert!(
            matches!(classify_x86(op), OpcodeClass::EmittableNeedsProof),
            "{op:?} must be EmittableNeedsProof (IN the value denominator), got {:?}",
            classify_x86(op)
        );
        let row = report
            .rows
            .iter()
            .find(|r| r.opcode_display == format!("x86_64::{op:?}"))
            .unwrap_or_else(|| panic!("x86_64::{op:?} must appear in the audit"));
        assert!(
            row.finding.is_none() && row.note.contains("RECONSTRUCTED"),
            "x86_64::{op:?} must be COVERED via lane-wise reconstruction: finding={:?}, note={}",
            row.finding,
            row.note
        );
    }
}

// ===========================================================================
// 7. Newly-wired AArch64 Csel + FP-trio (#1111).
// ===========================================================================

/// HONESTY (task #61) → CAPSTONE (task #62): the AArch64 conditional selects
/// CSEL/CSINC/CSNEG were once claimed COVERED via their IfConversion equivalence
/// proofs, which were X==X self-equalities (the machine side mirrored the spec;
/// no independent CSEL/CSINC/CSNEG encoder). #61 stopped counting them; #62
/// RETRACTED the degenerate proofs entirely. So the honest disposition is now
/// FailClosedAllowlisted with NO mapped value-proof at all — exactly like CSINV
/// (which never had a proof). This test pins that (a) the coverage gate keeps
/// them proof-required/RED, (b) `opcode_to_proof_query` now returns None
/// (the degenerate proof is gone), and (c) the database contains NO degenerate
/// IfConversion CSEL/CSINC/CSNEG self-equality any more. CSINV remains excluded
/// because lowering does not select it.
#[test]
fn aarch64_conditional_selects_have_no_proof_after_retraction_not_covered() {
    use trust_cg_verify::function_verifier::FunctionVerifier;

    let db = on_large_stack(ProofDatabase::new);

    for opcode in [
        AArch64Opcode::Csel,
        AArch64Opcode::Csinc,
        AArch64Opcode::Csneg,
    ] {
        // Emitted values stay in the denominator even without a faithful model.
        assert!(
            matches!(classify_aarch64(opcode), OpcodeClass::EmittableNeedsProof),
            "{opcode:?} has no value-proof (degenerate IfConversion proof retracted in #62) \
             and must remain an explicit RED obligation"
        );

        // The verifier mapping now returns None: the degenerate proof is gone.
        assert!(
            FunctionVerifier::opcode_to_proof_query(opcode).is_none(),
            "{opcode:?}: opcode_to_proof_query must be None after the #62 retraction"
        );
    }
    assert!(
        matches!(
            classify_aarch64(AArch64Opcode::Csinv),
            OpcodeClass::FailClosedAllowlisted { .. }
        ),
        "CSINV is not selected by lowering and remains explicitly excluded"
    );
    assert!(
        FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Csinv).is_none(),
        "CSINV must not gain an accidental proof query"
    );

    // And the database contains no degenerate IfConversion CSEL/CSINC/CSNEG
    // self-equality any more (the genuine condition-inversion algebra proof, which
    // is NON-degenerate, remains and is fine).
    for cp in db.by_category(trust_cg_verify::proof_database::ProofCategory::IfConversion) {
        assert!(
            cp.obligation.trust_ir_expr != cp.obligation.aarch64_expr,
            "IfConversion proof {:?} is degenerate X==X but should have been retracted in #62",
            cp.obligation.name
        );
    }
}

/// LOCKS IN the AArch64 width-polymorphic FP trio (FABS/FSQRT/FDIV): each is
/// EmittableNeedsProof and demands BOTH the F32 AND F64 value proof, each of
/// which exists and DISCHARGES. The F32/F64 discriminator in the matched proof
/// name pins width-exactness (an F64-only binding for an F32 op is the cardinal
/// sin this catches).
#[test]
fn aarch64_wired_fp_trio_requires_both_widths_and_discharges() {
    use trust_cg_verify::coverage_gate::aarch64_width_polymorphic_proofs;
    use trust_cg_verify::lowering_proof::verify_by_evaluation;
    use trust_cg_verify::verify::VerificationResult;

    let db = on_large_stack(ProofDatabase::new);

    for opcode in [
        AArch64Opcode::FabsRR,
        AArch64Opcode::FsqrtRR,
        AArch64Opcode::FdivRR,
    ] {
        assert!(
            matches!(classify_aarch64(opcode), OpcodeClass::EmittableNeedsProof),
            "{opcode:?} must be EmittableNeedsProof after wiring"
        );

        let proofs = aarch64_width_polymorphic_proofs(opcode)
            .unwrap_or_else(|| panic!("{opcode:?} must be width-polymorphic (F32 + F64)"));

        // Both F32 (32) and F64 (64) must be demanded.
        let widths: Vec<u32> = proofs.iter().map(|p| p.encoded_width_bits).collect();
        assert!(
            widths.contains(&32) && widths.contains(&64),
            "{opcode:?} must require BOTH F32 and F64 proofs, got {widths:?}"
        );

        for wp in proofs {
            let candidates = db.by_category(wp.category);
            let matched = candidates
                .iter()
                .find(|p| p.obligation.name.to_lowercase().contains(wp.query))
                .unwrap_or_else(|| {
                    panic!(
                        "{opcode:?}: required FP proof {:?} not found in {:?}",
                        wp.query, wp.category
                    )
                });
            // Width-exactness: the F32 entry must match an F32 proof, F64 -> F64.
            let want = if wp.encoded_width_bits == 32 {
                "F32"
            } else {
                "F64"
            };
            assert!(
                matched.obligation.name.contains(want),
                "{opcode:?}: width-{} query {:?} matched {:?} which is not a {want} proof",
                wp.encoded_width_bits,
                wp.query,
                matched.obligation.name
            );
            assert!(
                matches!(
                    verify_by_evaluation(&matched.obligation),
                    VerificationResult::Valid
                ),
                "{opcode:?}: FP {want} proof {:?} must DISCHARGE",
                matched.obligation.name
            );
        }
    }
}

// ===========================================================================
// 26. AArch64 logical/shift ops bind the GENERAL bitvector proof, NOT a
//     degenerate Peephole identity (trust-root anti-regression anchor).
// ===========================================================================

/// LOCKS IN the rank-3 trust-root fix: the AArch64 logical/shift opcodes
/// (AND/ORR/EOR, LSL/LSR/ASR) must be discharged by the GENERAL bitvector
/// proofs (`Band_I*`/`Bor_I*`/`Bxor_I*`/`Ishl_I*`/`Ushr_I*`/`Sshr_I*` under
/// ProofCategory::BitwiseShift), NOT by the degenerate special-case Peephole
/// rewrite identities they used to first-match (e.g. "AND Xd,Xn,Xn ≡ MOV",
/// which only proves Xn&Xn=Xn, or "LSL Xd,Xn,#0 ≡ MOV", shift-by-0). This
/// test is the anti-regression anchor that pins the per-instruction binding to
/// the general proof and rejects a silent revert to the Peephole identity.
#[test]
fn aarch64_logical_shift_ops_bind_general_proof_not_peephole_identity() {
    use trust_cg_verify::function_verifier::FunctionVerifier;
    use trust_cg_verify::lowering_proof::verify_by_evaluation;
    use trust_cg_verify::proof_database::ProofCategory;
    use trust_cg_verify::verify::VerificationResult;

    // (opcode, expected lowercase query, general mnemonic that MUST appear).
    // This test exercises the per-instruction DB query binding for AND/ORR/EOR
    // (the GENERAL BitwiseShift category, not Peephole). The shift ops LSL/LSR/ASR
    // are NOT here: their static-DB scalar proofs are degenerate and they are now
    // CREDITED via operand reconstruction instead (task #63 Step 4, #57) — see
    // `aarch64_scalar_shift_ops_are_reconstruction_covered_with_loadbearing_precond`.
    // (The gate now also credits AND/ORR/EOR via reconstruction; this test still
    // pins their genuine static-DB query binding as an anti-regression anchor.)
    let cases = [
        (AArch64Opcode::AndRR, "band_i", "-> AND"),
        (AArch64Opcode::AndRI, "band_i", "-> AND"),
        (AArch64Opcode::OrrRR, "bor_i", "-> OR"),
        (AArch64Opcode::OrrRI, "bor_i", "-> OR"),
        (AArch64Opcode::EorRR, "bxor_i", "-> XOR"),
        (AArch64Opcode::EorRI, "bxor_i", "-> XOR"),
    ];

    let db = on_large_stack(ProofDatabase::new);

    for (opcode, query, mnemonic) in cases {
        // (1) Still part of the proof-required surface.
        assert!(
            matches!(classify_aarch64(opcode), OpcodeClass::EmittableNeedsProof),
            "{opcode:?} must be EmittableNeedsProof"
        );

        // (2) The per-instruction mapping must resolve to BitwiseShift (the
        //     GENERAL proof category), NOT Peephole. This is the trust-root
        //     anti-regression anchor.
        let (bound_query, category) = FunctionVerifier::opcode_to_proof_query(opcode)
            .unwrap_or_else(|| panic!("{opcode:?}: opcode_to_proof_query returned None"));
        assert_eq!(
            category,
            ProofCategory::BitwiseShift,
            "{opcode:?} must bind the GENERAL BitwiseShift proof, not Peephole"
        );
        assert_eq!(bound_query, query, "{opcode:?}: wired query changed");

        // (3) The matched proof (case-insensitive contains within BitwiseShift,
        //     mirroring the live AArch64 verifier) names the GENERAL operation
        //     and is NOT a degenerate identity rewrite.
        let candidates = db.by_category(category);
        let matched = candidates
            .iter()
            .find(|p| p.obligation.name.to_lowercase().contains(query))
            .unwrap_or_else(|| panic!("{opcode:?}: no proof matching {query:?} in BitwiseShift"));
        let name = &matched.obligation.name;
        assert!(
            name.contains(mnemonic),
            "{opcode:?}: matched proof {name:?} lacks general mnemonic {mnemonic:?}"
        );
        assert!(
            !name.contains('≡') && !name.contains("MOV") && !name.contains("Peephole"),
            "{opcode:?}: matched proof {name:?} looks like a degenerate Peephole identity"
        );

        // (4) The general proof DISCHARGES.
        assert!(
            matches!(
                verify_by_evaluation(&matched.obligation),
                VerificationResult::Valid
            ),
            "{opcode:?}: general proof {name:?} must DISCHARGE"
        );
    }
}

/// LOCKS IN the stronger (width-polymorphic) gate treatment of the AArch64
/// logical/shift ops: each is wired into `aarch64_width_polymorphic_proofs`
/// demanding BOTH the I32 AND I64 GENERAL bitvector proof, each of which exists
/// and DISCHARGES. The 32/64-bit discriminator in the matched proof name pins
/// width-exactness, so no emitted width can ship silently unproven.
#[test]
fn aarch64_logical_shift_ops_require_both_widths_and_discharge() {
    use trust_cg_verify::coverage_gate::aarch64_width_polymorphic_proofs;
    use trust_cg_verify::lowering_proof::verify_by_evaluation;
    use trust_cg_verify::proof_database::ProofCategory;
    use trust_cg_verify::verify::VerificationResult;

    let db = on_large_stack(ProofDatabase::new);

    // HONESTY (task #61): only the GENUINE logical ops (AND/ORR/EOR -> Band/Bor/
    // Bxor) remain width-polymorphic-and-covered. The shift ops LSL/LSR/ASR were
    // removed (their scalar shift proofs are degenerate; see the new test
    // `aarch64_scalar_shift_ops_are_degenerate_backed_not_covered`).
    for opcode in [
        AArch64Opcode::AndRR,
        AArch64Opcode::AndRI,
        AArch64Opcode::OrrRR,
        AArch64Opcode::OrrRI,
        AArch64Opcode::EorRR,
        AArch64Opcode::EorRI,
    ] {
        assert!(
            matches!(classify_aarch64(opcode), OpcodeClass::EmittableNeedsProof),
            "{opcode:?} must be EmittableNeedsProof"
        );

        let proofs = aarch64_width_polymorphic_proofs(opcode)
            .unwrap_or_else(|| panic!("{opcode:?} must be width-polymorphic (I32 + I64)"));

        // Both I32 (32) and I64 (64) must be demanded.
        let widths: Vec<u32> = proofs.iter().map(|p| p.encoded_width_bits).collect();
        assert!(
            widths.contains(&32) && widths.contains(&64),
            "{opcode:?} must require BOTH I32 and I64 proofs, got {widths:?}"
        );

        for wp in proofs {
            assert_eq!(
                wp.category,
                ProofCategory::BitwiseShift,
                "{opcode:?}: width proof must be in the GENERAL BitwiseShift category"
            );
            let candidates = db.by_category(wp.category);
            let matched = candidates
                .iter()
                .find(|p| p.obligation.name.to_lowercase().contains(wp.query))
                .unwrap_or_else(|| {
                    panic!(
                        "{opcode:?}: required width proof {:?} not found in {:?}",
                        wp.query, wp.category
                    )
                });
            // Width-exactness: the 32 entry must match a (32-bit) proof, 64 -> (64-bit).
            let want = if wp.encoded_width_bits == 32 {
                "(32-bit)"
            } else {
                "(64-bit)"
            };
            assert!(
                matched.obligation.name.contains(want),
                "{opcode:?}: width-{} query {:?} matched {:?} which is not a {want} proof",
                wp.encoded_width_bits,
                wp.query,
                matched.obligation.name
            );
            // Not a degenerate identity.
            assert!(
                !matched.obligation.name.contains('≡')
                    && !matched.obligation.name.contains("Peephole"),
                "{opcode:?}: width proof {:?} looks like a degenerate identity",
                matched.obligation.name
            );
            assert!(
                matches!(
                    verify_by_evaluation(&matched.obligation),
                    VerificationResult::Valid
                ),
                "{opcode:?}: general {want} proof {:?} must DISCHARGE",
                matched.obligation.name
            );
        }
    }
}

/// RECONSTRUCTION resolves #57 (task #63 Step 4): the AArch64 scalar shift opcodes
/// (LSL/LSR/ASR, RR and RI forms) are now CREDITED via OPERAND RECONSTRUCTION, not
/// via the static-DB scalar proofs.
///
/// The static-DB scalar Ishl/Ushr/Sshr_I* proofs REMAIN degenerate (bvshl==bvshl
/// etc.) and on KNOWN_DEGENERATE_PENDING_FIX — this test still pins that so the
/// reconstruction credit is provably the GENUINE source of coverage, not the
/// static DB. But the opcodes are now `EmittableNeedsProof` and their
/// representative reconstructed obligation discharges `Valid` against the FAITHFUL
/// hardware-amount-masked machine side under a LOAD-BEARING `amount < width`
/// precondition. We assert the precondition is genuinely load-bearing: stripping
/// it makes the representative obligation REFUTE (a shift by exactly `width` is a
/// shift-by-0 on hardware but a clamp-to-0 in the in-house SMT). That is the #57
/// fix — the precondition is no longer cosmetic.
#[test]
fn aarch64_scalar_shift_ops_are_reconstruction_covered_with_loadbearing_precond() {
    use trust_cg_ir::cc::OperandSize;
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;
    use trust_cg_verify::aarch64_semantics::{encode_asr_rr_masked, encode_lsl_rr_masked};
    use trust_cg_verify::function_verifier::{
        reconstruct_alu_obligation, reconstruction_discharges_valid,
        representative_reconstructable_inst,
    };
    use trust_cg_verify::lowering_proof::{
        MachineSideProvenance, ProofObligation, VerificationConfig, verify_by_evaluation,
    };
    use trust_cg_verify::proof_database::{ProofCategory, is_known_degenerate_debt};
    use trust_cg_verify::smt::SmtExpr;
    use trust_cg_verify::trust_ir_semantics::encode_trust_ir_shift;
    use trust_cg_verify::verify::VerificationResult;

    let cfg = VerificationConfig::default();
    for opcode in [
        AArch64Opcode::LslRR,
        AArch64Opcode::LslRI,
        AArch64Opcode::LsrRR,
        AArch64Opcode::LsrRI,
        AArch64Opcode::AsrRR,
        AArch64Opcode::AsrRI,
    ] {
        // NEW disposition: EmittableNeedsProof and reconstruction-covered.
        assert!(
            matches!(classify_aarch64(opcode), OpcodeClass::EmittableNeedsProof),
            "{opcode:?} must be EmittableNeedsProof (reconstruction-credited)"
        );
        assert!(
            reconstruction_discharges_valid(opcode, &cfg),
            "{opcode:?}: representative reconstructed obligation must discharge Valid"
        );
        // The reconstructed obligation carries the load-bearing precondition.
        let inst = representative_reconstructable_inst(opcode)
            .unwrap_or_else(|| panic!("{opcode:?} must have a representative instance"));
        let ob = reconstruct_alu_obligation(&inst)
            .unwrap_or_else(|| panic!("{opcode:?} must reconstruct"));
        assert_eq!(
            ob.preconditions.len(),
            1,
            "{opcode:?}: shift reconstruction must carry exactly the amount<width precondition"
        );
    }

    // LOAD-BEARING demonstration at width 8 (exhaustive path, vacuous-guard
    // active). WITH the precondition the in-range equivalence is Valid; WITHOUT
    // it, a shift by exactly width (8 & 7 == 0 on hardware vs clamp-to-0 in SMT)
    // REFUTES — the precondition genuinely changes the verdict (#57, not cosmetic).
    let a = SmtExpr::var("recon_src1", 8);
    let amt = SmtExpr::var("recon_src2", 8);
    let mk = |pre: Vec<SmtExpr>| ProofObligation {
        name: "shift8 loadbearing demo".to_string(),
        trust_ir_expr: encode_trust_ir_shift(&Opcode::Ishl, Type::I8, a.clone(), amt.clone()),
        aarch64_expr: encode_lsl_rr_masked(OperandSize::S32, a.clone(), amt.clone()),
        inputs: vec![("recon_src1".to_string(), 8), ("recon_src2".to_string(), 8)],
        preconditions: pre,
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "LslRR".to_string(),
            arity: 2,
        },
    };
    let with_pre = mk(vec![amt.clone().bvult(SmtExpr::bv_const(8, 8))]);
    let without_pre = mk(vec![]);
    assert!(
        matches!(verify_by_evaluation(&with_pre), VerificationResult::Valid),
        "shift8 WITH amount<width precondition must be Valid (in-range equivalence)"
    );
    assert!(
        matches!(
            verify_by_evaluation(&without_pre),
            VerificationResult::Invalid { .. }
        ),
        "shift8 WITHOUT the precondition must REFUTE — the precondition is LOAD-BEARING (#57)"
    );
    // Also confirm a wrong shift opcode (Lsl as Asr-masked) refutes: bvshl vs bvashr.
    let wrong = ProofObligation {
        aarch64_expr: encode_asr_rr_masked(OperandSize::S32, a.clone(), amt.clone()),
        ..with_pre.clone()
    };
    assert!(
        matches!(
            verify_by_evaluation(&wrong),
            VerificationResult::Invalid { .. }
        ),
        "Ishl reconstructed against an ASR machine side must REFUTE (bvshl vs bvashr)"
    );

    // CAPSTONE (task #62): the static-DB scalar shift proofs (which were degenerate
    // X==X) have been RETRACTED — reconstruction (above) is the SOLE source of
    // coverage now. Assert they are no longer registered and no longer on the
    // (now-empty) debt ledger.
    let db = on_large_stack(ProofDatabase::new);
    let bws = db.by_category(ProofCategory::BitwiseShift);
    for gone in [
        "Ishl_I8 -> SHL (8-bit)",
        "Ishl_I32 -> LSL (32-bit)",
        "Ushr_I32 -> LSR (32-bit)",
        "Sshr_I64 -> ASR (64-bit)",
    ] {
        assert!(
            !bws.iter().any(|p| p.obligation.name == gone),
            "{gone:?}: degenerate static scalar shift proof must be RETRACTED (not registered)"
        );
        assert!(
            !is_known_degenerate_debt(gone),
            "{gone:?}: must no longer be on KNOWN_DEGENERATE_PENDING_FIX (ledger is empty)"
        );
    }
}

// ===========================================================================
// 8. #67 kept-carrier checked-overflow DETECTION opcodes are COVERED.
// ===========================================================================

/// LOCKS IN the #67 de-allowlisting for the ADD/SUB flag-recompute carriers:
/// ADDS/SUBS are EmittableNeedsProof and resolve — via the SAME
/// `opcode_to_proof_query` the gate uses — to their FAITHFUL `Checked*_I64`
/// obligation (registered under ProofCategory::Arithmetic), which carries the
/// exact instruction mnemonic and DISCHARGES. The matched proof must NOT be a
/// degenerate identity (f81e45b class): we pin the unique idiom mnemonic, that
/// the obligation is the two-input packed-overflow form, and (structurally) that
/// trust_ir_expr != aarch64_expr. SMULH/UMULH are handled separately (their
/// 64-bit FORMAL discharge is SMT-hard) — see
/// `aarch64_smulh_umulh_have_statistical_not_formal_64bit_evidence`.
#[test]
fn aarch64_overflow_detection_opcodes_are_covered_with_discharged_proofs() {
    use trust_cg_verify::function_verifier::FunctionVerifier;
    use trust_cg_verify::lowering_proof::verify_by_evaluation;
    use trust_cg_verify::proof_database::ProofCategory;
    use trust_cg_verify::verify::VerificationResult;

    // (opcode, expected query, UNIQUE mnemonic that must be in the proof name).
    // Only the add/sub flag-recompute forms stay EmittableNeedsProof: their i64
    // obligations discharge FORMALLY via ay (fast). SMULH/UMULH are now
    // FailClosedAllowlisted (their 64-bit FORMAL discharge is SMT-hard; the
    // honest width-8 evidence is locked separately in
    // `aarch64_smulh_umulh_have_statistical_not_formal_64bit_evidence`).
    let cases = [
        (AArch64Opcode::AddsRR, "checkedsadd_i64", "ADDS+CSET_VS"),
        (AArch64Opcode::SubsRR, "checkedssub_i64", "SUBS+CSET_VS"),
    ];

    let db = on_large_stack(ProofDatabase::new);

    for (opcode, query, mnemonic) in cases {
        assert!(
            matches!(classify_aarch64(opcode), OpcodeClass::EmittableNeedsProof),
            "{opcode:?} must be EmittableNeedsProof after #67 de-allowlisting"
        );

        let (bound_query, category) = FunctionVerifier::opcode_to_proof_query(opcode)
            .unwrap_or_else(|| panic!("{opcode:?}: opcode_to_proof_query returned None"));
        assert_eq!(bound_query, query, "{opcode:?}: wired query changed");
        assert_eq!(
            category,
            ProofCategory::Arithmetic,
            "{opcode:?}: checked-overflow proofs are registered under Arithmetic"
        );

        // Mirror the REAL per-compile verify() match EXACTLY:
        // name.to_lowercase().contains(query) — the NAME is lowercased but the
        // QUERY is NOT (function_verifier.rs ~2838). So the wired query MUST be
        // lowercase; a mixed-case query (e.g. the old "CheckedSadd_I64") silently
        // fails HERE and in the gate, leaving checked add/sub uncovered at compile
        // time even though the proof exists. The coverage audit's case-INSENSITIVE
        // match masked exactly this bug — this test now has teeth against it.
        let candidates = db.by_category(category);
        let matched = candidates
            .iter()
            .find(|p| p.obligation.name.to_lowercase().contains(query))
            .unwrap_or_else(|| panic!("{opcode:?}: no proof matching {query:?} in {category:?}"));
        assert!(
            matched.obligation.name.contains(mnemonic),
            "{opcode:?}: matched proof {:?} lacks idiom mnemonic {mnemonic:?}",
            matched.obligation.name
        );
        // Not a degenerate identity: the obligation is the two-input packed
        // (value :: overflow) form, NOT a single-var identity.
        assert_eq!(
            matched.obligation.inputs,
            vec![("a".to_string(), 64), ("b".to_string(), 64)],
            "{opcode:?}: matched proof {:?} is not the two-input packed-overflow form",
            matched.obligation.name
        );
        // STRUCTURAL NON-DEGENERACY (f81e45b / X==X guard): the bound obligation's
        // trust-ir side must NOT be structurally identical to its aarch64 side, or
        // it would discharge trivially and prove nothing. SmtExpr: Eq.
        assert_ne!(
            matched.obligation.trust_ir_expr, matched.obligation.aarch64_expr,
            "{opcode:?}: bound proof {:?} is DEGENERATE (trust_ir_expr == aarch64_expr) — \
             it proves nothing",
            matched.obligation.name
        );
        assert!(
            matches!(
                verify_by_evaluation(&matched.obligation),
                VerificationResult::Valid
            ),
            "{opcode:?}: bound checked-overflow proof {:?} must DISCHARGE",
            matched.obligation.name
        );
    }
}

/// SMULH/UMULH are emitted values and therefore remain in the denominator. Their
/// non-degenerate 64-bit obligations are accepted by the default statistical
/// regression evaluator; this must never be described as a 64-bit formal proof.
/// The same theorem is independently exhaustive at width 8.
#[test]
fn aarch64_smulh_umulh_have_statistical_not_formal_64bit_evidence() {
    use trust_cg_verify::function_verifier::FunctionVerifier;
    use trust_cg_verify::lowering_proof::verify_by_evaluation;
    use trust_cg_verify::proof_database::ProofCategory;
    use trust_cg_verify::verify::{VerificationResult, VerificationStrength};

    let db = on_large_stack(ProofDatabase::new);
    let arith = db.by_category(ProofCategory::Arithmetic);
    for op in [AArch64Opcode::Smulh, AArch64Opcode::Umulh] {
        assert!(matches!(
            classify_aarch64(op),
            OpcodeClass::EmittableNeedsProof
        ));
        let (query, category) =
            FunctionVerifier::opcode_to_proof_query(op).expect("SMULH/UMULH evidence query");
        let candidates = db.by_category(category);
        let matched = candidates
            .iter()
            .find(|p| p.obligation.name.to_lowercase().contains(query))
            .expect("mapped 64-bit high-half obligation");
        assert_ne!(
            matched.obligation.trust_ir_expr, matched.obligation.aarch64_expr,
            "{op:?}: 64-bit evidence must not be a degenerate X==X"
        );
        assert!(matches!(
            VerificationStrength::for_obligation(&matched.obligation),
            VerificationStrength::Statistical { .. }
        ));
        assert!(matches!(
            verify_by_evaluation(&matched.obligation),
            VerificationResult::Valid
        ));
    }

    // The width-8 evidence is complete for that width only.
    for want in [
        "CheckedSmul_I8 exact product overflow",
        "CheckedUmul_I8 exact product overflow",
    ] {
        let matched = arith
            .iter()
            .find(|p| p.obligation.name.contains(want))
            .unwrap_or_else(|| {
                panic!("width-8 mul-equivalence evidence {want:?} is NOT registered in the DB")
            });
        assert_eq!(
            matched.obligation.inputs,
            vec![("a".to_string(), 8), ("b".to_string(), 8)],
            "{want:?}: must be the width-8 two-input form"
        );
        assert_ne!(
            matched.obligation.trust_ir_expr, matched.obligation.aarch64_expr,
            "{want:?}: DEGENERATE (trust_ir_expr == aarch64_expr) — proves nothing"
        );
        assert!(
            matches!(
                verify_by_evaluation(&matched.obligation),
                VerificationResult::Valid
            ),
            "{want:?}: width-8 mul-equivalence proof must DISCHARGE exhaustively"
        );
    }
}

/// LOCKS IN the #67 split: the i128 carry-chain (ADC/SBC) and the 32->64
/// widening multiplies (SMULL/UMULL) stay emitted-value obligations in the
/// denominator (SMULL is RED until modeled; UMULL is now COVERED via its
/// faithful single-form zext64*zext64 obligation, proof_umull_rr — the SMULL
/// sext confusion refutes, so the signed form cannot inherit the credit),
/// while the never-emitted flag-setting immediate forms remain excluded.
#[test]
fn aarch64_widening_mul_stays_red_but_i128_carry_now_covered() {
    for op in [AArch64Opcode::Smull, AArch64Opcode::Umull] {
        assert!(
            matches!(classify_aarch64(op), OpcodeClass::EmittableNeedsProof),
            "{op:?} is emitted value debt and must stay in the denominator"
        );
    }
    // SMULL must remain a named deferred RED row; UMULL must NOT (it is covered
    // by its own faithful obligation, not by inheritance).
    assert!(
        aarch64_deferred_value_op_reason(AArch64Opcode::Smull).is_some(),
        "SMULL has no faithful widening obligation and must stay named RED debt"
    );
    assert!(
        aarch64_deferred_value_op_reason(AArch64Opcode::Umull).is_none(),
        "UMULL is credited via proof_umull_rr and must not sit in the deferred table"
    );
    for op in [AArch64Opcode::AddsRI, AArch64Opcode::SubsRI] {
        assert!(
            matches!(
                classify_aarch64(op),
                OpcodeClass::FailClosedAllowlisted { .. }
            ),
            "{op:?} is never selected and should remain explicitly excluded"
        );
    }
    // Adc/Sbc are NOW credited to the FAITHFUL i128 whole-chain composition proof
    // (proof_iadd/isub_i128_whole_chain) — EmittableNeedsProof, not allowlisted.
    for op in [AArch64Opcode::Adc, AArch64Opcode::Sbc] {
        assert!(
            matches!(classify_aarch64(op), OpcodeClass::EmittableNeedsProof),
            "{op:?} is now credited to the faithful i128 carry-chain composition proof"
        );
    }
}

/// Mark every line belonging to a contiguous comment run that records a ratio
/// *transition* somewhere within it.
///
/// These files carry running changelogs ("AArch64 126/126 (UNIVERSE BACKFILL
/// ...)" followed a few lines later by "-> EmittableNeedsProof"), so a
/// line-local arrow test marks only part of the narrative and the rest reads as
/// a stale current-state claim.
fn historical_comment_lines(lines: &[&str]) -> Vec<bool> {
    let is_comment = |l: &str| {
        let t = l.trim_start();
        t.starts_with("//") || t.starts_with('#')
    };
    let has_arrow = |l: &str| l.contains("->") || l.contains('\u{2192}');
    let mut out = vec![false; lines.len()];
    let mut i = 0;
    while i < lines.len() {
        if !is_comment(lines[i]) {
            out[i] = has_arrow(lines[i]);
            i += 1;
            continue;
        }
        let start = i;
        while i < lines.len() && is_comment(lines[i]) {
            i += 1;
        }
        if lines[start..i].iter().any(|l| has_arrow(l)) {
            out[start..i].fill(true);
        }
    }
    out
}

/// The first `N/M` token stated after `alias` on `line`.
///
/// The scan stops at the next architecture name, because these ratios are
/// routinely listed four-to-a-line ("x86-64 163/192 (29 RED), RISC-V 14/17
/// ..."); without that bound a fixed window reads the *next* architecture's
/// ratio and reports a false mismatch.
///
/// `ds`, `slash` and `ns` only ever hold positions of an ASCII digit or `/`, and
/// an ASCII byte is always a UTF-8 char boundary, so those slices are safe. The
/// window end is NOT: `start + WINDOW` is an arbitrary byte offset and these
/// lines contain em dashes, so it is walked back to a boundary before slicing.
fn ratio_after(line: &str, alias: &str, all_aliases: &[&str]) -> Option<(usize, usize)> {
    const WINDOW: usize = 32;
    let bytes = line.as_bytes();
    let rel = line.find(alias)?;
    let start = rel + alias.len();
    let mut end = line.len().min(start + WINDOW);
    while end > start && !line.is_char_boundary(end) {
        end -= 1;
    }
    for other in all_aliases {
        if let Some(next) = line[start..end].find(other) {
            end = start + next;
        }
    }
    let mut i = start;
    while i < end {
        if !bytes[i].is_ascii_digit() {
            i += 1;
            continue;
        }
        let ds = i;
        while i < end && bytes[i].is_ascii_digit() {
            i += 1;
        }
        if i < end && bytes[i] == b'/' {
            let slash = i;
            i += 1;
            let ns = i;
            while i < end && bytes[i].is_ascii_digit() {
                i += 1;
            }
            if i > ns
                && let (Ok(cov), Ok(em)) = (line[ds..slash].parse(), line[ns..i].parse())
            {
                return Some((cov, em));
            }
        }
    }
    None
}

/// Published coverage ratios must equal what the gate actually computes.
///
/// The four ratios were restated in eight places across README.md,
/// SOUNDNESS_CHECK.md, `scripts/soundness_check.sh` and three test files, with
/// nothing tying any of them to the gate. Commit 0c818cf0 moved x86-64 from
/// 158/187 to 160/189 and touched none of them, so the project published — via
/// two files listed in `publish/manifest.txt` — a ratio its own fail-closed gate
/// contradicted, and a doc comment in this very file disagreed with the
/// assertions 850 lines above it.
///
/// Deriving the expected values from the live report means a pin bump now fails
/// here rather than silently desyncing the shipped evidence surface.
///
/// Lines recording a *transition* (`158/187 -> 160/189`) legitimately name a
/// superseded ratio and are skipped. Known limitation: a ratio stated with no
/// architecture name within `WINDOW` bytes is not checked.
#[test]
fn published_coverage_ratios_match_the_gate() {
    let (aa, x86, rv, wasm) = on_large_stack(|| {
        let gate = CoverageGate::new();
        let audit = |arch| {
            let report = gate.audit(arch);
            (report.covered_count(), report.emittable_count())
        };
        (
            audit(GateArch::AArch64),
            audit(GateArch::X86_64),
            audit(GateArch::RiscV),
            audit(GateArch::Wasm),
        )
    });

    let arches: [(&[&str], (usize, usize)); 4] = [
        (&["AArch64"], aa),
        (&["x86-64"], x86),
        (&["RISC-V"], rv),
        (&["WebAssembly", "WASM", "wasm"], wasm),
    ];
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let files = [
        "README.md",
        "SOUNDNESS_CHECK.md",
        "scripts/soundness_check.sh",
        "crates/trust-cg-opt/src/x86_vectorize.rs",
        "crates/trust-cg-verify/tests/coverage_gate_tests.rs",
        "crates/trust-cg-verify/tests/soundness_manifest.rs",
        "crates/trust-cg-verify/tests/meta_theorems.rs",
    ];

    let all_aliases: Vec<&str> = arches
        .iter()
        .flat_map(|(aliases, _)| aliases.iter().copied())
        .collect();

    let mut stale = Vec::new();
    for relative in files {
        let path = root.join(relative);
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
        let lines: Vec<&str> = text.lines().collect();
        let historical = historical_comment_lines(&lines);
        for (index, line) in lines.iter().enumerate() {
            // A transition record legitimately names a superseded ratio, and the
            // arrow may sit several lines away inside the same comment block.
            if historical[index] {
                continue;
            }
            for (aliases, (covered, emittable)) in &arches {
                for alias in *aliases {
                    let Some((found_cov, found_em)) = ratio_after(line, alias, &all_aliases) else {
                        continue;
                    };
                    if (found_cov, found_em) != (*covered, *emittable) {
                        stale.push(format!(
                            "  {relative}:{} — `{alias}` is stated as {found_cov}/{found_em}, \
                             but the gate computes {covered}/{emittable}",
                            index + 1
                        ));
                    }
                }
            }
        }
    }

    assert!(
        stale.is_empty(),
        "published coverage ratios disagree with the gate's own computation:\n{}\n\n\
         Update each site, or if the pin genuinely moved, update the pinned \
         assertions first and let this test confirm the docs followed.",
        stale.join("\n")
    );
}
