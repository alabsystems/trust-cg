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
    classify_x86, x86_deferred_value_op_reason, x86_width_polymorphic_proofs,
};
use trust_cg_verify::proof_database::ProofDatabase;

/// The x86-64 SSE LANE credits stand on a CAPTURED corpus of emitted bytes, for
/// the same reason `MovRI` does: the gate crate cannot run the encoder. A
/// target that PINS the ratio those ten rows moved must not be able to stay
/// green on a stale capture, so it re-derives the corpus from the LIVE encoder
/// here. That placement is the whole point — while this re-derivation lived
/// only in `x86_sse_lane_gate`, an encoder change that made these bytes wrong
/// left every ratio-pinning target passing over frozen bytes.
#[path = "support/sse_lane_live_encode.rs"]
mod sse_lane_live;

use sse_lane_live::assert_sse_lane_corpus_is_what_the_live_encoder_emits;

/// The AArch64 decoded-value credits (register copies, SMULL, BFM, RBIT,
/// `ADD #imm12, LSL #12`, MRS) stand on a CAPTURED corpus of encoder words for
/// the same reason; this target pins their ratio, so it re-derives them too.
#[path = "support/a64_value_live_encode.rs"]
mod a64_value_live;

use a64_value_live::assert_a64_value_corpus_is_what_the_live_encoder_emits;
/// The `x86_64::MovsxdRMSib` credit stands on a CAPTURED corpus for the same
/// reason, and the same re-derivation runs here so the ratio pin cannot go green
/// on frozen bytes.
#[path = "support/movsxd_sib_live_encode.rs"]
mod movsxd_sib_live;

use movsxd_sib_live::assert_movsxd_sib_corpus_is_what_the_live_encoder_emits;
/// The wasm float credits (`f32.const`/`f64.const` payloads and the
/// `f.min`/`f.max`/`copysign` bodies) stand on CAPTURED corpora for the same
/// reason; this target pins the wasm ratio they moved, so it re-derives them
/// from the live backend too.
#[path = "support/wasm_float_live_emit.rs"]
mod wasm_float_live;

/// The wasm `memory.copy` / `memory.fill` credits stand on the captured guarded
/// MemCopy / MemSet bodies; this target pins the ratio they moved, so it
/// re-derives them from the live backend.
#[path = "support/wasm_bulk_memory_live_emit.rs"]
mod wasm_bulk_live;

/// The wasm ratio excludes the v128 forms as never selected; this target pins
/// it, so it checks the exclusion against the live backend's emission.
#[path = "support/wasm_never_selected_live_scan.rs"]
mod wasm_never_selected_live;

/// Run `f` on a 64 MiB stack so `ProofDatabase::new()` does not overflow the
/// default 8 MiB test-thread stack (proof_database.rs #205).
/// Rows that fail only because this host's `drat-trim` is not one the
/// bound-memory or atomic-memory manifest authorizes: the bound-memory and
/// atomic rows (and the volatile rows that follow them) fail closed there as
/// checker-identity misses, and exactly the manifests' qualification pins
/// (`bound_memory_set_binds_the_exact_runtime_checker_bytes`,
/// `atomic_memory_set_binds_the_exact_runtime_checker_bytes`) are red. On a
/// qualified host there are none.
fn checker_identity_misses(report: &trust_cg_verify::coverage_gate::CoverageReport) -> usize {
    let misses = report
        .rows
        .iter()
        .filter(|row| {
            row.finding.is_some()
                && row
                    .note
                    .contains(trust_cg_verify::bound_memory_authority::CHECKER_IDENTITY_MISS)
        })
        .count();
    if trust_cg_verify::bound_memory_authority::bound_memory_checker_qualification().is_ok()
        && trust_cg_verify::bound_memory_authority::atomic_memory_checker_qualification().is_ok()
        && trust_cg_verify::bound_memory_authority::neon_memory_checker_qualification().is_ok()
    {
        assert_eq!(misses, 0, "a qualified host has no checker-identity miss");
    }
    misses
}

fn on_large_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .name("coverage-gate".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn large-stack coverage-gate thread")
        .join()
        .expect("coverage-gate thread panicked")
}

/// The `x86_64::MovRI` credit stands on a CAPTURED corpus
/// (`x86_encoding_proofs::EMITTED_X86_MOV_IMMEDIATES`), because the gate crate
/// cannot run the encoder. A target that PINS that credit must not be able to
/// stay green on a stale capture, so it re-derives every entry from the LIVE
/// encoder here. `trust-cg-codegen` is a dev-dependency, which is allowed. Returns
/// the number of entries checked.
fn assert_movri_corpus_is_what_the_live_encoder_emits() -> usize {
    use trust_cg_codegen::x86_64::{X86Encoder, X86InstOperands};
    use trust_cg_ir::X86PReg;
    use trust_cg_verify::x86_encoding_proofs::EMITTED_X86_MOV_IMMEDIATES;
    let mut checked = 0usize;
    for &(name, imm, captured) in EMITTED_X86_MOV_IMMEDIATES {
        let reg = (0u16..64)
            .map(X86PReg::new)
            .find(|r| r.to_string() == name)
            .unwrap_or_else(|| panic!("trust-cg-ir has no GPR named `{name}`"));
        let mut encoder = X86Encoder::new();
        encoder
            .encode_instruction(X86Opcode::MovRI, &X86InstOperands::ri(reg, imm))
            .unwrap_or_else(|e| panic!("live encoder refused MovRI {name},{imm:#x}: {e:?}"));
        let live = encoder.finish();
        assert_eq!(
            live.as_slice(),
            captured,
            "STALE MovRI CORPUS: MOV {name},{imm:#x} is emitted as {live:02x?} by the live encoder \
             but captured as {captured:02x?}. The x86-64 MovRI credit would rest on bytes the \
             backend no longer emits; re-capture and re-run tests/x86_encoding_gate.rs"
        );
        checked += 1;
    }
    assert!(checked >= 150, "MovRI corpus shrank to {checked}");
    checked
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
/// 78/78, and the historical scalar-FP rollout (Fcmp's representative
/// FCMP→NZCV+CSET binding, since withdrawn because it lacked runtime
/// applicability; FmovImm VFPExpandImm encoding promoted out of the allowlist;
/// FRINT{M,P,Z} moved to per-instruction reconstruction) took it to 81/81, and the dense-
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
///     Statistical). Bfm (insert) and Rbit stay fail-closed. RorRI is NO LONGER
///     in that set: the rotate recognizer now emits it STANDALONE when the EOR
///     does not fuse, and it is covered on BOTH counts its former deferred
///     reason named — its own faithful W+X rotate obligations
///     (all_ror_immediate_proofs) AND the per-instruction, width- and
///     immediate-sensitive EXTR-alias reconstruction. Either alone would
///     discharge the row; both are required to stay wired.
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
/// * NEON SCALAR PAIRWISE ADD (L04-P6): `NeonAddpScalar` (`ADDP Dd, Vn.2D`)
///   left the fail-closed allowlist for the denominator and is credited by its
///   FAITHFUL cross-lane obligation (all_neon_addp_proofs: the doubleword sum
///   sliced from the raw D-halves against the `encode_neon_addp_scalar_2d`
///   model, which the live silicon differential checks on this CPU;
///   no-reduction, SUB, UMAXV-confusion, lane-miswire and `.4S`-size controls
///   refute). +1 covered, +1 to the denominator.
///
/// * BOUND-MEMORY FORM CERTIFICATES (L04-P1, X-OPCODES-P1/P2): the 46
///   single-instruction atomic rows (LDAR/STLR x3, CAS x4, SWP x4, LD<op> x32),
///   the 18 scalar memory rows (LDR/STR/LDRB/LDRH/LDRSB/LDRSH/STRB/STRH
///   immediate and register offset, W/X pre/post-index writeback; the H/S/D/Q
///   forms judged by their exact word-bound memory-effect decomposition) and
///   the six
///   pair rows (STP/LDP signed offset, STP pre-index, LDP post-index, and the
///   NEON Q-pair post-index STP/LDP) left the deferred table: each is
///   credited only when EVERY legal form of the opcode
///   has a committed form-theorem certificate that the independent checker
///   replays in process, representative instructions credited through the
///   Formal-only rule's clauses 2-4, and every machine defect refuted
///   (`bound_memory_row_credit`); the six volatile rows follow their
///   now-credited plain rows. +76 covered.
///
/// * CRC32 DECODED-WORD OBLIGATIONS (L04-P1): the eight FEAT_CRC32 rows
///   (`Crc32B` .. `Crc32Cx`) left the deferred table. Each form's re-derived
///   word, decoded independently and given its Arm ARM pseudocode (BitReverse,
///   Poly32Mod2, BitReverse; Xd[63:32] cleared), equals the reflected
///   LSB-first CRC intent for every register value, decided in process by
///   GF(2)-affine evaluation (`aarch64_crc32_proofs`, `gf2_affine_decide`), and
///   every word, width, polynomial, operand, bit- and byte-order control
///   refutes. Testing grade: accepted regression evidence, not a formal proof.
///   +8 covered.
///
/// * SUBS #imm DECODED-WORD OBLIGATION (L04-P1): `SubsRI` (the looped stack
///   probe's `SUBS X16, X16, #1`) left the deferred table. For both widths,
///   the destination value and N, Z, C, V of the independently decoded word
///   (Arm `AddWithCarry(Rn, NOT(imm), 1)`) equal the operands' difference and
///   comparison flags, each decided for every register value by the
///   bit-serial automaton in process (`aarch64_subs_imm_proofs`), with ADDS,
///   SUB, width, shifted-immediate, off-by-one, register and flag-meaning
///   controls refuted. Testing grade, not a formal proof. +1 covered.
///
/// * NEON LD1/ST1 POST-INDEX FORM CERTIFICATES (L04-P1): `NeonLd1Post` and
///   `NeonSt1Post` left the deferred table. Each of their seven arrangements
///   has a form theorem (`aarch64_neon_structure_forms`: the element loop of
///   the encoded fields against the operands' LDR/STR Dt|Qt intent, every
///   register or memory byte and the writeback) with a committed certificate
///   in its own set (`verdict_db/neon_memory_certs/`) that the independent
///   checker replays in process; the gate credits a row only when every
///   arrangement's certificate replays, representative instructions are
///   credited through clauses 2-4 (clause 2: the exact word-bound
///   memory-effect decomposition) and every machine defect refutes. +2
///   covered.
///
/// AArch64 accepted-obligation coverage is 267/302. The 35 RED rows are exactly
/// the 35 `DeferredUnfaithfulModel` findings; no row lacks a mapping. FCMP,
/// CSET, CSEL, CSINC and CSNEG are credited by the NZCV producer/consumer
/// family (`aarch64_flag_consumer_proofs`) and the four half-precision FCVT
/// forms by decoded-word obligations (`aarch64_fcvt_half`). The five
/// conditional trap carriers (L04-P12: `TrapNullIfZero`, `TrapDivZeroIfZero`,
/// `TrapBoundsCheckExact`, `TrapShiftRangeIfOOB`, `TrapOverflowExact`) entered
/// the denominator from the pseudo/trap bucket and are credited by the
/// trap-expansion family (`aarch64_trap_expansion`), decided in process. This ratio inventories evidence
/// acceptance for emitted value/effect opcodes; it is not a formal-correctness
/// percentage.
#[test]
fn aarch64_emittable_coverage_is_honest_under_strict() {
    // Thirteen rows below stand on captured encoder words; refuse a stale capture.
    assert_a64_value_corpus_is_what_the_live_encoder_emits();
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::AArch64));
    // Always print the full audit so the allowlist + degenerate-backed rows stay
    // visible in CI logs (honest gate, not silently truncated).
    eprintln!("{}", report.audit_log());

    assert!(
        report.emittable_count() > 0,
        "AArch64 audit found zero emittable opcodes — classifier is mis-wired"
    );

    // The denominator is every emitted AArch64 value/effect opcode. A covered
    // row is credited by a non-degenerate accepted obligation (static-DB proof,
    // reconstruction, or decoded-word obligation over the live encoder's words);
    // every uncovered row is a named DeferredUnfaithfulModel RED row, and no
    // emitted row lacks a mapping.
    // Per-opcode ratio history: docs/archive/session-reports/2026-09-proof-gate-count-ladders.md.
    //
    // RorRI's credit is DOUBLY sourced and both sources must stay wired: the
    // width-complete W+X registered rotate obligations AND the width- and
    // immediate-sensitive per-instruction EXTR-alias reconstruction — exactly
    // the two disjuncts its old deferred reason named as missing. The ordering
    // of the last two moves is immaterial: taking StrbRO/StrhRO first gives
    // 155/248 with 93 RED rows, and RorRI's discharge then lands on the same
    // 156/248 inventory with 92 named RED rows (the checked-i128 Adcs/Sbcs
    // rows then entered covered: 158/250 with the same 92 RED).
    //
    // PUBLICATION HONESTY: the emitted value/effect denominator includes the 94
    // forms previously hidden in the historical fail-closed/covered-elsewhere
    // bucket (memory effects, atomics, value copies/selects/conversions, and
    // emitted NEON permute/reduce/memory forms). Existing non-degenerate accepted
    // obligations still earn evidence credit; every unfaithfully modeled form is
    // a named DeferredUnfaithfulModel RED row. No emitted row lacks a mapping.
    // This is accepted-obligation
    // evidence coverage, not a formal-correctness percentage.
    assert_eq!(
        report.emittable_count(),
        302,
        "AArch64 emitted value/effect denominator changed; update the pin deliberately"
    );
    // On a host whose checker a certificate manifest does not authorize, the
    // bound-memory and atomic rows fail closed (`checker_identity_misses`).
    let misses = checker_identity_misses(&report);
    assert_eq!(
        report.covered_count() + misses,
        267,
        "AArch64 accepted-obligation count changed; do not re-admit X==X identities or hide \
         emitted value/effect debt outside the denominator:\n{}",
        report.audit_log()
    );
    if misses == 0 {
        assert!(
            (report.coverage_percent() - (267.0 / 302.0 * 100.0)).abs() < f64::EPSILON,
            "AArch64 accepted-obligation ratio drifted from the honest 267/302"
        );
    }

    // The 35-row table: FRINTN, the 29 LL/SC rows,
    // the two TLSLE TPREL adds and the three TLSDESC slots. Any missing
    // mapping or other finding class is a new regression; exclusion would
    // shrink the denominator.
    assert!(
        !report.is_clean(),
        "AArch64 must honestly retain the pinned emitted value/effect model gaps"
    );
    let failures: Vec<_> = report
        .failures()
        .into_iter()
        .filter(|row| {
            !row.note
                .contains(trust_cg_verify::bound_memory_authority::CHECKER_IDENTITY_MISS)
        })
        .collect();
    assert_eq!(
        failures.len(),
        35,
        "AArch64 must have exactly the 35 deferred rows:\n{}",
        report.failure_summary()
    );
    let actual_unmapped: Vec<_> = failures
        .iter()
        .filter(|row| matches!(row.finding, Some(CoverageFinding::NoProofMapping)))
        .map(|row| row.opcode_display.clone())
        .collect();
    assert!(
        actual_unmapped.is_empty(),
        "no AArch64 row may be NoProofMapping: {actual_unmapped:?}"
    );
    for op in [
        AArch64Opcode::Fcmp,
        AArch64Opcode::CSet,
        AArch64Opcode::Csel,
        AArch64Opcode::Csinc,
        AArch64Opcode::Csneg,
    ] {
        let row = report
            .rows
            .iter()
            .find(|row| row.opcode_display == format!("AArch64::{op:?}"))
            .unwrap_or_else(|| panic!("AArch64::{op:?} missing from audit universe"));
        assert!(row.finding.is_none(), "{row:?}");
        assert!(
            row.note.contains("NZCV PRODUCER/CONSUMER") && row.note.contains("NOT a formal proof"),
            "AArch64::{op:?} must be credited by the flag-consumer family: {}",
            row.note
        );
        assert!(aarch64_deferred_value_op_reason(op).is_none());
    }
    for op in trust_cg_verify::aarch64_crc32_proofs::CRC32_OPCODES {
        let row = report
            .rows
            .iter()
            .find(|row| row.opcode_display == format!("AArch64::{op:?}"))
            .unwrap_or_else(|| panic!("AArch64::{op:?} missing from audit universe"));
        assert!(row.finding.is_none(), "{row:?}");
        assert!(
            row.note.contains("CRC32 DECODED-WORD") && row.note.contains("NOT a formal proof"),
            "AArch64::{op:?} must be credited by the CRC32 family: {}",
            row.note
        );
        assert!(aarch64_deferred_value_op_reason(op).is_none());
        assert!(
            trust_cg_verify::FunctionVerifier::opcode_to_proof_query(op).is_none(),
            "AArch64::{op:?} must not be credited opcode-wide"
        );
    }
    let expected_deferred: std::collections::HashSet<_> = ALL_AARCH64_OPCODES
        .iter()
        .copied()
        .filter(|&op| aarch64_deferred_value_op_reason(op).is_some())
        .map(|op| format!("AArch64::{op:?}"))
        .collect();
    assert_eq!(
        expected_deferred.len(),
        35,
        "the deferred table must retain the three TLSDESC slots, the 29 LL/SC atomic rows, \
         the two TLSLE TPREL adds and FRINTN"
    );
    // The TLSLE TPREL adds: counted, RED, and bound to nothing in the
    // function verifier (no opcode-wide query).
    for op in [AArch64Opcode::AddTprelHi12, AArch64Opcode::AddTprelLo12] {
        assert!(matches!(
            classify_aarch64(op),
            OpcodeClass::EmittableNeedsProof
        ));
        let reason = aarch64_deferred_value_op_reason(op)
            .unwrap_or_else(|| panic!("AArch64::{op:?} must be a named deferred row"));
        assert!(
            reason.contains("TPREL") && reason.contains("ENC-5"),
            "{reason}"
        );
        assert!(
            trust_cg_verify::FunctionVerifier::opcode_to_proof_query(op).is_none(),
            "AArch64::{op:?} must not be credited opcode-wide"
        );
    }
    let actual_deferred: std::collections::HashSet<_> = failures
        .iter()
        .filter(|row| {
            matches!(
                row.finding,
                Some(CoverageFinding::DeferredUnfaithfulModel { .. })
            )
        })
        .map(|row| row.opcode_display.clone())
        .collect();
    assert_eq!(
        actual_deferred, expected_deferred,
        "AArch64 deferred rows must be exactly the unchanged named debt table"
    );
    assert!(
        failures.iter().all(|row| matches!(
            row.finding,
            Some(CoverageFinding::DeferredUnfaithfulModel { .. } | CoverageFinding::NoProofMapping)
        )),
        "an unrecognized AArch64 finding class is a regression:\n{}",
        report.failure_summary()
    );

    // The LL/SC pseudos appear in every pre-allocation stream the function
    // verifier sees and the exclusives/CLREX are emitted by their post-RA
    // expansion: all 29 are named RED denominator rows, never exclusions.
    for op in [
        AArch64Opcode::Ldaxr,
        AArch64Opcode::Stlxr,
        AArch64Opcode::Ldxr,
        AArch64Opcode::Ldxrb,
        AArch64Opcode::Ldxrh,
        AArch64Opcode::Ldaxrb,
        AArch64Opcode::Ldaxrh,
        AArch64Opcode::Stxr,
        AArch64Opcode::Stxrb,
        AArch64Opcode::Stxrh,
        AArch64Opcode::Stlxrb,
        AArch64Opcode::Stlxrh,
        AArch64Opcode::Clrex,
        AArch64Opcode::LlscRmw8,
        AArch64Opcode::LlscRmw16,
        AArch64Opcode::LlscRmw32,
        AArch64Opcode::LlscRmw64,
        AArch64Opcode::LlscCmpSwap8,
        AArch64Opcode::LlscCmpSwap16,
        AArch64Opcode::LlscCmpSwap32,
        AArch64Opcode::LlscCmpSwap64,
        AArch64Opcode::Ldxp,
        AArch64Opcode::Ldaxp,
        AArch64Opcode::Stxp,
        AArch64Opcode::Stlxp,
        AArch64Opcode::LlscLoad128,
        AArch64Opcode::LlscStore128,
        AArch64Opcode::LlscRmw128,
        AArch64Opcode::LlscCmpSwap128,
    ] {
        assert!(
            matches!(classify_aarch64(op), OpcodeClass::EmittableNeedsProof),
            "AArch64::{op:?} must stay in the emitted value/effect denominator"
        );
        assert!(
            aarch64_deferred_value_op_reason(op).is_some(),
            "AArch64::{op:?} must be named LL/SC RED debt"
        );
    }

    // The six volatile forms added after the original 93-row publication audit
    // are emitted effects, not structural exclusions. Their preservation facet
    // (X-OPCODES-P6: every path's volatile accesses kept in order, decided per
    // compile) holds, and each is covered with its credited plain row
    // (`aarch64_volatile_rows_need_both_facets`).
    for op in [
        AArch64Opcode::VolatileLdrRI,
        AArch64Opcode::VolatileStrRI,
        AArch64Opcode::VolatileLdrbRI,
        AArch64Opcode::VolatileLdrhRI,
        AArch64Opcode::VolatileStrbRI,
        AArch64Opcode::VolatileStrhRI,
    ] {
        let row = report
            .rows
            .iter()
            .find(|row| row.opcode_display == format!("AArch64::{op:?}"))
            .unwrap_or_else(|| panic!("AArch64::{op:?} missing from audit universe"));
        assert!(aarch64_deferred_value_op_reason(op).is_none());
        if misses > 0 && row.finding.is_some() {
            assert!(
                row.note
                    .contains(trust_cg_verify::bound_memory_authority::CHECKER_IDENTITY_MISS),
                "{row:?}"
            );
            continue;
        }
        assert!(row.finding.is_none(), "{row:?}");
        assert!(
            row.note.starts_with("VOLATILE")
                && row.note.contains("BOUND-MEMORY FORM CERTIFICATES")
                && row.note.contains("volatile access preservation"),
            "AArch64::{op:?} must be covered by both facets: {}",
            row.note
        );
    }

    // The bound-memory rows: every atomic opcode, every scalar memory opcode,
    // every pair opcode and the two NEON LD1/ST1 post-index opcodes are
    // covered by their per-form certificates, and nothing else is.
    let bound: Vec<_> = report
        .rows
        .iter()
        .filter(|row| row.note.starts_with("BOUND-MEMORY FORM CERTIFICATES"))
        .map(|row| row.opcode_display.clone())
        .collect();
    let missed_bound = report
        .rows
        .iter()
        .filter(|row| {
            row.finding.is_some()
                && row.note.starts_with("bound_memory_row_credit::")
                && row
                    .note
                    .contains(trust_cg_verify::bound_memory_authority::CHECKER_IDENTITY_MISS)
        })
        .count();
    assert_eq!(bound.len() + missed_bound, 46 + 18 + 6 + 2, "{bound:?}");
    for op in trust_cg_verify::aarch64_atomic_forms::ATOMIC_MEMORY_OPCODES {
        assert!(
            misses > 0 || bound.contains(&format!("AArch64::{op:?}")),
            "{op:?}"
        );
        assert!(aarch64_deferred_value_op_reason(op).is_none());
    }
}

/// Ledger `L04-P3`: every emitted scalar FP conversion, rounding and
/// arithmetic row carries the named IEEE 754 testing evidence in its note and
/// no other row does. The annotation is a pure note append, so it credits
/// nothing: FRINTN stays RED, every other row keeps whatever its own
/// obligation decided, and the accepted count pinned above is unchanged.
#[test]
fn scalar_fp_rows_carry_named_ieee_evidence_without_credit() {
    use trust_cg_verify::coverage_gate::{OpcodeAuditRow, with_named_fp_ieee_evidence};
    use trust_cg_verify::fp_ieee_evidence;
    const MARK: &str = "L04-P3 named TESTING evidence, NOT credit";
    let named = fp_ieee_evidence::opcodes();
    assert_eq!(named.len(), 24);
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::AArch64));
    for row in &report.rows {
        let is_named = named
            .iter()
            .any(|op| row.opcode_display == format!("AArch64::{op:?}"));
        assert_eq!(
            row.note.contains(MARK),
            is_named,
            "{}: {}",
            row.opcode_display,
            row.note
        );
        if is_named {
            assert_eq!(
                row.class,
                OpcodeClass::EmittableNeedsProof,
                "{}",
                row.opcode_display
            );
        }
    }
    let frintn = report
        .rows
        .iter()
        .find(|row| row.opcode_display == "AArch64::FrintnRR")
        .expect("FRINTN row");
    assert!(
        matches!(
            frintn.finding,
            Some(CoverageFinding::DeferredUnfaithfulModel { .. })
        ),
        "FRINTN must stay named RED debt: {frintn:?}"
    );
    for finding in [None, Some(CoverageFinding::NoProofMapping)] {
        let row = OpcodeAuditRow {
            opcode_display: "AArch64::FaddRR".into(),
            class: OpcodeClass::EmittableNeedsProof,
            finding,
            note: "own obligation".into(),
        };
        let annotated = with_named_fp_ieee_evidence(AArch64Opcode::FaddRR, row.clone());
        assert_eq!(
            (&annotated.class, &annotated.finding),
            (&row.class, &row.finding)
        );
        assert!(
            annotated.note.starts_with("own obligation; L04-P3"),
            "{}",
            annotated.note
        );
        assert_eq!(
            with_named_fp_ieee_evidence(AArch64Opcode::AddRR, row.clone()),
            row
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

/// RorRI is now emitted STANDALONE (the rotate recognizer emits it when the EOR
/// does not fuse), so its coverage credit must come from the complete W+X rotate
/// pair and the row must no longer sit in the deferred-value-op table.
#[test]
fn aarch64_ror_immediate_is_covered_by_complete_width_pair() {
    let proofs = aarch64_width_polymorphic_proofs(AArch64Opcode::RorRI)
        .expect("standalone RorRI must be width-complete gated");
    assert_eq!(proofs.len(), 2);
    assert!(proofs.iter().any(|p| p.encoded_width_bits == 32));
    assert!(proofs.iter().any(|p| p.encoded_width_bits == 64));
    assert!(
        aarch64_deferred_value_op_reason(AArch64Opcode::RorRI).is_none(),
        "RorRI is credited via all_ror_immediate_proofs and must not stay deferred"
    );
}

/// X-OPCODES-P10: MOVK and MOVN are polymorphic over (width, halfword shift).
/// Their per-form obligations were already bound per instruction, but the gate
/// had no mechanism to demand all of them, so both rows sat in the deferred
/// table. The form-polymorphic gate must name EXACTLY the architecturally legal
/// forms, each with the query the function verifier binds for that form, and
/// every form's proof must be non-degenerate and discharge. The illegal W-form
/// `#32`/`#48` shifts must bind nothing, and an incomplete, duplicated,
/// illegal-form or mis-queried table must turn the row RED.
#[test]
fn aarch64_move_wide_rows_require_every_legal_form() {
    use trust_cg_ir::{MachInst, MachOperand, RegClass, VReg};
    use trust_cg_verify::FunctionVerifier;
    use trust_cg_verify::const_materialize_proofs::{
        MOVK_HALFWORD_FORMS, MOVN_FORMS, movk_halfword_query, movn_halfword_query,
    };
    use trust_cg_verify::coverage_gate::{
        AARCH64_MOVE_WIDE_LEGAL_FORMS, FormProof, aarch64_form_polymorphic_proofs,
    };
    use trust_cg_verify::proof_database::ProofCategory;

    let mut legal: Vec<(u32, u32)> = AARCH64_MOVE_WIDE_LEGAL_FORMS.to_vec();
    legal.sort_unstable();
    for (opcode, query_of, proof_forms) in [
        (
            AArch64Opcode::Movk,
            movk_halfword_query as fn(u32, u32) -> Option<&'static str>,
            MOVK_HALFWORD_FORMS,
        ),
        (AArch64Opcode::Movn, movn_halfword_query, MOVN_FORMS),
    ] {
        let forms = aarch64_form_polymorphic_proofs(opcode)
            .unwrap_or_else(|| panic!("{opcode:?} must be form-polymorphic gated"));
        let mut named: Vec<(u32, u32)> = forms.iter().map(|f| (f.width_bits, f.shift)).collect();
        named.sort_unstable();
        assert_eq!(named, legal, "{opcode:?} must name exactly the legal forms");
        let mut registered = proof_forms.to_vec();
        registered.sort_unstable();
        assert_eq!(
            registered, legal,
            "{opcode:?} registers exactly one obligation per legal form"
        );
        assert!(
            aarch64_width_polymorphic_proofs(opcode).is_none(),
            "{opcode:?} must not also be width-gated"
        );
        assert!(aarch64_deferred_value_op_reason(opcode).is_none());
        assert!(FunctionVerifier::opcode_to_proof_query(opcode).is_none());
        for form in forms {
            assert_eq!(form.category, ProofCategory::ConstantMaterialization);
            assert_eq!(
                Some(form.query),
                query_of(form.width_bits, form.shift),
                "{opcode:?} gate query drifted from the per-form query"
            );
            let class = if form.width_bits == 32 {
                RegClass::Gpr32
            } else {
                RegClass::Gpr64
            };
            let inst = MachInst::new(
                opcode,
                vec![
                    MachOperand::VReg(VReg::new(0, class)),
                    MachOperand::Imm(0x1234),
                    MachOperand::Imm(i64::from(form.shift)),
                ],
            );
            assert_eq!(
                FunctionVerifier::inst_to_proof_query(&inst),
                Some((form.query, ProofCategory::ConstantMaterialization)),
                "{opcode:?} (w{}, lsl #{}) must bind exactly the gated obligation",
                form.width_bits,
                form.shift
            );
        }
        for shift in [32, 48] {
            let illegal = MachInst::new(
                opcode,
                vec![
                    MachOperand::VReg(VReg::new(0, RegClass::Gpr32)),
                    MachOperand::Imm(0x1234),
                    MachOperand::Imm(shift),
                ],
            );
            assert_eq!(FunctionVerifier::inst_to_proof_query(&illegal), None);
            assert_eq!(query_of(32, shift as u32), None);
        }
    }

    let (report, broken_rows) = on_large_stack(|| {
        let gate = CoverageGate::new();
        let report = gate.audit(GateArch::AArch64);
        let movk = aarch64_form_polymorphic_proofs(AArch64Opcode::Movk).unwrap();
        let movn = aarch64_form_polymorphic_proofs(AArch64Opcode::Movn).unwrap();
        let missing: Vec<FormProof> = movk[..movk.len() - 1].to_vec();
        let mut duplicated = movk.to_vec();
        duplicated.push(movk[0]);
        let mut illegal = movk.to_vec();
        illegal.push(FormProof {
            shift: 32,
            width_bits: 32,
            ..movk[4]
        });
        // A form whose query names a proof that does not exist.
        let mut absent = movk.to_vec();
        absent[2].query = "movk xd #imm16, lsl #32 does not exist";
        // A form whose query names a registered proof of the wrong category.
        let mut wrong_category = movn.to_vec();
        wrong_category[3].category = ProofCategory::Arithmetic;
        let broken = [missing, duplicated, illegal, absent]
            .iter()
            .map(|table| gate.audit_aarch64_form_table(AArch64Opcode::Movk, table))
            .chain(std::iter::once(gate.audit_aarch64_form_table(
                AArch64Opcode::Movn,
                &wrong_category,
            )))
            .collect::<Vec<_>>();
        (report, broken)
    });
    let broken = broken_rows;
    for opcode in [AArch64Opcode::Movk, AArch64Opcode::Movn] {
        let row = report
            .rows
            .iter()
            .find(|row| row.opcode_display == format!("AArch64::{opcode:?}"))
            .expect("move-wide rows stay in the emitted value/effect denominator");
        assert!(matches!(
            classify_aarch64(opcode),
            OpcodeClass::EmittableNeedsProof
        ));
        assert!(
            row.finding.is_none(),
            "{opcode:?} must be covered by every legal form: {}",
            row.note
        );
        assert!(row.note.contains("FORM-POLYMORPHIC"), "{}", row.note);
        // MOVN's only input is the 16-bit immediate, so each form is checked
        // over its complete domain; MOVK also quantifies over the prior
        // register value and is sampled. Neither is labelled a formal proof.
        let (label, why) = match opcode {
            AArch64Opcode::Movn => ("[Exhaustive]", "complete 16-bit immediate domain"),
            _ => ("NOT a formal proof", "sampled evaluator acceptance"),
        };
        assert_eq!(
            row.note.matches(label).count(),
            AARCH64_MOVE_WIDE_LEGAL_FORMS.len(),
            "every {opcode:?} form must carry its {why} label: {}",
            row.note
        );
        assert!(!row.note.contains("[Formal]"), "{}", row.note);
    }
    assert_eq!(broken.len(), 5);
    for row in &broken {
        assert!(
            row.finding.is_some(),
            "a broken form table must leave the move-wide row RED: {}",
            row.note
        );
    }
}

/// The sixteen rows X-OPCODES-P7/P8/P9 and L04-P11 (the typed
/// post-allocation copies and the ORR (vector) register copy) credit through
/// decoded-word obligations.
const DECODED_VALUE_OPCODES: [AArch64Opcode; 16] = [
    AArch64Opcode::MovR,
    AArch64Opcode::MOVWrr,
    AArch64Opcode::MOVXrr,
    AArch64Opcode::FmovFprFpr,
    AArch64Opcode::FmovFprGpr,
    AArch64Opcode::FmovGprFpr,
    AArch64Opcode::NeonOrrV,
    AArch64Opcode::Smull,
    AArch64Opcode::Bfm,
    AArch64Opcode::Rbit,
    AArch64Opcode::AddRIShift12,
    AArch64Opcode::Mrs,
    AArch64Opcode::FcvtHS,
    AArch64Opcode::FcvtHD,
    AArch64Opcode::FcvtSH,
    AArch64Opcode::FcvtDH,
];

/// X-OPCODES-P7/P8/P9: the register copies, the scalar value forms and the
/// half-precision FCVT forms leave the
/// deferred table ONLY through decoded-word obligations. Each row stays in the
/// denominator, names its decoded-word evidence and every form's registered
/// obligation, and every form's query resolves, in the database the function
/// verifier consults, to exactly that obligation. Every one of the sixteen
/// opcodes binds one form per concrete instruction; since L04-P11 that
/// includes the register copies (MovR, the typed post-allocation MOVWrr/MOVXrr
/// and the FMOVs), which the function verifier used to promote per instruction
/// as covered-elsewhere whatever their shape, and the ORR (vector) register
/// copy, which it used to credit opcode-wide through the lanewise ORR
/// obligation. That row also needs the lanewise obligation, which binds the
/// three-register 16B OR per instruction.
#[test]
fn aarch64_decoded_value_rows_are_credited_by_every_form() {
    use trust_cg_ir::{MachInst, MachOperand, RegClass, VReg};
    use trust_cg_verify::FunctionVerifier;
    use trust_cg_verify::aarch64_value_decode_proofs::{
        A64_VALUE_OPCODES_BOUND_PER_INSTRUCTION, A64ValueForm, TPIDR_EL0_KEY, a64_value_forms,
    };

    assert_a64_value_corpus_is_what_the_live_encoder_emits();
    let mut forms_seen = Vec::new();
    for op in DECODED_VALUE_OPCODES {
        assert!(matches!(
            classify_aarch64(op),
            OpcodeClass::EmittableNeedsProof
        ));
        assert!(
            aarch64_deferred_value_op_reason(op).is_none(),
            "{op:?} must have left the deferred table"
        );
        let forms = a64_value_forms(op).unwrap_or_else(|| panic!("{op:?} has no forms"));
        assert!(forms.iter().all(|form| form.opcode() == op));
        forms_seen.extend_from_slice(forms);
    }
    assert_eq!(forms_seen, A64ValueForm::ALL.to_vec());

    let (report, resolved) = on_large_stack(|| {
        let report = CoverageGate::new().audit(GateArch::AArch64);
        let db = ProofDatabase::new();
        let resolved: Vec<(A64ValueForm, Option<String>)> = A64ValueForm::ALL
            .iter()
            .map(|&form| {
                let name = db
                    .by_category(form.category())
                    .into_iter()
                    .find(|p| p.obligation.name.to_lowercase().contains(form.query()))
                    .map(|p| p.obligation.name.clone());
                (form, name)
            })
            .collect();
        (report, resolved)
    });
    for (form, name) in resolved {
        assert_eq!(
            name.as_deref(),
            Some(form.obligation_name()),
            "{form:?} query must resolve to its own obligation"
        );
    }
    for op in DECODED_VALUE_OPCODES {
        let row = report
            .rows
            .iter()
            .find(|row| row.opcode_display == format!("AArch64::{op:?}"))
            .unwrap_or_else(|| panic!("{op:?} missing from the audit"));
        assert!(
            row.finding.is_none(),
            "{op:?} must be credited: {}",
            row.note
        );
        assert!(row.note.starts_with("DECODED-WORD"), "{}", row.note);
        for form in a64_value_forms(op).unwrap() {
            assert!(
                row.note.contains(form.obligation_name()),
                "{op:?} note must name {form:?}: {}",
                row.note
            );
        }
        assert!(!row.note.contains("[Formal]"), "{}", row.note);
        if op == AArch64Opcode::NeonOrrV {
            assert!(
                row.note.contains("three-register 16B OR"),
                "the ORR (vector) row must name its lanewise credit: {}",
                row.note
            );
        }
    }

    for op in DECODED_VALUE_OPCODES {
        // No opcode-wide credit: only a concrete instance binds, per form.
        assert!(FunctionVerifier::opcode_to_proof_query(op).is_none());
        assert!(A64_VALUE_OPCODES_BOUND_PER_INSTRUCTION.contains(&op));
        assert!(
            !trust_cg_verify::function_verifier::is_covered_elsewhere_indirect_branch(
                trust_cg_verify::function_verifier::InstructionOpcode::AArch64(op)
            ),
            "{op:?} must not be promoted as covered-elsewhere"
        );
    }
    let g64 = |id| MachOperand::VReg(VReg::new(id, RegClass::Gpr64));
    let g32 = |id| MachOperand::VReg(VReg::new(id, RegClass::Gpr32));
    let f16 = |id| MachOperand::VReg(VReg::new(id, RegClass::Fpr16));
    let f32 = |id| MachOperand::VReg(VReg::new(id, RegClass::Fpr32));
    let f64 = |id| MachOperand::VReg(VReg::new(id, RegClass::Fpr64));
    let f128 = |id| MachOperand::VReg(VReg::new(id, RegClass::Fpr128));
    let imm = MachOperand::Imm;
    for (inst, form) in [
        (
            MachInst::new(AArch64Opcode::NeonOrrV, vec![f128(0), f128(1), f128(1)]),
            A64ValueForm::MovV16B,
        ),
        (
            MachInst::new(
                AArch64Opcode::NeonOrrV,
                vec![f64(0), f64(1), f64(1), imm(1)],
            ),
            A64ValueForm::MovV16B,
        ),
        (
            MachInst::new(AArch64Opcode::MovR, vec![g64(0), g64(1)]),
            A64ValueForm::MovX,
        ),
        (
            MachInst::new(AArch64Opcode::MovR, vec![g32(0), g32(1)]),
            A64ValueForm::MovW,
        ),
        (
            MachInst::new(AArch64Opcode::MOVWrr, vec![g32(0), g32(1)]),
            A64ValueForm::MovWrr,
        ),
        (
            MachInst::new(AArch64Opcode::MOVXrr, vec![g64(0), g64(1)]),
            A64ValueForm::MovXrr,
        ),
        (
            MachInst::new(AArch64Opcode::FmovFprFpr, vec![f64(0), f64(1)]),
            A64ValueForm::FmovD,
        ),
        (
            MachInst::new(AArch64Opcode::FmovFprGpr, vec![g32(0), f32(1)]),
            A64ValueForm::FmovWFromS,
        ),
        (
            MachInst::new(AArch64Opcode::FmovGprFpr, vec![f64(0), g64(1)]),
            A64ValueForm::FmovDFromX,
        ),
        (
            MachInst::new(AArch64Opcode::FcvtHS, vec![f32(0), f16(1)]),
            A64ValueForm::FcvtSFromH,
        ),
        (
            MachInst::new(AArch64Opcode::FcvtHD, vec![f64(0), f16(1)]),
            A64ValueForm::FcvtDFromH,
        ),
        (
            MachInst::new(AArch64Opcode::FcvtSH, vec![f16(0), f32(1)]),
            A64ValueForm::FcvtHFromS,
        ),
        (
            MachInst::new(AArch64Opcode::FcvtDH, vec![f16(0), f64(1)]),
            A64ValueForm::FcvtHFromD,
        ),
        (
            MachInst::new(AArch64Opcode::Smull, vec![g64(0), g32(1), g32(2)]),
            A64ValueForm::Smull,
        ),
        (
            MachInst::new(AArch64Opcode::Bfm, vec![g32(0), g32(1), imm(24), imm(4)]),
            A64ValueForm::BfmInsertW,
        ),
        (
            MachInst::new(AArch64Opcode::Bfm, vec![g64(0), g64(1), imm(56), imm(4)]),
            A64ValueForm::BfmInsertX,
        ),
        (
            MachInst::new(AArch64Opcode::Rbit, vec![g32(0), g32(1)]),
            A64ValueForm::RbitW,
        ),
        (
            MachInst::new(AArch64Opcode::Rbit, vec![g64(0), g64(1)]),
            A64ValueForm::RbitX,
        ),
        (
            MachInst::new(AArch64Opcode::AddRIShift12, vec![g32(0), g32(1), imm(7)]),
            A64ValueForm::AddLsl12W,
        ),
        (
            MachInst::new(AArch64Opcode::AddRIShift12, vec![g64(0), g64(0), imm(7)]),
            A64ValueForm::AddLsl12X,
        ),
        (
            MachInst::new(
                AArch64Opcode::Mrs,
                vec![g64(0), imm(i64::from(TPIDR_EL0_KEY))],
            ),
            A64ValueForm::MrsTpidrEl0,
        ),
    ] {
        assert_eq!(
            FunctionVerifier::inst_to_proof_query(&inst),
            Some((form.query(), form.category())),
            "{inst:?} must bind exactly {form:?}"
        );
    }
    // Refused shapes never fall back to an opcode-wide query.
    for inst in [
        MachInst::new(AArch64Opcode::Smull, vec![g32(0), g32(1), g32(2)]),
        MachInst::new(AArch64Opcode::Bfm, vec![g64(0), g64(1), imm(4), imm(10)]),
        MachInst::new(AArch64Opcode::AddRIShift12, vec![g64(0), g64(1), imm(4096)]),
        MachInst::new(AArch64Opcode::Mrs, vec![g64(0), imm(0xDE83)]),
        // Copies outside the forms: half precision and cross-width FMOVs.
        MachInst::new(AArch64Opcode::FmovFprFpr, vec![f16(0), f16(1)]),
        MachInst::new(AArch64Opcode::FmovFprGpr, vec![g64(0), f32(1)]),
        MachInst::new(AArch64Opcode::MovR, vec![]),
        // FCVT operand widths that name another conversion.
        MachInst::new(AArch64Opcode::FcvtHS, vec![f64(0), f16(1)]),
        MachInst::new(AArch64Opcode::FcvtSH, vec![f32(0), f16(1)]),
        MachInst::new(AArch64Opcode::FcvtDH, vec![f16(0), f32(1)]),
        // ORR (vector): the 8B OR, the 8B copy, the selector on a
        // three-register OR, an unknown selector.
        MachInst::new(AArch64Opcode::NeonOrrV, vec![f64(0), f64(1), f64(2)]),
        MachInst::new(AArch64Opcode::NeonOrrV, vec![f64(0), f64(1), f64(1)]),
        MachInst::new(
            AArch64Opcode::NeonOrrV,
            vec![f128(0), f128(1), f128(2), imm(1)],
        ),
        MachInst::new(
            AArch64Opcode::NeonOrrV,
            vec![f128(0), f128(1), f128(1), imm(7)],
        ),
    ] {
        assert_eq!(
            FunctionVerifier::inst_to_proof_query(&inst),
            None,
            "{inst:?}"
        );
    }
    // The three-register 16B OR binds the lanewise ORR obligation.
    assert_eq!(
        FunctionVerifier::inst_to_proof_query(&MachInst::new(
            AArch64Opcode::NeonOrrV,
            vec![f128(0), f128(1), f128(2)],
        )),
        Some((
            "orrv.16b lanewise-intent",
            trust_cg_verify::proof_database::ProofCategory::NeonLowering
        ))
    );
}

/// A decoded-value hook that stops accepting must turn exactly the sixteen
/// rows RED as `ProofNotDischarged` — never a quiet deferral — and cost
/// exactly sixteen covered rows, leaving every other row unchanged.
#[test]
fn aarch64_decoded_value_hook_failure_is_red_in_the_whole_report() {
    let (real, injected) = on_large_stack(|| {
        let gate = CoverageGate::new();
        let real = gate.audit(GateArch::AArch64);
        let injected = gate.audit_aarch64_with_value_credit(&|_| {
            Err("INJECTED: a negative control survived".to_string())
        });
        (real, injected)
    });
    assert_eq!(
        injected.covered_count() + DECODED_VALUE_OPCODES.len(),
        real.covered_count()
    );
    for (real_row, injected_row) in real.rows.iter().zip(&injected.rows) {
        assert_eq!(real_row.opcode_display, injected_row.opcode_display);
        let decoded = DECODED_VALUE_OPCODES
            .iter()
            .any(|op| real_row.opcode_display == format!("AArch64::{op:?}"));
        if decoded {
            match &injected_row.finding {
                Some(CoverageFinding::ProofNotDischarged { detail, .. }) => {
                    assert!(detail.contains("INJECTED"), "{detail}");
                }
                other => panic!(
                    "{} must be ProofNotDischarged under a failing hook, got {other:?}",
                    real_row.opcode_display
                ),
            }
        } else {
            assert_eq!(real_row.finding, injected_row.finding);
        }
    }
}

/// L04-P10: the `Umulh` row is covered only with BOTH its 64-bit checked-umul
/// obligation and the i128 checked-multiply idiom family. With the real hook
/// the row is covered and its note names the idiom credit; a hook that stops
/// accepting (a surviving negative control) turns exactly that one row RED as
/// `ProofNotDischarged` — never a quiet deferral — and costs exactly one
/// covered row, leaving every other row unchanged.
#[test]
fn umulh_row_requires_the_i128_checked_mul_family_credit() {
    let (real, injected) = on_large_stack(|| {
        let gate = CoverageGate::new();
        let real = gate.audit(GateArch::AArch64);
        let injected = gate.audit_aarch64_with_checked_mul_i128_credit(&|| {
            Err("INJECTED: a negative control survived".to_string())
        });
        (real, injected)
    });
    let umulh = real
        .rows
        .iter()
        .find(|row| row.opcode_display == "AArch64::Umulh")
        .expect("Umulh row");
    assert_eq!(umulh.finding, None, "{}", umulh.note);
    assert!(
        umulh.note.contains("i128 checked-multiply idiom credit"),
        "{}",
        umulh.note
    );
    assert!(
        umulh.note.contains("CheckedUmul_I64") && umulh.note.contains("CheckedUmul_I128"),
        "both the 64-bit and the i128 obligations must be named: {}",
        umulh.note
    );
    assert!(
        umulh.note.contains("NOT a formal proof"),
        "the note must state the evidence strength: {}",
        umulh.note
    );
    assert_eq!(injected.covered_count() + 1, real.covered_count());
    for (real_row, injected_row) in real.rows.iter().zip(&injected.rows) {
        assert_eq!(real_row.opcode_display, injected_row.opcode_display);
        if real_row.opcode_display == "AArch64::Umulh" {
            match &injected_row.finding {
                Some(CoverageFinding::ProofNotDischarged { detail, .. }) => {
                    assert!(detail.contains("INJECTED"), "{detail}");
                }
                other => {
                    panic!("Umulh must be ProofNotDischarged under a failing hook, got {other:?}")
                }
            }
        } else {
            assert_eq!(real_row.finding, injected_row.finding);
        }
    }
}

const VOLATILE_OPCODES: [AArch64Opcode; 6] = [
    AArch64Opcode::VolatileLdrRI,
    AArch64Opcode::VolatileLdrbRI,
    AArch64Opcode::VolatileLdrhRI,
    AArch64Opcode::VolatileStrRI,
    AArch64Opcode::VolatileStrbRI,
    AArch64Opcode::VolatileStrhRI,
];

/// The volatile rows whose plain counterpart is still RED: none since L04-P1.
const VOLATILE_DEFERRED: [AArch64Opcode; 0] = [];

/// X-OPCODES-P6: a volatile row needs BOTH facets. With the real hooks the
/// preservation facet holds and every plain row is credited (L04-P1), so the
/// six rows are covered, their notes recording both facets. A failing
/// preservation hook turns exactly the six rows `ProofNotDischarged` (a
/// regression, never a quiet deferral); a plain row injected as credited
/// changes nothing more.
#[test]
fn aarch64_volatile_rows_need_both_facets() {
    use trust_cg_verify::coverage_gate::{OpcodeAuditRow, aarch64_volatile_plain_counterpart};
    use trust_cg_verify::volatile_access_preservation::volatile_preservation_credit;

    let credited_plain = |plain: AArch64Opcode| OpcodeAuditRow {
        opcode_display: format!("AArch64::{plain:?}"),
        class: OpcodeClass::EmittableNeedsProof,
        finding: None,
        note: "ANTICIPATED plain memory-model credit (test seam)".to_string(),
    };
    let (real, failing, anticipated, anticipated_failing) = on_large_stack(move || {
        let gate = CoverageGate::new();
        let real = gate.audit(GateArch::AArch64);
        let failing = gate.audit_aarch64_with_volatile_hooks(
            &|| Err("INJECTED: a corrupted stream survived".to_string()),
            None,
        );
        let anticipated = gate.audit_aarch64_with_volatile_hooks(
            &volatile_preservation_credit,
            Some(&credited_plain),
        );
        let anticipated_failing = gate.audit_aarch64_with_volatile_hooks(
            &|| Err("INJECTED: a corrupted stream survived".to_string()),
            Some(&credited_plain),
        );
        (real, failing, anticipated, anticipated_failing)
    });
    let volatile = |row: &OpcodeAuditRow| {
        VOLATILE_OPCODES
            .iter()
            .any(|op| row.opcode_display == format!("AArch64::{op:?}"))
    };
    for op in VOLATILE_OPCODES {
        let plain = aarch64_volatile_plain_counterpart(op).unwrap();
        let deferred = VOLATILE_DEFERRED.contains(&op);
        assert_eq!(
            aarch64_deferred_value_op_reason(plain).is_some(),
            deferred,
            "{plain:?}"
        );
        assert_eq!(aarch64_deferred_value_op_reason(op).is_some(), deferred);
    }
    let misses = checker_identity_misses(&real);
    for (index, row) in real.rows.iter().enumerate() {
        if volatile(row) {
            let deferred = VOLATILE_DEFERRED
                .iter()
                .any(|op| row.opcode_display == format!("AArch64::{op:?}"));
            if misses > 0 && row.finding.is_some() {
                // An unqualified host: the plain row is a checker-identity
                // miss, so the volatile row is RED for that reason only.
                assert!(
                    row.note
                        .contains(trust_cg_verify::bound_memory_authority::CHECKER_IDENTITY_MISS),
                    "{row:?}"
                );
                continue;
            }
            assert!(
                row.note.contains("volatile access preservation"),
                "{}",
                row.note
            );
            if deferred {
                assert!(
                    matches!(
                        row.finding,
                        Some(CoverageFinding::DeferredUnfaithfulModel { .. })
                    ),
                    "{row:?}"
                );
                assert!(row.note.contains("X-OPCODES-P1"), "{}", row.note);
            } else {
                assert!(row.finding.is_none(), "{row:?}");
                assert!(
                    row.note.contains("BOUND-MEMORY FORM CERTIFICATES"),
                    "{}",
                    row.note
                );
            }
            assert!(
                matches!(
                    &failing.rows[index].finding,
                    Some(CoverageFinding::ProofNotDischarged { detail, .. }) if detail.contains("INJECTED")
                ),
                "{:?}",
                failing.rows[index]
            );
            assert!(
                anticipated.rows[index].finding.is_none(),
                "{:?}",
                anticipated.rows[index]
            );
            assert!(anticipated.rows[index].note.starts_with("VOLATILE"));
            assert!(matches!(
                anticipated_failing.rows[index].finding,
                Some(CoverageFinding::ProofNotDischarged { .. })
            ));
        } else {
            assert_eq!(
                row.finding, failing.rows[index].finding,
                "{}",
                row.opcode_display
            );
            assert_eq!(
                row.finding, anticipated.rows[index].finding,
                "{}",
                row.opcode_display
            );
        }
    }
    let volatile_covered = real
        .rows
        .iter()
        .filter(|row| volatile(row) && row.finding.is_none())
        .count();
    assert_eq!(
        anticipated.covered_count(),
        real.covered_count() + (VOLATILE_OPCODES.len() - volatile_covered)
    );
    assert_eq!(
        failing.covered_count(),
        real.covered_count() - volatile_covered
    );
    if misses == 0 {
        assert_eq!(
            volatile_covered,
            VOLATILE_OPCODES.len() - VOLATILE_DEFERRED.len()
        );
    }
}

/// L04-P1: a failing bound-memory credit hook turns exactly the 72
/// bound-memory rows and the six volatile rows that follow them out of the
/// covered count (the bound rows `ProofNotDischarged`: a regression, never a
/// quiet deferral).
#[test]
fn bound_memory_rows_need_every_form_and_a_failing_hook_is_red() {
    use trust_cg_verify::bound_memory_row_credit::{
        atomic_row_credit, neon_row_credit, pair_row_credit, scalar_row_credit,
    };
    let (real, failing) = on_large_stack(|| {
        let gate = CoverageGate::new();
        let real = gate.audit(GateArch::AArch64);
        let failing = gate.audit_aarch64_with_bound_memory_credit(&|opcode| {
            atomic_row_credit(opcode)
                .or_else(|| scalar_row_credit(opcode))
                .or_else(|| pair_row_credit(opcode))
                .or_else(|| neon_row_credit(opcode))
                .map(|_| Err("INJECTED: a form certificate did not replay".to_string()))
        });
        (real, failing)
    });
    let injected_finding = |injected: &trust_cg_verify::coverage_gate::OpcodeAuditRow| {
        matches!(
            &injected.finding,
            Some(CoverageFinding::ProofNotDischarged { detail, .. }) if detail.contains("INJECTED")
        ) || injected.note.contains("INJECTED")
    };
    let mut lost = 0;
    let mut missed = 0;
    for (row, injected) in real.rows.iter().zip(&failing.rows) {
        if row.finding.is_none() && injected.finding.is_some() {
            assert!(injected_finding(injected), "{injected:?}");
            lost += 1;
        } else if row.finding.is_some()
            && row
                .note
                .contains(trust_cg_verify::bound_memory_authority::CHECKER_IDENTITY_MISS)
        {
            // On an unqualified host a row is already uncovered by its
            // checker-identity miss; the failing hook replaces that refusal
            // with its own, and the row stays uncovered.
            assert!(injected_finding(injected), "{injected:?}");
            missed += 1;
        } else {
            assert_eq!(row.finding, injected.finding, "{}", row.opcode_display);
        }
    }
    assert_eq!(missed, checker_identity_misses(&real));
    assert_eq!(lost + missed, 46 + 18 + 6 + 2 + 6);
    assert_eq!(failing.covered_count(), real.covered_count() - lost);
}

/// UADDLP/SADDLP each encode both pairwise-widening stages under one opcode.
/// Opcode-wide coverage must therefore require the exact theorem for both input
/// arrangements instead of inheriting the historical `.16B->.8H` representative
/// for an emitted `.8H->.4S` instruction.
#[test]
fn aarch64_addlp_gate_requires_both_widening_arrangements() {
    for (opcode, prefix) in [
        (AArch64Opcode::NeonUaddlpV, "uaddlpv"),
        (AArch64Opcode::NeonSaddlpV, "saddlpv"),
    ] {
        let proofs = aarch64_width_polymorphic_proofs(opcode)
            .unwrap_or_else(|| panic!("{opcode:?} must be arrangement-complete gated"));
        assert_eq!(proofs.len(), 2, "{opcode:?} must demand both stages");
        assert!(proofs.iter().any(|p| {
            p.encoded_width_bits == 8 && p.query == format!("{prefix}.16b->.8h lanewise-intent")
        }));
        assert!(proofs.iter().any(|p| {
            p.encoded_width_bits == 16 && p.query == format!("{prefix}.8h->.4s lanewise-intent")
        }));
    }

    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::AArch64));
    for opcode in [AArch64Opcode::NeonUaddlpV, AArch64Opcode::NeonSaddlpV] {
        let display = format!("AArch64::{opcode:?}");
        let row = report
            .rows
            .iter()
            .find(|row| row.opcode_display == display)
            .unwrap_or_else(|| panic!("{display} missing from audit universe"));
        assert!(
            row.finding.is_none(),
            "{opcode:?} must be covered by both arrangement theorems: {}",
            row.note
        );
        assert!(
            row.note.to_lowercase().contains("16b->.8h")
                && row.note.to_lowercase().contains("8h->.4s"),
            "{opcode:?} audit note must name both discharged stages: {}",
            row.note
        );
    }
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
/// DEFERRED at that stage (left RED, not credited): MovRI (const==const, no
/// independent constant model in the single instruction — since CLOSED, and NOT
/// by reconstruction: `x86_encoding_proofs` decodes the REAL emitted bytes with
/// an independent SDM-derived decoder; see the MOV r,imm net below), Idiv/Div
/// (the dividend is the
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
/// value/effect rows. Its named gaps (28 today) are explicit
/// `DeferredUnfaithfulModel` debt; any generic mapping/discharge failure remains
/// a regression.
#[test]
fn x86_emittable_coverage_is_honest_under_strict() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::X86_64));
    eprintln!("{}", report.audit_log());
    // The pin below includes the corpus-based MovRI credit, the ten
    // corpus-based SSE LANE credits and the corpus-based MOVSXD-SIB credit;
    // refuse a stale corpus of any of them.
    assert_movri_corpus_is_what_the_live_encoder_emits();
    assert_sse_lane_corpus_is_what_the_live_encoder_emits();
    assert_movsxd_sib_corpus_is_what_the_live_encoder_emits();

    assert!(
        report.emittable_count() > 0,
        "x86-64 audit found zero emittable opcodes — classifier is mis-wired"
    );

    // What each x86-64 credit family establishes (the per-tier reconstruction
    // contracts). Every credited row is either a non-degenerate static-DB proof,
    // a reconstruction whose two sides are computed independently, or an
    // independent SDM-derived decode of the real emitted bytes; no X==X
    // identity is credited.
    //
    // MEMORY tier: GENUINE effective-address reconstruction of the load/store,
    // memory-ALU, and in-place inc/dec families. The deterministic
    // `SmtExpr::MemLoad` memory model treats `load(ea)` as a deterministic function
    // of the (effective-address, width, signedness) triple, so a wrong EA reads a
    // DIFFERENT value ⇒ REFUTE. The MACHINE EA is the INDEPENDENT x86 `encode_lea_*`
    // encoder; the SOURCE EA is the trust_ir Iadd/Imul composition. The
    // scaled-index MOVs (MovRMSib/MovMRSib, the 32-bit and 8-bit SIB pairs,
    // ImulRMSib, and the scalar-FP loads MovsdRMSib/MovssRMSib) reconstruct via
    // the SAME `x86_reconstruct_effective_address` `SibMemAddr` model on both
    // sides; a wrong base/index/scale/disp REFUTES, and a store's value half ties
    // the stored register to the IR store value.
    //
    // PACKED 128-bit MOVE tier: the whole-XMM memory moves MOVDQU{RM,MR}
    // (unaligned) and MOVDQA{RM,MR} (aligned), emitted for Fpr128 spill/reload,
    // are GENUINELY RECONSTRUCTED as TWO 64-bit halves at effective addresses
    // `ea` (low 64 bits) and `ea+8` (high 64 bits), little-endian, reusing the
    // PROVEN scalar effective-address machinery. A wrong base/index/scale/disp
    // (EA), a SWAPPED half, a wrong half OFFSET (`ea+16` for `ea+8`), a wrong
    // access WIDTH, or (store) a wrong/dropped value half REFUTES. MOVDQA carries
    // the HONEST `ea % 16 == 0` precondition (SSE MOVDQA #GP-faults on a
    // non-16-aligned address); MOVDQU does not — and the alignment assumption
    // NEVER weakens the value equality (see the `movdqa_*_alignment_*`
    // refutations in tests/reconstruction_x86.rs). MovdquRMSib/MovdquMRSib are
    // the same reconstruction over the SIB EA; they are deliberately
    // UNALIGNED-ONLY, because re-forming the address as base+index*scale could
    // invalidate MOVDQA's alignment precondition, so the aligned family gets no
    // SIB sibling.
    //
    // IMPLICIT-OPERAND tier: rows whose operative inputs are IMPLICIT:
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
    //     dividend ⇒ REFUTE. The evaluator's BvSDiv/BvUDiv model the 64-bit
    //     divide's 128-bit dividend exactly (no truncation).
    //   * Cmovcc / Cmovcc32: the IMPLICIT RFLAGS condition, reconstructed as a
    //     genuine CMP+CMOV PAIR — machine = ite(eval_int_condition(cc,
    //     flags_of(a,b)), src, dst); source = ite(icmp(intcc_for(cc), a, b), src,
    //     dst). Each condition code is a DISTINCT boolean formula over the genuine
    //     ZF/SF/CF/OF/PF flags (`encode_int_cmp_flags`), so a WRONG cc (E-for-NE,
    //     L-for-GE) gives the complementary boolean ⇒ REFUTE. The gate requires ALL
    //     ten value-select condition codes to discharge (not just one).
    //
    // MFENCE (SeqCst fence) is a NO-OP on single-thread data state, so its only
    // faithful value proof is structurally X==X; it is FailClosedAllowlisted
    // (coverage NOT claimed). Soundness is unchanged: the identity is registered
    // and witnessed by two refuting negative controls under proof_gate_strict,
    // and ordering is the Intel-SDM axiom.
    //
    // CMPXCHG (compare_exchange) is covered by the six width-polymorphic
    // conditional-data-flow proofs (Cmpxchg_I{32,64} returns-old +
    // conditional-store + success-flag), which `x86_width_polymorphic_proofs`
    // requires to ALL discharge — genuine obligations over symbolic (mem,
    // expected, desired) state; the negative controls REFUTE.
    //
    // Packed 64-bit multiply compose (the SSE2 vectorizer's i64 saxpy loops):
    // PSLLQ/PSRLQ are static-DB proofs parallel to the PSLLD/PSRLD dword forms
    // (group-13 0x73 encoding vs group-12 0x72; the wrong-lane-width negative
    // control REFUTES a dword-model swap). PMULUDQ's even-dword widening multiply
    // is the same-width i64x2 lane op `lo32(a)*lo32(b)`, backed by the static-DB
    // proof `V2I64 even-dword widening Umul -> PMULUDQ` whose machine side is the
    // INDEPENDENT SDM-structural even-dword-extract/zext/mul model; odd-lane,
    // sign-extending, and low-half-only wrong models all REFUTE.
    //
    // Psadbw (horizontal byte SAD) is covered by the PsadbwByteSad
    // reconstruction (encode_psadbw vs the independent
    // encode_trust_ir_byte_sad; a wrong lane-wise opcode REFUTES). RolRI is
    // covered by the existing RotL_I operand reconstruction; wrong
    // direction/count refutes.
    //
    // Memory-destination RMW ALU quartet XorMR/AddMR/XorMRSib/AddMRSib: the
    // MemRmw reconstruction composes the proven MemStore shape (address half +
    // stored-value half) with the proven MemAlu shape (the REAL machine ALU
    // encoder over a load of the same EA) on the shared
    // `x86_reconstruct_effective_address`; wrong EA / Add-for-Xor /
    // dropped-or-wrong src / plain-store-for-RMW all REFUTE (mem_rmw controls
    // in reconstruction_x86.rs). NOTHING emits these opcodes yet: proofs land
    // BEFORE the fusion peephole, whose admission gate is this very
    // reconstruction discharging Valid.
    //
    // RolRCl, the variable-count rotate: the RotlVar reconstruction pits the
    // bridge's masked shl/shr/or rotate idiom against the independent
    // hardware-masked `encode_rol_rcl_masked`, TOTAL (no count<width
    // precondition), machine half keyed off the real opcode. ROR-for-ROL /
    // dropped wrap half / unmasked count / wrong mask 31 / SHL-for-ROL all
    // REFUTE (rotl_var controls in reconstruction_x86.rs). NOTHING emits RolRCl
    // yet: the variable-rotate peephole is admission-gated on this very
    // reconstruction discharging Valid.
    //
    // MovRI (MOV r,imm): NOT a reconstruction credit and NOT a static-DB proof —
    // `const == const` is the self-equality a retracted ledger entry was. The
    // credit is `x86_encoding_proofs::mov_imm_discharges_valid` — an
    // INDEPENDENT decoder written from the Intel SDM's instruction format (it
    // models C6/C7 /0, AH..BH and the sign-extending REX.W C7 /0 id, none of
    // which the encoder emits) run over the REAL emitted bytes, compared as a
    // write to the 64-bit root register against the machine-IR intent
    // (register NAME, i64 immediate), with canonicality and exact framing
    // pinned. The hook refuses unless all 11 emitted physical form classes are
    // present and EVERY negative control refutes FOR ITS STATED REASON CLASS:
    // wrong register, flipped REX.B, sign-for-zero extension in both directions
    // (on VALUE), truncated imm64, wrong-width form, wrong opcode, every
    // single-byte immediate corruption, dropped forced REX, redundant prefixes,
    // bad framing, and every source-side re-claim. tests/x86_encoding_gate.rs
    // re-derives the captured corpus from the LIVE encoder. It says NOTHING
    // about whether the lowering chose the right constant.
    //
    // Narrow LOCK CMPXCHG (Cmpxchg8/Cmpxchg16): NOT the i32/i64
    // `Cmpxchg_I{32,64}` theorems — operand 0 is a Gpr32 carrier for BOTH i8
    // and i16, so inheriting those would bind a BYTE CAS to a DOUBLEWORD proof
    // (the degenerate-green trap; see
    // `narrow_cmpxchg_never_binds_the_wide_cmpxchg_proofs`). The credit is the
    // `X86SourceOp::CmpxchgNarrow` reconstruction: SOURCE =
    // `encode_trust_ir_cmpxchg`, a transcription of the pinned trust-ir
    // interpreter's `Inst::CmpXchg` arm over three w-bit VALUE leaves; MACHINE =
    // `encode_lock_cmpxchg_narrow`, an SDM transcription over the FULL 64-bit
    // RAX, the FULL 32-bit source carrier and a byte-addressable memory array at
    // the INDEPENDENTLY encoded effective address. ONE `64 + 2w + 1`-bit joint
    // obligation carries five facets: RAX[63:w] PRESERVED (the partial AL/AX
    // write), returns-old, the conditional store, the ADJACENT cell untouched
    // (which pins the store WIDTH), and ZF == success. Both opcodes must
    // discharge at disp=0 AND disp=-24. Controls (tests/reconstruction_x86.rs
    // `cmpxchg_narrow`): a zero-extending or 32-bit-write RAX merge, either
    // wrong machine width, the Gpr32 class trap, an unconditional store, a
    // suppressed store, a returns-desired variant, a missing failure load, a
    // backwards / wide-compare / wrong-bit flag, swapped roles, the wrong source
    // byte, a byte-swapped store, a wrong EA, a neighbour clobber, a
    // clean-carrier SOURCE claim, and a corruption confined to concat bits above
    // 64 ALL REFUTE. It says NOTHING about atomicity/LOCK ordering, nothing
    // about the emitted BYTES (`decode_check.rs` still allowlists these two
    // under NARROW_CMPXCHG, so REX / `0F B0` / the `66` prefix stay uncovered),
    // nothing about the identity of the accumulator with the surrounding MOVs,
    // and nothing tying w to the LIR type.
    //
    // The SSE lane family (Pshufd, Pmovmskb, MovdqaRR, Punpckldq, Punpcklqdq,
    // Punpcklbw, Punpckhbw, Ptest, Pblendvb, Packuswb): NOT a reconstruction
    // credit — every reconstruction the gate has is a per-lane same-width scalar
    // model, and a permutation, a reduction to RFLAGS, a reduction to a GPR, an
    // interleave, a saturating narrow and a whole-register copy are none of
    // those. And explicitly NOT the `PackLowQwords` reconstruction, which is
    // still the character-for-character `X == X` it always was and still
    // credits nothing. The credit is
    // `x86_sse_lane_proofs::sse_lane_discharges_valid`: an INDEPENDENT decoder
    // written from the Intel SDM's `0F` / `0F 38` packed-integer maps (it models
    // a dozen instructions the encoder never emits — PUNPCKLWD, PUNPCKHWD,
    // PUNPCKHDQ, PUNPCKHQDQ, PACKSSWB, PACKSSDW, MOVDQU, MOVQ, PSHUFHW,
    // PSHUFLW, BLENDVPS, BLENDVPD, the MOVDQA STORE direction and the MMX
    // forms, so it cannot have been obtained by inverting `encode.rs`), run over
    // the REAL emitted bytes, yielding an EXACT bit-level ROUTING denotation
    // compared against a PARAMETRIC statement of the machine-IR intent. Equality
    // of two such denotations decides the question for EVERY input — it is not a
    // sampled equivalence. Two facets cannot be a routing and get their own
    // obligations: PACKUSWB's unsigned-saturating narrow is settled EXHAUSTIVELY
    // over all 65536 inputs (the SDM's arithmetic formulation against the
    // machine IR's bit-pattern one), and PTEST's six status flags are settled by
    // EVALUATION over a structured witness family that reaches ZF=1 (a random
    // 128-bit sweep never does, so a `ZF = 0` model would otherwise survive).
    // The hook refuses unless all ten rows have captured encodings and EVERY
    // control refutes FOR ITS STATED REASON CLASS: the WRONG HALF (PUNPCKHBW
    // for PUNPCKLBW) and the WRONG ELEMENT WIDTH (PUNPCKLWD / PUNPCKLDQ), plus
    // swapped operands, identity passthrough, constant zero, the `_MM_SHUFFLE`
    // ORDER-field reversal, PSHUFHW/PSHUFLW half-permutes, PMOVMSKB from bit 0 /
    // reversed / sign-extended / 8-lane, PBLENDVB with the mask from the
    // explicit source instead of XMM0 / on bit 0 / with swapped arms /
    // dword- and qword-granular, PACKUSWB signed / halves-swapped /
    // order-reversed, and the byte mutants (neighbour opcode bytes, prefix
    // 66 to F3, the dropped 66, exchanged ModRM fields, mod cleared to 00, a
    // redundant REX, a REX before the 66, a trailing byte, a truncated tail and
    // corrupted ORDER fields). tests/x86_sse_lane_gate.rs re-derives the corpus
    // from the LIVE encoder, sweeps all 256 register pairs per row and all 256
    // PSHUFD immediates, and runs the SDM denotation against NATIVE SILICON. It
    // says NOTHING about whether instruction selection chose the right
    // instruction, permutation, mask or operands.
    //
    // MovsxdRMSib (the scaled SIGN-EXTENDING load) is in the denominator
    // COVERED even though nothing emits it: emitted value/effect debt does not
    // belong in the excluded bucket, the same posture the unemitted
    // XorMR/AddMR RMW quartet and RolRCl hold. The SibMemAddr reconstruction
    // cannot credit it: it builds BOTH sides of the address from the SAME
    // operand with the SAME `recon_base`/`recon_index` symbols, so it cannot
    // refute a wrong base, a wrong index or a base/index swap, and it has no
    // sign-extending load model at all. `x86_movsxd_sib_proofs` supplies the
    // missing shape: an INDEPENDENT SDM-derived decode of the REAL emitted
    // bytes (it models the no-base SIB form, the no-index sentinel, the
    // register-direct and RIP-relative forms, the non-SIB `[base+disp]` form,
    // `63 /r` without REX.W and `8B /r` — none of which the MovsxdRMSib encoder
    // arm emits, so it cannot have been obtained by inverting it), denoted as a
    // write to the 64-bit destination ROOT over per-register leaves NAMED FROM
    // THE DECODED REGISTER NUMBERS, against a parametric statement of the
    // machine-IR intent. The two sides are structurally distinct by
    // construction — a SHIFT by the raw SIB scale field against a MULTIPLY by
    // the entry size, and an explicit sign-extend of a zero-filling load against
    // a signed load — and the comparison REFUSES a machine side identical to the
    // source side, so the credit cannot decay into the X==X that the retracted
    // memory "proofs" were. The ADDRESS facet is EXACT for every 64-bit base and
    // index (`base + index*s == base + (index << ss)` iff `s == 1 << ss`, by
    // taking index = 1 for necessity); the VALUE facet is decided over a witness
    // family that is REQUIRED to exercise both sign cases of the loaded
    // doubleword. Every byte control (wrong destination, flipped REX.R/X/B,
    // cleared REX.W, the MOV opcode, a rotated SIB scale, a rewritten SIB
    // index/base, a dropped SIB byte, a register-direct ModR/M, a corrupted or
    // dropped displacement, framing, a doubled REX and every redundant legacy
    // prefix), every source re-claim, every WRONG-MODEL control run through the
    // comparison itself (a zero-extending model, the raw `ss` as a factor, the
    // base shifted instead of the index, a 64-bit access, a dropped
    // displacement, a dropped index, and a machine side spelled exactly like the
    // source side which must be refused as DEGENERATE) and every hand-written
    // SDM decoder control must REFUTE for its stated class, with an unbuildable
    // control counted as a battery defect rather than a refutation.
    // tests/x86_movsxd_sib_gate.rs re-derives the corpus from the LIVE encoder,
    // sweeps the whole destination x base x index x scale x displacement
    // product, runs the full `verify_by_evaluation` sampling sweep and an
    // EXHAUSTIVE sweep over a contiguous 2^16 address window. It claims NO
    // runtime win and NO per-compile check: NOTHING EMITS THIS OPCODE, and
    // `decode_check.rs` still allowlists it under JUMP_TABLE.
    //
    // `AtomicLoadCmpxchg16b`, the pseudo the selector emits for an I128
    // `AtomicLoad` (four zeroing XORs + LOCK CMPXCHG16B), is COVERED JOINTLY:
    // the byte-level address lane for its address, and the
    // `X86SourceOp::AtomicLoadCmpxchg16b` reconstruction for its value (the
    // whole expansion over arbitrary incoming registers vs the trust-ir
    // AtomicLoad, plus the bare CMPXCHG16B vs the trust-ir CmpXchg; eleven facet
    // equalities, per-facet non-degeneracy enforced by the reconstructor).
    //
    // 201 -> 206: the ZERO-EXTENDING loads `movzx r32, m8/m16` (`MovzxRM8`,
    // `MovzxRM16`, `MovzxRM8Sib`, `VolatileMovzxRM8`, `VolatileMovzxRM16`), the
    // selector's load for every byte and word, arrive COVERED: the byte-level
    // address lane decodes their `[REX] 0F B6/B7 /r` bytes for the address AND
    // the destination-write facet (the SDM register write of the decoded
    // production against the zero-extended access value, with the merging-MOV,
    // sign-extending and other-width models refuting through the same
    // comparison), the MemLoad reconstruction carries the value leg, and the
    // two volatile twins also need the VOL-x86 trace leg.
    assert_eq!(
        report.emittable_count(),
        206,
        "x86-64 emitted value/effect denominator changed; update the pin deliberately"
    );
    assert_eq!(
        report.covered_count(),
        206,
        "x86-64 GENUINE (non-degenerate / reconstructed-Valid) emittable coverage changed; \
         update the pinned numbers deliberately — do NOT re-admit X==X identities to inflate this, \
         do NOT credit a memory op without a faithful independent effective-address encoder, and \
         do NOT credit a division/cmov without the genuine double-width / per-cc flag model:\n{}",
        report.audit_log()
    );
    assert!(
        (report.coverage_percent() - (206.0 / 206.0 * 100.0)).abs() < f64::EPSILON,
        "x86-64 accepted-obligation ratio drifted from the honest 206/206"
    );

    // THE EXPECTED RED SET IS NOW EMPTY. It held exactly the sixteen volatile
    // memory forms, and they were credited on a JOINT address + value +
    // observation-boundary obligation. An empty set is the strongest form of
    // this assertion, not the weakest: any opcode that loses its obligation
    // appears here as an unexpected failure, and the sweep below still runs.
    let expected_red: std::collections::HashSet<String> = std::collections::HashSet::new();
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
/// from the array therefore fails.
#[test]
fn aarch64_universe_has_no_duplicates() {
    assert_inventory_matches_enum_source(
        "AArch64",
        "AArch64Opcode",
        include_str!("../../trust-cg-ir/src/inst.rs"),
        ALL_AARCH64_OPCODES,
    );
}

/// LOCKS IN universe completeness for x86-64, same rationale as the AArch64
/// counterpart. Source of truth: crates/trust-cg-ir/src/x86_64_ops.rs.
#[test]
fn x86_universe_has_no_duplicates() {
    assert_inventory_matches_enum_source(
        "x86-64",
        "X86Opcode",
        include_str!("../../trust-cg-ir/src/x86_64_ops.rs"),
        ALL_X86_OPCODES,
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
fn riscv_universe_has_no_duplicates() {
    assert_inventory_matches_enum_source(
        "RISC-V",
        "RiscVOpcode",
        include_str!("../../trust-cg-ir/src/riscv_ops.rs"),
        ALL_RISCV_OPCODES,
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
/// TRUE HONEST HEADLINE: 128 / 128 of the value-equivalence denominator. Of
/// the 19 value-bearing ops the full wasm32 lowering added, 13 are
/// reconstructed from their real bytes — clz/ctz (a clz byte for a ctz
/// refutes), rotl/rotr (the other direction refutes), eqz (a nonzero test
/// refutes), select (swapped values or an inverted condition refute) and
/// copysign (over the operands' bit patterns; swapped operands, fabs or fneg
/// refute; its captured emitted body fixes the operand order). f.min/f.max
/// exist only inside the FMin/FMax sequence, so the 4 rows are credited by that
/// captured emitted BODY, executed under the spec semantics for every
/// permitted NaN result against the relational trust-ir contract (opposite-op,
/// unguarded, inverted-guard and NaN-selecting controls refute; the -0/+0 tie
/// is credited under trust-ir's unpinned reading). A trust-ir MemCopy/MemSet
/// lowers to the guarded sequence (`if (n != 0)` around the op), so the
/// memory.copy/fill rows are credited by the captured guarded BODIES, executed on a
/// two-page memory under the spec semantics against the relational trust-ir
/// contract (a zero count is a no-op whatever the pointers; the unguarded body
/// refutes at a zero-byte out-of-memory range, and inverted-guard,
/// guard-on-destination, swapped-operand, forward-byte-copy and operand
/// truncation controls refute at their stated class; the battery observes every
/// operand bit below the model width, and the operand-provenance check — the
/// op's operands are the function's parameters — carries the bits above it).
/// memory.fill is emitted only there; memory.copy is
/// ALSO emitted, with a constant nonzero size, by the aggregate / lane / sret
/// moves (`emit_copy`), which the credit does not cover — the MemoryCopy note
/// must say so, and the live backend is required to emit every bulk op in one
/// of those two forms. The two INTEGER constant forms are credited by P4's
/// independent signed-LEB decode, the two FLOAT constant forms (f32.const 0x43
/// / f64.const 0x44) by an independent decode of the raw IEEE-754 payload
/// compared bit-exactly with the carrier's pattern, through a stated
/// roundTiesToEven narrowing for f32. NOTHING in the lowerer selects a v128
/// value, so the four lane-wise v128 value ops (i32x4.add/mul, f32x4.add/mul)
/// and the three v128 load/store/const forms are excluded as never selected —
/// checked, not assumed: a live corpus is scanned and must contain no
/// 0xfd-prefixed instruction (a patched module that does is reported); the
/// lane-wise reconstruction stays built and refutable in
/// `reconstruction_wasm`.
#[test]
fn wasm_inventory_pins_accepted_and_deferred_rows() {
    // The float credits stand on captured corpora; re-derive them from the
    // live backend so this pin cannot stay green over frozen bytes.
    wasm_float_live::assert_float_const_corpus_is_what_the_live_backend_emits();
    wasm_float_live::assert_float_binop_bodies_are_what_the_live_backend_emits();
    wasm_bulk_live::assert_bulk_memory_bodies_are_what_the_live_backend_emits();
    // The scope the bulk-memory notes state: every emitted bulk op is either
    // the guarded trust-ir lowering or a constant-nonzero-size aggregate copy.
    assert!(wasm_bulk_live::assert_bulk_memory_emission_is_guarded_or_constant_sized() > 0);
    wasm_bulk_live::assert_the_site_classifier_refuses_unguarded_and_zero_sized_ops();
    // The never-selected exclusion is a fact about emission: no module of the
    // live corpus contains an excluded opcode, and the scan reports one that
    // does.
    assert!(wasm_never_selected_live::assert_no_never_selected_opcode_is_emitted() > 0);
    wasm_never_selected_live::assert_the_scan_reports_an_emitted_excluded_opcode();
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::Wasm));
    // Always print the full audit so the allowlist stays visible in CI logs.
    eprintln!("{}", report.audit_log());

    // The denominator is the 128 value-bearing ops the lowerer can emit: 83
    // reconstructable scalar + 2 popcnt + 4 reinterpret + 8 int->FP convert + 8
    // saturating trunc + 4 emitted scalar constants (2 integer + 2 float) + 19
    // ops the full wasm32 lowering added (4 clz/ctz, 4 rotl/rotr, 2 eqz,
    // select and 2 copysign, reconstructed; 4 f.min/f.max, credited by the
    // emitted FMin/FMax body; memory.copy and memory.fill, credited by the
    // emitted guarded MemCopy/MemSet body). The 4 lane-wise v128 value ops and
    // the 3 v128 load/store/const forms are never selected.
    assert_eq!(
        report.emittable_count(),
        128,
        "wasm emittable (value-equivalence denominator) count changed — it must include ALL \
         FOUR scalar constants (i32/i64/f32/f64) and memory.copy/fill but NOT the 7 \
         never-selected v128 forms; update deliberately. Re-check classify_wasm and \
         wasm_function_verifier::opcode_to_source_op."
    );
    // COVERED = 83 scalar + 2 popcnt + 4 reinterpret + 16 conversion + 4
    // clz/ctz + 4 rotl/rotr + 2 eqz + select + 2 copysign = 118 via
    // stack-machine reconstruction (copysign also needs its emitted body), PLUS
    // 4 constants credited by a different path — reconstruction cannot help a
    // constant (const == const is a self-equality) — an INDEPENDENT
    // spec-derived decode of the real emitted immediate (signed-LEB at
    // canonical length for the integers, the raw IEEE-754 payload bit-exact
    // for the floats), PLUS the 4 f.min/f.max rows credited by the emitted
    // FMin/FMax body, PLUS memory.copy/fill credited by the emitted guarded
    // MemCopy/MemSet body. 128 total.
    assert_eq!(
        report.covered_count(),
        128,
        "wasm GENUINE covered count changed — must be 128 (83 scalar + 2 popcnt + 4 reinterpret + \
         16 conversions + 4 clz/ctz + 4 rotl/rotr + 2 eqz + select + 2 copysign via \
         reconstruction, + 4 scalar constants via the independent LEB / float-payload decoders, \
         + 4 f.min/f.max via the emitted FMin/FMax body, + memory.copy/fill via the emitted \
         guarded MemCopy/MemSet body). Do NOT inflate by crediting a never-selected v128 form.\n{}",
        report.audit_log()
    );
    assert!(
        (report.coverage_percent() - 100.0).abs() < 0.01,
        "wasm coverage_percent must be the honest 128/128"
    );

    // No RED row. This is a statement about THIS gate only — the
    // per-instruction value-equivalence inventory of the opcodes the lowerer
    // emits — and it is emphatically NOT a claim that the wasm lane is
    // verified. The value-domain gate still carries its 4 named deferrals, the
    // CFG family's bisimulation is deferred, and the ABI family's host-memory
    // obligations are the host's. A new op that cannot be faithfully modelled
    // belongs HERE as a DeferredUnfaithfulModel RED row, never allowlisted out.
    let failures = report.failures();
    assert!(
        failures.is_empty(),
        "the wasm denominator has no named deferral left:\n{}",
        report.failure_summary()
    );
    // The newly credited rows say what they rest on.
    for (display, needle) in [
        ("wasm::F32Const", "IEEE-754 payload"),
        ("wasm::F64Const", "IEEE-754 payload"),
        ("wasm::F32Min", "FMin/FMax body"),
        ("wasm::F64Max", "FMin/FMax body"),
        ("wasm::MemoryCopy", "guarded MemCopy/MemSet body"),
        ("wasm::MemoryCopy", "does NOT cover those instances"),
        ("wasm::MemoryCopy", "emit_copy"),
        ("wasm::MemoryFill", "guarded MemCopy/MemSet body"),
        (
            "wasm::MemoryFill",
            "emitted only by the guarded MemSet lowering",
        ),
        ("wasm::F32Copysign", "captured emitted body"),
    ] {
        let row = report
            .rows
            .iter()
            .find(|r| r.opcode_display == display)
            .unwrap_or_else(|| panic!("{display} row"));
        assert!(
            row.finding.is_none() && row.note.contains(needle),
            "{display}: {:?} / {}",
            row.finding,
            row.note
        );
    }
}

/// LOCKS IN universe completeness for WebAssembly, same rationale as the
/// AArch64 / x86-64 / RISC-V counterparts. Source of truth:
/// crates/trust-cg-ir/src/wasm_ops.rs (the `WasmOpcode::tests::opcode_count` pin).
#[test]
fn wasm_universe_has_no_duplicates() {
    assert_inventory_matches_enum_source(
        "WebAssembly",
        "WasmOpcode",
        include_str!("../../trust-cg-ir/src/wasm_ops.rs"),
        ALL_WASM_OPCODES,
    );
}

/// LOCKS IN the DENOMINATOR-HONEST wasm partition.
///
/// The value-equivalence denominator (classify_wasm EmittableNeedsProof) is now
/// exactly 128 opcodes: the 83 reconstructable scalar value ops + the value-
/// bearing ops that were wrongly allowlisted-out by the #71 bring-up (popcnt ×2,
/// reinterpret ×4, int->FP convert ×8, saturating trunc ×8), the four emitted
/// scalar constants (all credited by independent immediate decoders), and the
/// 19 ops the full wasm32 lowering added (clz/ctz, rotl/rotr, eqz, select and
/// copysign reconstructed; f.min/f.max credited by the emitted FMin/FMax body;
/// memory.copy/fill by the emitted guarded MemCopy/MemSet body). Only the
/// GENUINELY STRUCTURAL ops (locals/globals, word-sized memory, control flow,
/// calls) and the never-selected v128 forms (the 4 lane-wise value ops and
/// load/store/const) are fail-closed-allowlisted with TRUE reasons;
/// nop/unreachable are pseudo. This pins the partition so a value-bearing
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
        emittable, 128,
        "the value-equivalence denominator is 105 reconstructed rows, the FOUR emitted scalar \
         constants (i32/i64/f32/f64) and the 19 ops the full wasm32 lowering added (13 of them \
         reconstructed, 4 credited by the FMin/FMax body, 2 by the guarded MemCopy/MemSet \
         body); the 7 v128 forms (4 lane-wise value ops, load/store/const) are never selected"
    );
    assert_eq!(
        pseudo, 2,
        "nop + unreachable are the only pseudo/trap wasm opcodes"
    );
    assert_eq!(
        allowlisted,
        ALL_WASM_OPCODES.len() - 128 - 2,
        "only GENUINELY-structural opcodes are fail-closed-allowlisted (no emitted value-bearing \
         op may be allowlisted-out of the denominator); only the never-selected v128 forms stay \
         excluded"
    );
}

/// LOCKS IN the v128 partition: the lowerer never selects a v128 value.
///   * the 4 LANE-WISE value ops (i32x4.add/mul, f32x4.add/mul) are excluded
///     from the value-equivalence denominator as NEVER SELECTED (no v128
///     carrier, simd128 refused) — a credit for an opcode no emitted module
///     contains would cover no emitted code — while their lane-wise
///     reconstruction stays built and still discharges Valid, so they re-enter
///     the denominator unchanged the moment selection lands;
///   * the 3 reserved forms (v128.load/store/const) are never selected and are
///     allowlisted-OUT for the same reason. Scalar constants are emitted and
///     therefore do not share this classification.
///     A regression that credits a never-selected form, or loses the lane-wise
///     reconstruction, breaks this pin.
#[test]
fn wasm_v128_lanewise_reconstructed_structural_allowlisted() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::Wasm));

    // (a) The 4 lane-wise value ops are excluded as never selected, and their
    //     reconstruction still discharges.
    for op in [
        WasmOpcode::I32x4Add,
        WasmOpcode::I32x4Mul,
        WasmOpcode::F32x4Add,
        WasmOpcode::F32x4Mul,
    ] {
        match classify_wasm(op) {
            OpcodeClass::FailClosedAllowlisted { reason } => assert!(
                reason.contains("never selected") && reason.contains("simd128"),
                "wasm::{op:?} must disclose why it is never selected: {reason}"
            ),
            other => panic!("wasm::{op:?} must be never-selected, got {other:?}"),
        }
        let row = report
            .rows
            .iter()
            .find(|r| r.opcode_display == format!("wasm::{op:?}"))
            .unwrap_or_else(|| panic!("wasm::{op:?} must appear in the audit"));
        assert!(
            row.finding.is_none() && matches!(row.class, OpcodeClass::FailClosedAllowlisted { .. }),
            "wasm::{op:?} must be an excluded row, got {:?} / {:?}",
            row.class,
            row.finding
        );
        assert!(
            trust_cg_verify::wasm_function_verifier::reconstruction_discharges_valid(
                op,
                &trust_cg_verify::lowering_proof::VerificationConfig::default()
            ),
            "wasm::{op:?}: the lane-wise reconstruction must stay discharging"
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
            row.finding.is_none(),
            "wasm::{op:?} must be CREDITED by P4's independent signed-LEB immediate decode \
             (wasm_encoding_proofs) — it stays IN the denominator, and if that decoder ever \
             stops discharging it must return as an explicit DeferredUnfaithfulModel RED row \
             rather than being allowlisted out"
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
/// two sides are structurally distinct, plus the 32 P3 narrow-width obligations
/// (`wasm_value_domain::narrow_width_proofs` — an `i32`-carried
/// `u8`/`i8`/`u16`/`i16` respects its width invariant across the backend's
/// wrapping arithmetic). No X==X self-equality may sneak back in.
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
        86,
        "the 54 genuine wasm refinement witnesses + the 32 P3 narrow-width obligations are \
         registered"
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
        // The typed post-allocation copies are emitted by `lower_copies`.
        AArch64Opcode::MOVWrr,
        AArch64Opcode::MOVXrr,
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

    // Typed STR aliases are never selected, and RET is a structural control
    // edge. (The typed MOV aliases are emitted post-RA copies; see above.)
    for op in [
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

    // x86: MovRI is emitted value materialization and therefore stays IN the
    // denominator. Jmp/Call/Ret are structural control edges. (Lea /
    // LeaSib are NO LONGER in this list — they
    // are now CREDITED via operand reconstruction: the machine side is rebuilt
    // from the real effective-address encoder over fresh symbolic base/index, and
    // a wrong scale/disp refutes. MovRI is const==const in the single
    // instruction, so reconstruction can never help it; it is CREDITED instead
    // by x86_encoding_proofs' independent SDM-derived decode of the real emitted
    // bytes.)
    assert!(
        matches!(
            classify_x86(X86Opcode::MovRI),
            OpcodeClass::EmittableNeedsProof
        ),
        "x86_64::MovRI is emitted value materialization and must stay in the denominator"
    );
    {
        let report = on_large_stack(|| CoverageGate::new().audit(GateArch::X86_64));
        let row = report
            .rows
            .iter()
            .find(|row| row.opcode_display == "x86_64::MovRI")
            .expect("x86_64::MovRI missing from audit");
        assert!(
            row.finding.is_none(),
            "x86_64::MovRI must be CREDITED by the independent SDM-derived MOV-immediate decode \
             (x86_encoding_proofs) — it stays IN the denominator, and if that hook ever stops \
             discharging it must return as an explicit ProofNotDischarged RED row rather than \
             being allowlisted out: {:?}",
            row.finding
        );
        assert!(
            row.note.contains("DECODED")
                && row.note.contains("x86_encoding_proofs")
                && row.note.contains("mutants REFUTE")
                && row.note.contains("Says nothing about whether the LOWERING"),
            "x86_64::MovRI credit note must name its evidence and its non-claim: {}",
            row.note
        );
        assert!(
            !row.note.contains("[reconstruction]") && !row.note.contains("DEGENERATE"),
            "x86_64::MovRI is NOT a reconstruction credit: {}",
            row.note
        );
        assert!(
            trust_cg_verify::coverage_gate::x86_deferred_value_op_reason(X86Opcode::MovRI)
                .is_none(),
            "a credited row must not also sit in the deferred table"
        );
    }
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

/// A FAILING MovRI HOOK IS RED IN THE WHOLE REPORT, NOT JUST IN ITS ROW.
///
/// The credit hook `x86_encoding_proofs::mov_imm_discharges_valid` reads a fixed
/// corpus, so no ordinary test can make it return `Err`. Before this test
/// existed, the gate's hook-failure arm never ran with a real `Err`. Rewriting that
/// arm to report no finding left every test green, and with a broken obligation
/// stacked on top the ratio pins still read the credited count. The gate is now
/// handed an `Err` directly. The row must become `ProofNotDischarged` carrying
/// the hook's reason, MovRI must be the ONE extra failure, and the covered count
/// must drop by exactly one. With the real hook result, the injected audit must
/// equal the ordinary one row for row.
#[test]
fn movri_hook_failure_is_red_in_the_whole_report() {
    let (real, injected_ok, injected_err, real_credit) = on_large_stack(|| {
        let gate = CoverageGate::new();
        let real = gate.audit(GateArch::X86_64);
        let real_credit = trust_cg_verify::x86_encoding_proofs::mov_imm_discharges_valid();
        let injected_ok = gate.audit_x86_with_movri_credit(&real_credit);
        let injected_err = gate
            .audit_x86_with_movri_credit(&Err("INJECTED: a negative control survived".to_string()));
        (real, injected_ok, injected_err, real_credit)
    });
    assert!(real_credit.is_ok(), "{real_credit:?}");
    assert_eq!(
        real.rows, injected_ok.rows,
        "the injection seam must not change the audit when handed the real hook result"
    );

    let row = injected_err
        .rows
        .iter()
        .find(|row| row.opcode_display == "x86_64::MovRI")
        .expect("x86_64::MovRI missing from the injected audit");
    match &row.finding {
        Some(CoverageFinding::ProofNotDischarged { proof_name, detail }) => {
            assert!(proof_name.contains("MOV r,imm"), "{proof_name}");
            assert!(detail.contains("INJECTED"), "{detail}");
        }
        other => panic!(
            "a failing MovRI hook must surface as ProofNotDischarged (a regression, not a \
             deferral and not a credit), got {other:?}"
        ),
    }
    assert_eq!(row.class, OpcodeClass::EmittableNeedsProof);
    assert_eq!(
        injected_err.emittable_count(),
        real.emittable_count(),
        "a failing hook must not move MovRI out of the denominator"
    );
    assert_eq!(
        injected_err.covered_count() + 1,
        real.covered_count(),
        "a failing MovRI hook must cost exactly one covered row"
    );
    let real_red: std::collections::BTreeSet<_> = real
        .failures()
        .iter()
        .map(|r| r.opcode_display.clone())
        .collect();
    let injected_red: std::collections::BTreeSet<_> = injected_err
        .failures()
        .iter()
        .map(|r| r.opcode_display.clone())
        .collect();
    let extra: Vec<_> = injected_red.difference(&real_red).cloned().collect();
    assert_eq!(extra, vec!["x86_64::MovRI".to_string()]);
    assert!(real_red.is_subset(&injected_red));

    // The row builder on its own, both arms.
    let ok_row = trust_cg_verify::coverage_gate::x86_movri_audit_row(
        "x86_64::MovRI".to_string(),
        real_credit.clone(),
    );
    assert!(ok_row.finding.is_none());
    let err_row = trust_cg_verify::coverage_gate::x86_movri_audit_row(
        "x86_64::MovRI".to_string(),
        Err("why".to_string()),
    );
    assert!(err_row.is_failure());
}

/// A FAILING MOVSXD-SIB HOOK IS RED IN THE WHOLE REPORT, NOT JUST IN ITS ROW.
///
/// The sibling of `movri_hook_failure_is_red_in_the_whole_report`, for the same
/// reason: `x86_movsxd_sib_proofs::movsxd_sib_discharges_valid` reads a fixed
/// corpus, so no ordinary test can make it return `Err`, and without this seam
/// the gate's hook-failure arm would never run with a real `Err`. Rewriting that
/// arm to report no finding would leave every test green while the ratio pins
/// still read the credited count.
///
/// The row must become `ProofNotDischarged` carrying the hook's reason — NOT a
/// `DeferredUnfaithfulModel`, because the tests that require every x86 RED row
/// to be named deferral debt must then fail loudly — `MovsxdRMSib` must be the
/// ONE extra failure, the denominator must not move, and the covered count must
/// drop by exactly one.
#[test]
fn movsxd_sib_hook_failure_is_red_in_the_whole_report() {
    let (real, injected_ok, injected_err, real_credit) = on_large_stack(|| {
        let gate = CoverageGate::new();
        let real = gate.audit(GateArch::X86_64);
        let real_credit = trust_cg_verify::x86_movsxd_sib_proofs::movsxd_sib_discharges_valid();
        let injected_ok = gate.audit_x86_with_movsxd_sib_credit(&real_credit);
        let injected_err = gate.audit_x86_with_movsxd_sib_credit(&Err(
            "INJECTED: a wrong-model control survived".to_string(),
        ));
        (real, injected_ok, injected_err, real_credit)
    });
    assert!(real_credit.is_ok(), "{real_credit:?}");
    assert_eq!(
        real.rows, injected_ok.rows,
        "the injection seam must not change the audit when handed the real hook result"
    );

    let row = injected_err
        .rows
        .iter()
        .find(|row| row.opcode_display == "x86_64::MovsxdRMSib")
        .expect("x86_64::MovsxdRMSib missing from the injected audit");
    match &row.finding {
        Some(CoverageFinding::ProofNotDischarged { proof_name, detail }) => {
            assert!(proof_name.contains("x86_movsxd_sib"), "{proof_name}");
            assert!(detail.contains("INJECTED"), "{detail}");
        }
        other => panic!(
            "a failing MOVSXD-SIB hook must surface as ProofNotDischarged (a regression, not a \
             deferral and not a credit), got {other:?}"
        ),
    }
    assert_eq!(row.class, OpcodeClass::EmittableNeedsProof);
    assert_eq!(
        injected_err.emittable_count(),
        real.emittable_count(),
        "a failing hook must not move MovsxdRMSib out of the denominator"
    );
    assert_eq!(
        injected_err.covered_count() + 1,
        real.covered_count(),
        "a failing MOVSXD-SIB hook must cost exactly one covered row"
    );
    let real_red: std::collections::BTreeSet<_> = real
        .failures()
        .iter()
        .map(|r| r.opcode_display.clone())
        .collect();
    let injected_red: std::collections::BTreeSet<_> = injected_err
        .failures()
        .iter()
        .map(|r| r.opcode_display.clone())
        .collect();
    let extra: Vec<_> = injected_red.difference(&real_red).cloned().collect();
    assert_eq!(extra, vec!["x86_64::MovsxdRMSib".to_string()]);
    assert!(real_red.is_subset(&injected_red));

    // The row builder on its own, both arms.
    let ok_row = trust_cg_verify::coverage_gate::x86_movsxd_sib_audit_row(
        "x86_64::MovsxdRMSib".to_string(),
        real_credit.clone(),
    );
    assert!(ok_row.finding.is_none());
    assert!(
        ok_row.note.contains("NOTHING EMITS THIS OPCODE"),
        "the credited row must say plainly that nothing emits it: {}",
        ok_row.note
    );
    let err_row = trust_cg_verify::coverage_gate::x86_movsxd_sib_audit_row(
        "x86_64::MovsxdRMSib".to_string(),
        Err("why".to_string()),
    );
    assert!(err_row.is_failure());
}

/// `MovsxdRMSib` must be IN the denominator and CREDITED — never allowlisted out
/// again, and never silently credited by the SibMemAddr reconstruction.
///
/// The old allowlist reason claimed the scaled effective address was already the
/// `x86_reconstruct_effective_address` family's. It is not evidence: that
/// reconstruction builds BOTH sides of a `SibMemAddr` from the SAME operand with
/// the SAME `recon_base` / `recon_index` symbols, so a wrong base, a wrong index
/// or a base/index swap cannot refute, and it has no sign-extending load model.
/// This pins that the row is credited by the byte-level obligation instead.
#[test]
fn movsxd_sib_is_in_the_denominator_and_byte_credited() {
    assert!(
        matches!(
            classify_x86(X86Opcode::MovsxdRMSib),
            OpcodeClass::EmittableNeedsProof
        ),
        "MovsxdRMSib is emitted value/effect debt; it must never be allowlisted OUT of the \
         denominator again"
    );
    assert!(
        x86_deferred_value_op_reason(X86Opcode::MovsxdRMSib).is_none(),
        "MovsxdRMSib is credited, not deferred model debt"
    );
    let row = on_large_stack(|| {
        CoverageGate::new()
            .audit(GateArch::X86_64)
            .rows
            .into_iter()
            .find(|r| r.opcode_display == "x86_64::MovsxdRMSib")
            .expect("x86_64::MovsxdRMSib row")
    });
    assert!(row.finding.is_none(), "{row:?}");
    assert!(
        row.note.contains("x86_movsxd_sib_proofs"),
        "the row must name the byte-level obligation, not a reconstruction: {}",
        row.note
    );
    assert!(
        !row.note.contains("RECONSTRUCTED from real"),
        "MovsxdRMSib must NOT be credited by the SibMemAddr reconstruction: {}",
        row.note
    );
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

/// LOCKS IN that the ten actively emitted SSE LANE opcodes stay IN the
/// denominator and are credited by the SSE lane family — never allowlisted out,
/// never quietly reclassified.
///
/// They were RED for a stated reason: none of them is a per-lane same-width
/// scalar op, and a per-lane reconstruction was the only shape the gate had.
/// PSHUFD is an imm8 permutation, PBLENDVB has a hidden third operand, PTEST
/// reduces to RFLAGS, PMOVMSKB reduces to a GPR, PUNPCK*/PACKUSWB cross the lane
/// boundary, and MOVDQA{RR} is a whole-register copy. `x86_sse_lane_proofs`
/// supplies the shape that does fit: an INDEPENDENT SDM-derived decode of the
/// real emitted bytes yielding an EXACT bit-level ROUTING denotation, compared
/// against a PARAMETRIC statement of the machine-IR intent.
///
/// THIS TEST IS THE ANTI-LAUNDERING PIN. The forbidden move is promoting a row
/// by deleting a table entry or by reclassifying it out of the denominator, so
/// every row is asserted to be `EmittableNeedsProof` STILL — in the denominator,
/// counted — and its note is asserted to name the SDM evidence, so a row that
/// went green by any other route fails here. The `Punpcklqdq` row is the
/// specific case the gate's own correction comment recorded: its degenerate
/// `PackLowQwords` reconstruction is still `X == X` and still credits nothing,
/// and the WRONG HALF / WRONG ELEMENT WIDTH controls that correction named as
/// missing are what the credit now rests on.
///
/// PINSR*/PEXTR* remain excluded because they are never selected.
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
fn x86_emitted_sse_lane_opcodes_stay_in_the_denominator_and_are_sdm_credited() {
    // These ten credits are corpus-based: the hook decodes CAPTURED bytes. Pin
    // them to what the live encoder emits today, here, in the target that
    // asserts they are green — otherwise an encoder change that made the bytes
    // wrong would leave this test passing over a frozen capture, with only
    // `x86_sse_lane_gate` catching it.
    assert_sse_lane_corpus_is_what_the_live_encoder_emits();
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::X86_64));
    for op in [
        X86Opcode::Pshufd,
        X86Opcode::Pmovmskb,
        // MovdqaRR (register-register) is credited by the SSE lane family; the
        // MEMORY forms MovdqaRM/MovdqaMR (and MovdquRM/MovdquMR) are credited
        // by the two-64-bit-halves-at-ea/ea+8 reconstruction instead (see
        // `x86_packed_128bit_moves_are_reconstructed`). Do NOT move RM/MR here.
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
            "{op:?} is actively emitted value/effect debt and must stay in the denominator — a \
             credited row is still a COUNTED row, and reclassifying it out would launder the \
             ratio"
        );
        assert_eq!(
            x86_deferred_value_op_reason(op),
            None,
            "{op:?} is credited by the SSE lane family and must not also be named deferral debt"
        );
        let row = report
            .rows
            .iter()
            .find(|row| row.opcode_display == format!("x86_64::{op:?}"))
            .unwrap_or_else(|| panic!("x86_64::{op:?} missing from audit"));
        assert!(
            row.finding.is_none(),
            "x86_64::{op:?} must be credited: {row:?}"
        );
        assert!(
            row.note.contains("INDEPENDENT SDM-derived decoder")
                && row.note.contains("x86_sse_lane_proofs"),
            "x86_64::{op:?} went green by some other route than the SSE lane family, which is \
             exactly the laundering this test exists to catch: {}",
            row.note
        );
    }

    // The credit is WITHHELD when the hook does not discharge, and the row then
    // reports a REGRESSION rather than a deferral — so a broken obligation can
    // never be absorbed as honest debt.
    let failed: Result<trust_cg_verify::x86_sse_lane_proofs::SseLaneCredit, String> =
        Err("simulated regression".to_string());
    let degraded =
        on_large_stack(move || CoverageGate::new().audit_x86_with_sse_lane_credit(&failed));
    for op in [X86Opcode::Pshufd, X86Opcode::Ptest, X86Opcode::Packuswb] {
        let row = degraded
            .rows
            .iter()
            .find(|row| row.opcode_display == format!("x86_64::{op:?}"))
            .unwrap();
        assert!(
            matches!(
                &row.finding,
                Some(CoverageFinding::ProofNotDischarged { .. })
            ),
            "a failing SSE lane hook must surface as ProofNotDischarged, not a deferral: {row:?}"
        );
    }
    assert_eq!(
        degraded.covered_count(),
        206 - 10,
        "withholding the SSE lane credit must cost exactly the ten rows (the baseline moved \
         184 -> 200 when the sixteen volatile rows were credited, 200 -> 201 with the \
         128-bit atomic load's AtomicLoadCmpxchg16b, and 201 -> 206 with the five \
         zero-extending loads)"
    );

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
/// MOVDQA{RM,MR} (aligned) are EmittableNeedsProof AND credited COVERED.
///
/// Their evidence comes from TWO places, and the split matters:
///
///   * the VALUE facet from the two-64-bit-halves-at-`ea`/`ea+8` reconstruction
///     — a swapped half, a wrong half offset, a wrong access width or (for a
///     store) a wrong value REFUTES there, because each is a one-sided
///     structural difference in the two-half model
///     (see tests/reconstruction_x86.rs);
///   * the ADDRESS facet from `x86_addressing_proofs`, which decodes the REAL
///     emitted ModR/M+SIB bytes.
///
/// This docstring used to say the machine addresses came from "the INDEPENDENT
/// x86 `encode_lea_*` encoder" and that a wrong EA refutes. That was FALSE:
/// `x86_reconstruct_effective_address` builds BOTH of its address halves from
/// the same operand with structurally identical encoders, so the address half
/// is `X == X` and no wrong base, index, scale or displacement can refute
/// through it. `the_shared_reconstruction_still_has_no_address_teeth` pins that
/// measurement.
///
/// MOVDQARR (register-register) is a separate emitted value row and remains
/// explicit deferred RED debt. This pins the honest credit so a regression that
/// drops either facet (or re-defers the memory forms) is caught.
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
            row.finding.is_none(),
            "x86_64::{op:?} must be COVERED: finding={:?}, note={}",
            row.finding,
            row.note
        );
        assert!(
            row.note
                .contains("ADDRESS decoded from the REAL emitted bytes"),
            "x86_64::{op:?} must carry its ADDRESS facet on the byte-level credit, not on the \
             degenerate effective-address reconstruction: note={}",
            row.note
        );
    }
    // MOVDQARR (register-register copy) stays in the denominator, and its
    // deferral reason asked for exactly one thing: "an independently decoded
    // 128-bit bit-preservation obligation". It now has one, from a DIFFERENT
    // family than these memory forms — `x86_sse_lane_proofs` decodes the real
    // emitted bytes with an independent SDM-derived decoder and states that
    // they denote the full-width 128-bit copy with the intended direction and
    // registers. It is NOT the ea/ea+8 reconstruction that covers RM/MR, and it
    // does NOT claim MOVDQA differs from MOVDQU in VALUE — it does not; that
    // separation is the mnemonic-identity conjunct.
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
    assert!(
        row.finding.is_none() && row.note.contains("x86_sse_lane_proofs"),
        "MovdqaRR must be credited by the SSE lane family, not by the memory-form \
         reconstruction and not by anything else: {row:?}"
    );
    assert!(
        row.note.contains("FULL-WIDTH 128-bit copy"),
        "MovdqaRR's note must say what the credit actually is: {}",
        row.note
    );
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
/// RETRACTED the degenerate proofs entirely. This test pins that (a) the
/// coverage gate keeps them in the proof-required denominator (they are now
/// credited only by the per-instruction NZCV producer/consumer family, see
/// `aarch64_flag_consumer_gate`), (b) `opcode_to_proof_query` returns None —
/// no opcode-level query can credit a select without its reaching producer —
/// and (c) the database contains NO degenerate IfConversion CSEL/CSINC/CSNEG
/// self-equality any more. CSINV remains excluded because lowering does not
/// select it.
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
/// denominator, each covered by its OWN obligation — UMULL by the zext64*zext64
/// proof_umull_rr, SMULL by its sign-extending decoded-word obligation — so the
/// signed form never inherits the unsigned credit, while the never-emitted
/// flag-setting immediate forms remain excluded.
#[test]
fn aarch64_widening_muls_have_their_own_obligations_and_i128_carry_is_covered() {
    use trust_cg_verify::FunctionVerifier;
    use trust_cg_verify::aarch64_value_decode_proofs::{A64ValueForm, a64_value_forms};
    for op in [AArch64Opcode::Smull, AArch64Opcode::Umull] {
        assert!(
            matches!(classify_aarch64(op), OpcodeClass::EmittableNeedsProof),
            "{op:?} is emitted value debt and must stay in the denominator"
        );
        assert!(aarch64_deferred_value_op_reason(op).is_none());
    }
    // SMULL is credited by its own form, whose query cannot resolve to UMULL's
    // obligation, and UMULL keeps its opcode-level binding.
    assert_eq!(
        a64_value_forms(AArch64Opcode::Smull),
        Some(&[A64ValueForm::Smull][..])
    );
    assert!(a64_value_forms(AArch64Opcode::Umull).is_none());
    let (umull_query, _) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Umull)
        .expect("UMULL keeps its binding");
    assert!(
        !A64ValueForm::Smull
            .obligation_name()
            .to_lowercase()
            .contains(umull_query),
        "the SMULL obligation must not answer UMULL's query"
    );
    assert!(FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Smull).is_none());
    assert!(
        matches!(
            classify_aarch64(AArch64Opcode::AddsRI),
            OpcodeClass::FailClosedAllowlisted { .. }
        ),
        "AddsRI is never selected and should remain explicitly excluded"
    );
    // SubsRI IS emitted (the looped stack probe's `SUBS X16, X16, #1`), so it
    // is counted; it is credited only by its decoded-word family
    // (`aarch64_subs_imm_proofs`, L04-P1), never opcode-wide.
    assert!(matches!(
        classify_aarch64(AArch64Opcode::SubsRI),
        OpcodeClass::EmittableNeedsProof
    ));
    assert!(aarch64_deferred_value_op_reason(AArch64Opcode::SubsRI).is_none());
    assert!(FunctionVerifier::opcode_to_proof_query(AArch64Opcode::SubsRI).is_none());
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
/// routinely listed four-to-a-line ("x86-64 206/206 (0 RED), RISC-V 14/17
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
    // The published x86-64 ratio includes the corpus-based MovRI credit and the
    // ten corpus-based SSE LANE credits; refuse a stale capture of either. The
    // published AArch64 ratio includes fifteen corpus-based decoded-value credits.
    assert_movri_corpus_is_what_the_live_encoder_emits();
    assert_sse_lane_corpus_is_what_the_live_encoder_emits();
    assert_a64_value_corpus_is_what_the_live_encoder_emits();
    // The published x86-64 ratio includes the corpus-based MovRI credit, the
    // ten corpus-based SSE LANE credits and the corpus-based MOVSXD-SIB credit;
    // refuse a stale capture of any of them.
    assert_movri_corpus_is_what_the_live_encoder_emits();
    assert_sse_lane_corpus_is_what_the_live_encoder_emits();
    assert_movsxd_sib_corpus_is_what_the_live_encoder_emits();
    // The published WebAssembly ratio includes the float const and FMin/FMax/
    // copysign body credits; refuse a stale capture of either corpus.
    wasm_float_live::assert_float_const_corpus_is_what_the_live_backend_emits();
    wasm_float_live::assert_float_binop_bodies_are_what_the_live_backend_emits();
    wasm_bulk_live::assert_bulk_memory_bodies_are_what_the_live_backend_emits();
    let (aa, x86, rv, wasm) = on_large_stack(|| {
        let gate = CoverageGate::new();
        // The published AArch64 ratio is the one a host whose checker the
        // certificate manifests authorize computes; elsewhere the
        // checker-identity misses are added back (their pins are red there).
        let audit = |arch| {
            let report = gate.audit(arch);
            (
                report.covered_count() + checker_identity_misses(&report),
                report.emittable_count(),
            )
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
        "crates/trust-cg-verify/tests/coverage_gate_tests.rs",
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

/// The note of a row the ADDRESS row credits (`x86_address_audit_row`).
const X86_ADDRESS_ROW_NOTE: &str = "ADDRESS decoded from the REAL emitted bytes";
/// The VALUE leg the ADDRESS row conjoins with its address, as its note states it.
const X86_ADDRESS_ROW_VALUE_LEG: &str = "VALUE: RECONSTRUCTED from real";
/// The note of a row the volatile JOINT row credits (`x86_volatile_joint_audit_row`).
const X86_VOLATILE_JOINT_ROW_NOTE: &str = "VOLATILE, credited JOINTLY";
/// The note of a row the COMPARE-EXCHANGE joint row credits
/// (`x86_compare_exchange_joint_audit_row`), and the VALUE leg it states.
const X86_COMPARE_EXCHANGE_ROW_NOTE: &str = "COMPARE-EXCHANGE, credited JOINTLY";
const X86_COMPARE_EXCHANGE_ROW_VALUE_LEG: &str = "VALUE from the per-instruction reconstruction";

/// The x86-64 ADDRESS credit is LIVE, COUNTED and GATED.
///
/// Three things must hold together, and the third is the one that has bitten
/// this tree before:
///   1. the credited rows really do route through the address lane, not
///      silently past it into the degenerate reconstruction — the 37 plain rows
///      through the ADDRESS row, which also requires their VALUE
///      reconstruction, the 3 compare-exchange rows through their joint row,
///      and the 18 volatile rows through the volatile JOINT row only;
///   2. a FAILING address credit makes exactly those rows RED in the whole
///      report and costs exactly that many covered rows;
///   3. the loss is `ProofNotDischarged`, not `DeferredUnfaithfulModel` — a
///      lane that stopped refuting is a broken proof, not acknowledged debt.
#[test]
fn x86_address_credit_is_live_counted_and_has_teeth() {
    use trust_cg_verify::coverage_gate::{
        CoverageFinding, CoverageGate, GateArch, x86_opcode_has_address_credit,
        x86_opcode_is_compare_exchange_memory, x86_opcode_is_volatile_memory,
    };
    use trust_cg_verify::x86_addressing_proofs as addr;

    let address_opcodes: Vec<X86Opcode> = trust_cg_verify::coverage_gate::ALL_X86_OPCODES
        .iter()
        .copied()
        .filter(|&op| x86_opcode_has_address_credit(op))
        .collect();
    let covered_opcodes: Vec<String> = address_opcodes
        .iter()
        .map(|op| format!("x86_64::{op:?}"))
        .collect();
    // 53 -> 56: the three COMPARE-EXCHANGE rows (`Cmpxchg8`, `Cmpxchg16` and
    // the 128-bit atomic-load pseudo `AtomicLoadCmpxchg16b`). The teeth audit
    // now asks whether a perturbed-address obligation REFUTES rather than
    // whether its halves are different trees, and theirs never refutes; they
    // are credited jointly with their value reconstruction.
    // 56 -> 61: the five ZERO-EXTENDING loads (`MovzxRM8`, `MovzxRM16`,
    // `MovzxRM8Sib` and the two volatile twins), whose captured `0F B6/B7`
    // encodings also carry the destination-write facet.
    assert_eq!(
        covered_opcodes.len(),
        61,
        "the address lane must cover the 40 opcodes the teeth audit found unable to refute an \
         address error through the shared reconstruction (the 35 memory-ACCESS forms plus \
         Lea/LeaSib, for which the address IS the value, plus the 3 zero-extending loads), PLUS \
         the 18 VOLATILE forms, which are byte-identical to their plain siblings and so pose the \
         same address question, PLUS the 3 COMPARE-EXCHANGE forms, whose reconstructions refute \
         no address error either"
    );
    assert_eq!(
        address_opcodes
            .iter()
            .filter(|&&op| x86_opcode_is_volatile_memory(op))
            .count(),
        18,
        "eighteen of the address lane's rows are the volatile forms"
    );
    assert_eq!(
        address_opcodes
            .iter()
            .filter(|&&op| x86_opcode_is_compare_exchange_memory(op))
            .count(),
        3,
        "three of the address lane's rows are the compare-exchange forms"
    );

    // (1) The real credit discharges and the rows say so. A plain row's note
    //     states both of the ADDRESS row's legs, and a compare-exchange row's
    //     both of its joint row's; a volatile row must carry the volatile
    //     JOINT row's note, because the ADDRESS row alone is exactly the
    //     byte-identical plain MOV proof its deferral reason rejected.
    let healthy = on_large_stack(|| CoverageGate::new().audit(GateArch::X86_64));
    for (&op, name) in address_opcodes.iter().zip(&covered_opcodes) {
        let row = healthy
            .rows
            .iter()
            .find(|r| &r.opcode_display == name)
            .unwrap_or_else(|| panic!("{name} row"));
        assert!(row.finding.is_none(), "{name} must be covered: {row:?}");
        if x86_opcode_is_volatile_memory(op) {
            assert!(
                row.note.starts_with(X86_VOLATILE_JOINT_ROW_NOTE)
                    && !row.note.contains(X86_ADDRESS_ROW_NOTE),
                "{name} is VOLATILE and must be credited by the joint row alone, not by the \
                 address row: {}",
                row.note
            );
        } else if x86_opcode_is_compare_exchange_memory(op) {
            assert!(
                row.note.starts_with(X86_COMPARE_EXCHANGE_ROW_NOTE)
                    && row.note.contains(X86_ADDRESS_ROW_NOTE)
                    && row.note.contains(X86_COMPARE_EXCHANGE_ROW_VALUE_LEG),
                "{name} is a COMPARE-EXCHANGE row and must be credited by its joint row on \
                 both its ADDRESS and its VALUE: {}",
                row.note
            );
        } else {
            assert!(
                row.note.contains(X86_ADDRESS_ROW_NOTE),
                "{name} is credited by some OTHER path, so the address lane is not actually \
                 carrying it: {}",
                row.note
            );
            assert!(
                row.note.contains(X86_ADDRESS_ROW_VALUE_LEG),
                "{name} is credited on its ADDRESS alone; the address row must also require \
                 the VALUE reconstruction its note attributes the value facet to: {}",
                row.note
            );
        }
    }
    let healthy_covered = healthy.rows.iter().filter(|r| r.finding.is_none()).count();

    // (2) + (3) A failing credit costs exactly those rows, as ProofNotDischarged.
    let broken: Result<addr::MemMovAddressCredit, String> =
        Err("INJECTED: the address lane stopped refuting".to_string());
    let failed = on_large_stack(move || CoverageGate::new().audit_x86_with_address_credit(&broken));
    let failed_covered = failed.rows.iter().filter(|r| r.finding.is_none()).count();
    assert_eq!(
        healthy_covered - failed_covered,
        covered_opcodes.len(),
        "a failing address credit must cost EXACTLY the {} rows it carries",
        covered_opcodes.len()
    );
    for (&op, name) in address_opcodes.iter().zip(&covered_opcodes) {
        let row = failed
            .rows
            .iter()
            .find(|r| &r.opcode_display == name)
            .unwrap_or_else(|| panic!("{name} row"));
        match &row.finding {
            Some(CoverageFinding::ProofNotDischarged { proof_name, detail }) => {
                assert!(proof_name.contains("ADDR-x86"), "{name}: {proof_name}");
                assert!(detail.contains("INJECTED"), "{name}: {detail}");
                assert_eq!(
                    proof_name.starts_with("VOL-x86 joint"),
                    x86_opcode_is_volatile_memory(op),
                    "{name}: a volatile row fails as its JOINT obligation, a plain row as its \
                     address row: {proof_name}"
                );
            }
            other => panic!(
                "{name} must go RED as ProofNotDischarged when the address lane fails, not \
                 {other:?}"
            ),
        }
    }
}

/// The sixteen x86-64 VOLATILE rows are credited by the JOINT row, never by
/// the ADDRESS row.
///
/// A volatile MOV encodes byte for byte like its plain sibling, so the address
/// lane answers the same question for both. That is exactly why its credit
/// alone is the "byte-identical plain MOV proof" the rows' deferral reason
/// called insufficient. From 88de9e199 the joint row's VALUE leg asked
/// `X86FunctionVerifier::opcode_to_proof_query`, which has no volatile arm, so
/// the joint row returned nothing for all sixteen and each fell through to the
/// address row: all sixteen covered, with the VALUE and BOUNDARY legs gating
/// nothing (still so on ea8492fd9). On that tree this test fails at the first
/// volatile row.
#[test]
fn x86_volatile_rows_are_credited_by_the_joint_row_not_the_address_row() {
    use trust_cg_verify::coverage_gate::x86_opcode_is_volatile_memory;

    let volatile: Vec<String> = ALL_X86_OPCODES
        .iter()
        .filter(|&&op| x86_opcode_is_volatile_memory(op))
        .map(|op| format!("x86_64::{op:?}"))
        .collect();
    assert_eq!(
        volatile.len(),
        18,
        "the eighteen x86-64 volatile memory forms (sixteen MOV forms and the two \
         zero-extending loads)"
    );

    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::X86_64));
    for name in &volatile {
        let row = report
            .rows
            .iter()
            .find(|r| &r.opcode_display == name)
            .unwrap_or_else(|| panic!("{name} row"));
        assert!(row.finding.is_none(), "{name} must be covered: {row:?}");
        assert!(
            row.note.starts_with(X86_VOLATILE_JOINT_ROW_NOTE),
            "{name} is credited by a path other than the JOINT row, so its VALUE and BOUNDARY \
             legs gate nothing: {}",
            row.note
        );
        assert!(
            !row.note.contains(X86_ADDRESS_ROW_NOTE),
            "{name} carries the ADDRESS row's note, i.e. it is credited by the address lane \
             alone: {}",
            row.note
        );
    }
}

/// Assert that `report` differs from `healthy` in exactly the rows `lost`
/// names, each RED as `ProofNotDischarged` whose proof name contains every
/// entry of `names` and none of `absent`, and whose detail contains `detail`.
fn assert_x86_rows_lost_to(
    label: &str,
    healthy: &trust_cg_verify::coverage_gate::CoverageReport,
    report: &trust_cg_verify::coverage_gate::CoverageReport,
    lost: &[X86Opcode],
    names: &[&str],
    absent: &[&str],
    detail: &str,
) {
    let lost: std::collections::HashSet<String> =
        lost.iter().map(|op| format!("x86_64::{op:?}")).collect();
    assert_eq!(
        healthy.covered_count() - report.covered_count(),
        lost.len(),
        "{label}: exactly the {} rows that require the failing leg must leave the covered count",
        lost.len()
    );
    for (before, after) in healthy.rows.iter().zip(&report.rows) {
        assert_eq!(before.opcode_display, after.opcode_display);
        if !lost.contains(&after.opcode_display) {
            assert_eq!(
                before.finding.is_none(),
                after.finding.is_none(),
                "{label}: {} does not require the failing leg and must not move",
                after.opcode_display
            );
            continue;
        }
        let name = &after.opcode_display;
        assert!(
            before.finding.is_none(),
            "{label}: {name} is covered when healthy"
        );
        match &after.finding {
            Some(CoverageFinding::ProofNotDischarged {
                proof_name,
                detail: why,
            }) => {
                for want in names {
                    assert!(proof_name.contains(want), "{label}: {name}: {proof_name}");
                }
                for not in absent {
                    assert!(!proof_name.contains(not), "{label}: {name}: {proof_name}");
                }
                assert!(why.contains(detail), "{label}: {name}: {why}");
            }
            other => panic!(
                "{label}: {name} must go RED as ProofNotDischarged naming the failing leg, not \
                 {other:?}"
            ),
        }
    }
}

/// Each leg of the x86 volatile JOINT obligation is load-bearing.
///
/// With the ADDRESS lane still discharging, a failing VALUE leg or a failing
/// BOUNDARY leg (`x86_volatile_trace`) must take exactly the sixteen volatile
/// rows RED as `ProofNotDischarged` naming that leg, and move no other row. A
/// volatile row that stayed green here would be credited by the address lane
/// alone — the "byte-identical plain MOV proof" its deferral reason rejected.
/// The row functions are pinned directly as well: the joint row credits only
/// when all three legs hold, and the ADDRESS row refuses a volatile opcode even
/// when both of its own legs hold.
#[test]
fn x86_volatile_joint_row_withholds_credit_when_any_leg_fails() {
    use trust_cg_verify::coverage_gate::{
        x86_address_audit_row, x86_opcode_is_volatile_memory, x86_volatile_joint_audit_row,
    };
    use trust_cg_verify::x86_64_function_verifier::reconstruction_discharges_valid;
    use trust_cg_verify::x86_addressing_proofs::mem_mov_address_credit;
    use trust_cg_verify::x86_volatile_trace::volatile_trace_credit;

    let volatile: Vec<X86Opcode> = ALL_X86_OPCODES
        .iter()
        .copied()
        .filter(|&op| x86_opcode_is_volatile_memory(op))
        .collect();
    assert_eq!(
        volatile.len(),
        18,
        "the eighteen x86-64 volatile memory forms (sixteen MOV forms and the two \
         zero-extending loads)"
    );

    let (healthy, no_value, no_boundary) = on_large_stack(|| {
        let gate = CoverageGate::new();
        let healthy = gate.audit(GateArch::X86_64);
        let no_value = gate.audit_x86_with_value_and_trace_credit(
            &|op, config| {
                !x86_opcode_is_volatile_memory(op) && reconstruction_discharges_valid(op, config)
            },
            &volatile_trace_credit(),
        );
        let no_boundary = gate.audit_x86_with_value_and_trace_credit(
            &reconstruction_discharges_valid,
            &Err("INJECTED: a volatile hazard survived".to_string()),
        );
        (healthy, no_value, no_boundary)
    });
    let address = mem_mov_address_credit();
    let trace = volatile_trace_credit();
    assert!(
        address.is_ok(),
        "the ADDRESS leg must discharge throughout: {address:?}"
    );
    assert!(trace.is_ok(), "the BOUNDARY leg must discharge: {trace:?}");

    assert_x86_rows_lost_to(
        "VALUE leg failing",
        &healthy,
        &no_value,
        &volatile,
        &["VOL-x86 joint", "VALUE-x86"],
        &["ADDR-x86", "VOL-x86-trace"],
        "reconstruction",
    );
    assert_x86_rows_lost_to(
        "BOUNDARY leg failing",
        &healthy,
        &no_boundary,
        &volatile,
        &["VOL-x86 joint", "VOL-x86-trace"],
        &["ADDR-x86", "VALUE-x86"],
        "INJECTED",
    );

    for &op in &volatile {
        let display = format!("x86_64::{op:?}");
        let joint = |address_ok: bool, value: bool, trace_ok: bool| {
            x86_volatile_joint_audit_row(
                &display,
                op,
                if address_ok {
                    address.clone()
                } else {
                    Err("INJECTED address".to_string())
                },
                value,
                if trace_ok {
                    trace.clone()
                } else {
                    Err("INJECTED trace".to_string())
                },
            )
        };
        assert!(
            joint(true, true, true).finding.is_none(),
            "{display}: all three legs hold"
        );
        for (address_ok, value, trace_ok) in [
            (false, true, true),
            (true, false, true),
            (true, true, false),
            (false, false, false),
        ] {
            assert!(
                matches!(
                    joint(address_ok, value, trace_ok).finding,
                    Some(CoverageFinding::ProofNotDischarged { .. })
                ),
                "{display}: the joint row credited with a failing leg (address {address_ok}, \
                 value {value}, trace {trace_ok})"
            );
        }
        let address_row = x86_address_audit_row(display.clone(), op, address.clone(), true);
        assert!(
            matches!(
                &address_row.finding,
                Some(CoverageFinding::ProofNotDischarged { proof_name, .. })
                    if proof_name.starts_with("VOL-x86 joint")
            ),
            "{display}: the ADDRESS row must refuse a volatile opcode even when its address \
             and value legs hold: {address_row:?}"
        );
    }
}

/// The ADDRESS row requires the VALUE leg as well as the address.
///
/// The address lane proves the address from the real emitted bytes, and the
/// row's note attributes the value facet to the reconstruction. Before this
/// test the gate returned the address row without running the reconstruction
/// at all, so the value facet of all 37 plain rows — memory-ALU forms such as
/// `AddRM` and `XorMR` included — was checked by nothing. A failing VALUE leg
/// must now take exactly those rows RED as `ProofNotDischarged` naming it, with
/// the address lane still discharging. The three COMPARE-EXCHANGE rows read
/// their VALUE leg through the same hook, so a failure injected there takes
/// exactly those three RED as their joint row's failure. The row function is
/// pinned directly as well: each leg alone refuses.
#[test]
fn x86_address_rows_conjoin_the_value_reconstruction() {
    use trust_cg_verify::coverage_gate::{
        x86_address_audit_row, x86_opcode_has_address_credit,
        x86_opcode_is_compare_exchange_memory, x86_opcode_is_volatile_memory,
    };
    use trust_cg_verify::x86_64_function_verifier::reconstruction_discharges_valid;
    use trust_cg_verify::x86_addressing_proofs::mem_mov_address_credit;
    use trust_cg_verify::x86_volatile_trace::volatile_trace_credit;

    let plain = |op: X86Opcode| {
        x86_opcode_has_address_credit(op)
            && !x86_opcode_is_volatile_memory(op)
            && !x86_opcode_is_compare_exchange_memory(op)
    };
    let plain_rows: Vec<X86Opcode> = ALL_X86_OPCODES
        .iter()
        .copied()
        .filter(|&op| plain(op))
        .collect();
    assert_eq!(
        plain_rows.len(),
        40,
        "the 35 memory-ACCESS forms plus Lea/LeaSib, plus the 3 zero-extending loads"
    );
    let compare_exchange_rows: Vec<X86Opcode> = ALL_X86_OPCODES
        .iter()
        .copied()
        .filter(|&op| x86_opcode_is_compare_exchange_memory(op))
        .collect();
    assert_eq!(
        compare_exchange_rows.len(),
        3,
        "Cmpxchg8, Cmpxchg16 and AtomicLoadCmpxchg16b"
    );

    let (healthy, no_plain_value, no_cmpxchg_value) = on_large_stack(move || {
        let gate = CoverageGate::new();
        let healthy = gate.audit(GateArch::X86_64);
        let no_plain_value = gate.audit_x86_with_value_and_trace_credit(
            &|op, config| !plain(op) && reconstruction_discharges_valid(op, config),
            &volatile_trace_credit(),
        );
        let no_cmpxchg_value = gate.audit_x86_with_value_and_trace_credit(
            &|op, config| {
                !x86_opcode_is_compare_exchange_memory(op)
                    && reconstruction_discharges_valid(op, config)
            },
            &volatile_trace_credit(),
        );
        (healthy, no_plain_value, no_cmpxchg_value)
    });
    let address = mem_mov_address_credit();
    assert!(
        address.is_ok(),
        "the ADDRESS leg must discharge: {address:?}"
    );
    assert_x86_rows_lost_to(
        "VALUE leg failing on the plain address rows",
        &healthy,
        &no_plain_value,
        &plain_rows,
        &["VALUE-x86"],
        &["ADDR-x86", "VOL-x86"],
        "reconstruction",
    );
    assert_x86_rows_lost_to(
        "VALUE leg failing on the compare-exchange rows",
        &healthy,
        &no_cmpxchg_value,
        &compare_exchange_rows,
        &["ADDR-x86 + reconstruction"],
        &["VOL-x86"],
        "VALUE",
    );

    for &op in &plain_rows {
        let display = format!("x86_64::{op:?}");
        let row = |address_ok: bool, value: bool| {
            x86_address_audit_row(
                display.clone(),
                op,
                if address_ok {
                    address.clone()
                } else {
                    Err("INJECTED address".to_string())
                },
                value,
            )
        };
        assert!(
            row(true, true).finding.is_none(),
            "{display}: both legs hold"
        );
        for (address_ok, value, leg) in [
            (true, false, "VALUE-x86"),
            (false, true, "ADDR-x86"),
            (false, false, "ADDR-x86 + VALUE-x86"),
        ] {
            let red = row(address_ok, value);
            assert!(
                matches!(
                    &red.finding,
                    Some(CoverageFinding::ProofNotDischarged { proof_name, .. })
                        if proof_name == &format!("{leg} ({op:?})")
                ),
                "{display}: the ADDRESS row credited, or misnamed, a failing leg (address \
                 {address_ok}, value {value}): {red:?}"
            );
        }
    }
}

/// An address-credited memory-ALU row whose VALUE reconstruction is WRONG stays
/// RED, although its address is right.
///
/// The sibling of `x86_address_rows_conjoin_the_value_reconstruction` with a
/// real evaluation in place of an injected verdict: the VALUE hook rebuilds
/// each representative obligation of `AddRM`, `SubRM` and `ImulRM` from the
/// real opcode, then flips bit 0 of the machine-side result — a memory-ALU form
/// that loads from the right address and computes the wrong value — and
/// evaluates it. The address lane still discharges on the real emitted bytes.
/// Before the ADDRESS row required its VALUE leg, all three rows stayed green
/// here, because the gate never ran the reconstruction for them.
#[test]
fn x86_address_row_with_a_wrong_value_reconstruction_stays_red() {
    use trust_cg_verify::coverage_gate::{
        x86_opcode_has_address_credit, x86_opcode_is_compare_exchange_memory,
        x86_opcode_is_volatile_memory,
    };
    use trust_cg_verify::lowering_proof::{ProofObligation, verify_by_evaluation};
    use trust_cg_verify::smt::SmtExpr;
    use trust_cg_verify::verify::VerificationResult;
    use trust_cg_verify::x86_64_function_verifier::{
        reconstruct_alu_obligation, reconstruction_discharges_valid,
        representative_reconstructable_inst,
    };
    use trust_cg_verify::x86_volatile_trace::volatile_trace_credit;

    const WRONG_VALUE: [X86Opcode; 3] = [X86Opcode::AddRM, X86Opcode::SubRM, X86Opcode::ImulRM];
    for op in WRONG_VALUE {
        assert!(
            x86_opcode_has_address_credit(op)
                && !x86_opcode_is_volatile_memory(op)
                && !x86_opcode_is_compare_exchange_memory(op),
            "{op:?} must be a plain ADDRESS row"
        );
    }

    /// The representative obligation of `op`, with its machine-side result
    /// XORed with 1 when `corrupt`.
    fn obligation(op: X86Opcode, corrupt: bool) -> ProofObligation {
        let inst = representative_reconstructable_inst(op)
            .unwrap_or_else(|| panic!("{op:?} has a representative instance"));
        let mut obligation =
            reconstruct_alu_obligation(&inst).unwrap_or_else(|| panic!("{op:?} reconstructs"));
        if corrupt {
            let width = obligation
                .aarch64_expr
                .try_bv_width()
                .unwrap_or_else(|e| panic!("{op:?}: machine side is not a bitvector: {e:?}"));
            obligation.aarch64_expr = obligation
                .aarch64_expr
                .clone()
                .bvxor(SmtExpr::bv_const(1, width));
        }
        obligation
    }

    let (healthy, wrong_value) = on_large_stack(|| {
        // The control: the uncorrupted reconstruction is Valid and the
        // corrupted one is not, so the hook below withholds for the reason the
        // test names and for no other.
        for op in WRONG_VALUE {
            assert!(
                matches!(
                    verify_by_evaluation(&obligation(op, false)),
                    VerificationResult::Valid
                ),
                "{op:?}: the real reconstruction must be Valid"
            );
            assert!(
                !matches!(
                    verify_by_evaluation(&obligation(op, true)),
                    VerificationResult::Valid
                ),
                "{op:?}: a machine side with bit 0 flipped must not be Valid"
            );
        }
        let gate = CoverageGate::new();
        let healthy = gate.audit(GateArch::X86_64);
        let wrong_value = gate.audit_x86_with_value_and_trace_credit(
            &|op, config| {
                if WRONG_VALUE.contains(&op) {
                    matches!(
                        verify_by_evaluation(&obligation(op, true)),
                        VerificationResult::Valid
                    )
                } else {
                    reconstruction_discharges_valid(op, config)
                }
            },
            &volatile_trace_credit(),
        );
        (healthy, wrong_value)
    });
    assert!(
        trust_cg_verify::x86_addressing_proofs::mem_mov_address_credit().is_ok(),
        "the ADDRESS leg must discharge"
    );
    assert_x86_rows_lost_to(
        "a wrong VALUE reconstruction on memory-ALU rows",
        &healthy,
        &wrong_value,
        &WRONG_VALUE,
        &["VALUE-x86"],
        &["ADDR-x86", "VOL-x86"],
        "reconstruction",
    );
}

/// Opcode names ENC-5 has no arm for: `check_one` on the opcode with no
/// operands returns its catch-all `A64_UNDECODED_FAMILY` allowlist, which
/// only the catch-all arm returns, whatever the operands or the word. An
/// opcode with an arm returns something else, or panics on the empty operand
/// list.
fn aarch64_opcodes_without_an_enc5_arm() -> Vec<AArch64Opcode> {
    use trust_cg_codegen::aarch64::decode_check::{A64_UNDECODED_FAMILY, A64DecodeCheck};
    use trust_cg_codegen::decode_check::{DecodeCheck, DecodeCheckOutcome};

    ALL_AARCH64_OPCODES
        .iter()
        .copied()
        .filter(|&op| {
            let inst = trust_cg_ir::MachInst::new(op, vec![]);
            matches!(
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    A64DecodeCheck.check_one(&inst, &0u32.to_le_bytes(), None)
                })),
                Ok(DecodeCheckOutcome::Allowlisted(reason)) if reason == A64_UNDECODED_FAMILY
            )
        })
        .collect()
}

/// ENC-5 does not decode every emitted AArch64 word. Derived from the code:
/// the credited rows whose opcode ENC-5 has no arm for, split by how the
/// function verifier binds them (opcode-wide: its per-instruction query binds
/// even an instruction with no operands; otherwise per instruction, chosen or
/// refused from the operands), and the emitted rows without an arm at all.
/// Both lists and the count are pinned, so they only change deliberately, and
/// LIMITATIONS.md's paragraph must name exactly these opcodes and counts.
/// ENC-5's arms also return named allowlist reasons without decoding the word;
/// those reasons are pinned too, and the shifted register-ALU exits are
/// checked to allowlist only shapes the verifier refuses.
#[test]
fn credited_aarch64_rows_without_an_enc5_arm_are_pinned_and_disclosed() {
    use trust_cg_verify::FunctionVerifier;
    // E0.2: no row is credited opcode-wide any more. An operand-less
    // instance names at most a registry theorem found by name, which is
    // refused, so the opcode-wide list and its degenerate subset are empty
    // and every gate-covered row without an ENC-5 arm is bound (if at all)
    // per instruction.
    const OPCODE_WIDE: [&str; 0] = [];
    const DEGENERATE_FALLBACK: [&str; 0] = [];
    // The rows that WERE opcode-wide on a degenerate X==X binding before
    // E0.2; each is still first rebuilt from its operands when it can be.
    const FORMERLY_DEGENERATE_FALLBACK: [&str; 16] = [
        "Neg", "AndRI", "OrrRI", "EorRI", "FaddRR", "FsubRR", "FmulRR", "FdivRR", "FnegRR",
        "FsqrtRR", "FcvtzsRR", "FcvtzuRR", "ScvtfRR", "UcvtfRR", "FcvtSD", "FcvtDS",
    ];
    const PER_INSTRUCTION: [&str; 0] = [];
    // The opaque LL/SC carriers have no single-word encoding: the post-RA
    // expansion replaces each with its exclusive loop (decoded by ENC-5)
    // before encoding, and the encoder refuses a survivor by name.
    const EMITTED_WITHOUT_ARM: [&str; 12] = [
        "LlscRmw8",
        "LlscRmw16",
        "LlscRmw32",
        "LlscRmw64",
        "LlscCmpSwap8",
        "LlscCmpSwap16",
        "LlscCmpSwap32",
        "LlscCmpSwap64",
        "LlscLoad128",
        "LlscStore128",
        "LlscRmw128",
        "LlscCmpSwap128",
    ];
    const ENC5_ARM_EXITS: [&str; 28] = [
        "a64-fcmp: operand outside the scalar H/S/D register banks",
        "a64-slice1: non-imm add/sub-imm operand",
        "a64-slice1: non-imm move-wide source",
        "a64-slice1: non-register add/sub-imm operand",
        "a64-slice1: non-register branch-reg operand",
        "a64-slice1: non-register cmp-branch operand",
        "a64-slice1: non-register move-wide dst",
        "a64-slice1: unresolved branch target (no fixup hole recorded)",
        "a64-slice1: unresolved cmp-branch target",
        "a64-slice3: non-immediate EOR shifted-register amount",
        "a64-slice3: non-register EOR shifted-register operand",
        "a64-slice3: non-register add/sub-reg operand",
        "a64-slice3: non-register logical-reg operand",
        "a64-slice3: shifted add/sub variant not yet decoded",
        "a64-slice3: shifted logical variant not yet decoded",
        "a64-slice5: non-imm BCond cond",
        "a64-slice5: non-register MulRR operand",
        "a64-slice5: non-register div operand",
        "a64-slice5: non-register move operand",
        "a64-slice5: unresolved BCond target",
        "a64-slice6: non-immediate bitfield control",
        "a64-slice6: non-register bitfield operand",
        "a64-slice6: non-register extend operand",
        "a64-slice6: non-register shift operand",
        "a64-slice7: non-register ORN operand",
        "a64-slice7: non-register madd/msub operand",
        "a64-slice7: non-register variable-shift operand",
        "a64-value: shape outside the decoded value model",
    ];

    let undecoded = aarch64_opcodes_without_an_enc5_arm();
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::AArch64));
    let mut opcode_wide = Vec::new();
    let mut degenerate_fallback = Vec::new();
    let mut per_instruction = Vec::new();
    let mut emitted_without_arm = Vec::new();
    for (&op, row) in ALL_AARCH64_OPCODES.iter().zip(&report.rows) {
        assert_eq!(row.opcode_display, format!("AArch64::{op:?}"));
        if row.class != OpcodeClass::EmittableNeedsProof || !undecoded.contains(&op) {
            continue;
        }
        emitted_without_arm.push(format!("{op:?}"));
        // A checker-identity miss (`checker_identity_misses`) is a row a
        // qualified host credits. Skipping it here would make the lists below
        // depend on the host, so it must not be a row without an ENC-5 arm.
        assert!(
            !(row.finding.is_some()
                && row
                    .note
                    .contains(trust_cg_verify::bound_memory_authority::CHECKER_IDENTITY_MISS)),
            "{op:?} is a checker-identity miss with no ENC-5 arm: {row:?}"
        );
        if row.finding.is_some() {
            continue;
        }
        // Opcode-wide: an instruction with no operands at all still verifies
        // and promotes. A degenerate (X==X) binding is recorded as such.
        match verify_alone(trust_cg_ir::MachInst::new(op, vec![])) {
            (trust_cg_verify::InstructionVerificationResult::Verified { degenerate, .. }, true) => {
                opcode_wide.push(format!("{op:?}"));
                if degenerate {
                    degenerate_fallback.push(format!("{op:?}"));
                }
            }
            _ => per_instruction.push(format!("{op:?}")),
        }
    }
    assert_eq!(
        opcode_wide, OPCODE_WIDE,
        "credited opcode-wide with no ENC-5 arm; update the pin and LIMITATIONS.md deliberately"
    );
    assert_eq!(
        per_instruction, PER_INSTRUCTION,
        "credited per instruction with no ENC-5 arm; update the pin and LIMITATIONS.md deliberately"
    );
    assert_eq!(
        degenerate_fallback, DEGENERATE_FALLBACK,
        "opcode-wide rows whose operand-independent binding is degenerate; update the pin and \
         LIMITATIONS.md deliberately"
    );
    // Each of those is first rebuilt from its operands when it can be.
    for name in FORMERLY_DEGENERATE_FALLBACK {
        let op = *ALL_AARCH64_OPCODES
            .iter()
            .find(|op| format!("{op:?}") == name)
            .expect("an opcode");
        let representative =
            trust_cg_verify::function_verifier::representative_reconstructable_inst(op)
                .unwrap_or_else(|| panic!("{name} has no reconstruction"));
        assert!(
            trust_cg_verify::reconstruct_alu_obligation(&representative).is_some(),
            "{name}"
        );
    }
    assert_eq!(
        emitted_without_arm, EMITTED_WITHOUT_ARM,
        "emitted rows with no ENC-5 arm; update the pin and LIMITATIONS.md deliberately"
    );
    // The bitwise NEON ops left this list when ENC-5 began decoding their
    // bound 16B shape, FRINTN when its FP data-processing arm landed.
    for op in [
        AArch64Opcode::NeonAndV,
        AArch64Opcode::NeonOrrV,
        AArch64Opcode::NeonEorV,
        AArch64Opcode::NeonBicV,
        AArch64Opcode::NeonNotV,
        AArch64Opcode::FrintnRR,
    ] {
        assert!(!undecoded.contains(&op), "{op:?}");
    }

    let limitations = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../LIMITATIONS.md"),
    )
    .expect("read LIMITATIONS.md");
    const MARKER: &str = "ENC-5 does not decode every emitted AArch64 word.";
    let start = limitations
        .find(MARKER)
        .expect("LIMITATIONS.md must disclose the credited rows without an ENC-5 arm");
    let paragraph = &limitations[start..];
    let paragraph = &paragraph[..paragraph.find("\n\n").unwrap_or(paragraph.len())];
    let names = |segment: &str| -> std::collections::BTreeSet<String> {
        segment
            .split('`')
            .skip(1)
            .step_by(2)
            .filter(|token| {
                ALL_AARCH64_OPCODES
                    .iter()
                    .any(|op| format!("{op:?}") == *token)
            })
            .map(str::to_owned)
            .collect()
    };
    let as_set = |list: &[&str]| -> std::collections::BTreeSet<String> {
        list.iter().map(|name| (*name).to_owned()).collect()
    };
    // The paragraph names the opcode-wide rows, then (after "per
    // instruction") the per-instruction rows, then (after "degenerate") the
    // degenerate-fallback subset.
    let per_at = paragraph
        .find(" per instruction")
        .expect("a per-instruction segment");
    let degenerate_at = paragraph
        .find("degenerate X==X")
        .expect("a degenerate-fallback segment");
    let emitted_at = paragraph
        .find("emitted rows without an arm are")
        .expect("an emitted-without-arm segment");
    assert!(per_at < degenerate_at && degenerate_at < emitted_at);
    assert_eq!(
        names(&paragraph[..per_at]),
        as_set(&OPCODE_WIDE),
        "LIMITATIONS.md's opcode-wide list"
    );
    assert_eq!(
        names(&paragraph[per_at..degenerate_at]),
        as_set(&PER_INSTRUCTION),
        "LIMITATIONS.md's per-instruction list"
    );
    assert_eq!(
        names(&paragraph[degenerate_at..emitted_at]),
        as_set(&DEGENERATE_FALLBACK),
        "LIMITATIONS.md's degenerate-fallback list"
    );
    assert_eq!(
        names(&paragraph[emitted_at..]),
        as_set(&EMITTED_WITHOUT_ARM),
        "LIMITATIONS.md's emitted-without-arm list"
    );
    // LIMITATIONS.md states the credited count a host whose checker the
    // certificate manifests authorize computes; elsewhere the checker-identity
    // misses are added back, as `published_coverage_ratios_match_the_gate`
    // does (their qualification pins are red there).
    for count in [
        format!(
            "{} of the {} credited rows",
            OPCODE_WIDE.len() + PER_INSTRUCTION.len(),
            report.covered_count() + checker_identity_misses(&report)
        ),
        format!("{} opcode-wide", OPCODE_WIDE.len()),
        format!("{} per instruction", PER_INSTRUCTION.len()),
        format!("{} of the opcode-wide rows", DEGENERATE_FALLBACK.len()),
        format!(
            "{} of the {} emitted rows",
            EMITTED_WITHOUT_ARM.len(),
            report.emittable_count()
        ),
    ] {
        assert!(
            paragraph.contains(&count),
            "LIMITATIONS.md must state `{count}`"
        );
    }

    // Named allowlist exits inside ENC-5's arms (the catch-all is exported
    // as a constant and counted above).
    let source = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../trust-cg-codegen/src/aarch64/decode_check.rs"),
    )
    .expect("read the ENC-5 source");
    let body = &source[..source.find("#[cfg(test)]").unwrap_or(source.len())];
    let mut exits = std::collections::BTreeSet::new();
    for (index, _) in body.match_indices("Allowlisted(") {
        let rest = body[index + "Allowlisted(".len()..].trim_start();
        if let Some(literal) = rest.strip_prefix('"') {
            exits.insert(&literal[..literal.find('"').expect("closed literal")]);
        }
    }
    assert_eq!(
        exits.into_iter().collect::<Vec<_>>(),
        ENC5_ARM_EXITS,
        "ENC-5's named arm exits changed; update the pin and LIMITATIONS.md deliberately"
    );
    let exits_paragraph = &limitations[limitations
        .find("ENC-5's arms also allowlist")
        .expect("LIMITATIONS.md must disclose ENC-5's arm exits")..];
    let stated = format!("{} named reasons", ENC5_ARM_EXITS.len());
    assert!(
        exits_paragraph.contains(&stated),
        "LIMITATIONS.md must state `{stated}`"
    );

    // The shifted register-ALU exits: the three-register shape is decoded
    // (live word Match, other word Mismatch); a shape with an extra operand
    // reaches the exit, and the function verifier refuses it.
    use trust_cg_codegen::aarch64::decode_check::A64DecodeCheck;
    use trust_cg_codegen::aarch64::encode::encode_instruction;
    use trust_cg_codegen::decode_check::{DecodeCheck, DecodeCheckOutcome};
    use trust_cg_ir::{MachInst, MachOperand, PReg};
    let x = |n: u16| MachOperand::PReg(PReg::new(n));
    for op in [
        AArch64Opcode::AddRR,
        AArch64Opcode::SubRR,
        AArch64Opcode::AndRR,
        AArch64Opcode::OrrRR,
        AArch64Opcode::EorRR,
    ] {
        let three = MachInst::new(op, vec![x(0), x(1), x(2)]);
        let word = encode_instruction(&three).expect("encodes");
        assert!(
            matches!(
                A64DecodeCheck.check_one(&three, &word.to_le_bytes(), None),
                DecodeCheckOutcome::Match
            ),
            "{op:?}"
        );
        assert!(
            matches!(
                A64DecodeCheck.check_one(&three, &0xDEAD_BEEFu32.to_le_bytes(), None),
                DecodeCheckOutcome::Mismatch(_)
            ),
            "{op:?}"
        );
        let four = MachInst::new(op, vec![x(0), x(1), x(2), MachOperand::Imm(3)]);
        assert!(
            matches!(
                A64DecodeCheck.check_one(&four, &0xDEAD_BEEFu32.to_le_bytes(), None),
                DecodeCheckOutcome::Allowlisted(_)
            ),
            "{op:?}"
        );
        assert_eq!(FunctionVerifier::inst_to_proof_query(&four), None, "{op:?}");
    }

    // The immediate shifts with a register (or missing) amount: the encoder
    // refuses them, ENC-5 reports a mismatch for any word (it used to
    // allowlist one), and the function verifier refuses the register form.
    for op in [
        AArch64Opcode::LslRI,
        AArch64Opcode::LsrRI,
        AArch64Opcode::AsrRI,
    ] {
        let good = MachInst::new(op, vec![x(0), x(1), MachOperand::Imm(3)]);
        let word = encode_instruction(&good).expect("encodes");
        assert!(
            matches!(
                A64DecodeCheck.check_one(&good, &word.to_le_bytes(), None),
                DecodeCheckOutcome::Match
            ),
            "{op:?}"
        );
        for operands in [vec![x(0), x(1), x(2)], vec![x(0), x(1)]] {
            let bad = MachInst::new(op, operands);
            assert!(encode_instruction(&bad).is_err(), "{bad:?}");
            assert!(
                matches!(
                    A64DecodeCheck.check_one(&bad, &0xDEAD_BEEFu32.to_le_bytes(), None),
                    DecodeCheckOutcome::Mismatch(_)
                ),
                "{bad:?}"
            );
        }
        let register_amount = MachInst::new(op, vec![x(0), x(1), x(2)]);
        assert_eq!(
            FunctionVerifier::inst_to_proof_query(&register_amount),
            None,
            "{op:?}"
        );
        assert!(trust_cg_verify::reconstruct_alu_obligation(&register_amount).is_none());
    }
}

/// Verify one instruction alone: its result and whether it promotes.
fn verify_alone(
    inst: trust_cg_ir::MachInst,
) -> (trust_cg_verify::InstructionVerificationResult, bool) {
    let mut func = trust_cg_ir::MachFunction::new(
        "alone".to_string(),
        trust_cg_ir::Signature::new(vec![], vec![]),
    );
    let id = func.push_inst(inst);
    let entry = func.entry;
    func.append_inst(entry, id);
    let report = trust_cg_verify::verify_function(&func);
    let promotable = report.emitted_opcode_inventory().is_promotable();
    (report.instructions[0].result.clone(), promotable)
}

/// Operand shapes for the trailing-operand inventory: every shape of up to
/// three operands over a wide pool, four over a middle pool and five over a
/// small one (each longer shape extends a shorter one from the same pool).
fn trailing_operand_shapes() -> Vec<Vec<trust_cg_ir::MachOperand>> {
    use trust_cg_ir::types::BlockId;
    use trust_cg_ir::{MachOperand, PReg, SpecialReg};
    let p = |n: u16| MachOperand::PReg(PReg::new(n));
    let full = vec![
        p(1),
        p(2),
        p(33),
        p(34),
        p(97),
        p(98),
        p(129),
        p(130),
        p(65),
        p(66),
        p(166),
        p(31),
        MachOperand::Special(SpecialReg::XZR),
        MachOperand::Special(SpecialReg::WZR),
        MachOperand::Special(SpecialReg::SP),
        MachOperand::Imm(0),
        MachOperand::Imm(1),
        MachOperand::Imm(3),
        MachOperand::Imm(12),
        MachOperand::Imm(255),
        MachOperand::Imm(4096),
        MachOperand::Imm(0xF0F0),
        MachOperand::FImm(1.0),
        MachOperand::Symbol("s".into()),
        MachOperand::Block(BlockId(1)),
    ];
    let middle = vec![
        p(1),
        p(2),
        p(33),
        p(34),
        p(97),
        p(129),
        p(65),
        p(66),
        MachOperand::Special(SpecialReg::XZR),
        MachOperand::Imm(0),
        MachOperand::Imm(1),
        MachOperand::Imm(3),
        MachOperand::Imm(12),
        MachOperand::Symbol("s".into()),
    ];
    let small = vec![
        p(1),
        p(33),
        p(97),
        p(65),
        MachOperand::Imm(0),
        MachOperand::Imm(1),
        MachOperand::Imm(3),
        MachOperand::Imm(12),
    ];
    let mut out = vec![vec![]];
    let mut previous: Vec<Vec<MachOperand>> = vec![vec![]];
    for arity in 1..=5 {
        let pool = match arity {
            1..=3 => &full,
            4 => &middle,
            _ => &small,
        };
        let mut next = Vec::new();
        for base in &previous {
            if !base.iter().all(|operand| pool.contains(operand)) {
                continue;
            }
            for operand in pool {
                let mut shape = base.clone();
                shape.push(operand.clone());
                next.push(shape);
            }
        }
        out.extend(next.iter().cloned());
        previous = next;
    }
    out
}

/// The encoder does not check arity: for many opcodes it ignores an operand
/// after the ones its form encodes. Derived from the code: the opcodes with a
/// shape (from [`trailing_operand_shapes`]) whose last operand, other than
/// `#0`, leaves the encoded word unchanged, while the function verifier binds
/// that shape to an obligation (per-instruction query or reconstruction). The
/// list is pinned so it only changes deliberately, and LIMITATIONS.md must
/// name exactly these opcodes. It is an open gap, not a claim that the words
/// are wrong: ENC-5 ignores the extra operand too for most of them.
#[test]
fn credited_aarch64_shapes_with_an_ignored_trailing_operand_are_pinned_and_disclosed() {
    use std::collections::BTreeMap;
    use trust_cg_codegen::aarch64::encode::encode_instruction;
    use trust_cg_ir::{MachInst, MachOperand};
    use trust_cg_verify::FunctionVerifier;
    const IGNORED_TRAILING_OPERAND: [&str; 117] = [
        "AddRI",
        "SubRI",
        "MulRR",
        "Msub",
        "Umull",
        "SDiv",
        "UDiv",
        "Madd",
        "Smulh",
        "Umulh",
        "Adc",
        "Sbc",
        "EorRRShift",
        "AddRRShift",
        "SubRRShift",
        "AddRRShiftLsr",
        "LdrLiteral",
        "STRWui",
        "STRXui",
        "STRSui",
        "STRDui",
        "LdrswRO",
        "Adr",
        "Adrp",
        "AddPCRel",
        "LdrGot",
        "LdrTlvp",
        "B",
        "BCond",
        "Bcc",
        "Bl",
        "BL",
        "TailCall",
        "Sxtb",
        "Sxth",
        "Sxtw",
        "Uxtb",
        "Uxth",
        "Uxtw",
        "FaddRR",
        "FsubRR",
        "FmulRR",
        "FdivRR",
        "FmaddRR",
        "FnegRR",
        "FabsRR",
        "FsqrtRR",
        "FmaxnmRR",
        "FminnmRR",
        "FcvtSD",
        "FcvtDS",
        "Ldar",
        "Ldarb",
        "Ldarh",
        "Stlr",
        "Stlrb",
        "Stlrh",
        "Cas",
        "Casa",
        "Casal",
        "Casl",
        "Ldadd",
        "Ldadda",
        "Ldaddal",
        "Ldaddl",
        "Ldclr",
        "Ldclra",
        "Ldclral",
        "Ldclrl",
        "Ldeor",
        "Ldeora",
        "Ldeoral",
        "Ldeorl",
        "Ldset",
        "Ldseta",
        "Ldsetal",
        "Ldsetl",
        "NeonAddV",
        "NeonSubV",
        "NeonMulV",
        "NeonOrrV",
        "NeonCmeqV",
        "NeonCmgeV",
        "NeonCmgtV",
        "NeonCmhiV",
        "NeonCmhsV",
        "NeonFaddV",
        "NeonFsubV",
        "NeonFmulV",
        "NeonFdivV",
        "NeonFmlaV",
        "NeonFmlsV",
        "NeonUcvtfV",
        "NeonScvtfV",
        "NeonDupScalarD",
        "NeonFmlaLaneV",
        "NeonFcvtlV",
        "NeonFcvtl2V",
        "NeonFcmgtV",
        "NeonSmaxV",
        "NeonSminV",
        "NeonUmaxV",
        "NeonUminV",
        "NeonDupGen",
        "NeonDupElem",
        "NeonInsGen",
        "NeonUmovGen",
        "NeonMovi",
        "NeonRbitV",
        "NeonRev32V",
        "NeonRev64V",
        "NeonCntV",
        "NeonBitV",
        "NeonUdotV",
        "NeonExtV",
        "NeonLd1Post",
        "NeonSt1Post",
    ];

    let found = on_large_stack(|| {
        let shapes = trailing_operand_shapes();
        let mut found = Vec::new();
        for &op in ALL_AARCH64_OPCODES {
            let mut words: BTreeMap<String, u32> = BTreeMap::new();
            let mut credited = false;
            for shape in &shapes {
                let inst = MachInst::new(op, shape.clone());
                let Ok(Ok(word)) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    encode_instruction(&inst)
                })) else {
                    continue;
                };
                words.insert(format!("{shape:?}"), word);
                if credited || shape.len() < 2 || matches!(shape.last(), Some(MachOperand::Imm(0)))
                {
                    continue;
                }
                let prefix = format!("{:?}", &shape[..shape.len() - 1]);
                if words.get(&prefix) != Some(&word) {
                    continue;
                }
                credited = FunctionVerifier::inst_to_proof_query(&inst).is_some()
                    || trust_cg_verify::reconstruct_alu_obligation(&inst).is_some();
            }
            if credited {
                found.push(format!("{op:?}"));
            }
        }
        found
    });
    assert_eq!(
        found, IGNORED_TRAILING_OPERAND,
        "credited shapes whose trailing operand the encoder ignores; update the pin and \
         LIMITATIONS.md deliberately"
    );
    // The shapes the verifier refuses left this list.
    for gone in [
        "AddRR", "SubRR", "AndRR", "OrrRR", "EorRR", "AddsRR", "SubsRR", "Neg", "LslRI", "LsrRI",
        "AsrRI",
    ] {
        assert!(!found.iter().any(|name| name == gone), "{gone}");
    }

    let limitations = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../LIMITATIONS.md"),
    )
    .expect("read LIMITATIONS.md");
    const MARKER: &str = "The AArch64 encoder does not check arity.";
    let start = limitations
        .find(MARKER)
        .expect("LIMITATIONS.md must disclose the ignored trailing operands");
    let paragraph = &limitations[start..];
    let paragraph = &paragraph[..paragraph.find("\n\n").unwrap_or(paragraph.len())];
    let named: Vec<&str> = paragraph
        .split('`')
        .skip(1)
        .step_by(2)
        .filter(|token| {
            ALL_AARCH64_OPCODES
                .iter()
                .any(|op| format!("{op:?}") == *token)
        })
        .collect();
    let mut named_sorted = named.clone();
    named_sorted.sort_unstable();
    named_sorted.dedup();
    let mut expected: Vec<&str> = IGNORED_TRAILING_OPERAND.to_vec();
    expected.sort_unstable();
    assert_eq!(
        named_sorted, expected,
        "LIMITATIONS.md must name exactly these opcodes"
    );
    let stated = format!("{} opcodes", IGNORED_TRAILING_OPERAND.len());
    assert!(
        paragraph.contains(&stated),
        "LIMITATIONS.md must state `{stated}`"
    );
}

// ---------------------------------------------------------------------------
// E0.2: the coverage gate is an inventory, not a credit path
// ---------------------------------------------------------------------------

/// Occurrences of the coverage gate as CODE (a path or type use) in one Rust
/// source, one entry per use. Comments (line and block), string literals
/// (including multi-line and raw strings) and char literals are dropped first,
/// so a comment or message that says "mirrors coverage_gate" is not a use.
fn coverage_gate_code_uses(source: &str) -> Vec<String> {
    let chars: Vec<char> = source.chars().collect();
    let mut code = String::with_capacity(source.len());
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        let next = chars.get(i + 1).copied();
        if c == '/' && next == Some('/') {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
        } else if c == '/' && next == Some('*') {
            let mut depth = 0usize;
            while i < chars.len() {
                if chars[i] == '/' && chars.get(i + 1) == Some(&'*') {
                    depth += 1;
                    i += 2;
                } else if chars[i] == '*' && chars.get(i + 1) == Some(&'/') {
                    depth -= 1;
                    i += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    i += 1;
                }
            }
            code.push(' ');
        } else if c == 'r'
            && (next == Some('"') || next == Some('#'))
            && !code.ends_with(|p: char| p.is_ascii_alphanumeric() || p == '_')
        {
            let mut j = i + 1;
            let mut hashes = 0;
            while chars.get(j) == Some(&'#') {
                hashes += 1;
                j += 1;
            }
            if chars.get(j) == Some(&'"') {
                j += 1;
                'raw: while j < chars.len() {
                    if chars[j] == '"' && (1..=hashes).all(|k| chars.get(j + k) == Some(&'#')) {
                        j += 1 + hashes;
                        break 'raw;
                    }
                    j += 1;
                }
                code.push(' ');
                i = j;
            } else {
                code.push(c);
                i += 1;
            }
        } else if c == '"' {
            i += 1;
            while i < chars.len() && chars[i] != '"' {
                i += if chars[i] == '\\' { 2 } else { 1 };
            }
            i += 1;
            code.push(' ');
        } else if c == '\'' {
            // A char literal ('x', '\n', '\''), else a lifetime or label.
            if next == Some('\\') {
                let mut j = i + 2;
                while j < chars.len() && chars[j] != '\'' {
                    j += 1;
                }
                i = j + 1;
                code.push(' ');
            } else if chars.get(i + 2) == Some(&'\'') {
                i += 3;
                code.push(' ');
            } else {
                code.push(c);
                i += 1;
            }
        } else {
            code.push(c);
            i += 1;
        }
    }
    let is_ident = |c: char| c.is_ascii_alphanumeric() || c == '_';
    code.lines()
        .filter(|line| {
            line.split(|c: char| !is_ident(c))
                .any(|token| token == "coverage_gate" || token == "CoverageGate")
        })
        .map(|line| line.trim().to_string())
        .collect()
}

/// The gate still credits an opcode row when a registry theorem found by name
/// discharges, or when a REPRESENTATIVE reconstructed obligation discharges by
/// sampling. Since E0.2 neither is instruction credit, and the gate is safe to
/// keep only because nothing that decides promotion reads it: no crate other
/// than `trust-cg-verify` (the codegen promotion gates, the CLI, the rustc
/// bridge, the JIT) uses it as code. A promotion path that starts consulting
/// the gate must turn this red and face the E0.2 decision explicitly.
#[test]
fn coverage_gate_is_not_consulted_by_any_promotion_crate() {
    // The scanner itself must see each use and ignore each kind of mention.
    let probe = [
        "use trust_cg_verify::coverage_gate::CoverageGate;",
        "let g = trust_cg_verify::coverage_gate::CoverageGate::new();",
        "// mirrors coverage_gate discharge_one",
        "/* coverage_gate */ let q = '\"';",
        "let s = \"(mirrors coverage_gate\\",
        "    discharge_one; CoverageGate)\";",
        "let r = r#\"coverage_gate \"quoted\" CoverageGate\"#;",
        "let t: &'static str = \"\\\"CoverageGate\";",
    ]
    .join("\n");
    assert_eq!(
        coverage_gate_code_uses(&probe),
        vec![
            "use trust_cg_verify::coverage_gate::CoverageGate;".to_string(),
            "let g = trust_cg_verify::coverage_gate::CoverageGate::new();".to_string(),
        ]
    );

    let crates = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates/ directory");
    let mut scanned = 0usize;
    let mut offenders = Vec::new();
    let mut stack = Vec::new();
    for entry in std::fs::read_dir(crates).expect("read crates/") {
        let path = entry.expect("crate entry").path();
        if path
            .file_name()
            .is_some_and(|name| name == "trust-cg-verify")
        {
            continue;
        }
        let src = path.join("src");
        if src.is_dir() {
            stack.push(src);
        }
    }
    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(&dir).expect("read source dir") {
            let path = entry.expect("source entry").path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|ext| ext == "rs") {
                let source = std::fs::read_to_string(&path).expect("read source");
                scanned += 1;
                for line in coverage_gate_code_uses(&source) {
                    offenders.push(format!("{}: {line}", path.display()));
                }
            }
        }
    }
    // The workspace has ~480 production sources outside the verifier;
    // a tiny count means the walk found the wrong directory.
    assert!(scanned > 400, "scanned only {scanned} source files");
    assert!(
        offenders.is_empty(),
        "a promotion crate now uses the opcode coverage gate, whose rows are \
         not instruction credit (E0.2):\n{}",
        offenders.join("\n")
    );
}

/// The eight CRC32 rows are covered only through the CRC32 family's credit
/// hook (L04-P1): an injected failing hook turns each row RED
/// (`ProofNotDischarged`), never a quiet deferral, and the real hook credits
/// every form with its controls.
#[test]
fn crc32_rows_need_the_family_credit_and_a_failing_hook_is_red() {
    use trust_cg_verify::aarch64_crc32_proofs::{CRC32_OPCODES, crc32_credit};
    let gate = CoverageGate::new();
    let credit = crc32_credit().expect("the CRC32 family holds");
    assert_eq!(credit.forms, 8);
    assert!(credit.controls_refuted >= 8 * 40, "{credit:?}");
    for op in CRC32_OPCODES {
        assert_eq!(classify_aarch64(op), OpcodeClass::EmittableNeedsProof);
        let real = gate.audit_aarch64_crc32_with(op, &crc32_credit);
        assert!(real.finding.is_none(), "{real:?}");
        let refused = gate.audit_aarch64_crc32_with(op, &|| Err("injected refusal".into()));
        assert!(
            matches!(
                refused.finding,
                Some(CoverageFinding::ProofNotDischarged { .. })
            ),
            "{refused:?}"
        );
    }
}

/// The `SubsRI` row is covered only through its decoded-word family's credit
/// hook (L04-P1): an injected failing hook turns it RED.
#[test]
fn subs_imm_row_needs_its_family_credit_and_a_failing_hook_is_red() {
    use trust_cg_verify::aarch64_subs_imm_proofs::subs_imm_credit;
    let gate = CoverageGate::new();
    let real = gate.audit_aarch64_subs_imm_with(&subs_imm_credit);
    assert!(real.finding.is_none(), "{real:?}");
    assert!(
        real.note.contains("SUBS #imm DECODED-WORD") && real.note.contains("NOT a formal proof"),
        "{}",
        real.note
    );
    let refused = gate.audit_aarch64_subs_imm_with(&|| Err("injected refusal".into()));
    assert!(
        matches!(
            refused.finding,
            Some(CoverageFinding::ProofNotDischarged { .. })
        ),
        "{refused:?}"
    );
}
