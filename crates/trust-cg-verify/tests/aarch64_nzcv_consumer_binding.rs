// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The NZCV-CONSUMER binding: which obligation a `CSET` or `CSEL` is BOUND to
//! — the one of the lowering it completes — through the REAL AArch64 selector.
//!
//! `opcode_to_proof_query` leaves both opcodes unmapped, and must: a generic
//! template establishes neither the instruction's condition, nor its carrier
//! width, nor its reaching flag producer. The walk's in-block source-bound
//! binding (`FunctionVerifier::NZCV_CONSUMER_ARMS`) establishes those three
//! plus the TV-1 stamped SOURCE CLASS, and fails closed when any one is
//! missing. These tests drive the production `InstructionSelector` so the
//! shapes under test are the ones the compiler actually emits, then assert the
//! inventory rows.
//!
//! NOTHING HERE IS CREDITED. Since E0.2 (`8d4e83b54`, "a registry name lookup
//! and a sampled discharge are not proof credit") the walk turns EVERY
//! in-block query hit into `withdrawn_registry_credit`: the row is
//! `Unverified`, and its detail names the query the binding selected —
//! "no operand-exact evidence: registry name lookup is not proof credit: query
//! `icmp_eq_i32` in Comparison selects a theorem by name, not an obligation
//! built from this instruction". A theorem selected by name is not an
//! obligation built from this instruction, on any ISA, so no assertion in this
//! file claims `OpcodeInventoryStatus::Verified` for a CSET/CSEL row.
//!
//! What remains observable, and what these tests pin, is the BINDING:
//!
//! * BOUND to query `Q` (`assert_bound_to`): the row is `Unverified` and its
//!   detail is exactly that withdrawal naming `Q` — the whole query, never a
//!   substring another family member also contains.
//! * REFUSED (`assert_refused`): the row is `Unverified` and names no query at
//!   all ("no proof mapping for opcode CSet"). Every missing fact — condition,
//!   width, producer, source stamp, chain shape, arm wiring — still produces
//!   this, so every must-refute control below still separates its two cases.
//!
//! For a source-bound class (an `IntCmp`/`Overflow`-stamped `CSET`, a
//! `Select`/`Shift`-stamped `CSEL`) the source-bound binding DECIDES whether a
//! query is named at all, and the name kept is the machine-level
//! reaching-producer binding's (`flag_consumer_query`) whenever that has one.
//! For a `CSET` the two agree (`icmp_<cond>_i<w>`, `checked<op>_i64`). For a
//! `CSEL` they do not: the refusal names the machine-level `a64 nzcv csel ...`
//! form, so what the source-bound binding ITSELF selected (`select_<cond>_...`,
//! `<direction>_i128`) is read from the published arm table
//! (`source_bound_selections`).
//!
//! Test names that say "credit"/"credited" predate the withdrawal; read them
//! as "bind"/"bound".
//!
//! What is NOT claimed here: that any named obligation is discharged or
//! credited, nor anything about `CSINC`/`CSINV`/`CSNEG`/`FCSEL`, which the
//! source-bound binding does not reach and which are pinned so below.

use trust_cg_ir::{AArch64Opcode, LoweringProvenance, MachFunction, TrustIrInstId};
use trust_cg_lower::Type;
use trust_cg_lower::abi::AArch64AbiVariant;
use trust_cg_lower::function::{BasicBlock, Function, Signature};
use trust_cg_lower::instructions::{Block, Instruction, IntCC, Opcode, Value};
use trust_cg_lower::isel::InstructionSelector;
use trust_cg_verify::aarch64_flag_consumer_proofs::{
    ProducerForm, ProducerKind, SelectForm, SelectOp,
};
use trust_cg_verify::function_verifier::{
    FunctionVerifier, InstructionOpcode, OpcodeInventoryStatus, REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT,
};
use trust_cg_verify::proof_database::ProofCategory;
use trust_cg_verify::provenance_xcheck::{LirSourceIndex, ProvenanceXCheckMode};

const ALL_CONDITIONS: [IntCC; 10] = [
    IntCC::Equal,
    IntCC::NotEqual,
    IntCC::SignedLessThan,
    IntCC::SignedGreaterThanOrEqual,
    IntCC::SignedGreaterThan,
    IntCC::SignedLessThanOrEqual,
    IntCC::UnsignedLessThan,
    IntCC::UnsignedGreaterThanOrEqual,
    IntCC::UnsignedGreaterThan,
    IntCC::UnsignedLessThanOrEqual,
];

/// Mirror the production raw-selection setup (same seeders as
/// `aarch64_affine_lowering.rs`, so immediate/constant folding behaves as it
/// does in a real compile).
fn select(function: &Function) -> MachFunction {
    let mut selector = InstructionSelector::new(function.name.clone(), function.signature.clone());
    selector.set_abi_variant(AArch64AbiVariant::Darwin);
    selector.set_stack_slots(function.stack_slots.clone());
    selector.seed_value_types(&function.value_types);
    selector.seed_iconst_origins(
        function
            .blocks
            .values()
            .map(|block| block.instructions.as_slice()),
    );
    selector.seed_function_value_use_counts(function);
    selector
        .lower_formal_arguments(&function.signature, function.entry_block)
        .expect("fixture formal arguments must lower");
    for id in function.layout_order() {
        let block = &function.blocks[&id];
        selector
            .select_block_with_provenance(
                id,
                &block.instructions,
                &block.source_locs,
                &function.trust_ir_origins[&id],
            )
            .expect("fixture body must lower");
    }
    selector
        .finalize_with_eh_info(&function.eh_info)
        .expect("fixture EH metadata must match")
        .to_ir_func()
}

/// A single-block LIR function with `params` parameters of type `param_ty`,
/// the given body, and a return of `returned` at `return_ty`.
fn source_function(
    name: &str,
    param_tys: Vec<Type>,
    mut instructions: Vec<Instruction>,
    returned: u32,
    return_ty: Type,
    extra_types: Vec<(u32, Type)>,
) -> Function {
    let signature = Signature {
        params: param_tys.clone(),
        returns: vec![return_ty],
    };
    let mut function = Function::new(name, signature);
    let params: Vec<_> = param_tys
        .iter()
        .enumerate()
        .map(|(index, ty)| (Value(index as u32), ty.clone()))
        .collect();
    function.value_types.extend(params.iter().cloned());
    for (value, ty) in extra_types {
        function.value_types.insert(Value(value), ty);
    }
    instructions.push(Instruction {
        opcode: Opcode::Return,
        args: vec![Value(returned)],
        results: vec![],
    });
    function.trust_ir_origins.insert(
        Block(0),
        (0..instructions.len())
            .map(|index| Some(TrustIrInstId(40 + index as u32)))
            .collect(),
    );
    function.blocks.insert(
        Block(0),
        BasicBlock {
            params,
            source_locs: vec![None; instructions.len()],
            instructions,
        },
    );
    function.block_order.push(Block(0));
    function
}

/// `fn(a: ty, b: ty) -> b1 { icmp cond a, b }` — the canonical `CMP ; CSET`.
fn icmp_function(ty: Type, cond: IntCC) -> Function {
    source_function(
        "icmp_fixture",
        vec![ty.clone(), ty.clone()],
        vec![Instruction {
            opcode: Opcode::Icmp { cond },
            args: vec![Value(0), Value(1)],
            results: vec![Value(10)],
        }],
        10,
        Type::B1,
        vec![(10, Type::B1)],
    )
}

/// `fn(a: ty, b: ty) -> b1 { (_v, ov) = <checked> a, b; ov }` —
/// `ADDS/SUBS ; CSET <VS|HS|LO>`. The overflow bit is returned so the CSET
/// that materializes it is live.
fn checked_function(ty: Type, opcode: Opcode) -> Function {
    source_function(
        "checked_fixture",
        vec![ty.clone(), ty.clone()],
        vec![Instruction {
            opcode,
            args: vec![Value(0), Value(1)],
            results: vec![Value(10), Value(11)],
        }],
        11,
        Type::B1,
        vec![(10, ty), (11, Type::B1)],
    )
}

/// `fn(c: b1, t: ty, f: ty) -> ty { select cond c, t, f }` — `CMP ; CSEL`.
fn select_function(ty: Type, cond: IntCC) -> Function {
    source_function(
        "select_fixture",
        vec![Type::B1, ty.clone(), ty.clone()],
        vec![Instruction {
            opcode: Opcode::Select { cond },
            args: vec![Value(0), Value(1), Value(2)],
            results: vec![Value(10)],
        }],
        10,
        ty.clone(),
        vec![(10, ty)],
    )
}

/// Inventory rows for `opcode`, as `(status, detail)`.
fn rows_for(
    machine: &MachFunction,
    lir: &Function,
    opcode: AArch64Opcode,
) -> Vec<(OpcodeInventoryStatus, String)> {
    let verifier = FunctionVerifier::new();
    let report =
        verifier.verify_with_lir_source_and_mode(machine, Some(lir), ProvenanceXCheckMode::Enforce);
    assert!(
        report.precondition_failure.is_none(),
        "{:?}",
        report.precondition_failure
    );
    report
        .emitted_opcode_inventory()
        .entries
        .into_iter()
        .filter(|entry| entry.opcode == InstructionOpcode::AArch64(opcode))
        .map(|entry| (entry.status, entry.detail))
        .collect()
}

/// The proof names that describe a whole LOWERED SEQUENCE — the comparison or
/// the checked-arithmetic idiom a `CSET` completes. Binding one of these to a
/// consumer whose reaching flag producer is not what the theorem names is the
/// unfaithful inheritance #62 retracted, so the negative tests below assert
/// that a refused row names NONE of them, separately from its status.
fn is_sequence_citation(name: &str) -> bool {
    let lowered = name.to_lowercase();
    ["icmp_", "checked", "select_", "condbr", "tst "]
        .iter()
        .any(|prefix| lowered.contains(prefix))
}

/// The DECODED-WORD `CSET` row: the weaker per-instruction claim. It states
/// only that the emitted word materialises its own condition as 0/1 in its own
/// destination, over all sixteen NZCV states — nothing about a reaching
/// producer or a source operation. It is a registered, discharged obligation
/// with NO promotion authority, so the negative tests below assert that it is
/// not cited either: an uncovered CSET must stay uncovered, not be downgraded
/// to a partial claim promoted as a whole one.
fn is_decoded_word_citation(name: &str) -> bool {
    name.starts_with("A64 decoded CSET ")
}

/// The `(query, category)` a row's detail NAMES, when it names one.
///
/// Since E0.2 an in-block binding hit is never credit: the walk writes
/// `withdrawn_registry_credit(query, category)`, whose detail is EXACTLY
/// "`REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT`: query \`Q\` in C selects a theorem by
/// name, not an obligation built from this instruction". Only a detail of
/// exactly that shape yields `Some`; a binding refusal ("no proof mapping for
/// opcode CSet") or any other reason names no query.
fn withdrawn_query(detail: &str) -> Option<(&str, &str)> {
    let rest = detail
        .strip_prefix(REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT)?
        .strip_prefix(": query `")?;
    let (query, rest) = rest.split_once('`')?;
    let category = rest.strip_prefix(" in ")?.strip_suffix(
        " selects a theorem by name, not an obligation built from this instruction",
    )?;
    Some((query, category))
}

/// BOUND to `query`: the merged-tree meaning of what this file asserted as
/// "credited to `query`" before E0.2. The row is NOT credited (`Unverified`),
/// and its detail is the withdrawal naming EXACTLY `query` in `category` —
/// whole-string equality, so `icmp_eq_i32` never matches `icmp_eq_i64`, nor a
/// CSEL form for `hs` one for `hi`.
fn assert_bound_to(
    row: &(OpcodeInventoryStatus, String),
    query: &str,
    category: ProofCategory,
    what: &str,
) {
    let (status, detail) = row;
    assert_eq!(
        *status,
        OpcodeInventoryStatus::Unverified,
        "{what}: a CSET/CSEL row was credited, but registry-name credit is withdrawn: {detail}"
    );
    assert_eq!(
        withdrawn_query(detail),
        Some((query, category.name())),
        "{what}: expected the binding to select `{query}` in {}, the row says: {detail}",
        category.name()
    );
}

/// Whether the row is REFUSED: not credited, and its detail names no query —
/// the binding selected nothing.
fn is_refused(row: &(OpcodeInventoryStatus, String)) -> bool {
    row.0 == OpcodeInventoryStatus::Unverified && withdrawn_query(&row.1).is_none()
}

/// Whether the row is BOUND to some query (see [`assert_bound_to`]).
fn is_bound(row: &(OpcodeInventoryStatus, String)) -> bool {
    row.0 == OpcodeInventoryStatus::Unverified && withdrawn_query(&row.1).is_some()
}

/// REFUSED, asserted (see [`is_refused`]).
fn assert_refused(row: &(OpcodeInventoryStatus, String), what: &str) {
    let (status, detail) = row;
    assert_eq!(
        *status,
        OpcodeInventoryStatus::Unverified,
        "{what}: credited: {detail}"
    );
    assert!(
        withdrawn_query(detail).is_none(),
        "{what}: expected the binding to refuse, but it selected a query: {detail}"
    );
}

/// What the SOURCE-BOUND binding itself selects for every `opcode` instruction,
/// in walk order: `FunctionVerifier::NZCV_CONSUMER_ARMS` run in order — which
/// is exactly `nzcv_consumer_source_bound_query` (`nzcv_consumer_arm_order_is_
/// pinned`) — with the replayed-LIR source the walk hands it.
///
/// Needed for a `CSEL`, whose refusal names the machine-level
/// `a64 nzcv csel ...` form and therefore cannot show which `Select_*` member
/// or which i128 shift DIRECTION the source-bound binding selected.
fn source_bound_selections(
    machine: &MachFunction,
    lir: &Function,
    opcode: AArch64Opcode,
) -> Vec<Option<&'static str>> {
    let index = LirSourceIndex::build(lir);
    let mut selected = Vec::new();
    for block in &machine.blocks {
        for (block_pos, &inst_id) in block.insts.iter().enumerate() {
            let inst = &machine.insts[inst_id.0 as usize];
            if inst.opcode != opcode {
                continue;
            }
            let source = match machine.inst_lowering_provenance(inst_id) {
                LoweringProvenance::SourceInst { id, .. } => index.get(id),
                _ => None,
            };
            selected.push(
                FunctionVerifier::NZCV_CONSUMER_ARMS
                    .iter()
                    .find_map(|(_, arm)| arm(machine, &block.insts, block_pos, inst, source))
                    .map(|(query, _)| query),
            );
        }
    }
    selected
}

/// The registry's trust-ir spelling of each integer condition (`Icmp_<c>_*`,
/// `Select_<c>_*`), keyed by the AArch64 condition immediate that denotes it.
/// `MI`/`PL`/`VS`/`VC` have none.
const INTEGER_CONDITION_SPELLINGS: [(i64, &str); 10] = [
    (0, "eq"),
    (1, "ne"),
    (2, "uge"),
    (3, "ult"),
    (8, "ugt"),
    (9, "ule"),
    (10, "sge"),
    (11, "slt"),
    (12, "sgt"),
    (13, "sle"),
];

/// The trust-ir spelling of the integer condition `cc` denotes.
fn condition_spelling(cc: i64) -> &'static str {
    INTEGER_CONDITION_SPELLINGS
        .iter()
        .find(|(code, _)| *code == cc)
        .unwrap_or_else(|| panic!("cc {cc} has no integer-comparison spelling"))
        .1
}

/// The condition immediate a correct SCALAR lowering of `cond` carries
/// (`from_intcc`) — the test's own statement, independent of the selector.
fn scalar_cc(cond: IntCC) -> i64 {
    match cond {
        IntCC::Equal => 0,
        IntCC::NotEqual => 1,
        IntCC::UnsignedGreaterThanOrEqual => 2,
        IntCC::UnsignedLessThan => 3,
        IntCC::UnsignedGreaterThan => 8,
        IntCC::UnsignedLessThanOrEqual => 9,
        IntCC::SignedGreaterThanOrEqual => 10,
        IntCC::SignedLessThan => 11,
        IntCC::SignedGreaterThan => 12,
        IntCC::SignedLessThanOrEqual => 13,
    }
}

/// The machine-level query of a plain `CSEL` of `sel_width` reached by an
/// integer `CMP` of `cmp_width` with condition `cc` — the name a bound `CSEL`
/// row's refusal carries.
fn csel_form_query(sel_width: u32, cmp_width: u32, cc: i64) -> &'static str {
    SelectForm {
        op: SelectOp::Csel,
        width: sel_width,
        producer: ProducerForm::new(ProducerKind::Cmp, cmp_width),
        cond: u8::try_from(cc).expect("condition immediate fits a byte"),
    }
    .query()
}

// ---------------------------------------------------------------------------
// POSITIVE: the binding fires on what the compiler really emits
// ---------------------------------------------------------------------------

/// Every integer comparison the selector lowers as `CMP ; CSET` has its CSET
/// BOUND to the SAME `Icmp_<cond>_I<w> -> CMP+CSET_<cc>` family member as the
/// CMP half of the pair — this source's own condition and the reaching
/// comparison's own width, not a representative. The query is named in the
/// withdrawal, not credited; that each `icmp_<cond>_<width>` query resolves to
/// its own `Icmp_*` (CMP+CSET) row is pinned by
/// `select_family_registration_does_not_shadow_the_comparison_families`.
#[test]
fn every_lowered_icmp_credits_its_cset_to_its_own_family_member() {
    let mut checked = 0;
    for ty in [Type::I32, Type::I64] {
        for cond in ALL_CONDITIONS {
            let lir = icmp_function(ty.clone(), cond);
            let machine = select(&lir);
            let rows = rows_for(&machine, &lir, AArch64Opcode::CSet);
            assert_eq!(rows.len(), 1, "{ty:?} {cond:?}: expected exactly one CSET");
            let width = if ty == Type::I32 { "i32" } else { "i64" };
            let query = format!("icmp_{}_{width}", condition_spelling(scalar_cc(cond)));
            assert_bound_to(
                &rows[0],
                &query,
                ProofCategory::Comparison,
                &format!("{ty:?} {cond:?}"),
            );
            checked += 1;
        }
    }
    assert_eq!(checked, 20);
}

/// Every scalar select the selector lowers as `CMP ; CSEL` has its CSEL bound
/// to its own condition's member at both levels. The source-bound binding
/// selects the faithful `Select_<cond>_Nzcv<w>_Sel<w> -> CSEL_<cc>` member;
/// the refusal names the machine-level `CSEL` form it gates, for the same
/// condition, select width and reaching `CMP` (the fixture's boolean operand is
/// compared as `CMP Xc, #0`, so that producer is 64-bit at both select widths).
#[test]
fn every_lowered_select_credits_its_csel_to_its_own_family_member() {
    let mut checked = 0;
    for ty in [Type::I32, Type::I64] {
        for cond in ALL_CONDITIONS {
            let lir = select_function(ty.clone(), cond);
            let machine = select(&lir);
            let rows = rows_for(&machine, &lir, AArch64Opcode::Csel);
            assert!(!rows.is_empty(), "{ty:?} {cond:?}: no CSEL was emitted");
            let sel_width = if ty == Type::I32 { 32 } else { 64 };
            let cc = scalar_cc(cond);
            for row in &rows {
                assert_bound_to(
                    row,
                    csel_form_query(sel_width, 64, cc),
                    ProofCategory::Comparison,
                    &format!("{ty:?} {cond:?}"),
                );
            }
            let family = format!("select_{}_nzcv64_sel{sel_width}", condition_spelling(cc));
            let selected = source_bound_selections(&machine, &lir, AArch64Opcode::Csel);
            assert_eq!(selected.len(), rows.len());
            for query in selected {
                assert_eq!(
                    query,
                    Some(family.as_str()),
                    "{ty:?} {cond:?}: the source-bound binding did not select `{family}`"
                );
            }
            checked += 1;
        }
    }
    assert_eq!(checked, 20);
}

/// The `CSET` that materializes a checked add/sub overflow bit is bound to the
/// `Checked*_I64` obligation whose theorem NAMES it (`CheckedSadd_I64 ->
/// ADDS+CSET_VS`, `CheckedUsub_I64 -> SUBS+CSET_LO`, ...), and the SOURCE picks
/// SIGNED vs UNSIGNED — the per-block refinement the opcode-level
/// `AddsRR`/`SubsRR` arms say they cannot make.
#[test]
fn checked_add_sub_csets_cite_the_obligation_that_names_them() {
    let cases = [
        (Opcode::CheckedSadd, "checkedsadd_i64"),
        (Opcode::CheckedUadd, "checkeduadd_i64"),
        (Opcode::CheckedSsub, "checkedssub_i64"),
        (Opcode::CheckedUsub, "checkedusub_i64"),
    ];
    let mut checked = 0;
    for (opcode, token) in cases {
        let lir = checked_function(Type::I64, opcode.clone());
        let rows = rows_for(&select(&lir), &lir, AArch64Opcode::CSet);
        assert_eq!(rows.len(), 1, "{opcode:?}: expected exactly one CSET");
        assert_bound_to(
            &rows[0],
            token,
            ProofCategory::Arithmetic,
            &format!("{opcode:?} overflow CSET"),
        );
        checked += 1;
    }
    assert_eq!(checked, 4);
}

/// The signed and unsigned members of the SAME producer opcode must cite
/// DIFFERENT obligations. `ADDS` serves both `CheckedSadd` (V flag) and
/// `CheckedUadd` (C flag); if the condition were not observed, both would land
/// on one theorem — which is the whole reason the opcode-level arm defers this
/// to a per-block refinement.
#[test]
fn the_condition_separates_signed_from_unsigned_overflow() {
    let cite = |opcode| {
        let lir = checked_function(Type::I64, opcode);
        rows_for(&select(&lir), &lir, AArch64Opcode::CSet)[0]
            .1
            .clone()
    };
    assert_ne!(
        cite(Opcode::CheckedSadd),
        cite(Opcode::CheckedUadd),
        "signed and unsigned ADDS overflow cited the same obligation"
    );
    assert_ne!(
        cite(Opcode::CheckedSsub),
        cite(Opcode::CheckedUsub),
        "signed and unsigned SUBS overflow cited the same obligation"
    );
}

/// There is no `Checked*_I32` obligation, so a 32-bit checked add/sub must
/// earn nothing rather than inherit the 64-bit theorem — the #62
/// unfaithful-inheritance rule, applied to width.
#[test]
fn a_narrow_checked_overflow_cset_does_not_inherit_the_64_bit_theorem() {
    for opcode in [
        Opcode::CheckedSadd,
        Opcode::CheckedUadd,
        Opcode::CheckedSsub,
        Opcode::CheckedUsub,
    ] {
        let lir = checked_function(Type::I32, opcode.clone());
        let Ok(machine) = std::panic::catch_unwind(|| select(&lir)) else {
            // A 32-bit checked op the selector refuses to lower is not a case
            // this binding can be wrong about.
            continue;
        };
        for (status, detail) in rows_for(&machine, &lir, AArch64Opcode::CSet) {
            // The original assertion, UNWEAKENED, plus two strictly stronger
            // ones: no whole-sequence theorem is inherited at I32, AND the row
            // is not downgraded to the decoded-word claim either. (The
            // decoded-word CSET family exists and is discharged, but it has no
            // promotion authority — see the block comment in
            // `function_verifier`.)
            assert!(
                !is_sequence_citation(&detail),
                "{opcode:?} at I32 inherited a 64-bit theorem: {detail}"
            );
            assert!(
                !is_decoded_word_citation(&detail),
                "{opcode:?} at I32 was credited the decoded-word row: {detail}"
            );
            assert_eq!(
                status,
                OpcodeInventoryStatus::Unverified,
                "{opcode:?} at I32 inherited a 64-bit theorem: {detail}"
            );
        }
    }
}

/// An i128 comparison is lowered as a SEQUENCE of 64-bit limb comparisons
/// (`CMP hi ; CSET EQ ; CMP lo ; CSET EQ ; AND`, and the signed/unsigned
/// three-CSET shape), and each limb `CSET` is bound to the 64-bit theorem for
/// ITS OWN reaching `CMP` and condition — never to a 128-bit one, and never to
/// a theorem for a different condition.
///
/// This is deliberate and it is worth stating why it is not the #62
/// unfaithful-inheritance hazard. #62 was about crediting a theorem that is
/// FALSE of the instruction — a narrow `SWP` credited to the 32-bit theorem
/// claims a 4-byte store where one byte happens. Here `Icmp_Eq_I64 ->
/// CMP+CSET_EQ` is TRUE of the pair it is bound to: those two instructions do
/// compute the 64-bit equality of that limb. What the row does NOT claim is
/// that the FUNCTION implements the i128 predicate; assembling the limbs is
/// the surrounding `AND`/`ORR`/`CSEL`'s own coverage question, and those rows
/// answer it separately. The binding is width- and condition-exact, which is
/// strictly more precise than the opcode-level `"cmp"` token the `CMP`
/// instructions in the same idiom reach.
#[test]
fn i128_limb_csets_cite_their_own_limb_theorem() {
    use trust_cg_ir::MachOperand;
    let mut seen_multi = 0;
    for cond in ALL_CONDITIONS {
        let lir = icmp_function(Type::I128, cond);
        let machine = select(&lir);
        let rows = rows_for(&machine, &lir, AArch64Opcode::CSet);
        assert!(!rows.is_empty(), "{cond:?}: no CSET was emitted");
        if rows.len() > 1 {
            seen_multi += 1;
        }
        // Each limb CSET's OWN condition, in the walk's (and so the
        // inventory's) order.
        let limb_ccs: Vec<i64> = machine
            .blocks
            .iter()
            .flat_map(|block| block.insts.iter())
            .map(|id| &machine.insts[id.0 as usize])
            .filter(|inst| inst.opcode == AArch64Opcode::CSet)
            .map(|inst| match inst.operands[1] {
                MachOperand::Imm(cc) => cc,
                ref other => panic!("CSET condition is {other:?}"),
            })
            .collect();
        assert_eq!(rows.len(), limb_ccs.len(), "{cond:?}: rows vs CSETs");
        for (row, cc) in rows.iter().zip(&limb_ccs) {
            let query = format!("icmp_{}_i64", condition_spelling(*cc));
            assert_bound_to(
                row,
                &query,
                ProofCategory::Comparison,
                &format!("{cond:?} limb cc {cc}"),
            );
            // Every limb comparison is 64-bit: an i128 CSET must never be bound
            // to a 32-bit member, and there is no 128-bit member to bind.
            let named = withdrawn_query(&row.1).map_or("", |(query, _)| query);
            assert!(
                named.contains("i64"),
                "{cond:?}: limb binding `{}` is not the 64-bit theorem",
                row.1
            );
            assert!(
                !named.contains("i32") && !named.contains("i128"),
                "{cond:?}: limb binding `{}` names the wrong width",
                row.1
            );
        }
    }
    assert!(
        seen_multi > 0,
        "no i128 condition lowered to a multi-limb CSET sequence — \
         the fixture no longer exercises the case this pins"
    );
}

/// The CSET's carrier width is the REACHING COMPARISON's, not the
/// destination's: ISel always picks the X-form CSET ("regardless of whether
/// the reaching CMP uses W or X operands"), so reading the width off the
/// destination would bind every 32-bit comparison to the 64-bit theorem.
#[test]
fn cset_width_follows_the_comparison_not_the_destination() {
    let i32_lir = icmp_function(Type::I32, IntCC::SignedLessThan);
    let i32_detail = rows_for(&select(&i32_lir), &i32_lir, AArch64Opcode::CSet)[0]
        .1
        .to_lowercase();
    let i64_lir = icmp_function(Type::I64, IntCC::SignedLessThan);
    let i64_detail = rows_for(&select(&i64_lir), &i64_lir, AArch64Opcode::CSet)[0]
        .1
        .to_lowercase();
    assert!(i32_detail.contains("i32"), "{i32_detail}");
    assert!(i64_detail.contains("i64"), "{i64_detail}");
    assert_ne!(
        i32_detail, i64_detail,
        "both widths cited the same obligation — the width is not observed"
    );
}

// ---------------------------------------------------------------------------
// NEGATIVE: every missing fact fails closed
// ---------------------------------------------------------------------------

/// Without a replayed LIR there is no stamped source class, so the
/// source-bound binding never runs. This is the mode every direct-query and
/// pre-warm caller uses, and it must keep earning nothing.
///
/// What such a row NAMES on this tree is the machine-level reaching-producer
/// binding's query (`flag_consumer_query`), which reads only the emitted
/// instruction and its block and so needs no provenance: a `CMP ; CSET` names
/// its `icmp_<cond>_i<w>` member inside the withdrawal. That is not credit, but
/// it makes this file's original "no sequence theorem is named" assertion
/// FALSE for a `CSET` here, for a reason that is not this binding. It is kept
/// verbatim for the `CSEL`, where the source-bound `Select_*` member still
/// never appears; for the `CSET` it is restated as "the only sequence name is
/// this comparison's own machine-level member, inside the withdrawal".
#[test]
fn no_provenance_means_no_credit() {
    let verifier = FunctionVerifier::new();
    for ty in [Type::I32, Type::I64] {
        for cond in ALL_CONDITIONS {
            for (lir, opcode) in [
                (icmp_function(ty.clone(), cond), AArch64Opcode::CSet),
                (select_function(ty.clone(), cond), AArch64Opcode::Csel),
            ] {
                let machine = select(&lir);
                // `Off` builds no LIR index at all.
                let report = verifier.verify_with_lir_source_and_mode(
                    &machine,
                    Some(&lir),
                    ProvenanceXCheckMode::Off,
                );
                for entry in report.emitted_opcode_inventory().entries {
                    if entry.opcode != InstructionOpcode::AArch64(opcode) {
                        continue;
                    }
                    let row = (entry.status, entry.detail);
                    // With no replayed LIR there is no source instruction at
                    // all, so no binding can establish which source operation
                    // the instruction completes or whether its condition is
                    // the right one — and the decoded-word row, which needs no
                    // provenance precisely because it makes no claim about a
                    // source, must therefore not be named either.
                    assert!(
                        !is_decoded_word_citation(&row.1),
                        "{opcode:?} was credited the decoded-word row without \
                         provenance: {}",
                        row.1
                    );
                    assert_eq!(
                        row.0,
                        OpcodeInventoryStatus::Unverified,
                        "{opcode:?} was credited without provenance: {}",
                        row.1
                    );
                    if opcode == AArch64Opcode::Csel {
                        // The original assertion, UNWEAKENED.
                        assert!(
                            !is_sequence_citation(&row.1),
                            "{opcode:?} was credited a sequence theorem without provenance: {}",
                            row.1
                        );
                    } else {
                        let width = if ty == Type::I32 { "i32" } else { "i64" };
                        assert_bound_to(
                            &row,
                            &format!("icmp_{}_{width}", condition_spelling(scalar_cc(cond))),
                            ProofCategory::Comparison,
                            &format!("{ty:?} {cond:?} CSET without provenance"),
                        );
                    }
                }
            }
        }
    }
}

/// The three encoding-family siblings compute DIFFERENT false arms (+1, NOT,
/// NEG) and have no obligation here. `CSINV` in particular is the codebase's
/// canonical uncovered-opcode fixture: a family-wide arm would silently
/// promote it.
#[test]
fn the_conditional_select_siblings_are_not_credited() {
    use trust_cg_ir::aarch64_regs::{X0, X1, X2};
    use trust_cg_ir::{MachInst, MachOperand};
    // A real `CMP ; <sibling>` window: the reaching producer and the condition
    // are both present, so only the per-opcode binding keeps these red.
    let lir = select_function(Type::I64, IntCC::NotEqual);
    let mut machine = select(&lir);
    let insts = machine.insts.clone();
    let csel_index = insts
        .iter()
        .position(|i| i.opcode == AArch64Opcode::Csel)
        .expect("the fixture lowers to a CSEL");
    let cc = insts[csel_index].operands[3].clone();
    for sibling in [
        AArch64Opcode::Csinc,
        AArch64Opcode::Csinv,
        AArch64Opcode::Csneg,
    ] {
        machine.insts[csel_index] = MachInst::new(
            sibling,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
                cc.clone(),
            ],
        );
        for (status, detail) in rows_for(&machine, &lir, sibling) {
            assert_eq!(
                status,
                OpcodeInventoryStatus::Unverified,
                "{sibling:?} inherited the CSEL binding: {detail}"
            );
        }
    }
}

/// A `CSET` whose reaching flag producer is not an integer `CMP` earns
/// nothing: an `Fcmp`'s NZCV is an FP relation, a `Tst` clears C and V, and an
/// `AddsRR`/`SubsRR`'s flags belong to a checked-arithmetic idiom. Crediting
/// an integer comparison theorem against any of them is exactly the
/// unfaithful inheritance #62 retracted.
#[test]
fn a_non_cmp_flag_producer_earns_the_consumer_nothing() {
    use trust_cg_ir::aarch64_regs::{D0, D1, X0, X1};
    use trust_cg_ir::{MachInst, MachOperand};
    let lir = icmp_function(Type::I64, IntCC::Equal);
    let base = select(&lir);
    let cmp_index = base
        .insts
        .iter()
        .position(|i| {
            matches!(
                i.opcode,
                AArch64Opcode::CmpRR | AArch64Opcode::CmpRI | AArch64Opcode::CMPXrr
            )
        })
        .expect("the fixture lowers to a CMP");
    let mut checked = 0;
    for producer in [
        MachInst::new(
            AArch64Opcode::Fcmp,
            vec![MachOperand::PReg(D0), MachOperand::PReg(D1)],
        ),
        MachInst::new(
            AArch64Opcode::Tst,
            vec![MachOperand::PReg(X0), MachOperand::PReg(X1)],
        ),
        MachInst::new(
            AArch64Opcode::AddsRR,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
            ],
        ),
        MachInst::new(
            AArch64Opcode::SubsRR,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
            ],
        ),
    ] {
        let mut machine = base.clone();
        machine.insts[cmp_index] = producer.clone();
        for (status, detail) in rows_for(&machine, &lir, AArch64Opcode::CSet) {
            // The original assertion, UNWEAKENED, plus two strictly stronger
            // ones. The REACHING FLAG PRODUCER is the third of the three facts
            // this codebase's own `CSet` refusal names, and a decoded-word row
            // says nothing about it — so an unattested producer must leave the
            // row uncovered rather than moving it to a claim that quantifies
            // over every NZCV state and therefore cannot be wrong about any
            // producer.
            assert!(
                !is_sequence_citation(&detail),
                "a {:?} flag producer credited the CSET a sequence theorem: {detail}",
                producer.opcode
            );
            assert!(
                !is_decoded_word_citation(&detail),
                "a {:?} flag producer credited the CSET the decoded-word row: {detail}",
                producer.opcode
            );
            assert_eq!(
                status,
                OpcodeInventoryStatus::Unverified,
                "a {:?} flag producer credited the CSET: {detail}",
                producer.opcode
            );
        }
        checked += 1;
    }
    assert_eq!(checked, 4);
}

/// With the reaching `CMP` replaced by a `Nop`, the flags are live-IN from a
/// predecessor. Cross-block flag provenance is not established by this
/// binding, so the consumer earns nothing.
#[test]
fn a_consumer_with_no_in_block_producer_earns_nothing() {
    use trust_cg_ir::MachInst;
    let lir = icmp_function(Type::I32, IntCC::UnsignedGreaterThan);
    let mut machine = select(&lir);
    let cmp_index = machine
        .insts
        .iter()
        .position(|i| {
            matches!(
                i.opcode,
                AArch64Opcode::CmpRR | AArch64Opcode::CmpRI | AArch64Opcode::CMPWrr
            )
        })
        .expect("the fixture lowers to a CMP");
    machine.insts[cmp_index] = MachInst::new(AArch64Opcode::Nop, vec![]);
    for (status, detail) in rows_for(&machine, &lir, AArch64Opcode::CSet) {
        // The original assertion, UNWEAKENED, plus two strictly stronger ones;
        // see the note in `a_non_cmp_flag_producer_earns_the_consumer_nothing`.
        // Cross-block flag provenance is still NOT established.
        assert!(
            !is_sequence_citation(&detail),
            "a CSET with no in-block producer was credited a sequence theorem: {detail}"
        );
        assert!(
            !is_decoded_word_citation(&detail),
            "a CSET with no in-block producer was credited the decoded-word row: {detail}"
        );
        assert_eq!(
            status,
            OpcodeInventoryStatus::Unverified,
            "a CSET with no in-block producer was credited: {detail}"
        );
    }
}

/// The `Select_*` family is registered in `ProofCategory::Comparison`, where
/// the walk resolves a query by the FIRST case-insensitive substring match.
/// Registering it must therefore not change what any PRE-EXISTING token
/// resolves to — in particular the opcode-level `"cmp"` token every
/// `CmpRR`/`CmpRI` reaches, whose name also contains "cmp". (Since E0.2 a
/// resolved token is named in a refusal, not credited; which row it names is
/// what this pins.)
#[test]
fn select_family_registration_does_not_shadow_the_comparison_families() {
    use trust_cg_verify::proof_database::{ProofCategory, ProofDatabase};
    let db = ProofDatabase::new();
    let first_containing = |token: &str| -> Option<String> {
        db.all()
            .iter()
            .filter(|p| p.category == ProofCategory::Comparison)
            .find(|p| p.obligation.name.to_lowercase().contains(token))
            .map(|p| p.obligation.name.clone())
    };
    // The opcode-level CMP token still lands on the integer comparison family,
    // not on a `-> CMP+CSEL_*` select row.
    let cmp = first_containing("cmp").expect("the `cmp` token must still resolve");
    assert!(
        cmp.starts_with("Icmp_"),
        "the opcode-level `cmp` token now resolves to `{cmp}`"
    );
    // Every precise integer-comparison citation still resolves to its own
    // family member.
    for cond in [
        "eq", "ne", "slt", "sge", "sgt", "sle", "ult", "uge", "ugt", "ule",
    ] {
        for width in ["i32", "i64"] {
            let token = format!("icmp_{cond}_{width}");
            let hit =
                first_containing(&token).unwrap_or_else(|| panic!("`{token}` no longer resolves"));
            assert!(
                hit.to_lowercase().starts_with(&token),
                "`{token}` now resolves to `{hit}`"
            );
        }
    }
}

/// The opcode-level mapping must STAY absent. Three integration tests in other
/// files assert this by name; it is restated here because this file is what
/// would tempt someone to "simplify" the contextual binding into an opcode arm
/// — which is precisely the generic template the `CSet => None` comment
/// rejects on proof grounds.
#[test]
fn the_opcode_level_mapping_stays_absent() {
    for opcode in [
        AArch64Opcode::CSet,
        AArch64Opcode::Csel,
        AArch64Opcode::Csinc,
        AArch64Opcode::Csinv,
        AArch64Opcode::Csneg,
        AArch64Opcode::Fcmp,
        AArch64Opcode::FcselRR,
    ] {
        assert!(
            FunctionVerifier::opcode_to_proof_query(opcode).is_none(),
            "{opcode:?} gained an opcode-level mapping"
        );
    }
}

// ---------------------------------------------------------------------------
// i128 VARIABLE-SHIFT CHAIN: the CSEL guards of the funnel decomposition
//
// `select_i128_shl` / `_lshr` / `_ashr` emit `CMP shift,#0 ; CSEL …,EQ` and
// `CMP shift,#64 ; CSEL …,HS ; CSEL …,HS`. Those three CSELs are the residual
// uncovered `AArch64::Csel` in the certificate lane: their source is a SHIFT,
// not a `Select`, so `csel_reaching_cmp_query` fails closed on the source
// class and nothing else bound them. The source-bound binding selects for them
// the faithful WHOLE-CHAIN obligation of the shift they implement — the same
// move as `(AddsRR, Adc) => "iadd_i128 whole-chain"`.
//
// On this tree nothing is credited, and the source-bound binding only GATES
// these rows: a guard it accepts names the machine-level `a64 nzcv csel x over
// cmp w<amount> <eq|hs>:` form in the withdrawal, a guard it refuses names no
// query. The DIRECTION it selected is therefore read from the arm table
// (`source_bound_selections`), not from the row.
// ---------------------------------------------------------------------------

/// `fn(a: i128, b: <amount_ty>) -> i128 { <shift> a, b }` with a RUNTIME
/// amount, so the `i128_const_shift_amount` pre-scan cannot fold it and the
/// general funnel+CSEL path is what lowers.
///
/// BOTH amount types matter and only one of them is the production shape.
/// `use_i128_shift_amount` hands the amount to the guards in ITS OWN carrier:
/// an `I32` count is compared with `CMP Wn, #0` / `CMP Wn, #64` while the
/// limbs stay 64-bit. That is what `core`'s `<u128>::unchecked_shl` emits —
/// measured on the object: `and w0, w2, #0x7f ; … ; cmp w0, #0x0 ; csel x5,
/// x4, x6, eq ; … ; cmp w0, #0x40 ; csel x0, x4, x5, hs`. An `I128`-typed
/// amount instead yields `CMP Xn, …`. A fixture that covered only the second
/// would pass while the binding refused every real one, which is exactly what
/// happened before this parameter existed.
fn i128_variable_shift_function_with_amount(opcode: Opcode, amount_ty: Type) -> Function {
    source_function(
        "i128_shift_fixture",
        vec![Type::I128, amount_ty],
        vec![Instruction {
            opcode,
            args: vec![Value(0), Value(1)],
            results: vec![Value(10)],
        }],
        10,
        Type::I128,
        vec![(10, Type::I128)],
    )
}

/// The two amount carriers the guards can be emitted at. `I32` FIRST, because
/// it is the one `core` actually compiles.
const I128_SHIFT_AMOUNT_TYPES: [Type; 2] = [Type::I32, Type::I128];

/// The production-shape fixture (a 32-bit amount).
fn i128_variable_shift_function(opcode: Opcode) -> Function {
    i128_variable_shift_function_with_amount(opcode, Type::I32)
}

/// The registry obligation each shift DIRECTION's guards are bound to by the
/// source-bound binding; its lowercase is the query that binding selects.
const I128_SHIFT_CITATIONS: [(Opcode, &str); 3] = [
    (Opcode::Ishl, "Ishl_I128"),
    (Opcode::Ushr, "Ushr_I128"),
    (Opcode::Sshr, "Sshr_I128"),
];

/// Whether a detail names any shift direction's whole-chain obligation, by its
/// registry spelling or by its query.
fn names_a_shift_direction(detail: &str) -> bool {
    let lowered = detail.to_lowercase();
    I128_SHIFT_CITATIONS
        .iter()
        .any(|(_, citation)| lowered.contains(&citation.to_lowercase()))
}

/// The carrier width of the guards' `CMP`s: the shift AMOUNT's own (`CMP Wn`
/// for an `I32` count, `CMP Xn` for a wider one), never the limbs'.
fn i128_shift_amount_cmp_width(lir: &Function) -> u32 {
    if lir.signature.params[1] == Type::I32 {
        32
    } else {
        64
    }
}

/// Assert the UNMUTATED chain BINDS all three guards: each row is uncredited
/// and names the machine-level form of one chain guard — `CSEL X` over the
/// amount-width `CMP`, one `EQ` spill guard and two `HS` selectors. Every
/// control below calls this on its own baseline first: a control that asserts
/// only "refused" would pass identically if the binding never fired at all,
/// which is the shape of a control that cannot fail. This makes each one LIVE.
fn assert_all_three_guards_bound(machine: &MachFunction, lir: &Function, what: &str) {
    let rows = rows_for(machine, lir, AArch64Opcode::Csel);
    assert_eq!(rows.len(), 3, "{what}: expected three guards, got {rows:?}");
    let width = i128_shift_amount_cmp_width(lir);
    let mut named: Vec<&str> = rows
        .iter()
        .map(|(status, detail)| {
            assert_eq!(
                *status,
                OpcodeInventoryStatus::Unverified,
                "{what}: a guard was credited, but registry-name credit is withdrawn: {detail}"
            );
            withdrawn_query(detail)
                .unwrap_or_else(|| {
                    panic!("{what}: baseline guard refused ({detail}) — this control cannot fail")
                })
                .0
        })
        .collect();
    named.sort_unstable();
    let mut expected = vec![
        csel_form_query(64, width, 0),
        csel_form_query(64, width, 2),
        csel_form_query(64, width, 2),
    ];
    expected.sort_unstable();
    assert_eq!(
        named, expected,
        "{what}: the baseline guards are not bound to the chain's own guard forms"
    );
}

/// POSITIVE: every CSEL the i128 variable-shift decomposition emits is bound,
/// and the source-bound binding selects the obligation of THIS shift's own
/// direction — `Ishl` does not inherit `Ushr`'s theorem.
///
/// The row itself names the machine-level CSEL form, which carries no
/// direction (that is what the merged `nzcv_consumer_query` keeps), so the
/// direction is read from the arm table; the row is asserted to name no
/// direction's obligation at all.
#[test]
fn every_i128_variable_shift_csel_cites_its_own_direction_whole_chain() {
    let mut checked = 0;
    for (opcode, expected) in I128_SHIFT_CITATIONS {
        for amount in I128_SHIFT_AMOUNT_TYPES {
            let lir = i128_variable_shift_function_with_amount(opcode.clone(), amount.clone());
            let machine = select(&lir);
            let rows = rows_for(&machine, &lir, AArch64Opcode::Csel);
            assert_eq!(
                rows.len(),
                3,
                "{opcode:?}/{amount:?} must lower to the three funnel guards, got {rows:?}"
            );
            assert_all_three_guards_bound(&machine, &lir, &format!("{opcode:?}/{amount:?}"));
            for (_, detail) in &rows {
                assert!(
                    !names_a_shift_direction(detail),
                    "{opcode:?}/{amount:?} guard row names a direction obligation: {detail}"
                );
            }
            let own = expected.to_lowercase();
            let selected = source_bound_selections(&machine, &lir, AArch64Opcode::Csel);
            assert_eq!(selected.len(), 3, "{opcode:?}/{amount:?}: {selected:?}");
            for query in selected {
                assert_eq!(
                    query,
                    Some(own.as_str()),
                    "{opcode:?}/{amount:?} guard was not bound to {expected}"
                );
                for (_, other) in I128_SHIFT_CITATIONS {
                    if other != expected {
                        assert_ne!(
                            query,
                            Some(other.to_lowercase().as_str()),
                            "{opcode:?}/{amount:?} guard inherited {other}"
                        );
                    }
                }
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 18);
}

/// MUST-REFUTE (amount-width coherence): the two boundaries must be tested at
/// the SAME amount carrier. Widening only the `#64` guard's compared register
/// to X while the `#0` guard stays at W leaves both boundaries, both
/// conditions, both producers and the limb widths intact — and must still be
/// refused, because a chain that tests one boundary at 32 bits and the other at
/// 64 is not one the cited theorem describes.
#[test]
fn an_i128_shift_chain_with_mismatched_guard_widths_is_refused() {
    use trust_cg_ir::MachOperand;
    use trust_cg_ir::aarch64_regs::X0;
    let mut checked = 0;
    for (opcode, _) in I128_SHIFT_CITATIONS {
        let lir = i128_variable_shift_function_with_amount(opcode.clone(), Type::I32);
        let base = select(&lir);
        assert_all_three_guards_bound(&base, &lir, &format!("{opcode:?} baseline"));
        let cmp64 = base
            .insts
            .iter()
            .position(|inst| {
                matches!(inst.opcode, AArch64Opcode::CmpRI)
                    && inst.operands.get(1) == Some(&MachOperand::Imm(64))
            })
            .expect("the chain compares against #64");
        let mut machine = base.clone();
        machine.insts[cmp64].operands[0] = MachOperand::PReg(X0);
        let rows = rows_for(&machine, &lir, AArch64Opcode::Csel);
        assert!(
            rows.iter().all(is_refused),
            "{opcode:?}: mismatched guard widths were bound: {rows:?}"
        );
        checked += 1;
    }
    assert_eq!(checked, 3);
}

/// PRODUCER-BOUND PIN for the three rows this binding newly SELECTS.
///
/// On this tree the selection is not credit (E0.2 withdrew registry-name
/// credit, and the guard rows name the machine-level CSEL form); it is what
/// `source_bound_selections` observes. The pin keeps that selection on each
/// direction's own, non-degenerate row, so no substituted or X==X row can ride
/// this binding should an operand-exact path ever credit it.
///
/// This lane adds no obligation — `EXPECTED_STATIC_PROOF_OBLIGATION_COUNT` does
/// not move — so the corpus-cardinality ratchet has nothing to pin. What IS new
/// is that three long-registered rows are now selected for an opcode that had no
/// mapping, and the substitution hole `494a96e76`/`fb76822f0`/`fba592707`
/// closed for the cardinality gates applies here in the same shape: a
/// name-plus-non-degeneracy check would be satisfied by ANY row that happened
/// to carry the name. Each cited row is therefore bound to the INDIVIDUAL
/// PRODUCER function that mints it, and to the exact query token the walk uses,
/// within the exact category the walk searches.
///
/// Why non-degeneracy is load-bearing rather than decorative:
/// `emitted_opcode_inventory` maps EVERY `Verified` result to
/// `OpcodeInventoryStatus::Verified`, degenerate or not. Citing a degenerate
/// X==X row would therefore convert a loud `[TCG-PROOF-465]` refusal into a
/// silent claim of verified codegen — the exact harm this binding must not do.
///
/// MUTATION-PROVED: substituting a real pre-existing `ProofCategory::Arithmetic`
/// row (`proof_iadd_i128_lo()`, registered long before this lane) for any of the
/// three makes this test FAIL — the producer-identity assertion rejects it even
/// though it is registered exactly once, in the right category, and passes every
/// name/degeneracy check.
#[test]
fn the_i128_shift_chain_citations_are_producer_bound_and_not_degenerate() {
    use trust_cg_verify::lowering_proof::{proof_ishl_i128, proof_sshr_i128, proof_ushr_i128};
    use trust_cg_verify::proof_database::{ProofCategory, ProofDatabase, is_known_degenerate_debt};
    let db = ProofDatabase::new();
    // (query token the walk emits, the individual producer that must mint the
    // row it resolves to, the name the positive test observes in the citation).
    let audited: [(&str, trust_cg_verify::lowering_proof::ProofObligation, &str); 3] = [
        ("ishl_i128", proof_ishl_i128(), "Ishl_I128"),
        ("ushr_i128", proof_ushr_i128(), "Ushr_I128"),
        ("sshr_i128", proof_sshr_i128(), "Sshr_I128"),
    ];
    let mut checked = 0;
    for (token, produced, display) in audited {
        assert!(
            produced.name.contains(display),
            "producer name {} lost the spelling the citation asserts ({display})",
            produced.name
        );
        assert!(
            !produced.is_degenerate(),
            "{} became X==X — it may not be cited",
            produced.name
        );
        assert!(
            !is_known_degenerate_debt(&produced.name),
            "{} joined the degenerate ledger — it may not be cited",
            produced.name
        );
        // The walk resolves a query by `by_category` then a lowercase substring
        // match on the NAME, first hit in registration order. Both halves are
        // pinned: exactly one row in that category matches the token, and that
        // row is EXACTLY what this direction's own producer mints.
        let hits: Vec<_> = db
            .by_category(ProofCategory::Arithmetic)
            .into_iter()
            .filter(|row| row.obligation.name.to_lowercase().contains(token))
            .collect();
        assert_eq!(
            hits.len(),
            1,
            "token {token:?} matched {} Arithmetic rows",
            hits.len()
        );
        assert_eq!(
            hits[0].obligation, produced,
            "the row token {token:?} resolves to is not what {display}'s own producer              mints — a substituted obligation may not inherit this binding's credit"
        );
        assert_eq!(
            db.all()
                .iter()
                .filter(|row| row.obligation.name == produced.name)
                .count(),
            1,
            "{} is missing or duplicated in the registry",
            produced.name
        );
        checked += 1;
    }
    assert_eq!(checked, 3);
}

/// MUST-REFUTE (guard condition): a condition the chain never emits earns
/// nothing. The chain's only conditions are `EQ` (the `shift == 0` spill
/// guard) and `HS` (the `shift >= 64` selector).
#[test]
fn an_i128_shift_csel_on_a_foreign_condition_is_refused() {
    use trust_cg_ir::MachOperand;
    let mut checked = 0;
    for (opcode, _) in I128_SHIFT_CITATIONS {
        let lir = i128_variable_shift_function(opcode.clone());
        let base = select(&lir);
        let csels: Vec<usize> = base
            .insts
            .iter()
            .enumerate()
            .filter(|(_, inst)| inst.opcode == AArch64Opcode::Csel)
            .map(|(index, _)| index)
            .collect();
        assert_eq!(csels.len(), 3);
        assert_all_three_guards_bound(&base, &lir, &format!("{opcode:?} baseline"));
        // NE=1, LO=3, MI=4, GT=12 — none is a chain guard.
        for wrong in [1i64, 3, 4, 12] {
            let mut machine = base.clone();
            machine.insts[csels[0]].operands[3] = MachOperand::Imm(wrong);
            let rows = rows_for(&machine, &lir, AArch64Opcode::Csel);
            assert!(
                rows.iter().all(is_refused),
                "{opcode:?} with cc={wrong} was bound: {rows:?}"
            );
            checked += 1;
        }
    }
    assert_eq!(checked, 12);
}

/// MUST-REFUTE (guard boundary): the condition must be the one THIS guard's
/// reaching comparison establishes. Relabelling the `shift == 0` spill guard's
/// `CSEL EQ` as `CSEL HS` leaves a chain-shaped window whose every other fact
/// still holds — the condition is a real guard condition, the producer is a
/// 64-bit integer CMP, the sibling shape is untouched — and it must still be
/// refused, because `HS` pairs with `CMP shift,#64` and this one is
/// `CMP shift,#0`.
#[test]
fn an_i128_shift_csel_read_against_the_wrong_boundary_is_refused() {
    use trust_cg_ir::MachOperand;
    let mut checked = 0;
    for (opcode, _) in I128_SHIFT_CITATIONS {
        let lir = i128_variable_shift_function(opcode.clone());
        let base = select(&lir);
        let eq_guard = base
            .insts
            .iter()
            .position(|inst| {
                inst.opcode == AArch64Opcode::Csel
                    && inst.operands.get(3) == Some(&MachOperand::Imm(0))
            })
            .expect("the chain has one EQ-guarded spill select");
        assert_all_three_guards_bound(&base, &lir, &format!("{opcode:?} baseline"));
        let mut machine = base.clone();
        // HS, whose boundary is #64, against a producer comparing against #0.
        machine.insts[eq_guard].operands[3] = MachOperand::Imm(2);
        let rows = rows_for(&machine, &lir, AArch64Opcode::Csel);
        let bound = rows.iter().filter(|row| is_bound(row)).count();
        let refused = rows.iter().filter(|row| is_refused(row)).count();
        // NONE bound, not two. The selected query is the WHOLE-CHAIN theorem;
        // a chain with one relabelled guard is not the funnel it describes, so
        // the two untouched selects may not keep selecting it either (fact 8,
        // data flow).
        assert_eq!(
            (bound, refused),
            (0, 3),
            "{opcode:?}: a guard of a broken chain kept the whole-chain binding: {rows:?}"
        );
        // And the refused row is the relabelled guard's own (rows follow the
        // walk's instruction order).
        let relabelled = chain_csel_sites(&base)
            .iter()
            .position(|(site, _)| *site == eq_guard)
            .expect("the EQ guard is a chain CSEL");
        assert!(
            is_refused(&rows[relabelled]),
            "{opcode:?}: the relabelled guard kept its binding: {rows:?}"
        );
        checked += 1;
    }
    assert_eq!(checked, 3);
}

/// MUST-REFUTE (carrier width): the chain is entirely 64-bit limbs. A
/// 32-bit-carrier `CSEL` cannot be one of its guards and earns nothing.
#[test]
fn a_narrow_carrier_i128_shift_csel_is_refused() {
    use trust_cg_ir::aarch64_regs::{W0, W1, W2};
    use trust_cg_ir::{MachInst, MachOperand};
    let mut checked = 0;
    for (opcode, _) in I128_SHIFT_CITATIONS {
        let lir = i128_variable_shift_function(opcode.clone());
        let base = select(&lir);
        let csel = base
            .insts
            .iter()
            .position(|inst| inst.opcode == AArch64Opcode::Csel)
            .expect("the chain has a CSEL");
        assert_all_three_guards_bound(&base, &lir, &format!("{opcode:?} baseline"));
        let cc = base.insts[csel].operands[3].clone();
        let mut machine = base.clone();
        machine.insts[csel] = MachInst::new(
            AArch64Opcode::Csel,
            vec![
                MachOperand::PReg(W0),
                MachOperand::PReg(W1),
                MachOperand::PReg(W2),
                cc,
            ],
        );
        let rows = rows_for(&machine, &lir, AArch64Opcode::Csel);
        let bound = rows.iter().filter(|row| is_bound(row)).count();
        let refused = rows.iter().filter(|row| is_refused(row)).count();
        // NONE bound, not two: with one select narrowed the chain no longer
        // reconstructs as the cited funnel, and no select of it may select the
        // whole-chain theorem (fact 8, data flow).
        assert_eq!(
            (bound, refused),
            (0, 3),
            "{opcode:?}: a select of a chain with a 32-bit CSEL was bound: {rows:?}"
        );
        // And the refused row is the narrowed CSEL's own: it is the chain's
        // first, and rows follow the walk's instruction order.
        assert!(
            is_refused(&rows[0]),
            "{opcode:?}: the 32-bit CSEL was bound: {rows:?}"
        );
        checked += 1;
    }
    assert_eq!(checked, 3);
}

/// MUST-REFUTE (chain shape): a THIRD comparison boundary among the
/// instructions stamped with this shift means the window is not the chain, and
/// EVERY guard loses its binding — the shape fact is chain-wide, not per
/// instruction.
#[test]
fn a_third_boundary_in_the_i128_shift_window_refuses_every_guard() {
    use trust_cg_ir::MachOperand;
    let mut checked = 0;
    for (opcode, _) in I128_SHIFT_CITATIONS {
        let lir = i128_variable_shift_function(opcode.clone());
        let base = select(&lir);
        let cmp = base
            .insts
            .iter()
            .position(|inst| {
                matches!(inst.opcode, AArch64Opcode::CmpRI)
                    && inst.operands.get(1) == Some(&MachOperand::Imm(64))
            })
            .expect("the chain compares against #64");
        assert_all_three_guards_bound(&base, &lir, &format!("{opcode:?} baseline"));
        let mut machine = base.clone();
        machine.insts[cmp].operands[1] = MachOperand::Imm(65);
        let rows = rows_for(&machine, &lir, AArch64Opcode::Csel);
        assert!(
            rows.iter().all(is_refused),
            "{opcode:?}: a {{0, 65}} boundary pair was bound: {rows:?}"
        );
        checked += 1;
    }
    assert_eq!(checked, 3);
}

/// MUST-REFUTE (conditional-select siblings): `CSINC`/`CSINV`/`CSNEG` add,
/// invert and negate their false arm. They are not the chain's selects and
/// inherit nothing from this binding, exactly as they inherit nothing from the
/// `Select` one.
///
/// Every row is uncredited on this tree, so the inheritance is checked where it
/// would show: the source-bound binding selects nothing for the sibling, and
/// its row names neither a `CSEL` form nor any direction's chain obligation.
/// (`CSINC`/`CSNEG` rows may name their OWN machine-level form; that is the
/// machine-level binding, not this one.)
#[test]
fn the_i128_shift_binding_does_not_reach_the_conditional_select_siblings() {
    use trust_cg_ir::{MachInst, MachOperand};
    let mut checked = 0;
    for (opcode, _) in I128_SHIFT_CITATIONS {
        let lir = i128_variable_shift_function(opcode.clone());
        let base = select(&lir);
        let csel = base
            .insts
            .iter()
            .position(|inst| inst.opcode == AArch64Opcode::Csel)
            .expect("the chain has a CSEL");
        assert_all_three_guards_bound(&base, &lir, &format!("{opcode:?} baseline"));
        let operands = base.insts[csel].operands.clone();
        for sibling in [
            AArch64Opcode::Csinc,
            AArch64Opcode::Csinv,
            AArch64Opcode::Csneg,
        ] {
            let mut machine = base.clone();
            machine.insts[csel] = MachInst::new(sibling, operands.clone());
            for (status, detail) in rows_for(&machine, &lir, sibling) {
                assert_eq!(
                    status,
                    OpcodeInventoryStatus::Unverified,
                    "{sibling:?} inherited the i128 shift binding: {detail}"
                );
                let named = withdrawn_query(&detail).map_or("", |(query, _)| query);
                assert!(
                    !named.starts_with("a64 nzcv csel ") && !names_a_shift_direction(&detail),
                    "{sibling:?} inherited the i128 shift binding: {detail}"
                );
            }
            let selected = source_bound_selections(&machine, &lir, sibling);
            assert_eq!(
                selected,
                vec![None::<&str>],
                "{sibling:?}: the source-bound binding reached a sibling"
            );
            checked += 1;
        }
        let _ = MachOperand::Imm(0);
    }
    assert_eq!(checked, 9);
}

/// MUST-REFUTE (source stamp): with no replayed LIR there is no source
/// operation, so the direction the chain theorem is keyed on is unknown and
/// every guard earns nothing. This is the same fail-closed rule the CSET/CSEL
/// bindings have; it is restated here because this binding reads a FINER fact
/// (the LIR opcode, not just its class).
///
/// On this tree such a row may still name the machine-level CSEL form (that
/// binding needs no source), but never a direction's chain obligation.
#[test]
fn an_i128_shift_csel_without_a_source_stamp_earns_nothing() {
    let mut checked = 0;
    for (opcode, _) in I128_SHIFT_CITATIONS {
        let lir = i128_variable_shift_function(opcode.clone());
        let machine = select(&lir);
        assert_all_three_guards_bound(&machine, &lir, &format!("{opcode:?} baseline"));
        let verifier = FunctionVerifier::new();
        let report = verifier.verify(&machine);
        let rows: Vec<_> = report
            .emitted_opcode_inventory()
            .entries
            .into_iter()
            .filter(|entry| entry.opcode == InstructionOpcode::AArch64(AArch64Opcode::Csel))
            .collect();
        assert_eq!(rows.len(), 3);
        for entry in rows {
            assert_eq!(
                entry.status,
                OpcodeInventoryStatus::Unverified,
                "{opcode:?} guard credited with no provenance: {}",
                entry.detail
            );
            assert!(
                !names_a_shift_direction(&entry.detail),
                "{opcode:?} guard bound to a direction with no provenance: {}",
                entry.detail
            );
            checked += 1;
        }
    }
    assert_eq!(checked, 9);
}

// ---------------------------------------------------------------------------
// THE SOURCE-CONDITION BINDING
//
// Facts 1-4 of the block comment in `function_verifier` are all read off the
// EMITTED instruction and its block — and so is the `cc` immediate that NAMES
// the cited family member. Without a conjunct binding that condition to the
// source, the theorem is selected BY the instruction under test: mutate only
// the condition immediate, leave the LIR alone so the code no longer implements
// its own source, and the citation simply moves to another true theorem about
// another program. Ten of the fourteen conditions have an `Icmp_*` family
// member, so for those ten `NoProofMapping` was never the barrier at all.
// ---------------------------------------------------------------------------

/// Every AArch64 condition-code immediate, with its mnemonic, in encoding
/// order (`AArch64CC`'s declaration order).
const ALL_CC_IMMEDIATES: [(i64, &str); 14] = [
    (0, "EQ"),
    (1, "NE"),
    (2, "HS"),
    (3, "LO"),
    (4, "MI"),
    (5, "PL"),
    (6, "VS"),
    (7, "VC"),
    (8, "HI"),
    (9, "LS"),
    (10, "GE"),
    (11, "LT"),
    (12, "GT"),
    (13, "LE"),
];

/// The index of the single `CSet` in a lowered machine function.
fn sole_cset_index(machine: &MachFunction) -> usize {
    let found: Vec<usize> = machine
        .insts
        .iter()
        .enumerate()
        .filter(|(_, inst)| inst.opcode == AArch64Opcode::CSet)
        .map(|(index, _)| index)
        .collect();
    assert_eq!(found.len(), 1, "expected exactly one CSET, got {found:?}");
    found[0]
}

/// WITNESS 1. `fn(a: i64, b: i64) -> b1 { icmp slt a, b }` lowered by the
/// production selector to `CMP ; CSET LT`. Mutate ONLY the CSET's condition
/// immediate — the LIR is untouched, so the emitted code no longer implements
/// its own source — and read the inventory row.
///
/// `LT` is the genuine lowering and must stay bound to its whole-sequence
/// `Icmp_SLT_I64` member (named in the withdrawal; not credit). EVERY other
/// condition must be REFUSED — bound to nothing. Four of them
/// (`MI`/`PL`/`VS`/`VC`) were already refused before this binding existed, but
/// for the wrong reason: the `Icmp_*` registry family has no member for them,
/// so `NoProofMapping` was doing the work. The other nine were credited a true
/// theorem about a different comparison (and the machine-level binding alone
/// would still name one). `CMP a,b ; CSET MI` is a genuine miscompile of signed
/// `a < b` — at `a = i64::MIN, b = 1` the source says 1 and `CSET MI` answers 0.
#[test]
fn witness_a_cset_condition_inconsistent_with_its_source_is_refused() {
    use trust_cg_ir::MachOperand;
    let lir = icmp_function(Type::I64, IntCC::SignedLessThan);
    let base = select(&lir);
    let cset = sole_cset_index(&base);
    assert!(
        matches!(base.insts[cset].operands[1], MachOperand::Imm(11)),
        "fixture must lower `icmp slt` to `CSET LT` (cc 11), got {:?}",
        base.insts[cset].operands[1]
    );

    println!("cond | status       | citation");
    let mut refused = 0;
    for (code, name) in ALL_CC_IMMEDIATES {
        let mut machine = base.clone();
        machine.insts[cset].operands[1] = MachOperand::Imm(code);
        let rows = rows_for(&machine, &lir, AArch64Opcode::CSet);
        assert_eq!(rows.len(), 1);
        let (status, detail) = &rows[0];
        println!("{name:<4} | {status:<12} | {detail}");
        if code == 11 {
            assert_bound_to(
                &rows[0],
                "icmp_slt_i64",
                ProofCategory::Comparison,
                "the genuine LT lowering must stay bound to the SLT family member",
            );
        } else {
            assert_refused(
                &rows[0],
                &format!("cc {name} is inconsistent with `icmp slt` and must be refused"),
            );
            assert!(
                !is_sequence_citation(detail),
                "cc {name} was credited a sequence theorem: {detail}"
            );
            assert!(
                !is_decoded_word_citation(detail),
                "cc {name} was credited the decoded-word row: {detail}"
            );
            refused += 1;
        }
    }
    assert_eq!(refused, 13);

    // The no-provenance row belongs in the same table: with no replayed LIR
    // there is no source instruction, so nothing can attest the condition.
    let verifier = FunctionVerifier::new();
    let report = verifier.verify(&base);
    let rows: Vec<_> = report
        .emitted_opcode_inventory()
        .entries
        .into_iter()
        .filter(|entry| entry.opcode == InstructionOpcode::AArch64(AArch64Opcode::CSet))
        .collect();
    assert_eq!(rows.len(), 1);
    println!(
        "{:<4} | {:<12} | {}",
        "none", rows[0].status, rows[0].detail
    );
    assert_eq!(
        rows[0].status,
        OpcodeInventoryStatus::Unverified,
        "a CSET with no provenance was credited: {}",
        rows[0].detail
    );
}

/// The same fact for the other nine source conditions: the genuine condition
/// stays bound to its own member, and a condition the source cannot produce is
/// refused. `SLE` is the interesting row — the i128 limb decomposition of a
/// signed `<=` legitimately emits `LT` on the high limbs, so `LT` is admitted
/// under an `SLE` source and this test does not claim otherwise.
#[test]
fn only_the_conditions_a_source_comparison_can_emit_are_credited() {
    use trust_cg_ir::MachOperand;
    let mut checked = 0;
    for cond in ALL_CONDITIONS {
        let lir = icmp_function(Type::I64, cond);
        let base = select(&lir);
        let cset = sole_cset_index(&base);
        // `MI`/`PL`/`VS`/`VC` are flag-only conditions no integer comparison's
        // lowering can emit, at either width or limb position.
        for (code, name) in [(4, "MI"), (5, "PL"), (6, "VS"), (7, "VC")] {
            let mut machine = base.clone();
            machine.insts[cset].operands[1] = MachOperand::Imm(code);
            let rows = rows_for(&machine, &lir, AArch64Opcode::CSet);
            assert_eq!(rows.len(), 1);
            assert_refused(&rows[0], &format!("{cond:?} + cc {name}"));
            checked += 1;
        }
        // And the genuine one is untouched.
        let rows = rows_for(&base, &lir, AArch64Opcode::CSet);
        assert_bound_to(
            &rows[0],
            &format!("icmp_{}_i64", condition_spelling(scalar_cc(cond))),
            ProofCategory::Comparison,
            &format!("{cond:?}: the genuine lowering"),
        );
    }
    assert_eq!(checked, 40);
}

/// The checked-arithmetic signedness now comes from the SOURCE opcode. `ADDS`
/// serves both `CheckedSadd` (V flag, `CSET VS`) and `CheckedUadd` (carry-out,
/// `CSET HS`); the arm used to read WHICH from the emitted condition, so an
/// `ADDS ; CSET VS` emitted while lowering a `CheckedUadd` cited
/// `CheckedSadd_I64` and promoted. Those are different predicates —
/// `1 + i64::MAX` overflows signed and not unsigned — so that row was green
/// about a program it was not compiling. On this tree the genuine condition
/// stays bound to its own source's member, and the other signedness' condition
/// is refused outright rather than re-bound to the other member (which is what
/// the machine-level binding alone would name).
#[test]
fn the_checked_overflow_signedness_is_taken_from_the_source() {
    use trust_cg_ir::MachOperand;
    // (source, its genuine cc, that source's own member, a cc that belongs to
    // the OTHER signedness of the same producer opcode)
    let cases = [
        (Opcode::CheckedSadd, 6, "checkedsadd_i64", 2),
        (Opcode::CheckedUadd, 2, "checkeduadd_i64", 6),
        (Opcode::CheckedSsub, 6, "checkedssub_i64", 3),
        (Opcode::CheckedUsub, 3, "checkedusub_i64", 6),
    ];
    let mut checked = 0;
    for (opcode, genuine, own, foreign) in cases {
        let lir = checked_function(Type::I64, opcode.clone());
        let base = select(&lir);
        let cset = sole_cset_index(&base);
        assert!(
            matches!(base.insts[cset].operands[1], MachOperand::Imm(cc) if cc == genuine),
            "{opcode:?} must lower to cc {genuine}, got {:?}",
            base.insts[cset].operands[1]
        );
        assert_bound_to(
            &rows_for(&base, &lir, AArch64Opcode::CSet)[0],
            own,
            ProofCategory::Arithmetic,
            &format!("{opcode:?} baseline (this control cannot fail)"),
        );
        let mut machine = base.clone();
        machine.insts[cset].operands[1] = MachOperand::Imm(foreign);
        let rows = rows_for(&machine, &lir, AArch64Opcode::CSet);
        assert_eq!(rows.len(), 1);
        assert_refused(
            &rows[0],
            &format!("{opcode:?} with the other signedness' condition"),
        );
        checked += 1;
    }
    assert_eq!(checked, 4);
}

// ---------------------------------------------------------------------------
// THE i128 VARIABLE-SHIFT GUARD ARM WIRING
// ---------------------------------------------------------------------------

/// The block positions of the chain's `Csel`s, in emission order, with their
/// condition immediates.
fn chain_csel_sites(machine: &MachFunction) -> Vec<(usize, i64)> {
    use trust_cg_ir::MachOperand;
    machine
        .insts
        .iter()
        .enumerate()
        .filter(|(_, inst)| inst.opcode == AArch64Opcode::Csel)
        .map(|(index, inst)| match inst.operands[3] {
            MachOperand::Imm(cc) => (index, cc),
            ref other => panic!("CSEL condition is {other:?}"),
        })
        .collect()
}

/// WITNESS 2. Swapping the TWO ARMS of one chain guard is a two-byte object
/// change that satisfies every fact the guard binding checked before this
/// conjunct — same opcode, same three 64-bit registers, same condition, same
/// reaching `CMP` boundary, same chain shape — and it miscompiles: swapping the
/// `shift == 0` spill guard makes `1u128 << 0` evaluate to `2^64 + 1`, because
/// the guard's purpose is to force the spill term to zero WHEN the condition
/// holds and the swap forces it to zero when the condition FAILS.
///
/// Every one of the three guards in every one of the three directions must
/// refuse when its arms are swapped, at both amount carriers.
#[test]
fn witness_an_i128_shift_guard_with_swapped_arms_is_refused() {
    let mut checked = 0;
    for (opcode, _) in I128_SHIFT_CITATIONS {
        for amount in I128_SHIFT_AMOUNT_TYPES {
            let lir = i128_variable_shift_function_with_amount(opcode.clone(), amount.clone());
            let base = select(&lir);
            assert_all_three_guards_bound(&base, &lir, &format!("{opcode:?}/{amount:?} baseline"));
            for (site, cc) in chain_csel_sites(&base) {
                let mut machine = base.clone();
                machine.insts[site].operands.swap(1, 2);
                let rows = rows_for(&machine, &lir, AArch64Opcode::Csel);
                assert_eq!(rows.len(), 3);
                assert!(
                    rows.iter()
                        .all(|(status, _)| *status == OpcodeInventoryStatus::Unverified),
                    "{opcode:?}/{amount:?}: a guard was credited: {rows:?}"
                );
                let refused = rows.iter().filter(|row| is_refused(row)).count();
                assert!(
                    refused >= 1,
                    "{opcode:?}/{amount:?}: swapping the cc={cc} guard's arms left every \
                     guard bound: {rows:?}"
                );
                checked += 1;
            }
        }
    }
    // 3 directions x 2 amount carriers x 3 guards.
    assert_eq!(checked, 18);
}

/// The wiring conjunct must not be satisfiable by ANY other same-block
/// register: pointing the `EQ` guard's TRUE arm at the funnel's combined
/// result, or at the raw spill it is meant to override, is refused.
#[test]
fn the_eq_spill_guard_true_arm_must_be_the_materialised_zero() {
    let mut checked = 0;
    for (opcode, _) in I128_SHIFT_CITATIONS {
        let lir = i128_variable_shift_function(opcode.clone());
        let base = select(&lir);
        assert_all_three_guards_bound(&base, &lir, &format!("{opcode:?} baseline"));
        let eq_site = chain_csel_sites(&base)
            .into_iter()
            .find(|(_, cc)| *cc == 0)
            .expect("the chain emits one EQ spill guard")
            .0;
        // Point the TRUE arm at the guard's own FALSE arm (the raw spill). The
        // select then computes the raw spill under every flag state, which is
        // exactly the masking bug the guard exists to prevent.
        let mut machine = base.clone();
        let false_arm = machine.insts[eq_site].operands[2].clone();
        machine.insts[eq_site].operands[1] = false_arm;
        let rows = rows_for(&machine, &lir, AArch64Opcode::Csel);
        assert!(
            rows.iter()
                .all(|(status, _)| *status == OpcodeInventoryStatus::Unverified),
            "{opcode:?}: a guard was credited: {rows:?}"
        );
        let refused = rows.iter().filter(|row| is_refused(row)).count();
        assert!(
            refused >= 1,
            "{opcode:?}: a degenerate EQ guard was bound: {rows:?}"
        );
        checked += 1;
    }
    assert_eq!(checked, 3);
}

// ---------------------------------------------------------------------------
// WALK ORDER
// ---------------------------------------------------------------------------

/// WALK-CHAIN ORDER IS LOAD-BEARING AND NO COUNT CAN SEE IT. The arms above the
/// i128 variable-shift guard cite theorems about the WHOLE lowered sequence a
/// `CSET`/`CSEL` completes, which is strictly more than a guard-level row
/// states; a weaker or differently scoped arm moved in front of them REPLACES
/// those citations while every census root set stays byte-identical. Measured:
/// moving a per-instruction CSET arm to the FRONT of this chain took this test
/// file from 13 passed / 0 failed to 9 passed / 4 FAILED with the core and
/// alloc root sets UNCHANGED.
///
/// `FunctionVerifier::NZCV_CONSUMER_ARMS` IS the order the walk runs —
/// `nzcv_consumer_source_bound_query` has no other source of it — so asserting
/// this list asserts what executes.
#[test]
fn nzcv_consumer_arm_order_is_pinned() {
    let names: Vec<&str> = FunctionVerifier::NZCV_CONSUMER_ARMS
        .iter()
        .map(|(name, _)| *name)
        .collect();
    assert_eq!(
        names,
        [
            "cset_reaching_cmp",
            "cset_checked_overflow",
            "csel_reaching_cmp",
            "i128_variable_shift_chain_csel",
        ],
        "the NZCV-consumer walk order changed"
    );
    assert_eq!(
        names.last().copied(),
        Some("i128_variable_shift_chain_csel"),
        "the i128 variable-shift guard arm must stay LAST"
    );
}

/// The same defect, same fix, for the `CSEL` arm: the cited
/// `Select_<cond>_...` family member is named by the condition read off the
/// emitted instruction. A `Select { cond: SLT }` lowered as `CMP ; CSEL GT`
/// implements the OPPOSITE selection and must be refused, not re-bound. The
/// machine-level binding alone would name the foreign condition's form, so a
/// row that names NO query is exactly the source-bound refusal.
#[test]
fn a_csel_condition_inconsistent_with_its_source_select_is_refused() {
    use trust_cg_ir::MachOperand;
    let mut checked = 0;
    for cond in ALL_CONDITIONS {
        let lir = select_function(Type::I64, cond);
        let base = select(&lir);
        let sites: Vec<usize> = base
            .insts
            .iter()
            .enumerate()
            .filter(|(_, inst)| inst.opcode == AArch64Opcode::Csel)
            .map(|(index, _)| index)
            .collect();
        assert_eq!(sites.len(), 1, "{cond:?}: expected one CSEL");
        let baseline = rows_for(&base, &lir, AArch64Opcode::Csel);
        assert_bound_to(
            &baseline[0],
            csel_form_query(64, 64, scalar_cc(cond)),
            ProofCategory::Comparison,
            &format!("{cond:?} baseline (this control cannot fail)"),
        );
        let genuine = match base.insts[sites[0]].operands[3] {
            MachOperand::Imm(cc) => cc,
            ref other => panic!("CSEL condition is {other:?}"),
        };
        for (code, name) in ALL_CC_IMMEDIATES {
            if code == genuine {
                continue;
            }
            let mut machine = base.clone();
            machine.insts[sites[0]].operands[3] = MachOperand::Imm(code);
            let rows = rows_for(&machine, &lir, AArch64Opcode::Csel);
            assert_eq!(rows.len(), 1);
            assert_refused(&rows[0], &format!("{cond:?} + cc {name}"));
            checked += 1;
        }
    }
    // 10 source conditions x 13 foreign condition codes.
    assert_eq!(checked, 130);
}

// ---------------------------------------------------------------------------
// THE HOLES `2e194289f` DISCLOSED AND DID NOT CLOSE
//
// Each witness below mutates the MACHINE CODE ONLY — the LIR is untouched, so
// the mutated code no longer implements its own source — and every one of them
// keeps every per-instruction fact the bindings checked before: same opcodes,
// same widths, same conditions admitted by the source, same boundaries, same
// arm opcodes. What moves is a ROLE (which limb, which position) or a DATA-FLOW
// edge (which value an arm is built from). Measured on the base, every witness
// here is BOUND: its rows name the whole-chain or comparison query the binding
// selected (at `572c4ce34`, before E0.2 withdrew registry-name credit, the same
// witnesses were `Verified` — PROMOTED). `hole1_*` lives with the
// source-bound frame's unit tests (`source_bound_diamond_tests.rs`), because
// that lane's query is crate-private.
// ---------------------------------------------------------------------------

/// Per row of `opcode`, in function order: is the row BOUND (it names the
/// query the binding selected)?
fn bound_rows(machine: &MachFunction, lir: &Function, opcode: AArch64Opcode) -> Vec<bool> {
    rows_for(machine, lir, opcode)
        .iter()
        .map(is_bound)
        .collect()
}

/// Per row of `opcode`, in function order: is the row REFUSED (it names no
/// query at all)?
fn refused_rows(machine: &MachFunction, lir: &Function, opcode: AArch64Opcode) -> Vec<bool> {
    rows_for(machine, lir, opcode)
        .iter()
        .map(is_refused)
        .collect()
}

/// Assert EVERY row of `opcode` is REFUSED: the binding selected nothing.
fn assert_all_refused(machine: &MachFunction, lir: &Function, opcode: AArch64Opcode, what: &str) {
    let rows = rows_for(machine, lir, opcode);
    assert!(!rows.is_empty(), "{what}: no {opcode:?} row at all");
    assert!(
        rows.iter().all(is_refused),
        "{what}: a {opcode:?} row is still bound: {rows:?}"
    );
}

/// The instruction indices of `opcode` in a single-block lowering, in order.
fn sites_of(machine: &MachFunction, opcode: AArch64Opcode) -> Vec<usize> {
    machine
        .insts
        .iter()
        .enumerate()
        .filter(|(_, inst)| inst.opcode == opcode)
        .map(|(index, _)| index)
        .collect()
}

/// The two `HS` selects of a lowered i128 variable-shift chain, in emission
/// order, and its `EQ` spill guard.
fn shift_chain_selects(machine: &MachFunction) -> (usize, [usize; 2]) {
    let sites = chain_csel_sites(machine);
    let guard: Vec<usize> = sites
        .iter()
        .filter(|(_, cc)| *cc == 0)
        .map(|(i, _)| *i)
        .collect();
    let hs: Vec<usize> = sites
        .iter()
        .filter(|(_, cc)| *cc == 2)
        .map(|(i, _)| *i)
        .collect();
    assert_eq!(
        (guard.len(), hs.len()),
        (1, 2),
        "not the funnel's three selects: {sites:?}"
    );
    (guard[0], [hs[0], hs[1]])
}

// ------------------------------- HOLE 2 ------------------------------------

/// WITNESS, HOLE 2. The two `HS` selects exchange their arm PAIRS:
/// `dst_lo := CSEL(hi_big, hi_normal, HS)`, `dst_hi := CSEL(zero, lo_normal,
/// HS)` for a left shift (and the mirror for the right shifts). Each select
/// still satisfies facts 1-7 — the asymmetry fact included, because it is a
/// fact about ONE select's arms — and the function returns its two limbs
/// SWAPPED (`1u128 << 0` returns `2^64`). Every select of the chain must lose
/// the whole-chain citation, in every direction, at both amount carriers.
#[test]
fn hole2_witness_exchanging_the_limb_selects_arm_pairs_is_refused() {
    let mut checked = 0;
    for (opcode, _) in I128_SHIFT_CITATIONS {
        for amount in I128_SHIFT_AMOUNT_TYPES {
            let what = format!("{opcode:?}/{amount:?}");
            let lir = i128_variable_shift_function_with_amount(opcode.clone(), amount.clone());
            let base = select(&lir);
            assert_all_three_guards_bound(&base, &lir, &format!("{what} baseline"));
            let (_, [a, b]) = shift_chain_selects(&base);
            let mut machine = base.clone();
            let arms_a: Vec<_> = machine.insts[a].operands[1..3].to_vec();
            let arms_b: Vec<_> = machine.insts[b].operands[1..3].to_vec();
            machine.insts[a].operands.splice(1..3, arms_b);
            machine.insts[b].operands.splice(1..3, arms_a);
            assert_all_refused(
                &machine,
                &lir,
                AArch64Opcode::Csel,
                &format!("{what} arm-pair swap"),
            );
            checked += 1;
        }
    }
    assert_eq!(checked, 6);
}

// ------------------------------- HOLE 3 ------------------------------------

/// The eight ORDERED integer conditions (the three-`CSET` lowering).
const ORDERED_CONDITIONS: [IntCC; 8] = [
    IntCC::SignedLessThan,
    IntCC::SignedGreaterThanOrEqual,
    IntCC::SignedGreaterThan,
    IntCC::SignedLessThanOrEqual,
    IntCC::UnsignedLessThan,
    IntCC::UnsignedGreaterThanOrEqual,
    IntCC::UnsignedGreaterThan,
    IntCC::UnsignedLessThanOrEqual,
];

/// What `CMP x, y ; CSET cc` computes, for the ten integer conditions.
fn cc_holds(cc: i64, x: u64, y: u64) -> bool {
    let (sx, sy) = (x as i64, y as i64);
    match cc {
        0 => x == y,
        1 => x != y,
        2 => x >= y,
        3 => x < y,
        8 => x > y,
        9 => x <= y,
        10 => sx >= sy,
        11 => sx < sy,
        12 => sx > sy,
        13 => sx <= sy,
        _ => panic!("cc {cc} is not an integer comparison condition"),
    }
}

/// What the ordered `select_i128_cmp` lowering computes when its three `CSET`s
/// carry `ccs` in emission order: `ORR(cset0, AND(cset1, cset2))`, the first two
/// reading the high limbs and the third the low limbs.
fn i128_cmp_lowering(ccs: [i64; 3], a: u128, b: u128) -> bool {
    let (a_hi, a_lo, b_hi, b_lo) = ((a >> 64) as u64, a as u64, (b >> 64) as u64, b as u64);
    cc_holds(ccs[0], a_hi, b_hi) || (cc_holds(ccs[1], a_hi, b_hi) && cc_holds(ccs[2], a_lo, b_lo))
}

/// The source predicate.
fn icmp_i128(cond: IntCC, a: u128, b: u128) -> bool {
    let (sa, sb) = (a as i128, b as i128);
    match cond {
        IntCC::Equal => a == b,
        IntCC::NotEqual => a != b,
        IntCC::SignedLessThan => sa < sb,
        IntCC::SignedGreaterThanOrEqual => sa >= sb,
        IntCC::SignedGreaterThan => sa > sb,
        IntCC::SignedLessThanOrEqual => sa <= sb,
        IntCC::UnsignedLessThan => a < b,
        IntCC::UnsignedGreaterThanOrEqual => a >= b,
        IntCC::UnsignedGreaterThan => a > b,
        IntCC::UnsignedLessThanOrEqual => a <= b,
    }
}

/// Probe values: equal/unequal high limbs, sign boundaries, carries.
const I128_PROBES: [u128; 8] = [
    0,
    3,
    5,
    1 << 64,
    (1 << 64) + 5,
    u128::MAX,
    1 << 127,
    (1 << 127) + 3,
];

/// A pair of probes on which the lowering with `ccs` disagrees with the source.
fn disagreement(cond: IntCC, ccs: [i64; 3]) -> Option<(u128, u128)> {
    I128_PROBES.iter().find_map(|&a| {
        I128_PROBES
            .iter()
            .find(|&&b| i128_cmp_lowering(ccs, a, b) != icmp_i128(cond, a, b))
            .map(|&b| (a, b))
    })
}

/// The condition immediates of a lowering's three `CSET`s, in order.
fn limb_cset_conditions(machine: &MachFunction) -> (Vec<usize>, [i64; 3]) {
    use trust_cg_ir::MachOperand;
    let sites = sites_of(machine, AArch64Opcode::CSet);
    assert_eq!(sites.len(), 3, "not the ordered three-CSET lowering");
    let cc = |site: usize| match machine.insts[site].operands[1] {
        MachOperand::Imm(cc) => cc,
        ref other => panic!("CSET condition is {other:?}"),
    };
    let ccs = [cc(sites[0]), cc(sites[1]), cc(sites[2])];
    (sites, ccs)
}

/// WITNESS, HOLE 3 (conditions). At emission count 3 the admissible SET is
/// `{hi_cc, EQ, lo_cc}` at EVERY position, so any permutation of the three
/// genuine conditions passed. Every permutation that changes the emitted code is
/// a real miscompile — shown on concrete operands against the source predicate,
/// so the refusal is not over-strict — and every `CSET` whose condition moved
/// must be refused.
#[test]
fn hole3_witness_the_right_limb_conditions_in_the_wrong_order_are_refused() {
    use trust_cg_ir::MachOperand;
    const PERMUTATIONS: [[usize; 3]; 5] = [[0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]];
    let mut checked = 0;
    for cond in ORDERED_CONDITIONS {
        let lir = icmp_function(Type::I128, cond);
        let base = select(&lir);
        let (sites, genuine) = limb_cset_conditions(&base);
        assert!(
            bound_rows(&base, &lir, AArch64Opcode::CSet)
                .iter()
                .all(|bound| *bound),
            "{cond:?}: the genuine limb CSETs must stay bound"
        );
        assert_eq!(
            disagreement(cond, genuine),
            None,
            "{cond:?}: the evaluator disagrees with the GENUINE lowering {genuine:?}"
        );
        for permutation in PERMUTATIONS {
            let permuted = permutation.map(|from| genuine[from]);
            if permuted == genuine {
                continue;
            }
            let (a, b) = disagreement(cond, permuted).unwrap_or_else(|| {
                panic!("{cond:?}: {permuted:?} is equivalent to the source — not a witness")
            });
            let mut machine = base.clone();
            for (slot, site) in sites.iter().enumerate() {
                machine.insts[*site].operands[1] = MachOperand::Imm(permuted[slot]);
            }
            let refused = refused_rows(&machine, &lir, AArch64Opcode::CSet);
            for slot in 0..3 {
                if permuted[slot] != genuine[slot] {
                    assert!(
                        refused[slot],
                        "{cond:?}: {permuted:?} (wrong at a={a:#x}, b={b:#x}) kept position {slot} bound"
                    );
                }
            }
            checked += 1;
        }
    }
    // 8 conditions; the unsigned `<`/`>` forms repeat a condition (hi_cc ==
    // lo_cc), so fewer of their permutations change the code.
    assert!(checked >= 24, "only {checked} permutations exercised");
}

/// WITNESS, HOLE 3 (roles). The two HIGH-limb `CSET`s read the same flags and
/// write different registers, so their ORDER is free — which is why a positional
/// binding cannot close hole 3. Exchanging only their DESTINATIONS leaves every
/// position carrying its genuine condition (`CSET hi_eq, LT ; CSET hi_cond, EQ`
/// for a signed `<`) and computes `hi_a == hi_b || (hi_a < hi_b && ...)`. The
/// role binding keys on what READS each value, so both are refused.
#[test]
fn hole3_witness_exchanging_the_high_limb_csets_destinations_is_refused() {
    let mut checked = 0;
    for cond in ORDERED_CONDITIONS {
        let lir = icmp_function(Type::I128, cond);
        let base = select(&lir);
        let (sites, genuine) = limb_cset_conditions(&base);
        let swapped_roles = [genuine[1], genuine[0], genuine[2]];
        assert!(
            disagreement(cond, swapped_roles).is_some(),
            "{cond:?}: exchanging the high CSETs' roles is not observable"
        );
        let mut machine = base.clone();
        let first = machine.insts[sites[0]].operands[0].clone();
        let second = machine.insts[sites[1]].operands[0].clone();
        machine.insts[sites[0]].operands[0] = second;
        machine.insts[sites[1]].operands[0] = first;
        let refused = refused_rows(&machine, &lir, AArch64Opcode::CSet);
        assert!(
            refused[0] && refused[1],
            "{cond:?}: a high-limb CSET writing the other's role is still bound: {refused:?}"
        );
        assert!(
            bound_rows(&machine, &lir, AArch64Opcode::CSet)[2],
            "{cond:?}: the untouched low-limb CSET lost its binding"
        );
        checked += 1;
    }
    assert_eq!(checked, 8);
}

/// WITNESS, HOLE 3 (the `EQ`/`NE` combiner). The two-`CSET` equality forms
/// carry the SAME condition at both positions, so no permutation of them is a
/// witness — but their ROLE still includes what COMBINES them: `a == b` is
/// `hi_eq AND lo_eq`, `a != b` is `hi_ne ORR lo_ne`. Exchanging the combiner
/// keeps every `CSET` condition, every reaching `CMP` and every position, and
/// computes `hi_eq OR lo_eq` — true for `a = 1, b = 0`. Both limb `CSET`s must
/// lose the `Icmp_Eq_I64`/`Icmp_NE_I64` citation.
#[test]
fn hole3_witness_an_equality_combined_by_the_wrong_combiner_is_refused() {
    let mut checked = 0;
    for (cond, genuine, swapped) in [
        (IntCC::Equal, AArch64Opcode::AndRR, AArch64Opcode::OrrRR),
        (IntCC::NotEqual, AArch64Opcode::OrrRR, AArch64Opcode::AndRR),
    ] {
        let lir = icmp_function(Type::I128, cond);
        let base = select(&lir);
        let rows = bound_rows(&base, &lir, AArch64Opcode::CSet);
        assert_eq!(rows.len(), 2, "{cond:?}: not the two-CSET lowering");
        assert!(
            rows.iter().all(|bound| *bound),
            "{cond:?}: the genuine limb CSETs must stay bound"
        );
        let combiners = sites_of(&base, genuine);
        assert_eq!(
            combiners.len(),
            1,
            "{cond:?}: one {genuine:?} combines the limbs"
        );
        // Observable: with the other combiner, `a = 1, b = 0` (equal high
        // limbs, different low limbs) flips the answer.
        let (hi_eq, lo_eq) = (true, false);
        let wrong = if swapped == AArch64Opcode::OrrRR {
            // `EQ` limbs ORed: hi_eq | lo_eq.
            hi_eq || lo_eq
        } else {
            // `NE` limbs ANDed: hi_ne & lo_ne.
            !hi_eq && !lo_eq
        };
        assert_ne!(
            wrong,
            icmp_i128(cond, 1, 0),
            "{cond:?}: the swap is not observable"
        );
        let mut machine = base.clone();
        machine.insts[combiners[0]].opcode = swapped;
        assert_all_refused(
            &machine,
            &lir,
            AArch64Opcode::CSet,
            &format!("{cond:?} combined by {swapped:?}"),
        );
        checked += 1;
    }
    assert_eq!(checked, 2);
}

// ------------------------------- HOLE 4 ------------------------------------

/// The `ORR` of a lowered chain, and the operand slot holding the `EQ` guard's
/// (guarded spill's) register.
fn chain_orr_spill_slot(machine: &MachFunction) -> (usize, usize) {
    let (guard, _) = shift_chain_selects(machine);
    let spill = machine.insts[guard].operands[0].clone();
    let orrs = sites_of(machine, AArch64Opcode::OrrRR);
    assert_eq!(orrs.len(), 1, "the funnel has one ORR");
    let slot = (1..3)
        .find(|slot| machine.insts[orrs[0]].operands[*slot] == spill)
        .expect("the funnel ORR reads the guarded spill");
    (orrs[0], slot)
}

/// WITNESS, HOLE 4 (data flow). The funnel `ORR` combines the RAW spill instead
/// of the guarded one: `hi_normal = (hi << s) | (lo >> (64 - s))` with no `s ==
/// 0` override. AArch64 register shifts mask the amount by 63, so at `s == 0`
/// the raw spill is `lo >> 0 = lo` and `1u128 << 0` gains `2^64` in its high
/// limb — the exact bug the guard exists to prevent. Facts 1-7 only ask that
/// the combined arm IS an `ORR`, so the base credits it.
#[test]
fn hole4_witness_a_funnel_that_ors_in_the_unguarded_spill_is_refused() {
    let mut checked = 0;
    for (opcode, _) in I128_SHIFT_CITATIONS {
        for amount in I128_SHIFT_AMOUNT_TYPES {
            let what = format!("{opcode:?}/{amount:?}");
            let lir = i128_variable_shift_function_with_amount(opcode.clone(), amount.clone());
            let base = select(&lir);
            assert_all_three_guards_bound(&base, &lir, &format!("{what} baseline"));
            let (guard, _) = shift_chain_selects(&base);
            let (orr, slot) = chain_orr_spill_slot(&base);
            let mut machine = base.clone();
            machine.insts[orr].operands[slot] = base.insts[guard].operands[2].clone();
            assert_all_refused(
                &machine,
                &lir,
                AArch64Opcode::Csel,
                &format!("{what} raw spill"),
            );
            checked += 1;
        }
    }
    assert_eq!(checked, 6);
}

/// WITNESS, HOLE 4 (source limbs). Every limb shift of the chain reads the
/// source's low and high limbs EXCHANGED. The chain is internally consistent —
/// one value everywhere the theorem says `lo`, one everywhere it says `hi` — so
/// a check that only compared the chain against itself would accept it; it
/// shifts `(lo : hi)` instead of `(hi : lo)`. The limbs must be the shifted
/// operand's own AAPCS64 register pair.
#[test]
fn hole4_witness_a_chain_reading_the_source_limbs_exchanged_is_refused() {
    let mut checked = 0;
    for (opcode, _) in I128_SHIFT_CITATIONS {
        for amount in I128_SHIFT_AMOUNT_TYPES {
            let what = format!("{opcode:?}/{amount:?}");
            let lir = i128_variable_shift_function_with_amount(opcode.clone(), amount.clone());
            let base = select(&lir);
            assert_all_three_guards_bound(&base, &lir, &format!("{what} baseline"));
            let shifts: Vec<usize> = base
                .insts
                .iter()
                .enumerate()
                .filter(|(_, inst)| {
                    matches!(
                        inst.opcode,
                        AArch64Opcode::LslRR | AArch64Opcode::LsrRR | AArch64Opcode::AsrRR
                    )
                })
                .map(|(index, _)| index)
                .collect();
            let mut limbs = Vec::new();
            for &site in &shifts {
                let value = base.insts[site].operands[1].clone();
                if !limbs.contains(&value) {
                    limbs.push(value);
                }
            }
            assert_eq!(
                limbs.len(),
                2,
                "{what}: the funnel shifts exactly two limbs"
            );
            let mut machine = base.clone();
            for &site in &shifts {
                let value = &mut machine.insts[site].operands[1];
                *value = if *value == limbs[0] {
                    limbs[1].clone()
                } else {
                    limbs[0].clone()
                };
            }
            assert_all_refused(
                &machine,
                &lir,
                AArch64Opcode::Csel,
                &format!("{what} limbs exchanged"),
            );
            checked += 1;
        }
    }
    assert_eq!(checked, 6);
}

/// The PRODUCTION shape of the amount: `core` masks every 128-bit shift count
/// (`And(count, 127)`, `unchecked_shl`'s own LIR), and the chain shifts by that
/// masked value.
fn masked_i128_variable_shift_function(opcode: Opcode) -> Function {
    source_function(
        "i128_masked_shift_fixture",
        vec![Type::I128, Type::I32],
        vec![
            Instruction {
                opcode: Opcode::Iconst {
                    ty: Type::I32,
                    imm: 127,
                },
                args: vec![],
                results: vec![Value(4)],
            },
            Instruction {
                opcode: Opcode::Band,
                args: vec![Value(1), Value(4)],
                results: vec![Value(5)],
            },
            Instruction {
                opcode,
                args: vec![Value(0), Value(5)],
                results: vec![Value(10)],
            },
        ],
        10,
        Type::I128,
        vec![(4, Type::I32), (5, Type::I32), (10, Type::I128)],
    )
}

/// The masked (production) fixture's genuine chain is bound, and the
/// source-bound binding selects this direction's whole-chain obligation.
#[test]
fn every_masked_i128_variable_shift_csel_is_bound() {
    for (opcode, expected) in I128_SHIFT_CITATIONS {
        let lir = masked_i128_variable_shift_function(opcode.clone());
        let machine = select(&lir);
        assert_all_three_guards_bound(&machine, &lir, &format!("{opcode:?} masked"));
        let own = expected.to_lowercase();
        assert_eq!(
            source_bound_selections(&machine, &lir, AArch64Opcode::Csel),
            vec![Some(own.as_str()); 3],
            "{opcode:?} masked: not bound to {expected}"
        );
    }
}

/// WITNESS, HOLE 4 (amount). The chain compares and shifts by the RAW count
/// instead of the masked one — every use at once, so the chain is internally
/// consistent and facts 1-7 (which compare each shift's amount with the guard's
/// own compared register) hold. At `count = 128` the source shifts by `128 & 127
/// = 0` and returns its operand; the chain takes the `>= 64` path and returns
/// `(lo : 0)`. The amount must be the source's amount operand: here, the value
/// its `Band` wrote.
#[test]
fn hole4_witness_a_chain_shifting_by_the_unmasked_amount_is_refused() {
    let mut checked = 0;
    for (opcode, _) in I128_SHIFT_CITATIONS {
        let lir = masked_i128_variable_shift_function(opcode.clone());
        let base = select(&lir);
        assert_all_three_guards_bound(&base, &lir, &format!("{opcode:?} masked baseline"));
        let ands = sites_of(&base, AArch64Opcode::AndRI);
        assert_eq!(ands.len(), 1, "{opcode:?}: the mask lowers to one AND");
        let masked = base.insts[ands[0]].operands[0].clone();
        let raw = base.insts[ands[0]].operands[1].clone();
        let mut machine = base.clone();
        let mut rewired = 0;
        for inst in machine.insts.iter_mut().skip(ands[0] + 1) {
            for operand in inst.operands.iter_mut() {
                if *operand == masked {
                    *operand = raw.clone();
                    rewired += 1;
                }
            }
        }
        assert!(
            rewired >= 6,
            "{opcode:?}: only {rewired} amount uses rewired"
        );
        assert_all_refused(
            &machine,
            &lir,
            AArch64Opcode::Csel,
            &format!("{opcode:?} unmasked"),
        );
        checked += 1;
    }
    assert_eq!(checked, 3);
}

// --------------------- THE PRODUCTION SHAPE, ALLOCATED ----------------------

/// `<u128>::unchecked_shl` exactly as `library/core` compiles it at `-O0`
/// (dumped from the backend at `572c4ce34`): four blocks, the UB-check call and
/// the precondition call, the source limbs parked in callee-saved `x19`/`x20`
/// across both calls, the count masked in block 3, the funnel, and the result
/// returned through a coalesced `NOP x0, x0` and `MOV x1, x2` past the
/// epilogue's `LDP`s. This is the one root `2e194289f` cleared; it must stay
/// bound with every new fact, and the arm-pair swap must still be refused on it.
fn production_unchecked_shl() -> (Function, MachFunction) {
    use trust_cg_ir::function::Type as M;
    use trust_cg_ir::provenance::{SourceInstId, SyntheticReason};
    use trust_cg_ir::{BlockId, LoweringProvenance, MachInst, MachOperand, PReg, SpecialReg};
    use trust_cg_lower::function::Signature;

    let v = |n: u32| Value(n);
    let inst = |opcode, args: Vec<Value>, results: Vec<Value>| Instruction {
        opcode,
        args,
        results,
    };
    let name = "_RNvMs8_NtCsbmub5fGRlIb_4core3numo13unchecked_shl";
    let mut lir = Function::new(
        name,
        Signature {
            params: vec![Type::I128, Type::I32, Type::I64],
            returns: vec![Type::I128],
        },
    );
    let call = |callee: &str| Opcode::Call {
        name: callee.to_string(),
        binding: Default::default(),
    };
    let blocks = [
        (
            vec![(v(0), Type::I128), (v(1), Type::I32), (v(2), Type::I64)],
            vec![
                inst(call("check_language_ub"), vec![], vec![v(3)]),
                inst(Opcode::Jump { dest: Block(1) }, vec![], vec![]),
            ],
        ),
        (
            vec![],
            vec![inst(
                Opcode::Brif {
                    cond: v(3),
                    then_dest: Block(2),
                    else_dest: Block(3),
                },
                vec![v(3)],
                vec![],
            )],
        ),
        (
            vec![],
            vec![
                inst(call("precondition_check"), vec![v(1), v(2)], vec![]),
                inst(Opcode::Jump { dest: Block(3) }, vec![], vec![]),
            ],
        ),
        (
            vec![],
            vec![
                inst(
                    Opcode::Iconst {
                        ty: Type::I32,
                        imm: 127,
                    },
                    vec![],
                    vec![v(4)],
                ),
                inst(Opcode::Band, vec![v(1), v(4)], vec![v(5)]),
                inst(Opcode::Ishl, vec![v(0), v(5)], vec![v(6)]),
                inst(Opcode::Return, vec![v(6)], vec![]),
            ],
        ),
    ];
    for (index, (params, instructions)) in blocks.into_iter().enumerate() {
        let count = instructions.len();
        lir.blocks.insert(
            Block(index as u32),
            BasicBlock {
                params,
                source_locs: vec![None; count],
                instructions,
            },
        );
        lir.block_order.push(Block(index as u32));
    }
    // NO `value_types`: the production LIR records no type for these results
    // (measured — the masked count `v5` reached the binding untyped), so the
    // amount's scalar type must come from the typing rule, not a recorded
    // table. A fixture that recorded them passed while production refused.

    let x = |n: u16| MachOperand::PReg(PReg::new(n));
    let w = |n: u16| MachOperand::PReg(PReg::new(32 + n));
    let i = MachOperand::Imm;
    let sp = MachOperand::Special(SpecialReg::SP);
    let block = MachOperand::Block;
    let unattributed = LoweringProvenance::Synthetic {
        reason: SyntheticReason::Unattributed,
    };
    let formal = LoweringProvenance::Synthetic {
        reason: SyntheticReason::FormalArguments,
    };
    // (opcode, operands, provenance: None = synthetic kind, Some((block, index)))
    type Row = (
        AArch64Opcode,
        Vec<MachOperand>,
        Result<(u32, u32), LoweringProvenance>,
    );
    use AArch64Opcode as A;
    let rows: [Vec<Row>; 4] = [
        vec![
            (
                A::StpPreIndex,
                vec![x(22), x(21), sp.clone(), i(-48)],
                Err(unattributed),
            ),
            (
                A::StpRI,
                vec![x(20), x(19), sp.clone(), i(16)],
                Err(unattributed),
            ),
            (
                A::StpRI,
                vec![x(29), x(30), sp.clone(), i(32)],
                Err(unattributed),
            ),
            (A::AddRI, vec![x(29), sp.clone(), i(32)], Err(unattributed)),
            (A::MOVXrr, vec![x(19), x(0)], Err(formal)),
            (A::MOVXrr, vec![x(20), x(1)], Err(formal)),
            (A::MOVWrr, vec![w(21), x(2)], Err(formal)),
            (A::MOVXrr, vec![x(22), x(3)], Err(formal)),
            (
                A::Bl,
                vec![MachOperand::Symbol("check_language_ub".into())],
                Ok((0, 0)),
            ),
            (A::Nop, vec![x(0), x(0)], Ok((0, 0))),
            (A::Uxtb, vec![x(1), x(0)], Ok((0, 0))),
            (A::B, vec![block(BlockId(1))], Ok((0, 1))),
        ],
        vec![
            (A::CmpRI, vec![x(1), i(0)], Ok((1, 0))),
            (A::BCond, vec![i(1), block(BlockId(2))], Ok((1, 0))),
            (A::B, vec![block(BlockId(3))], Ok((1, 0))),
        ],
        vec![
            (A::MOVWrr, vec![w(0), w(21)], Ok((2, 0))),
            (A::MOVXrr, vec![x(1), x(22)], Ok((2, 0))),
            (
                A::Bl,
                vec![MachOperand::Symbol("precondition_check".into())],
                Ok((2, 0)),
            ),
            (A::B, vec![block(BlockId(3))], Ok((2, 1))),
        ],
        vec![
            (A::Movz, vec![w(0), i(127)], Ok((3, 0))),
            (A::AndRI, vec![w(0), w(21), i(127)], Ok((3, 1))),
            (A::Movz, vec![x(1), i(64)], Ok((3, 2))),
            (A::Movz, vec![x(2), i(0)], Ok((3, 2))),
            (A::SubRR, vec![x(3), x(1), w(0)], Ok((3, 2))),
            (A::LsrRR, vec![x(4), x(19), x(3)], Ok((3, 2))),
            (A::CmpRI, vec![w(0), i(0)], Ok((3, 2))),
            (A::Csel, vec![x(3), x(2), x(4), i(0)], Ok((3, 2))),
            (A::LslRR, vec![x(4), x(20), w(0)], Ok((3, 2))),
            (A::OrrRR, vec![x(5), x(4), x(3)], Ok((3, 2))),
            (A::LslRR, vec![x(3), x(19), w(0)], Ok((3, 2))),
            (A::SubRR, vec![x(4), w(0), x(1)], Ok((3, 2))),
            (A::LslRR, vec![x(1), x(19), x(4)], Ok((3, 2))),
            (A::CmpRI, vec![w(0), i(64)], Ok((3, 2))),
            (A::Csel, vec![x(0), x(2), x(3), i(2)], Ok((3, 2))),
            (A::Csel, vec![x(2), x(1), x(5), i(2)], Ok((3, 2))),
            (A::Nop, vec![x(0), x(0)], Ok((3, 3))),
            (A::MOVXrr, vec![x(1), x(2)], Ok((3, 3))),
            (
                A::LdpRI,
                vec![x(29), x(30), sp.clone(), i(32)],
                Err(unattributed),
            ),
            (
                A::LdpRI,
                vec![x(20), x(19), sp.clone(), i(16)],
                Err(unattributed),
            ),
            (
                A::LdpPostIndex,
                vec![x(22), x(21), sp.clone(), i(48)],
                Err(unattributed),
            ),
            (A::Ret, vec![x(30)], Ok((3, 3))),
        ],
    ];
    let mut machine = MachFunction::new(
        name.to_string(),
        trust_cg_ir::function::Signature::new(vec![M::I128, M::I32, M::I64], vec![M::I128]),
    );
    for _ in 1..4 {
        machine.create_block();
    }
    for (index, rows) in rows.into_iter().enumerate() {
        for (opcode, operands, provenance) in rows {
            let id = machine.push_inst(MachInst::new(opcode, operands));
            machine.append_inst(BlockId(index as u32), id);
            let provenance = match provenance {
                Ok((block, position)) => LoweringProvenance::SourceInst {
                    id: SourceInstId {
                        block,
                        index: position,
                    },
                    digest: lir.blocks[&Block(block)].instructions[position as usize]
                        .lowering_digest(),
                    trust_ir_inst: None,
                },
                Err(synthetic) => synthetic,
            };
            machine.set_inst_lowering_provenance(id, provenance);
        }
    }
    let edge = |machine: &mut MachFunction, from: u32, to: u32| {
        machine.blocks[from as usize].succs.push(BlockId(to));
        machine.blocks[to as usize].preds.push(BlockId(from));
    };
    edge(&mut machine, 0, 1);
    edge(&mut machine, 1, 2);
    edge(&mut machine, 1, 3);
    edge(&mut machine, 2, 3);
    (lir, machine)
}

/// POSITIVE: the production chain is bound — its limbs traced back across two
/// calls in callee-saved registers to `x0`/`x1` on entry, its amount to the
/// `Band`, its results forward past the epilogue to `x0`/`x1` at `RET` — and
/// all three selects are bound to `Ishl_I128`.
#[test]
fn the_production_unchecked_shl_chain_is_bound() {
    let (lir, machine) = production_unchecked_shl();
    let rows = rows_for(&machine, &lir, AArch64Opcode::Csel);
    assert_eq!(rows.len(), 3);
    assert!(
        rows.iter().all(is_bound),
        "production unchecked_shl guard refused: {rows:?}"
    );
    assert_eq!(
        source_bound_selections(&machine, &lir, AArch64Opcode::Csel),
        vec![Some("ishl_i128"); 3],
        "production unchecked_shl guards not bound to Ishl_I128"
    );
}

/// WITNESSES, HOLES 2 and 4, on the production shape: the arm-pair swap of the
/// two limb selects (positions 14/15 of block 3), and the source limbs `x19`
/// and `x20` exchanged in every funnel shift.
#[test]
fn the_production_unchecked_shl_refuses_the_hole_witnesses() {
    use trust_cg_ir::{MachOperand, PReg};
    let (lir, base) = production_unchecked_shl();
    let block3 = &base.blocks[3].insts;
    let (lo, hi) = (block3[14].0 as usize, block3[15].0 as usize);
    let mut swapped = base.clone();
    let arms_lo: Vec<_> = swapped.insts[lo].operands[1..3].to_vec();
    let arms_hi: Vec<_> = swapped.insts[hi].operands[1..3].to_vec();
    swapped.insts[lo].operands.splice(1..3, arms_hi);
    swapped.insts[hi].operands.splice(1..3, arms_lo);
    assert_all_refused(
        &swapped,
        &lir,
        AArch64Opcode::Csel,
        "production arm-pair swap",
    );

    let (x19, x20) = (
        MachOperand::PReg(PReg::new(19)),
        MachOperand::PReg(PReg::new(20)),
    );
    let mut exchanged = base.clone();
    for id in block3 {
        let inst = &mut exchanged.insts[id.0 as usize];
        if matches!(inst.opcode, AArch64Opcode::LslRR | AArch64Opcode::LsrRR) {
            if inst.operands[1] == x19 {
                inst.operands[1] = x20.clone();
            } else if inst.operands[1] == x20 {
                inst.operands[1] = x19.clone();
            }
        }
    }
    assert_all_refused(
        &exchanged,
        &lir,
        AArch64Opcode::Csel,
        "production limbs exchanged",
    );
}

/// WITNESSES, HOLE 4 (limb width), on the production shape. `MOVWrr` is a
/// 32-bit move whatever register views its operands name — the encoder takes
/// `sf = 0` from the OPCODE — so it zero-extends the low word and drops the
/// high one. Turning any limb copy into one keeps every opcode shape, operand
/// register and stamp of the chain, and truncates a 64-bit limb: the two
/// source-limb homes (`x19`/`x20` on entry) and the two result-limb moves
/// (`MOV x1, x2` and the coalesced `NOP x0, x0`) before `RET`. The limb walk
/// followed the copy because its operands NAME 64-bit registers; it must stop
/// at a copy whose opcode is narrower than the limb.
#[test]
fn the_production_unchecked_shl_refuses_a_truncating_limb_copy() {
    let (lir, base) = production_unchecked_shl();
    for (what, block, position, before) in [
        (
            "low source limb, MOVWrr x19, x0",
            0,
            4,
            AArch64Opcode::MOVXrr,
        ),
        (
            "high source limb, MOVWrr x20, x1",
            0,
            5,
            AArch64Opcode::MOVXrr,
        ),
        ("low result limb, MOVWrr x0, x0", 3, 16, AArch64Opcode::Nop),
        (
            "high result limb, MOVWrr x1, x2",
            3,
            17,
            AArch64Opcode::MOVXrr,
        ),
    ] {
        let mut machine = base.clone();
        let id = machine.blocks[block].insts[position].0 as usize;
        assert_eq!(machine.insts[id].opcode, before, "{what}: fixture moved");
        machine.insts[id].opcode = AArch64Opcode::MOVWrr;
        assert_all_refused(&machine, &lir, AArch64Opcode::Csel, what);
    }
}
