// trust-cg-verify/tests/x86_volatile_trace_gate.rs - the x86-64 volatile ACCESS TRACE obligation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The gate for [`trust_cg_verify::x86_volatile_trace`].
//!
//! The obligation: every volatile access the source asks for is emitted exactly
//! once, at the same width, in the same direction, through the same register
//! file, and in the same order within each block.
//!
//! The battery below is the point. A trace comparison that cannot refute an
//! elided access is not evidence, so each of the six ways a compiler breaks
//! volatile gets its own control and each must be refuted FOR ITS OWN REASON.

use trust_cg_verify::x86_volatile_trace as vt;
use vt::{AccessClass, VolatileAccess, VolatileTrace, VolatileTraceViolation};

fn acc(width_bits: u32, is_store: bool, class: AccessClass) -> VolatileAccess {
    VolatileAccess {
        width_bits,
        is_store,
        class,
    }
}

/// A two-block trace: `[load8, store32]` then `[loadF64]`.
fn baseline() -> VolatileTrace {
    VolatileTrace {
        per_block: vec![
            vec![
                acc(8, false, AccessClass::Gpr),
                acc(32, true, AccessClass::Gpr),
            ],
            vec![acc(64, false, AccessClass::Fp)],
        ],
    }
}

#[test]
fn an_unchanged_trace_holds() {
    let t = baseline();
    let holds = vt::volatile_trace_holds(&t, &t, true).expect("an identical trace must hold");
    assert_eq!(holds.accesses, 3);
    assert_eq!(holds.shapes, 3);
    assert_eq!(holds.blocks_ordered, 2);
}

/// EVERY hazard refutes, each for its own reason.
#[test]
fn every_volatile_hazard_refutes_for_its_own_reason() {
    let source = baseline();

    // (1) ELIDE — the classic: a redundant-load pass removes the second access.
    let mut elided = baseline();
    elided.per_block[0].remove(1);
    assert!(
        matches!(
            vt::volatile_trace_holds(&source, &elided, true),
            Err(VolatileTraceViolation::Elided { .. })
        ),
        "an elided volatile access must refute AS an elision"
    );

    // (2) DUPLICATE — an unrolling or rematerialising pass clones one.
    let mut duplicated = baseline();
    duplicated.per_block[1].push(acc(64, false, AccessClass::Fp));
    assert!(
        matches!(
            vt::volatile_trace_holds(&source, &duplicated, true),
            Err(VolatileTraceViolation::Duplicated { .. })
        ),
        "a duplicated volatile access must refute AS a duplication"
    );

    // (3) WIDEN — an i8 load becomes an i32 load. Caught TWICE: the i8 is
    //     elided and the i32 was never asked for. Either is a correct refusal;
    //     the elision is reported first because it is checked first.
    let mut widened = baseline();
    widened.per_block[0][0] = acc(32, false, AccessClass::Gpr);
    assert!(
        matches!(
            vt::volatile_trace_holds(&source, &widened, true),
            Err(VolatileTraceViolation::Elided { .. } | VolatileTraceViolation::Unasked { .. })
        ),
        "a widened volatile access must refute"
    );

    // (4) NARROW — the reverse.
    let mut narrowed = baseline();
    narrowed.per_block[0][1] = acc(8, true, AccessClass::Gpr);
    assert!(
        matches!(
            vt::volatile_trace_holds(&source, &narrowed, true),
            Err(VolatileTraceViolation::Elided { .. } | VolatileTraceViolation::Unasked { .. })
        ),
        "a narrowed volatile access must refute"
    );

    // (5) REDIRECT — a store becomes a load of the same width.
    let mut redirected = baseline();
    redirected.per_block[0][1] = acc(32, false, AccessClass::Gpr);
    assert!(
        matches!(
            vt::volatile_trace_holds(&source, &redirected, true),
            Err(VolatileTraceViolation::Elided { .. } | VolatileTraceViolation::Unasked { .. })
        ),
        "a volatile store emitted as a load must refute"
    );

    // (6) REORDER — two accesses in one block swap. The MULTISET is unchanged,
    //     so this is exactly the hazard the per-block sequence exists for.
    let mut reordered = baseline();
    reordered.per_block[0].swap(0, 1);
    assert_eq!(
        reordered.multiset(),
        source.multiset(),
        "the reorder control must leave the multiset UNCHANGED, or it is testing the wrong thing"
    );
    assert!(
        matches!(
            vt::volatile_trace_holds(&source, &reordered, true),
            Err(VolatileTraceViolation::Reordered { .. })
        ),
        "two reordered volatile accesses must refute AS a reordering"
    );

    // (7) CLASS CHANGE — an f64 volatile load lowered through a GPR moves the
    //     same bytes and is still the wrong access.
    let mut reclassed = baseline();
    reclassed.per_block[1][0] = acc(64, false, AccessClass::Gpr);
    assert!(
        vt::volatile_trace_holds(&source, &reclassed, true).is_err(),
        "a volatile access moved through the wrong register file must refute"
    );
}

/// A LAYOUT change must NOT refute.
///
/// This is the counterpart the battery needs: a check that refutes everything
/// is no more useful than one that refutes nothing. `X86BranchLayout`'s
/// cold-arm sink permutes `block_order` without changing execution order, and
/// the function-level multiset is deliberately invariant under that.
#[test]
fn a_block_layout_permutation_does_not_refute() {
    let source = baseline();
    let permuted = VolatileTrace {
        per_block: vec![source.per_block[1].clone(), source.per_block[0].clone()],
    };
    assert_eq!(
        vt::volatile_trace_holds(&source, &permuted, false)
            .expect("a pure layout permutation must NOT be reported as a volatile violation")
            .accesses,
        3
    );
}

/// The recognised opcode set is COMPLETE against the coverage gate's own
/// volatile rows.
///
/// This is the one way the trace could pass while missing an access: an opcode
/// the backend emits that `volatile_access_of_opcode` returns `None` for is
/// invisible to the comparison. Pinning the set against the gate's row list
/// makes a newly added volatile opcode a FAILURE here rather than a silent hole.
#[test]
fn every_volatile_opcode_the_gate_counts_is_recognised_by_the_trace() {
    use trust_cg_verify::coverage_gate::ALL_X86_OPCODES;

    let mut unrecognised: Vec<String> = Vec::new();
    let mut recognised = 0usize;
    for &opcode in ALL_X86_OPCODES {
        if !format!("{opcode:?}").starts_with("Volatile") {
            continue;
        }
        match vt::volatile_access_of_opcode(opcode) {
            Some(_) => recognised += 1,
            None => unrecognised.push(format!("{opcode:?}")),
        }
    }
    assert!(
        unrecognised.is_empty(),
        "these volatile opcodes are INVISIBLE to the volatile trace, so an access through them \
         could be elided without the obligation noticing: {unrecognised:?}"
    );
    assert_eq!(
        recognised,
        vt::RECOGNISED_VOLATILE_OPCODES.len(),
        "the published set and the opcodes actually recognised have drifted"
    );
    assert_eq!(
        recognised, 18,
        "the x86 volatile surface is eighteen opcodes: the sixteen MOV forms and the two \
         zero-extending loads (`VolatileMovzxRM8`, `VolatileMovzxRM16`)"
    );
}

/// Each recognised opcode reads back the width and direction its NAME states.
///
/// Cheap, and it is the facet a copy-paste error in the table would break: a
/// `VolatileMovRM16` arm returning width 32 would make a widened access look
/// correct.
#[test]
fn each_volatile_opcode_reads_back_the_access_its_name_states() {
    use trust_cg_ir::X86Opcode as O;
    let cases = [
        (O::VolatileMovRM8, 8, false, AccessClass::Gpr),
        (O::VolatileMovRM16, 16, false, AccessClass::Gpr),
        (O::VolatileMovRM32, 32, false, AccessClass::Gpr),
        (O::VolatileMovRM, 64, false, AccessClass::Gpr),
        (O::VolatileMovMR8, 8, true, AccessClass::Gpr),
        (O::VolatileMovMR16, 16, true, AccessClass::Gpr),
        (O::VolatileMovMR32, 32, true, AccessClass::Gpr),
        (O::VolatileMovMR, 64, true, AccessClass::Gpr),
        (O::VolatileMovssRM, 32, false, AccessClass::Fp),
        (O::VolatileMovsdRM, 64, false, AccessClass::Fp),
        (O::VolatileMovssMR, 32, true, AccessClass::Fp),
        (O::VolatileMovsdMR, 64, true, AccessClass::Fp),
        (O::VolatileMovdquRM, 128, false, AccessClass::V128),
        (O::VolatileMovdqaRM, 128, false, AccessClass::V128),
        (O::VolatileMovdquMR, 128, true, AccessClass::V128),
        (O::VolatileMovdqaMR, 128, true, AccessClass::V128),
        (O::VolatileMovzxRM8, 8, false, AccessClass::Gpr),
        (O::VolatileMovzxRM16, 16, false, AccessClass::Gpr),
    ];
    for (opcode, width, is_store, class) in cases {
        assert_eq!(
            vt::volatile_access_of_opcode(opcode),
            Some(acc(width, is_store, class)),
            "{opcode:?} reads back the wrong access"
        );
    }
    // And a PLAIN opcode is not mistaken for a volatile one — the trace must
    // not count accesses the source never marked.
    for plain in [
        O::MovRM,
        O::MovzxRM8,
        O::MovzxRM16,
        O::MovMR8,
        O::MovsdRM,
        O::MovdquMR,
        O::Lea,
    ] {
        assert_eq!(
            vt::volatile_access_of_opcode(plain),
            None,
            "{plain:?} is NOT a volatile access and must not enter the trace"
        );
    }
}

/// THE PER-COMPILE CHECK HAS TEETH.
///
/// The obligation above is exercised on hand-built traces. This pins the thing
/// that matters in production: the comparison is run against a REAL emitted
/// function, and a volatile access removed from that function is refused.
///
/// The machine side is read with the same `machine_volatile_trace` the compiler
/// calls, so this is the production extractor and not a test-only mirror.
#[test]
fn a_volatile_access_deleted_from_a_real_function_is_refused() {
    use trust_cg_ir::{X86Opcode, X86PReg};
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::instructions::Block;
    use trust_cg_lower::x86_64_isel::{X86ISelBlock, X86ISelFunction, X86ISelInst, X86ISelOperand};

    let preg = |n: u16| X86ISelOperand::PReg(X86PReg::new(n));
    let mem = |base: u16| X86ISelOperand::MemAddr {
        base: Box::new(preg(base)),
        disp: 0,
    };
    let build = |opcodes: &[X86Opcode]| {
        let mut func = X86ISelFunction::new(
            "volatile_probe".to_string(),
            Signature {
                params: vec![],
                returns: vec![],
            },
        );
        let b = Block(0);
        func.ensure_block(b);
        let block: &mut X86ISelBlock = func.blocks.get_mut(&b).unwrap();
        for &op in opcodes {
            block
                .insts
                .push(X86ISelInst::new(op, vec![preg(0), mem(3)]));
        }
        func
    };

    // A function performing three volatile accesses, plus a plain one that must
    // not enter the trace at all.
    let full = build(&[
        X86Opcode::VolatileMovRM8,
        X86Opcode::MovRM,
        X86Opcode::VolatileMovMR32,
        X86Opcode::VolatileMovsdRM,
    ]);
    let before = vt::machine_volatile_trace(&full);
    assert_eq!(
        before.len(),
        3,
        "the plain MovRM must NOT be counted as a volatile access"
    );

    // Unchanged: holds.
    assert!(
        vt::volatile_trace_holds(&before, &vt::machine_volatile_trace(&full), true).is_ok(),
        "an unmodified function must hold"
    );

    // ELIDED: the middle volatile access is deleted, as a redundant-store pass
    // would. Must refuse.
    let elided = build(&[
        X86Opcode::VolatileMovRM8,
        X86Opcode::MovRM,
        X86Opcode::VolatileMovsdRM,
    ]);
    let violation = vt::volatile_trace_holds(&before, &vt::machine_volatile_trace(&elided), true)
        .expect_err("a deleted volatile access must be REFUSED");
    assert!(
        matches!(violation, VolatileTraceViolation::Elided { .. }),
        "expected an Elided violation, got {violation}"
    );

    // WIDENED: the i8 load becomes an i32 load. Must refuse.
    let widened = build(&[
        X86Opcode::VolatileMovRM32,
        X86Opcode::MovRM,
        X86Opcode::VolatileMovMR32,
        X86Opcode::VolatileMovsdRM,
    ]);
    assert!(
        vt::volatile_trace_holds(&before, &vt::machine_volatile_trace(&widened), true).is_err(),
        "a widened volatile access must be REFUSED"
    );

    // DUPLICATED, as an unrolling pass would. Must refuse.
    let duplicated = build(&[
        X86Opcode::VolatileMovRM8,
        X86Opcode::VolatileMovRM8,
        X86Opcode::MovRM,
        X86Opcode::VolatileMovMR32,
        X86Opcode::VolatileMovsdRM,
    ]);
    assert!(
        matches!(
            vt::volatile_trace_holds(&before, &vt::machine_volatile_trace(&duplicated), true),
            Err(VolatileTraceViolation::Duplicated { .. })
        ),
        "a duplicated volatile access must be REFUSED"
    );

    // And a function with NO volatile access has an empty trace, which is the
    // path every ordinary compile takes.
    let plain = build(&[X86Opcode::MovRM, X86Opcode::MovMR]);
    assert!(vt::machine_volatile_trace(&plain).is_empty());
}

/// THE LOWERING HALF: the LIR source trace and the ISel machine trace agree.
///
/// The optimizer bracket in `compiler.rs` starts AFTER instruction selection,
/// so it cannot see a selection that dropped, widened or redirected a volatile
/// access. This is the half that can: the LIR carries
/// `Opcode::VolatileLoad`/`VolatileStore` with a trust-ir-derived TYPE, put
/// there by the adapter, and the machine side carries a `Volatile*` OPCODE
/// chosen by ISel. Neither is computed from the other.
#[test]
fn the_lir_source_trace_and_the_machine_trace_describe_the_same_accesses() {
    use std::collections::HashMap;
    use trust_cg_lower::function::{BasicBlock, Function};
    use trust_cg_lower::instructions::{Block, Instruction, Opcode};
    use trust_cg_lower::{Type, function::Signature};

    let volatile_inst = |ty: Type, is_store: bool| Instruction {
        opcode: if is_store {
            Opcode::VolatileStore { ty, align: None }
        } else {
            Opcode::VolatileLoad { ty, align: None }
        },
        args: vec![],
        results: vec![],
    };

    let mut blocks = HashMap::new();
    blocks.insert(
        Block(0),
        BasicBlock {
            params: vec![],
            instructions: vec![
                volatile_inst(Type::I8, false),
                volatile_inst(Type::I32, true),
                volatile_inst(Type::F64, false),
            ],
            ..Default::default()
        },
    );
    let mut lir = Function::new(
        "volatile_lowering_probe",
        Signature {
            params: vec![],
            returns: vec![],
        },
    );
    lir.blocks = blocks;
    lir.block_order = vec![Block(0)];
    lir.entry_block = Block(0);

    let (source, unmodelled) = vt::lir_volatile_trace(&lir);
    assert_eq!(
        unmodelled, 0,
        "every access in this probe uses a modelled LIR type"
    );
    assert_eq!(source.len(), 3);

    // The machine side ISel would produce for exactly those three accesses.
    let machine = VolatileTrace {
        per_block: vec![vec![
            acc(8, false, AccessClass::Gpr),
            acc(32, true, AccessClass::Gpr),
            acc(64, false, AccessClass::Fp),
        ]],
    };
    vt::volatile_trace_holds(&source, &machine, true)
        .expect("a faithful selection must hold against the LIR source trace");

    // And a selection that DROPPED the middle access is refused — the defect
    // the optimizer bracket structurally cannot see, because it starts after
    // selection has already happened.
    let dropped = VolatileTrace {
        per_block: vec![vec![
            acc(8, false, AccessClass::Gpr),
            acc(64, false, AccessClass::Fp),
        ]],
    };
    assert!(
        matches!(
            vt::volatile_trace_holds(&source, &dropped, true),
            Err(VolatileTraceViolation::Elided { .. })
        ),
        "a selection that dropped a volatile access must be REFUSED"
    );

    // A selection that lowered the f64 access through a GPR is refused too:
    // it moves the same eight bytes and is still the wrong access.
    let reclassed = VolatileTrace {
        per_block: vec![vec![
            acc(8, false, AccessClass::Gpr),
            acc(32, true, AccessClass::Gpr),
            acc(64, false, AccessClass::Gpr),
        ]],
    };
    assert!(
        vt::volatile_trace_holds(&source, &reclassed, true).is_err(),
        "an f64 volatile access selected through a GPR must be REFUSED"
    );
}

/// An UNMODELLED LIR type is reported, never silently dropped.
///
/// If `lir_volatile_trace` quietly skipped an access whose type it does not
/// model, the source trace would be short and a genuinely elided access would
/// look correct. The count is returned so a caller must decide what to do.
#[test]
fn an_unmodelled_lir_access_type_is_counted_not_dropped() {
    use std::collections::HashMap;
    use trust_cg_lower::function::{BasicBlock, Function};
    use trust_cg_lower::instructions::{Block, Instruction, Opcode};
    use trust_cg_lower::{Type, function::Signature};

    let mut blocks = HashMap::new();
    blocks.insert(
        Block(0),
        BasicBlock {
            params: vec![],
            instructions: vec![Instruction {
                // i128 has no single-access x86 volatile lowering — ISel
                // refuses it outright rather than splitting it — so this lane
                // deliberately does not model it.
                opcode: Opcode::VolatileLoad {
                    ty: Type::I128,
                    align: None,
                },
                args: vec![],
                results: vec![],
            }],
            ..Default::default()
        },
    );
    let mut lir = Function::new(
        "unmodelled_probe",
        Signature {
            params: vec![],
            returns: vec![],
        },
    );
    lir.blocks = blocks;
    lir.block_order = vec![Block(0)];
    lir.entry_block = Block(0);

    let (trace, unmodelled) = vt::lir_volatile_trace(&lir);
    assert_eq!(unmodelled, 1, "the unmodelled access must be COUNTED");
    assert!(
        trace.is_empty(),
        "and must not enter the trace, where it would compare against nothing"
    );
}
