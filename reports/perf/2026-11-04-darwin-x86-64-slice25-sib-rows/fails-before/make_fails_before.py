"""Build the fails-before copy of the slice-25 fixtures for the base worktree.

The slice25 test file's fixture and edited-pair sections (everything above
its "Controls" section) use only the slice 1-24a API; this copies them into
the base worktree (6c036f1de, slice 25.0) with one test that records, on the
code before slice 25, the outcome of every fixture, of every edit a slice-25
control holds (the neutral and qualified edits), of every verdict-transition
edit, and of every fixture stated in parts at every point; and registers it
after slice 24a. The base worktree may be the lane's own tree with
`crates/trust-cg-verify/src` checked out at the base commit.
Usage: python3 -I make_fails_before.py <lane worktree> <base worktree>
"""
import pathlib, sys

lane, base = map(pathlib.Path, sys.argv[1:3])
src = (lane / "crates/trust-cg-verify/src/x86_source_bound_body_slice25_tests.rs").read_text()
marker = "// ---------------------------------------------------------------------------\n// Controls (slice 25)\n"
head = src[: src.index(marker)] if marker in src else src
head = head.replace("use super::slice5::describe;", "#![allow(dead_code, unused_imports)]\n\nuse super::slice5::describe;", 1)
test = r'''
// ---------------------------------------------------------------------------
// Fails before (this copy only; never committed)
// ---------------------------------------------------------------------------

/// Every slice-25 fixture on the code before slice 25: whether its machine
/// stream has the rows it is for, its outcome, and whether it would pass the
/// slice-25 owner control (stated and holding).
#[test]
fn s25_fails_before() {
    let mut stated = Vec::new();
    for shape in SLICE_TWENTY_FIVE {
        let Ok((source, machine)) = std::panic::catch_unwind(|| slice25_pair(shape)) else {
            eprintln!("S25_FAILS_BEFORE shape={shape:?} fixture=panicked");
            stated.push(format!("{shape:?} (no fixture)"));
            continue;
        };
        let present: Vec<bool> = shape
            .expected()
            .iter()
            .map(|opcode| !rows_with(&machine, &[*opcode]).is_empty())
            .collect();
        let result = owner25(&source, &machine);
        let holds = result.as_ref().map(|owner| owner_holds(owner).is_ok()).unwrap_or(false);
        eprintln!(
            "S25_FAILS_BEFORE shape={shape:?} rows_present={present:?} rows={:?} holds={holds} result={}",
            slice25_rows(&machine),
            refusal_text25(&result)
        );
        if result.is_ok() {
            stated.push(format!("{shape:?}"));
        }
    }
    // The edits a slice-25 control holds, and the transitions: none may be
    // stated and hold before slice 25 (a transition's text is the record).
    let mut labels: Vec<&str> = Vec::new();
    for label in NEUTRAL.iter().chain(QUALIFIED_EDITS).chain(TRANSITIONS) {
        if !labels.contains(label) {
            labels.push(label);
        }
    }
    for label in labels {
        let Ok((source, machine)) = std::panic::catch_unwind(|| case25(label)) else {
            eprintln!("S25_FAILS_BEFORE edit={label:?} pair=panicked");
            stated.push(format!("{label} (no pair)"));
            continue;
        };
        let result = owner25(&source, &machine);
        let holds = result.as_ref().map(|owner| owner_holds(owner).is_ok()).unwrap_or(false);
        eprintln!(
            "S25_FAILS_BEFORE edit={label:?} holds={holds} result={}",
            refusal_text25(&result)
        );
        if holds {
            stated.push(format!("edit {label}"));
        }
    }
    // Every fixture in parts at every point (the split route, OD-182).
    for shape in SLICE_TWENTY_FIVE {
        let Ok((source, machine)) = std::panic::catch_unwind(|| slice25_pair(shape)) else {
            continue;
        };
        let points = super::slice16::every_point(&source, &machine);
        let result = super::slice16::in_parts(&source, &machine, points);
        let holds = result.as_ref().map(|owner| owner_holds(owner).is_ok()).unwrap_or(false);
        eprintln!(
            "S25_FAILS_BEFORE split={shape:?} holds={holds} result={}",
            refusal_text25(&result)
        );
        if holds {
            stated.push(format!("{shape:?} in parts"));
        }
    }
    // Every scaled-index fixture split into the rows slices 4 and 17 state
    // (`lea t, [slot]` for a slot base, `LeaSib t, [base + index*scale +
    // disp]`, the access through `[t + 0]`), whole and in parts at the
    // fixture's points: the slice-25 split that fails must fail here too,
    // on the code before slice 25 (no record for the read-modify-write
    // fixtures, whose decomposition needs slice 25's opcode table).
    for shape in SLICE_TWENTY_FIVE {
        let Ok((source, machine)) = std::panic::catch_unwind(|| slice25_pair(shape)) else {
            continue;
        };
        let Some(decomposed) = base_decompose(&machine) else {
            continue;
        };
        let whole = owner25(&source, &decomposed);
        let whole_holds = whole.as_ref().map(|owner| owner_holds(owner).is_ok()).unwrap_or(false);
        let points = super::slice16::every_point(&source, &machine);
        let split = match super::slice16::in_parts(&source, &decomposed, points) {
            Ok(owner) => match owner_holds(&owner) {
                Ok(()) => "holds".to_owned(),
                Err(why) => why,
            },
            Err(refusal) => refusal.to_string(),
        };
        eprintln!(
            "S25_FAILS_BEFORE decomposed={shape:?} whole_holds={whole_holds} whole={} split={split}",
            refusal_text25(&whole)
        );
    }
    assert!(stated.is_empty(), "stated before slice 25, or no fixture: {stated:?}");
}

/// `machine` with every scaled-index load and store split as
/// `decomposition_equivalence` splits it, by the base-only sibling opcode;
/// `None` for a machine with a read-modify-write row or no such row.
fn base_decompose(machine: &X86ISelFunction) -> Option<X86ISelFunction> {
    use X86Opcode as Op;
    let sibling = |opcode: Op| -> Option<(Op, usize)> {
        Some(match opcode {
            Op::MovRMSib => (Op::MovRM, 1),
            Op::MovRM32Sib => (Op::MovRM32, 1),
            Op::MovRM8Sib => (Op::MovRM8, 1),
            Op::MovzxRM8Sib => (Op::MovzxRM8, 1),
            Op::MovsdRMSib => (Op::MovsdRM, 1),
            Op::MovssRMSib => (Op::MovssRM, 1),
            Op::MovMRSib => (Op::MovMR, 0),
            Op::MovMR32Sib => (Op::MovMR32, 0),
            Op::MovMR8Sib => (Op::MovMR8, 0),
            _ => return None,
        })
    };
    let mut machine = machine.clone();
    let mut fresh = 20_000u32;
    let mut any = false;
    for block in machine.block_order.clone() {
        let Some(body) = machine.blocks.get_mut(&block) else {
            continue;
        };
        let mut split = Vec::with_capacity(body.insts.len());
        for inst in body.insts.drain(..) {
            if matches!(inst.opcode, Op::AddMR | Op::XorMR | Op::AddMRSib | Op::XorMRSib) {
                return None;
            }
            let Some((to, at)) = sibling(inst.opcode) else {
                split.push(inst);
                continue;
            };
            let O::SibMemAddr { base, index, scale, disp } = inst.operands[at].clone() else {
                split.push(inst);
                continue;
            };
            any = true;
            let base = match *base {
                O::StackSlot(slot) => {
                    fresh += 1;
                    let b = vreg(fresh);
                    split.push(X86ISelInst::new(
                        Op::Lea,
                        vec![b.clone(), O::MemAddr { base: Box::new(O::StackSlot(slot)), disp: 0 }],
                    ));
                    b
                }
                other => other,
            };
            fresh += 1;
            let t = vreg(fresh);
            split.push(X86ISelInst::new(
                Op::LeaSib,
                vec![t.clone(), O::SibMemAddr { base: Box::new(base), index, scale, disp }],
            ));
            let mut row = X86ISelInst::new(to, inst.operands.clone());
            row.operands[at] = O::MemAddr { base: Box::new(t), disp: 0 };
            row.lowering_provenance = inst.lowering_provenance;
            split.push(row);
        }
        body.insts = split;
    }
    any.then_some(machine)
}
'''
(base / "crates/trust-cg-verify/src/x86_source_bound_body_slice25_tests.rs").write_text(head + test)
tests = base / "crates/trust-cg-verify/src/x86_source_bound_body_tests.rs"
t = tests.read_text()
anchor = '#[path = "x86_source_bound_body_slice24_qualification_tests.rs"]\nmod slice24_qualification;\n'
reg = '\n#[path = "x86_source_bound_body_slice25_tests.rs"]\nmod slice25;\n'
if reg not in t:
    assert anchor in t, "the slice-24a registration is not where it is expected"
    t = t.replace(anchor, anchor + reg, 1)
    tests.write_text(t)
print("wrote", len(head + test), "bytes")
