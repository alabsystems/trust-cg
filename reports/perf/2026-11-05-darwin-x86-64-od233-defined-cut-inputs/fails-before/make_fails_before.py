"""Build the fails-before copy of the OD-233 fixtures for a helper worktree.

The od233 test file's fixture section (everything above its "Controls
(OD-233)" section) uses only the API of the code before OD-233, and none of
slice 25's; this copies it into a helper worktree with one test that records,
on the code there, the outcome of every positive fixture, every control and
every wrong lowering, stated in parts at the fixture's points (the split
route, OD-182): its parts, its verdict on samples and the digest of its
statement and parts. Kind `base` (the slice-25 base, b30110fcd) also records
P6 (slice 25's three slot fixtures at every point) and W5 (SlotConstU64's
`imul` by 16); kind `pre` (12ebba653, before slice 25) records the module's
own fixtures and W1-W4 only (none has a scaled-index load or store row, which
`every_fixture_has_its_shape` asserts). Kind `base` also records, for the
review round's cross-tree comparison, the digest (or refusal) of every
fixture of slices 1 to 25 and of the module stated in parts at every block
start and every clean point (`od233_base_digests`, the same subjects and
labels as the head's sweep, which prints `OD233_SWEEP_DIGEST`). The copy is
registered after slice 25's qualification module (base) or slice 24a's
(pre). The fixture section is read from the lane's COMMIT `<lane sha>`
(`git show`), never from its working tree.
Usage: python3 -I make_fails_before.py <lane worktree> <lane sha> <helper worktree> base|pre
"""
import pathlib
import subprocess
import sys

lane = pathlib.Path(sys.argv[1])
lane_sha = sys.argv[2]
helper = pathlib.Path(sys.argv[3])
kind = sys.argv[4]
assert kind in ("base", "pre"), kind
src = subprocess.run(
    ["git", "-C", str(lane), "show",
     f"{lane_sha}:crates/trust-cg-verify/src/x86_source_bound_body_od233_tests.rs"],
    check=True, capture_output=True, text=True,
).stdout
marker = "// ---------------------------------------------------------------------------\n// Controls (OD-233)\n"
assert marker in src, "the od233 test file has no Controls section"
head = src[: src.index(marker)]
head = head.replace("use super::slice5::describe;", "#![allow(dead_code, unused_imports)]\n\nuse super::slice5::describe;", 1)
shapes = "POSITIVE.into_iter().chain(CONTROLS)"
wrongs = "WRONG.to_vec()"
slot = r'''
    // P6: slice 25's three slot fixtures at every point, and W5.
    use super::slice25::{Shape25, slice25_pair};
    for shape in [Shape25::SlotConstU64, Shape25::SlotConstAcrossBlocks, Shape25::SlotStoreReloadU32] {
        let (source, machine) = slice25_pair(shape);
        let points = super::slice16::every_point(&source, &machine);
        let result = in_parts(&source, &machine, points.clone());
        record(&format!("P6 {shape:?}"), &points, &result);
    }
    {
        let (source, mut machine) = slice25_pair(Shape25::SlotConstU64);
        let mut edited = 0;
        for block in machine.block_order.clone() {
            for inst in &mut machine.blocks.get_mut(&block).unwrap().insts {
                if inst.opcode == X86Opcode::ImulRRI && inst.operands.get(2) == Some(&O::Imm(8)) {
                    inst.operands[2] = O::Imm(16);
                    edited += 1;
                }
            }
        }
        assert!(edited > 0, "W5: no imul by 8\n{}", describe(&machine));
        let points = super::slice16::every_point(&source, &machine);
        let result = in_parts(&source, &machine, points.clone());
        record("W5 SlotConstU64 imul by 16", &points, &result);
        eprintln!(
            "OD233_FAILS_BEFORE wrong=W5 refuted={}",
            result.as_ref().map(|owner| owner_refuted(owner)).unwrap_or(false)
        );
    }
''' if kind == "base" else ""
test = r'''
// ---------------------------------------------------------------------------
// Fails before (this copy only; never committed)
// ---------------------------------------------------------------------------

fn record(
    label: &str,
    points: &[(Block, usize)],
    result: &Result<SourceBoundX86Body<'_>, X86BodyRefusal>,
) {
    let (parts, digest) = match result {
        Ok(owner) => (owner.parts().len(), statement_digest233(owner)),
        Err(_) => (0, String::new()),
    };
    let per_part: Vec<String> = match result {
        Ok(owner) => owner
            .parts()
            .iter()
            .map(|part| format!("{}", super::slice9::dag_holds_on_samples(part)))
            .collect(),
        Err(_) => Vec::new(),
    };
    eprintln!(
        "OD233_FAILS_BEFORE fixture={label} points={points:?} parts={parts} part_holds={per_part:?} \
         result={} verdict={} digest={digest}",
        refusal_text233(result),
        verdict233(result)
    );
}

/// Every OD-233 fixture, control and wrong lowering on the code here, stated
/// in parts at its points: its parts, verdict and statement digest.
#[test]
fn od233_fails_before() {
    for shape in SHAPES {
        let (source, machine) = od233_pair(shape);
        let points = points233(shape, &source);
        let result = owner233(shape, &source, &machine);
        record(&format!("{} {shape:?}", shape.label()), &points, &result);
    }
    for wrong in WRONGS {
        let (source, machine) = wrong233(wrong);
        let points = points233(wrong.shape(), &source);
        let result = owner233(wrong.shape(), &source, &machine);
        record(&format!("{} {wrong:?}", wrong.label()), &points, &result);
        eprintln!(
            "OD233_FAILS_BEFORE wrong={} refuted={}",
            wrong.label(),
            result.as_ref().map(|owner| owner_refuted(owner)).unwrap_or(false)
        );
    }
SLOT}
DIGESTS'''.replace("SHAPES", shapes).replace("WRONGS", wrongs).replace("SLOT", slot)
digests = r'''
/// Every fixture of slices 1 to 25 and of this module, stated in parts at
/// every block start and every clean point on the code here: its
/// statement's digest, or its refusal (the head's sweep prints the same
/// subjects, `OD233_SWEEP_DIGEST`).
#[test]
fn od233_base_digests() {
    let mut fixtures = super::slice16::earlier_fixtures();
    fixtures.extend(super::slice24::later_fixtures());
    for shape in super::slice24::SLICE_TWENTY_FOUR {
        let (source, machine) = super::slice24::slice24_pair(shape);
        fixtures.push((format!("s24 {shape:?}"), source, machine));
    }
    for shape in super::slice25::SLICE_TWENTY_FIVE {
        let (source, machine) = super::slice25::slice25_pair(shape);
        fixtures.push((format!("s25 {shape:?}"), source, machine));
    }
    for shape in POSITIVE.into_iter().chain(CONTROLS) {
        let (source, machine) = od233_pair(shape);
        fixtures.push((format!("od233 {} {shape:?}", shape.label()), source, machine));
    }
    for (label, source, machine) in fixtures {
        for (cut, points) in [
            ("every block", super::slice16::every_block(&source)),
            ("every point", super::slice16::every_point(&source, &machine)),
        ] {
            let digest = match in_parts(&source, &machine, points) {
                Ok(owner) => statement_digest233(&owner),
                Err(refusal) => format!("refused: {refusal}"),
            };
            eprintln!("OD233_BASE_DIGEST\t{label}\t{cut}\t{digest}");
        }
    }
}
''' if kind == "base" else ""
test = test.replace("DIGESTS", digests)
(helper / "crates/trust-cg-verify/src/x86_source_bound_body_od233_tests.rs").write_text(head + test)
tests = helper / "crates/trust-cg-verify/src/x86_source_bound_body_tests.rs"
t = tests.read_text()
anchor = {
    "base": '#[path = "x86_source_bound_body_slice25_qualification_tests.rs"]\nmod slice25_qualification;\n',
    "pre": '#[path = "x86_source_bound_body_slice24_qualification_tests.rs"]\nmod slice24_qualification;\n',
}[kind]
reg = '\n#[path = "x86_source_bound_body_od233_tests.rs"]\nmod od233;\n'
if reg not in t:
    assert anchor in t, "the registration anchor is not where it is expected"
    t = t.replace(anchor, anchor + reg, 1)
    tests.write_text(t)
print("wrote", len(head + test), "bytes")
