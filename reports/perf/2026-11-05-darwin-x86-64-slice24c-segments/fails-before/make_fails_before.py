"""Build the fails-before copy of the slice-24c fixtures for the base worktree.

The slice24c test file's fixture and edited-pair sections (everything above
its "Controls" section) use only the slice 1-25 API; this copies them into
the base worktree (a617488aa, slice 25 merged with origin/main) with one test
that records, on the code before slice 24c, the outcome of every fixture
(P1-P6, P9, P11), of P1 under both encodings (P7), of the long diamond (P8,
the production route and the N13 policy points), of the short tail (P8s) and
the forked tail (P12, the production route and its N13 policy point), of
the composition (the O2 pipeline over five earlier fixtures), of every wrong
lowering and refusal control, and the O0 owners record (`S24C_O0` lines),
and registers it after slice 25. No slice-24c text may appear in any record,
and no fixture, P8s, P12 or composition subject may be stated there.
Usage: python3 -I make_fails_before.py <lane worktree> <base worktree>
"""
import pathlib, sys

lane, base = map(pathlib.Path, sys.argv[1:3])
src = (lane / "crates/trust-cg-verify/src/x86_source_bound_body_slice24c_tests.rs").read_text()
marker = "// ---------------------------------------------------------------------------\n// Controls (slice 24c)\n"
assert marker in src, "the Controls marker moved"
head = src[: src.index(marker)]
head = head.replace("use super::slice5::describe;", "#![allow(dead_code, unused_imports)]\n\nuse super::slice5::describe;", 1)
test = r'''
// ---------------------------------------------------------------------------
// Fails before (this copy only; never committed)
// ---------------------------------------------------------------------------

/// Texts only the slice-24c code writes (design §3): none may appear before.
const S24C_TEXTS: &[&str] = &[
    "over segments",
    "; no segment:",
    "the segment of",
    "segment member",
    "where the segment exits to",
    "is not single-entry",
];

/// Every slice-24c fixture and case on the code before slice 24c: its
/// outcome, and whether its theorem holds on samples.
#[test]
fn s24c_fails_before() {
    let mut stated = Vec::new();
    let mut named = Vec::new();
    // Fixtures that did not build, and P7 encodings stated.
    let mut absent: Vec<String> = Vec::new();
    let mut record = |what: String, result: &Result<SourceBoundX86Body<'_>, X86BodyRefusal>, must_refuse: bool| {
        let holds = result.as_ref().map(|owner| owner_holds(owner).is_ok()).unwrap_or(false);
        let text = outcome24c(result);
        eprintln!("S24C_FAILS_BEFORE {what} holds={holds} result={text}");
        if S24C_TEXTS.iter().any(|needle| text.contains(needle)) {
            named.push(what.clone());
        }
        if must_refuse && result.is_ok() {
            stated.push(what);
        }
    };
    for shape in SLICE_TWENTY_FOUR_C {
        let Ok((source, machine)) = std::panic::catch_unwind(|| pair24c(shape)) else {
            eprintln!("S24C_FAILS_BEFORE shape={shape:?} fixture=panicked");
            absent.push(format!("{shape:?} (no fixture)"));
            continue;
        };
        let cmovs = cmov_rows(&machine).len();
        record(format!("shape={shape:?} cmovs={cmovs}"), &owner24c(&source, &machine), true);
    }
    for (encoding, theorem) in encodings_of_p1() {
        let text = theorem.as_ref().map_or_else(|refusal| format!("{refusal}"), |_| "stated".into());
        eprintln!("S24C_FAILS_BEFORE encoding=P7 {encoding} result={text}");
        if theorem.is_ok() {
            absent.push(format!("P7 {encoding} stated"));
        }
    }
    let (source, machine) = case24c("P8");
    record("shape=LongDiamond route=production".into(), &owner24c(&source, &machine), true);
    for (k, point) in p8_points(&source).into_iter().enumerate() {
        record(
            format!("shape=LongDiamond route=policy point={k} at={point:?}"),
            &parts24c(&source, &machine, vec![point]),
            false,
        );
    }
    let (source, machine) = case24c("P8s");
    record("shape=ShortTail route=production".into(), &owner24c(&source, &machine), true);
    let (source, machine) = case24c("P12");
    record("shape=ForkedTail route=production".into(), &owner24c(&source, &machine), true);
    let point = p12_point(&source);
    record(
        format!("shape=ForkedTail route=policy at={point:?}"),
        &parts24c(&source, &machine, vec![point]),
        false,
    );
    for (label, source, machine) in composition24c() {
        record(format!("composition={label}"), &owner24c(&source, &machine), true);
    }
    for label in CASES24C {
        let Ok((source, machine)) = std::panic::catch_unwind(|| case24c(label)) else {
            eprintln!("S24C_FAILS_BEFORE case={label} pair=panicked");
            continue;
        };
        record(format!("case={label}"), &owner24c(&source, &machine), false);
    }
    // The O0 owners record (`slice24c_o0_owners.txt`).
    for line in o0_outcomes24c() {
        eprintln!("S24C_O0\t{line}");
    }
    assert!(named.is_empty(), "slice-24c texts before slice 24c: {named:?}");
    assert!(stated.is_empty(), "stated before slice 24c: {stated:?}");
    assert!(absent.is_empty(), "no fixture, or P7 stated: {absent:?}");
}
'''
(base / "crates/trust-cg-verify/src/x86_source_bound_body_slice24c_tests.rs").write_text(head + test)
tests = base / "crates/trust-cg-verify/src/x86_source_bound_body_tests.rs"
t = tests.read_text()
anchor = '#[path = "x86_source_bound_body_slice25_qualification_tests.rs"]\nmod slice25_qualification;\n'
reg = '\n#[path = "x86_source_bound_body_slice24c_tests.rs"]\nmod slice24c;\n'
if reg not in t:
    assert anchor in t, "the slice-25 registration is not where it is expected"
    t = t.replace(anchor, anchor + reg, 1)
    tests.write_text(t)
print("wrote", len(head + test), "bytes")
