"""Build the fails-before copy of the slice-24a fixtures for the base worktree.

The slice24 test file's fixture section (everything above its "Controls"
section) uses only the slice 1-23 API; this copies it into the base
worktree (7ee0def54) with one test that records every fixture's outcome on
the code before slice 24a, and registers it after slice 23.
Usage: python3 -I make_fails_before.py <lane worktree> <base worktree>
"""
import pathlib, sys

lane, base = map(pathlib.Path, sys.argv[1:3])
src = (lane / "crates/trust-cg-verify/src/x86_source_bound_body_slice24_tests.rs").read_text()
marker = "// ---------------------------------------------------------------------------\n// Controls (slice 24a)\n"
head = src[: src.index(marker)]
head = head.replace("use super::slice5::describe;", "#![allow(dead_code)]\n\nuse super::slice5::describe;", 1)
test = r'''
// ---------------------------------------------------------------------------
// Fails before (this copy only; never committed)
// ---------------------------------------------------------------------------

/// Every slice-24a fixture on the code before slice 24a: its outcome, and
/// whether it would pass the slice-24a owner control (stated and holding).
#[test]
fn s24_fails_before() {
    use sha2::{Digest, Sha256};
    let mut stated = Vec::new();
    for shape in SLICE_TWENTY_FOUR {
        let (source, machine) = slice24_pair(shape);
        let result = owner24(&source, &machine);
        let holds = result.as_ref().map(|owner| owner_holds(owner).is_ok()).unwrap_or(false);
        eprintln!("S24_FAILS_BEFORE shape={shape:?} holds={holds} result={}", refusal_text(&result));
        if result.is_ok() {
            stated.push(format!("{shape:?}"));
        }
    }
    for (label, source, machine, points) in parts_fixtures() {
        let result = parts24(&source, &machine, points);
        eprintln!("S24_FAILS_BEFORE parts={label:?} result={}", refusal_text(&result));
        if result.is_ok() {
            stated.push(label.to_string());
        }
    }
    for (label, source, machine, route, expected) in refusal_controls() {
        let result = match route {
            None => owner24(&source, &machine),
            Some(points) => parts24(&source, &machine, points),
        };
        eprintln!(
            "S24_FAILS_BEFORE refusal={label:?} names_expected={} result={}",
            refusal_text(&result).contains(expected),
            refusal_text(&result)
        );
    }
    for (label, source, machine) in slice_twenty_four_refutations() {
        let result = owner24(&source, &machine);
        eprintln!("S24_FAILS_BEFORE wrong={label:?} result={}", refusal_text(&result));
    }
    let (source, machine) = variant24_pair(Variant24::OnePathChain);
    let owner = owner24(&source, &machine).expect("the one-path control states today");
    eprintln!(
        "S24_FAILS_BEFORE one_path_sha256={:x}",
        Sha256::digest(text(owner.obligation()).as_bytes())
    );
    for variant in [
        Variant24::AbsorbedParams,
        Variant24::DoWhile,
        Variant24::DeadCycle,
        Variant24::CopyAcrossSeam,
        Variant24::SilentStore,
        Variant24::GuardBeforeBranch,
        Variant24::FloatConstChain,
        Variant24::NanConstChain,
        Variant24::NoParamEntry,
        Variant24::RoutineChain,
        Variant24::LongChain,
    ] {
        let (source, machine) = variant24_pair(variant);
        eprintln!(
            "S24_FAILS_BEFORE variant={variant:?} result={}",
            refusal_text(&owner24(&source, &machine))
        );
    }
    for label in ["D2 folded", "entry behind a dead Jump", "routine chain", "long chain"] {
        let (source, machine) = extra24(label);
        eprintln!(
            "S24_FAILS_BEFORE extra={label:?} result={}",
            refusal_text(&owner24(&source, &machine))
        );
    }
    let (source, machine) = extra24("routine chain");
    eprintln!(
        "S24_FAILS_BEFORE extra=\"routine chain\" in_module result={}",
        refusal_text(&super::slice22::fixture_owner(&source, &machine))
    );
    let (source, machine) = slice24_pair(Shape24::EntryChain);
    let next = jump_dest(&source, source.entry_block);
    let policy = super::split::SplitPolicy { region_blocks: 2, ..cut_at(vec![(next, 0)]) };
    eprintln!(
        "S24_FAILS_BEFORE region_bound result={}",
        refusal_text(&source_bound_x86_body_in_parts(&source, &machine, SYSV, &policy))
    );
    // The O0 outcomes `o0_is_untouched` compares (slice24_o0_owners.txt).
    for line in o0_outcomes() {
        eprintln!("S24_O0\t{line}");
    }
    assert!(stated.is_empty(), "stated before slice 24a: {stated:?}");
}
'''
(base / "crates/trust-cg-verify/src/x86_source_bound_body_slice24_tests.rs").write_text(head + test)
tests = base / "crates/trust-cg-verify/src/x86_source_bound_body_tests.rs"
t = tests.read_text()
anchor = '#[path = "x86_source_bound_body_slice23_qualification_tests.rs"]\nmod slice23_qualification;\n'
reg = '\n#[path = "x86_source_bound_body_slice24_tests.rs"]\nmod slice24;\n'
if reg not in t:
    t = t.replace(anchor, anchor + reg, 1)
    tests.write_text(t)
print("wrote", len(head + test), "bytes")
