#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: compiling the same program twice gives the same refusal.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS. `bridge_corpus/fix_p_collection_refusal_order.rs` has one
// function with two `[TCG-COLLECTION-IMAGE]` refusals (an escaping `&Nat` that
// owns a `Vec<u64>`, an escaping `&Name` that owns a `String`). The
// memory-backed analysis reported whichever it met first while walking a
// `HashMap` in hash order, so the text varied between compiles of one file —
// measured 3 x `String`, 5 x `Vec<u64>` over eight — and the Trust run-make test
// `trust-ir-cg-collection-owner-image`, which asserts the `Vec<u64` text, failed
// at random (2026-09-28). The analysis now walks in local order. Revert that and
// eight compiles agree with probability about 1/128.
//
// A refusal is the expected outcome here: this pins its DETERMINISM, not a
// capability. The LLVM oracle runs first so the fixture is known to be a valid
// program. The bridge side passes `no-proof-certs` (see
// `fat_thin_reborrow_differential.rs`) so the refusal is this one, not
// `[TCG-PROOF-465]`.

use std::process::Command;

const COMPILES: usize = 8;

#[test]
fn collection_image_refusal_is_the_same_on_every_compile() {
    if toolchain_support::skip_without_backend_knobs(
        "collection_image_refusal_is_the_same_on_every_compile",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = std::env::temp_dir().join(format!("tcg_refusal_order_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    let src = dir.join("fix_p_collection_refusal_order.rs");
    std::fs::write(
        &src,
        include_str!("bridge_corpus/fix_p_collection_refusal_order.rs"),
    )
    .expect("write source");

    let oracle_bin = dir.join("oracle");
    let oracle = toolchain_support::rustc_command()
        .args(["--crate-type", "bin", "-Cpanic=abort", "-Copt-level=0"])
        .arg("-o")
        .arg(&oracle_bin)
        .arg(&src)
        .output()
        .expect("spawn the compiler");
    assert!(
        oracle.status.success(),
        "LLVM oracle failed: {}",
        String::from_utf8_lossy(&oracle.stderr)
    );
    let ran = Command::new(&oracle_bin).output().expect("run oracle");
    assert_eq!(String::from_utf8_lossy(&ran.stdout), "2 3\n");

    let mut refusals = Vec::with_capacity(COMPILES);
    for _ in 0..COMPILES {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(&dylib);
        let output = toolchain_support::rustc_command()
            .args(["--crate-type", "bin", "-Cpanic=abort", "-Copt-level=0"])
            .arg(backend_arg)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]))
            .arg("-o")
            .arg(dir.join("bridge"))
            .arg(&src)
            .output()
            .expect("spawn the compiler");
        assert!(
            !output.status.success(),
            "the bridge compiled a function that owns slot-modeled collections by \
             escaping reference; this test pins the refusal's determinism and must be \
             revisited, not deleted, if that shape becomes supported"
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        let refusal = stderr
            .lines()
            .find(|line| line.contains("[TCG-COLLECTION-IMAGE]"))
            .unwrap_or_else(|| panic!("no [TCG-COLLECTION-IMAGE] refusal in: {stderr}"))
            .to_owned();
        assert!(
            refusal.contains("collection field std::vec::Vec<u64"),
            "the refusal must name the first escaping referent in local order (`a`, \
             whose field is `Vec<u64>`): {refusal}"
        );
        refusals.push(refusal);
    }
    assert!(
        refusals.windows(2).all(|pair| pair[0] == pair[1]),
        "the same program was refused with different texts: {refusals:#?}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}
