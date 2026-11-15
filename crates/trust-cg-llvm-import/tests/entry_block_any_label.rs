#![cfg(feature = "driver")]
// trust-cg-llvm-import / tests / entry_block_any_label.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The entry block is the FIRST block, whatever it is named.
//
// Before this was fixed, two cases worked — a block literally labelled
// `entry:`, picked up by name, and an UNLABELLED first block (LLVM's implicit
// `%0`), aliased via `implicit_entry_block_label`. A first block carrying any
// OTHER explicit label fell through both: the interned `entry` block stayed
// EMPTY while the real first block became a separate one, and the function was
// rejected with
//
//     block in @f has no terminator (phi or fallthrough not supported)
//
// which names neither the cause nor the block and blames phis that are fine.
//
// THIS MATTERS BEYOND HAND-WRITTEN IR: rustc names its first block `start`, so
// every rustc-emitted function hit this.
//
// Both directions are pinned here, because the diagnosis turned on the pair:
// the same function imports when its first block is `entry` and used to fail
// when it is `start`.

use std::io::Write;
use std::sync::atomic::{AtomicUsize, Ordering};
use trust_cg_llvm_import::import_module;

/// Per-call suffix of the fixture directory. Tests reuse tags (`entry`,
/// `start`, `bb0`, ...) and libtest runs them concurrently in one process, so
/// the process id and tag alone would let one call remove a directory another
/// call is still writing.
static FIXTURE_SEQ: AtomicUsize = AtomicUsize::new(0);

/// Write `text` to a uniquely-named `.ll` under the test temp dir and import
/// it. The public entry point takes a path, so the fixture goes to disk; the
/// directory (unique to this call) is removed once the import has read it,
/// whatever it returned.
fn import_text(tag: &str, text: &str) -> trust_cg_llvm_import::Result<trust_ir::Module> {
    let seq = FIXTURE_SEQ.fetch_add(1, Ordering::Relaxed);
    let dir =
        std::env::temp_dir().join(format!("tcg-entrylabel-{}-{seq}-{tag}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let path = dir.join("m.ll");
    let mut f = std::fs::File::create(&path).expect("create");
    f.write_all(text.as_bytes()).expect("write");
    drop(f);
    let imported = import_module(&path);
    std::fs::remove_dir_all(&dir).expect("remove the fixture directory");
    imported
}

/// One function whose first block carries `$label`, with a loop-carried phi so
/// the body is not trivially straight-line.
fn module_with_entry_label(label: &str) -> String {
    format!(
        "target triple = \"x86_64-unknown-linux-gnu\"\n\
         define i64 @f(i64 %n) {{\n\
         {label}:\n\
         \x20 br label %loop\n\
         loop:\n\
         \x20 %i = phi i64 [ 0, %{label} ], [ %i2, %loop ]\n\
         \x20 %s = phi i64 [ 0, %{label} ], [ %s2, %loop ]\n\
         \x20 %s2 = add i64 %s, %i\n\
         \x20 %i2 = add i64 %i, 1\n\
         \x20 %c = icmp ult i64 %i2, %n\n\
         \x20 br i1 %c, label %loop, label %out\n\
         out:\n\
         \x20 ret i64 %s2\n\
         }}\n"
    )
}

#[test]
fn an_entry_block_named_entry_imports() {
    let m = module_with_entry_label("entry");
    assert!(
        import_text("entry", &m).is_ok(),
        "the historically-accepted spelling must still import"
    );
}

#[test]
fn an_entry_block_named_start_imports_too() {
    // rustc's spelling. This is the regression.
    let m = module_with_entry_label("start");
    let got = import_text("start", &m);
    assert!(
        got.is_ok(),
        "a first block labelled `start` must be recognized as the entry block; got {:?}",
        got.err()
    );
}

#[test]
fn an_arbitrarily_named_entry_block_imports() {
    for label in ["bb0", "for.cond.preheader", "L1", "topofloop"] {
        let m = module_with_entry_label(label);
        let got = import_text(label, &m);
        assert!(
            got.is_ok(),
            "first block `{label}` must be the entry block; got {:?}",
            got.err()
        );
    }
}

#[test]
fn every_spelling_imports_and_none_reports_a_missing_terminator() {
    // The old failure mode was a bogus "has no terminator (phi or fallthrough
    // not supported)". Pin that no accepted spelling produces it, so a future
    // regression names itself rather than blaming phis again.
    for label in ["entry", "start", "bb0", "for.cond.preheader"] {
        match import_text(label, &module_with_entry_label(label)) {
            Ok(_) => {}
            Err(e) => panic!("entry block `{label}` refused: {e:?}"),
        }
    }
}

#[test]
fn named_first_block_does_not_alias_a_later_entry_label() {
    let text = r#"
target triple = "x86_64-unknown-linux-gnu"
define i64 @f(i64 %n) {
start:
  %v = add i64 %n, 1
  br label %entry
entry:
  %out = add i64 %v, 2
  ret i64 %out
}
"#;
    let module = import_text("later-entry-named", text).expect("valid two-block module imports");
    let function = &module.functions[0];
    assert_eq!(
        function.blocks.len(),
        2,
        "first start and later entry are distinct LLVM blocks"
    );
    assert_eq!(function.entry, function.blocks[0].id);
    match &function.blocks[0].terminator().unwrap().inst {
        trust_ir::Inst::Br { target, .. } => assert_eq!(*target, function.blocks[1].id),
        other => panic!("first block must branch to the separate later entry block: {other:?}"),
    }
    assert!(matches!(
        function.blocks[1].terminator().unwrap().inst,
        trust_ir::Inst::Return { .. }
    ));
}

#[test]
fn implicit_first_block_does_not_alias_a_later_entry_label() {
    // The implicit entry's numeric name also must not reserve the name entry
    // for itself. This is a nearby preexisting alias-collision control.
    let text = r#"
target triple = "x86_64-unknown-linux-gnu"
define i64 @f(i64 %n) {
  %v = add i64 %n, 1
  br label %entry
entry:
  %out = add i64 %v, 2
  ret i64 %out
}
"#;
    let module = import_text("later-entry-implicit", text).expect("valid two-block module imports");
    let function = &module.functions[0];
    assert_eq!(
        function.blocks.len(),
        2,
        "implicit first block and later entry are distinct LLVM blocks"
    );
    assert_eq!(function.entry, function.blocks[0].id);
    match &function.blocks[0].terminator().unwrap().inst {
        trust_ir::Inst::Br { target, .. } => assert_eq!(*target, function.blocks[1].id),
        other => {
            panic!("implicit first block must branch to the separate later entry block: {other:?}")
        }
    }
    assert!(matches!(
        function.blocks[1].terminator().unwrap().inst,
        trust_ir::Inst::Return { .. }
    ));
}
