#![cfg(feature = "driver")]

// LLVM `available_externally` definitions, imported and compiled.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// LLVM's `available_externally` linkage means "the body is available for
// inlining; the definition is emitted elsewhere". The importer used to read a
// `define available_externally` as an `External` DEFINITION, so the object
// carried a strong symbol LLVM would not emit. It now imports trust-ir
// `Linkage::AvailableExternally`, which the backend never emits (every call
// reaches the undefined symbol) and splices as an inline-only body at O1+
// under a disclosed one-definition premise (`docs/jit-inline-only-bodies.md`):
//
//  * the imported function has `AvailableExternally` linkage and its body;
//  * at O0, and at O2 under `TCG_NO_INLINE_ONLY_BODIES`, the object is byte
//    for byte the object of the same program with the function only
//    DECLARED — no definition, an undefined symbol;
//  * at O2 both calls are spliced and disclosed, and the symbol is no longer
//    referenced by the caller.

mod common;

use common::{TARGETS, compiler_for, object_symbol, undefined_symbols};
use trust_cg_codegen::INLINE_ONLY_BODIES_KILL_SWITCH;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_llvm_import::import_text;
use trust_ir::Linkage;

const WITH_BODY: &str = "\
define available_externally i64 @read_lit(ptr %t, i64 %i) {
entry:
  %len = load i64, ptr %t
  %ok = icmp ult i64 %i, %len
  br i1 %ok, label %fast, label %slow
fast:
  %s = add i64 %i, 1
  %p = getelementptr i64, ptr %t, i64 %s
  %v = load i64, ptr %p
  ret i64 %v
slow:
  %r = call i64 @read_lit_slow(ptr %t, i64 %i)
  ret i64 %r
}

declare i64 @read_lit_slow(ptr, i64)

define i64 @entry(ptr %t, i64 %i) {
entry:
  %a = call i64 @read_lit(ptr %t, i64 %i)
  %j = add i64 %i, 1
  %b = call i64 @read_lit(ptr %t, i64 %j)
  %sum = add i64 %a, %b
  ret i64 %sum
}
";

const DECLARED: &str = "\
declare i64 @read_lit(ptr, i64)

declare i64 @read_lit_slow(ptr, i64)

define i64 @entry(ptr %t, i64 %i) {
entry:
  %a = call i64 @read_lit(ptr %t, i64 %i)
  %j = add i64 %i, 1
  %b = call i64 @read_lit(ptr %t, i64 %j)
  %sum = add i64 %a, %b
  ret i64 %sum
}
";

fn import(src: &str, triple: &str) -> trust_ir::Module {
    let target = format!("target triple = \"{triple}\"\n\n");
    import_text(&format!("{target}{src}"), "available_externally_e2e").expect("import")
}

#[test]
fn an_available_externally_define_imports_as_available_externally_with_its_body() {
    let module = import(WITH_BODY, TARGETS[0]);
    let read = module
        .functions
        .iter()
        .find(|f| f.name == "read_lit")
        .expect("read_lit imported");
    assert_eq!(read.linkage, Linkage::AvailableExternally);
    assert!(read.has_body(), "the body is kept for the inliner");
    let entry = module.functions.iter().find(|f| f.name == "entry").unwrap();
    assert_eq!(entry.linkage, Linkage::External);
}

#[test]
fn the_body_is_never_emitted_and_is_spliced_only_where_admitted() {
    for triple in TARGETS {
        let with_body = import(WITH_BODY, triple);
        let declared = import(DECLARED, triple);
        let compile = |module: &trust_ir::Module, opt_level| {
            compiler_for(triple, opt_level)
                .compile(module)
                .unwrap_or_else(|e| panic!("{triple} {opt_level:?}: {e}"))
        };

        // O0: no inliner; the object is the declaration's.
        let o0 = compile(&with_body, OptLevel::O0);
        assert_eq!(
            o0.object_code,
            compile(&declared, OptLevel::O0).object_code,
            "{triple}: an available_externally body is never emitted"
        );
        assert!(
            undefined_symbols(&o0.object_code).contains(&object_symbol(triple, "read_lit")),
            "{triple}: the call reaches the undefined symbol"
        );

        // O2 with the inline-only kill switch: still the declaration's bytes.
        let killed = trust_cg_codegen::env_lock::with_env_overrides(
            &[(INLINE_ONLY_BODIES_KILL_SWITCH, "1")],
            || compile(&with_body, OptLevel::O2),
        );
        assert_eq!(
            killed.object_code,
            compile(&declared, OptLevel::O2).object_code,
            "{triple}: withheld, the body leaves no trace"
        );

        // O2: both calls spliced and disclosed; the caller no longer calls it.
        let o2 = compile(&with_body, OptLevel::O2);
        let spliced: Vec<_> = o2
            .inline_only_bodies
            .spliced
            .iter()
            .map(|u| (u.name.as_str(), u.sites))
            .collect();
        assert_eq!(spliced, vec![("read_lit", 2)], "{triple}");
        let undefined = undefined_symbols(&o2.object_code);
        assert!(
            !undefined.contains(&object_symbol(triple, "read_lit")),
            "{triple}: {undefined:?}"
        );
        assert!(
            undefined.contains(&object_symbol(triple, "read_lit_slow")),
            "{triple}: the slow path stays an external call: {undefined:?}"
        );
    }
}
