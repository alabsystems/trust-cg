#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / objectsize_intrinsic.rs
//
// Regression coverage for clang -O0 llvm.objectsize calls imported from LLVM IR.
// The in-tree Mach-O and ELF readers check both explicit targets on every
// host; `nm -u` reads the host triple's object on a native host.

mod common;

use std::fs;

use common::{
    HOST_TRIPLE, TARGETS, compile_for, compile_for_host, native_host_or_skip, nm_undefined,
    undefined_symbols, unique_temp_dir,
};
use trust_cg_codegen::pipeline::OptLevel;

const LL_OBJECTSIZE_INTRINSIC: &str = r#"
target triple = "arm64-apple-macosx26.0.0"

declare i64 @llvm.objectsize.i64.p0(ptr, i1 immarg, i1 immarg, i1 immarg)

define i32 @main() {
entry:
  %buf = alloca i8, i64 16, align 1
  %size = call i64 @llvm.objectsize.i64.p0(ptr %buf, i1 false, i1 true, i1 false)
  %trunc = trunc i64 %size to i32
  ret i32 %trunc
}
"#;

#[test]
fn objectsize_i64_p0_does_not_emit_runtime_symbol() {
    for triple in TARGETS {
        let object = compile_for(
            LL_OBJECTSIZE_INTRINSIC,
            "objectsize_intrinsic",
            triple,
            OptLevel::O0,
        );
        let undefined = undefined_symbols(&object);
        assert!(
            undefined
                .iter()
                .all(|name| !name.contains("llvm.objectsize")),
            "objectsize intrinsic was left as an unresolved symbol for `{triple}`: {undefined:?}"
        );
    }
    if !native_host_or_skip("objectsize_i64_p0_does_not_emit_runtime_symbol") {
        return;
    }

    let object = compile_for_host(
        LL_OBJECTSIZE_INTRINSIC,
        "objectsize_intrinsic",
        OptLevel::O0,
    );
    let dir = unique_temp_dir("objectsize");
    let obj_path = dir.join("objectsize.o");
    fs::write(&obj_path, object).expect("write object");

    let undefined = nm_undefined(&obj_path);
    assert!(
        !undefined.contains("llvm.objectsize"),
        "objectsize intrinsic was left as an unresolved symbol for `{HOST_TRIPLE}`:\n{undefined}"
    );
}
