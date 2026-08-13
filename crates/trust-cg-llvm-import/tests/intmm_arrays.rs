// trust-cg-llvm-import / tests / intmm_arrays.rs
//
// Focused coverage for the fixed-array globals and GEP shapes emitted by
// clang -O0 for SingleSource/Benchmarks/Stanford/IntMM.c.

use trust_cg_llvm_import::{Error, import_text};
use trust_ir::{BinOp, Constant, Function, Module, Ty, inst::Inst};

fn function<'a>(module: &'a Module, name: &str) -> &'a Function {
    module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("function `{name}` not found"))
}

fn i64_constants(func: &Function) -> Vec<i128> {
    func.blocks
        .iter()
        .flat_map(|block| block.body.iter())
        .filter_map(|node| match &node.inst {
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(value),
            } => Some(*value),
            _ => None,
        })
        .collect()
}

fn gep_shapes(func: &Function) -> Vec<(Ty, usize)> {
    func.blocks
        .iter()
        .flat_map(|block| block.body.iter())
        .filter_map(|node| match &node.inst {
            Inst::GEP {
                pointee_ty,
                indices,
                ..
            } => Some((pointee_ty.clone(), indices.len())),
            _ => None,
        })
        .collect()
}

fn copy_count(func: &Function) -> usize {
    func.blocks
        .iter()
        .flat_map(|block| block.body.iter())
        .filter(|node| matches!(node.inst, Inst::Copy { .. }))
        .count()
}

fn i64_mul_count(func: &Function) -> usize {
    func.blocks
        .iter()
        .flat_map(|block| block.body.iter())
        .filter(|node| {
            matches!(
                node.inst,
                Inst::BinOp {
                    op: BinOp::Mul,
                    ty: Ty::I64,
                    ..
                }
            )
        })
        .count()
}

#[test]
fn intmm_globals_are_flattened_to_bytes() {
    let src = r#"
%struct.Pair = type { i32, float }

@seed = common global i64 0, align 8
@ima = common global [41 x [41 x i32]] zeroinitializer, align 4
@flt = internal global [2 x [3 x float]] zeroinitializer, align 4
@pairs = internal global [4 x %struct.Pair] zeroinitializer, align 4
"#;
    let module = import_text(src, "intmm_arrays").expect("import fixed array globals");
    assert_eq!(module.globals.len(), 4);

    let seed = &module.globals[0];
    assert_eq!(seed.name, "seed");
    assert_eq!(seed.ty, Ty::Ptr);
    let Some(Constant::Aggregate(seed_bytes)) = &seed.initializer else {
        panic!("expected flattened byte aggregate for @seed");
    };
    assert_eq!(seed_bytes.len(), 8);
    assert!(seed_bytes.iter().all(|byte| *byte == Constant::Int(0)));

    let ima = &module.globals[1];
    assert_eq!(ima.name, "ima");
    assert_eq!(ima.ty, Ty::Ptr);
    assert!(ima.mutable);
    let Some(Constant::Aggregate(ima_bytes)) = &ima.initializer else {
        panic!("expected flattened byte aggregate for @ima");
    };
    assert_eq!(ima_bytes.len(), 41 * 41 * 4);
    assert!(ima_bytes.iter().all(|byte| *byte == Constant::Int(0)));

    let flt = &module.globals[2];
    let Some(Constant::Aggregate(flt_bytes)) = &flt.initializer else {
        panic!("expected flattened byte aggregate for @flt");
    };
    assert_eq!(flt_bytes.len(), 2 * 3 * 4);

    let pairs = &module.globals[3];
    let Some(Constant::Aggregate(pair_bytes)) = &pairs.initializer else {
        panic!("expected flattened byte aggregate for @pairs");
    };
    assert_eq!(pair_bytes.len(), 4 * 8);
}

#[test]
fn intmm_matrix_geps_use_byte_offsets_not_copy_fallback() {
    let src = r#"
@imr = common global [41 x [41 x i32]] zeroinitializer, align 4

define ptr @global_row(i64 %row) {
entry:
  %p = getelementptr inbounds [41 x [41 x i32]], ptr @imr, i64 0, i64 %row
  ret ptr %p
}

define ptr @matrix_row(ptr %matrix, i64 %row) {
entry:
  %p = getelementptr inbounds [41 x i32], ptr %matrix, i64 %row
  ret ptr %p
}

define ptr @row_col(ptr %row, i64 %col) {
entry:
  %p = getelementptr inbounds [41 x i32], ptr %row, i64 0, i64 %col
  ret ptr %p
}
"#;
    let module = import_text(src, "intmm_geps").expect("import IntMM GEP shapes");

    for (name, stride) in [("global_row", 164), ("matrix_row", 164), ("row_col", 4)] {
        let func = function(&module, name);
        assert_eq!(
            gep_shapes(func),
            vec![(Ty::I8, 1)],
            "{name} should lower to a single byte-offset GEP"
        );
        assert_eq!(
            copy_count(func),
            0,
            "{name} must not fall through to Inst::Copy"
        );
        assert!(
            i64_constants(func).contains(&stride),
            "{name} should materialize byte stride {stride}"
        );
        assert_eq!(
            i64_mul_count(func),
            1,
            "{name} should scale the dynamic index exactly once"
        );
    }
}

#[test]
fn external_aggregate_declarations_stay_unsupported() {
    let src = r#"
@arr = external global [2 x [2 x i32]], align 4
"#;
    let result = import_text(src, "external_aggregate");
    match result {
        Err(Error::Unsupported(message)) => {
            assert!(
                message.contains("non-scalar global @arr"),
                "unexpected unsupported reason: {message}"
            );
        }
        other => panic!("external aggregate declaration should be unsupported, got {other:?}"),
    }
}
