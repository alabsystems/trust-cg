// R13 — THE NAT REDUCER, LIVE: native == JIT over Clean's literal-arithmetic
// Nat reducer (reduce_nat / is_def_eq_offset) compiled through Trust
// (Rust -> MIR -> trust-ir -> trust-cg -> machine code). SOUNDNESS-CRITICAL:
// a wrong Nat literal reduction proves False (2+2 =?= 5). No prior round
// exercised reduce_nat — every scenario returned None on the R6..R12 stub.
//
// Slice: crates/trust-cg-codegen/tests/slices/clean_nat_reduce_slice.rs.
// Deterministic regeneration on the aarch64 macOS bootstrap host:
//   T=$HOME/trust
//   S=$T/build/aarch64-apple-darwin/stage1
//   F=$T/first-party/trust-ir/frontend
//   C=$T/first-party/trust-cg
//   cd "$F"
//   env -u RUSTUP_TOOLCHAIN TRUST_NO_VERIFY=1 RUSTC="$S/bin/rustc" \
//     DYLD_LIBRARY_PATH="$S/lib" \
//     "$F/target/stage1-private/debug/trust_ir_mir" \
//     "$C/crates/trust-cg-codegen/tests/slices/clean_nat_reduce_slice.rs" \
//     --crate-type=lib --mir-emit-closure <root> <out.tir>
//   roots/outputs: nat_arith_root -> clean_nat_reduce_arith.tir,
//     nat_defeq_root -> clean_nat_reduce_defeq.tir,
//     nat_mulpow_root -> clean_nat_reduce_mulpow.tir.
// `TRUST_NO_VERIFY=1` is the compiler's documented nested-tool transport: the
// driver translates it to the tracked `-Zno-trust-verify` option. This analysis
// tool validates every emitted TrustIR module itself (`validate_module = 0`).
// Rebuild the prepared frontend driver as documented in frontend/Cargo.toml.
//
// Per-process under `perl -e 'alarm 600; exec @ARGV' -- <bin> --test-threads=1`.
#![allow(clippy::all)]
#![allow(dead_code)]
#![allow(non_snake_case)]
#![allow(unused_imports)]

use std::collections::HashMap;
use std::sync::Arc;
use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

// The native oracle: the slice compiled as a Rust module.
#[path = "slices/clean_nat_reduce_slice.rs"]
pub mod rn;

// The VERBATIM MIR-emitted trust-ir closures of the three roots, embedded from
// the in-repo regeneration artifacts (emit recipe in the header; re-emit and
// diff to reproduce). Each is `validate_module = 0`.
const ARITH_TIR: &str = include_str!("clean_nat_reduce_arith.tir");
const DEFEQ_TIR: &str = include_str!("clean_nat_reduce_defeq.tir");
const MULPOW_TIR: &str = include_str!("clean_nat_reduce_mulpow.tir");
fn tir(root: &str) -> String {
    match root {
        "nat_arith_root" => ARITH_TIR.to_string(),
        "nat_defeq_root" => DEFEQ_TIR.to_string(),
        "nat_mulpow_root" => MULPOW_TIR.to_string(),
        _ => panic!("unknown root {root}"),
    }
}

// ── shims (Vec<u64> + Arc<Expr> + Option/Try + num) ──
extern "C" fn s_alloc(size: usize, align: usize) -> *mut u8 {
    unsafe { std::alloc::alloc(std::alloc::Layout::from_size_align(size, align).unwrap()) }
}
extern "C" fn s_dealloc(ptr: *mut u8, size: usize, align: usize) {
    unsafe {
        std::alloc::dealloc(
            ptr,
            std::alloc::Layout::from_size_align(size, align).unwrap(),
        )
    }
}
extern "C" fn s_realloc(ptr: *mut u8, size: usize, align: usize, new_size: usize) -> *mut u8 {
    unsafe {
        std::alloc::realloc(
            ptr,
            std::alloc::Layout::from_size_align(size, align).unwrap(),
            new_size,
        )
    }
}

extern "C" fn v_new(sret: *mut Vec<u64>) {
    unsafe {
        std::ptr::write(sret, Vec::new());
    }
}
extern "C" fn v_push(v: *mut Vec<u64>, val: u64) {
    unsafe {
        (*v).push(val);
    }
}
extern "C" fn v_len(v: *const Vec<u64>) -> u64 {
    unsafe { (*v).len() as u64 }
}
extern "C" fn v_pop(sret: *mut Option<u64>, v: *mut Vec<u64>) {
    unsafe {
        std::ptr::write(sret, (*v).pop());
    }
}
extern "C" fn v_clone(sret: *mut Vec<u64>, this: *const Vec<u64>) {
    unsafe {
        std::ptr::write(sret, (*this).clone());
    }
}
extern "C" fn v_index(v: *const Vec<u64>, idx: u64) -> *const u64 {
    unsafe {
        let s: &[u64] = (*v).as_slice();
        assert!((idx as usize) < s.len(), "vec idx oob");
        s.as_ptr().add(idx as usize)
    }
}
extern "C" fn v_index_mut(v: *mut Vec<u64>, idx: u64) -> *mut u64 {
    unsafe {
        let s: &mut [u64] = (*v).as_mut_slice();
        assert!((idx as usize) < s.len(), "vec idx_mut oob");
        s.as_mut_ptr().add(idx as usize)
    }
}

extern "C" fn s_ovf_add(sret: *mut (u64, bool), a: u64, b: u64) {
    unsafe {
        std::ptr::write(sret, a.overflowing_add(b));
    }
}
extern "C" fn s_ovf_sub(sret: *mut (u64, bool), a: u64, b: u64) {
    unsafe {
        std::ptr::write(sret, a.overflowing_sub(b));
    }
}
extern "C" fn s_wrap_mul(a: u64, b: u64) -> u64 {
    a.wrapping_mul(b)
}
extern "C" fn s_lead_zeros(a: u64) -> u32 {
    a.leading_zeros()
}

// &u64 Div/Rem (checked_div_rem_big Small fast path).
extern "C" fn s_ref_div(a: *const u64, b: *const u64) -> u64 {
    unsafe { (*a) / (*b) }
}
extern "C" fn s_ref_rem(a: *const u64, b: *const u64) -> u64 {
    unsafe { (*a) % (*b) }
}
// &u32 PartialEq/PartialOrd (Sort/BVar/Proj eq; Reducibility::compare gt/lt).
// The receiver of `<&u32 as PartialEq/PartialOrd>::{eq,gt,lt}` is `&&u32` — a
// DOUBLE pointer (`&self` where Self = &u32). (Div/Rem take self BY VALUE, so
// those are single pointers.)
extern "C" fn s_ref_u32_eq(a: *const *const u32, b: *const *const u32) -> bool {
    unsafe { (**a) == (**b) }
}
extern "C" fn s_ref_u32_gt(a: *const *const u32, b: *const *const u32) -> bool {
    unsafe { (**a) > (**b) }
}
extern "C" fn s_ref_u32_lt(a: *const *const u32, b: *const *const u32) -> bool {
    unsafe { (**a) < (**b) }
}

// Arc<Expr> clone / as_ref.
extern "C" fn s_arc_expr_clone(sret: *mut Arc<rn::Expr>, this: *const Arc<rn::Expr>) {
    unsafe {
        std::ptr::write(sret, Arc::clone(&*this));
    }
}
extern "C" fn s_arc_expr_as_ref(arc_ref: *const *const u8) -> *const rn::Expr {
    unsafe { (*arc_ref).add(16) as *const rn::Expr }
}

// Option<Expr>::is_some.
extern "C" fn s_opt_expr_is_some(this: *const Option<rn::Expr>) -> bool {
    unsafe { (*this).is_some() }
}

// `?` operator leaves (real std Try/FromResidual semantics, retyped).
extern "C" fn s_opt_bignat_branch(
    sret: *mut std::ops::ControlFlow<Option<std::convert::Infallible>, rn::BigNat>,
    this: *const Option<rn::BigNat>,
) {
    unsafe {
        let cf = match std::ptr::read(this) {
            Some(v) => std::ops::ControlFlow::Continue(v),
            None => std::ops::ControlFlow::Break(None),
        };
        std::ptr::write(sret, cf);
    }
}
extern "C" fn s_opt_u64_branch(
    sret: *mut std::ops::ControlFlow<Option<std::convert::Infallible>, u64>,
    this: *const Option<u64>,
) {
    unsafe {
        let cf = match std::ptr::read(this) {
            Some(v) => std::ops::ControlFlow::Continue(v),
            None => std::ops::ControlFlow::Break(None),
        };
        std::ptr::write(sret, cf);
    }
}
extern "C" fn s_opt_expr_from_residual(
    sret: *mut Option<rn::Expr>,
    _residual: *const Option<std::convert::Infallible>,
) {
    unsafe {
        std::ptr::write(sret, None);
    }
}

// <u32 as TryFrom<u64>>::try_from  (checked_pow_big; mulpow only).
extern "C" fn s_u32_try_from_u64(sret: *mut Result<u32, std::num::TryFromIntError>, val: u64) {
    unsafe {
        std::ptr::write(sret, u32::try_from(val));
    }
}

/// Semantic identities for the deliberately modeled std leaves in this slice.
///
/// Rust-v0 symbols contain compiler/crate disambiguator hashes. Pinning the
/// complete symbol made a routine fixture regeneration look like a missing
/// semantic model whenever those hashes changed. We instead classify only the
/// stable, length-encoded path/type fragments and then bind the *exact* symbol
/// present in the parsed module. Unknown symbols still fail closed.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
enum NatExtern {
    Alloc,
    Dealloc,
    Realloc,
    VecNew,
    VecPush,
    VecLen,
    VecPop,
    VecClone,
    VecIndex,
    VecIndexMut,
    OverflowingAdd,
    OverflowingSub,
    WrappingMul,
    LeadingZeros,
    RefDiv,
    RefRem,
    RefU32Eq,
    RefU32Gt,
    RefU32Lt,
    ArcExprClone,
    ArcExprAsRef,
    OptionExprIsSome,
    OptionBigNatBranch,
    OptionU64Branch,
    OptionExprFromResidual,
    U32TryFromU64,
}

fn classify_nat_extern(name: &str) -> Option<NatExtern> {
    if !name.starts_with("_R") {
        return match name {
            "__rust_alloc" => Some(NatExtern::Alloc),
            "__rust_dealloc" => Some(NatExtern::Dealloc),
            "__rust_realloc" => Some(NatExtern::Realloc),
            _ => None,
        };
    }
    let has = |fragment: &str| name.contains(fragment);
    Some(match name {
        _ if has("5alloc3vec") && has("3VecyE3new") => NatExtern::VecNew,
        _ if has("5alloc3vec") && has("3VecyE4push") => NatExtern::VecPush,
        _ if has("5alloc3vec") && has("3VecyE3len") => NatExtern::VecLen,
        _ if has("5alloc3vec") && has("3VecyE3pop") => NatExtern::VecPop,
        _ if has("5alloc3vec") && has("3VecyE") && has("5clone5Clone5clone") => NatExtern::VecClone,
        _ if has("5alloc3vec") && has("5IndexjE5index") => NatExtern::VecIndex,
        _ if has("5alloc3vec") && has("8IndexMutjE9index_mut") => NatExtern::VecIndexMut,
        _ if has("4core3numy15overflowing_add") => NatExtern::OverflowingAdd,
        _ if has("4core3numy15overflowing_sub") => NatExtern::OverflowingSub,
        _ if has("4core3numy12wrapping_mul") => NatExtern::WrappingMul,
        _ if has("4core3numy13leading_zeros") => NatExtern::LeadingZeros,
        _ if has("4core3ops5arithRy") && has("3Div3div") => NatExtern::RefDiv,
        _ if has("4core3ops5arithRy") && has("3Rem3rem") => NatExtern::RefRem,
        _ if has("4core3cmp5implsRm") && has("9PartialEq2eq") => NatExtern::RefU32Eq,
        _ if has("4core3cmp5implsRm") && has("10PartialOrd2gt") => NatExtern::RefU32Gt,
        _ if has("4core3cmp5implsRm") && has("10PartialOrd2lt") => NatExtern::RefU32Lt,
        _ if has("5alloc4sync") && has("3Arc") && has("4ExprE") && has("5clone5Clone5clone") => {
            NatExtern::ArcExprClone
        }
        _ if has("5alloc4sync")
            && has("3Arc")
            && has("4ExprE")
            && has("7convert5AsRef")
            && has("6as_ref") =>
        {
            NatExtern::ArcExprAsRef
        }
        _ if has("4core6option") && has("6Option") && has("4ExprE7is_some") => {
            NatExtern::OptionExprIsSome
        }
        _ if has("4core6option") && has("6BigNatE") && has("3Try6branch") => {
            NatExtern::OptionBigNatBranch
        }
        _ if has("4core6option") && has("6OptionyE") && has("3Try6branch") => {
            NatExtern::OptionU64Branch
        }
        _ if has("4core6option") && has("4ExprE") && has("13from_residual") => {
            NatExtern::OptionExprFromResidual
        }
        _ if has("4core7convert3numm") && has("7TryFromyE8try_from") => NatExtern::U32TryFromU64,
        _ => return None,
    })
}

fn nat_extern_signature(kind: NatExtern) -> (Vec<trust_ir::Ty>, Vec<trust_ir::Ty>) {
    use trust_ir::Ty::{Bool, Ptr, U32, U64};

    match kind {
        NatExtern::Alloc => (vec![U64, U64], vec![Ptr]),
        NatExtern::Dealloc => (vec![Ptr, U64, U64], vec![]),
        NatExtern::Realloc => (vec![Ptr, U64, U64, U64], vec![Ptr]),
        NatExtern::VecNew => (vec![Ptr], vec![]),
        NatExtern::VecPush => (vec![Ptr, U64], vec![]),
        NatExtern::VecLen => (vec![Ptr], vec![U64]),
        NatExtern::VecPop | NatExtern::VecClone => (vec![Ptr, Ptr], vec![]),
        NatExtern::VecIndex | NatExtern::VecIndexMut => (vec![Ptr, U64], vec![Ptr]),
        NatExtern::OverflowingAdd | NatExtern::OverflowingSub => (vec![Ptr, U64, U64], vec![]),
        NatExtern::WrappingMul => (vec![U64, U64], vec![U64]),
        NatExtern::LeadingZeros => (vec![U64], vec![U32]),
        NatExtern::RefDiv | NatExtern::RefRem => (vec![Ptr, Ptr], vec![U64]),
        NatExtern::RefU32Eq | NatExtern::RefU32Gt | NatExtern::RefU32Lt => {
            (vec![Ptr, Ptr], vec![Bool])
        }
        NatExtern::ArcExprClone => (vec![Ptr, Ptr], vec![]),
        NatExtern::ArcExprAsRef => (vec![Ptr], vec![Ptr]),
        NatExtern::OptionExprIsSome => (vec![Ptr], vec![Bool]),
        NatExtern::OptionBigNatBranch | NatExtern::OptionU64Branch => (vec![Ptr, Ptr], vec![]),
        NatExtern::OptionExprFromResidual => (vec![Ptr], vec![]),
        NatExtern::U32TryFromU64 => (vec![Ptr, U64], vec![]),
    }
}

fn validate_nat_extern_signature(
    module: &trust_ir::Module,
    function: &trust_ir::Function,
    kind: NatExtern,
) -> Result<(), String> {
    let actual = module.func_type(function.ty).ok_or_else(|| {
        format!(
            "Nat fixture extern `{}` references missing function type {:?}",
            function.name, function.ty
        )
    })?;
    let (expected_params, expected_returns) = nat_extern_signature(kind);
    if actual.is_vararg || actual.params != expected_params || actual.returns != expected_returns {
        return Err(format!(
            "Nat fixture extern `{}` classified as {kind:?} has signature {:?} -> {:?}{}; expected {:?} -> {:?}",
            function.name,
            actual.params,
            actual.returns,
            if actual.is_vararg { " (vararg)" } else { "" },
            expected_params,
            expected_returns,
        ));
    }
    Ok(())
}

fn nat_extern_ptr(kind: NatExtern) -> *const u8 {
    match kind {
        NatExtern::Alloc => s_alloc as *const u8,
        NatExtern::Dealloc => s_dealloc as *const u8,
        NatExtern::Realloc => s_realloc as *const u8,
        NatExtern::VecNew => v_new as *const u8,
        NatExtern::VecPush => v_push as *const u8,
        NatExtern::VecLen => v_len as *const u8,
        NatExtern::VecPop => v_pop as *const u8,
        NatExtern::VecClone => v_clone as *const u8,
        NatExtern::VecIndex => v_index as *const u8,
        NatExtern::VecIndexMut => v_index_mut as *const u8,
        NatExtern::OverflowingAdd => s_ovf_add as *const u8,
        NatExtern::OverflowingSub => s_ovf_sub as *const u8,
        NatExtern::WrappingMul => s_wrap_mul as *const u8,
        NatExtern::LeadingZeros => s_lead_zeros as *const u8,
        NatExtern::RefDiv => s_ref_div as *const u8,
        NatExtern::RefRem => s_ref_rem as *const u8,
        NatExtern::RefU32Eq => s_ref_u32_eq as *const u8,
        NatExtern::RefU32Gt => s_ref_u32_gt as *const u8,
        NatExtern::RefU32Lt => s_ref_u32_lt as *const u8,
        NatExtern::ArcExprClone => s_arc_expr_clone as *const u8,
        NatExtern::ArcExprAsRef => s_arc_expr_as_ref as *const u8,
        NatExtern::OptionExprIsSome => s_opt_expr_is_some as *const u8,
        NatExtern::OptionBigNatBranch => s_opt_bignat_branch as *const u8,
        NatExtern::OptionU64Branch => s_opt_u64_branch as *const u8,
        NatExtern::OptionExprFromResidual => s_opt_expr_from_residual as *const u8,
        NatExtern::U32TryFromU64 => s_u32_try_from_u64 as *const u8,
    }
}

fn externs(module: &trust_ir::Module) -> Result<HashMap<String, *const u8>, String> {
    // Allocation intrinsics are referenced by modeled Vec/Arc shims during
    // lowering and need not appear as blockless TrustIR declarations.
    let mut externs = HashMap::from([
        ("__rust_alloc".to_string(), nat_extern_ptr(NatExtern::Alloc)),
        (
            "__rust_dealloc".to_string(),
            nat_extern_ptr(NatExtern::Dealloc),
        ),
        (
            "__rust_realloc".to_string(),
            nat_extern_ptr(NatExtern::Realloc),
        ),
    ]);
    let mut semantic_symbols: HashMap<NatExtern, String> = HashMap::new();
    for function in module
        .functions
        .iter()
        .filter(|function| function.blocks.is_empty())
    {
        let kind = classify_nat_extern(&function.name).ok_or_else(|| {
            format!(
                "unmodeled Nat fixture extern `{}`; add an exact semantic shim classification",
                function.name
            )
        })?;
        validate_nat_extern_signature(module, function, kind)?;

        if let Some(previous) = semantic_symbols.get(&kind) {
            if previous != &function.name {
                return Err(format!(
                    "Nat fixture has duplicate semantic extern identity {kind:?}: `{previous}` and `{}`",
                    function.name
                ));
            }
        } else {
            semantic_symbols.insert(kind, function.name.clone());
        }

        let ptr = nat_extern_ptr(kind);
        if let Some(previous) = externs.insert(function.name.clone(), ptr) {
            if previous != ptr {
                return Err(format!(
                    "Nat fixture extern `{}` resolves to conflicting shim pointers",
                    function.name
                ));
            }
            // The closure emitter can repeat one exact empty declaration at
            // multiple call sites. Identical name/type/semantic repetitions
            // are one declaration identity, not two independently modeled
            // externs.
        }
    }
    Ok(externs)
}

#[test]
fn nat_extern_bindings_accept_only_exact_current_fixture_contracts() {
    for (what, text) in [
        ("arith", ARITH_TIR),
        ("defeq", DEFEQ_TIR),
        ("mulpow", MULPOW_TIR),
    ] {
        let module = parse_validate(text, what);
        let bindings = externs(&module)
            .unwrap_or_else(|error| panic!("{what} exact extern contract rejected: {error}"));
        for function in module
            .functions
            .iter()
            .filter(|function| function.blocks.is_empty())
        {
            assert!(
                bindings.contains_key(&function.name),
                "{what} exact extern `{}` was not bound",
                function.name
            );
        }
    }
}

#[test]
fn nat_extern_classifier_rejects_wrong_monomorphized_types() {
    let module = parse_validate(ARITH_TIR, "arith classifier type exactness");
    let arc_expr = module
        .functions
        .iter()
        .filter(|function| function.blocks.is_empty())
        .find(|function| classify_nat_extern(&function.name) == Some(NatExtern::ArcExprClone))
        .expect("arith fixture must import Arc<Expr>::clone")
        .name
        .clone();
    let arc_bignat = arc_expr.replacen("4ExprE", "6BigNatE", 1);
    assert_ne!(arc_bignat, arc_expr);
    assert_eq!(
        classify_nat_extern(&arc_bignat),
        None,
        "Arc<BigNat>::clone must not bind the Arc<Expr> shim"
    );

    let vec_u64 = module
        .functions
        .iter()
        .filter(|function| function.blocks.is_empty())
        .find(|function| classify_nat_extern(&function.name) == Some(NatExtern::VecLen))
        .expect("arith fixture must import Vec<u64>::len")
        .name
        .clone();
    let vec_u32 = vec_u64.replacen("3VecyE", "3VecmE", 1);
    assert_ne!(vec_u32, vec_u64);
    assert_eq!(
        classify_nat_extern(&vec_u32),
        None,
        "Vec<u32>::len must not bind the Vec<u64> shim"
    );
}

#[test]
fn nat_extern_bindings_reject_signature_drift() {
    let mut module = parse_validate(ARITH_TIR, "arith extern signature mutation");
    let wrong_ty = module.add_func_type(trust_ir::FuncTy {
        params: vec![trust_ir::Ty::Ptr, trust_ir::Ty::U64],
        returns: vec![trust_ir::Ty::U64],
        is_vararg: false,
    });
    let function = module
        .functions
        .iter_mut()
        .filter(|function| function.blocks.is_empty())
        .find(|function| classify_nat_extern(&function.name) == Some(NatExtern::OverflowingAdd))
        .expect("arith fixture must import u64::overflowing_add");
    function.ty = wrong_ty;

    let error = externs(&module).expect_err("wrong shim signature must fail closed");
    assert!(
        error.contains("OverflowingAdd"),
        "wrong semantic identity in: {error}"
    );
    assert!(
        error.contains("expected"),
        "missing exact signature diagnostic: {error}"
    );
}

#[test]
fn nat_extern_bindings_reject_unknown_and_duplicate_semantic_symbols() {
    let module = parse_validate(ARITH_TIR, "arith extern identity mutation");
    let original = module
        .functions
        .iter()
        .filter(|function| function.blocks.is_empty())
        .find(|function| classify_nat_extern(&function.name) == Some(NatExtern::VecLen))
        .expect("arith fixture must import Vec<u64>::len")
        .clone();

    let mut unknown_module = module.clone();
    let mut unknown = original.clone();
    unknown.name = "_Runmodeled_nat_fixture_leaf".to_string();
    unknown_module.functions.push(unknown);
    let error = externs(&unknown_module).expect_err("unknown extern must fail closed");
    assert!(
        error.contains("unmodeled Nat fixture extern"),
        "wrong error: {error}"
    );

    let mut duplicate_module = module;
    let mut duplicate = original;
    duplicate.name = format!("_Rduplicate_{}", duplicate.name);
    duplicate_module.functions.push(duplicate);
    let error = externs(&duplicate_module)
        .expect_err("two distinct symbols for one semantic shim must fail closed");
    assert!(
        error.contains("duplicate semantic extern identity"),
        "wrong error: {error}"
    );
    assert!(
        error.contains("VecLen"),
        "missing duplicate identity detail: {error}"
    );
}

fn parse_validate(text: &str, what: &str) -> trust_ir::Module {
    let m = trust_ir::parser::parse_module(text).unwrap_or_else(|e| panic!("{what} parse: {e:?}"));
    let errs = trust_ir_build::validate_module(&m);
    assert!(errs.is_empty(), "{what} validate: {errs:?}");
    m
}

fn jit(text: &str, what: &str) -> trust_cg_codegen::jit::ExecutableBuffer {
    let module = parse_validate(text, what);
    let ext = externs(&module).unwrap_or_else(|error| panic!("{what} extern binding: {error}"));
    for f in &module.functions {
        if f.blocks.is_empty() {
            assert!(
                ext.contains_key(&f.name),
                "unbound extern `{}` in {what}",
                f.name
            );
        }
    }
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(&module, &ext)
        .unwrap_or_else(|e| panic!("JIT compile {what} failed: {e:?}"))
        .buffer
}

fn bind(buf: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buf.get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("sym {sym} not found"))
        .as_ptr()
}

// ── ArithResult mirror (must match rn::ArithResult layout) ──
type ArithFn = extern "C" fn(*mut rn::ArithResult, u64, u64, u64, u64, u64);
type DefeqFn = extern "C" fn(u64) -> u64;

fn ar_default() -> rn::ArithResult {
    rn::ArithResult {
        reduced: 0,
        kind: 3,
        lo: 0,
        hi: 0,
        nlimbs: 0,
        hash: 0,
    }
}
fn ar_eq(a: &rn::ArithResult, b: &rn::ArithResult) -> bool {
    a.reduced == b.reduced
        && a.kind == b.kind
        && a.lo == b.lo
        && a.hi == b.hi
        && a.nlimbs == b.nlimbs
        && a.hash == b.hash
}
// oracle comparison ignores the meta hash (the oracle is value-only).
fn ar_eq_value(a: &rn::ArithResult, b: &rn::ArithResult) -> bool {
    a.reduced == b.reduced
        && a.kind == b.kind
        && a.lo == b.lo
        && a.hi == b.hi
        && a.nlimbs == b.nlimbs
}
fn ar_str(a: &rn::ArithResult) -> String {
    format!(
        "{{reduced:{},kind:{},lo:{},hi:{},nlimbs:{},hash:{:#x}}}",
        a.reduced, a.kind, a.lo, a.hi, a.nlimbs, a.hash
    )
}

fn native_arith(op: u64, a_lo: u64, a_hi: u64, b_lo: u64, b_hi: u64) -> rn::ArithResult {
    let mut out = ar_default();
    rn::nat_arith_root(&mut out as *mut rn::ArithResult, op, a_lo, a_hi, b_lo, b_hi);
    out
}
fn jit_arith(f: ArithFn, op: u64, a_lo: u64, a_hi: u64, b_lo: u64, b_hi: u64) -> rn::ArithResult {
    let mut out = ar_default();
    f(&mut out as *mut rn::ArithResult, op, a_lo, a_hi, b_lo, b_hi);
    out
}

// ── the INDEPENDENT host oracle (u128, not the slice transcription) ──
// Returns (reduced, kind, lo, hi, nlimbs). kind: 0 nat, 1 bool_true, 2 bool_false.
fn oracle(op: u64, a: u128, b: u128) -> (u64, u64, u64, u64, u64) {
    let nat = |v: u128| -> (u64, u64, u64, u64, u64) {
        let lo = v as u64;
        let hi = (v >> 64) as u64;
        let nlimbs = if hi != 0 { 2 } else { 1 };
        (1, 0, lo, hi, nlimbs)
    };
    let boolean = |t: bool| -> (u64, u64, u64, u64, u64) { (1, if t { 1 } else { 2 }, 0, 0, 0) };
    match op {
        0 => nat(a + b),                          // add
        1 => nat(if a > b { a - b } else { 0 }),  // sub (floored)
        3 => nat(if b == 0 { 0 } else { a / b }), // div
        4 => nat(if b == 0 { a } else { a % b }), // mod
        5 => {
            // gcd
            let mut x = a;
            let mut y = b;
            while y != 0 {
                let r = x % y;
                x = y;
                y = r;
            }
            nat(x)
        }
        7 => boolean(a == b), // beq
        8 => boolean(a <= b), // ble
        9 => nat(a & b),      // land
        10 => nat(a | b),     // lor
        11 => nat(a ^ b),     // xor
        12 => {
            // shl (bounded)
            if a == 0 {
                return nat(0);
            }
            let sh = b;
            if sh > 1024 {
                return (0, 3, 0, 0, 0);
            }
            // only model results fitting u128 in the sweep
            let v = a << sh;
            nat(v)
        }
        13 => {
            // shr
            if b > (u64::MAX as u128) / 2 {
                return nat(0);
            }
            nat(a >> b)
        }
        14 => nat(a + 1),                         // succ
        15 => nat(if a > 0 { a - 1 } else { 0 }), // pred (floored)
        _ => (0, 3, 0, 0, 0),
    }
}

fn oracle_ar(op: u64, a: u128, b: u128) -> rn::ArithResult {
    let (reduced, kind, lo, hi, nlimbs) = oracle(op, a, b);
    rn::ArithResult {
        reduced,
        kind,
        lo,
        hi,
        nlimbs,
        hash: 0,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 1 — module sanity + hook wiring.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn nat_module_sanity_and_hook_wiring() {
    for root in ["nat_arith_root", "nat_defeq_root", "nat_mulpow_root"] {
        let text = tir(root);
        let m = parse_validate(&text, root);
        let bodied = |sym: &str| {
            m.functions
                .iter()
                .any(|f| f.name == sym && !f.blocks.is_empty())
        };
        assert!(
            bodied("Verifier__reduce_nat"),
            "{root}: the shared engine reduce_nat must be bodied (live)"
        );
        assert!(
            !m.functions.iter().any(|function| {
                function.name.contains("6BigNatE3map") && function.name.contains("10bignat_lit")
            }),
            "{root}: Option<BigNat>::map must be inlined before TrustIR emission; a native shim would cross an unstable enum-layout ABI"
        );
    }
    // The whnf_core + lazy_delta must Call reduce_nat + is_def_eq_offset (the
    // production hook edges must genuinely RUN in machine code).
    let text = tir("nat_defeq_root");
    let m = parse_validate(&text, "nat_defeq_root");
    let idx_exact = |sym: &str| {
        m.functions
            .iter()
            .position(|f| f.name == sym)
            .unwrap_or_else(|| panic!("{sym} not in module"))
    };
    let ldi = idx_exact("Verifier__lazy_delta_reduction");
    let rni = idx_exact("Verifier__reduce_nat");
    let odi = idx_exact("Verifier__is_def_eq_offset");
    let wcn = idx_exact("Verifier__whnf_core_no_delta");
    let body = |i: usize| -> String {
        let name = &m.functions[i].name;
        let start = text.find(&format!("fn @{name}(")).unwrap();
        let after = &text[start + 1..];
        let end = after
            .find("\nfn @")
            .map(|k| start + 1 + k)
            .unwrap_or(text.len());
        text[start..end].to_string()
    };
    let ld_body = body(ldi);
    assert!(
        ld_body.contains(&format!("@func.{rni}(")),
        "lazy_delta must Call reduce_nat"
    );
    assert!(
        ld_body.contains(&format!("@func.{odi}(")),
        "lazy_delta must Call is_def_eq_offset"
    );
    // the whnf_core pre-check hook (whnf.rs:421) must also Call reduce_nat.
    assert!(
        body(wcn).contains(&format!("@func.{rni}(")),
        "whnf_core must Call reduce_nat (pre-check hook)"
    );
    eprintln!(
        "sanity: reduce_nat live and wired at BOTH hooks (lazy_delta func.{rni}/{odi}, whnf_core)"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 2 — the ARITHMETIC sweep: native == JIT == independent u128 oracle,
// bit-for-bit on the reduced BigNat limbs. THE soundness core.
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn nat_arith_native_jit_oracle_sweep() {
    let text = tir("nat_arith_root");
    let buf = jit(&text, "nat_arith_root");
    let f: ArithFn = unsafe { std::mem::transmute(bind(&buf, "nat_arith_root")) };

    // operand values (as u128; only lo/hi limbs are passed).
    let vals: &[u128] = &[
        0,
        1,
        2,
        3,
        4,
        5,
        7,
        10,
        100,
        1000,
        0xFFFF_FFFF,
        0xFFFF_FFFF_FFFF_FFFF, // 2^64-1 (Small max)
        1u128 << 63,
        (1u128 << 64), // 2^64 (Big, 2 limbs)
        (1u128 << 64) + 12345,
        (1u128 << 100),
        ((1u128 << 64) | 0xABCD), // Big with low bits
        (0xDEAD_BEEF_u128 << 64) | 0x1234_5678,
    ];
    // ops: add sub div mod gcd beq ble land lor xor succ pred (u64-safe).
    let binops: &[u64] = &[0, 1, 3, 4, 5, 7, 8, 9, 10, 11];
    let unops: &[u64] = &[14, 15];

    let split = |v: u128| -> (u64, u64) { (v as u64, (v >> 64) as u64) };
    let mut n = 0u64;
    for &op in binops {
        for &a in vals {
            for &b in vals {
                // add can overflow past 2 limbs (u128) for the largest pairs;
                // skip those (oracle only models <=2-limb results). All shown
                // results here stay within u128.
                if op == 0 && a.checked_add(b).is_none() {
                    continue;
                }
                let (a_lo, a_hi) = split(a);
                let (b_lo, b_hi) = split(b);
                let nat = native_arith(op, a_lo, a_hi, b_lo, b_hi);
                let jt = jit_arith(f, op, a_lo, a_hi, b_lo, b_hi);
                let orc = oracle_ar(op, a, b);
                assert!(
                    ar_eq(&nat, &jt),
                    "op={op} a={a} b={b}: NATIVE {} != JIT {}",
                    ar_str(&nat),
                    ar_str(&jt)
                );
                assert!(
                    ar_eq_value(&jt, &orc),
                    "op={op} a={a} b={b}: JIT {} != ORACLE {}",
                    ar_str(&jt),
                    ar_str(&orc)
                );
                n += 1;
            }
        }
    }
    // shift ops with small shift amounts (results kept within u128).
    for &op in &[12u64, 13u64] {
        for &a in vals {
            for &sh in &[0u128, 1, 2, 7, 8, 16, 30, 60] {
                if op == 12 {
                    // keep result within u128 (avoid oracle overflow).
                    if a != 0 && (128 - (a.leading_zeros())) as u128 + sh > 127 {
                        continue;
                    }
                }
                let (a_lo, a_hi) = split(a);
                let (b_lo, b_hi) = split(sh);
                let nat = native_arith(op, a_lo, a_hi, b_lo, b_hi);
                let jt = jit_arith(f, op, a_lo, a_hi, b_lo, b_hi);
                let orc = oracle_ar(op, a, sh);
                assert!(
                    ar_eq(&nat, &jt),
                    "shift op={op} a={a} sh={sh}: NATIVE {} != JIT {}",
                    ar_str(&nat),
                    ar_str(&jt)
                );
                assert!(
                    ar_eq_value(&jt, &orc),
                    "shift op={op} a={a} sh={sh}: JIT {} != ORACLE {}",
                    ar_str(&jt),
                    ar_str(&orc)
                );
                n += 1;
            }
        }
    }
    for &op in unops {
        for &a in vals {
            let (a_lo, a_hi) = split(a);
            let nat = native_arith(op, a_lo, a_hi, 0, 0);
            let jt = jit_arith(f, op, a_lo, a_hi, 0, 0);
            let orc = oracle_ar(op, a, 0);
            assert!(
                ar_eq(&nat, &jt),
                "unop={op} a={a}: NATIVE {} != JIT {}",
                ar_str(&nat),
                ar_str(&jt)
            );
            assert!(
                ar_eq_value(&jt, &orc),
                "unop={op} a={a}: JIT {} != ORACLE {}",
                ar_str(&jt),
                ar_str(&orc)
            );
            n += 1;
        }
    }
    eprintln!("arith sweep: {n} (op,a,b) triples native==JIT==oracle bit-for-bit");
    assert!(n > 900, "sweep too small: {n}");

    // NEGATIVE CONTROL: a poisoned oracle (a+b+1) must DIVERGE from the JIT on add.
    let (a_lo, a_hi) = split(2);
    let jt = jit_arith(f, 0, a_lo, a_hi, a_lo, a_hi); // 2+2 = 4
    let poisoned = rn::ArithResult {
        reduced: 1,
        kind: 0,
        lo: 5,
        hi: 0,
        nlimbs: 1,
        hash: 0,
    }; // a+b+1 = 5
    assert!(
        !ar_eq_value(&jt, &poisoned),
        "poisoned oracle (2+2=5) must diverge from JIT (2+2=4)"
    );
    eprintln!("neg-control: poisoned oracle (2+2=5) diverges from JIT (2+2=4) as required");
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 3 — decisive def_eq scenarios (a)/(b)/(c)/(d): native == JIT, and the
// blind control (reduce_nat = None) DIVERGES on exactly the Nat cases.
// ════════════════════════════════════════════════════════════════════════════
fn native_defeq(idx: u64) -> u64 {
    rn::nat_defeq_root(idx)
}
fn jit_defeq(f: DefeqFn, idx: u64) -> u64 {
    f(idx)
}

const AWARE: u64 = 0;
const BLIND_NAT: u64 = 0x100;
const BLIND_OFF: u64 = 0x200;

#[test]
fn nat_defeq_decisive_and_blind_divergence() {
    let text = tir("nat_defeq_root");
    let buf = jit(&text, "nat_defeq_root");
    let f: DefeqFn = unsafe { std::mem::transmute(bind(&buf, "nat_defeq_root")) };

    let run = |idx: u64| -> (u64, u64) { (native_defeq(idx), jit_defeq(f, idx)) };
    let agree = |idx: u64| -> u64 {
        let (n, j) = run(idx);
        assert_eq!(n, j, "native({idx}) != JIT({idx})");
        j
    };

    // (a) 2+2 =?= 4 : AWARE accept; BLIND_NAT reject (Nat.add has no delta/iota).
    assert_eq!(agree(0 | AWARE), 1, "(a) 2+2=?=4 aware must ACCEPT");
    assert_eq!(
        agree(0 | BLIND_NAT),
        0,
        "(a) 2+2=?=4 blind must REJECT — reduce_nat is load-bearing"
    );
    // (b) 2+2 =?= 5 : AWARE reject (RIGHT answer: folds to 4, 4!=5).
    assert_eq!(
        agree(1 | AWARE),
        0,
        "(b) 2+2=?=5 aware must REJECT (right answer)"
    );
    // (c1) succ^3(zero) =?= 3 : offset OR reduce_nat. In BLIND_NAT it accepts
    //      UNIQUELY via is_def_eq_offset (structural congruence can't accept
    //      App-succ vs Lit). BLIND_NAT|BLIND_OFF must then REJECT.
    assert_eq!(agree(2 | AWARE), 1, "(c1) aware accept");
    assert_eq!(
        agree(2 | BLIND_NAT),
        1,
        "(c1) blind_nat still ACCEPTs via is_def_eq_offset"
    );
    assert_eq!(
        agree(2 | BLIND_NAT | BLIND_OFF),
        0,
        "(c1) with offset ALSO off -> REJECT (offset was the decider)"
    );
    // (c2) succ(succ(n)) =?= 2 : offset peels twice then stuck -> REJECT (correct).
    assert_eq!(
        agree(3 | AWARE),
        0,
        "(c2) variable-base tower vs 2 -> REJECT"
    );
    assert_eq!(agree(3 | BLIND_NAT), 0, "(c2) blind_nat also REJECT");
    // (d) 2^63 + 2^63 =?= 2^64 : add crossing Small->Big; aware accept, blind reject.
    assert_eq!(
        agree(4 | AWARE),
        1,
        "(d) 2^63+2^63 =?= 2^64 aware ACCEPT (bignum path)"
    );
    assert_eq!(agree(4 | BLIND_NAT), 0, "(d) blind REJECT");
    // (d') 2^64 + 2^64 =?= 2^65 : Big+Big.
    assert_eq!(agree(5 | AWARE), 1, "(d') Big+Big aware ACCEPT");
    assert_eq!(agree(5 | BLIND_NAT), 0, "(d') blind REJECT");
    // (e) 10 - 3 =?= 7 : sub accept; wrong-answer 10-3=?=8 reject.
    assert_eq!(agree(6 | AWARE), 1, "(e) 10-3=?=7 aware ACCEPT");
    assert_eq!(agree(6 | BLIND_NAT), 0, "(e) blind REJECT");
    assert_eq!(
        agree(7 | AWARE),
        0,
        "(e') 10-3=?=8 aware REJECT (right answer is 7)"
    );
    // (f) and (g): the formerly pinned mul/pow arms now execute through the
    // same production-position reduce_nat hook. Blind mode proves the hook is
    // load-bearing; adjacent wrong-answer controls prove arithmetic direction.
    assert_eq!(agree(8 | AWARE), 1, "(f) 7*11=?=77 aware ACCEPT");
    assert_eq!(agree(8 | BLIND_NAT), 0, "(f) blind REJECT");
    assert_eq!(agree(9 | AWARE), 1, "(g) 3^5=?=243 aware ACCEPT");
    assert_eq!(agree(9 | BLIND_NAT), 0, "(g) blind REJECT");
    assert_eq!(agree(10 | AWARE), 0, "(f') 7*11=?=78 aware REJECT");
    assert_eq!(agree(11 | AWARE), 0, "(g') 3^5=?=244 aware REJECT");

    eprintln!(
        "decisive: (a)-(e) native==JIT; blind_nat diverges on every Nat-arith case; offset attributed"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 4 — the NON-NAT inertness set: aware verdict == blind verdict AND
// native == JIT (turning reduce_nat live changes NOTHING off the Nat path).
// ════════════════════════════════════════════════════════════════════════════
#[test]
fn nat_defeq_nonnat_inertness() {
    let text = tir("nat_defeq_root");
    let buf = jit(&text, "nat_defeq_root");
    let f: DefeqFn = unsafe { std::mem::transmute(bind(&buf, "nat_defeq_root")) };

    // (scenario, expected verdict)
    let cases: &[(u64, u64)] = &[
        (20, 1), // foo =?= foo
        (21, 0), // foo =?= bar
        (22, 1), // (λx.x) foo =?= foo (beta)
        (23, 1), // Sort 0 =?= Sort 0
        (24, 0), // Sort 0 =?= Sort 1
        (25, 1), // g foo =?= g foo
        (26, 0), // g foo =?= g bar
        (27, 1), // dfn =?= foo (delta)
    ];
    for &(sc, exp) in cases {
        for flag in [AWARE, BLIND_NAT, BLIND_NAT | BLIND_OFF] {
            let n = native_defeq(sc | flag);
            let j = jit_defeq(f, sc | flag);
            assert_eq!(n, j, "scenario {sc} flag {flag:#x}: native != JIT");
            assert_eq!(
                j, exp,
                "scenario {sc} flag {flag:#x}: verdict {j} != expected {exp} (must be inert to nat-blinding)"
            );
        }
    }
    // (scenario 28) g (2+2) =?= g 4 : reduce_nat UNDER App congruence.
    assert_eq!(native_defeq(28 | AWARE), jit_defeq(f, 28 | AWARE));
    assert_eq!(
        jit_defeq(f, 28 | AWARE),
        1,
        "g(2+2)=?=g 4 aware ACCEPT (hook composes under congruence)"
    );
    assert_eq!(jit_defeq(f, 28 | BLIND_NAT), 0, "g(2+2)=?=g 4 blind REJECT");
    assert_eq!(native_defeq(28 | BLIND_NAT), jit_defeq(f, 28 | BLIND_NAT));
    eprintln!(
        "inertness: non-Nat verdicts identical aware/blind and native==JIT; hook composes under congruence"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 5 — mul/pow clean bill after the u128 multiply lowering landed.
// ════════════════════════════════════════════════════════════════════════════
fn native_mulpow(op: u64, a_lo: u64, a_hi: u64, b_lo: u64, b_hi: u64) -> rn::ArithResult {
    let mut out = ar_default();
    rn::nat_mulpow_root(&mut out as *mut rn::ArithResult, op, a_lo, a_hi, b_lo, b_hi);
    out
}
fn oracle_mul(a: u128, b: u128) -> rn::ArithResult {
    let v = a * b;
    let lo = v as u64;
    let hi = (v >> 64) as u64;
    rn::ArithResult {
        reduced: 1,
        kind: 0,
        lo,
        hi,
        nlimbs: if hi != 0 { 2 } else { 1 },
        hash: 0,
    }
}
fn oracle_pow(a: u128, e: u32) -> rn::ArithResult {
    let mut r: u128 = 1;
    for _ in 0..e {
        r = r * a;
    }
    let lo = r as u64;
    let hi = (r >> 64) as u64;
    rn::ArithResult {
        reduced: 1,
        kind: 0,
        lo,
        hi,
        nlimbs: if hi != 0 { 2 } else { 1 },
        hash: 0,
    }
}

#[test]
fn nat_mulpow_native_jit_oracle_clean_bill() {
    let text = tir("nat_mulpow_root");
    let buf = jit(&text, "nat_mulpow_root");
    let jit_fn: ArithFn = unsafe { std::mem::transmute(bind(&buf, "nat_mulpow_root")) };

    // Native and JIT mul/pow arithmetic are both checked against the
    // independent u128 oracle, including Small/Big limb transitions.
    let muls: &[(u128, u128)] = &[
        (0, 5),
        (1, 1),
        (2, 3),
        (7, 11),
        (1000, 1000),
        (0xFFFF_FFFF, 0xFFFF_FFFF),
        (0xFFFF_FFFF_FFFF_FFFF, 2),
        (0x1_0000_0000, 0x1_0000_0000),
        (12345678, 87654321),
    ];
    let split = |v: u128| -> (u64, u64) { (v as u64, (v >> 64) as u64) };
    for &(a, b) in muls {
        let (a_lo, a_hi) = split(a);
        let (b_lo, b_hi) = split(b);
        let nat = native_mulpow(2, a_lo, a_hi, b_lo, b_hi); // op 2 = mul
        let jt = jit_arith(jit_fn, 2, a_lo, a_hi, b_lo, b_hi);
        let orc = oracle_mul(a, b);
        assert!(
            ar_eq_value(&nat, &orc),
            "NATIVE mul {a}*{b} = {} != ORACLE {}",
            ar_str(&nat),
            ar_str(&orc)
        );
        assert!(
            ar_eq(&nat, &jt),
            "mul {a}*{b}: NATIVE {} != JIT {}",
            ar_str(&nat),
            ar_str(&jt)
        );
        assert!(
            ar_eq_value(&jt, &orc),
            "JIT mul {a}*{b} = {} != ORACLE {}",
            ar_str(&jt),
            ar_str(&orc)
        );
    }
    let pows: &[(u128, u32)] = &[(2, 0), (2, 1), (2, 10), (3, 5), (10, 6), (7, 3), (2, 63)];
    for &(a, e) in pows {
        let (a_lo, a_hi) = split(a);
        let nat = native_mulpow(6, a_lo, a_hi, e as u64, 0); // op 6 = pow
        let jt = jit_arith(jit_fn, 6, a_lo, a_hi, e as u64, 0);
        let orc = oracle_pow(a, e);
        assert!(
            ar_eq_value(&nat, &orc),
            "NATIVE pow {a}^{e} = {} != ORACLE {}",
            ar_str(&nat),
            ar_str(&orc)
        );
        assert!(
            ar_eq(&nat, &jt),
            "pow {a}^{e}: NATIVE {} != JIT {}",
            ar_str(&nat),
            ar_str(&jt)
        );
        assert!(
            ar_eq_value(&jt, &orc),
            "JIT pow {a}^{e} = {} != ORACLE {}",
            ar_str(&jt),
            ar_str(&orc)
        );
    }
    // NEGATIVE CONTROL: a wrong-arithmetic poisoned oracle (a*b+1) must diverge.
    let bad = {
        let v = 1000u128 * 1000 + 1;
        rn::ArithResult {
            reduced: 1,
            kind: 0,
            lo: v as u64,
            hi: 0,
            nlimbs: 1,
            hash: 0,
        }
    };
    let good = native_mulpow(2, 1000, 0, 1000, 0);
    let jit_good = jit_arith(jit_fn, 2, 1000, 0, 1000, 0);
    assert!(
        !ar_eq_value(&good, &bad),
        "poisoned mul oracle (a*b+1) must diverge from native"
    );
    assert!(
        !ar_eq_value(&jit_good, &bad),
        "poisoned mul oracle must diverge from JIT"
    );
    eprintln!("mulpow clean bill: native==JIT==u128 oracle; poisoned oracle diverges");
}

// ════════════════════════════════════════════════════════════════════════════
// TEST 6 — ARMED negative controls: (1) golden TEXT corruption of compute_meta's
// FNV mix constant makes the reduced literal's JIT meta-hash DIVERGE from native
// (value stays correct — the differential is genuinely load-bearing on the hash
// path); (2) a poisoned arithmetic shim (overflowing_add computes a+b+1) makes
// the JIT VALUE diverge from native (the JIT genuinely runs the shim arithmetic).
// ════════════════════════════════════════════════════════════════════════════

// poisoned overflowing_add: a + b + 1 (a real miscompile of the ALU leaf).
extern "C" fn s_ovf_add_POISON(sret: *mut (u64, bool), a: u64, b: u64) {
    unsafe {
        std::ptr::write(sret, a.overflowing_add(b).0.overflowing_add(1));
    }
}

fn jit_with_externs(
    text: &str,
    what: &str,
    ext: &HashMap<String, *const u8>,
) -> trust_cg_codegen::jit::ExecutableBuffer {
    let module = parse_validate(text, what);
    for f in &module.functions {
        if f.blocks.is_empty() {
            assert!(
                ext.contains_key(&f.name),
                "unbound extern `{}` in {what}",
                f.name
            );
        }
    }
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(&module, ext)
        .unwrap_or_else(|e| panic!("JIT {what}: {e:?}"))
        .buffer
}

#[test]
fn nat_armed_golden_and_shim_corruption_controls() {
    let base = tir("nat_arith_root");
    let nat = native_arith(0, 2, 0, 2, 0); // native add(2,2) = 4, hash = H
    assert_eq!(nat.lo, 4);
    assert_eq!(nat.reduced, 1);

    // baseline: uncorrupted JIT matches native fully (value AND hash).
    {
        let buf = jit(&base, "nat_arith_root");
        let f: ArithFn = unsafe { std::mem::transmute(bind(&buf, "nat_arith_root")) };
        let jt = jit_arith(f, 0, 2, 0, 2, 0);
        assert!(
            ar_eq(&nat, &jt),
            "baseline JIT must match native fully: {} vs {}",
            ar_str(&nat),
            ar_str(&jt)
        );
    }

    // (1) ARMED golden corruption: flip the FNV mix constant in the module text.
    // add(2,2) must still VALUE-equal native (4), but the meta HASH must DIVERGE.
    {
        let corrupted = base.replace("const u64 1099511628211", "const u64 1099511628213");
        assert!(corrupted != base, "corruption must change the text");
        let buf = jit(&corrupted, "nat_arith_root(FNV-corrupted)");
        let f: ArithFn = unsafe { std::mem::transmute(bind(&buf, "nat_arith_root")) };
        let jt = jit_arith(f, 0, 2, 0, 2, 0);
        assert!(
            ar_eq_value(&nat, &jt),
            "FNV corruption must NOT change the value: {} vs {}",
            ar_str(&nat),
            ar_str(&jt)
        );
        assert!(
            nat.hash != jt.hash,
            "FNV corruption MUST change the meta hash: native {:#x} == corrupted-JIT {:#x} (differential NOT load-bearing!)",
            nat.hash,
            jt.hash
        );
        eprintln!(
            "armed(1): FNV-corrupted JIT keeps value 4 but meta-hash diverges {:#x} != {:#x}",
            nat.hash, jt.hash
        );
    }

    // (2) ARMED shim corruption: poisoned overflowing_add (a+b+1). add(2,2) JIT
    // must diverge from native (JIT computes 5, native computes 4).
    {
        let module = parse_validate(&base, "nat_arith_root(poison-add externs)");
        let mut ext = externs(&module).expect("armed Nat fixture externs must bind exactly");
        let add_symbol = module
            .functions
            .iter()
            .filter(|function| function.blocks.is_empty())
            .find(|function| classify_nat_extern(&function.name) == Some(NatExtern::OverflowingAdd))
            .map(|function| function.name.clone())
            .expect("the armed fixture must import u64::overflowing_add");
        ext.insert(add_symbol, s_ovf_add_POISON as *const u8);
        let buf = jit_with_externs(&base, "nat_arith_root(poison-add)", &ext);
        let f: ArithFn = unsafe { std::mem::transmute(bind(&buf, "nat_arith_root")) };
        let jt = jit_arith(f, 0, 2, 0, 2, 0);
        assert!(
            !ar_eq_value(&nat, &jt),
            "poisoned add shim MUST diverge from native: native {} == poisoned-JIT {}",
            ar_str(&nat),
            ar_str(&jt)
        );
        eprintln!(
            "armed(2): poisoned overflowing_add(a+b+1) -> JIT add(2,2) = {} diverges from native 4",
            jt.lo
        );
    }
}
