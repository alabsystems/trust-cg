// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg(test)]
mod support;
use support::*;
mod common_arguments;

include!(concat!(env!("OUT_DIR"), "/test_build_compiler.rs"));

const PROBE: &str = r#"
pub fn pair32(p: (u32, u32)) -> u32 {
    let c = |v: (u32, u32)| v.0; c(p)
}
pub fn pair_word(p: (u32, usize)) -> u32 {
    let c = |v: (u32, usize)| v.0; c(p)
}
pub fn two_pairs(a: (u32, u32), b: (u32, usize)) -> u32 {
    let c = |x: (u32, u32), y: (u32, usize)| x.0 + y.0; c(a, b)
}
struct Z;
pub fn ignored_inputs() -> impl FnOnce((), (u32, u32), ()) -> u32 {
    let z = Z;
    move |_: (), v: (u32, u32), _: ()| { drop(z); v.0 }
}
pub fn pair_return() {
    let c = |v: u32| (v, v + 1); let _ = c(3);
}
pub fn buffer_return() {
    let c = |v: u64| [v; 5]; let _ = c(3);
}
pub fn wide_input(v: &[u32]) -> usize {
    let c = |s: &[u32]| s.len(); c(v)
}
struct Token(u64);
pub fn value_environment(k: u64) -> impl FnOnce((u32,u32)) -> u32 {
    let token = Token(k);
    move |v| { drop(token); v.0 }
}
struct Token32(u32);
struct TokenWord(usize);
pub fn pair_environment(a: u32, b: usize) -> impl FnOnce((u32,u32)) -> u32 {
    let first = Token32(a); let second = TokenWord(b);
    move |v| { drop(first); drop(second); v.0 }
}
"#;

fn check_pair(tcx: TyCtxt<'_>, name: &str, zero_env: bool) {
    let (mut ctx, instance) = closure(tcx, name);
    assert!(matches!(instance.def, ty::InstanceKind::Item(_)));
    let body = tcx.instance_mir(instance.def);
    let local = body
        .args_iter()
        .find(|arg| {
            matches!(ctx.monomorphize_ty(body.local_decls[*arg].ty).kind(),
            ty::Tuple(elements) if elements.len() == 2)
        })
        .expect("actual two-field closure argument");
    let input = ctx.normalize_ty(ctx.monomorphize_ty(body.local_decls[local].ty));
    let abi_index = rustc_fn_abi_arg_index_for_mir_arg(local).unwrap();
    let plan = ctx
        .scalar_pair_param_plan(input, abi_index, RustcFnAbiSource::Instance(instance))
        .unwrap()
        .expect("actual AArch64 closure Pair plan");
    assert_eq!(plan.ty, input);
    assert_eq!(
        plan.offsets(),
        if name == "pair_word" { [0, 8] } else { [0, 4] }
    );
    let fn_abi = RustcFnAbiSource::Instance(instance).query(tcx).unwrap();
    assert!(matches!(
        fn_abi.args[abi_index].mode,
        rustc_target::callconv::PassMode::Pair(..)
    ));
    assert_eq!(closure_body_takes_env(tcx, instance), !zero_env);
    let receiver = body.args_iter().next().expect("actual source receiver");
    let receiver_ty = ctx.normalize_ty(ctx.monomorphize_ty(body.local_decls[receiver].ty));
    let environment = if zero_env {
        assert!(is_zero_sized_ty(tcx, receiver_ty));
        assert!(matches!(
            fn_abi.args[0].mode,
            rustc_target::callconv::PassMode::Ignore
        ));
        None
    } else {
        let ty::Ref(_, closure_ty, _) = receiver_ty.kind() else {
            panic!("this source fixture has a borrowed closure receiver")
        };
        assert_eq!(
            ctx.normalize_ty(*closure_ty),
            instance.ty(tcx, ty::TypingEnv::fully_monomorphized())
        );
        // func_ty_for_instance retains a typed immutable env reference. Do
        // not erase that metadata to Ptr in the independent expectation.
        let declaration_receiver = Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, *closure_ty);
        Some(rust_ty_to_trust_ir_ty(tcx, declaration_receiver).unwrap())
    };
    let signature = ctx.func_ty_for_instance(instance).unwrap();
    let expected: Vec<_> = environment.into_iter().chain(plan.declared()).collect();
    assert_eq!(
        ctx.module.func_types[signature.index() as usize].params,
        expected
    );
    let env = ValueId::new(800);
    let slot = ValueId::new(801);
    let mut block = Block::new(BlockId::new(0));
    let arguments =
        closure_body_call_args_from_values(&mut ctx, &mut block, instance, Some(env), vec![slot])
            .unwrap();
    assert_eq!(arguments.len(), expected.len());
    if !zero_env {
        assert_eq!(arguments[0], env);
    }
    assert_eq!(
        loads(&block),
        plan.plan
            .lanes
            .iter()
            .map(|(ty, _)| ty.clone())
            .collect::<Vec<_>>()
    );
    let offsets = addresses(&block, slot);
    assert_eq!(offsets, plan.offsets());

    // Exercise actual body entry, not only the hand-built call helper. This
    // invokes the ordinary lowering and all its unchanged structural gates.
    let lowered = mir_to_trust_ir(tcx, instance, name, &mut CrateRefineMemo::default())
        .unwrap_or_else(|error| panic!("{name}: actual closure body: {error}"));
    let function = lowered
        .module
        .functions
        .iter()
        .find(|f| f.name == name)
        .expect("owned lowered closure body");
    let entry = function.blocks.first().expect("actual entry block");
    assert_eq!(
        entry
            .params
            .iter()
            .map(|(_, ty)| ty.clone())
            .collect::<Vec<_>>(),
        expected
    );
    for (lane_ty, _) in &plan.plan.lanes {
        assert!(
            entry
                .body
                .iter()
                .any(|node| matches!(&node.inst, Inst::Store { ty, .. } if ty == lane_ty))
        );
    }
}

fn check_preflight(tcx: TyCtxt<'_>) {
    let (mut ctx, instance) = closure(tcx, "two_pairs");
    let before = ctx.next_value;
    let original_module = ctx.module.clone();
    let original_copies = ctx.fresh_arg_copies.clone();
    let abi = RustcFnAbiSource::Instance(instance).query(tcx).unwrap();
    let first = ClosureArg {
        ty: abi.args[1].layout.ty,
        abi_arg_index: 1,
        src: ClosureArgSrc::Slot(ValueId::new(801)),
    };
    let second = ClosureArg {
        ty: abi.args[2].layout.ty,
        abi_arg_index: 2,
        src: ClosureArgSrc::Scalar(ValueId::new(802)),
    };
    let mut block = Block::new(BlockId::new(0));
    let error = closure_body_call_args(
        &mut ctx,
        &mut block,
        instance,
        Some(ValueId::new(800)),
        vec![first, second],
    )
    .unwrap_err();
    assert!(
        error.contains("[TCG-ARG-ABI]") && error.contains("original slot"),
        "{error}"
    );
    assert!(
        block.body.is_empty(),
        "no prefix loads before a later refusal"
    );
    assert_eq!(ctx.next_value, before);
    assert_eq!(ctx.module, original_module);
    assert_eq!(ctx.fresh_arg_copies, original_copies);
    let error = closure_call_arg_values(
        &mut ctx,
        &mut block,
        RustcFnAbiSource::Instance(instance),
        vec![first, second],
    )
    .err()
    .expect("common Fn-trait argument batch refuses a later scalar Pair source");
    assert!(
        error.contains("[TCG-ARG-ABI] closure argument 2")
            && error.contains("not its original slot bytes"),
        "{error}"
    );
    assert!(block.body.is_empty());
    assert_eq!(ctx.next_value, before);
    assert_eq!(ctx.module, original_module);
    assert_eq!(ctx.fresh_arg_copies, original_copies);
    let error = closure_body_call_args(
        &mut ctx,
        &mut block,
        instance,
        Some(ValueId::new(800)),
        vec![first],
    )
    .unwrap_err();
    assert_eq!(
        error,
        "[TCG-ARG-ABI] closure argument 2 is missing its original FnAbi input"
    );
    let error = closure_body_call_args(
        &mut ctx,
        &mut block,
        instance,
        Some(ValueId::new(800)),
        vec![first, first],
    )
    .unwrap_err();
    assert_eq!(
        error,
        "[TCG-ARG-ABI] closure argument 1 repeats its original FnAbi ordinal"
    );
    let escaped = ClosureArg {
        src: ClosureArgSrc::TupleField {
            slot: ValueId::new(802),
            offset: 16,
            tuple_size: 8,
        },
        ..second
    };
    let error = closure_body_call_args(
        &mut ctx,
        &mut block,
        instance,
        Some(ValueId::new(800)),
        vec![first, escaped],
    )
    .unwrap_err();
    assert!(
        error.contains("[TCG-ARG-ABI] closure argument 2")
            && error.contains("original tuple field escapes its enclosing byte image"),
        "{error}"
    );
    assert!(block.body.is_empty());
    assert_eq!(ctx.next_value, before);
    assert_eq!(ctx.module, original_module);
    assert_eq!(ctx.fresh_arg_copies, original_copies);
    let error = closure_body_call_args_from_values(
        &mut ctx,
        &mut block,
        instance,
        Some(ValueId::new(800)),
        vec![],
    )
    .unwrap_err();
    assert!(
        error.contains("[TCG-ARG-ABI]")
            && error.contains("passes 0 argument value(s) for 2 non-zero-sized parameter(s)"),
        "{error}"
    );
    assert!(block.body.is_empty());
    assert_eq!(ctx.next_value, before);
    // A real argument type at a stale original ordinal must not borrow a
    // different argument's ABI. Both source types come from the actual TCX.
    let stale = ClosureArg {
        abi_arg_index: 2,
        ..first
    };
    let error = closure_body_call_args(
        &mut ctx,
        &mut block,
        instance,
        Some(ValueId::new(800)),
        vec![first, stale],
    )
    .unwrap_err();
    assert!(
        error.contains("[TCG-ARG-ABI] closure argument 2")
            && error.contains("original FnAbi ordinal does not describe this argument type"),
        "{error}"
    );
    assert!(block.body.is_empty());
    assert_eq!(ctx.next_value, before);
    assert_eq!(ctx.module, original_module);
    assert_eq!(ctx.fresh_arg_copies, original_copies);
}

fn check_return_and_wide_floors(tcx: TyCtxt<'_>) {
    for (name, diagnostic) in [
        ("pair_return", "[TCG-RET-ABI]"),
        ("buffer_return", "[TCG-SRET-ABI]"),
    ] {
        let (mut ctx, instance) = closure(tcx, name);
        ctx.func_ty_for_instance(instance).unwrap();
        let error = refuse_single_result_call(&ctx, instance).unwrap_err();
        assert!(error.contains(diagnostic), "{name}: {error}");
        let mut block = Block::new(BlockId::new(0));
        let closure_ty = instance.ty(tcx, ty::TypingEnv::fully_monomorphized());
        let before = ctx.next_value;
        let error = emit_closure_call_n(
            &mut ctx,
            &mut block,
            closure_ty,
            ValueId::new(800),
            vec![ValueId::new(801)],
            TrustIrTy::U64,
        )
        .unwrap_err();
        assert!(error.contains(diagnostic), "{name}: {error}");
        assert!(block.body.is_empty());
        assert_eq!(ctx.next_value, before);
    }
    // Genuine once shim: no spoofed InstanceKind or receiver convention.
    let (_, instance) = closure(tcx, "pair32");
    let ty::Closure(definition, args) = *instance
        .ty(tcx, ty::TypingEnv::fully_monomorphized())
        .kind()
    else {
        panic!("actual Fn closure type")
    };
    let shim = Instance::resolve_closure(tcx, definition, args, ty::ClosureKind::FnOnce);
    assert!(!matches!(shim.def, ty::InstanceKind::Item(_)));
    assert!(
        matches!(
            shim.ty(tcx, ty::TypingEnv::fully_monomorphized()).kind(),
            ty::FnDef(..)
        ),
        "this genuine once shim follows the ordinary FnDef contract"
    );
    let source = RustcFnAbiSource::Instance(shim);
    let abi = source.query(tcx).unwrap();
    assert!(matches!(
        abi.args[0].mode,
        rustc_target::callconv::PassMode::Ignore
    ));
    assert!(matches!(
        abi.args[1].mode,
        rustc_target::callconv::PassMode::Pair(..)
    ));
    let mut ctx = MirLoweringCtx::new("actual_once_shim", tcx, shim);
    let input = ctx.normalize_ty(abi.args[1].layout.ty);
    let plan = ctx
        .scalar_pair_param_plan(input, 1, source)
        .unwrap()
        .expect("the actual FnDef shim uses the ordinary checked Pair plan");
    assert_eq!(plan.offsets(), [0, 4]);
    assert_eq!(plan.declared(), [TrustIrTy::I32, TrustIrTy::I32]);
    let signature = ctx.func_ty_for_instance(shim).unwrap();
    assert_eq!(
        ctx.module.func_types[signature.index() as usize].params,
        plan.declared()
    );
    let slot = ValueId::new(801);
    let mut block = Block::new(BlockId::new(0));
    let values =
        closure_body_call_args_from_values(&mut ctx, &mut block, shim, None, vec![slot]).unwrap();
    assert_eq!(values.len(), 2);
    assert_eq!(loads(&block), [TrustIrTy::I32, TrustIrTy::I32]);
    assert_eq!(addresses(&block, slot), [0, 4]);
    let lowered = mir_to_trust_ir(
        tcx,
        shim,
        "actual_once_shim",
        &mut CrateRefineMemo::default(),
    )
    .unwrap_or_else(|error| panic!("actual once shim body: {error}"));
    let function = lowered
        .module
        .functions
        .iter()
        .find(|f| f.name == "actual_once_shim")
        .expect("actual once shim emitted");
    assert_eq!(
        lowered.module.func_types[function.ty.index() as usize].params,
        plan.declared()
    );
    assert_eq!(
        function
            .blocks
            .first()
            .expect("actual rewritten shim entry")
            .params
            .iter()
            .map(|(_, ty)| ty.clone())
            .collect::<Vec<_>>(),
        plan.declared()
    );
    // A Pair at receiver ordinal0 is not this source shim's Pair at ordinal1.
    // Retain a genuine fail-closed control, rather than the obsolete None rule.
    let mut refused = Block::new(BlockId::new(1));
    let before = ctx.next_value;
    let original = ctx.module.clone();
    let copies = ctx.fresh_arg_copies.clone();
    let error = closure_call_arg_values(
        &mut ctx,
        &mut refused,
        source,
        vec![ClosureArg {
            ty: input,
            abi_arg_index: 0,
            src: ClosureArgSrc::Slot(slot),
        }],
    )
    .err()
    .expect("wrong genuine receiver ordinal");
    assert!(
        error.contains("[TCG-ARG-ABI] closure argument 0")
            && error.contains("original FnAbi ordinal does not describe this argument type"),
        "{error}"
    );
    assert!(refused.body.is_empty());
    assert_eq!(ctx.next_value, before);
    assert_eq!(ctx.module, original);
    assert_eq!(ctx.fresh_arg_copies, copies);
}

#[test]
fn actual_closure_pair_declaration_entry_call_and_fail_closed_preflight() {
    const CHILD: &str = "BRIDGE_AARCH64_CLOSURE_PAIR_TEST_CHILD";
    const MARKER: &str = "actual closure Pair declaration-entry-call controls checked";
    if std::env::var_os(CHILD).is_some() {
        extern crate rustc_interface;
        struct Callbacks;
        impl rustc_driver::Callbacks for Callbacks {
            fn config(&mut self, config: &mut rustc_interface::interface::Config) {
                config.input = rustc_session::config::Input::Str {
                    name: rustc_span::FileName::Custom("closure_pair.rs".into()),
                    input: PROBE.into(),
                };
            }
            fn after_analysis<'tcx>(
                &mut self,
                _: &rustc_interface::interface::Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> rustc_driver::Compilation {
                check_pair(tcx, "pair32", false);
                check_pair(tcx, "pair_word", false);
                check_pair(tcx, "ignored_inputs", true);
                check_preflight(tcx);
                check_return_and_wide_floors(tcx);
                common_arguments::check_actual_wide_and_value_environments(tcx);
                eprintln!("{MARKER}");
                rustc_driver::Compilation::Stop
            }
        }
        let sysroot = std::process::Command::new(BUILD_COMPILER)
            .args(["--print", "sysroot"])
            .output()
            .expect("actual compiler sysroot");
        assert!(
            sysroot.status.success(),
            "{}",
            String::from_utf8_lossy(&sysroot.stderr)
        );
        let arguments = vec![
            "trustc".into(),
            "--crate-type=lib".into(),
            "--emit=metadata".into(),
            "-Ztrust-verify=off".into(),
            "--sysroot".into(),
            String::from_utf8(sysroot.stdout).unwrap().trim().into(),
            "-".into(),
        ];
        rustc_driver::run_compiler(&arguments, &mut Callbacks);
        return;
    }
    let output = std::process::Command::new(std::env::current_exe().unwrap()).args([
        "--exact", "closure_body_abi::tests::compiler::actual_closure_pair_declaration_entry_call_and_fail_closed_preflight", "--nocapture",
    ]).env(CHILD, "1").output().expect("isolated actual compiler-context test");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stderr}");
    assert!(
        stderr.contains(MARKER),
        "assertions were not executed: {stderr}"
    );
    assert!(!stderr.contains("panicked"), "{stderr}");
}
