// trust-cg-codegen/tests/compiler_preflight.rs
//
// `Compiler::preflight`: the per-function refusal census of
// `Compiler::compile`. `compile` stops at its first refusal; the census lists
// every function the codegen license, the module-local binding census or the
// adapter refuses, ordered by the function's position in the module, and
// produces no object. It is diagnostic only: `compile` still decides.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{CompileError, Compiler, CompilerConfig};
use trust_cg_lower::AdapterError;
use trust_ir::{
    BinOp, Block, BlockId, BodyGate, Constant, FuncId, FuncTy, Function, Global, Inst, InstrNode,
    Linkage, Module, ParamAttrs, Ty, ValueId, Visibility,
};

/// `fn(i64) -> i64 { return x + 1 }`, named `name`, with `linkage`.
fn add_one(id: u32, name: &str, sig: trust_ir::FuncTyId, linkage: Linkage) -> Function {
    let mut function = Function::new(FuncId::new(id), name, sig, BlockId::new(0));
    function.linkage = linkage;
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    function
}

/// A module with one refusal of every census stage (on an object path that
/// cannot bind module-local functions), in this module order:
///
/// 0. `helper` (Internal, `x + 1`): its identity is materialized in the
///    initializer of the global `helper_slot` (binding census);
/// 1. `caller` (External): a direct call to `helper` (binding census);
/// 2. `ungated`: `body_gate = Ungated` (codegen license);
/// 3. `variadic`: a variadic definition (adapter);
/// 4. `by_value`: a `byval` parameter (adapter);
/// 5. `fine`: nothing to refuse.
fn every_stage_module() -> Module {
    let mut module = Module::new("preflight_every_stage");
    let unary = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let variadic_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: true,
        })
        .expect("Module::add_func_type: test fixture");
    let pointer_sink = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    module
        .try_add_function(add_one(0, "helper", unary, Linkage::Internal))
        .expect("Module::try_add_function: test fixture");

    let mut caller = Function::new(FuncId::new(1), "caller", unary, BlockId::new(0));
    caller.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![ValueId::new(0)],
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module
        .try_add_function(caller)
        .expect("Module::try_add_function: test fixture");

    let mut ungated = add_one(2, "ungated", unary, Linkage::External);
    ungated.body_gate = Some(BodyGate::Ungated);
    module
        .try_add_function(ungated)
        .expect("Module::try_add_function: test fixture");

    module
        .try_add_function(add_one(3, "variadic", variadic_ty, Linkage::External))
        .expect("Module::try_add_function: test fixture");

    let mut by_value = Function::new(FuncId::new(4), "by_value", pointer_sink, BlockId::new(0));
    by_value.attrs.params = vec![ParamAttrs {
        byval: true,
        ..ParamAttrs::default()
    }];
    by_value.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr)],
        body: vec![InstrNode::new(Inst::Return { values: vec![] })],
    }];
    module
        .try_add_function(by_value)
        .expect("Module::try_add_function: test fixture");

    module
        .try_add_function(add_one(5, "fine", unary, Linkage::External))
        .expect("Module::try_add_function: test fixture");

    // `fndef` is a constant of the function's own type (typed admission
    // refuses it at `ptr` for the whole module, which would end the census).
    module.globals.push(Global {
        name: "helper_slot".into(),
        ty: Ty::Func(unary),
        mutable: false,
        initializer: Some(Constant::FnDef(FuncId::new(0))),
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    module
}

/// Only `fine` and `helper`, called from `caller` (both External): a module
/// every stage admits.
fn admitted_module() -> Module {
    let mut module = every_stage_module();
    module
        .functions
        .retain(|function| ["fine", "caller", "helper"].contains(&function.name.as_str()));
    for (position, function) in module.functions.iter_mut().enumerate() {
        function.linkage = Linkage::External;
        // Dense ids again (`caller` still calls `helper`, id 0).
        function.id = FuncId::new(position as u32);
    }
    module.globals.clear();
    module
}

fn compiler(triple: &str) -> Compiler {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O2,
            parallel: false,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).expect("triple"),
    )
    .with_codegen_license(permit_unlicensed())
}

/// A row's function id and a stable class name for its refusal.
fn class(row: &(FuncId, CompileError)) -> (u32, String) {
    let (id, error) = row;
    let class = match error {
        CompileError::Adapter(AdapterError::UngatedBody { function }) => {
            format!("license:ungated:{function}")
        }
        CompileError::Adapter(AdapterError::VariadicDefinitionUnsupported { function }) => {
            format!("adapter:variadic:{function}")
        }
        CompileError::Adapter(AdapterError::ByvalParamUnsupported { function, index }) => {
            format!("adapter:byval:{function}:{index}")
        }
        CompileError::AotDirectModuleFunctionBindingUnsupported { call_count, .. } => {
            format!("binding:direct:{call_count}")
        }
        CompileError::AotStaticFunctionIdentityBindingUnsupported {
            candidate_count, ..
        } => format!("binding:identity:{candidate_count}"),
        other => format!("unexpected:{other:?}"),
    };
    (id.index(), class)
}

/// `compile` stops at its first refusal; `preflight` reports every function
/// each stage refuses, by module position, and produces no object.
#[test]
fn preflight_reports_every_refusal_not_only_the_first() {
    let module = every_stage_module();

    // COFF remains unbound; ELF and Mach-O read back local references.
    // Keep the complete refusal census on an unsupported object format.
    let x86 = compiler("x86_64-pc-windows-msvc");
    assert!(!x86.object_binds_module_local_functions());
    let first = x86
        .compile(&module)
        .expect_err("the module carries six refusals");
    assert!(
        matches!(
            &first,
            CompileError::Adapter(AdapterError::UngatedBody { function }) if function == "ungated"
        ),
        "compile reports its FIRST refusal (the license, decided before anything else): {first:?}"
    );
    let rows: Vec<(u32, String)> = x86.preflight(&module).iter().map(class).collect();
    assert_eq!(
        rows,
        vec![
            (0, "binding:identity:1".to_string()),
            (1, "binding:direct:1".to_string()),
            (2, "license:ungated:ungated".to_string()),
            (3, "adapter:variadic:variadic".to_string()),
            (4, "adapter:byval:by_value:0".to_string()),
        ],
        "x86-64 COFF census"
    );

    // The object paths that bind module-local functions — both AArch64
    // formats and x86-64 ELF/Mach-O — have no binding rows for the same module, and
    // the other rows are unchanged.
    for triple in [
        "aarch64-apple-darwin",
        "aarch64-unknown-linux-gnu",
        "x86_64-unknown-linux-gnu",
        "x86_64-apple-darwin",
    ] {
        let aarch64 = compiler(triple);
        assert!(aarch64.object_binds_module_local_functions(), "{triple}");
        let rows: Vec<(u32, String)> = aarch64.preflight(&module).iter().map(class).collect();
        assert_eq!(
            rows,
            vec![
                (2, "license:ungated:ungated".to_string()),
                (3, "adapter:variadic:variadic".to_string()),
                (4, "adapter:byval:by_value:0".to_string()),
            ],
            "{triple} census"
        );
        // Each refusal is still `compile`'s, one at a time: fixing the
        // license leaves the adapter's first refusal.
        let mut licensed = module.clone();
        licensed.functions[2].body_gate = None;
        assert!(
            matches!(
                aarch64
                    .compile(&licensed)
                    .expect_err("two adapter refusals remain"),
                CompileError::Adapter(AdapterError::VariadicDefinitionUnsupported { .. })
            ),
            "{triple}"
        );
        let rows: Vec<(u32, String)> = aarch64.preflight(&licensed).iter().map(class).collect();
        assert_eq!(
            rows,
            vec![
                (3, "adapter:variadic:variadic".to_string()),
                (4, "adapter:byval:by_value:0".to_string()),
            ],
            "{triple} census after the license fix"
        );
    }

    // A module every stage admits has no row, and `compile` accepts it.
    for triple in [
        "x86_64-unknown-linux-gnu",
        "aarch64-apple-darwin",
        "aarch64-unknown-linux-gnu",
    ] {
        let compiler = compiler(triple);
        let admitted = admitted_module();
        let rows: Vec<(u32, String)> = compiler.preflight(&admitted).iter().map(class).collect();
        assert_eq!(rows, Vec::<(u32, String)>::new(), "{triple}");
        compiler
            .compile(&admitted)
            .unwrap_or_else(|error| panic!("{triple}: the admitted module compiles: {error:?}"));
    }
}

/// The census is per function, not per module: two functions refused by the
/// same stage for the same reason are two rows, and a body the license
/// refuses is not also reported by the adapter.
#[test]
fn preflight_lists_each_refused_function_once_per_stage() {
    let mut module = every_stage_module();
    // `variadic` is also ungated: one license row, no adapter row for it.
    module.functions[3].body_gate = Some(BodyGate::Ungated);
    // A second variadic definition: its own adapter row.
    let variadic_ty = module.functions[3].ty;
    let mut second = add_one(6, "variadic_too", variadic_ty, Linkage::External);
    second.body_gate = None;
    module
        .try_add_function(second)
        .expect("Module::try_add_function: test fixture");
    let rows: Vec<(u32, String)> = compiler("aarch64-apple-darwin")
        .preflight(&module)
        .iter()
        .map(class)
        .collect();
    assert_eq!(
        rows,
        vec![
            (2, "license:ungated:ungated".to_string()),
            (3, "license:ungated:variadic".to_string()),
            (4, "adapter:byval:by_value:0".to_string()),
            (6, "adapter:variadic:variadic_too".to_string()),
        ]
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
