// Copyright 2026 Andrew Yates | Apache-2.0
//! Call edges into a variadic callee that carry no fixed/anonymous split are
//! refused by name, never placed by the named-argument rules.
//!
//! Review findings against the unsigned-variadic refusal (OD-55), each with a
//! reproducer here:
//!
//! * F1: an x86-64 invoke of a signed variadic callee lowered to
//!   `Opcode::Invoke`, which x86 selection lowers as an ordinary call, with
//!   no `mov al, N`. A callee prologue that tests `AL` then skips saving the
//!   vector argument registers and `va_arg(double)` reads garbage. Only base
//!   AAPCS64 places anonymous arguments as named ones, so every other
//!   convention now refuses a variadic invoke.
//! * F6: the Darwin variadic-invoke refusal read the convention from the TLS
//!   dialect alone. `TlsDialect::RejectThreadLocals` (no convention) and an
//!   ELF dialect beside a declared Apple triple both let the invoke through,
//!   while selection takes DarwinPCS from the triple. The invoke is admitted
//!   only when the dialect and the declared triple both name AAPCS64.
//! * F3: a `CallIndirect` through a pointer that visibly names a variadic
//!   declaration (`SymbolAddr("fcntl")`, or a reified `FnDef`) passed every
//!   argument by the edge's non-variadic signature: `FD_CLOEXEC` in `w2`
//!   where DarwinPCS `fcntl` reads it from `[sp]`. It is now refused, with
//!   `[TCG-UNSIGNED-VARIADIC]` when the declaration states no fixed prefix
//!   and `[TCG-VARARG-ABI]` when it does.

use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::{AdapterError, Function as LirFunction, GuardCarrierArch, TlsDialect};
use trust_ir::{
    Block, BlockId, CallingConv, CastOp, Constant, FuncId, FuncTy, Function, Inst, InstrNode,
    Linkage, Module, Ty, ValueId,
};

const VARARG_TAG: &str = "[TCG-VARARG-ABI]";
const UNSIGNED_TAG: &str = "[TCG-UNSIGNED-VARIADIC]";
const CALLER: &str = "caller";

const DARWIN: &str = "aarch64-apple-darwin";
const LINUX: &str = "aarch64-unknown-linux-gnu";
const X86_LINUX: &str = "x86_64-unknown-linux-gnu";
const X86_DARWIN: &str = "x86_64-apple-darwin";

fn target(triple: &str) -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Site {
    Call,
    Invoke,
}

/// `i32 caller(i32 fd) { return callee(fd, 2.5); }` against the bodyless C
/// declaration `callee(<params>[, ...]) -> i32`. The `double` argument is
/// the one whose x86-64 SysV placement `AL` announces.
fn variadic_module(params: Vec<Ty>, is_vararg: bool, site: Site, triple: Option<&str>) -> Module {
    let mut module = Module::new("variadic_edge");
    module.target_info = triple.map(target);
    let callee_ty = module
        .add_func_type(FuncTy {
            params,
            returns: vec![Ty::I32],
            abi: None,
            is_vararg,
        })
        .expect("Module::add_func_type: test fixture");
    let mut callee = Function::new(FuncId::new(0), "vf", callee_ty, BlockId::new(0));
    callee.blocks.clear();
    callee.linkage = Linkage::External;
    callee.calling_conv = CallingConv::C;
    module
        .try_add_function(callee)
        .expect("Module::try_add_function: test fixture");
    let caller_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut caller = Function::new(FuncId::new(1), CALLER, caller_ty, BlockId::new(0));
    let fd = ValueId::new(0);
    let x = ValueId::new(1);
    let result = ValueId::new(3);
    let mut body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::F64,
            value: Constant::Float(2.5),
        })
        .with_result(x),
    ];
    let mut blocks = Vec::new();
    match site {
        Site::Call => {
            body.push(
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(0),
                    args: vec![fd, x],
                })
                .with_result(result),
            );
            body.push(InstrNode::new(Inst::Return {
                values: vec![result],
            }));
        }
        Site::Invoke => {
            body.push(
                InstrNode::new(Inst::Invoke {
                    callee: FuncId::new(0),
                    args: vec![fd, x],
                    normal_dest: BlockId::new(1),
                    normal_args: vec![],
                    unwind_dest: BlockId::new(2),
                })
                .with_result(result),
            );
            let mut normal = Block::new(BlockId::new(1));
            normal.body.push(InstrNode::new(Inst::Return {
                values: vec![result],
            }));
            let mut unwind = Block::new(BlockId::new(2));
            unwind.body.push(
                InstrNode::new(Inst::LandingPad {
                    is_cleanup: true,
                    catch_type_indices: vec![],
                })
                .with_results(vec![ValueId::new(10), ValueId::new(11)]),
            );
            unwind.body.push(InstrNode::new(Inst::Resume {
                exn: ValueId::new(10),
            }));
            blocks.extend([normal, unwind]);
        }
    }
    blocks.insert(
        0,
        Block {
            id: BlockId::new(0),
            params: vec![(fd, Ty::I32)],
            body,
        },
    );
    caller.blocks = blocks;
    module
        .try_add_function(caller)
        .expect("Module::try_add_function: test fixture");
    module
}

fn caller_lir(
    module: &Module,
    arch: GuardCarrierArch,
    dialect: TlsDialect,
) -> Result<LirFunction, AdapterError> {
    Ok(
        trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            module,
            arch,
            dialect,
            &permit_unlicensed(),
        )?
        .into_iter()
        .map(|(function, _)| function)
        .find(|function| function.name == CALLER)
        .expect("caller lowered"),
    )
}

fn call_opcodes(lir: &LirFunction) -> Vec<&Opcode> {
    lir.blocks
        .values()
        .flat_map(|block| &block.instructions)
        .map(|instruction| &instruction.opcode)
        .filter(|opcode| {
            matches!(
                opcode,
                Opcode::Call { .. }
                    | Opcode::CallIndirect
                    | Opcode::CallVariadic { .. }
                    | Opcode::Invoke { .. }
            )
        })
        .collect()
}

fn assert_variadic_invoke_refused(error: &AdapterError, what: &str, detail: &str) {
    let message = error.to_string();
    assert!(
        message.contains(VARARG_TAG) && message.contains("invoke of variadic callee `vf`"),
        "{what}: expected the named variadic-invoke refusal, got {message}"
    );
    assert!(message.contains(detail), "{what}: {message}");
}

/// F1: x86-64 refuses an invoke of a signed variadic callee (its selection
/// would write no `AL`), while the same callee reached by a `Call` keeps
/// lowering to `CallVariadic` with its stated fixed count, and an invoke of
/// a non-variadic callee is unchanged.
#[test]
fn x86_64_refuses_a_variadic_invoke_and_keeps_the_variadic_call() {
    for triple in [X86_LINUX, X86_DARWIN] {
        let dialect = if triple == X86_LINUX {
            TlsDialect::ElfExecutable
        } else {
            TlsDialect::MachOTlv
        };
        let invoke = variadic_module(vec![Ty::I32], true, Site::Invoke, Some(triple));
        let error = caller_lir(&invoke, GuardCarrierArch::X86_64, dialect)
            .expect_err("an x86-64 invoke of a variadic callee must not lower");
        assert_variadic_invoke_refused(&error, triple, "`AL`");

        let call = variadic_module(vec![Ty::I32], true, Site::Call, Some(triple));
        let lir = caller_lir(&call, GuardCarrierArch::X86_64, dialect)
            .unwrap_or_else(|error| panic!("{triple} variadic call: {error}"));
        assert!(
            matches!(
                call_opcodes(&lir).as_slice(),
                [Opcode::CallVariadic { name, fixed_args: 1 }] if name == "vf"
            ),
            "{triple}: {:?}",
            call_opcodes(&lir)
        );

        let plain = variadic_module(vec![Ty::I32, Ty::F64], false, Site::Invoke, Some(triple));
        let lir = caller_lir(&plain, GuardCarrierArch::X86_64, dialect)
            .unwrap_or_else(|error| panic!("{triple} non-variadic invoke: {error}"));
        assert!(
            matches!(
                call_opcodes(&lir).as_slice(),
                [Opcode::Invoke { name, .. }] if name == "vf"
            ),
            "{triple}: {:?}",
            call_opcodes(&lir)
        );
    }
}

/// F6: an AArch64 variadic invoke is admitted only when the TLS dialect and
/// the declared triple both name base AAPCS64 (or no triple is declared).
#[test]
fn aarch64_variadic_invoke_needs_aapcs64_from_dialect_and_declared_triple() {
    let refused = [
        // The pre-existing refusal: DarwinPCS from the dialect.
        (Some(DARWIN), TlsDialect::MachOTlv, "DarwinPCS"),
        (Some(LINUX), TlsDialect::MachOTlv, "DarwinPCS"),
        (None, TlsDialect::MachOTlv, "DarwinPCS"),
        // A dialect that names no convention.
        (
            Some(DARWIN),
            TlsDialect::RejectThreadLocals,
            "names no AArch64",
        ),
        (
            Some(LINUX),
            TlsDialect::RejectThreadLocals,
            "names no AArch64",
        ),
        (None, TlsDialect::RejectThreadLocals, "names no AArch64"),
        // An ELF dialect beside a declared Apple triple.
        (Some(DARWIN), TlsDialect::ElfExecutable, "Apple triple"),
        (Some(DARWIN), TlsDialect::ElfSharedObject, "Apple triple"),
        // A declared triple that selects no AArch64 convention.
        (
            Some("aarch64-pc-windows-msvc"),
            TlsDialect::ElfExecutable,
            "selects no AArch64",
        ),
    ];
    for (triple, dialect, detail) in refused {
        let module = variadic_module(vec![Ty::I32], true, Site::Invoke, triple);
        let what = format!("{triple:?} {dialect:?}");
        let error = caller_lir(&module, GuardCarrierArch::AArch64, dialect)
            .expect_err(&format!("{what}: the variadic invoke must not lower"));
        assert_variadic_invoke_refused(&error, &what, detail);
    }

    for (triple, dialect) in [
        (Some(LINUX), TlsDialect::ElfExecutable),
        (Some(LINUX), TlsDialect::ElfSharedObject),
        (None, TlsDialect::ElfExecutable),
    ] {
        let module = variadic_module(vec![Ty::I32], true, Site::Invoke, triple);
        let lir = caller_lir(&module, GuardCarrierArch::AArch64, dialect)
            .unwrap_or_else(|error| panic!("{triple:?} {dialect:?}: {error}"));
        assert!(
            matches!(
                call_opcodes(&lir).as_slice(),
                [Opcode::Invoke { name, .. }] if name == "vf"
            ),
            "{triple:?} {dialect:?}: {:?}",
            call_opcodes(&lir)
        );
    }
}

/// How the indirect callee pointer is produced.
#[derive(Clone, Copy, Debug)]
enum Pointer {
    /// `Const SymbolAddr { symbol: "fcntl", addend: 0 }` at `Ptr`.
    Symbol,
    /// The symbol address copied and turned into a 64-bit integer.
    SymbolThroughCopyAndPtrToInt,
    /// `Const FnDef(fcntl)` reified to `Ptr`.
    ReifiedFnDef,
}

/// `i32 caller(i32 fd) { return ((i32 (*)(i32, i32, i32)) &fcntl)(fd,
/// F_SETFD, FD_CLOEXEC); }`: a non-variadic C edge through a pointer that
/// names the declaration `fcntl(<params>[, ...]) -> i32`.
fn indirect_module(params: Vec<Ty>, is_vararg: bool, pointer: Pointer, triple: &str) -> Module {
    let mut module = Module::new("variadic_pointer");
    module.target_info = Some(target(triple));
    let declared = module
        .add_func_type(FuncTy {
            params,
            returns: vec![Ty::I32],
            abi: None,
            is_vararg,
        })
        .expect("Module::add_func_type: test fixture");
    let mut fcntl = Function::new(FuncId::new(0), "fcntl", declared, BlockId::new(0));
    fcntl.blocks.clear();
    fcntl.linkage = Linkage::External;
    fcntl.calling_conv = CallingConv::C;
    module
        .try_add_function(fcntl)
        .expect("Module::try_add_function: test fixture");
    let edge = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let caller_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut caller = Function::new(FuncId::new(1), CALLER, caller_ty, BlockId::new(0));
    let fd = ValueId::new(0);
    let cmd = ValueId::new(1);
    let flag = ValueId::new(2);
    let result = ValueId::new(3);
    let mut next = 4u32;
    let mut fresh = || {
        let value = ValueId::new(next);
        next += 1;
        value
    };
    let mut body = Vec::new();
    let symbol = || Constant::SymbolAddr {
        symbol: "fcntl".into(),
        addend: 0,
    };
    let callee = match pointer {
        Pointer::Symbol => {
            let address = fresh();
            body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::Ptr,
                    value: symbol(),
                })
                .with_result(address),
            );
            address
        }
        Pointer::SymbolThroughCopyAndPtrToInt => {
            let address = fresh();
            let copy = fresh();
            let integer = fresh();
            body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::Ptr,
                    value: symbol(),
                })
                .with_result(address),
            );
            body.push(
                InstrNode::new(Inst::Copy {
                    ty: Ty::Ptr,
                    operand: address,
                })
                .with_result(copy),
            );
            body.push(
                InstrNode::new(Inst::Cast {
                    op: CastOp::PtrToInt,
                    src_ty: Ty::Ptr,
                    dst_ty: Ty::I64,
                    operand: copy,
                })
                .with_result(integer),
            );
            integer
        }
        Pointer::ReifiedFnDef => {
            let item = fresh();
            let address = fresh();
            body.push(
                InstrNode::new(Inst::Const {
                    ty: Ty::Func(declared),
                    value: Constant::FnDef(FuncId::new(0)),
                })
                .with_result(item),
            );
            body.push(
                InstrNode::new(Inst::Cast {
                    op: CastOp::ReifyFnPointer,
                    src_ty: Ty::Func(declared),
                    dst_ty: Ty::Ptr,
                    operand: item,
                })
                .with_result(address),
            );
            address
        }
    };
    body.extend([
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(2),
        })
        .with_result(cmd),
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(1),
        })
        .with_result(flag),
        InstrNode::new(Inst::CallIndirect {
            callee,
            sig: edge,
            args: vec![fd, cmd, flag],
            calling_conv: CallingConv::C,
        })
        .with_result(result),
        InstrNode::new(Inst::Return {
            values: vec![result],
        }),
    ]);
    caller.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(fd, Ty::I32)],
        body,
    }];
    module
        .try_add_function(caller)
        .expect("Module::try_add_function: test fixture");
    module
}

/// The indirect-call entries: AArch64 Darwin and Linux, x86-64, and the
/// validating entry.
fn indirect_entries(
    params: &[Ty],
    is_vararg: bool,
    pointer: Pointer,
) -> Vec<(String, Result<Vec<LirFunction>, AdapterError>)> {
    let mut entries = Vec::new();
    for (triple, arch, dialect) in [
        (DARWIN, GuardCarrierArch::AArch64, TlsDialect::MachOTlv),
        (LINUX, GuardCarrierArch::AArch64, TlsDialect::ElfExecutable),
        (
            X86_LINUX,
            GuardCarrierArch::X86_64,
            TlsDialect::ElfExecutable,
        ),
    ] {
        let module = indirect_module(params.to_vec(), is_vararg, pointer, triple);
        entries.push((
            format!("{triple} {pointer:?}"),
            lowered(
                trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                    &module,
                    arch,
                    dialect,
                    &permit_unlicensed(),
                ),
            ),
        ));
    }
    let module = indirect_module(params.to_vec(), is_vararg, pointer, DARWIN);
    entries.push((
        format!("validating {pointer:?}"),
        lowered(
            trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
                &module,
                GuardCarrierArch::AArch64,
                TlsDialect::MachOTlv,
                &permit_unlicensed(),
            )
            .map(|(functions, _report)| functions),
        ),
    ));
    entries
}

fn lowered<T>(
    result: Result<Vec<(LirFunction, T)>, AdapterError>,
) -> Result<Vec<LirFunction>, AdapterError> {
    result.map(|functions| {
        functions
            .into_iter()
            .map(|(function, _)| function)
            .collect()
    })
}

const POINTERS: [Pointer; 3] = [
    Pointer::Symbol,
    Pointer::SymbolThroughCopyAndPtrToInt,
    Pointer::ReifiedFnDef,
];

/// F3: a function pointer to the unsigned `(...)` declaration is refused by
/// the same name as a direct call through it.
#[test]
fn indirect_call_to_an_unsigned_variadic_declaration_is_refused_by_name() {
    for pointer in POINTERS {
        for (entry, result) in indirect_entries(&[], true, pointer) {
            let error = result.expect_err(&format!("{entry}: must not lower"));
            assert!(
                matches!(
                    &error,
                    AdapterError::UnsignedVariadicCallee { callee, .. } if callee == "fcntl"
                ),
                "{entry}: expected the unsigned-variadic refusal, got {error:?}"
            );
            assert!(error.to_string().contains(UNSIGNED_TAG), "{entry}: {error}");
        }
    }
}

/// F3: a non-variadic edge through a pointer to a SIGNED variadic
/// declaration places the anonymous argument as a named one, and is refused.
#[test]
fn indirect_call_to_a_signed_variadic_declaration_is_refused() {
    for pointer in POINTERS {
        for (entry, result) in indirect_entries(&[Ty::I32, Ty::I32], true, pointer) {
            let error = result.expect_err(&format!("{entry}: must not lower"));
            let message = error.to_string();
            assert!(
                message.contains(VARARG_TAG)
                    && message.contains("CallIndirect through a function pointer to variadic")
                    && message.contains("`fcntl` (2 fixed parameter(s))"),
                "{entry}: {message}"
            );
        }
    }
}

/// Control: the same pointers to a non-variadic declaration still lower to
/// a `CallIndirect` on every entry.
#[test]
fn indirect_call_to_a_non_variadic_declaration_still_lowers() {
    for pointer in POINTERS {
        for (entry, result) in indirect_entries(&[Ty::I32, Ty::I32, Ty::I32], false, pointer) {
            let functions = result.unwrap_or_else(|error| panic!("{entry}: {error}"));
            let caller = functions
                .iter()
                .find(|function| function.name == CALLER)
                .expect("caller lowered");
            assert!(
                matches!(call_opcodes(caller).as_slice(), [Opcode::CallIndirect]),
                "{entry}: {:?}",
                call_opcodes(caller)
            );
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
