// Copyright 2026 Andrew Yates | Apache-2.0
//! A call through a variadic declaration that states no fixed-argument count
//! is refused by name (`[TCG-UNSIGNED-VARIADIC]`), never lowered as
//! `CallVariadic { fixed_args: 0 }`.
//!
//! The defect (Trust run-make `trust-cg-f1-c-callee-abi`, measured
//! 2026-10-02): the Trust producer publishes a C callee it cannot sign, the
//! variadic `fcntl` or the non-variadic `posix_spawn_file_actions_adddup2`, as
//! `(...) -> (i32)`. Lowered with zero fixed arguments, DarwinPCS passes every
//! argument on the stack, so `fcntl(fd, F_SETFD, FD_CLOEXEC)` read whatever
//! `w0`/`w1` held and ran as a silent `F_DUPFD`.
//!
//! The checks here, independent of the production ABI classifier:
//! * (a) every adapter entry, on every target, refuses the unsigned shapes by
//!   name, for a call and for an invoke;
//! * (b) a variadic declaration that states its fixed prefix lowers to
//!   `CallVariadic { fixed_args: N }`, and instruction selection puts the N
//!   fixed arguments in `w0..` (Darwin and AAPCS64) and the anonymous one on
//!   the stack (Darwin) or in the next register (AAPCS64); a control shows
//!   the same check catches the zero-fixed-argument placement;
//! * (c) a signed non-variadic C callee is untouched: an ordinary `Call` with
//!   every argument in a register.

use trust_cg_ir::{AArch64Opcode, regs::SP};
use trust_cg_lower::abi::{AArch64AbiVariant, PReg, gpr};
use trust_cg_lower::instructions::{Block as LirBlock, DirectCallBinding, Opcode};
use trust_cg_lower::isel::{ISelFunction, ISelOperand, InstructionSelector};
use trust_cg_lower::{AdapterError, Function as LirFunction, GuardCarrierArch, TlsDialect};
use trust_ir::{
    Block, BlockId, CallingConv, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Linkage,
    Module, Ty, ValueId,
};

const TAG: &str = "[TCG-UNSIGNED-VARIADIC]";
const CALLER: &str = "set_cloexec";
/// `F_SETFD` and `FD_CLOEXEC` on Darwin: distinct from each other and from 0
/// (`F_DUPFD`), so a misplaced argument is visible.
const F_SETFD: i128 = 2;
const FD_CLOEXEC: i128 = 1;

fn aarch64_target(dialect: TlsDialect) -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: match dialect {
            TlsDialect::MachOTlv => "aarch64-apple-darwin",
            _ => "aarch64-unknown-linux-gnu",
        }
        .into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}

fn x86_64_target() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}

/// How the caller reaches the callee.
#[derive(Clone, Copy, Debug)]
enum Site {
    Call,
    Invoke,
}

/// The callee declaration's signature.
struct Decl {
    name: &'static str,
    params: Vec<Ty>,
    is_vararg: bool,
    conv: CallingConv,
}

/// `i32 set_cloexec(i32 fd) { return callee(fd, F_SETFD, FD_CLOEXEC); }`
/// against the bodyless external declaration `decl`.
fn module(decl: &Decl, site: Site) -> Module {
    let mut module = Module::new("unsigned_variadic_callee");
    module.target_info = Some(aarch64_target(TlsDialect::MachOTlv));
    let callee_ty = module
        .add_func_type(FuncTy {
            params: decl.params.clone(),
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: decl.is_vararg,
        })
        .expect("Module::add_func_type: test fixture");
    let mut callee = Function::new(FuncId::new(0), decl.name, callee_ty, BlockId::new(0));
    callee.blocks.clear();
    callee.linkage = Linkage::External;
    callee.calling_conv = decl.conv;
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
    let cmd = ValueId::new(1);
    let flag = ValueId::new(2);
    let result = ValueId::new(3);
    let mut body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(F_SETFD),
        })
        .with_result(cmd),
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(FD_CLOEXEC),
        })
        .with_result(flag),
    ];
    let args = vec![fd, cmd, flag];
    let mut blocks = Vec::new();
    match site {
        Site::Call => {
            body.push(
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(0),
                    args,
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
                    args,
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

/// Every adapter entry a driver reaches, by name: the compatibility module
/// and function entries, each target (AArch64 Darwin and Linux, x86-64), the
/// validating entry, and the strict identity-only entry.
fn every_entry(module: &Module) -> Vec<(&'static str, Result<(), AdapterError>)> {
    let caller = &module.functions[1];
    let mut darwin = module.clone();
    darwin.target_info = Some(aarch64_target(TlsDialect::MachOTlv));
    let mut linux = module.clone();
    linux.target_info = Some(aarch64_target(TlsDialect::ElfExecutable));
    let mut x86 = module.clone();
    x86.target_info = Some(x86_64_target());
    vec![
        (
            "translate_module",
            trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                module,
                trust_cg_lower::GuardCarrierArch::default(),
                trust_cg_lower::TlsDialect::default(),
                &permit_unlicensed(),
            )
            .map(drop),
        ),
        (
            "translate_function",
            trust_cg_lower::translate_function_with_license(caller, module, &permit_unlicensed())
                .map(drop),
        ),
        (
            "aarch64 darwin",
            trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                &darwin,
                GuardCarrierArch::AArch64,
                TlsDialect::MachOTlv,
                &permit_unlicensed(),
            )
            .map(drop),
        ),
        (
            "aarch64 linux",
            trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                &linux,
                GuardCarrierArch::AArch64,
                TlsDialect::ElfExecutable,
                &permit_unlicensed(),
            )
            .map(drop),
        ),
        (
            "x86-64 linux",
            trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                &x86,
                GuardCarrierArch::X86_64,
                TlsDialect::ElfExecutable,
                &permit_unlicensed(),
            )
            .map(drop),
        ),
        (
            "validating (retained declaration ids)",
            trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
                &darwin,
                GuardCarrierArch::AArch64,
                TlsDialect::MachOTlv,
                &permit_unlicensed(),
            )
            .map(drop),
        ),
        (
            "strict identity-only",
            trust_cg_lower::translate_module_strict_for_arch_with_tls_and_validation_with_license(
                &darwin,
                GuardCarrierArch::AArch64,
                TlsDialect::MachOTlv,
                &permit_unlicensed(),
            )
            .map(drop),
        ),
    ]
}

/// (a) The unsigned shapes are refused by name on every entry, for a call and
/// for an invoke. The refusal is a lowering error, so it precedes any output
/// gate: no gate policy (strict or allow-unknown) gets a placement to grade.
#[test]
fn unsigned_variadic_declaration_is_refused_by_name_on_every_entry() {
    let shapes = [
        // The producer's `(...)` for a variadic C callee it cannot sign.
        ("fcntl", vec![], CallingConv::C),
        // ... and for a non-variadic one (`*mut *mut c_void` parameter).
        ("posix_spawn_file_actions_adddup2", vec![], CallingConv::C),
        // The same spelling under the Rust convention (the THIR placeholder).
        ("upstream_fn", vec![], CallingConv::Rust),
        // A Rust-convention variadic with a fixed prefix: the Rust ABI has no
        // variadic form, so the prefix is no statement either.
        ("upstream_prefixed", vec![Ty::I32], CallingConv::Rust),
    ];
    for (name, params, conv) in shapes {
        let decl = Decl {
            name,
            params,
            is_vararg: true,
            conv,
        };
        for site in [Site::Call, Site::Invoke] {
            let module = module(&decl, site);
            for (entry, result) in every_entry(&module) {
                let error = result.expect_err(&format!(
                    "{name} {site:?} via {entry}: an unsigned variadic callee must not lower"
                ));
                assert!(
                    matches!(
                        &error,
                        AdapterError::UnsignedVariadicCallee { callee, .. } if callee == name
                    ),
                    "{name} {site:?} via {entry}: expected the named refusal, got {error:?}"
                );
                assert!(
                    error.to_string().contains(TAG),
                    "{name} {site:?} via {entry}: {error}"
                );
            }
        }
    }
}

/// The shared predicate, by shape: only a variadic signature without a
/// trustworthy fixed prefix is refused.
#[test]
fn shared_predicate_refuses_only_unsigned_shapes() {
    let refused = |conv: CallingConv, params: Vec<Ty>, is_vararg: bool| {
        let mut declaration = Function::new(
            FuncId::new(0),
            "callee",
            trust_ir::FuncTyId::new(0),
            BlockId::new(0),
        );
        declaration.blocks.clear();
        declaration.calling_conv = conv;
        let signature = FuncTy {
            params,
            returns: vec![Ty::I32],
            abi: None,
            is_vararg,
        };
        trust_cg_lower::reject_unsigned_variadic_callee(&declaration, &signature).is_err()
    };
    assert!(refused(CallingConv::C, vec![], true));
    assert!(refused(CallingConv::Rust, vec![], true));
    assert!(refused(CallingConv::Rust, vec![Ty::I32], true));
    assert!(!refused(CallingConv::C, vec![Ty::I32, Ty::I32], true));
    assert!(!refused(CallingConv::C, vec![], false));
    assert!(!refused(CallingConv::Rust, vec![], false));
    assert!(!refused(
        CallingConv::C,
        vec![Ty::I32, Ty::I32, Ty::I32],
        false
    ));
}

/// Translate for AArch64 under `dialect` and return the caller's LIR.
fn caller_lir(module: &Module, dialect: TlsDialect) -> LirFunction {
    let mut module = module.clone();
    module.target_info = Some(aarch64_target(dialect));
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        GuardCarrierArch::AArch64,
        dialect,
        &permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{dialect:?}: {error}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == CALLER)
    .expect("caller lowered")
}

/// The caller's single call opcode.
fn call_opcode(lir: &LirFunction) -> &Opcode {
    let mut calls = lir
        .blocks
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
        });
    let call = calls.next().expect("one call");
    assert!(calls.next().is_none(), "exactly one call");
    call
}

/// Run instruction selection over a whole LIR function, as the pipeline does.
fn select(lir: &LirFunction, variant: AArch64AbiVariant) -> ISelFunction {
    let mut isel = InstructionSelector::new(lir.name.clone(), lir.signature.clone());
    isel.set_abi_variant(variant);
    isel.seed_value_types(&lir.value_types);
    isel.lower_formal_arguments(&lir.signature, lir.entry_block)
        .expect("formal arguments");
    let mut order: Vec<LirBlock> = lir.blocks.keys().copied().collect();
    order.sort_by_key(|block| {
        if *block == lir.entry_block {
            0
        } else {
            block.0 + 1
        }
    });
    for block in order {
        let bb = &lir.blocks[&block];
        isel.select_block_with_source_locs(block, &bb.instructions, &bb.source_locs)
            .expect("instruction selection");
    }
    isel.finalize()
}

/// Where an argument went.
#[derive(Clone, Debug, PartialEq)]
enum Destination {
    Register(PReg),
    Stack(i64),
}

/// What an argument value is, traced back through its selected definition.
#[derive(Clone, Debug, PartialEq)]
enum Source {
    /// The caller's incoming first argument (`fd`, copied out of `x0`).
    IncomingFd,
    /// A materialized constant.
    Constant(i64),
}

/// The argument marshalling of the single `bl callee`, as
/// `(destination, source)` pairs in instruction order, each source traced to
/// its definition in the selected function, and the registers the `bl`
/// declares it reads.
///
/// Like `tests/aarch64_variadic_abi.rs`, this reads the selected instructions
/// themselves and never asks the production ABI classifier: a `Copy` into a
/// physical register or a `StrRI` to `[sp, #imm]` before the call is an
/// argument placement, and anything there other than those and the traced
/// definitions is refused.
fn marshalling(isel: &ISelFunction, callee: &str) -> (Vec<(Destination, Source)>, Vec<PReg>) {
    let insts: Vec<_> = isel
        .block_order
        .iter()
        .flat_map(|block| &isel.blocks[block].insts)
        .collect();
    let trace = |vreg: u32| -> Source {
        let mut current = vreg;
        for _ in 0..16 {
            let def = insts
                .iter()
                .find(|inst| {
                    matches!(
                        inst.operands.first(),
                        Some(ISelOperand::VReg(dst)) if dst.id == current
                    )
                })
                .unwrap_or_else(|| panic!("no definition of v{current}"));
            match (def.opcode, &def.operands[1..]) {
                (AArch64Opcode::Copy, [ISelOperand::PReg(src)]) if *src == gpr::X0 => {
                    return Source::IncomingFd;
                }
                (AArch64Opcode::Copy, [ISelOperand::VReg(src)]) => current = src.id,
                (AArch64Opcode::Movz | AArch64Opcode::MovI, [ISelOperand::Imm(value), ..]) => {
                    return Source::Constant(*value);
                }
                (opcode, operands) => panic!("v{current} is defined by {opcode:?} {operands:?}"),
            }
        }
        panic!("copy chain of v{vreg} is too long")
    };
    let bls: Vec<usize> = insts
        .iter()
        .enumerate()
        .filter(|(_, inst)| inst.opcode == AArch64Opcode::Bl)
        .map(|(index, _)| index)
        .collect();
    let [call] = bls.as_slice() else {
        panic!("expected exactly one `bl`, found {}", bls.len());
    };
    assert!(
        matches!(
            insts[*call].operands.as_slice(),
            [ISelOperand::Symbol(name)] if name == callee
        ),
        "the call is `bl {callee}`: {:?}",
        insts[*call]
    );
    let placements = insts[..*call]
        .iter()
        .filter_map(|inst| match (inst.opcode, inst.operands.as_slice()) {
            (AArch64Opcode::Copy, [ISelOperand::PReg(dst), ISelOperand::VReg(src)]) => {
                Some((Destination::Register(*dst), trace(src.id)))
            }
            (
                AArch64Opcode::StrRI,
                [
                    ISelOperand::VReg(src),
                    ISelOperand::PReg(base),
                    ISelOperand::Imm(offset),
                ],
            ) if *base == SP => Some((Destination::Stack(*offset), trace(src.id))),
            // The incoming-argument copy and the constants are the traced
            // definitions; nothing else may precede the call.
            (AArch64Opcode::Copy, [ISelOperand::VReg(_), ISelOperand::PReg(_)])
            | (AArch64Opcode::Movz | AArch64Opcode::MovI, _) => None,
            (opcode, operands) => {
                panic!("unexpected instruction before the call: {opcode:?} {operands:?}")
            }
        })
        .collect();
    (placements, insts[*call].implicit_uses.clone())
}

fn reg(preg: PReg) -> Destination {
    Destination::Register(preg)
}

/// (b) A variadic declaration that states its fixed prefix
/// (`int fcntl(int, int, ...)`) keeps lowering, with exactly that many fixed
/// arguments, and the fixed arguments land in registers.
#[test]
fn signed_variadic_lowers_with_its_fixed_count_and_places_fixed_args_in_registers() {
    let decl = Decl {
        name: "fcntl",
        params: vec![Ty::I32, Ty::I32],
        is_vararg: true,
        conv: CallingConv::C,
    };
    let module = module(&decl, Site::Call);
    let fd = Source::IncomingFd;
    let cmd = Source::Constant(F_SETFD as i64);
    let flag = Source::Constant(FD_CLOEXEC as i64);
    for (dialect, variant, expected, uses) in [
        (
            TlsDialect::MachOTlv,
            AArch64AbiVariant::Darwin,
            // DarwinPCS: fixed in w0/w1, the anonymous `FD_CLOEXEC` at [sp].
            vec![
                (reg(gpr::W0), fd.clone()),
                (reg(gpr::W1), cmd.clone()),
                (Destination::Stack(0), flag.clone()),
            ],
            vec![gpr::X0, gpr::X1],
        ),
        (
            TlsDialect::ElfExecutable,
            AArch64AbiVariant::Aapcs64,
            // Base AAPCS64: anonymous arguments use the next free register.
            vec![
                (reg(gpr::W0), fd.clone()),
                (reg(gpr::W1), cmd.clone()),
                (reg(gpr::W2), flag.clone()),
            ],
            vec![gpr::X0, gpr::X1, gpr::X2],
        ),
    ] {
        let lir = caller_lir(&module, dialect);
        assert!(
            matches!(
                call_opcode(&lir),
                Opcode::CallVariadic { name, fixed_args: 2 } if name == "fcntl"
            ),
            "{dialect:?}: {:?}",
            call_opcode(&lir)
        );
        let (placements, implicit_uses) = marshalling(&select(&lir, variant), "fcntl");
        assert_eq!(placements, expected, "{variant:?} placement");
        assert_eq!(implicit_uses, uses, "{variant:?} call register uses");

        // Teeth: the zero-fixed-argument lowering the unsigned `(...)` used to
        // get. Under DarwinPCS it moves `fd` and `F_SETFD` out of w0/w1 onto
        // the stack, and the same check sees it.
        if variant == AArch64AbiVariant::Darwin {
            let mut zero_fixed = lir.clone();
            for block in zero_fixed.blocks.values_mut() {
                for instruction in &mut block.instructions {
                    if let Opcode::CallVariadic { fixed_args, .. } = &mut instruction.opcode {
                        *fixed_args = 0;
                    }
                }
            }
            let (placements, implicit_uses) = marshalling(&select(&zero_fixed, variant), "fcntl");
            assert_eq!(
                placements,
                vec![
                    (Destination::Stack(0), fd.clone()),
                    (Destination::Stack(8), cmd.clone()),
                    (Destination::Stack(16), flag.clone()),
                ],
                "control: zero fixed arguments put every argument on the Darwin stack"
            );
            assert!(implicit_uses.is_empty(), "{implicit_uses:?}");
        }
    }

    // No entry gives it the unsigned refusal. Entries that retain declared
    // import identities keep their existing refusal of any CallVariadic.
    for (entry, result) in every_entry(&module) {
        if let Err(error) = result {
            assert!(
                !matches!(error, AdapterError::UnsignedVariadicCallee { .. }),
                "{entry}: a signed variadic must not get the unsigned refusal: {error}"
            );
            assert!(
                error
                    .to_string()
                    .contains("cannot retain imported FuncId through CallVariadic"),
                "{entry}: unexpected refusal of a signed variadic call: {error}"
            );
        }
    }
}

/// (c) A signed non-variadic C callee is unchanged: an ordinary interposable
/// `Call`, every argument in a register, on every entry.
#[test]
fn signed_non_variadic_c_callee_is_unchanged() {
    let decl = Decl {
        name: "signed_c_callee",
        params: vec![Ty::I32, Ty::I32, Ty::I32],
        is_vararg: false,
        conv: CallingConv::C,
    };
    for site in [Site::Call, Site::Invoke] {
        for (entry, result) in every_entry(&module(&decl, site)) {
            result.unwrap_or_else(|error| panic!("{site:?} via {entry}: {error}"));
        }
    }
    let module = module(&decl, Site::Call);
    for (dialect, variant) in [
        (TlsDialect::MachOTlv, AArch64AbiVariant::Darwin),
        (TlsDialect::ElfExecutable, AArch64AbiVariant::Aapcs64),
    ] {
        let lir = caller_lir(&module, dialect);
        assert!(
            matches!(
                call_opcode(&lir),
                Opcode::Call { name, binding: DirectCallBinding::Interposable }
                    if name == "signed_c_callee"
            ),
            "{dialect:?}: {:?}",
            call_opcode(&lir)
        );
        let (placements, implicit_uses) = marshalling(&select(&lir, variant), "signed_c_callee");
        assert_eq!(
            placements,
            vec![
                (reg(gpr::W0), Source::IncomingFd),
                (reg(gpr::W1), Source::Constant(F_SETFD as i64)),
                (reg(gpr::W2), Source::Constant(FD_CLOEXEC as i64)),
            ],
            "{variant:?}"
        );
        assert_eq!(
            implicit_uses,
            vec![gpr::X0, gpr::X1, gpr::X2],
            "{variant:?}"
        );
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
