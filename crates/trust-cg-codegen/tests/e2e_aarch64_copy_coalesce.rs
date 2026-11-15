// trust-cg-codegen/tests/e2e_aarch64_copy_coalesce.rs
//
// Codegen-quality gate for the LinearScan copy-coalescing register hints
// (crates/trust-cg-regalloc: copy_register_hints + LinearScan hint honoring with
// the copy-point reserved-interference exemption). These bias a vreg that is
// copy-related to a fixed ABI register (formal-arg / return / call-result copies)
// onto that register, so the copy becomes an identity move `post_ra_coalesce`
// deletes — closing the redundant arg/return `mov` gap vs LLVM.
//
// Before the hints, `fn() -> i64 { 42 }` emitted `mov x1,#42 ; mov x0,x1 ; ret`
// (3 insns) and `a*b+c` emitted `mov x4,x1 ; madd x1,.. ; mov x0,x1 ; ret`
// (4 insns). The return-value copy is now eliminated (the value is produced
// directly in x0), matching clang. This test pins the exact emitted code words
// and the instruction-count metric so a coalescing regression fails closed.
//
// Every module is compiled for BOTH explicit AArch64 targets on every host
// (object emission only; nothing is linked or run), and the code section is
// read by the container parser in `common/native_host.rs`, not by the
// compiler's own emitter. The coalesced BODY is the same on both targets; they
// differ only in the leaf frame record around it:
//
// - `aarch64-apple-darwin` (Mach-O) admits a red zone, so these trivial leaves
//   get no frame record: the code is the body followed by `ret`.
// - `aarch64-unknown-linux-gnu` (ELF) has no red zone (18e1ab693). The
//   zero-storage leaf policy (e26492c26, `frame/zero_storage.rs`) omits the
//   empty frame only for audited leaves. It deliberately keeps the exact
//   sixteen-byte FP/LR envelope for ADD/SUB/immediate-LSL bodies (ad795539f)
//   and for returning leaves made only of constants, copies, compares and
//   branches (b488c3cc1): that envelope is the source-bound frame owner through
//   which the verifier binds the complete body to Formal evidence, and dropping
//   it would turn supported proof exports into sampling (ARCHITECTURE.md,
//   AArch64 zero-storage leaf policy; LIMITATIONS.md, source-bound leaf
//   frames). Such a body is emitted as `stp x29,x30,[sp,#-16]! ; mov x29,sp ;
//   <body> ; ldp x29,x30,[sp],#16 ; ret`, three words longer than GCC 13.3's
//   frameless -O2 leaf on Linux AArch64. Only a source the owner can judge
//   keeps the envelope. MADD is an audited zero-storage operation and
//   `addmul`'s body has no ADD/SUB beside it, so addmul is frameless on both
//   targets.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#[path = "common/native_host.rs"]
mod native_host;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{Target, TargetSpec};

use trust_ir::{
    BinOp, Block as TrustIrBlock, Constant, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

const DARWIN_TRIPLE: &str = "aarch64-apple-darwin";
const LINUX_TRIPLE: &str = "aarch64-unknown-linux-gnu";

// The exact sixteen-byte FP/LR envelope and return (decoded with LLVM objdump).
const STP_FP_LR_PRE16: u32 = 0xa9bf_7bfd; // stp x29, x30, [sp, #-16]!
const MOV_FP_SP: u32 = 0x9100_03fd; // mov x29, sp
const LDP_FP_LR_POST16: u32 = 0xa8c1_7bfd; // ldp x29, x30, [sp], #16
const RET: u32 = 0xd65f_03c0; // ret

/// The leaf frame the Linux ELF target emits around a coalesced body.
#[derive(Clone, Copy, Debug)]
enum LinuxLeafFrame {
    /// Audited zero-storage leaf: no frame record, as on Darwin (e26492c26).
    Omitted,
    /// The body's source-bound frame owner keeps the exact FP/LR envelope
    /// (ad795539f for ADD/SUB/LSL, b488c3cc1 for constant/copy returns).
    SourceBoundEnvelope,
}

/// Compile `module` at O2 for `triple` and return the instruction-count metric
/// and the words of the object's code section.
fn emit(module: &TrustIrModule, triple: &str) -> (usize, Vec<u32>) {
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O2,
            target: Target::Aarch64,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).expect("supported AArch64 triple"),
    )
    .with_codegen_license(permit_unlicensed());
    let result = compiler.compile(module).expect("must compile");
    if triple == LINUX_TRIPLE {
        native_host::assert_elf_aarch64_object(&result.object_code);
    } else {
        native_host::assert_macho_arm64_object(&result.object_code);
    }
    (
        result.metrics.instruction_count,
        native_host::text_words(&result.object_code),
    )
}

/// Assert the exact code of `module` on both targets: `body ; ret` on Darwin,
/// and on Linux either the same or `body` inside the FP/LR envelope.
fn assert_exact_code(module: &TrustIrModule, body: &[u32], linux: LinuxLeafFrame, what: &str) {
    let frameless: Vec<u32> = body.iter().copied().chain([RET]).collect();
    let enveloped: Vec<u32> = [STP_FP_LR_PRE16, MOV_FP_SP]
        .into_iter()
        .chain(body.iter().copied())
        .chain([LDP_FP_LR_POST16, RET])
        .collect();
    let linux_expected = match linux {
        LinuxLeafFrame::Omitted => &frameless,
        LinuxLeafFrame::SourceBoundEnvelope => &enveloped,
    };
    for (triple, expected) in [(DARWIN_TRIPLE, &frameless), (LINUX_TRIPLE, linux_expected)] {
        let (instruction_count, words) = emit(module, triple);
        assert_eq!(
            &words, expected,
            "{what} on {triple} ({linux:?} on Linux): emitted {words:08x?}, expected {expected:08x?}"
        );
        assert_eq!(
            instruction_count,
            expected.len(),
            "{what} on {triple}: instruction_count metric"
        );
    }
}

/// `fn c() -> i64 { 42 }`
fn const_return_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("const_ret");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(0), "c42", ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(42),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ],
    }];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

/// `fn f(a,b,c) -> i64 { a*b + c }`
fn addmul_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("addmul");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(0), "addmul", ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::I64),
            (ValueId::new(1), Ty::I64),
            (ValueId::new(2), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(3),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(4)],
            }),
        ],
    }];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

/// `fn f(a,b) -> i64 { a - b }`
fn sub2_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("sub2");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(0), "sub2", ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Sub,
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
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

/// `fn f(a,b,c) -> i64 { a + b + c }`
fn sum3_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("sum3");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(0), "sum3", ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::I64),
            (ValueId::new(1), Ty::I64),
            (ValueId::new(2), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(3),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(4)],
            }),
        ],
    }];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

#[test]
fn sub2_coalesces_arg_and_return() {
    // `sub x0, x0, x1` — both the arg-a copy and the return copy are gone (a
    // stays in x0, the sub writes x0). Matches clang. (Was led by `mov x_,x0`.)
    // Enabled by precise incoming-argument liveness (isel append_formal_livein_uses).
    // Linux keeps the SUB body's source-bound FP/LR envelope (ad795539f).
    assert_exact_code(
        &sub2_module(),
        &[0xcb01_0000], // sub x0, x0, x1
        LinuxLeafFrame::SourceBoundEnvelope,
        "sub2",
    );
}

#[test]
fn sum3_coalesces_arg_copy() {
    // `add x3, x0, x1 ; add x0, x3, x2` — the arg-a copy is gone (a stays in x0
    // for the first add). Matches clang. (Was led by `mov x_,x0`.)
    // Linux keeps the ADD body's source-bound FP/LR envelope (ad795539f).
    assert_exact_code(
        &sum3_module(),
        &[
            0x8b01_0003, // add x3, x0, x1
            0x8b02_0060, // add x0, x3, x2
        ],
        LinuxLeafFrame::SourceBoundEnvelope,
        "sum3",
    );
}

#[test]
fn const_return_has_no_redundant_move() {
    // `mov x0, #42` — the return-value copy is coalesced away.
    // (Was `mov x1, #42 ; mov x0, x1`.)
    // Linux keeps the constant return's source-bound FP/LR envelope (b488c3cc1).
    assert_exact_code(
        &const_return_module(),
        &[0xd280_0540], // mov x0, #42
        LinuxLeafFrame::SourceBoundEnvelope,
        "const-return",
    );
}

#[test]
fn addmul_coalesces_return_copy() {
    // `madd x0, x0, x1, x2` — BOTH the arg-a copy and the return copy are gone;
    // the madd reads a in x0 and writes the result to x0. Matches clang's
    // optimal 2-instruction lowering. (Was 4 with a leading `mov x_,x0` and a
    // trailing `mov x0,x1`; then 3 once the return copy coalesced; now 2 once
    // `Madd`/`Msub` were added to the backward-def coalescer's retargetable set,
    // letting the madd write x0 directly — the arg copy is no longer needed.)
    // MADD is an audited zero-storage operation, so Linux omits the frame too.
    assert_exact_code(
        &addmul_module(),
        &[0x9b01_0800], // madd x0, x0, x1, x2
        LinuxLeafFrame::Omitted,
        "addmul",
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
