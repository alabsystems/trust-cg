// E2E: the Darwin AArch64 mixed-codegen exception/RAII/destructor-count
// campaign (ledger X-DARWIN-P7): C++ throwers and catchers, and Rust panics,
// crossing trust-cg frames, against C++-only and Rust-only reference builds of
// the same case matrix.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ----------------------------------------------------------------------------
// WHAT THIS PINS
// ----------------------------------------------------------------------------
// Two trust-ir modules build chain functions from `Inst::Invoke` /
// `Inst::LandingPad` / `Inst::Resume`. Every chain has a compact-unwind twin
// (`NAME`) and a runtime-sized twin (`NAME_dyn`, with an
// `Alloca { count: Some(n) }`). trust-cg's compact-unwind encoder
// (`frame.rs` `encode_compact_unwind`) sends every frame with a dynamic
// alloca to the DWARF fallback, so the `_dyn` twins are the campaign's
// DWARF-fallback frames. That is trust-cg's conservative policy, not an Apple
// limit: Apple clang gives such a frame a FRAME-mode compact encoding. The
// nested chains call their own family's inner chain, so a `_dyn` case crosses
// only DWARF-fallback CG frames.
//
// * C++ module (`__gxx_personality_v0`, type table `[CaseError, int]`),
//   fifteen chains over a C++ thrower (fixtures/eh_raii_darwin): CG cleanup
//   pads that run a C++ destructor (`TcgGuard`, a RAII object living in the CG
//   frame's own slot, whose destructor checks its address), catch-all pads,
//   typed pads (`CaseError&` including a derived class, `int`, both, typed
//   then catch-all, a guard destroyed before a typed handler), two guards and
//   two invokes in one frame, CG -> CG -> CG nesting, a plain CG frame with no
//   pad, a CG rethrow (`__cxa_rethrow` invoked from a handler whose cleanup pad
//   ends the catch), a C++ frame that catches and rethrows between two CG
//   frames, a destructor-free cleanup that throws and catches a second
//   exception while the first is in flight, and an empty cleanup. The C++
//   driver calls each chain under its own typed handlers for five kinds (none,
//   CaseError, DerivedError, int, OtherError), both throwing calls of the
//   two-guard chain and four inputs: 632 cases per build.
// * The same module's touch family: the Linux 768-case campaign's CG frame
//   (e2e_aarch64_elf_link.rs `UNWIND_PROVIDER`/`UNWIND_DRIVER`) on 64-bit
//   inputs. `touch` adds its input to an imported memory word (`tcg_words`,
//   through the GOT), reads `&tcg_words[1]` from a relocated data slot, calls
//   the C++ provider directly and again through a function-pointer slot
//   (`CallIndirect`); the provider updates the word and throws from either
//   call. `touch_guarded` adds a CG cleanup pad running a guard destructor
//   around the direct call and makes the indirect call after it, so that
//   throw crosses the frame's LSDA at a call site with no pad; `touch_catch`
//   is a CG catch-all frame over `touch`. The driver runs each twin on the
//   Linux campaign's 64 inputs (eight 64-bit edges, then its LCG sequence)
//   and three throw stages (none, the direct call, the indirect call) and
//   prints the return value, the catch, the payload, all three memory words,
//   the provider's call and destructor counts and the event log: 1,152
//   cases per build, each equal to this file's own model line for line.
// * Rust module (declares `rust_eh_personality`), seven chains over a
//   panicking Rust leaf: cleanup pads that run a Rust guard's drop glue
//   (`ptr::drop_in_place`), an empty cleanup, a plain frame, nesting, two
//   guards, and a Rust frame that `catch_unwind`s and `resume_unwind`s
//   between two CG frames; three kinds (none, `panic_any`, `resume_unwind`),
//   observed by `catch_unwind`: 184 cases per build.
//
// Every chain case prints one line: return value, catch site, payload, the
// ordered event log (guard constructions and destructor runs with the
// in-flight exception count or `panicking()`, handler entries,
// exception-object destructions, the panic hook) and the residual state,
// which must be zero. The reference builds are checked against this file's
// own model (catch site, destructor ids, order and in-flight flag for every
// chain case; the whole line for every touch case), and every trust-cg build
// must print exactly the reference's lines:
//
// * AOT, O0-O3: the C++ object (both matrices, 1,784 cases per build) linked
//   into the executable by c++ and, as the Linux campaign does with its
//   shared object, into a CG dylib of its own that imports the helpers and
//   typeinfo from a separate C++ dylib: 2 x 4 x 1,784 cases; and 4 x 184 Rust
//   cases (rustc links the object): 15,008 cases. Apple's objdump and nm read
//   each linked image's `__unwind_info` back: FRAME-mode encodings for the
//   `NAME` twins and DWARF-mode encodings naming an `__eh_frame` FDE for the
//   `NAME_dyn` twins.
// * The unchecked in-memory JIT, O0-O3: the C++ module without its four typed
//   chains (the JIT refuses typed catches; each refusal is pinned by name
//   below), 4 x (472 + 1,152) cases through the C++ driver loaded with
//   dlopen, and the whole Rust module, 4 x 184 cases in process: 7,232 cases.
//   Every published function's FDE is read back through the process
//   unwinder; there, every frame (compact twins included) unwinds through its
//   registered FDE.
//
// Negative controls: mutated trust-ir functions (a cleanup pad that skips its
// guard's destructor, two invokes bound to each other's landing pad, a typed
// pad bound to `int` instead of `CaseError`, the touch family's cleanup pad
// without its destructor, `touch` without its memory-word store) must differ
// from the reference in exactly the cases the mutation reaches and in no
// other: 24 AOT runs (C++ and Rust, O0-O3) and 4 JIT runs (O0 and O2).
//
// Host-neutral rows (every host) read the Mach-O objects: every `NAME` twin
// has a FRAME-mode compact-unwind entry and no FDE, every `NAME_dyn` twin a
// DWARF-mode entry and an FDE naming its own LSDA, `__eh_frame` holds exactly
// one CIE (augmentation `zPLR`, naming the module's personality) and one FDE
// per `NAME_dyn` twin, each EH function carries its module's personality, the
// typed LSDAs GOT-relocate `__ZTI9CaseError` and `__ZTIi`, the touch
// family's two data slots relocate against `_tcg_words` and `_tcg_provider`,
// and its code reaches `_tcg_words` only through GOT loads.
// The JIT refusal row (AArch64 macOS) pins, per typed chain, the named
// `JitUnwindTypedCatchUnsupported` refusal, and the proof-grade JIT's
// `JitUnwindProofEvidenceUnavailable` refusal of the campaign's untyped
// chains.
//
// Evidence boundary: native execution against reference builds, models and
// object and image decoding. This is not a proof of the LSDA, the CFI, the
// personality routines or the unwinder, and the proof-grade JIT still refuses
// EH. trust-ir has no indirect invoke, so no CG landing pad covers an indirect
// call site.

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::macho::linker::{MachOParser, ParsedObject};
use trust_cg_codegen::macho::reloc::AArch64RelocKind;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_lower::function::EH_TYPE_TABLE_GLOBAL;
use trust_ir::value::{FuncTyId, GlobalId};
use trust_ir::{
    BinOp, Block, BlockId, CallingConv, CastOp, Constant, FuncId, FuncTy, Function, Global, ICmpOp,
    Inst, InstrNode, Linkage, Module, Ty, ValueId,
};

const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const DARWIN_TRIPLE: &str = "aarch64-apple-darwin";
const CXX_PERSONALITY: &str = "__gxx_personality_v0";
const RUST_PERSONALITY: &str = "rust_eh_personality";

/// Catch type indices of the C++ module's type table.
const TYPE_TABLE: [&str; 2] = ["_ZTI9CaseError", "_ZTIi"];
const CASE_ERROR: u32 = 1;
const INT: u32 = 2;
/// Selector of a catch-all match in a function that catches a typed
/// exception (`N + 1`) and in one that does not (`1`).
const TYPED_CATCH_ALL_SELECTOR: i128 = TYPE_TABLE.len() as i128 + 1;
const UNTYPED_CATCH_ALL_SELECTOR: i128 = 1;

// ---------------------------------------------------------------------------
// Chains
// ---------------------------------------------------------------------------

/// The C++ module's chains, in the table order of fixtures/eh_raii_darwin
/// (`TCG_CHAINS` in common.h).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CxxChain {
    Cleanup,
    CatchAll,
    CatchCase,
    CatchIntOrCase,
    CatchCaseThenAll,
    GuardCatchInt,
    TwoGuards,
    NestedCleanup,
    PlainMid,
    CatchOverPlain,
    Rethrow,
    CxxMid,
    CleanupInnerThrow,
    EmptyCleanup,
    DeepCatch,
}

const CXX_CHAINS: [CxxChain; 15] = [
    CxxChain::Cleanup,
    CxxChain::CatchAll,
    CxxChain::CatchCase,
    CxxChain::CatchIntOrCase,
    CxxChain::CatchCaseThenAll,
    CxxChain::GuardCatchInt,
    CxxChain::TwoGuards,
    CxxChain::NestedCleanup,
    CxxChain::PlainMid,
    CxxChain::CatchOverPlain,
    CxxChain::Rethrow,
    CxxChain::CxxMid,
    CxxChain::CleanupInnerThrow,
    CxxChain::EmptyCleanup,
    CxxChain::DeepCatch,
];

impl CxxChain {
    fn name(self) -> &'static str {
        match self {
            Self::Cleanup => "cleanup",
            Self::CatchAll => "catch_all",
            Self::CatchCase => "catch_case",
            Self::CatchIntOrCase => "catch_int_or_case",
            Self::CatchCaseThenAll => "catch_case_then_all",
            Self::GuardCatchInt => "guard_catch_int",
            Self::TwoGuards => "two_guards",
            Self::NestedCleanup => "nested_cleanup",
            Self::PlainMid => "plain_mid",
            Self::CatchOverPlain => "catch_over_plain",
            Self::Rethrow => "rethrow",
            Self::CxxMid => "cxx_mid",
            Self::CleanupInnerThrow => "cleanup_inner_throw",
            Self::EmptyCleanup => "empty_cleanup",
            Self::DeepCatch => "deep_catch",
        }
    }

    fn index(self) -> usize {
        CXX_CHAINS
            .iter()
            .position(|chain| *chain == self)
            .expect("every chain is in the table")
    }

    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    fn from_name(name: &str) -> Self {
        *CXX_CHAINS
            .iter()
            .find(|chain| chain.name() == name)
            .unwrap_or_else(|| panic!("unknown C++ chain {name}"))
    }

    /// Chains with a typed landing pad: the in-memory JIT refuses them.
    fn typed(self) -> bool {
        matches!(
            self,
            Self::CatchCase | Self::CatchIntOrCase | Self::CatchCaseThenAll | Self::GuardCatchInt
        )
    }

    /// Whether the chain's own frame has a landing pad.
    fn has_pad(self) -> bool {
        self != Self::PlainMid
    }

    /// The typeinfo symbols the chain's pads name.
    fn typeinfo(self) -> Vec<&'static str> {
        match self {
            Self::CatchCase | Self::CatchCaseThenAll => vec![TYPE_TABLE[0]],
            Self::CatchIntOrCase => vec![TYPE_TABLE[0], TYPE_TABLE[1]],
            Self::GuardCatchInt => vec![TYPE_TABLE[1]],
            _ => vec![],
        }
    }
}

/// The C++ module's touch family, in the table order of fixtures/eh_raii_darwin
/// (`TCG_TOUCH_CHAINS` in common.h): `(x: i64) -> i64` functions with the
/// Linux campaign's frame shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TouchChain {
    Touch,
    Guarded,
    Catch,
}

const TOUCH_CHAINS: [TouchChain; 3] = [TouchChain::Touch, TouchChain::Guarded, TouchChain::Catch];

impl TouchChain {
    fn name(self) -> &'static str {
        match self {
            Self::Touch => "touch",
            Self::Guarded => "touch_guarded",
            Self::Catch => "touch_catch",
        }
    }

    fn index(self) -> usize {
        TOUCH_CHAINS
            .iter()
            .position(|chain| *chain == self)
            .expect("every touch function is in the table")
    }

    fn has_pad(self) -> bool {
        self != Self::Touch
    }
}

/// The touch family's guard id, handler site, and the value `touch_catch`
/// adds on its normal path.
const TOUCH_GUARD: i128 = 31;
const TOUCH_CATCH_SITE: i128 = 301;
const TOUCH_CATCH_ADD: i128 = 32;

/// The Rust module's chains, in the table order of `rust_arm.rs`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RustChain {
    Cleanup,
    EmptyCleanup,
    Plain,
    Nested,
    Through,
    TwoGuards,
    RustMid,
}

const RUST_CHAINS: [RustChain; 7] = [
    RustChain::Cleanup,
    RustChain::EmptyCleanup,
    RustChain::Plain,
    RustChain::Nested,
    RustChain::Through,
    RustChain::TwoGuards,
    RustChain::RustMid,
];

impl RustChain {
    fn name(self) -> &'static str {
        match self {
            Self::Cleanup => "cleanup",
            Self::EmptyCleanup => "empty_cleanup",
            Self::Plain => "plain",
            Self::Nested => "nested",
            Self::Through => "through",
            Self::TwoGuards => "two_guards",
            Self::RustMid => "rust_mid",
        }
    }

    fn index(self) -> usize {
        RUST_CHAINS
            .iter()
            .position(|chain| *chain == self)
            .expect("every chain is in the table")
    }

    #[cfg(all(target_arch = "aarch64", target_os = "macos"))]
    fn from_name(name: &str) -> Self {
        *RUST_CHAINS
            .iter()
            .find(|chain| chain.name() == name)
            .unwrap_or_else(|| panic!("unknown Rust chain {name}"))
    }

    fn has_pad(self) -> bool {
        self != Self::Plain
    }
}

fn cxx_symbol(chain: CxxChain, dynamic: bool) -> String {
    format!("tcg_{}{}", chain.name(), if dynamic { "_dyn" } else { "" })
}

fn touch_symbol(chain: TouchChain, dynamic: bool) -> String {
    format!("tcg_{}{}", chain.name(), if dynamic { "_dyn" } else { "" })
}

fn rust_symbol(chain: RustChain, dynamic: bool) -> String {
    format!("tcgr_{}{}", chain.name(), if dynamic { "_dyn" } else { "" })
}

// ---------------------------------------------------------------------------
// trust-ir construction
// ---------------------------------------------------------------------------

fn b(index: u32) -> BlockId {
    BlockId::new(index)
}

fn f(index: u32) -> FuncId {
    FuncId::new(index)
}

fn declare(module: &mut Module, id: u32, name: &str, params: Vec<Ty>, returns: Vec<Ty>) {
    let signature = module
        .add_func_type(FuncTy {
            params,
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(f(id), name, signature, b(0));
    function.linkage = Linkage::External;
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

fn add_type_table(module: &mut Module) {
    let pointer = module
        .add_type(Ty::Ptr)
        .expect("Module::add_type: test fixture");
    module.globals.push(Global {
        name: EH_TYPE_TABLE_GLOBAL.to_string(),
        ty: Ty::Array(pointer, TYPE_TABLE.len() as u64),
        mutable: false,
        initializer: Some(Constant::Array(
            TYPE_TABLE
                .iter()
                .map(|symbol| Constant::SymbolAddr {
                    symbol: (*symbol).to_string(),
                    addend: 0,
                })
                .collect(),
        )),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
}

/// Function ids of the external callees a chain body may name. Roles a
/// module does not provide are `None`.
#[derive(Clone, Copy)]
struct Callees {
    leaf: u32,
    guard_init: u32,
    guard_fini: u32,
    scratch: u32,
    mid: u32,
    begin_catch: Option<u32>,
    end_catch: Option<u32>,
    rethrow: Option<u32>,
    on_any: Option<u32>,
    on_case: Option<u32>,
    on_int: Option<u32>,
    note: Option<u32>,
    inner_throw: Option<u32>,
}

impl Callees {
    fn role(role: Option<u32>, name: &str) -> u32 {
        role.unwrap_or_else(|| panic!("this module declares no `{name}`"))
    }
}

/// Block builder for one function of one parameter `x` (`v0`): `(x: i32) ->
/// i32` for a chain, `(x: i64) -> i64` for the touch family.
struct Code {
    param: Ty,
    next_value: u32,
    blocks: Vec<Block>,
    open: Option<(u32, Vec<InstrNode>)>,
}

impl Code {
    fn new(param: Ty) -> Self {
        Self {
            param,
            next_value: 1,
            blocks: Vec::new(),
            open: None,
        }
    }

    fn x() -> ValueId {
        ValueId::new(0)
    }

    fn fresh(&mut self) -> ValueId {
        let value = ValueId::new(self.next_value);
        self.next_value += 1;
        value
    }

    fn begin(&mut self, id: u32) {
        assert!(self.open.is_none(), "block {id} opened inside another");
        self.open = Some((id, Vec::new()));
    }

    fn emit(&mut self, node: InstrNode) {
        self.open.as_mut().expect("an open block").1.push(node);
    }

    fn terminate(&mut self, node: InstrNode) {
        let (id, mut body) = self.open.take().expect("an open block");
        body.push(node);
        let params = if id == 0 {
            vec![(Self::x(), self.param.clone())]
        } else {
            vec![]
        };
        self.blocks.push(Block {
            id: b(id),
            params,
            body,
        });
    }

    fn constant(&mut self, ty: Ty, value: i128) -> ValueId {
        let result = self.fresh();
        self.emit(
            InstrNode::new(Inst::Const {
                ty,
                value: Constant::Int(value),
            })
            .with_result(result),
        );
        result
    }

    fn binop(&mut self, op: BinOp, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.binop_ty(op, Ty::I32, lhs, rhs)
    }

    fn binop_ty(&mut self, op: BinOp, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        let result = self.fresh();
        self.emit(InstrNode::new(Inst::BinOp { op, ty, lhs, rhs }).with_result(result));
        result
    }

    fn add_const(&mut self, lhs: ValueId, value: i128) -> ValueId {
        self.add_const_ty(Ty::I32, lhs, value)
    }

    fn add_const_ty(&mut self, ty: Ty, lhs: ValueId, value: i128) -> ValueId {
        let rhs = self.constant(ty.clone(), value);
        self.binop_ty(BinOp::Add, ty, lhs, rhs)
    }

    fn zext_i32_to_i64(&mut self, operand: ValueId) -> ValueId {
        let result = self.fresh();
        self.emit(
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::I32,
                dst_ty: Ty::I64,
                operand,
            })
            .with_result(result),
        );
        result
    }

    fn global_addr(&mut self, global: GlobalId) -> ValueId {
        let result = self.fresh();
        self.emit(InstrNode::new(Inst::GlobalAddr { global }).with_result(result));
        result
    }

    fn load(&mut self, ty: Ty, ptr: ValueId) -> ValueId {
        let result = self.fresh();
        self.emit(
            InstrNode::new(Inst::Load {
                ty,
                ptr,
                volatile: false,
                align: Some(8),
            })
            .with_result(result),
        );
        result
    }

    fn store(&mut self, ty: Ty, ptr: ValueId, value: ValueId) {
        self.emit(InstrNode::new(Inst::Store {
            ty,
            ptr,
            value,
            volatile: false,
            align: Some(8),
        }));
    }

    fn call_indirect_value(
        &mut self,
        callee: ValueId,
        sig: FuncTyId,
        args: Vec<ValueId>,
    ) -> ValueId {
        let result = self.fresh();
        self.emit(
            InstrNode::new(Inst::CallIndirect {
                callee,
                sig,
                args,
                calling_conv: CallingConv::C,
            })
            .with_result(result),
        );
        result
    }

    fn call(&mut self, callee: u32, args: Vec<ValueId>) {
        self.emit(InstrNode::new(Inst::Call {
            callee: f(callee),
            args,
        }));
    }

    fn call_value(&mut self, callee: u32, args: Vec<ValueId>) -> ValueId {
        let result = self.fresh();
        self.emit(
            InstrNode::new(Inst::Call {
                callee: f(callee),
                args,
            })
            .with_result(result),
        );
        result
    }

    /// `invoke callee(args) to normal unwind unwind`, ending the block.
    fn invoke(
        &mut self,
        callee: u32,
        args: Vec<ValueId>,
        normal: u32,
        unwind: u32,
        returns_value: bool,
    ) -> Option<ValueId> {
        let result = returns_value.then(|| self.fresh());
        let node = InstrNode::new(Inst::Invoke {
            callee: f(callee),
            args,
            normal_dest: b(normal),
            normal_args: vec![],
            unwind_dest: b(unwind),
        });
        self.terminate(match result {
            Some(result) => node.with_result(result),
            None => node,
        });
        result
    }

    /// Open `id` as a landing pad; returns (exception pointer, selector).
    fn landing_pad(&mut self, id: u32, is_cleanup: bool, catches: Vec<u32>) -> (ValueId, ValueId) {
        self.begin(id);
        let exception = self.fresh();
        let selector = self.fresh();
        self.emit(
            InstrNode::new(Inst::LandingPad {
                is_cleanup,
                catch_type_indices: catches,
            })
            .with_results(vec![exception, selector]),
        );
        (exception, selector)
    }

    fn selector_is(&mut self, selector: ValueId, expected: i128) -> ValueId {
        let constant = self.constant(Ty::I32, expected);
        let result = self.fresh();
        self.emit(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I32,
                lhs: selector,
                rhs: constant,
            })
            .with_result(result),
        );
        result
    }

    fn cond_br(&mut self, cond: ValueId, then_block: u32, else_block: u32) {
        self.terminate(InstrNode::new(Inst::CondBr {
            cond,
            then_target: b(then_block),
            then_args: vec![],
            else_target: b(else_block),
            else_args: vec![],
        }));
    }

    fn ret(&mut self, value: ValueId) {
        self.terminate(InstrNode::new(Inst::Return {
            values: vec![value],
        }));
    }

    fn resume(&mut self, exception: ValueId) {
        self.terminate(InstrNode::new(Inst::Resume { exn: exception }));
    }

    fn unreachable(&mut self) {
        self.terminate(InstrNode::new(Inst::Unreachable));
    }

    /// A 16-byte, 8-aligned guard slot: a fixed frame object.
    fn guard_slot(&mut self) -> ValueId {
        let count = self.constant(Ty::I64, 2);
        let slot = self.fresh();
        self.emit(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: Some(count),
                align: Some(8),
            })
            .with_result(slot),
        );
        slot
    }

    /// The DWARF-fallback twin's prologue: a `(x & 63) + 8`-byte runtime
    /// alloca handed to the scratch helper, so the frame is runtime-sized.
    fn dynamic_prologue(&mut self, scratch: u32) {
        let length = if self.param == Ty::I64 {
            let mask = self.constant(Ty::I64, 63);
            let low = self.binop_ty(BinOp::And, Ty::I64, Self::x(), mask);
            self.add_const_ty(Ty::I64, low, 8)
        } else {
            let mask = self.constant(Ty::I32, 63);
            let low = self.binop(BinOp::And, Self::x(), mask);
            let length32 = self.add_const(low, 8);
            self.zext_i32_to_i64(length32)
        };
        let buffer = self.fresh();
        self.emit(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I8,
                count: Some(length),
                align: None,
            })
            .with_result(buffer),
        );
        self.call(scratch, vec![buffer, length]);
    }

    fn finish(self) -> Vec<Block> {
        assert!(self.open.is_none(), "every block is terminated");
        self.blocks
    }
}

/// What a catch handler does with the exception it claims.
#[derive(Clone, Copy)]
enum Handler {
    /// `on_any(site)` (the helper classifies the exception by rethrowing it).
    Any(i128),
    /// `on_case(site, begin_catch(exn))`.
    Case(i128),
    /// `on_int(site, *begin_catch(exn))`.
    Int(i128),
}

/// `[prologue] [guard] r = invoke callee(x) -> b1 unwind b2;
/// b1: [inner_throw] [fini] ret r + add;
/// b2: cleanup pad { [inner_throw] [fini] resume }`.
fn cleanup_chain(
    code: &mut Code,
    callees: &Callees,
    callee: u32,
    guard: Option<i128>,
    inner_throw: Option<i128>,
    add: i128,
) {
    let slot = guard.map(|id| {
        let slot = code.guard_slot();
        let id = code.constant(Ty::I32, id);
        code.call(callees.guard_init, vec![slot, id]);
        slot
    });
    let result = code
        .invoke(callee, vec![Code::x()], 1, 2, true)
        .expect("value");
    let run_cleanups = |code: &mut Code| {
        if let Some(site) = inner_throw {
            let site = code.constant(Ty::I32, site);
            code.call(
                Callees::role(callees.inner_throw, "inner_throw"),
                vec![site],
            );
        }
        if let Some(slot) = slot {
            code.call(callees.guard_fini, vec![slot]);
        }
    };
    code.begin(1);
    run_cleanups(code);
    let out = code.add_const(result, add);
    code.ret(out);
    let (exception, _) = code.landing_pad(2, true, vec![]);
    run_cleanups(code);
    code.resume(exception);
}

/// `[prologue] [guard] r = invoke callee(x) -> b1 unwind b2;
/// b1: [fini] ret r + add;
/// b2: pad(catches) { [fini] dispatch the selector over `handlers`, else
/// resume }`. A handler block claims the exception (`__cxa_begin_catch`),
/// runs its helper, ends the catch and returns the helper's value.
fn catch_chain(
    code: &mut Code,
    callees: &Callees,
    callee: u32,
    guard: Option<i128>,
    catches: Vec<u32>,
    handlers: &[(i128, Handler)],
    add: i128,
) {
    let slot = guard.map(|id| {
        let slot = code.guard_slot();
        let id = code.constant(Ty::I32, id);
        code.call(callees.guard_init, vec![slot, id]);
        slot
    });
    let result = code
        .invoke(callee, vec![Code::x()], 1, 2, true)
        .expect("value");
    code.begin(1);
    if let Some(slot) = slot {
        code.call(callees.guard_fini, vec![slot]);
    }
    let out = code.add_const(result, add);
    code.ret(out);
    let (exception, selector) = code.landing_pad(2, guard.is_some(), catches);
    if let Some(slot) = slot {
        code.call(callees.guard_fini, vec![slot]);
    }
    // Dispatch blocks 10.., handler blocks 20.., resume block 30.
    for (position, (expected, _)) in handlers.iter().enumerate() {
        let position = position as u32;
        if position > 0 {
            code.begin(10 + position);
        }
        let matched = code.selector_is(selector, *expected);
        let next = if (position as usize) + 1 < handlers.len() {
            10 + position + 1
        } else {
            30
        };
        code.cond_br(matched, 20 + position, next);
    }
    for (position, (_, handler)) in handlers.iter().enumerate() {
        code.begin(20 + position as u32);
        let begin_catch = Callees::role(callees.begin_catch, "__cxa_begin_catch");
        let object = code.call_value(begin_catch, vec![exception]);
        let value = match *handler {
            Handler::Any(site) => {
                let site = code.constant(Ty::I32, site);
                code.call_value(Callees::role(callees.on_any, "on_any"), vec![site])
            }
            Handler::Case(site) => {
                let site = code.constant(Ty::I32, site);
                code.call_value(
                    Callees::role(callees.on_case, "on_case"),
                    vec![site, object],
                )
            }
            Handler::Int(site) => {
                let loaded = code.fresh();
                code.emit(
                    InstrNode::new(Inst::Load {
                        ty: Ty::I32,
                        ptr: object,
                        volatile: false,
                        align: Some(4),
                    })
                    .with_result(loaded),
                );
                let site = code.constant(Ty::I32, site);
                code.call_value(Callees::role(callees.on_int, "on_int"), vec![site, loaded])
            }
        };
        code.call(Callees::role(callees.end_catch, "__cxa_end_catch"), vec![]);
        code.ret(value);
    }
    code.begin(30);
    code.resume(exception);
}

/// `[prologue] s1, s2 = slots; init(s1, a); r1 = invoke leaf(x) -> b1 unwind
/// b3; b1: init(s2, b); r2 = invoke leaf(r1) -> b2 unwind b4; b2: o = r1 ^
/// r2; fini(s2); fini(s1); ret o; b3: cleanup { fini(s1); resume }; b4:
/// cleanup { fini(s2); fini(s1); resume }`.
fn two_guards_chain(code: &mut Code, callees: &Callees, first: i128, second: i128) {
    let first_slot = code.guard_slot();
    let second_slot = code.guard_slot();
    let first_id = code.constant(Ty::I32, first);
    code.call(callees.guard_init, vec![first_slot, first_id]);
    let r1 = code
        .invoke(callees.leaf, vec![Code::x()], 1, 3, true)
        .expect("value");
    code.begin(1);
    let second_id = code.constant(Ty::I32, second);
    code.call(callees.guard_init, vec![second_slot, second_id]);
    let r2 = code
        .invoke(callees.leaf, vec![r1], 2, 4, true)
        .expect("value");
    code.begin(2);
    let out = code.binop(BinOp::Xor, r1, r2);
    code.call(callees.guard_fini, vec![second_slot]);
    code.call(callees.guard_fini, vec![first_slot]);
    code.ret(out);
    let (exception, _) = code.landing_pad(3, true, vec![]);
    code.call(callees.guard_fini, vec![first_slot]);
    code.resume(exception);
    let (exception, _) = code.landing_pad(4, true, vec![]);
    code.call(callees.guard_fini, vec![second_slot]);
    code.call(callees.guard_fini, vec![first_slot]);
    code.resume(exception);
}

/// A plain frame: `[prologue] r = leaf(x); ret r + add` (no pad).
fn plain_chain(code: &mut Code, callees: &Callees, add: i128) {
    let result = code.call_value(callees.leaf, vec![Code::x()]);
    let out = code.add_const(result, add);
    code.ret(out);
}

/// `r = invoke leaf(x) -> b1 unwind b2; b1: ret r + 11; b2: catch-all pad {
/// p = begin_catch(e); note(111); invoke __cxa_rethrow() -> b3 unwind b4 };
/// b3: unreachable; b4: cleanup { end_catch(); resume }`.
fn rethrow_chain(code: &mut Code, callees: &Callees) {
    let result = code
        .invoke(callees.leaf, vec![Code::x()], 1, 2, true)
        .expect("value");
    code.begin(1);
    let out = code.add_const(result, 11);
    code.ret(out);
    let (exception, selector) = code.landing_pad(2, false, vec![0]);
    let matched = code.selector_is(selector, UNTYPED_CATCH_ALL_SELECTOR);
    code.cond_br(matched, 5, 6);
    code.begin(5);
    code.call_value(
        Callees::role(callees.begin_catch, "__cxa_begin_catch"),
        vec![exception],
    );
    let site = code.constant(Ty::I32, 111);
    code.call(Callees::role(callees.note, "note"), vec![site]);
    code.invoke(
        Callees::role(callees.rethrow, "__cxa_rethrow"),
        vec![],
        3,
        4,
        false,
    );
    code.begin(3);
    code.unreachable();
    let (rethrown, _) = code.landing_pad(4, true, vec![]);
    code.call(Callees::role(callees.end_catch, "__cxa_end_catch"), vec![]);
    code.resume(rethrown);
    code.begin(6);
    code.resume(exception);
}

fn define_chain(
    module: &mut Module,
    id: u32,
    name: &str,
    dynamic: bool,
    callees: &Callees,
    body: impl FnOnce(&mut Code),
) {
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(f(id), name, signature, b(0));
    let mut code = Code::new(Ty::I32);
    code.begin(0);
    if dynamic {
        code.dynamic_prologue(callees.scratch);
    }
    body(&mut code);
    function.blocks = code.finish();
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

/// The touch family's globals: the imported memory words and the two
/// relocated pointer slots, as the Linux campaign's module declares them.
struct TouchGlobals {
    /// `tcg_words` (`[i64; 3]`, defined by the C++ helpers).
    words: GlobalId,
    /// A mutable pointer slot holding `&tcg_words[1]`.
    data_slot: GlobalId,
    /// A mutable pointer slot holding `tcg_provider`.
    fn_slot: GlobalId,
}

fn add_touch_globals(module: &mut Module) -> TouchGlobals {
    let word = module
        .add_type(Ty::I64)
        .expect("Module::add_type: test fixture");
    let mut push = |name: &str, ty: Ty, linkage: Linkage, initializer: Option<Constant>| {
        module.globals.push(Global {
            name: name.to_string(),
            ty,
            mutable: true,
            initializer,
            linkage,
            tls: None,
            align: Some(8),
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        GlobalId::new(module.globals.len() as u32 - 1)
    };
    let slot = |symbol: &str, addend: i64| {
        Some(Constant::SymbolAddr {
            symbol: symbol.to_string(),
            addend,
        })
    };
    TouchGlobals {
        words: push("tcg_words", Ty::Array(word, 3), Linkage::External, None),
        data_slot: push(
            "tcg_touch_data_slot",
            Ty::Ptr,
            Linkage::Internal,
            slot("tcg_words", 8),
        ),
        fn_slot: push(
            "tcg_touch_fn_slot",
            Ty::Ptr,
            Linkage::Internal,
            slot("tcg_provider", 0),
        ),
    }
}

/// `[prologue] words[0] += x; p = *data_slot; [guard] first = provider(x, p)
/// (an invoke to b1 with a cleanup pad b2 when guarded); [fini] f =
/// *fn_slot; ret f(first, p)` (a `CallIndirect`, after the guard is gone).
fn touch_body(
    code: &mut Code,
    callees: &Callees,
    globals: &TouchGlobals,
    provider: u32,
    provider_sig: FuncTyId,
    guard: Option<i128>,
) {
    let words = code.global_addr(globals.words);
    let first_word = code.load(Ty::I64, words);
    let sum = code.binop_ty(BinOp::Add, Ty::I64, first_word, Code::x());
    code.store(Ty::I64, words, sum);
    let data_slot = code.global_addr(globals.data_slot);
    let word = code.load(Ty::Ptr, data_slot);
    let indirect = |code: &mut Code, first: ValueId| {
        let fn_slot = code.global_addr(globals.fn_slot);
        let target = code.load(Ty::Ptr, fn_slot);
        let result = code.call_indirect_value(target, provider_sig, vec![first, word]);
        code.ret(result);
    };
    match guard {
        None => {
            let first = code.call_value(provider, vec![Code::x(), word]);
            indirect(code, first);
        }
        Some(id) => {
            let slot = code.guard_slot();
            let id = code.constant(Ty::I32, id);
            code.call(callees.guard_init, vec![slot, id]);
            let first = code
                .invoke(provider, vec![Code::x(), word], 1, 2, true)
                .expect("value");
            code.begin(1);
            code.call(callees.guard_fini, vec![slot]);
            indirect(code, first);
            let (exception, _) = code.landing_pad(2, true, vec![]);
            code.call(callees.guard_fini, vec![slot]);
            code.resume(exception);
        }
    }
}

/// `r = invoke inner(x) -> b1 unwind b2; b1: ret r + 32; b2: catch-all pad {
/// begin_catch(e); v = on_any(301); end_catch(); ret zext(v) }`.
fn touch_catch_body(code: &mut Code, callees: &Callees, inner: u32) {
    let result = code
        .invoke(inner, vec![Code::x()], 1, 2, true)
        .expect("value");
    code.begin(1);
    let out = code.add_const_ty(Ty::I64, result, TOUCH_CATCH_ADD);
    code.ret(out);
    let (exception, selector) = code.landing_pad(2, false, vec![0]);
    let matched = code.selector_is(selector, UNTYPED_CATCH_ALL_SELECTOR);
    code.cond_br(matched, 3, 4);
    code.begin(3);
    code.call_value(
        Callees::role(callees.begin_catch, "__cxa_begin_catch"),
        vec![exception],
    );
    let site = code.constant(Ty::I32, TOUCH_CATCH_SITE);
    let value = code.call_value(Callees::role(callees.on_any, "on_any"), vec![site]);
    code.call(Callees::role(callees.end_catch, "__cxa_end_catch"), vec![]);
    let wide = code.zext_i32_to_i64(value);
    code.ret(wide);
    code.begin(4);
    code.resume(exception);
}

fn define_touch(
    module: &mut Module,
    id: u32,
    name: &str,
    dynamic: bool,
    callees: &Callees,
    body: impl FnOnce(&mut Code),
) {
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(f(id), name, signature, b(0));
    let mut code = Code::new(Ty::I64);
    code.begin(0);
    if dynamic {
        code.dynamic_prologue(callees.scratch);
    }
    body(&mut code);
    function.blocks = code.finish();
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

const CXX_FIRST_CHAIN_ID: u32 = 20;
const TOUCH_FIRST_ID: u32 = 60;
const TOUCH_PROVIDER_ID: u32 = 13;

fn touch_id(chain: TouchChain, dynamic: bool) -> u32 {
    TOUCH_FIRST_ID
        + if dynamic {
            TOUCH_CHAINS.len() as u32
        } else {
            0
        }
        + chain.index() as u32
}

fn cxx_chain_id(chain: CxxChain, dynamic: bool) -> u32 {
    CXX_FIRST_CHAIN_ID + if dynamic { CXX_CHAINS.len() as u32 } else { 0 } + chain.index() as u32
}

/// The C++ module. `chains` and `touch` select the chains and touch
/// functions it defines (both twins of each); the type table is present when
/// any selected chain is typed, the touch globals and provider when any touch
/// function is selected.
fn cxx_module(chains: &[CxxChain], touch: &[TouchChain]) -> Module {
    let mut module = Module::new("darwin_eh_raii_cxx");
    module.target_info = Some(trust_ir::TargetInfo {
        triple: DARWIN_TRIPLE.into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    declare(&mut module, 0, "cxx_leaf", vec![Ty::I32], vec![Ty::I32]);
    declare(
        &mut module,
        1,
        "tcg_guard_init",
        vec![Ty::Ptr, Ty::I32],
        vec![],
    );
    declare(&mut module, 2, "tcg_guard_fini", vec![Ty::Ptr], vec![]);
    declare(
        &mut module,
        3,
        "__cxa_begin_catch",
        vec![Ty::Ptr],
        vec![Ty::Ptr],
    );
    declare(&mut module, 4, "__cxa_end_catch", vec![], vec![]);
    declare(&mut module, 5, "__cxa_rethrow", vec![], vec![]);
    declare(&mut module, 6, "tcg_on_any", vec![Ty::I32], vec![Ty::I32]);
    declare(
        &mut module,
        7,
        "tcg_on_case",
        vec![Ty::I32, Ty::Ptr],
        vec![Ty::I32],
    );
    declare(
        &mut module,
        8,
        "tcg_on_int",
        vec![Ty::I32, Ty::I32],
        vec![Ty::I32],
    );
    declare(&mut module, 9, "tcg_note", vec![Ty::I32], vec![]);
    declare(
        &mut module,
        10,
        "cxx_mid_frame",
        vec![Ty::I32],
        vec![Ty::I32],
    );
    declare(&mut module, 11, "tcg_inner_throw", vec![Ty::I32], vec![]);
    declare(
        &mut module,
        12,
        "tcg_scratch",
        vec![Ty::Ptr, Ty::I64],
        vec![],
    );
    if chains.iter().any(|chain| chain.typed()) {
        add_type_table(&mut module);
    }
    let touch_globals = (!touch.is_empty()).then(|| {
        declare(
            &mut module,
            TOUCH_PROVIDER_ID,
            "tcg_provider",
            vec![Ty::I64, Ty::Ptr],
            vec![Ty::I64],
        );
        add_touch_globals(&mut module)
    });
    let callees = Callees {
        leaf: 0,
        guard_init: 1,
        guard_fini: 2,
        scratch: 12,
        mid: 10,
        begin_catch: Some(3),
        end_catch: Some(4),
        rethrow: Some(5),
        on_any: Some(6),
        on_case: Some(7),
        on_int: Some(8),
        note: Some(9),
        inner_throw: Some(11),
    };
    for dynamic in [false, true] {
        for &chain in chains {
            let same = |inner: CxxChain| {
                assert!(
                    chains.contains(&inner),
                    "{chain:?} calls {inner:?}, which the module must define"
                );
                cxx_chain_id(inner, dynamic)
            };
            let id = cxx_chain_id(chain, dynamic);
            let name = cxx_symbol(chain, dynamic);
            let c = &callees;
            match chain {
                CxxChain::Cleanup => define_chain(&mut module, id, &name, dynamic, c, |code| {
                    cleanup_chain(code, c, c.leaf, Some(1), None, 1)
                }),
                CxxChain::CatchAll => define_chain(&mut module, id, &name, dynamic, c, |code| {
                    catch_chain(
                        code,
                        c,
                        c.leaf,
                        None,
                        vec![0],
                        &[(UNTYPED_CATCH_ALL_SELECTOR, Handler::Any(21))],
                        2,
                    )
                }),
                CxxChain::CatchCase => define_chain(&mut module, id, &name, dynamic, c, |code| {
                    catch_chain(
                        code,
                        c,
                        c.leaf,
                        None,
                        vec![CASE_ERROR],
                        &[(i128::from(CASE_ERROR), Handler::Case(31))],
                        3,
                    )
                }),
                CxxChain::CatchIntOrCase => {
                    define_chain(&mut module, id, &name, dynamic, c, |code| {
                        catch_chain(
                            code,
                            c,
                            c.leaf,
                            None,
                            vec![INT, CASE_ERROR],
                            &[
                                (i128::from(INT), Handler::Int(41)),
                                (i128::from(CASE_ERROR), Handler::Case(42)),
                            ],
                            4,
                        )
                    })
                }
                CxxChain::CatchCaseThenAll => {
                    define_chain(&mut module, id, &name, dynamic, c, |code| {
                        catch_chain(
                            code,
                            c,
                            c.leaf,
                            None,
                            vec![CASE_ERROR, 0],
                            &[
                                (i128::from(CASE_ERROR), Handler::Case(51)),
                                (TYPED_CATCH_ALL_SELECTOR, Handler::Any(52)),
                            ],
                            5,
                        )
                    })
                }
                CxxChain::GuardCatchInt => {
                    define_chain(&mut module, id, &name, dynamic, c, |code| {
                        catch_chain(
                            code,
                            c,
                            c.leaf,
                            Some(6),
                            vec![INT],
                            &[(i128::from(INT), Handler::Int(61))],
                            6,
                        )
                    })
                }
                CxxChain::TwoGuards => define_chain(&mut module, id, &name, dynamic, c, |code| {
                    two_guards_chain(code, c, 71, 72)
                }),
                CxxChain::NestedCleanup => {
                    let inner = same(CxxChain::Cleanup);
                    define_chain(&mut module, id, &name, dynamic, c, |code| {
                        cleanup_chain(code, c, inner, Some(8), None, 8)
                    })
                }
                CxxChain::PlainMid => define_chain(&mut module, id, &name, dynamic, c, |code| {
                    plain_chain(code, c, 9)
                }),
                CxxChain::CatchOverPlain => {
                    let inner = same(CxxChain::PlainMid);
                    define_chain(&mut module, id, &name, dynamic, c, |code| {
                        catch_chain(
                            code,
                            c,
                            inner,
                            None,
                            vec![0],
                            &[(UNTYPED_CATCH_ALL_SELECTOR, Handler::Any(101))],
                            10,
                        )
                    })
                }
                CxxChain::Rethrow => define_chain(&mut module, id, &name, dynamic, c, |code| {
                    rethrow_chain(code, c)
                }),
                CxxChain::CxxMid => define_chain(&mut module, id, &name, dynamic, c, |code| {
                    cleanup_chain(code, c, c.mid, Some(12), None, 12)
                }),
                CxxChain::CleanupInnerThrow => {
                    define_chain(&mut module, id, &name, dynamic, c, |code| {
                        cleanup_chain(code, c, c.leaf, None, Some(13), 13)
                    })
                }
                CxxChain::EmptyCleanup => {
                    define_chain(&mut module, id, &name, dynamic, c, |code| {
                        cleanup_chain(code, c, c.leaf, None, None, 14)
                    })
                }
                CxxChain::DeepCatch => {
                    let inner = same(CxxChain::NestedCleanup);
                    define_chain(&mut module, id, &name, dynamic, c, |code| {
                        catch_chain(
                            code,
                            c,
                            inner,
                            None,
                            vec![0],
                            &[(UNTYPED_CATCH_ALL_SELECTOR, Handler::Any(151))],
                            15,
                        )
                    })
                }
            }
        }
    }
    if let Some(globals) = &touch_globals {
        let provider_sig = module
            .add_func_type(FuncTy {
                params: vec![Ty::I64, Ty::Ptr],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        for dynamic in [false, true] {
            for &chain in touch {
                let id = touch_id(chain, dynamic);
                let name = touch_symbol(chain, dynamic);
                let c = &callees;
                match chain {
                    TouchChain::Touch => define_touch(&mut module, id, &name, dynamic, c, |code| {
                        touch_body(code, c, globals, TOUCH_PROVIDER_ID, provider_sig, None)
                    }),
                    TouchChain::Guarded => {
                        define_touch(&mut module, id, &name, dynamic, c, |code| {
                            touch_body(
                                code,
                                c,
                                globals,
                                TOUCH_PROVIDER_ID,
                                provider_sig,
                                Some(TOUCH_GUARD),
                            )
                        })
                    }
                    TouchChain::Catch => {
                        assert!(
                            touch.contains(&TouchChain::Touch),
                            "touch_catch calls touch, which the module must define"
                        );
                        let inner = touch_id(TouchChain::Touch, dynamic);
                        define_touch(&mut module, id, &name, dynamic, c, |code| {
                            touch_catch_body(code, c, inner)
                        })
                    }
                }
            }
        }
    }
    module
}

/// The chains the unchecked JIT publishes: every chain without a typed pad
/// (and, with them, the whole touch family).
fn untyped_cxx_chains() -> Vec<CxxChain> {
    CXX_CHAINS
        .into_iter()
        .filter(|chain| !chain.typed())
        .collect()
}

const RUST_FIRST_CHAIN_ID: u32 = 20;

fn rust_chain_id(chain: RustChain, dynamic: bool) -> u32 {
    RUST_FIRST_CHAIN_ID + if dynamic { RUST_CHAINS.len() as u32 } else { 0 } + chain.index() as u32
}

/// The Rust module: declaring `rust_eh_personality` makes it the personality
/// of every EH function.
fn rust_module() -> Module {
    let mut module = Module::new("darwin_eh_raii_rust");
    module.target_info = Some(trust_ir::TargetInfo {
        triple: DARWIN_TRIPLE.into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    declare(&mut module, 0, "rs_leaf", vec![Ty::I32], vec![Ty::I32]);
    declare(
        &mut module,
        1,
        "rs_guard_init",
        vec![Ty::Ptr, Ty::I32],
        vec![],
    );
    declare(&mut module, 2, "rs_guard_drop", vec![Ty::Ptr], vec![]);
    declare(&mut module, 3, "rs_mid", vec![Ty::I32], vec![Ty::I32]);
    declare(&mut module, 4, "rs_scratch", vec![Ty::Ptr, Ty::I64], vec![]);
    declare(&mut module, 5, RUST_PERSONALITY, vec![], vec![]);
    let callees = Callees {
        leaf: 0,
        guard_init: 1,
        guard_fini: 2,
        scratch: 4,
        mid: 3,
        begin_catch: None,
        end_catch: None,
        rethrow: None,
        on_any: None,
        on_case: None,
        on_int: None,
        note: None,
        inner_throw: None,
    };
    for dynamic in [false, true] {
        for chain in RUST_CHAINS {
            let id = rust_chain_id(chain, dynamic);
            let name = rust_symbol(chain, dynamic);
            let c = &callees;
            match chain {
                RustChain::Cleanup => define_chain(&mut module, id, &name, dynamic, c, |code| {
                    cleanup_chain(code, c, c.leaf, Some(1), None, 1)
                }),
                RustChain::EmptyCleanup => {
                    define_chain(&mut module, id, &name, dynamic, c, |code| {
                        cleanup_chain(code, c, c.leaf, None, None, 2)
                    })
                }
                RustChain::Plain => define_chain(&mut module, id, &name, dynamic, c, |code| {
                    plain_chain(code, c, 3)
                }),
                RustChain::Nested => {
                    let inner = rust_chain_id(RustChain::Cleanup, dynamic);
                    define_chain(&mut module, id, &name, dynamic, c, |code| {
                        cleanup_chain(code, c, inner, Some(4), None, 4)
                    })
                }
                RustChain::Through => {
                    let inner = rust_chain_id(RustChain::Plain, dynamic);
                    define_chain(&mut module, id, &name, dynamic, c, |code| {
                        cleanup_chain(code, c, inner, Some(5), None, 5)
                    })
                }
                RustChain::TwoGuards => define_chain(&mut module, id, &name, dynamic, c, |code| {
                    two_guards_chain(code, c, 61, 62)
                }),
                RustChain::RustMid => define_chain(&mut module, id, &name, dynamic, c, |code| {
                    cleanup_chain(code, c, c.mid, Some(7), None, 7)
                }),
            }
        }
    }
    module
}

fn compile_darwin(module: &Module, opt_level: OptLevel) -> Vec<u8> {
    let spec = TargetSpec::parse(DARWIN_TRIPLE).expect("triple parses");
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        spec,
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .unwrap_or_else(|error| panic!("{} {opt_level:?}: {error}", module.name))
    .object_code
}

// ---------------------------------------------------------------------------
// Object readback (every host)
// ---------------------------------------------------------------------------

/// `UNWIND_ARM64_MODE_MASK` and the two modes the campaign relies on.
const UNWIND_ARM64_MODE_MASK: u32 = 0x0f00_0000;
const UNWIND_ARM64_MODE_FRAME: u32 = 0x0400_0000;
const UNWIND_ARM64_MODE_DWARF: u32 = 0x0300_0000;

/// One `__LD,__compact_unwind` entry of a function, read from the object.
struct CompactEntry {
    mode: u32,
    personality: Option<String>,
    has_lsda: bool,
}

fn symbol_name(parsed: &ParsedObject, index: u32) -> String {
    parsed.symbols[index as usize].name.as_str().to_owned()
}

/// Every compact-unwind entry by function symbol (Mach-O spelling), from
/// the entry's 32 bytes and its relocations (function start at +0,
/// personality at +16, LSDA at +24).
fn compact_entries(parsed: &ParsedObject) -> std::collections::BTreeMap<String, CompactEntry> {
    let section = parsed
        .sections
        .iter()
        .find(|section| section.name == "__compact_unwind")
        .expect("the object carries __LD,__compact_unwind");
    assert_eq!(section.data.len() % 32, 0, "32-byte entries");
    let mut entries = std::collections::BTreeMap::new();
    for (index, entry) in section.data.as_chunks::<32>().0.iter().enumerate() {
        let base = (index * 32) as u32;
        let at = |offset: u32| {
            section
                .relocations
                .iter()
                .find(|reloc| reloc.offset == base + offset)
        };
        let function = at(0).expect("function-start relocation");
        assert!(function.is_extern, "function start names its symbol");
        let personality = at(16).map(|reloc| {
            assert!(reloc.is_extern, "personality names its symbol");
            symbol_name(parsed, reloc.symbol_index)
        });
        let encoding = u32::from_le_bytes(entry[12..16].try_into().unwrap());
        let previous = entries.insert(
            symbol_name(parsed, function.symbol_index),
            CompactEntry {
                mode: encoding & UNWIND_ARM64_MODE_MASK,
                personality,
                has_lsda: at(24).is_some(),
            },
        );
        assert!(previous.is_none(), "one entry per function");
    }
    entries
}

/// What `__eh_frame` names: the FDEs' pc-begin functions, their LSDAs and
/// the personalities the CIEs GOT-relocate (each sorted, deduplicated), and
/// the section's own records: each CIE's augmentation string, in order, and
/// the FDE count.
struct EhFrameTargets {
    functions: Vec<String>,
    lsdas: Vec<String>,
    personalities: Vec<String>,
    cie_augmentations: Vec<String>,
    fdes: usize,
}

/// Walk the `__eh_frame` records: a 32-bit length (no 64-bit extension),
/// then a 32-bit CIE id that is zero for a CIE (followed by its version byte
/// and NUL-terminated augmentation string) and a back-pointer for an FDE.
fn eh_frame_records(data: &[u8]) -> (Vec<String>, usize) {
    let mut cies = Vec::new();
    let mut fdes = 0;
    let mut at = 0;
    while at < data.len() {
        let length = u32::from_le_bytes(data[at..at + 4].try_into().unwrap()) as usize;
        assert!(
            length != 0 && length != 0xffff_ffff,
            "record at {at}: length {length:#x}"
        );
        let record = &data[at + 4..at + 4 + length];
        if u32::from_le_bytes(record[..4].try_into().unwrap()) == 0 {
            assert_eq!(record[4], 1, "CIE at {at}: version");
            let augmentation = &record[5..];
            let end = augmentation
                .iter()
                .position(|byte| *byte == 0)
                .expect("NUL-terminated augmentation");
            cies.push(String::from_utf8(augmentation[..end].to_vec()).expect("ASCII"));
        } else {
            fdes += 1;
        }
        at += 4 + length;
    }
    (cies, fdes)
}

fn eh_frame_targets(parsed: &ParsedObject) -> EhFrameTargets {
    let mut targets = EhFrameTargets {
        functions: vec![],
        lsdas: vec![],
        personalities: vec![],
        cie_augmentations: vec![],
        fdes: 0,
    };
    let Some(section) = parsed
        .sections
        .iter()
        .find(|section| section.name == "__eh_frame")
    else {
        return targets;
    };
    (targets.cie_augmentations, targets.fdes) = eh_frame_records(&section.data);
    for reloc in &section.relocations {
        let name = symbol_name(parsed, reloc.symbol_index);
        match reloc.kind {
            AArch64RelocKind::Unsigned if name.contains("GCC_except_table") => {
                targets.lsdas.push(name)
            }
            AArch64RelocKind::Unsigned => targets.functions.push(name),
            AArch64RelocKind::PointerToGot => targets.personalities.push(name),
            _ => {}
        }
    }
    for list in [
        &mut targets.functions,
        &mut targets.lsdas,
        &mut targets.personalities,
    ] {
        list.sort();
        list.dedup();
    }
    targets
}

/// Every chain twin has the frame shape its family names, and every EH
/// frame reaches its personality and LSDA through that shape: a compact
/// FRAME entry for `NAME`, a DWARF-mode entry plus an FDE for `NAME_dyn`,
/// under the section's single CIE (augmentation `zPLR`, naming the
/// module's personality).
fn check_frame_shapes(parsed: &ParsedObject, level: OptLevel, personality: &str, twins: &[Twin]) {
    let entries = compact_entries(parsed);
    let eh_frame = eh_frame_targets(parsed);
    let mach_personality = format!("_{personality}");
    let mut expected_fdes = Vec::new();
    let mut expected_fde_lsdas = Vec::new();
    for Twin {
        symbol,
        dynamic,
        has_pad,
    } in twins
    {
        let mach = format!("_{symbol}");
        let entry = entries
            .get(&mach)
            .unwrap_or_else(|| panic!("{level:?}: no compact-unwind entry for {symbol}"));
        if *dynamic {
            assert_eq!(
                entry.mode, UNWIND_ARM64_MODE_DWARF,
                "{level:?}: {symbol} is runtime-sized and must defer to its FDE"
            );
            // Every FDE sits under the module's one zPLR CIE (checked
            // below), whose augmentation gives each FDE an LSDA pointer: a
            // pad-free twin names a no-handler LSDA of its own, which the
            // native rows unwind through.
            expected_fde_lsdas.push(format!("_GCC_except_table{mach}"));
            expected_fdes.push(mach);
        } else {
            assert_eq!(
                entry.mode, UNWIND_ARM64_MODE_FRAME,
                "{level:?}: {symbol} has a fixed frame and must use compact unwind"
            );
            assert_eq!(
                entry.personality.as_deref(),
                has_pad.then_some(mach_personality.as_str()),
                "{level:?}: {symbol}'s compact entry names its personality iff it has a pad"
            );
            assert_eq!(entry.has_lsda, *has_pad, "{level:?}: {symbol} LSDA");
        }
    }
    expected_fdes.sort();
    expected_fde_lsdas.sort();
    assert_eq!(
        eh_frame.functions, expected_fdes,
        "{level:?}: exactly the runtime-sized twins get an __eh_frame FDE"
    );
    assert_eq!(
        eh_frame.lsdas, expected_fde_lsdas,
        "{level:?}: each runtime-sized twin names its own LSDA from its FDE"
    );
    assert_eq!(
        eh_frame.personalities,
        vec![mach_personality],
        "{level:?}: the DWARF-fallback CIE names the module's personality"
    );
    assert_eq!(
        eh_frame.cie_augmentations,
        ["zPLR"],
        "{level:?}: __eh_frame holds exactly one CIE, with a personality, an LSDA encoding \
         and an FDE pointer encoding"
    );
    assert_eq!(
        eh_frame.fdes,
        expected_fdes.len(),
        "{level:?}: one FDE per runtime-sized twin and no other record"
    );
}

/// One chain twin: its symbol, whether it is the runtime-sized
/// (DWARF-fallback) twin, and whether its frame has a landing pad.
struct Twin {
    symbol: String,
    dynamic: bool,
    has_pad: bool,
}

fn cxx_twins(chains: &[CxxChain], touch: &[TouchChain]) -> Vec<Twin> {
    [false, true]
        .into_iter()
        .flat_map(|dynamic| {
            chains
                .iter()
                .map(move |chain| Twin {
                    symbol: cxx_symbol(*chain, dynamic),
                    dynamic,
                    has_pad: chain.has_pad(),
                })
                .chain(touch.iter().map(move |chain| Twin {
                    symbol: touch_symbol(*chain, dynamic),
                    dynamic,
                    has_pad: chain.has_pad(),
                }))
        })
        .collect()
}

fn rust_twins() -> Vec<Twin> {
    [false, true]
        .into_iter()
        .flat_map(|dynamic| {
            RUST_CHAINS.into_iter().map(move |chain| Twin {
                symbol: rust_symbol(chain, dynamic),
                dynamic,
                has_pad: chain.has_pad(),
            })
        })
        .collect()
}

#[test]
fn cxx_objects_pin_compact_and_dwarf_fallback_frames_and_typeinfo() {
    let module = cxx_module(&CXX_CHAINS, &TOUCH_CHAINS);
    let chains = cxx_twins(&CXX_CHAINS, &TOUCH_CHAINS);
    for level in OPT_LEVELS {
        let object = compile_darwin(&module, level);
        let parsed = MachOParser::parse(&object).expect("parse Mach-O object");
        check_frame_shapes(&parsed, level, CXX_PERSONALITY, &chains);
        // The touch family's two pointer slots relocate against the imported
        // words and the provider (the linked images bind both).
        let data = parsed
            .sections
            .iter()
            .find(|section| section.name == "__data")
            .expect("the C++ object carries the touch family's pointer slots");
        let mut slot_targets: Vec<String> = data
            .relocations
            .iter()
            .map(|reloc| {
                assert_eq!(reloc.kind, AArch64RelocKind::Unsigned, "{level:?}");
                symbol_name(&parsed, reloc.symbol_index)
            })
            .collect();
        slot_targets.sort();
        assert_eq!(
            slot_targets,
            ["_tcg_provider", "_tcg_words"],
            "{level:?}: one absolute pointer slot per touch-family target"
        );
        // The code reaches the imported words only through a GOT slot.
        let text = parsed
            .sections
            .iter()
            .find(|section| section.name == "__text")
            .expect("__text");
        let mut word_access: Vec<AArch64RelocKind> = text
            .relocations
            .iter()
            .filter(|reloc| {
                reloc.is_extern && symbol_name(&parsed, reloc.symbol_index) == "_tcg_words"
            })
            .map(|reloc| reloc.kind)
            .collect();
        word_access.sort_by_key(|kind| *kind as u8);
        word_access.dedup();
        assert_eq!(
            word_access,
            [
                AArch64RelocKind::GotLoadPage21,
                AArch64RelocKind::GotLoadPageoff12
            ],
            "{level:?}: tcg_words is an import bound through the GOT"
        );
        let lsda = parsed
            .sections
            .iter()
            .find(|section| section.name == "__gcc_except_tab")
            .expect("the C++ object carries __gcc_except_tab");
        let mut typeinfo: Vec<String> = lsda
            .relocations
            .iter()
            .map(|reloc| {
                assert_eq!(reloc.kind, AArch64RelocKind::PointerToGot, "{level:?}");
                symbol_name(&parsed, reloc.symbol_index)
            })
            .collect();
        typeinfo.sort();
        typeinfo.dedup();
        assert_eq!(
            typeinfo,
            ["__ZTI9CaseError", "__ZTIi"],
            "{level:?}: the typed pads bind both typeinfo symbols through the GOT"
        );
        assert!(
            !parsed
                .symbols
                .iter()
                .any(|symbol| symbol.name.as_str().contains(RUST_PERSONALITY)),
            "{level:?}: a C++-only module imports no Rust personality"
        );
    }
}

#[test]
fn rust_objects_pin_compact_and_dwarf_fallback_frames() {
    let module = rust_module();
    let chains = rust_twins();
    for level in OPT_LEVELS {
        let object = compile_darwin(&module, level);
        let parsed = MachOParser::parse(&object).expect("parse Mach-O object");
        check_frame_shapes(&parsed, level, RUST_PERSONALITY, &chains);
        assert!(
            !parsed
                .symbols
                .iter()
                .any(|symbol| symbol.name.as_str().contains(CXX_PERSONALITY)),
            "{level:?}: the Rust module imports no C++ personality"
        );
    }
}

// ---------------------------------------------------------------------------
// The model the reference traces must satisfy
// ---------------------------------------------------------------------------

/// Where a case's exception ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Catch {
    /// No exception: the chain returned.
    Returned,
    /// A chain's own handler claimed it (the helper's site).
    Handler(u32),
    /// The driver's typed handler for the thrown kind (901-904).
    Top(u32),
}

/// One trace line's fields.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
struct TraceLine<'a> {
    name: &'a str,
    dynamic: bool,
    fields: std::collections::BTreeMap<&'a str, &'a str>,
    events: Vec<&'a str>,
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
impl<'a> TraceLine<'a> {
    fn parse(line: &'a str) -> Self {
        let (head, rest) = line
            .split_once(" ev=[")
            .unwrap_or_else(|| panic!("trace line without events: {line}"));
        let (events, tail) = rest
            .split_once("] ")
            .unwrap_or_else(|| panic!("trace line with unterminated events: {line}"));
        let mut words = head.split(' ');
        let full_name = words.next().expect("chain name");
        let (name, dynamic) = match full_name.strip_suffix("_dyn") {
            Some(name) => (name, true),
            None => (full_name, false),
        };
        let fields = words
            .chain(tail.split(' '))
            .map(|word| {
                word.split_once('=')
                    .unwrap_or_else(|| panic!("field without '=': {word} in {line}"))
            })
            .collect();
        let events = if events.is_empty() {
            vec![]
        } else {
            events.split(' ').collect()
        };
        Self {
            name,
            dynamic,
            fields,
            events,
        }
    }

    fn number(&self, key: &str) -> u32 {
        self.fields[key]
            .parse()
            .unwrap_or_else(|_| panic!("field {key}"))
    }

    fn hex(&self, key: &str) -> u32 {
        u32::from_str_radix(self.fields[key], 16).unwrap_or_else(|_| panic!("field {key}"))
    }

    fn decimal(&self, key: &str) -> i64 {
        self.fields[key]
            .parse()
            .unwrap_or_else(|_| panic!("field {key}"))
    }

    /// The `D<id><flag><0|1>` destructor events, in order, as (id, flag).
    fn destructors(&self, flag: char) -> Vec<(u32, u32)> {
        self.events
            .iter()
            .filter_map(|event| event.strip_prefix('D'))
            .map(|rest| {
                let (id, in_flight) = rest
                    .split_once(flag)
                    .unwrap_or_else(|| panic!("destructor event D{rest}"));
                (id.parse().unwrap(), in_flight.parse().unwrap())
            })
            .collect()
    }

    fn count(&self, prefix: char) -> usize {
        self.events
            .iter()
            .filter(|event| event.starts_with(prefix))
            .count()
    }
}

/// Leading decimal digits of `text`.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn leading_number(text: &str) -> u32 {
    let digits: String = text.chars().take_while(char::is_ascii_digit).collect();
    digits
        .parse()
        .unwrap_or_else(|_| panic!("no number in {text}"))
}

fn cxx_expected_catch(chain: CxxChain, kind: u32) -> Catch {
    if kind == 0 {
        return Catch::Returned;
    }
    let top = Catch::Top(900 + kind);
    let case_error = kind == 1 || kind == 2;
    match chain {
        CxxChain::CatchAll => Catch::Handler(21),
        CxxChain::CatchCase if case_error => Catch::Handler(31),
        CxxChain::CatchIntOrCase if kind == 3 => Catch::Handler(41),
        CxxChain::CatchIntOrCase if case_error => Catch::Handler(42),
        CxxChain::CatchCaseThenAll if case_error => Catch::Handler(51),
        CxxChain::CatchCaseThenAll => Catch::Handler(52),
        CxxChain::GuardCatchInt if kind == 3 => Catch::Handler(61),
        CxxChain::CatchOverPlain => Catch::Handler(101),
        CxxChain::DeepCatch => Catch::Handler(151),
        _ => top,
    }
}

/// The CG-frame guards a C++ case destroys, in destruction order.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn cxx_expected_guards(chain: CxxChain, kind: u32, at: u32) -> Vec<u32> {
    match chain {
        CxxChain::Cleanup => vec![1],
        CxxChain::GuardCatchInt => vec![6],
        CxxChain::TwoGuards if kind != 0 && at == 1 => vec![71],
        CxxChain::TwoGuards => vec![72, 71],
        CxxChain::NestedCleanup | CxxChain::DeepCatch => vec![1, 8],
        CxxChain::CxxMid => vec![1, 12],
        _ => vec![],
    }
}

/// Totals over a trace that satisfied the model.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[derive(Debug, Default, PartialEq, Eq)]
struct TraceStats {
    cases: usize,
    /// Destructor runs of CG-frame (or reference-frame) guards: every `D`
    /// event except the driver frame's guard 900.
    guard_destructors: usize,
    /// The subset that ran while an exception or panic was in flight: in a
    /// trust-cg build, destructors run by CG cleanup landing pads.
    unwinding_guard_destructors: usize,
    /// Cases whose exception a chain's own handler claimed.
    handler_catches: usize,
    /// Cases whose exception reached the driver's catch.
    top_catches: usize,
    /// Cases with no exception.
    returns: usize,
    /// Cases of the runtime-sized (`_dyn`) twins. In a linked AOT image
    /// their CG frames all defer to `__eh_frame` FDEs (DWARF fallback); in
    /// the JIT every frame, compact twins included, unwinds through its
    /// registered FDE, so there this counts runtime-sized frames only.
    runtime_sized_cases: usize,
}

/// Totals of the whole C++ chain matrix (every build of
/// `cxx_module(&CXX_CHAINS, ..)` and the C++ reference).
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
const CXX_MATRIX_STATS: TraceStats = TraceStats {
    cases: 632,
    guard_destructors: 432,
    unwinding_guard_destructors: 352,
    handler_catches: 176,
    top_catches: 336,
    returns: 120,
    runtime_sized_cases: 316,
};

/// Totals of the C++ matrix without the four typed chains (the JIT's).
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
const CXX_UNTYPED_MATRIX_STATS: TraceStats = TraceStats {
    cases: 472,
    guard_destructors: 392,
    unwinding_guard_destructors: 320,
    handler_catches: 96,
    top_catches: 288,
    returns: 88,
    runtime_sized_cases: 236,
};

/// Totals of the Rust matrix.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
const RUST_MATRIX_STATS: TraceStats = TraceStats {
    cases: 184,
    guard_destructors: 208,
    unwinding_guard_destructors: 144,
    handler_catches: 0,
    top_catches: 128,
    returns: 56,
    runtime_sized_cases: 92,
};

/// Check every line of a C++ trace against the model: catch site, return
/// value of a handled case, CG guard destructor ids, order and in-flight
/// count, the driver guard's in-flight count, the rethrow note, the nested
/// in-cleanup throw, and zero residual state. Returns the totals.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn check_cxx_model(lines: &[&str]) -> TraceStats {
    let mut stats = TraceStats::default();
    let (summary, cases) = lines.split_last().expect("a trace");
    for line in cases {
        let parsed = TraceLine::parse(line);
        let chain = CxxChain::from_name(parsed.name);
        let kind = parsed.number("k");
        let at = parsed.number("a");
        let expected = cxx_expected_catch(chain, kind);
        let site = parsed.number("site");
        let handler = parsed
            .events
            .iter()
            .find(|event| event.starts_with(['A', 'K', 'I']))
            .map(|event| leading_number(&event[1..]));
        let observed = match (site, handler) {
            (0, None) => Catch::Returned,
            (0, Some(handler)) => Catch::Handler(handler),
            (site, None) => Catch::Top(site),
            (site, Some(handler)) => panic!("{line}: caught at {site} and by handler {handler}"),
        };
        assert_eq!(observed, expected, "catch site: {line}");
        if let Catch::Handler(site) = expected {
            assert_eq!(
                parsed.hex("ret"),
                site * 1000 + kind,
                "a handled case returns its handler's value: {line}"
            );
        }
        let in_flight = u32::from(kind != 0);
        let mut destructors = parsed.destructors('u');
        let driver = destructors.pop().expect("the driver guard runs last");
        assert_eq!(
            driver,
            (900, u32::from(matches!(expected, Catch::Top(_)))),
            "driver guard: {line}"
        );
        let expected_guards: Vec<(u32, u32)> = cxx_expected_guards(chain, kind, at)
            .into_iter()
            .map(|id| (id, in_flight))
            .collect();
        assert_eq!(destructors, expected_guards, "CG guard destructors: {line}");
        assert_eq!(
            parsed.count('G'),
            destructors.len() + 1,
            "every constructed guard is destroyed exactly once: {line}"
        );
        assert_eq!(
            parsed.events.contains(&"N111u0"),
            chain == CxxChain::Rethrow && kind != 0,
            "the rethrowing handler runs exactly for a thrown case: {line}"
        );
        if chain == CxxChain::CleanupInnerThrow {
            let inner = format!("J13u{in_flight}v{in_flight}");
            assert!(
                parsed.events.contains(&inner.as_str()),
                "the in-cleanup throw sees the outer exception: {line}"
            );
        }
        for key in ["live", "guards", "unc", "cur"] {
            assert_eq!(parsed.decimal(key), 0, "residual {key}: {line}");
        }
        stats.cases += 1;
        stats.runtime_sized_cases += usize::from(parsed.dynamic);
        stats.guard_destructors += destructors.len();
        stats.unwinding_guard_destructors += destructors.iter().filter(|(_, u)| *u == 1).count();
        match expected {
            Catch::Returned => stats.returns += 1,
            Catch::Handler(_) => stats.handler_catches += 1,
            Catch::Top(_) => stats.top_catches += 1,
        }
    }
    assert_eq!(
        *summary,
        format!("cases={} errors=0", stats.cases),
        "trace summary"
    );
    stats
}

/// The same check for a Rust trace: `catch_unwind` result and payload
/// kind, guard drop ids, order and `panicking()` flag, the panic hook, the
/// Rust middle frame's catch and resume, and zero residual state.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn check_rust_model(lines: &[&str]) -> TraceStats {
    let mut stats = TraceStats::default();
    let (summary, cases) = lines.split_last().expect("a trace");
    for line in cases {
        let parsed = TraceLine::parse(line);
        let chain = RustChain::from_name(parsed.name);
        let kind = parsed.number("k");
        let at = parsed.number("a");
        assert_eq!(
            parsed.number("caught"),
            kind,
            "catch_unwind sees the kind's payload: {line}"
        );
        let in_flight = u32::from(kind != 0);
        let mut drops = parsed.destructors('p');
        let driver = drops.pop().expect("the driver guard drops last");
        assert_eq!(driver, (900, in_flight), "driver guard: {line}");
        let expected: Vec<(u32, u32)> = match chain {
            RustChain::Cleanup => vec![1],
            RustChain::Nested => vec![1, 4],
            RustChain::Through => vec![5],
            RustChain::TwoGuards if kind != 0 && at == 1 => vec![61],
            RustChain::TwoGuards => vec![62, 61],
            RustChain::RustMid => vec![1, 7],
            RustChain::EmptyCleanup | RustChain::Plain => vec![],
        }
        .into_iter()
        .map(|id| (id, in_flight))
        .collect();
        assert_eq!(drops, expected, "CG guard drops: {line}");
        assert_eq!(
            parsed.count('G'),
            drops.len() + 1,
            "every constructed guard is dropped exactly once: {line}"
        );
        assert_eq!(
            parsed.count('H'),
            usize::from(kind == 1),
            "the panic hook runs for panic_any only: {line}"
        );
        assert_eq!(
            parsed.events.contains(&"R0"),
            chain == RustChain::RustMid && kind != 0,
            "the Rust middle frame catches and resumes exactly a panic: {line}"
        );
        for key in ["live", "guards"] {
            assert_eq!(parsed.decimal(key), 0, "residual {key}: {line}");
        }
        assert_eq!(parsed.fields["panicking"], "0", "{line}");
        stats.cases += 1;
        stats.runtime_sized_cases += usize::from(parsed.dynamic);
        stats.guard_destructors += drops.len();
        stats.unwinding_guard_destructors += drops.iter().filter(|(_, p)| *p == 1).count();
        if kind == 0 {
            stats.returns += 1;
        } else {
            stats.top_catches += 1;
        }
    }
    assert_eq!(
        *summary,
        format!("cases={} errors=0", stats.cases),
        "trace summary"
    );
    stats
}

// ---------------------------------------------------------------------------
// The touch family's model (every host)
// ---------------------------------------------------------------------------

/// The Linux campaign's inputs (`UNWIND_DRIVER`): eight 64-bit edges, then
/// its LCG sequence, 64 per function twin.
const TOUCH_EDGES: [u64; 8] = [
    0,
    1,
    u64::MAX,
    0x8000_0000_0000_0000,
    0x7fff_ffff_ffff_ffff,
    0x1_0000_0000,
    255,
    256,
];
const TOUCH_INPUTS: usize = 64;

/// Totals of a touch trace.
#[derive(Debug, Default, PartialEq, Eq)]
struct TouchStats {
    cases: usize,
    /// Destructor runs of `touch_guarded`'s CG-slot guard.
    guard_destructors: usize,
    /// The subset its cleanup pad ran while the exception was in flight.
    unwinding_guard_destructors: usize,
    /// Cases whose exception `touch_catch`'s CG catch-all pad claimed.
    handler_catches: usize,
    /// Cases whose exception reached the driver's catch.
    top_catches: usize,
    /// Cases with no exception.
    returns: usize,
    /// Throws out of the provider call made through the function-pointer
    /// slot (`CallIndirect`).
    indirect_call_throws: usize,
    /// Cases of the runtime-sized (`_dyn`) twins.
    runtime_sized_cases: usize,
}

/// Totals of the whole touch matrix: 3 functions x 2 twins x 64 inputs x 3
/// stages.
const TOUCH_MATRIX_STATS: TouchStats = TouchStats {
    cases: 1152,
    guard_destructors: 384,
    unwinding_guard_destructors: 128,
    handler_catches: 256,
    top_catches: 512,
    returns: 384,
    indirect_call_throws: 384,
    runtime_sized_cases: 576,
};

/// The exact trace the touch matrix must print over `chains` (in table
/// order), computed as the Linux driver's `reference_provider` computes its
/// expectations: the input, the three memory words after the case, the
/// provider's calls and frame-guard destructor runs (`V<call>`,
/// `p<in flight>`), the return value or the payload and stage that reached
/// a catch, the CG guard's construction and destructor run, the CG
/// handler's entry and the exception object's destruction. Every residual
/// counter is zero.
fn touch_model(chains: &[TouchChain]) -> (Vec<String>, TouchStats) {
    const K: u64 = 0x0000_0100_0000_01b3;
    const C: u64 = 0x27d4_eb2d;
    const D: u64 = 0xdeca_fbad_1234_5678;
    let mut lines = Vec::new();
    let mut stats = TouchStats::default();
    for dynamic in [false, true] {
        for chain in TOUCH_CHAINS
            .into_iter()
            .filter(|chain| chains.contains(chain))
        {
            let guarded = chain == TouchChain::Guarded;
            let mut random: u64 = 0x3141_5926_5358_9793;
            for index in 0..TOUCH_INPUTS {
                random = random
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1);
                let x = TOUCH_EDGES.get(index).copied().unwrap_or(random);
                for stage in 0..3u32 {
                    let mut events = vec!["G900".to_string()];
                    if guarded {
                        events.push(format!("G{TOUCH_GUARD}"));
                    }
                    let w0 = random.wrapping_add(x);
                    let mut w1 = !random;
                    events.push("V1".into());
                    w1 = w1.wrapping_add(x.wrapping_mul(K).wrapping_add(C));
                    let (thrown, value) = if stage == 1 {
                        events.push("p1".into());
                        if guarded {
                            events.push(format!("D{TOUCH_GUARD}u1"));
                        }
                        (Some((x ^ w1 ^ D, 1)), 0)
                    } else {
                        let first = w1 ^ (x >> 7);
                        events.push("p0".into());
                        if guarded {
                            events.push(format!("D{TOUCH_GUARD}u0"));
                        }
                        events.push("V2".into());
                        w1 = w1.wrapping_add(first.wrapping_mul(K).wrapping_add(C));
                        if stage == 2 {
                            events.push("p1".into());
                            (Some((first ^ w1 ^ D, 2)), 0)
                        } else {
                            events.push("p0".into());
                            (None, w1 ^ (first >> 7))
                        }
                    };
                    let calls = if stage == 1 { 1 } else { 2 };
                    let (ret, site, payload, thrown_stage) = match thrown {
                        None => {
                            events.push("D900u0".into());
                            stats.returns += 1;
                            let add = if chain == TouchChain::Catch {
                                TOUCH_CATCH_ADD as u64
                            } else {
                                0
                            };
                            (value.wrapping_add(add), 0, 0, 0)
                        }
                        Some((payload, _)) if chain == TouchChain::Catch => {
                            events.push(format!("A{TOUCH_CATCH_SITE}k5p{:x}", payload as u32));
                            events.push("x5".into());
                            events.push("D900u0".into());
                            stats.handler_catches += 1;
                            (TOUCH_CATCH_SITE as u64 * 1000 + 5, 0, 0, 0)
                        }
                        Some((payload, at)) => {
                            events.push("D900u1".into());
                            events.push("x5".into());
                            stats.top_catches += 1;
                            (0, 905, payload, at)
                        }
                    };
                    lines.push(format!(
                        "{}{} s={stage} i={index} r={random:016x} x={x:016x} ret={ret:016x} \
                         site={site} pay={payload:016x} st={thrown_stage} w0={w0:016x} \
                         w1={w1:016x} w2={:016x} calls={calls} pd={calls} ev=[{}] live=0 \
                         guards=0 unc=0 cur=0",
                        chain.name(),
                        if dynamic { "_dyn" } else { "" },
                        0xfeed_face_cafe_beef_u64,
                        events.join(" ")
                    ));
                    stats.cases += 1;
                    stats.runtime_sized_cases += usize::from(dynamic);
                    stats.indirect_call_throws += usize::from(stage == 2);
                    if guarded {
                        stats.guard_destructors += 1;
                        stats.unwinding_guard_destructors += usize::from(stage == 1);
                    }
                }
            }
        }
    }
    lines.push(format!("cases={} errors=0", stats.cases));
    (lines, stats)
}

/// A touch trace must be exactly the model's, line for line.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn check_touch_model(what: &str, lines: &[&str], chains: &[TouchChain]) -> TouchStats {
    let (model, stats) = touch_model(chains);
    for (index, (got, want)) in lines.iter().zip(&model).enumerate() {
        assert_eq!(
            got, want,
            "{what}: touch case {index} differs from the model"
        );
    }
    assert_eq!(lines.len(), model.len(), "{what}: touch case count");
    stats
}

/// A C++ trace: the chain matrix and its summary line, then the touch
/// matrix and its summary line.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn split_cxx_trace(trace: &str) -> (Vec<&str>, Vec<&str>) {
    let lines: Vec<&str> = trace.lines().collect();
    let chains_end = lines
        .iter()
        .position(|line| line.starts_with("cases="))
        .unwrap_or_else(|| panic!("no chain summary in a {}-line trace", lines.len()));
    let (chains, touch) = lines.split_at(chains_end + 1);
    (chains.to_vec(), touch.to_vec())
}

/// Every case of `actual` must equal the reference's line for the same case.
/// `keep` selects the reference cases the implementation ran.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn assert_same_trace(what: &str, reference: &[&str], actual: &[&str], keep: impl Fn(&str) -> bool) {
    let (_, reference_cases) = reference.split_last().expect("reference trace");
    let expected: Vec<&str> = reference_cases
        .iter()
        .copied()
        .filter(|line| keep(line))
        .collect();
    let (summary, actual_cases) = actual
        .split_last()
        .unwrap_or_else(|| panic!("{what}: empty trace"));
    for (index, (want, got)) in expected.iter().zip(actual_cases).enumerate() {
        assert_eq!(
            got, want,
            "{what}: case {index} differs from the reference build"
        );
    }
    assert_eq!(
        actual_cases.len(),
        expected.len(),
        "{what}: case count (summary {summary})"
    );
    assert_eq!(
        *summary,
        format!("cases={} errors=0", expected.len()),
        "{what}: summary"
    );
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
fn is_untyped_cxx_case(line: &str) -> bool {
    !CxxChain::from_name(TraceLine::parse(line).name).typed()
}

/// The model's case count of a C++ table (both twins of each chain): five
/// kinds x four inputs, and the second throwing call of the two-guard chain.
fn cxx_case_count(chains: &[CxxChain]) -> usize {
    chains
        .iter()
        .map(|chain| {
            2 * (5 * 4
                + if *chain == CxxChain::TwoGuards {
                    4 * 4
                } else {
                    0
                })
        })
        .sum()
}

/// The same for the Rust table (three kinds).
fn rust_case_count() -> usize {
    RUST_CHAINS
        .iter()
        .map(|chain| {
            2 * (3 * 4
                + if *chain == RustChain::TwoGuards {
                    2 * 4
                } else {
                    0
                })
        })
        .sum()
}

#[test]
fn model_counts_match_the_matrix_denominators() {
    assert_eq!(cxx_case_count(&CXX_CHAINS), 632);
    assert_eq!(cxx_case_count(&untyped_cxx_chains()), 472);
    assert_eq!(rust_case_count(), 184);
    // The touch family: 3 functions x 2 twins x 64 inputs x 3 stages, the
    // eight 64-bit edges first for every twin.
    let (touch, stats) = touch_model(&TOUCH_CHAINS);
    assert_eq!(stats, TOUCH_MATRIX_STATS);
    assert_eq!(touch.len(), 2 * TOUCH_CHAINS.len() * TOUCH_INPUTS * 3 + 1);
    assert!(touch[0].starts_with("touch s=0 i=0 r=ec513f7c765391d8 x=0000000000000000 "));
    assert!(touch[2 * 3].contains(" i=2 ") && touch[2 * 3].contains(" x=ffffffffffffffff "));
    // The model's catch table covers every chain and kind with a single
    // disposition, and the four typed chains are exactly the ones whose
    // disposition depends on the thrown type below the catch-all.
    for chain in CXX_CHAINS {
        let dispositions: Vec<Catch> = (1..5).map(|kind| cxx_expected_catch(chain, kind)).collect();
        let all_top = dispositions
            .iter()
            .enumerate()
            .all(|(index, catch)| *catch == Catch::Top(901 + index as u32));
        let all_one_handler = dispositions.windows(2).all(|pair| pair[0] == pair[1])
            && matches!(dispositions[0], Catch::Handler(_));
        assert_eq!(
            chain.typed(),
            !all_top && !all_one_handler,
            "{chain:?}: {dispositions:?}"
        );
        assert_eq!(chain.typeinfo().is_empty(), !chain.typed(), "{chain:?}");
    }
}

// ---------------------------------------------------------------------------
// Exception-table obligations (ledger L03-P14), every host
// ---------------------------------------------------------------------------
//
// Every object above is emitted only after `trust_cg_verify::eh_obligations`
// decided the exception-table obligations over its bytes (the compiler's
// emission gate, `[TCG-EH-OBLIGATION]`): call-site coverage, landing pads,
// action tables, personality, LSDA binding, and the unwind description at
// every call against the frame the function's own words build. These rows
// capture those decisions, pin what held per object, and replay the decision
// on corrupted bytes (or a corrupted IR side), each of which must be refused
// by the obligation it breaks. Evidence strength: exact decisions made in
// process (testing grade), not a certificate; the native rows above execute
// the same gated objects.

/// A section header's file placement, read from the object independently of
/// the obligation checker.
struct SectionPlace {
    file_offset: usize,
    size: usize,
    reloff: usize,
    nreloc: usize,
    addr: u64,
}

fn le32(bytes: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().expect("four bytes"))
}

fn section_place(object: &[u8], segname: &str, sectname: &str) -> SectionPlace {
    let ncmds = le32(object, 16) as usize;
    let mut at = 32;
    for _ in 0..ncmds {
        let cmd = le32(object, at);
        let size = le32(object, at + 4) as usize;
        if cmd == 0x19 {
            let nsects = le32(object, at + 64) as usize;
            for index in 0..nsects {
                let base = at + 72 + index * 80;
                let name = |offset: usize| {
                    let raw = &object[base + offset..base + offset + 16];
                    let end = raw.iter().position(|&b| b == 0).unwrap_or(16);
                    String::from_utf8_lossy(&raw[..end]).into_owned()
                };
                if name(0) == sectname && name(16) == segname {
                    return SectionPlace {
                        addr: u64::from_le_bytes(object[base + 32..base + 40].try_into().unwrap()),
                        size: u64::from_le_bytes(object[base + 40..base + 48].try_into().unwrap())
                            as usize,
                        file_offset: le32(object, base + 48) as usize,
                        reloff: le32(object, base + 56) as usize,
                        nreloc: le32(object, base + 60) as usize,
                    };
                }
            }
        }
        at += size;
    }
    panic!("no {segname},{sectname}");
}

/// `(index, name, value)` of every symbol.
fn symbol_table(object: &[u8]) -> Vec<(u32, String, u64)> {
    let ncmds = le32(object, 16) as usize;
    let mut at = 32;
    for _ in 0..ncmds {
        if le32(object, at) == 0x2 {
            let (symoff, nsyms, stroff) = (
                le32(object, at + 8) as usize,
                le32(object, at + 12) as usize,
                le32(object, at + 16) as usize,
            );
            return (0..nsyms)
                .map(|index| {
                    let base = symoff + index * 16;
                    let strx = stroff + le32(object, base) as usize;
                    let end = object[strx..].iter().position(|&b| b == 0).unwrap();
                    let name = String::from_utf8_lossy(&object[strx..strx + end]).into_owned();
                    let value = u64::from_le_bytes(object[base + 8..base + 16].try_into().unwrap());
                    (index as u32, name, value)
                })
                .collect();
        }
        at += le32(object, at + 4) as usize;
    }
    panic!("no LC_SYMTAB");
}

fn symbol_index(object: &[u8], name: &str) -> u32 {
    symbol_table(object)
        .into_iter()
        .find(|(_, symbol, _)| symbol == name)
        .unwrap_or_else(|| panic!("no symbol {name}"))
        .0
}

fn symbol_value(object: &[u8], name: &str) -> u64 {
    symbol_table(object)
        .into_iter()
        .find(|(_, symbol, _)| symbol == name)
        .unwrap_or_else(|| panic!("no symbol {name}"))
        .2
}

/// `(file offset of the record, r_address, symbolnum, type)` of a section's
/// relocations.
fn relocation_records(object: &[u8], place: &SectionPlace) -> Vec<(usize, u32, u32, u32)> {
    (0..place.nreloc)
        .map(|index| {
            let at = place.reloff + index * 8;
            let info = le32(object, at + 4);
            (at, le32(object, at), info & 0x00ff_ffff, info >> 28)
        })
        .collect()
}

/// Point the relocation at `address` of `place` (of type `kind`) at symbol
/// `symbol` instead.
fn retarget_relocation(
    object: &mut [u8],
    place: &SectionPlace,
    address: u32,
    kind: u32,
    symbol: u32,
) {
    let (at, _, _, _) = relocation_records(object, place)
        .into_iter()
        .find(|&(_, r_address, _, r_kind)| r_address == address && r_kind == kind)
        .unwrap_or_else(|| panic!("no type-{kind} relocation at {address:#x}"));
    let info = le32(object, at + 4);
    object[at + 4..at + 8].copy_from_slice(&((info & 0xff00_0000) | symbol).to_le_bytes());
}

/// A ULEB128 field: file offset, width and value.
#[derive(Clone, Copy, Debug)]
struct Uleb {
    at: usize,
    width: usize,
    value: u64,
}

fn read_uleb(bytes: &[u8], at: usize) -> Uleb {
    let (mut value, mut shift, mut width) = (0u64, 0, 0);
    loop {
        let byte = bytes[at + width];
        value |= u64::from(byte & 0x7f) << shift;
        shift += 7;
        width += 1;
        if byte & 0x80 == 0 {
            return Uleb { at, width, value };
        }
    }
}

/// Rewrite `field` with `value`, padded to the field's width (a valid,
/// redundant ULEB128 spelling), so no other byte moves.
fn write_uleb(bytes: &mut [u8], field: Uleb, value: u64) {
    let mut rest = value;
    for i in 0..field.width {
        let mut byte = (rest & 0x7f) as u8;
        rest >>= 7;
        if i + 1 < field.width {
            byte |= 0x80;
        }
        bytes[field.at + i] = byte;
    }
    assert_eq!(
        rest, 0,
        "{value} does not fit a {}-byte ULEB128",
        field.width
    );
}

/// The call-site records `[start, length, landing pad, action]` of the
/// function's LSDA (symbol `_GCC_except_table_<function>`), as file fields.
fn lsda_records(object: &[u8], function: &str) -> Vec<[Uleb; 4]> {
    let table = section_place(object, "__TEXT", "__gcc_except_tab");
    let at = table.file_offset
        + (symbol_value(object, &format!("_GCC_except_table_{function}")) - table.addr) as usize;
    lsda_records_at(object, at)
}

/// The call-site records of the LSDA at byte `at` of `object`.
fn lsda_records_at(object: &[u8], at: usize) -> Vec<[Uleb; 4]> {
    assert_eq!(object[at], 0xff, "LPStart omitted");
    let mut position = at + 2;
    if object[at + 1] != 0xff {
        position = read_uleb(object, position).at + read_uleb(object, position).width;
    }
    assert_eq!(object[position], 0x01, "ULEB128 call-site encoding");
    let length = read_uleb(object, position + 1);
    let mut cursor = length.at + length.width;
    let end = cursor + length.value as usize;
    let mut records = Vec::new();
    while cursor < end {
        let mut fields = [Uleb {
            at: 0,
            width: 0,
            value: 0,
        }; 4];
        for field in &mut fields {
            *field = read_uleb(object, cursor);
            cursor += field.width;
        }
        records.push(fields);
    }
    records
}

/// A landing-pad value one instruction away that fits the field's width.
fn shifted_pad(field: Uleb) -> u64 {
    if field.value + 4 < 1 << (7 * field.width) {
        field.value + 4
    } else {
        field.value - 4
    }
}

/// Is `word` a `BL` or `BLR`?
fn is_call_word(word: u32) -> bool {
    word & 0xfc00_0000 == 0x9400_0000 || word & 0xffff_fc1f == 0xd63f_0000
}

/// The calls that can unwind in every function of `intent`, counted by this
/// file's own decoding of the instruction bodies (`code_of` returns a
/// function's bytes): every `BL`/`BLR` word minus the calls the IR declares
/// unable to unwind. With no unreached call, the gate's unwind points are
/// exactly these.
fn unwinding_call_words(
    intent: &trust_cg_verify::eh_obligations::EhObjectIntent,
    code_of: impl Fn(usize, &trust_cg_verify::eh_obligations::EhFunctionIntent) -> Vec<u8>,
) -> usize {
    intent
        .functions
        .iter()
        .enumerate()
        .map(|(index, function)| {
            let code = code_of(index, function);
            let calls = code[..function.body_len as usize]
                .as_chunks::<4>()
                .0
                .iter()
                .filter(|word| is_call_word(u32::from_le_bytes(**word)))
                .count();
            calls - function.nounwind_calls.len()
        })
        .sum()
}

/// The bytes of `function` in the Mach-O object `object`.
fn function_bytes(object: &[u8], function: &str, code_len: u32) -> Vec<u8> {
    let text = section_place(object, "__TEXT", "__text");
    let start =
        text.file_offset + (symbol_value(object, &format!("_{function}")) - text.addr) as usize;
    object[start..start + code_len as usize].to_vec()
}

/// Function offsets of the `BL`/`BLR` words of `function`.
fn call_offsets(object: &[u8], function: &str, code_len: u32) -> Vec<u64> {
    let text = section_place(object, "__TEXT", "__text");
    let start =
        text.file_offset + (symbol_value(object, &format!("_{function}")) - text.addr) as usize;
    (0..u64::from(code_len))
        .step_by(4)
        .filter(|&offset| is_call_word(le32(object, start + offset as usize)))
        .collect()
}

/// What the gate reports for every campaign object and JIT image, the same
/// at O0, O1, O2 and O3: `(route, module, report)`. Mach-O: one compact and
/// one DWARF-fallback twin per chain; the covered calls are the unwind
/// points minus the calls of the pad-free compact twins, which carry no
/// LSDA. JIT: an FDE per function, and every function's calls covered.
fn pinned_report(route: &str, module: &str) -> trust_cg_verify::eh_obligations::EhObligationReport {
    // (functions, with EH, unwind points, covered calls, invokes, landing
    // pads, compact frames, DWARF frames)
    let (functions, eh_functions, unwind_points, covered_calls, invokes, pads, compact, dwarf) =
        match (route, module) {
            ("macho", "cxx") => (36, 32, 212, 209, 36, 36, 18, 18),
            ("macho", "rust") => (14, 12, 75, 74, 14, 14, 7, 7),
            ("jit", "cxx") => (28, 24, 150, 150, 28, 28, 0, 28),
            ("jit", "rust") => (14, 12, 75, 75, 14, 14, 0, 14),
            other => panic!("no pinned report for {other:?}"),
        };
    trust_cg_verify::eh_obligations::EhObligationReport {
        functions,
        eh_functions,
        unwind_points,
        unreached_calls: 0,
        covered_calls,
        invokes,
        landing_pads: pads,
        compact_frames: compact,
        dwarf_frames: dwarf,
    }
}

fn function_intent<'a>(
    intent: &'a trust_cg_verify::eh_obligations::EhObjectIntent,
    name: &str,
) -> &'a trust_cg_verify::eh_obligations::EhFunctionIntent {
    intent
        .functions
        .iter()
        .find(|function| function.symbol == name)
        .unwrap_or_else(|| panic!("no intent for {name}"))
}

fn compile_captured(
    module: &Module,
    level: OptLevel,
) -> trust_cg_codegen::pipeline::EhObligationCapture {
    let (object, mut captured) =
        trust_cg_codegen::pipeline::capture_eh_obligations(|| compile_darwin(module, level));
    assert_eq!(captured.len(), 1, "{level:?}: one gated object per compile");
    let capture = captured.pop().expect("one capture");
    assert_eq!(capture.route, "macho");
    assert_eq!(
        capture.bytes, object,
        "{level:?}: the gate saw the emitted bytes"
    );
    capture
}

/// Every campaign object passes the gate at O0-O3, and the report counts
/// what held: one compact or DWARF description per twin, every pad's
/// landing pad and action chain, and the frame at every call. The report
/// is pinned exactly, and its unwind points are cross-checked against this
/// file's own count of the call words: a gate that stopped following the
/// exceptional edge into landing pads (their `_Unwind_Resume`, destructor
/// and `__cxa_begin_catch` calls) would report unreached calls and fewer
/// unwind points.
#[test]
fn eh_table_obligations_hold_for_every_campaign_object() {
    for (label, module, twins) in [
        (
            "cxx",
            cxx_module(&CXX_CHAINS, &TOUCH_CHAINS),
            cxx_twins(&CXX_CHAINS, &TOUCH_CHAINS),
        ),
        ("rust", rust_module(), rust_twins()),
    ] {
        for level in OPT_LEVELS {
            let capture = compile_captured(&module, level);
            let report = &capture.report;
            let with_pads = twins.iter().filter(|twin| twin.has_pad).count();
            assert_eq!(
                report.functions,
                twins.len(),
                "{label} {level:?}: {report:?}"
            );
            assert_eq!(
                report.eh_functions, with_pads,
                "{label} {level:?}: {report:?}"
            );
            assert_eq!(
                (report.compact_frames, report.dwarf_frames),
                (twins.len() / 2, twins.len() / 2),
                "{label} {level:?}: compact twins and DWARF-fallback twins"
            );
            assert!(
                report.invokes >= with_pads && report.landing_pads >= with_pads,
                "{label} {level:?}: {report:?}"
            );
            assert_eq!(
                report.unwind_points,
                unwinding_call_words(&capture.intent, |_, function| function_bytes(
                    &capture.bytes,
                    &function.symbol,
                    function.code_len
                )),
                "{label} {level:?}: every call that can unwind is an unwind point: {report:?}"
            );
            assert_eq!(*report, pinned_report("macho", label), "{label} {level:?}");
            // The decision is a function of the bytes and the intent.
            assert_eq!(
                capture.recheck(&capture.bytes, &capture.intent).as_ref(),
                Ok(report),
                "{label} {level:?}"
            );
            println!(
                "EH_OBLIGATIONS route=macho module={label} level={level:?} {}",
                report.summary()
            );
        }
    }
}

/// One corruption: what it changes and the obligation that must refuse it.
fn expect_refused(
    capture: &trust_cg_codegen::pipeline::EhObligationCapture,
    what: &str,
    object: &[u8],
    intent: &trust_cg_verify::eh_obligations::EhObjectIntent,
    expected: trust_cg_verify::eh_obligations::EhObligationKind,
    function: Option<&str>,
) {
    match capture.recheck(object, intent) {
        Ok(report) => panic!("{what}: accepted ({})", report.summary()),
        Err(violation) => {
            assert_eq!(violation.kind, expected, "{what}: {violation}");
            if let Some(function) = function {
                assert_eq!(
                    violation.function.as_deref(),
                    Some(function),
                    "{what}: {violation}"
                );
            }
            println!("EH_OBLIGATION_CONTROL refused {what}: {violation}");
        }
    }
}

/// The corruption controls: each mutated object (or IR side) breaks one
/// obligation and is refused by name. The C++ object at O0 and O2.
#[test]
fn eh_table_obligations_refuse_corrupted_objects() {
    use trust_cg_verify::eh_obligations::{EhObligationKind as Kind, EhReg};
    let module = cxx_module(&CXX_CHAINS, &TOUCH_CHAINS);
    let mut refused = 0;
    for level in [OptLevel::O0, OptLevel::O2] {
        let capture = compile_captured(&module, level);
        let original = &capture.bytes;
        let intent = &capture.intent;
        let compact = "tcg_two_guards";
        let dynamic = "tcg_two_guards_dyn";
        let compact_intent = function_intent(intent, compact);
        let records = lsda_records(original, compact);
        let calls = call_offsets(original, compact, compact_intent.code_len);
        let what = |name: &str| format!("{level:?} {name}");

        // 1. A call outside every record: shorten the record covering a
        //    call that is not an invoke so it stops right before the call.
        let invoke_calls: Vec<u64> = compact_intent
            .eh
            .as_ref()
            .expect("EH")
            .invokes
            .iter()
            .map(|invoke| u64::from(invoke.call_offset))
            .collect();
        let (record, call) = records
            .iter()
            .find_map(|record| {
                calls
                    .iter()
                    .find(|&&call| {
                        !invoke_calls.contains(&call)
                            && record[0].value < call
                            && call < record[0].value + record[1].value
                    })
                    .map(|&call| (*record, call))
            })
            .expect("a filler record covering a plain call");
        let mut object = original.clone();
        write_uleb(&mut object, record[1], call - record[0].value);
        expect_refused(
            &capture,
            &what("call outside every record"),
            &object,
            intent,
            Kind::CallSiteCoverage,
            Some(compact),
        );
        refused += 1;

        // 2. A wrong landing pad: the first invoke's record names the
        //    instruction after its landing block.
        let invoke = records
            .iter()
            .find(|record| record[2].value != 0)
            .expect("an invoke record");
        let mut object = original.clone();
        write_uleb(&mut object, invoke[2], shifted_pad(invoke[2]));
        expect_refused(
            &capture,
            &what("wrong landing pad"),
            &object,
            intent,
            Kind::LandingPad,
            Some(compact),
        );
        refused += 1;

        // 3. A wrong personality, compact entry: the personality relocation
        //    names `___cxa_begin_catch`.
        let unwind = section_place(original, "__LD", "__compact_unwind");
        let function_symbol = symbol_index(original, &format!("_{compact}"));
        let entry = relocation_records(original, &unwind)
            .into_iter()
            .find(|&(_, address, symbol, kind)| {
                address % 32 == 0 && symbol == function_symbol && kind == 0
            })
            .expect("the compact entry of the function")
            .1;
        let mut object = original.clone();
        retarget_relocation(
            &mut object,
            &unwind,
            entry + 16,
            0,
            symbol_index(original, "___cxa_begin_catch"),
        );
        expect_refused(
            &capture,
            &what("wrong compact personality"),
            &object,
            intent,
            Kind::Personality,
            Some(compact),
        );
        refused += 1;

        // 4. A wrong personality, DWARF fallback: the CIE's GOT-relocated
        //    personality names `___cxa_begin_catch`.
        let eh_frame = section_place(original, "__TEXT", "__eh_frame");
        let cie_personality = relocation_records(original, &eh_frame)
            .into_iter()
            .find(|&(_, _, _, kind)| kind == 7)
            .expect("the CIE personality relocation")
            .1;
        let mut object = original.clone();
        retarget_relocation(
            &mut object,
            &eh_frame,
            cie_personality,
            7,
            symbol_index(original, "___cxa_begin_catch"),
        );
        expect_refused(
            &capture,
            &what("wrong CIE personality"),
            &object,
            intent,
            Kind::Personality,
            None,
        );
        refused += 1;

        // 5. A CFA offset off by 16 in an FDE: `DW_CFA_def_cfa x29, 16` reads
        //    `x29, 32`.
        let start = eh_frame.file_offset;
        let def_cfa = (start..start + eh_frame.size - 2)
            .find(|&at| original[at..at + 3] == [0x0c, 0x1d, 0x10])
            .expect("DW_CFA_def_cfa x29, 16");
        let mut object = original.clone();
        object[def_cfa + 2] = 0x20;
        expect_refused(
            &capture,
            &what("FDE CFA offset off by 16"),
            &object,
            intent,
            Kind::FrameDescription,
            None,
        );
        refused += 1;

        // 6. The same error on the code side: the prologue's frame-pointer
        //    setup lands 16 bytes off, so FP + 16 is not the CFA the compact
        //    encoding promises at any call.
        let text = section_place(original, "__TEXT", "__text");
        let code = text.file_offset
            + (symbol_value(original, &format!("_{compact}")) - text.addr) as usize;
        let setup = (0..compact_intent.body_len as usize)
            .step_by(4)
            .find(|&offset| le32(original, code + offset) & 0xffc0_03ff == 0x9100_03fd)
            .expect("ADD X29, SP, #imm");
        let word = le32(original, code + setup);
        let mut object = original.clone();
        object[code + setup..code + setup + 4].copy_from_slice(&(word + (16 << 10)).to_le_bytes());
        expect_refused(
            &capture,
            &what("frame pointer set 16 bytes off"),
            &object,
            intent,
            Kind::UnwindPointFrame,
            Some(compact),
        );
        refused += 1;

        // 7. A missing callee-saved save rule and a compact encoding that
        //    disagrees with the prologue, on the first compact frame that
        //    saves X19/X20: clear the pair bit (refused against the frame
        //    owner), then also drop the pair from the frame owner's side
        //    (refused against the words: X19 changes before a call).
        let saver = intent
            .functions
            .iter()
            .find(|function| {
                !function.symbol.ends_with("_dyn")
                    && function
                        .frame
                        .saved
                        .iter()
                        .any(|(reg, _)| *reg == EhReg::X(19))
            })
            .expect("a compact frame saving X19");
        let saver_symbol = symbol_index(original, &format!("_{}", saver.symbol));
        let saver_entry = relocation_records(original, &unwind)
            .into_iter()
            .find(|&(_, address, symbol, kind)| {
                address % 32 == 0 && symbol == saver_symbol && kind == 0
            })
            .expect("the compact entry")
            .1 as usize;
        let encoding_at = unwind.file_offset + saver_entry + 12;
        let encoding = le32(original, encoding_at);
        assert_eq!(
            encoding & 0x0f00_0001,
            0x0400_0001,
            "FRAME mode with X19_X20"
        );
        let mut object = original.clone();
        object[encoding_at..encoding_at + 4].copy_from_slice(&(encoding & !1).to_le_bytes());
        expect_refused(
            &capture,
            &what("compact encoding drops X19/X20"),
            &object,
            intent,
            Kind::FrameDescription,
            Some(&saver.symbol),
        );
        let mut dropped = intent.clone();
        let frame = &mut dropped
            .functions
            .iter_mut()
            .find(|function| function.symbol == saver.symbol)
            .expect("saver")
            .frame;
        // The frame owner now agrees with the encoding: FP/LR, then the
        // remaining pairs from CFA-24 down in the compact encoding's order.
        let mut kept: Vec<EhReg> = frame
            .saved
            .iter()
            .map(|(reg, _)| *reg)
            .filter(|reg| !matches!(reg, EhReg::X(19 | 20 | 29 | 30)))
            .collect();
        kept.sort();
        frame.saved = vec![(EhReg::X(29), -16), (EhReg::X(30), -8)];
        frame.saved.extend(
            kept.into_iter()
                .enumerate()
                .map(|(i, reg)| (reg, -24 - 8 * i as i64)),
        );
        expect_refused(
            &capture,
            &what("X19/X20 save rule missing on both sides"),
            &object,
            &dropped,
            Kind::UnwindPointFrame,
            Some(&saver.symbol),
        );
        // The words disagree with an encoding the frame owner agrees with:
        // the prologue stores X21 where the encoding says X20 lives.
        let saver_code = text.file_offset
            + (symbol_value(original, &format!("_{}", saver.symbol)) - text.addr) as usize;
        let pair_store = (0..saver.body_len as usize)
            .step_by(4)
            .find(|&offset| {
                let word = le32(original, saver_code + offset);
                // STP X20, X19, [SP, #imm]! or [SP, #imm]
                word & 0xffc0_7fff == 0xa980_4ff4 || word & 0xffc0_7fff == 0xa900_4ff4
            })
            .expect("the X20/X19 pair store");
        let word = le32(original, saver_code + pair_store);
        let mut object = original.clone();
        object[saver_code + pair_store..saver_code + pair_store + 4]
            .copy_from_slice(&((word & !0x1f) | 21).to_le_bytes());
        expect_refused(
            &capture,
            &what("prologue stores X21 in X20's slot"),
            &object,
            intent,
            Kind::UnwindPointFrame,
            Some(&saver.symbol),
        );
        refused += 3;

        // 8. A typed catch bound to the wrong typeinfo: the `CaseError`
        //    slot's GOT relocation names `int`.
        let table = section_place(original, "__TEXT", "__gcc_except_tab");
        let case_error = symbol_index(original, "__ZTI9CaseError");
        let slot = relocation_records(original, &table)
            .into_iter()
            .find(|&(_, _, symbol, kind)| symbol == case_error && kind == 7)
            .expect("a CaseError slot")
            .1;
        let mut object = original.clone();
        retarget_relocation(
            &mut object,
            &table,
            slot,
            7,
            symbol_index(original, "__ZTIi"),
        );
        expect_refused(
            &capture,
            &what("CaseError slot names int"),
            &object,
            intent,
            Kind::ActionTable,
            None,
        );
        refused += 1;

        // 9. The IR side: the two invokes of the compact frame swap landing
        //    blocks, so the bytes no longer express the IR's binding.
        let mut swapped = intent.clone();
        let tables = swapped
            .functions
            .iter_mut()
            .find(|function| function.symbol == compact)
            .expect("compact")
            .eh
            .as_mut()
            .expect("EH");
        assert_eq!(tables.invokes.len(), 2, "two invokes");
        let first = tables.invokes[0].landing_block;
        tables.invokes[0].landing_block = tables.invokes[1].landing_block;
        tables.invokes[1].landing_block = first;
        expect_refused(
            &capture,
            &what("IR invokes swap landing blocks"),
            original,
            &swapped,
            Kind::LandingPad,
            Some(compact),
        );
        refused += 1;

        // 10. The LSDA pointer of the DWARF twin's FDE names the compact
        //     twin's table.
        let dynamic_lsda = symbol_index(original, &format!("_GCC_except_table_{dynamic}"));
        let fde_lsda = relocation_records(original, &eh_frame)
            .into_iter()
            .find(|&(_, _, symbol, kind)| symbol == dynamic_lsda && kind == 0)
            .expect("the FDE LSDA relocation")
            .1;
        let mut object = original.clone();
        retarget_relocation(
            &mut object,
            &eh_frame,
            fde_lsda,
            0,
            symbol_index(original, &format!("_GCC_except_table_{compact}")),
        );
        assert!(
            capture.recheck(&object, intent).is_err(),
            "{level:?}: a foreign LSDA must be refused"
        );
        println!(
            "EH_OBLIGATION_CONTROL refused {level:?} foreign LSDA: {}",
            capture.recheck(&object, intent).unwrap_err()
        );
        refused += 1;

        // 11. A frame with no pad still answers its personality: the
        //     DWARF-fallback twin of the plain chain carries a filler LSDA
        //     under the zPLR CIE; shortened so it stops before the frame's
        //     first call, that call is outside every record (the personality
        //     would stop the unwind there).
        let plain = "tcg_plain_mid_dyn";
        let plain_intent = function_intent(intent, plain);
        assert!(plain_intent.eh.is_none(), "a pad-free twin");
        let filler = lsda_records(original, plain);
        let first_call = call_offsets(original, plain, plain_intent.code_len)[0];
        assert_eq!(filler.len(), 1, "one filler record");
        assert_eq!((filler[0][0].value, filler[0][2].value), (0, 0));
        let mut object = original.clone();
        write_uleb(&mut object, filler[0][1], first_call);
        expect_refused(
            &capture,
            &what("filler LSDA stops before a call"),
            &object,
            intent,
            Kind::CallSiteCoverage,
            Some(plain),
        );
        refused += 1;

        // 12. The CIE's personality field keeps its GOT relocation but its
        //     encoding drops DW_EH_PE_indirect (0x9b -> 0x1b): an unwinder
        //     would call the GOT slot's own address.
        let encoding_at = eh_frame.file_offset + cie_personality as usize - 1;
        assert_eq!(
            original[encoding_at], 0x9b,
            "indirect|pcrel|sdata4 personality"
        );
        let mut object = original.clone();
        object[encoding_at] = 0x1b;
        expect_refused(
            &capture,
            &what("direct personality encoding over a GOT relocation"),
            &object,
            intent,
            Kind::CfiStructure,
            None,
        );
        refused += 1;

        // 13. The frame record is overwritten through a release, a SIMD
        //     structure and an exclusive store into [X29] (CFA-16) between
        //     the frame-pointer setup and the first call: the first
        //     non-branch word after the setup becomes the store.
        let first_call = calls
            .iter()
            .copied()
            .find(|&call| call > setup as u64)
            .expect("a call after the frame-pointer setup") as usize;
        let victim = (setup + 4..first_call)
            .step_by(4)
            .find(|&offset| (le32(original, code + offset) >> 26) & 0b111 != 0b101)
            .expect("a non-branch word between the setup and the first call");
        for (name, store) in [
            ("stlr xzr, [x29]", 0xc89f_ffbf_u32),
            ("st1 {v0.2d}, [x29]", 0x4c00_7fa0),
            ("stxr w0, xzr, [x29]", 0xc800_7fbf),
        ] {
            let mut object = original.clone();
            object[code + victim..code + victim + 4].copy_from_slice(&store.to_le_bytes());
            expect_refused(
                &capture,
                &what(&format!("frame record overwritten by {name}")),
                &object,
                intent,
                Kind::UnwindPointFrame,
                Some(compact),
            );
            refused += 1;
        }
    }
    assert_eq!(refused, 34, "seventeen controls at two levels");
}

/// The unchecked JIT's published images pass the same obligations before
/// they are mapped (untyped C++ chains and the Rust module, O0-O3), and a
/// corrupted image or IR side is refused by name.
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn eh_table_obligations_hold_and_refuse_corruption_in_jit_images() {
    use std::collections::HashMap;
    use trust_cg_verify::eh_obligations::EhObligationKind as Kind;

    extern "C" fn stub() {}
    let externs: HashMap<String, *const u8> = [
        "cxx_leaf",
        "tcg_guard_init",
        "tcg_guard_fini",
        "__cxa_begin_catch",
        "__cxa_end_catch",
        "__cxa_rethrow",
        "tcg_on_any",
        "tcg_on_case",
        "tcg_on_int",
        "tcg_note",
        "cxx_mid_frame",
        "tcg_inner_throw",
        "tcg_scratch",
        "tcg_provider",
        "tcg_words",
        "rs_leaf",
        "rs_guard_init",
        "rs_guard_drop",
        "rs_mid",
        "rs_scratch",
        CXX_PERSONALITY,
        RUST_PERSONALITY,
        "_Unwind_Resume",
    ]
    .into_iter()
    .map(|name| (name.to_owned(), stub as extern "C" fn() as *const u8))
    .collect();
    let chains = untyped_cxx_chains();
    let mut controls = 0;
    for (label, module) in [
        ("cxx", cxx_module(&chains, &TOUCH_CHAINS)),
        ("rust", rust_module()),
    ] {
        for level in OPT_LEVELS {
            let (result, mut captured) = trust_cg_codegen::pipeline::capture_eh_obligations(|| {
                Compiler::new(CompilerConfig {
                    opt_level: level,
                    parallel: false,
                    ..CompilerConfig::for_host_jit_unchecked()
                })
                .with_codegen_license(permit_unlicensed())
                .compile_module_to_jit(&module, &externs)
                .map(drop)
                .map_err(|error| error.to_string())
            });
            if let Err(error) = result {
                panic!("{label} {level:?}: {error}");
            }
            assert_eq!(captured.len(), 1, "{label} {level:?}: one gated image");
            let capture = captured.pop().expect("one capture");
            assert_eq!(capture.route, "jit");
            let report = &capture.report;
            let layout = capture.jit.as_ref().expect("JIT layout");
            assert_eq!(
                report.unwind_points,
                unwinding_call_words(&capture.intent, |index, function| {
                    let start = layout.functions[index].code_offset as usize;
                    capture.bytes[start..start + function.code_len as usize].to_vec()
                }),
                "{label} {level:?}: every call that can unwind is an unwind point: {report:?}"
            );
            assert_eq!(*report, pinned_report("jit", label), "{label} {level:?}");
            assert_eq!(
                capture.recheck(&capture.bytes, &capture.intent).as_ref(),
                Ok(report)
            );
            println!(
                "EH_OBLIGATIONS route=jit module={label} level={level:?} {}",
                report.summary()
            );
            if level != OptLevel::O0 && level != OptLevel::O2 {
                continue;
            }
            let what = |name: &str| format!("JIT {label} {level:?} {name}");
            let (eh_start, eh_len) = (layout.eh_frame.0 as usize, layout.eh_frame.1 as usize);

            // A CFA offset off by 16 in an FDE.
            let def_cfa = (eh_start..eh_start + eh_len - 2)
                .find(|&at| capture.bytes[at..at + 3] == [0x0c, 0x1d, 0x10])
                .expect("DW_CFA_def_cfa x29, 16");
            let mut image = capture.bytes.clone();
            image[def_cfa + 2] = 0x20;
            expect_refused(
                &capture,
                &what("FDE CFA offset off by 16"),
                &image,
                &capture.intent,
                Kind::FrameDescription,
                None,
            );

            // The personality slot holds another address: follow the CIE's
            // `P` field (pc-relative, indirect) to the slot.
            let mut at = eh_start + 9;
            while capture.bytes[at] != 0 {
                at += 1;
            }
            at += 1; // augmentation string terminator
            for _ in 0..4 {
                // code alignment, data alignment, return-address column and
                // augmentation length: one byte each in this CIE
                assert!(capture.bytes[at] & 0x80 == 0, "one-byte LEB128 fields");
                at += 1;
            }
            assert_eq!(capture.bytes[at], 0x9b, "indirect|pcrel|sdata4 personality");
            let field = at + 1;
            let delta = i32::from_le_bytes(capture.bytes[field..field + 4].try_into().unwrap());
            let slot = (field as i64 + i64::from(delta)) as usize;
            let (_, address) = layout.personalities[0].clone();
            assert_eq!(
                capture.bytes[slot..slot + 8],
                address.to_le_bytes(),
                "the slot holds the bound personality"
            );
            let mut image = capture.bytes.clone();
            image[slot..slot + 8].copy_from_slice(&(address + 4).to_le_bytes());
            expect_refused(
                &capture,
                &what("personality slot names another routine"),
                &image,
                &capture.intent,
                Kind::Personality,
                None,
            );

            // A wrong landing pad: the first EH function's first invoke
            // record names the next instruction. Its FDE's LSDA pointer is
            // the pc-relative field after the augmentation length.
            let (index, function) = capture
                .intent
                .functions
                .iter()
                .enumerate()
                .find(|(_, function)| function.eh.is_some())
                .expect("an EH function");
            let fde = layout.functions[index].fde_offset as usize;
            let field = fde + 17;
            let delta = i32::from_le_bytes(capture.bytes[field..field + 4].try_into().unwrap());
            let lsda = (field as i64 + i64::from(delta)) as usize;
            let records = lsda_records_at(&capture.bytes, lsda);
            let invoke = records
                .iter()
                .find(|record| record[2].value != 0)
                .expect("an invoke record");
            let mut image = capture.bytes.clone();
            write_uleb(&mut image, invoke[2], shifted_pad(invoke[2]));
            expect_refused(
                &capture,
                &what("wrong landing pad"),
                &image,
                &capture.intent,
                Kind::LandingPad,
                Some(&function.symbol),
            );
            controls += 3;
        }
    }
    assert_eq!(controls, 12, "three controls, two modules, two levels");
}

// ---------------------------------------------------------------------------
// JIT refusals (AArch64 macOS)
// ---------------------------------------------------------------------------

/// Each typed chain is refused by the unchecked in-memory JIT by name
/// (`JitUnwindTypedCatchUnsupported`, naming the function and the typeinfo
/// symbols its pads bind), before anything is published; the untyped
/// campaign module publishes (the native JIT rows run it), and a proof-grade
/// JIT request for it is refused by name (`JitUnwindProofEvidenceUnavailable`).
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn jit_refuses_every_typed_chain_and_proof_grade_eh_by_name() {
    use std::collections::HashMap;
    use trust_cg_codegen::compiler::{CompileError, JitValidationMode};
    use trust_cg_codegen::jit::JitError;

    extern "C" fn stub() {}
    let externs: HashMap<String, *const u8> = [
        "cxx_leaf",
        "tcg_guard_init",
        "tcg_guard_fini",
        "__cxa_begin_catch",
        "__cxa_end_catch",
        "__cxa_rethrow",
        "tcg_on_any",
        "tcg_on_case",
        "tcg_on_int",
        "tcg_note",
        "cxx_mid_frame",
        "tcg_inner_throw",
        "tcg_scratch",
        CXX_PERSONALITY,
        "_Unwind_Resume",
    ]
    .into_iter()
    .map(|name| (name.to_owned(), stub as extern "C" fn() as *const u8))
    .collect();
    let mut refused = Vec::new();
    for chain in CXX_CHAINS.into_iter().filter(|chain| chain.typed()) {
        let module = cxx_module(&[chain], &[]);
        for level in [OptLevel::O0, OptLevel::O2] {
            let error = Compiler::new(CompilerConfig {
                opt_level: level,
                parallel: false,
                ..CompilerConfig::for_host_jit_unchecked()
            })
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &externs)
            .err()
            .unwrap_or_else(|| panic!("{chain:?} {level:?}: a typed catch must not publish"));
            match error {
                CompileError::Jit(JitError::JitUnwindTypedCatchUnsupported {
                    function,
                    mut typeinfo_symbols,
                }) => {
                    assert_eq!(function, cxx_symbol(chain, false), "{level:?}");
                    typeinfo_symbols.sort();
                    typeinfo_symbols.dedup();
                    let mut expected = chain.typeinfo();
                    expected.sort();
                    assert_eq!(typeinfo_symbols, expected, "{chain:?} {level:?}");
                }
                other => panic!("{chain:?} {level:?}: expected the named refusal, got {other}"),
            }
        }
        refused.push(chain.name());
    }
    assert_eq!(
        refused,
        [
            "catch_case",
            "catch_int_or_case",
            "catch_case_then_all",
            "guard_catch_int"
        ]
    );
    let untyped = cxx_module(&untyped_cxx_chains(), &[]);
    let result = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        parallel: false,
        jit_validation_mode_override: Some(JitValidationMode::AlwaysVerify),
        ..CompilerConfig::for_host_jit()
    })
    .with_codegen_license(permit_unlicensed())
    .compile_module_to_jit(&untyped, &externs);
    match result {
        Err(CompileError::Jit(JitError::JitUnwindProofEvidenceUnavailable { function })) => {
            assert!(function.starts_with("tcg_"), "{function}");
        }
        Err(other) => panic!("expected the proof-grade EH refusal, got {other}"),
        Ok(_) => panic!("proof-grade JIT publication of EH frames must be refused"),
    }
}

// ---------------------------------------------------------------------------
// Native campaign (AArch64 macOS)
// ---------------------------------------------------------------------------

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
mod common;

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[path = "fixtures/eh_raii_darwin/rust_arm.rs"]
mod rust_arm;

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
mod native {
    use super::*;

    use std::collections::HashMap;
    use std::ffi::{CStr, CString, c_char, c_int, c_void};
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::sync::{Mutex, MutexGuard, OnceLock};
    use std::time::Duration;

    use trust_cg_codegen::compiler::JitCompilationResult;
    use trust_cg_codegen::jit_unwind::registered_unwind_fde_for_pc;

    /// JIT publications register their tables with the process unwinder;
    /// keep one campaign publishing at a time.
    static SERIAL: Mutex<()> = Mutex::new(());

    fn serial() -> MutexGuard<'static, ()> {
        SERIAL
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    fn fixture_dir() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/eh_raii_darwin")
    }

    /// A fresh directory of this process's own, removed when the test ends,
    /// passed or failed. A failing test keeps its sources, objects and
    /// binaries only when `TRUST_CG_KEEP_TEST_OBJECTS` is set.
    fn work_dir(name: &str) -> crate::fresh_dir::ScratchDir {
        crate::fresh_dir::create(&format!("trust-cg-eh-raii-{name}-"))
    }

    fn run_tool(command: &mut Command, what: &str) {
        let result = common::rosetta::command_output_with_timeout(
            command,
            common::rosetta::codegen_link_timeout(),
        )
        .unwrap_or_else(|error| panic!("{what}: {error}"));
        assert!(
            !result.timed_out && result.output.status.success(),
            "{what} failed:\n{}\n{}",
            String::from_utf8_lossy(&result.output.stdout),
            String::from_utf8_lossy(&result.output.stderr)
        );
    }

    /// Run a campaign executable; returns whether it exited 0 and its trace.
    /// A timeout or a signal (134 = `std::terminate`/abort) fails here.
    fn run_trace_status(binary: &Path, what: &str) -> (bool, String) {
        let result = common::rosetta::command_output_with_timeout(
            &mut Command::new(binary),
            common::rosetta::exec_timeout(Duration::from_secs(60)),
        )
        .unwrap_or_else(|error| panic!("{what}: {error}"));
        let stdout = String::from_utf8_lossy(&result.output.stdout).into_owned();
        // The drivers write each line as soon as its case has run, so a
        // crash leaves every earlier case behind.
        let mut last: Vec<&str> = stdout.lines().rev().take(3).collect();
        last.reverse();
        assert!(
            !result.timed_out && matches!(result.output.status.code(), Some(0 | 1)),
            "{what}: exit {:?} (134 = std::terminate/abort; None = a signal) after {} trace \
             lines; a crashing case is the one after the last line\nstderr: {}\nlast lines:\n{}",
            result.output.status.code(),
            stdout.lines().count(),
            String::from_utf8_lossy(&result.output.stderr),
            last.join("\n")
        );
        (result.output.status.success(), stdout)
    }

    /// Run a campaign executable that must exit 0; returns its trace.
    fn run_trace(binary: &Path, what: &str) -> String {
        let (success, stdout) = run_trace_status(binary, what);
        assert!(success, "{what}: the driver reported integrity errors");
        stdout
    }

    fn tool_stdout(command: &mut Command, what: &str) -> String {
        let result = common::rosetta::command_output_with_timeout(
            command,
            common::rosetta::codegen_link_timeout(),
        )
        .unwrap_or_else(|error| panic!("{what}: {error}"));
        assert!(
            !result.timed_out && result.output.status.success(),
            "{what} failed: {}",
            String::from_utf8_lossy(&result.output.stderr)
        );
        String::from_utf8(result.output.stdout).expect("tool output is UTF-8")
    }

    /// `UNWIND_HAS_LSDA` in a linked `__unwind_info` encoding.
    const UNWIND_HAS_LSDA: u32 = 0x4000_0000;

    /// Read the linked image's (executable's or dylib's) `__unwind_info`
    /// back with Apple's `objdump` and its symbols with `nm`: every `NAME`
    /// twin keeps a FRAME-mode encoding (with an LSDA iff it has a pad) and
    /// every `NAME_dyn` twin a DWARF-mode encoding naming a nonzero
    /// `__eh_frame` FDE offset, so the unwinder reached the runtime-sized
    /// frames through their FDEs.
    fn check_linked_unwind_info(binary: &Path, twins: &[Twin], what: &str) {
        let symbols = tool_stdout(
            Command::new("/usr/bin/nm").arg("-n").arg(binary),
            &format!("{what}: nm"),
        );
        let mut addresses = HashMap::new();
        for line in symbols.lines() {
            let mut fields = line.split_whitespace();
            if let (Some(address), Some(_), Some(name)) =
                (fields.next(), fields.next(), fields.next())
                && let Ok(address) = u64::from_str_radix(address, 16)
            {
                addresses.insert(name.to_owned(), address);
            }
        }
        // `__unwind_info` function offsets are relative to the image base,
        // the `__TEXT` segment's address (0x100000000 for an executable, 0
        // for a dylib).
        let load_commands = tool_stdout(
            Command::new("/usr/bin/otool").arg("-l").arg(binary),
            &format!("{what}: otool -l"),
        );
        let base = load_commands
            .split("segname __TEXT")
            .nth(1)
            .and_then(|rest| rest.split_once("vmaddr 0x"))
            .and_then(|(_, rest)| rest.split_whitespace().next())
            .and_then(|address| u64::from_str_radix(address, 16).ok())
            .unwrap_or_else(|| panic!("{what}: no __TEXT segment address"));
        let unwind_info = tool_stdout(
            Command::new("/usr/bin/objdump")
                .args(["--macho", "--unwind-info"])
                .arg(binary),
            &format!("{what}: objdump --unwind-info"),
        );
        // Second-level entries, from compressed pages (`encoding[k]=0x...`)
        // or regular pages (`encoding=0x...`).
        let mut encodings = HashMap::new();
        for line in unwind_info.lines() {
            let Some((_, rest)) = line.split_once("function offset=0x") else {
                continue;
            };
            let Some((offset, rest)) = rest.split_once(", encoding") else {
                continue;
            };
            let (_, encoding) = rest.rsplit_once("=0x").expect("encoding value");
            encodings.insert(
                u64::from_str_radix(offset, 16).expect("function offset"),
                u32::from_str_radix(encoding.trim(), 16).expect("encoding"),
            );
        }
        for twin in twins {
            let address = addresses[&format!("_{}", twin.symbol)];
            let encoding = *encodings
                .get(&(address - base))
                .unwrap_or_else(|| panic!("{what}: no __unwind_info entry for {}", twin.symbol));
            let mode = encoding & UNWIND_ARM64_MODE_MASK;
            if twin.dynamic {
                assert_eq!(mode, UNWIND_ARM64_MODE_DWARF, "{what}: {}", twin.symbol);
                assert_ne!(
                    encoding & 0x00ff_ffff,
                    0,
                    "{what}: {} FDE offset",
                    twin.symbol
                );
                assert_ne!(
                    encoding & UNWIND_HAS_LSDA,
                    0,
                    "{what}: {} LSDA",
                    twin.symbol
                );
            } else {
                assert_eq!(mode, UNWIND_ARM64_MODE_FRAME, "{what}: {}", twin.symbol);
                assert_eq!(
                    encoding & UNWIND_HAS_LSDA != 0,
                    twin.has_pad,
                    "{what}: {} LSDA",
                    twin.symbol
                );
            }
        }
    }

    // -----------------------------------------------------------------------
    // Mutated trust-cg frames (negative controls)
    // -----------------------------------------------------------------------

    fn function_mut<'m>(module: &'m mut Module, name: &str) -> &'m mut Function {
        module
            .functions
            .iter_mut()
            .find(|function| function.name == name)
            .unwrap_or_else(|| panic!("no function {name}"))
    }

    fn block_mut(function: &mut Function, id: u32) -> &mut Block {
        let name = function.name.clone();
        function
            .blocks
            .iter_mut()
            .find(|block| block.id == b(id))
            .unwrap_or_else(|| panic!("{name} has no block {id}"))
    }

    /// Both twins of `chain`'s cleanup pad (block 2) stop calling `callee`
    /// (the guard destructor): the frame leaks its guard when it unwinds.
    fn drop_pad_destructor(module: &mut Module, symbol: &str, callee: u32) {
        for name in [symbol.to_owned(), format!("{symbol}_dyn")] {
            let pad = block_mut(function_mut(module, &name), 2);
            let before = pad.body.len();
            pad.body.retain(
                |node| !matches!(&node.inst, Inst::Call { callee: c, .. } if *c == f(callee)),
            );
            assert_eq!(
                pad.body.len() + 1,
                before,
                "{name}: one destructor call removed"
            );
        }
    }

    /// Both twins of the two-guard chain bind each invoke to the other's
    /// landing pad (the first call's exception runs the second guard's
    /// destructor on storage no guard occupies).
    fn swap_two_guard_pads(module: &mut Module, symbol: &str) {
        for name in [symbol.to_owned(), format!("{symbol}_dyn")] {
            let function = function_mut(module, &name);
            let mut swapped = 0;
            for block in &mut function.blocks {
                for node in &mut block.body {
                    if let Inst::Invoke { unwind_dest, .. } = &mut node.inst {
                        *unwind_dest = if *unwind_dest == b(3) { b(4) } else { b(3) };
                        swapped += 1;
                    }
                }
            }
            assert_eq!(swapped, 2, "{name}: both invokes retargeted");
        }
    }

    /// Both twins of `catch_case` bind their typed pad to `int` (catch type
    /// index 2) instead of `CaseError`, with a handler that classifies
    /// whatever it claims.
    fn bind_catch_case_to_int(module: &mut Module) {
        let symbol = cxx_symbol(CxxChain::CatchCase, false);
        for name in [symbol.clone(), format!("{symbol}_dyn")] {
            let function = function_mut(module, &name);
            let pad = block_mut(function, 2);
            for node in &mut pad.body {
                match &mut node.inst {
                    Inst::LandingPad {
                        catch_type_indices, ..
                    } => *catch_type_indices = vec![INT],
                    Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(value),
                    } if *value == i128::from(CASE_ERROR) => *value = i128::from(INT),
                    _ => {}
                }
            }
            let handler = block_mut(function, 20);
            for node in &mut handler.body {
                if let Inst::Call { callee, args } = &mut node.inst
                    && *callee == f(7)
                {
                    *callee = f(6);
                    args.truncate(1);
                }
            }
        }
    }

    /// Indices of the cases whose lines differ between two traces of the
    /// same matrix (both complete).
    fn differing_cases(reference: &[&str], actual: &[&str], what: &str) -> Vec<usize> {
        assert_eq!(
            reference.len(),
            actual.len(),
            "{what}: the mutated build must still run every case"
        );
        let cases = reference.len() - 1;
        (0..cases)
            .filter(|&index| reference[index] != actual[index])
            .collect()
    }

    /// Both twins of `touch` lose their store to `tcg_words[0]` (the load
    /// and add stay): the memory effect the trace checks after every case.
    fn drop_touch_store(module: &mut Module) {
        for dynamic in [false, true] {
            let name = touch_symbol(TouchChain::Touch, dynamic);
            let entry = block_mut(function_mut(module, &name), 0);
            let before = entry.body.len();
            entry
                .body
                .retain(|node| !matches!(node.inst, Inst::Store { .. }));
            assert_eq!(entry.body.len() + 1, before, "{name}: one store removed");
        }
    }

    fn cxx_command() -> Command {
        let mut command = Command::new("c++");
        command.args(["-std=c++17", "-O1", "-Wall", "-Werror", "-I"]);
        command.arg(fixture_dir());
        command
    }

    /// The C++ fixture objects shared by every C++ build.
    struct CxxObjects {
        main: PathBuf,
        driver: PathBuf,
        helpers: PathBuf,
    }

    impl CxxObjects {
        fn all(&self) -> [&PathBuf; 3] {
            [&self.main, &self.driver, &self.helpers]
        }
    }

    fn compile_cxx(dir: &Path, source: &str) -> PathBuf {
        let object = dir.join(source.replace(".cpp", ".o"));
        run_tool(
            cxx_command()
                .arg("-c")
                .arg(fixture_dir().join(source))
                .arg("-o")
                .arg(&object),
            &format!("compile {source}"),
        );
        object
    }

    fn cxx_objects(dir: &Path) -> CxxObjects {
        CxxObjects {
            main: compile_cxx(dir, "main.cpp"),
            driver: compile_cxx(dir, "driver.cpp"),
            helpers: compile_cxx(dir, "helpers.cpp"),
        }
    }

    /// The C++ driver and helpers as a dylib of their own: the typeinfo, the
    /// thrower, the guards, the provider and `tcg_words` that a CG dylib
    /// imports (the Linux campaign's separate provider library).
    fn cxx_provider_dylib(dir: &Path, driver: &Path, helpers: &Path) -> PathBuf {
        let library = dir.join("libtcg_eh_raii_cxx.dylib");
        run_tool(
            Command::new("c++")
                .arg("-shared")
                .arg(driver)
                .arg(helpers)
                .arg("-o")
                .arg(&library),
            "link the C++ provider dylib",
        );
        library
    }

    /// The C++-only reference trace: its chain part checked against the
    /// chain model, its touch part equal to the touch model.
    fn cxx_reference_trace(dir: &Path, objects: &CxxObjects) -> String {
        let reference = compile_cxx(dir, "reference.cpp");
        let binary = dir.join("cxx_reference");
        run_tool(
            Command::new("c++")
                .args(objects.all())
                .arg(&reference)
                .arg("-o")
                .arg(&binary),
            "link the C++ reference",
        );
        let trace = run_trace(&binary, "C++ reference");
        let (chains, touch) = split_cxx_trace(&trace);
        assert_eq!(check_cxx_model(&chains), CXX_MATRIX_STATS);
        assert_eq!(
            check_touch_model("C++ reference", &touch, &TOUCH_CHAINS),
            TOUCH_MATRIX_STATS
        );
        trace
    }

    /// `nm`'s symbol table of a linked image: each symbol's type letter.
    fn symbol_types(binary: &Path, what: &str) -> HashMap<String, String> {
        tool_stdout(
            Command::new("/usr/bin/nm").arg(binary),
            &format!("{what}: nm"),
        )
        .lines()
        .filter_map(|line| {
            let mut fields = line.split_whitespace().rev();
            let name = fields.next()?;
            let kind = fields.next()?;
            Some((name.to_owned(), kind.to_owned()))
        })
        .collect()
    }

    /// The CG-dylib arm's boundary: the CG dylib defines every twin and
    /// imports the helpers, the provider, the memory words and the typeinfo;
    /// the executable imports every twin.
    fn check_cg_dylib_boundary(cg_dylib: &Path, binary: &Path, twins: &[Twin], what: &str) {
        let library = symbol_types(cg_dylib, what);
        let executable = symbol_types(binary, what);
        for twin in twins {
            let name = format!("_{}", twin.symbol);
            assert_eq!(
                library.get(&name).map(String::as_str),
                Some("T"),
                "{what}: {name}"
            );
            assert_eq!(
                executable.get(&name).map(String::as_str),
                Some("U"),
                "{what}: {name}"
            );
        }
        for import in [
            "_cxx_leaf",
            "_tcg_guard_init",
            "_tcg_provider",
            "_tcg_words",
            "__ZTI9CaseError",
            "__ZTIi",
        ] {
            assert_eq!(
                library.get(import).map(String::as_str),
                Some("U"),
                "{what}: {import}"
            );
        }
    }

    /// Both parts of a trust-cg build's trace equal the reference's (and so
    /// the models); returns the number of cases.
    fn check_cxx_build(what: &str, reference: &str, trace: &str) -> usize {
        let (reference_chains, reference_touch) = split_cxx_trace(reference);
        let (chains, touch) = split_cxx_trace(trace);
        assert_same_trace(what, &reference_chains, &chains, |_| true);
        assert_eq!(check_cxx_model(&chains), CXX_MATRIX_STATS, "{what}");
        assert_same_trace(what, &reference_touch, &touch, |_| true);
        assert_eq!(
            check_touch_model(what, &touch, &TOUCH_CHAINS),
            TOUCH_MATRIX_STATS
        );
        CXX_MATRIX_STATS.cases + TOUCH_MATRIX_STATS.cases
    }

    /// C++ throwers and catchers through trust-cg frames, AOT at O0-O3,
    /// against the C++-only reference build and the models. Each level's
    /// object is linked into the executable and, separately, into a CG
    /// dylib of its own that imports everything it names from the C++
    /// provider dylib (the executable holds only `main`).
    #[test]
    fn cxx_campaign_aot_matches_the_cxx_reference_at_o0_to_o3() {
        let dir = work_dir("cxx_aot");
        let objects = cxx_objects(&dir);
        let reference = cxx_reference_trace(&dir, &objects);
        println!("EH_RAII_CXX_REFERENCE chains {CXX_MATRIX_STATS:?} touch {TOUCH_MATRIX_STATS:?}");
        let provider = cxx_provider_dylib(&dir, &objects.driver, &objects.helpers);
        let module = cxx_module(&CXX_CHAINS, &TOUCH_CHAINS);
        let twins = cxx_twins(&CXX_CHAINS, &TOUCH_CHAINS);
        let mut cases = 0;
        for level in OPT_LEVELS {
            let object = dir.join(format!("cg_{level:?}.o"));
            std::fs::write(&object, compile_darwin(&module, level)).expect("write object");

            let binary = dir.join(format!("cxx_cg_{level:?}"));
            run_tool(
                Command::new("c++")
                    .args(objects.all())
                    .arg(&object)
                    .arg("-o")
                    .arg(&binary),
                &format!("{level:?}: link the trust-cg object"),
            );
            check_linked_unwind_info(&binary, &twins, &format!("{level:?}"));
            let trace = run_trace(&binary, &format!("{level:?}: C++ campaign"));
            let ran = check_cxx_build(&format!("AOT {level:?}"), &reference, &trace);
            cases += ran;
            println!("EH_RAII_CXX_AOT {level:?} executable cases={ran}");

            let cg_dylib = dir.join(format!("libtcg_cg_{level:?}.dylib"));
            run_tool(
                Command::new("c++")
                    .arg("-shared")
                    .arg(&object)
                    .arg(&provider)
                    .arg("-o")
                    .arg(&cg_dylib),
                &format!("{level:?}: link the trust-cg object into a dylib"),
            );
            check_linked_unwind_info(&cg_dylib, &twins, &format!("{level:?} CG dylib"));
            let binary = dir.join(format!("cxx_cg_dylib_{level:?}"));
            run_tool(
                Command::new("c++")
                    .arg(&objects.main)
                    .arg(&cg_dylib)
                    .arg(&provider)
                    .arg("-o")
                    .arg(&binary),
                &format!("{level:?}: link main against the CG and provider dylibs"),
            );
            check_cg_dylib_boundary(&cg_dylib, &binary, &twins, &format!("{level:?} CG dylib"));
            let trace = run_trace(
                &binary,
                &format!("{level:?}: C++ campaign through a CG dylib"),
            );
            let ran = check_cxx_build(&format!("AOT {level:?} CG dylib"), &reference, &trace);
            cases += ran;
            println!("EH_RAII_CXX_AOT {level:?} cg_dylib cases={ran}");
        }
        assert_eq!(cases, 2 * 4 * (632 + 1152));
        let _ = std::fs::remove_dir_all(&dir);
    }

    type Mutation = fn(&mut Module);

    /// Which cases a mutation reaches: chain cases by chain and kind, or
    /// touch cases by their parsed line.
    enum Reach {
        Chains(fn(CxxChain, u32) -> bool),
        Touch(fn(&TraceLine<'_>) -> bool),
    }

    /// Negative controls: five mutated C++ modules, each at O0-O3, must
    /// differ from the reference in exactly the cases the mutation reaches
    /// (and in no other, in either matrix), so the comparison and the models
    /// are sensitive to a leaked destructor, a landing pad bound to the wrong
    /// call site, a typed catch bound to the wrong typeinfo, a leaked guard
    /// in the touch family's pad and a lost memory store.
    #[test]
    fn cxx_campaign_detects_mutated_cg_frames() {
        let dir = work_dir("cxx_mutants");
        let objects = cxx_objects(&dir);
        let reference = cxx_reference_trace(&dir, &objects);
        let (reference_chains, reference_touch) = split_cxx_trace(&reference);
        let mutants: [(&str, Mutation, Reach); 5] = [
            (
                "cleanup pad skips its guard destructor",
                |module| drop_pad_destructor(module, "tcg_cleanup", 2),
                Reach::Chains(|chain, kind| {
                    kind != 0
                        && matches!(
                            chain,
                            CxxChain::Cleanup
                                | CxxChain::NestedCleanup
                                | CxxChain::CxxMid
                                | CxxChain::DeepCatch
                        )
                }),
            ),
            (
                "two-guard invokes bound to each other's pad",
                |module| swap_two_guard_pads(module, "tcg_two_guards"),
                Reach::Chains(|chain, kind| kind != 0 && chain == CxxChain::TwoGuards),
            ),
            (
                "typed pad bound to int instead of CaseError",
                bind_catch_case_to_int,
                Reach::Chains(|chain, kind| {
                    chain == CxxChain::CatchCase && (1..=3).contains(&kind)
                }),
            ),
            (
                "touch_guarded's cleanup pad skips its guard destructor",
                |module| drop_pad_destructor(module, "tcg_touch_guarded", 2),
                Reach::Touch(|line| line.name == "touch_guarded" && line.number("s") == 1),
            ),
            (
                "touch loses its store to tcg_words[0]",
                drop_touch_store,
                // `touch_catch` calls `touch`; an input of zero leaves the
                // word unchanged either way.
                Reach::Touch(|line| {
                    matches!(line.name, "touch" | "touch_catch")
                        && line.fields["x"] != "0000000000000000"
                }),
            ),
        ];
        let reached = |lines: &[&str], reach: &dyn Fn(&TraceLine<'_>) -> bool| -> Vec<usize> {
            lines[..lines.len() - 1]
                .iter()
                .enumerate()
                .filter(|(_, line)| reach(&TraceLine::parse(line)))
                .map(|(index, _)| index)
                .collect()
        };
        let mut runs = 0;
        for (what, mutate, reach) in mutants {
            let (expected_chains, expected_touch) = match reach {
                Reach::Chains(reach) => (
                    reached(&reference_chains, &|line| {
                        reach(CxxChain::from_name(line.name), line.number("k"))
                    }),
                    vec![],
                ),
                Reach::Touch(reach) => (vec![], reached(&reference_touch, &reach)),
            };
            let expected = expected_chains.len() + expected_touch.len();
            assert!(expected > 0, "{what}: the mutation reaches some case");
            let mut module = cxx_module(&CXX_CHAINS, &TOUCH_CHAINS);
            mutate(&mut module);
            for level in OPT_LEVELS {
                let object = dir.join(format!("mutant_{runs}.o"));
                std::fs::write(&object, compile_darwin(&module, level)).expect("write object");
                let binary = dir.join(format!("mutant_{runs}"));
                run_tool(
                    Command::new("c++")
                        .args(objects.all())
                        .arg(&object)
                        .arg("-o")
                        .arg(&binary),
                    &format!("{what} {level:?}: link"),
                );
                let (_, trace) = run_trace_status(&binary, &format!("{what} {level:?}"));
                let (chains, touch) = split_cxx_trace(&trace);
                assert_eq!(
                    differing_cases(&reference_chains, &chains, what),
                    expected_chains,
                    "{what} {level:?}: exactly the reached chain cases differ from the reference"
                );
                assert_eq!(
                    differing_cases(&reference_touch, &touch, what),
                    expected_touch,
                    "{what} {level:?}: exactly the reached touch cases differ from the reference"
                );
                runs += 1;
                println!(
                    "EH_RAII_CXX_MUTANT {level:?} {what}: {expected} of {} cases differ",
                    reference_chains.len() + reference_touch.len() - 2
                );
            }
        }
        assert_eq!(runs, 20);
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The installed Trust package's `trustc` (or `$RUSTC`) in its explicit
    /// unverified lane. trustc refuses to run under any TRUST_CG_*/TCG_*
    /// control, which a gate may export to this test, so they are removed.
    fn rustc() -> Command {
        let mut command = Command::new(
            std::env::var_os("RUSTC")
                .map(PathBuf::from)
                .unwrap_or_else(|| PathBuf::from("trustc")),
        );
        for (key, _) in std::env::vars_os() {
            let key_text = key.to_string_lossy();
            if key_text.starts_with("TRUST_CG_") || key_text.starts_with("TCG_") {
                command.env_remove(&key);
            }
        }
        command.args([
            "-Ztrust-verify=off",
            "--edition",
            "2024",
            "-C",
            "panic=unwind",
            "-O",
        ]);
        command.arg(fixture_dir().join("rust_main.rs"));
        command
    }

    /// Rust panics through trust-cg frames under `rust_eh_personality`, AOT
    /// at O0-O3, against the Rust-only reference build and the model.
    #[test]
    fn rust_campaign_aot_matches_the_rust_reference_at_o0_to_o3() {
        let dir = work_dir("rust_aot");
        let reference_binary = dir.join("rust_reference");
        run_tool(
            rustc()
                .args(["--cfg", "reference", "-o"])
                .arg(&reference_binary),
            "build the Rust reference",
        );
        let reference = run_trace(&reference_binary, "Rust reference");
        let reference: Vec<&str> = reference.lines().collect();
        let stats = check_rust_model(&reference);
        assert_eq!(stats, RUST_MATRIX_STATS);
        println!("EH_RAII_RUST_REFERENCE {stats:?}");
        let module = rust_module();
        let mut cases = 0;
        for level in OPT_LEVELS {
            let object = dir.join(format!("cg_{level:?}.o"));
            std::fs::write(&object, compile_darwin(&module, level)).expect("write object");
            let binary = dir.join(format!("rust_cg_{level:?}"));
            run_tool(
                rustc()
                    .arg("-o")
                    .arg(&binary)
                    .arg(format!("-Clink-arg={}", object.display())),
                &format!("{level:?}: link the trust-cg object with trustc"),
            );
            check_linked_unwind_info(&binary, &rust_twins(), &format!("{level:?}"));
            let trace = run_trace(&binary, &format!("{level:?}: Rust campaign"));
            let trace: Vec<&str> = trace.lines().collect();
            assert_same_trace(&format!("AOT {level:?}"), &reference, &trace, |_| true);
            assert_eq!(check_rust_model(&trace), stats, "{level:?}");
            cases += stats.cases;
            println!("EH_RAII_RUST_AOT {level:?} cases={} {stats:?}", stats.cases);
        }
        assert_eq!(cases, 4 * 184);

        // Negative control: a cleanup pad that skips its guard's drop glue
        // must differ from the reference in exactly the panicking cases that
        // cross it (and in no other), at O0-O3.
        let mut module = rust_module();
        drop_pad_destructor(&mut module, "tcgr_cleanup", 2);
        let expected: Vec<usize> = reference[..reference.len() - 1]
            .iter()
            .enumerate()
            .filter(|(_, line)| {
                let parsed = TraceLine::parse(line);
                parsed.number("k") != 0
                    && matches!(
                        RustChain::from_name(parsed.name),
                        RustChain::Cleanup | RustChain::Nested | RustChain::RustMid
                    )
            })
            .map(|(index, _)| index)
            .collect();
        assert_eq!(expected.len(), 48);
        for level in OPT_LEVELS {
            let object = dir.join(format!("mutant_{level:?}.o"));
            std::fs::write(&object, compile_darwin(&module, level)).expect("write object");
            let binary = dir.join(format!("rust_mutant_{level:?}"));
            run_tool(
                rustc()
                    .arg("-o")
                    .arg(&binary)
                    .arg(format!("-Clink-arg={}", object.display())),
                &format!("{level:?}: link the mutated object with trustc"),
            );
            let (_, trace) = run_trace_status(&binary, &format!("{level:?}: Rust mutant"));
            let trace: Vec<&str> = trace.lines().collect();
            assert_eq!(
                differing_cases(&reference, &trace, "Rust mutant"),
                expected,
                "{level:?}: exactly the panics crossing the mutated pad differ"
            );
            println!(
                "EH_RAII_RUST_MUTANT {level:?}: {} of {} cases differ",
                expected.len(),
                reference.len() - 1
            );
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    // -----------------------------------------------------------------------
    // JIT
    // -----------------------------------------------------------------------

    unsafe extern "C" {
        fn dlopen(path: *const c_char, mode: c_int) -> *mut c_void;
        fn dlsym(handle: *mut c_void, symbol: *const c_char) -> *mut c_void;
        fn dlerror() -> *const c_char;
        fn rust_eh_personality();
    }

    const RTLD_NOW: c_int = 2;
    const RTLD_GLOBAL: c_int = 0x8;

    /// The C++ helpers and driver as a dylib, loaded once per process and
    /// never unloaded, so their code outlives every JIT publication. Its
    /// work directory is removed once it is loaded: the mapping stays valid.
    struct CxxLibrary {
        handle: usize,
    }

    impl CxxLibrary {
        fn symbol(&self, name: &str) -> *const u8 {
            let name_c = CString::new(name).unwrap();
            // SAFETY: `handle` is a live dlopen handle; the lookup also
            // searches the library's dependencies (libc++abi).
            let address = unsafe { dlsym(self.handle as *mut c_void, name_c.as_ptr()) };
            assert!(
                !address.is_null(),
                "the C++ campaign library lacks `{name}`"
            );
            address as *const u8
        }
    }

    fn cxx_library() -> &'static CxxLibrary {
        static LIBRARY: OnceLock<CxxLibrary> = OnceLock::new();
        LIBRARY.get_or_init(|| {
            let dir = work_dir("cxx_jit_library");
            let library = cxx_provider_dylib(
                &dir,
                &compile_cxx(&dir, "driver.cpp"),
                &compile_cxx(&dir, "helpers.cpp"),
            );
            let path = CString::new(library.to_str().unwrap()).unwrap();
            // SAFETY: loading a library this test just built; it stays loaded.
            let handle = unsafe { dlopen(path.as_ptr(), RTLD_NOW | RTLD_GLOBAL) };
            if handle.is_null() {
                // SAFETY: dlerror returns a NUL-terminated message after a failure.
                let message = unsafe { CStr::from_ptr(dlerror()) }.to_string_lossy();
                panic!("dlopen {library:?}: {message}");
            }
            // The loaded image no longer needs its file.
            let _ = std::fs::remove_dir_all(&dir);
            CxxLibrary {
                handle: handle as usize,
            }
        })
    }

    fn jit_compiler(level: OptLevel) -> Compiler {
        Compiler::new(CompilerConfig {
            opt_level: level,
            parallel: false,
            ..CompilerConfig::for_host_jit_unchecked()
        })
        .with_codegen_license(permit_unlicensed())
    }

    fn jit_pointer(result: &JitCompilationResult, name: &str) -> *const u8 {
        result
            .buffer
            .get_fn_ptr_bound(name)
            .unwrap_or_else(|| panic!("missing JIT symbol {name}"))
            .as_ptr()
    }

    /// The published tables name `personality` once, every twin has a
    /// frame-pointer FDE the process unwinder returns for its entry PC, and
    /// exactly the pad-free twins carry a no-handler filler LSDA.
    fn check_jit_tables(
        result: &JitCompilationResult,
        twins: &[Twin],
        personality: &str,
        level: OptLevel,
    ) {
        let manifest = result
            .buffer
            .unwind_tables()
            .expect("EH module publishes unwind tables");
        assert_eq!(
            manifest.personality.as_ref().map(|p| p.symbol.as_str()),
            Some(personality),
            "{level:?}"
        );
        assert!(result.buffer.unwind_tables_registered(), "{level:?}");
        let base = result.buffer.code_slice().as_ptr() as u64;
        for twin in twins {
            let record = manifest
                .function(&twin.symbol)
                .unwrap_or_else(|| panic!("{level:?}: {} has no FDE", twin.symbol));
            assert!(record.frame_pointer, "{level:?}: {}", twin.symbol);
            assert_eq!(
                record.lsda_is_filler, !twin.has_pad,
                "{level:?}: {} LSDA",
                twin.symbol
            );
            assert_eq!(
                registered_unwind_fde_for_pc(base + record.code_offset).expect("FDE lookup"),
                Some(base + record.fde_offset),
                "{level:?}: the unwinder returns {}'s registered FDE",
                twin.symbol
            );
        }
    }

    type RunMatrix = unsafe extern "C" fn(*const *const u8, *const c_char) -> c_int;

    /// Run the driver's two matrices over one JIT publication: the chain
    /// table (null for every chain the module does not define, which the
    /// driver skips) and the whole touch table. Returns both traces.
    fn run_cxx_jit_matrices(
        library: &CxxLibrary,
        result: &JitCompilationResult,
        chains: &[CxxChain],
        dir: &Path,
        tag: &str,
    ) -> (String, String) {
        // SAFETY: both functions have this C signature (common.h).
        let run_matrix: RunMatrix =
            unsafe { std::mem::transmute(library.symbol("tcg_run_matrix")) };
        // SAFETY: as above.
        let run_touch: RunMatrix = unsafe { std::mem::transmute(library.symbol("tcg_run_touch")) };
        let mut table = vec![std::ptr::null::<u8>(); 2 * CXX_CHAINS.len()];
        for dynamic in [false, true] {
            for &chain in chains {
                let slot = usize::from(dynamic) * CXX_CHAINS.len() + chain.index();
                table[slot] = jit_pointer(result, &cxx_symbol(chain, dynamic));
            }
        }
        let touch_table: Vec<*const u8> = [false, true]
            .into_iter()
            .flat_map(|dynamic| {
                TOUCH_CHAINS.map(|chain| jit_pointer(result, &touch_symbol(chain, dynamic)))
            })
            .collect();
        let out = dir.join(format!("jit_{tag}.txt"));
        let touch_out = dir.join(format!("jit_{tag}_touch.txt"));
        let out_c = CString::new(out.to_str().unwrap()).unwrap();
        let touch_out_c = CString::new(touch_out.to_str().unwrap()).unwrap();
        trust_cg_codegen::jit::ensure_jit_execute_mode();
        // SAFETY: the tables hold JIT entry points with the chain and touch
        // signatures (or null); `result` keeps them, their data image and
        // their registered unwind tables alive across both calls.
        let ran = unsafe { run_matrix(table.as_ptr(), out_c.as_ptr()) };
        assert_eq!(ran as usize, cxx_case_count(chains), "{tag}: chain cases");
        // SAFETY: as above.
        let ran = unsafe { run_touch(touch_table.as_ptr(), touch_out_c.as_ptr()) };
        assert_eq!(ran as usize, TOUCH_MATRIX_STATS.cases, "{tag}: touch cases");
        (
            std::fs::read_to_string(&out).expect("read the JIT chain trace"),
            std::fs::read_to_string(&touch_out).expect("read the JIT touch trace"),
        )
    }

    /// C++ throwers and catchers through trust-cg frames published by the
    /// unchecked in-memory JIT at O0-O3 (every untyped chain and the whole
    /// touch family, whose memory words and function-pointer slot the JIT
    /// data image places and relocates), against the C++-only reference
    /// build. The typed chains are refused by name
    /// (`jit_refuses_every_typed_chain_and_proof_grade_eh_by_name`), so the
    /// table holds null for them and the driver skips them.
    #[test]
    fn cxx_campaign_jit_matches_the_cxx_reference_at_o0_to_o3() {
        let _guard = serial();
        let dir = work_dir("cxx_jit");
        let objects = cxx_objects(&dir);
        let reference = cxx_reference_trace(&dir, &objects);
        let (reference_chains, reference_touch) = split_cxx_trace(&reference);
        let library = cxx_library();
        let mut externs: HashMap<String, *const u8> = HashMap::new();
        for name in [
            "cxx_leaf",
            "tcg_guard_init",
            "tcg_guard_fini",
            "__cxa_begin_catch",
            "__cxa_end_catch",
            "__cxa_rethrow",
            "tcg_on_any",
            "tcg_on_case",
            "tcg_on_int",
            "tcg_note",
            "cxx_mid_frame",
            "tcg_inner_throw",
            "tcg_scratch",
            "tcg_provider",
            "tcg_words",
            CXX_PERSONALITY,
            "_Unwind_Resume",
        ] {
            externs.insert(name.to_owned(), library.symbol(name));
        }
        let chains = untyped_cxx_chains();
        let module = cxx_module(&chains, &TOUCH_CHAINS);
        let twins = cxx_twins(&chains, &TOUCH_CHAINS);
        let mut cases = 0;
        for level in OPT_LEVELS {
            let result = jit_compiler(level)
                .compile_module_to_jit(&module, &externs)
                .unwrap_or_else(|error| panic!("{level:?}: {error}"));
            check_jit_tables(&result, &twins, CXX_PERSONALITY, level);
            // The two pointer slots are placed and relocated in the JIT data
            // image; `tcg_words` is an import bound through a GOT slot.
            let image = result
                .buffer
                .data_image()
                .expect("the touch family's data image");
            assert_eq!(
                (image.import_count, image.relocation_count),
                (1, 2),
                "{level:?}: {image:?}"
            );
            let tag = format!("{level:?}");
            let (trace, touch) = run_cxx_jit_matrices(library, &result, &chains, &dir, &tag);
            let trace: Vec<&str> = trace.lines().collect();
            assert_same_trace(
                &format!("JIT {level:?}"),
                &reference_chains,
                &trace,
                is_untyped_cxx_case,
            );
            let stats = check_cxx_model(&trace);
            assert_eq!(stats, CXX_UNTYPED_MATRIX_STATS, "{level:?}");
            let touch: Vec<&str> = touch.lines().collect();
            assert_same_trace(
                &format!("JIT {level:?} touch"),
                &reference_touch,
                &touch,
                |_| true,
            );
            let touch_stats = check_touch_model(&format!("JIT {level:?}"), &touch, &TOUCH_CHAINS);
            assert_eq!(touch_stats, TOUCH_MATRIX_STATS, "{level:?}");
            cases += stats.cases + touch_stats.cases;
            println!(
                "EH_RAII_CXX_JIT {level:?} cases={} chains {stats:?} touch {touch_stats:?}",
                stats.cases + touch_stats.cases
            );
            drop(result);
        }
        assert_eq!(cases, 4 * (472 + 1152));

        // Negative control: the published cleanup pad that skips its guard
        // destructor differs from the reference in exactly the thrown chain
        // cases that cross it, and in no touch case.
        let untyped_reference: Vec<&str> = reference_chains
            .iter()
            .copied()
            .filter(|line| line.starts_with("cases=") || is_untyped_cxx_case(line))
            .collect();
        let expected: Vec<usize> = untyped_reference[..untyped_reference.len() - 1]
            .iter()
            .enumerate()
            .filter(|(_, line)| {
                let parsed = TraceLine::parse(line);
                parsed.number("k") != 0
                    && matches!(
                        CxxChain::from_name(parsed.name),
                        CxxChain::Cleanup
                            | CxxChain::NestedCleanup
                            | CxxChain::CxxMid
                            | CxxChain::DeepCatch
                    )
            })
            .map(|(index, _)| index)
            .collect();
        assert_eq!(expected.len(), 128);
        let mut mutant = module;
        drop_pad_destructor(&mut mutant, "tcg_cleanup", 2);
        for level in [OptLevel::O0, OptLevel::O2] {
            let result = jit_compiler(level)
                .compile_module_to_jit(&mutant, &externs)
                .unwrap_or_else(|error| panic!("mutant {level:?}: {error}"));
            let tag = format!("mutant_{level:?}");
            let (trace, touch) = run_cxx_jit_matrices(library, &result, &chains, &dir, &tag);
            let trace: Vec<&str> = trace.lines().collect();
            assert_eq!(
                differing_cases(&untyped_reference, &trace, "JIT mutant"),
                expected,
                "{level:?}: exactly the throws crossing the mutated pad differ"
            );
            let touch: Vec<&str> = touch.lines().collect();
            assert_eq!(
                differing_cases(&reference_touch, &touch, "JIT mutant touch"),
                Vec::<usize>::new(),
                "{level:?}: the mutation reaches no touch case"
            );
            println!(
                "EH_RAII_CXX_JIT_MUTANT {level:?}: {} of {} cases differ",
                expected.len(),
                untyped_reference.len() - 1 + reference_touch.len() - 1
            );
            drop(result);
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    fn address<T: Copy>(function: T) -> *const u8 {
        assert_eq!(std::mem::size_of::<T>(), std::mem::size_of::<*const u8>());
        // SAFETY: `T` is a function-pointer type of pointer size.
        unsafe { std::mem::transmute_copy::<T, *const u8>(&function) }
    }

    /// Rust panics through trust-cg frames published by the unchecked
    /// in-memory JIT at O0-O3 under `rust_eh_personality`, in this process,
    /// against the Rust-only reference run on the same thread.
    #[test]
    fn rust_campaign_jit_matches_the_rust_reference_at_o0_to_o3() {
        let _guard = serial();
        rust_arm::install_quiet_hook();
        let reference = rust_arm::run_matrix(&rust_arm::reference_table(), |_| {});
        let reference: Vec<&str> = reference.iter().map(String::as_str).collect();
        let stats = check_rust_model(&reference);
        assert_eq!(stats, RUST_MATRIX_STATS);
        let externs: HashMap<String, *const u8> = HashMap::from([
            (
                "rs_leaf".to_owned(),
                address(rust_arm::rs_leaf as extern "C-unwind" fn(u32) -> u32),
            ),
            (
                "rs_guard_init".to_owned(),
                address(
                    rust_arm::rs_guard_init as unsafe extern "C" fn(*mut rust_arm::RsGuard, u32),
                ),
            ),
            (
                "rs_guard_drop".to_owned(),
                address(rust_arm::rs_guard_drop as unsafe extern "C" fn(*mut rust_arm::RsGuard)),
            ),
            (
                "rs_mid".to_owned(),
                address(rust_arm::rs_mid as extern "C-unwind" fn(u32) -> u32),
            ),
            (
                "rs_scratch".to_owned(),
                address(rust_arm::rs_scratch as unsafe extern "C" fn(*mut u8, u64)),
            ),
            (
                RUST_PERSONALITY.to_owned(),
                address(rust_eh_personality as unsafe extern "C" fn()),
            ),
        ]);
        let module = rust_module();
        let mut cases = 0;
        for level in OPT_LEVELS {
            let result = jit_compiler(level)
                .compile_module_to_jit(&module, &externs)
                .unwrap_or_else(|error| panic!("{level:?}: {error}"));
            check_jit_tables(&result, &rust_twins(), RUST_PERSONALITY, level);
            let table: rust_arm::Table = std::array::from_fn(|slot| {
                let dynamic = slot >= RUST_CHAINS.len();
                let chain = RUST_CHAINS[slot % RUST_CHAINS.len()];
                let pointer = jit_pointer(&result, &rust_symbol(chain, dynamic));
                // SAFETY: every chain has the `(u32) -> u32` C-unwind
                // signature; `result` outlives the matrix run below.
                unsafe { std::mem::transmute::<*const u8, rust_arm::ChainFn>(pointer) }
            });
            trust_cg_codegen::jit::ensure_jit_execute_mode();
            let trace = rust_arm::run_matrix(&table, |_| {});
            let trace: Vec<&str> = trace.iter().map(String::as_str).collect();
            assert_same_trace(&format!("JIT {level:?}"), &reference, &trace, |_| true);
            assert_eq!(check_rust_model(&trace), stats, "{level:?}");
            cases += stats.cases;
            println!("EH_RAII_RUST_JIT {level:?} cases={} {stats:?}", stats.cases);
            drop(result);
        }
        assert_eq!(cases, 4 * 184);

        // Negative control: a published cleanup pad that skips its guard's
        // drop glue differs in exactly the panics that cross it.
        let expected: Vec<usize> = reference[..reference.len() - 1]
            .iter()
            .enumerate()
            .filter(|(_, line)| {
                let parsed = TraceLine::parse(line);
                parsed.number("k") != 0
                    && matches!(
                        RustChain::from_name(parsed.name),
                        RustChain::Cleanup | RustChain::Nested | RustChain::RustMid
                    )
            })
            .map(|(index, _)| index)
            .collect();
        assert_eq!(expected.len(), 48);
        let mut mutant = module;
        drop_pad_destructor(&mut mutant, "tcgr_cleanup", 2);
        for level in [OptLevel::O0, OptLevel::O2] {
            let result = jit_compiler(level)
                .compile_module_to_jit(&mutant, &externs)
                .unwrap_or_else(|error| panic!("mutant {level:?}: {error}"));
            let table: rust_arm::Table = std::array::from_fn(|slot| {
                let dynamic = slot >= RUST_CHAINS.len();
                let chain = RUST_CHAINS[slot % RUST_CHAINS.len()];
                let pointer = jit_pointer(&result, &rust_symbol(chain, dynamic));
                // SAFETY: as above.
                unsafe { std::mem::transmute::<*const u8, rust_arm::ChainFn>(pointer) }
            });
            trust_cg_codegen::jit::ensure_jit_execute_mode();
            let trace = rust_arm::run_matrix(&table, |_| {});
            let trace: Vec<&str> = trace.iter().map(String::as_str).collect();
            assert_eq!(
                differing_cases(&reference, &trace, "Rust JIT mutant"),
                expected,
                "{level:?}: exactly the panics crossing the mutated pad differ"
            );
            println!(
                "EH_RAII_RUST_JIT_MUTANT {level:?}: {} of {} cases differ",
                expected.len(),
                reference.len() - 1
            );
            drop(result);
        }
    }
}

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
