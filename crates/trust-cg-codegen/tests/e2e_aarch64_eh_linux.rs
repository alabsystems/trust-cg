// E2E: CG-owned landing pads, cleanup and unwind on AArch64 Linux GNU.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Ledger gap L03-P2. Two trust-ir modules are compiled for
// `aarch64-unknown-linux-gnu` at O0-O3:
//
// * the C++ module (personality `__gxx_personality_v0`): a catch-all pad that
//   reads the payload through `__cxa_begin_catch` (`tc_catch`), a cleanup pad
//   that resumes (`tc_cleanup`), a catch-all around that cleanup frame
//   (`tc_nested`), a plain frame with no handler (`tc_mid`), a catch-all
//   around the plain frame (`tc_through`), a catch-all whose invoke follows
//   another call in the same trust-ir block (`tc_merged`), and one whose invoke
//   follows a plain call that itself throws on odd input (`tc_early`);
// * the Rust module (declaring `rust_eh_personality` selects the Rust
//   personality): cleanup pads that resume a real Rust panic (`tr_cleanup`,
//   `tr_nested`, `tr_through`, `tr_merged`, whose invoke follows another call
//   in its block, and `tr_early`, whose earlier plain call panics on odd input)
//   and a plain frame (`tr_mid`).
//
// Host-neutral rows read every emitted object with this file's own ELF,
// `.eh_frame` and LSDA decoders (not the compiler's emitters or decoders) and
// check that each invoke's call site is covered by its landing pad with the
// right action, that every other call continues unwinding, that the CIE
// personality goes through the `DW.ref.<personality>` slot, and that every
// `BL _Unwind_Resume` is followed by `BRK #1` (a resume never falls through).
// They also pin the named refusal of EH metadata without a personality, that
// the adapter moves an invoke that follows another call into a block of its
// own (exception metadata admits one call per protected block), which calls
// before an invoke it sees (trust-ir calls, `frem`, i128 <-> float casts), and
// exact Invoke identity when instruction selection adds other calls in the
// same block (i128 division and remainder, an aggregate copy). The separate
// legacy block-only resolver control still refuses an unbound second call.
//
// Linux GNU rows link the objects with libstdc++/libgcc_s (`g++`) or Rust std
// (`rustc`), run every function on both invoke successors, and compare exact
// stage order, payload, destructor/cleanup counts and runtime exception state
// with a model. GNU `readelf`, `llvm-dwarfdump` and `llvm-objdump` read the
// relocatable object and the linked executable independently. Mutating one
// LSDA call-site row in the linked executable (dropping the invoke's entry, or
// retargeting its landing pad) must make the run terminate or take the wrong
// path; moving a merged function's landing pad from the invoke's row to the
// row of the call before it must lose the handler; copying the invoke's pad
// onto an early-throw function's earlier-call row must make the pad run for
// the earlier call's exception, which the unmutated image passes to the
// caller; and linking without the personality's runtime must fail naming it.
//
// Evidence boundary: native execution, tool readback and mutation controls
// for these fixtures. This is not a proof of LSDA or personality correctness,
// and typed catches, filters and mixed personalities remain refused.

#[path = "common/pinned_target.rs"]
mod pinned_target;

use std::collections::BTreeMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_ir::{
    BinOp, Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Linkage, Module,
    Ty, ValueId,
};

const LINUX_TRIPLE: &str = "aarch64-unknown-linux-gnu";
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const CXX_PERSONALITY: &str = "__gxx_personality_v0";
const RUST_PERSONALITY: &str = "rust_eh_personality";

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Pad {
    CatchAll,
    Cleanup,
}

/// What an emitted function's exception table must say.
#[derive(Clone, Copy, Debug)]
struct FnSpec {
    name: &'static str,
    /// The invoked callee and the pad its unwind edge enters; `None` for a
    /// plain frame, whose every call must continue unwinding.
    invoke: Option<(&'static str, Pad)>,
}

const CXX_FUNCTIONS: [FnSpec; 7] = [
    FnSpec {
        name: "tc_catch",
        invoke: Some(("cxx_callee", Pad::CatchAll)),
    },
    FnSpec {
        name: "tc_cleanup",
        invoke: Some(("cxx_callee", Pad::Cleanup)),
    },
    FnSpec {
        name: "tc_nested",
        invoke: Some(("tc_cleanup", Pad::CatchAll)),
    },
    FnSpec {
        name: "tc_mid",
        invoke: None,
    },
    FnSpec {
        name: "tc_through",
        invoke: Some(("tc_mid", Pad::CatchAll)),
    },
    FnSpec {
        name: "tc_merged",
        invoke: Some(("cxx_callee", Pad::CatchAll)),
    },
    FnSpec {
        name: "tc_early",
        invoke: Some(("cxx_callee", Pad::CatchAll)),
    },
];

const RUST_FUNCTIONS: [FnSpec; 6] = [
    FnSpec {
        name: "tr_cleanup",
        invoke: Some(("rs_callee", Pad::Cleanup)),
    },
    FnSpec {
        name: "tr_mid",
        invoke: None,
    },
    FnSpec {
        name: "tr_nested",
        invoke: Some(("tr_cleanup", Pad::Cleanup)),
    },
    FnSpec {
        name: "tr_through",
        invoke: Some(("tr_mid", Pad::Cleanup)),
    },
    FnSpec {
        name: "tr_merged",
        invoke: Some(("rs_callee", Pad::Cleanup)),
    },
    FnSpec {
        name: "tr_early",
        invoke: Some(("rs_callee", Pad::Cleanup)),
    },
];

/// The functions whose invoke follows the entry stage call in one trust-ir
/// block (see `merge_invoke_into_entry`), and that entry stage.
const MERGED: [(&str, i32); 2] = [("tc_merged", 50), ("tr_merged", 50)];

/// The functions whose invoke follows, in one trust-ir block, the entry stage
/// call and a plain call to a callee that throws or panics on odd input (see
/// `early_throw_function`): (function, that callee, entry stage).
const EARLY: [(&str, &str, i32); 2] = [("tc_early", "cxx_first", 60), ("tr_early", "rs_first", 60)];

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn b(index: u32) -> BlockId {
    BlockId::new(index)
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
    let mut function = Function::new(FuncId::new(id), name, signature, b(0));
    function.linkage = Linkage::External;
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

fn define(module: &mut Module, id: u32, name: &str, blocks: Vec<Block>) {
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(id), name, signature, b(0));
    function.blocks = blocks;
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

fn i32_const(value: i128, result: u32) -> InstrNode {
    InstrNode::new(Inst::Const {
        ty: Ty::I32,
        value: Constant::Int(value),
    })
    .with_result(v(result))
}

fn call(callee: u32, args: &[u32]) -> InstrNode {
    InstrNode::new(Inst::Call {
        callee: FuncId::new(callee),
        args: args.iter().map(|arg| v(*arg)).collect(),
    })
}

/// `stage(<constant>)` through the constant's fresh value `result`.
fn stage(stage_fn: u32, value: i128, result: u32) -> [InstrNode; 2] {
    [i32_const(value, result), call(stage_fn, &[result])]
}

/// `out = lhs + <constant>` through the constant's fresh value `out - 1`.
fn add_const(lhs: u32, value: i128, out: u32) -> [InstrNode; 2] {
    [
        i32_const(value, out - 1),
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(lhs),
            rhs: v(out - 1),
        })
        .with_result(v(out)),
    ]
}

fn ret(value: u32) -> InstrNode {
    InstrNode::new(Inst::Return {
        values: vec![v(value)],
    })
}

fn block(id: u32, params: Vec<(ValueId, Ty)>, body: Vec<InstrNode>) -> Block {
    Block {
        id: b(id),
        params,
        body,
    }
}

/// `b0: stage(entry); br b3` and `b3: r = invoke callee(x) to b1 unwind b2`.
///
/// The invoke has a trust-ir block of its own here. `merge_invoke_into_entry`
/// builds the other shape, where the adapter must move it into one.
fn invoke_entry(stage_fn: u32, entry_stage: i128, callee: u32) -> [Block; 2] {
    let mut entry = stage(stage_fn, entry_stage, 1).to_vec();
    entry.push(InstrNode::new(Inst::Br {
        target: b(3),
        args: vec![],
    }));
    let invoke = InstrNode::new(Inst::Invoke {
        callee: FuncId::new(callee),
        args: vec![v(0)],
        normal_dest: b(1),
        normal_args: vec![],
        unwind_dest: b(2),
    })
    .with_result(v(2));
    [
        block(0, vec![(v(0), Ty::I32)], entry),
        block(3, vec![], vec![invoke]),
    ]
}

/// Normal successor: `stage(normal); return r + add`.
fn normal_return(stage_fn: u32, normal_stage: i128, add: i128) -> Block {
    let mut body = stage(stage_fn, normal_stage, 10).to_vec();
    body.extend(add_const(2, add, 12));
    body.push(ret(12));
    block(1, vec![], body)
}

fn landing_pad(pad: Pad) -> InstrNode {
    InstrNode::new(Inst::LandingPad {
        is_cleanup: pad == Pad::Cleanup,
        catch_type_indices: if pad == Pad::CatchAll {
            vec![0]
        } else {
            vec![]
        },
    })
    .with_results(vec![v(20), v(21)])
}

/// Runtime entry points a C++ catch pad calls.
struct CatchRuntime {
    stage: u32,
    observe: u32,
    begin: u32,
    end: u32,
}

/// `x -> { stage(entry); r = invoke callee(x) } normal { stage(normal);
/// r + normal_add } catch (...) { p = __cxa_begin_catch(exn);
/// observe(p->code, p->tag); stage(pad); __cxa_end_catch(); p->code + caught }`.
#[allow(clippy::too_many_arguments)]
fn catch_function(
    module: &mut Module,
    id: u32,
    name: &str,
    callee: u32,
    rt: &CatchRuntime,
    stages: [i128; 3],
    normal_add: i128,
    caught_add: i128,
) {
    let mut pad = vec![
        landing_pad(Pad::CatchAll),
        InstrNode::new(Inst::Call {
            callee: FuncId::new(rt.begin),
            args: vec![v(20)],
        })
        .with_result(v(22)),
        InstrNode::new(Inst::Load {
            ty: Ty::I32,
            ptr: v(22),
            volatile: false,
            align: Some(4),
        })
        .with_result(v(23)),
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(4),
        })
        .with_result(v(24)),
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::I8,
            base: v(22),
            indices: vec![v(24)],
            inbounds: true,
        })
        .with_result(v(25)),
        InstrNode::new(Inst::Load {
            ty: Ty::I32,
            ptr: v(25),
            volatile: false,
            align: Some(4),
        })
        .with_result(v(26)),
        call(rt.observe, &[23, 26]),
    ];
    pad.extend(stage(rt.stage, stages[2], 27));
    pad.push(call(rt.end, &[]));
    pad.extend(add_const(23, caught_add, 29));
    pad.push(ret(29));
    define(
        module,
        id,
        name,
        [
            invoke_entry(rt.stage, stages[0], callee).to_vec(),
            vec![
                normal_return(rt.stage, stages[1], normal_add),
                block(2, vec![], pad),
            ],
        ]
        .concat(),
    );
}

/// `x -> { stage(entry); r = invoke callee(x) } normal { stage(normal);
/// r + normal_add } cleanup { cleanup(x); stage(pad); resume }`.
#[allow(clippy::too_many_arguments)]
fn cleanup_function(
    module: &mut Module,
    id: u32,
    name: &str,
    callee: u32,
    stage_fn: u32,
    cleanup_fn: u32,
    stages: [i128; 3],
    normal_add: i128,
) {
    let mut pad = vec![landing_pad(Pad::Cleanup), call(cleanup_fn, &[0])];
    pad.extend(stage(stage_fn, stages[2], 22));
    pad.push(InstrNode::new(Inst::Resume { exn: v(20) }));
    define(
        module,
        id,
        name,
        [
            invoke_entry(stage_fn, stages[0], callee).to_vec(),
            vec![
                normal_return(stage_fn, stages[1], normal_add),
                block(2, vec![], pad),
            ],
        ]
        .concat(),
    );
}

/// Rebuild `name` so its invoke follows the entry stage call in the entry
/// block: `b0: stage(entry); r = invoke callee(x) to b1 unwind b2`. The
/// protected call is then the block's second call.
fn merge_invoke_into_entry(module: &mut Module, name: &str) {
    let function = module
        .functions
        .iter_mut()
        .find(|function| function.name == name)
        .expect("function to merge");
    let position = function
        .blocks
        .iter()
        .position(|candidate| candidate.id == b(3))
        .expect("invoke block");
    let invoke_block = function.blocks.remove(position);
    let entry = &mut function.blocks[0];
    assert!(
        matches!(
            entry.body.pop().map(|node| node.inst),
            Some(Inst::Br { .. })
        ),
        "{name}: the entry must end in its branch to the invoke block"
    );
    entry.body.extend(invoke_block.body);
}

/// Rebuild merged `name` so a plain call precedes its invoke in the entry
/// block and feeds it: `b0: stage(entry); h = first(x); r = invoke callee(h)
/// to b1 unwind b2`. `first` throws or panics on odd `x` and returns `x / 2`
/// otherwise, so the three paths are: the earlier call throws past this
/// frame's pad, the invoke throws into it, or both return.
fn early_throw_function(module: &mut Module, name: &str, first: u32) {
    merge_invoke_into_entry(module, name);
    let function = module
        .functions
        .iter_mut()
        .find(|function| function.name == name)
        .expect("function to rebuild");
    let entry = &mut function.blocks[0];
    let mut invoke = entry.body.pop().expect("the merged invoke");
    let Inst::Invoke { args, .. } = &mut invoke.inst else {
        panic!("{name}: the entry must end in its invoke");
    };
    *args = vec![v(3)];
    entry.body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(first),
            args: vec![v(0)],
        })
        .with_result(v(3)),
    );
    entry.body.push(invoke);
}

/// A frame with no handler: `x -> { r = callee(x); stage(s); r + add }`.
fn plain_function(
    module: &mut Module,
    id: u32,
    name: &str,
    callee: u32,
    stage_fn: u32,
    s: i128,
    add: i128,
) {
    let mut body = vec![
        InstrNode::new(Inst::Call {
            callee: FuncId::new(callee),
            args: vec![v(0)],
        })
        .with_result(v(2)),
    ];
    body.extend(stage(stage_fn, s, 3));
    body.extend(add_const(2, add, 5));
    body.push(ret(5));
    define(
        module,
        id,
        name,
        vec![block(0, vec![(v(0), Ty::I32)], body)],
    );
}

/// The C++-personality module. Stage numbers are the model's vocabulary.
fn cxx_module() -> Module {
    let mut module = Module::new("linux_eh_cxx");
    pinned_target::pin(&mut module, "aarch64-unknown-linux-gnu");
    declare(&mut module, 0, "cxx_callee", vec![Ty::I32], vec![Ty::I32]);
    declare(&mut module, 1, "cg_stage", vec![Ty::I32], vec![]);
    declare(&mut module, 2, "cg_cleanup", vec![Ty::I32], vec![]);
    declare(&mut module, 3, "cg_observe", vec![Ty::I32, Ty::I32], vec![]);
    declare(
        &mut module,
        4,
        "__cxa_begin_catch",
        vec![Ty::Ptr],
        vec![Ty::Ptr],
    );
    declare(&mut module, 5, "__cxa_end_catch", vec![], vec![]);
    let rt = CatchRuntime {
        stage: 1,
        observe: 3,
        begin: 4,
        end: 5,
    };
    catch_function(&mut module, 6, "tc_catch", 0, &rt, [1, 2, 3], 0, 1000);
    cleanup_function(&mut module, 7, "tc_cleanup", 0, 1, 2, [10, 11, 12], 1);
    catch_function(&mut module, 8, "tc_nested", 7, &rt, [20, 21, 22], 2, 2000);
    plain_function(&mut module, 9, "tc_mid", 0, 1, 30, 3);
    catch_function(&mut module, 10, "tc_through", 9, &rt, [40, 41, 42], 0, 3000);
    catch_function(&mut module, 11, "tc_merged", 0, &rt, [50, 51, 52], 4, 4000);
    merge_invoke_into_entry(&mut module, "tc_merged");
    declare(&mut module, 12, "cxx_first", vec![Ty::I32], vec![Ty::I32]);
    catch_function(&mut module, 13, "tc_early", 0, &rt, [60, 61, 62], 5, 5000);
    early_throw_function(&mut module, "tc_early", 12);
    module
}

/// The Rust-personality module: declaring `rust_eh_personality` selects it.
fn rust_module() -> Module {
    let mut module = Module::new("linux_eh_rust");
    pinned_target::pin(&mut module, "aarch64-unknown-linux-gnu");
    declare(&mut module, 0, "rs_callee", vec![Ty::I32], vec![Ty::I32]);
    declare(&mut module, 1, "rs_stage", vec![Ty::I32], vec![]);
    declare(&mut module, 2, "rs_cleanup", vec![Ty::I32], vec![]);
    declare(&mut module, 3, RUST_PERSONALITY, vec![], vec![]);
    cleanup_function(&mut module, 4, "tr_cleanup", 0, 1, 2, [10, 11, 12], 1);
    plain_function(&mut module, 5, "tr_mid", 0, 1, 30, 3);
    cleanup_function(&mut module, 6, "tr_nested", 4, 1, 2, [20, 21, 23], 2);
    cleanup_function(&mut module, 7, "tr_through", 5, 1, 2, [40, 41, 43], 0);
    cleanup_function(&mut module, 8, "tr_merged", 0, 1, 2, [50, 51, 53], 4);
    merge_invoke_into_entry(&mut module, "tr_merged");
    declare(&mut module, 9, "rs_first", vec![Ty::I32], vec![Ty::I32]);
    cleanup_function(&mut module, 10, "tr_early", 0, 1, 2, [60, 61, 63], 5);
    early_throw_function(&mut module, "tr_early", 9);
    module
}

fn compile(module: &Module, level: OptLevel) -> Vec<u8> {
    let spec = trust_cg_codegen::target::TargetSpec::parse(LINUX_TRIPLE).expect("triple parses");
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: level,
            ..CompilerConfig::default()
        },
        spec,
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .unwrap_or_else(|error| panic!("{} at {level:?}: {error}", module.name))
    .object_code
}

// ---------------------------------------------------------------------------
// Independent readers: ELF64 relocatable objects, `.eh_frame`, LSDAs
// ---------------------------------------------------------------------------

fn u16_at(bytes: &[u8], at: usize) -> u16 {
    u16::from_le_bytes(bytes[at..at + 2].try_into().unwrap())
}

fn u32_at(bytes: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
}

fn u64_at(bytes: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap())
}

fn uleb(bytes: &[u8], at: &mut usize) -> u64 {
    let (mut value, mut shift) = (0u64, 0);
    loop {
        let byte = bytes[*at];
        *at += 1;
        value |= u64::from(byte & 0x7f) << shift;
        shift += 7;
        if byte & 0x80 == 0 {
            return value;
        }
    }
}

fn sleb(bytes: &[u8], at: &mut usize) -> i64 {
    let (mut value, mut shift) = (0i64, 0);
    loop {
        let byte = bytes[*at];
        *at += 1;
        value |= i64::from(byte & 0x7f) << shift;
        shift += 7;
        if byte & 0x80 == 0 {
            if shift < 64 && byte & 0x40 != 0 {
                value |= -1 << shift;
            }
            return value;
        }
    }
}

fn push_uleb(out: &mut Vec<u8>, mut value: u64) {
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        if value == 0 {
            out.push(byte);
            return;
        }
        out.push(byte | 0x80);
    }
}

fn uleb_len(value: u64) -> usize {
    let mut out = Vec::new();
    push_uleb(&mut out, value);
    out.len()
}

struct ElfSection {
    name: String,
    offset: usize,
    size: usize,
    info: u32,
}

struct ElfSymbol {
    name: String,
    value: u64,
    size: u64,
    kind: u8,
    bind: u8,
    shndx: u16,
}

struct ElfRela {
    offset: u64,
    kind: u32,
    symbol: usize,
    addend: i64,
}

const R_AARCH64_ABS64: u32 = 257;
const R_AARCH64_PREL32: u32 = 261;
const R_AARCH64_CALL26: u32 = 283;

/// A relocatable AArch64 ELF64 object, read by this file alone.
struct Elf<'a> {
    bytes: &'a [u8],
    sections: Vec<ElfSection>,
    symbols: Vec<ElfSymbol>,
}

impl<'a> Elf<'a> {
    fn parse(bytes: &'a [u8]) -> Self {
        assert_eq!(&bytes[..6], b"\x7fELF\x02\x01", "ELF64 little-endian");
        assert_eq!(u16_at(bytes, 16), 1, "ET_REL");
        assert_eq!(u16_at(bytes, 18), 183, "EM_AARCH64");
        let table = u64_at(bytes, 40) as usize;
        let entry = usize::from(u16_at(bytes, 58));
        let count = usize::from(u16_at(bytes, 60));
        let names = table + usize::from(u16_at(bytes, 62)) * entry;
        let names = &bytes[u64_at(bytes, names + 24) as usize..];
        let c_str = |table: &[u8], at: usize| {
            let end = table[at..].iter().position(|b| *b == 0).unwrap();
            String::from_utf8(table[at..at + end].to_vec()).unwrap()
        };
        let mut sections = Vec::new();
        let mut symtab = None;
        for index in 0..count {
            let header = table + index * entry;
            let section = ElfSection {
                name: c_str(names, u32_at(bytes, header) as usize),
                offset: u64_at(bytes, header + 24) as usize,
                size: u64_at(bytes, header + 32) as usize,
                info: u32_at(bytes, header + 44),
            };
            if u32_at(bytes, header + 4) == 2 {
                symtab = Some((index, u32_at(bytes, header + 40) as usize));
            }
            sections.push(section);
        }
        let (symtab, strtab) = symtab.expect("ELF object carries .symtab");
        let strings = &bytes[sections[strtab].offset..][..sections[strtab].size];
        let symbols = bytes[sections[symtab].offset..][..sections[symtab].size]
            .as_chunks::<24>()
            .0
            .iter()
            .map(|row| ElfSymbol {
                name: c_str(strings, u32_at(row, 0) as usize),
                value: u64_at(row, 8),
                size: u64_at(row, 16),
                kind: row[4] & 0xf,
                bind: row[4] >> 4,
                shndx: u16_at(row, 6),
            })
            .collect();
        Self {
            bytes,
            sections,
            symbols,
        }
    }

    fn section(&self, name: &str) -> (usize, &ElfSection) {
        let mut found = self
            .sections
            .iter()
            .enumerate()
            .filter(|(_, s)| s.name == name);
        let first = found
            .next()
            .unwrap_or_else(|| panic!("ELF object has no {name} section"));
        assert!(found.next().is_none(), "duplicate {name} section");
        first
    }

    fn data(&self, name: &str) -> &'a [u8] {
        let (_, section) = self.section(name);
        &self.bytes[section.offset..][..section.size]
    }

    /// RELA rows applying to section `name`, keyed by patched offset.
    fn relocations(&self, name: &str) -> BTreeMap<u64, ElfRela> {
        let (index, _) = self.section(name);
        let mut rows = BTreeMap::new();
        for section in self.sections.iter().filter(|s| s.info as usize == index) {
            if !section.name.starts_with(".rela") {
                continue;
            }
            for row in self.bytes[section.offset..][..section.size]
                .as_chunks::<24>()
                .0
            {
                let info = u64_at(row, 8);
                let rela = ElfRela {
                    offset: u64_at(row, 0),
                    kind: info as u32,
                    symbol: (info >> 32) as usize,
                    addend: u64_at(row, 16) as i64,
                };
                assert!(
                    rows.insert(rela.offset, rela).is_none(),
                    "two relocations patch one {name} field"
                );
            }
        }
        rows
    }

    /// The section a relocation's symbol is defined in (for STT_SECTION
    /// anchors and defined symbols).
    fn symbol_section(&self, symbol: usize) -> &str {
        &self.sections[usize::from(self.symbols[symbol].shndx)].name
    }

    fn function(&self, name: &str) -> &ElfSymbol {
        let rows: Vec<_> = self
            .symbols
            .iter()
            .filter(|s| s.name == name && s.kind == 2 && s.shndx != 0)
            .collect();
        assert_eq!(rows.len(), 1, "one defined STT_FUNC {name}");
        rows[0]
    }
}

/// One decoded call-site row, offsets relative to the function start.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CallSite {
    start: u64,
    len: u64,
    lp: u64,
    action: u64,
}

/// An LSDA decoded by this file (GCC `.gcc_except_table` layout).
#[derive(Clone, Debug, PartialEq, Eq)]
struct Lsda {
    ttype_enc: u8,
    call_sites: Vec<CallSite>,
    /// Action records reached from the call sites, verbatim.
    actions: Vec<u8>,
    /// Type-table entries 1..=n (entry 1 is nearest the TType base).
    types: Vec<u32>,
    /// Encoded length in bytes, header through the last table byte.
    len: usize,
}

const DW_EH_PE_OMIT: u8 = 0xff;
const DW_EH_PE_ULEB128: u8 = 0x01;
const DW_EH_PE_INDIRECT_PCREL_SDATA4: u8 = 0x9b;
const DW_EH_PE_PCREL_SDATA4: u8 = 0x1b;

impl Lsda {
    /// The header and call-site table only: (TType encoding, TType base
    /// offset, first action-table byte, rows).
    fn call_site_table(bytes: &[u8]) -> Result<(u8, Option<usize>, usize, Vec<CallSite>), String> {
        let mut at = 0;
        if bytes[at] != DW_EH_PE_OMIT {
            return Err(format!("LPStart encoding {:#x} is not omitted", bytes[at]));
        }
        at += 1;
        let ttype_enc = bytes[at];
        at += 1;
        let ttype_base = if ttype_enc == DW_EH_PE_OMIT {
            None
        } else {
            if ttype_enc != DW_EH_PE_INDIRECT_PCREL_SDATA4 {
                return Err(format!("unexpected TType encoding {ttype_enc:#x}"));
            }
            let field = uleb(bytes, &mut at);
            Some(at + field as usize)
        };
        if bytes[at] != DW_EH_PE_ULEB128 {
            return Err(format!(
                "call-site encoding {:#x} is not ULEB128",
                bytes[at]
            ));
        }
        at += 1;
        let table_len = uleb(bytes, &mut at) as usize;
        let actions_start = at + table_len;
        let mut call_sites = Vec::new();
        while at < actions_start {
            call_sites.push(CallSite {
                start: uleb(bytes, &mut at),
                len: uleb(bytes, &mut at),
                lp: uleb(bytes, &mut at),
                action: uleb(bytes, &mut at),
            });
        }
        if at != actions_start {
            return Err("call-site table overruns its length".into());
        }
        Ok((ttype_enc, ttype_base, actions_start, call_sites))
    }

    /// Decode a complete LSDA whose action and type tables hold exactly the
    /// records its call sites reach.
    fn decode(bytes: &[u8]) -> Result<Self, String> {
        let (ttype_enc, ttype_base, actions_start, call_sites) = Self::call_site_table(bytes)?;
        let mut actions_end = actions_start;
        let mut max_filter = 0i64;
        for site in call_sites.iter().filter(|s| s.action != 0) {
            let mut record = actions_start + site.action as usize - 1;
            loop {
                let mut cursor = record;
                let filter = sleb(bytes, &mut cursor);
                let next_field = cursor;
                let next = sleb(bytes, &mut cursor);
                actions_end = actions_end.max(cursor);
                max_filter = max_filter.max(filter);
                if filter < 0 {
                    return Err("exception-specification filters are not expected".into());
                }
                if next == 0 {
                    break;
                }
                record = (next_field as i64 + next) as usize;
            }
        }
        let actions = bytes[actions_start..actions_end].to_vec();
        let (types, len) = match ttype_base {
            None => {
                if max_filter != 0 {
                    return Err("typed action without a type table".into());
                }
                (Vec::new(), actions_end)
            }
            Some(base) => {
                let types: Vec<u32> = (1..=max_filter as usize)
                    .map(|index| u32_at(bytes, base - 4 * index))
                    .collect();
                let table_start = base - 4 * types.len();
                if table_start < actions_end
                    || bytes[actions_end..table_start].iter().any(|b| *b != 0)
                {
                    return Err(
                        "bytes between the action and type tables are not zero padding".into(),
                    );
                }
                (types, base)
            }
        };
        Ok(Self {
            ttype_enc,
            call_sites,
            actions,
            types,
            len,
        })
    }

    /// Re-encode with the layout GCC and clang use: ULEB128 call sites and
    /// a type table 4-byte aligned from the LSDA start.
    fn encode(&self) -> Vec<u8> {
        let mut sites = Vec::new();
        for site in &self.call_sites {
            for field in [site.start, site.len, site.lp, site.action] {
                push_uleb(&mut sites, field);
            }
        }
        let mut body = vec![DW_EH_PE_ULEB128];
        push_uleb(&mut body, sites.len() as u64);
        body.extend(&sites);
        body.extend(&self.actions);
        let mut out = vec![DW_EH_PE_OMIT, self.ttype_enc];
        if self.ttype_enc == DW_EH_PE_OMIT {
            out.extend(body);
            return out;
        }
        let types = 4 * self.types.len();
        let pad = (0..8)
            .find(|pad| {
                let base = body.len() + pad + types;
                (2 + uleb_len(base as u64) + body.len() + pad).is_multiple_of(4)
            })
            .unwrap();
        push_uleb(&mut out, (body.len() + pad + types) as u64);
        out.extend(body);
        out.extend(std::iter::repeat_n(0, pad));
        for entry in self.types.iter().rev() {
            out.extend(entry.to_le_bytes());
        }
        out
    }

    /// The (filter, next) action record at 1-based `action`.
    fn action_record(&self, action: u64) -> (i64, i64) {
        let mut at = action as usize - 1;
        (sleb(&self.actions, &mut at), sleb(&self.actions, &mut at))
    }

    fn covering(&self, offset: u64) -> Option<(usize, CallSite)> {
        self.call_sites
            .iter()
            .copied()
            .enumerate()
            .find(|(_, site)| site.start <= offset && offset < site.start + site.len)
    }
}

/// A direct call instruction at `offset` (function relative) to `target`.
#[derive(Debug)]
struct CallInsn {
    offset: u64,
    target: String,
}

/// Check one function's exception table against its call instructions.
///
/// Every call site is covered; the invoke's row enters a landing pad inside
/// the function with the pad's action (catch-all: filter 1 -> NULL type-table
/// entry; cleanup: action 0) and is the only row with a landing pad; every
/// other call continues unwinding (landing pad 0). Returns the invoke's row.
fn check_function_table(
    spec: &FnSpec,
    size: u64,
    calls: &[CallInsn],
    lsda: &Lsda,
) -> Result<Option<(usize, CallSite)>, String> {
    let name = spec.name;
    let mut previous_end = 0;
    for site in &lsda.call_sites {
        if site.start < previous_end || site.start + site.len > size {
            return Err(format!(
                "{name}: call-site row {site:?} is unordered or outside {size:#x}"
            ));
        }
        previous_end = site.start + site.len;
    }
    let with_pad: Vec<_> = lsda.call_sites.iter().filter(|s| s.lp != 0).collect();
    let invoke_row = match spec.invoke {
        None => {
            if !with_pad.is_empty() || lsda.ttype_enc != DW_EH_PE_OMIT || !lsda.actions.is_empty() {
                return Err(format!(
                    "{name}: a plain frame must have filler rows only: {lsda:?}"
                ));
            }
            None
        }
        Some((callee, pad)) => {
            let sites: Vec<_> = calls.iter().filter(|c| c.target == callee).collect();
            if sites.len() != 1 {
                return Err(format!(
                    "{name}: expected one call to {callee}, found {calls:?}"
                ));
            }
            let (index, row) = lsda
                .covering(sites[0].offset)
                .ok_or_else(|| format!("{name}: invoke of {callee} is not covered: {lsda:?}"))?;
            if row.lp == 0 || with_pad.len() != 1 {
                return Err(format!(
                    "{name}: the invoke row must be the one landing-pad row: {lsda:?}"
                ));
            }
            if row.lp >= size
                || row.lp % 4 != 0
                || (row.start..row.start + row.len).contains(&row.lp)
            {
                return Err(format!(
                    "{name}: landing pad {:#x} is not a body instruction",
                    row.lp
                ));
            }
            match pad {
                Pad::Cleanup if row.action != 0 || lsda.ttype_enc != DW_EH_PE_OMIT => {
                    return Err(format!(
                        "{name}: a cleanup pad needs action 0 and no type table: {lsda:?}"
                    ));
                }
                Pad::CatchAll
                    if row.action == 0
                        || lsda.action_record(row.action) != (1, 0)
                        || lsda.types != [0]
                        || lsda.ttype_enc != DW_EH_PE_INDIRECT_PCREL_SDATA4 =>
                {
                    return Err(format!(
                        "{name}: catch-all needs filter 1 -> NULL typeinfo: {lsda:?}"
                    ));
                }
                _ => {}
            }
            Some((index, row))
        }
    };
    for call in calls {
        if spec.invoke.is_some_and(|(callee, _)| callee == call.target) {
            continue;
        }
        match lsda.covering(call.offset) {
            Some((_, row)) if row.lp == 0 => {}
            other => {
                return Err(format!(
                    "{name}: call to {} at {:#x} must continue unwinding, row {other:?}",
                    call.target, call.offset
                ));
            }
        }
    }
    Ok(invoke_row)
}

/// Object-level facts of one module read by this file's decoders.
struct ObjectTables {
    personality_slot: String,
    slot_target: String,
    /// `BL _Unwind_Resume; BRK #1` pairs seen.
    resumes: usize,
    lsdas: BTreeMap<String, Lsda>,
}

/// `BRK #1`, the trap that ends a block after a noreturn call.
const BRK_1: u32 = 0xd420_0020;

/// Decode `.eh_frame`, its relocations and every LSDA of a relocatable
/// object, and check each function in `specs` against its call instructions.
fn read_object_tables(object: &[u8], specs: &[FnSpec]) -> ObjectTables {
    let elf = Elf::parse(object);
    let eh = elf.data(".eh_frame");
    let eh_relocs = elf.relocations(".eh_frame");
    let lsda_section = elf.data(".gcc_except_table");
    let reloc_at = |offset: usize, kind: u32| -> &ElfRela {
        let row = eh_relocs
            .get(&(offset as u64))
            .unwrap_or_else(|| panic!("no relocation at .eh_frame+{offset:#x}"));
        assert_eq!(row.kind, kind, "relocation kind at .eh_frame+{offset:#x}");
        row
    };
    let mut at = 0;
    let mut personality_slot = None;
    let mut fdes = Vec::new();
    while at < eh.len() {
        let length = u32_at(eh, at) as usize;
        assert_ne!(length, 0, "no mid-object terminator expected");
        let id = u32_at(eh, at + 4);
        let body = at + 8;
        if id == 0 {
            let mut cursor = body;
            assert_eq!(eh[cursor], 1, "CIE version");
            cursor += 1;
            let aug_end = cursor + eh[cursor..].iter().position(|b| *b == 0).unwrap();
            let augmentation = std::str::from_utf8(&eh[cursor..aug_end])
                .unwrap()
                .to_owned();
            cursor = aug_end + 1;
            assert_eq!(uleb(eh, &mut cursor), 4, "code alignment");
            assert_eq!(sleb(eh, &mut cursor), -8, "data alignment");
            assert_eq!(uleb(eh, &mut cursor), 30, "return address column");
            assert_eq!(augmentation, "zPLR", "EH CIE augmentation");
            let _aug_len = uleb(eh, &mut cursor);
            assert_eq!(
                eh[cursor], DW_EH_PE_INDIRECT_PCREL_SDATA4,
                "personality encoding"
            );
            let personality = reloc_at(cursor + 1, R_AARCH64_PREL32);
            assert_eq!(personality.addend, 0);
            personality_slot = Some(elf.symbols[personality.symbol].name.clone());
            assert_eq!(eh[cursor + 5], DW_EH_PE_PCREL_SDATA4, "LSDA encoding");
            assert_eq!(
                eh[cursor + 6],
                DW_EH_PE_PCREL_SDATA4,
                "FDE pointer encoding"
            );
        } else {
            let pc = reloc_at(body, R_AARCH64_PREL32);
            assert_eq!(
                elf.symbol_section(pc.symbol),
                ".text",
                "FDE PC-begin anchor"
            );
            let mut cursor = body + 8;
            assert_eq!(uleb(eh, &mut cursor), 4, "FDE augmentation length");
            let lsda = reloc_at(cursor, R_AARCH64_PREL32);
            assert_eq!(
                elf.symbol_section(lsda.symbol),
                ".gcc_except_table",
                "LSDA anchor"
            );
            fdes.push((
                pc.addend as u64,
                u64::from(u32_at(eh, body + 4)),
                lsda.addend as usize,
            ));
        }
        at += 4 + length;
    }
    let personality_slot = personality_slot.expect("EH object has a CIE");
    let slot = elf
        .symbols
        .iter()
        .find(|s| s.name == personality_slot)
        .expect("personality slot symbol");
    assert_eq!(
        (slot.kind, slot.bind, slot.size),
        (1, 2, 8),
        "DW.ref slot is an 8-byte weak STT_OBJECT"
    );
    let slot_section = elf.symbol_section(
        elf.symbols
            .iter()
            .position(|s| s.name == personality_slot)
            .unwrap(),
    );
    let slot_relocs = elf.relocations(slot_section);
    let slot_reloc = slot_relocs
        .get(&slot.value)
        .expect("the slot's content relocation");
    assert_eq!(slot_reloc.kind, R_AARCH64_ABS64);
    let slot_target = elf.symbols[slot_reloc.symbol].name.clone();

    let text = elf.data(".text");
    let text_relocs = elf.relocations(".text");
    let function_at = |offset: u64| {
        elf.symbols
            .iter()
            .find(|s| s.kind == 2 && s.shndx != 0 && s.value == offset)
            .map(|s| s.name.clone())
    };
    let mut lsdas = BTreeMap::new();
    let mut resumes = 0;
    for spec in specs {
        let symbol = elf.function(spec.name);
        let fde: Vec<_> = fdes
            .iter()
            .filter(|(start, ..)| *start == symbol.value)
            .collect();
        assert_eq!(fde.len(), 1, "{}: one FDE", spec.name);
        let (_, range, lsda_offset) = *fde[0];
        assert_eq!(range, symbol.size, "{}: FDE covers the body", spec.name);
        let lsda = Lsda::decode(&lsda_section[lsda_offset..])
            .unwrap_or_else(|error| panic!("{}: {error}", spec.name));
        assert_eq!(
            lsda.encode(),
            lsda_section[lsda_offset..lsda_offset + lsda.len],
            "{}: the LSDA re-encodes byte for byte",
            spec.name
        );
        let mut calls = Vec::new();
        for offset in (0..symbol.size).step_by(4) {
            let at = symbol.value + offset;
            let word = u32_at(text, at as usize);
            if word & 0xfc00_0000 != 0x9400_0000 {
                continue;
            }
            let target = match text_relocs.get(&at) {
                Some(row) => {
                    assert_eq!(row.kind, R_AARCH64_CALL26);
                    elf.symbols[row.symbol].name.clone()
                }
                None => {
                    let delta = (((word & 0x03ff_ffff) << 6) as i32 >> 4) as i64;
                    function_at((at as i64 + delta) as u64).expect("direct BL names a function")
                }
            };
            if target == "_Unwind_Resume" {
                // The noreturn resume never falls through into the next block.
                assert_eq!(
                    u32_at(text, at as usize + 4),
                    BRK_1,
                    "{}: BL _Unwind_Resume at {offset:#x} must be followed by BRK #1",
                    spec.name
                );
                resumes += 1;
            }
            calls.push(CallInsn { offset, target });
        }
        let cleanup = matches!(spec.invoke, Some((_, Pad::Cleanup)));
        assert_eq!(
            calls
                .iter()
                .filter(|c| c.target == "_Unwind_Resume")
                .count(),
            usize::from(cleanup),
            "{}: one resume per cleanup pad",
            spec.name
        );
        check_function_table(spec, symbol.size, &calls, &lsda)
            .unwrap_or_else(|error| panic!("{error}"));
        lsdas.insert(spec.name.to_owned(), lsda);
    }
    ObjectTables {
        personality_slot,
        slot_target,
        resumes,
        lsdas,
    }
}

// ---------------------------------------------------------------------------
// Host-neutral rows
// ---------------------------------------------------------------------------

/// Every Linux object at O0-O3 carries a zPLR CIE whose personality goes
/// through `DW.ref.<personality>`, and an LSDA per function whose rows match
/// the function's call instructions.
#[test]
fn linux_objects_cover_every_invoke_with_its_landing_pad_at_o0_to_o3() {
    let (mut functions, mut resumes) = (0, 0);
    for level in LEVELS {
        for (module, specs, personality) in [
            (cxx_module(), &CXX_FUNCTIONS[..], CXX_PERSONALITY),
            (rust_module(), &RUST_FUNCTIONS[..], RUST_PERSONALITY),
        ] {
            let object = compile(&module, level);
            let tables = read_object_tables(&object, specs);
            assert_eq!(tables.personality_slot, format!("DW.ref.{personality}"));
            assert_eq!(tables.slot_target, personality);
            functions += tables.lsdas.len();
            resumes += tables.resumes;
        }
    }
    assert_eq!(
        functions,
        LEVELS.len() * (CXX_FUNCTIONS.len() + RUST_FUNCTIONS.len())
    );
    println!("EH_LINUX_OBJECT_TABLES functions={functions} resumes={resumes}");
}

/// The mutations the Linux rows apply are exactly the intended row edits:
/// dropping the invoke's row leaves its call uncovered, and retargeting its
/// landing pad changes nothing else.
#[test]
fn lsda_mutations_edit_exactly_the_invoke_row() {
    let object = compile(&cxx_module(), OptLevel::O0);
    let tables = read_object_tables(&object, &CXX_FUNCTIONS);
    for spec in CXX_FUNCTIONS.iter().filter(|s| s.invoke.is_some()) {
        let lsda = &tables.lsdas[spec.name];
        let (index, row) = lsda
            .call_sites
            .iter()
            .copied()
            .enumerate()
            .find(|(_, s)| s.lp != 0)
            .unwrap();
        // Dropping the row keeps the (now unreferenced) action and type
        // tables; only the call-site table changes.
        let dropped = drop_row(lsda, index);
        assert!(dropped.len() <= lsda.len);
        let (_, _, _, rows) = Lsda::call_site_table(&dropped).unwrap();
        let mut expected = lsda.call_sites.clone();
        expected.remove(index);
        assert_eq!(rows, expected, "{}: only the invoke row is gone", spec.name);
        assert!(
            !rows
                .iter()
                .any(|s| s.start <= row.start && row.start < s.start + s.len),
            "{}: invoke still covered",
            spec.name
        );
        let moved = retarget_row(lsda, index, row.start + row.len);
        assert!(
            moved.len() <= lsda.len,
            "{}: retargeting fits in place",
            spec.name
        );
        let decoded = Lsda::decode(&moved).unwrap();
        let mut expected = lsda.clone();
        expected.call_sites[index].lp = row.start + row.len;
        expected.len = moved.len();
        assert_eq!(
            decoded, expected,
            "{}: only the landing pad moved",
            spec.name
        );
    }
}

fn drop_row(lsda: &Lsda, index: usize) -> Vec<u8> {
    let mut edited = lsda.clone();
    edited.call_sites.remove(index);
    edited.encode()
}

fn retarget_row(lsda: &Lsda, index: usize, landing_pad: u64) -> Vec<u8> {
    let mut edited = lsda.clone();
    edited.call_sites[index].lp = landing_pad;
    edited.encode()
}

/// Exception metadata admits one call per protected block. The adapter moves
/// an invoke that follows another call of its trust-ir block into a LIR block
/// of its own, reached by a jump after the earlier calls, and records that
/// block as the call site; an invoke with a trust-ir block of its own stays
/// there. The object rows above then give the earlier calls no-handler rows.
#[test]
fn invoke_after_another_call_moves_into_a_block_of_its_own() {
    use trust_cg_lower::instructions::Opcode;
    let mut moved = 0;
    for module in [cxx_module(), rust_module()] {
        let lowered = permit_translate_module(&module).expect("lowering");
        for (function, _) in &lowered {
            let invokes: Vec<_> = function
                .blocks
                .iter()
                .filter(|(_, block)| {
                    block
                        .instructions
                        .iter()
                        .any(|inst| matches!(inst.opcode, Opcode::Invoke { .. }))
                })
                .collect();
            let Some(&(invoke_block, block)) = invokes.first() else {
                continue;
            };
            let name = function.name.as_str();
            assert_eq!(invokes.len(), 1, "{name}: one invoke");
            assert_eq!(
                block.instructions.len(),
                1,
                "{name}: the invoke is alone in its block"
            );
            let call_sites: Vec<_> = function
                .eh_info
                .call_sites
                .iter()
                .map(|site| site.call_block)
                .collect();
            assert_eq!(call_sites, [*invoke_block], "{name}: the call site");
            let entry = &function.blocks[&function.entry_block];
            let entry_calls = entry
                .instructions
                .iter()
                .filter(|inst| matches!(inst.opcode, Opcode::Call { .. }))
                .count();
            // The entry stage call, and for an early-throw function its call
            // to the throwing first callee.
            let early = EARLY.iter().any(|(early, ..)| *early == name);
            assert_eq!(
                entry_calls,
                1 + usize::from(early),
                "{name}: the entry's plain calls"
            );
            assert!(
                matches!(
                    entry.instructions.last().map(|inst| &inst.opcode),
                    Some(Opcode::Jump { dest }) if dest == invoke_block
                ),
                "{name}: the entry jumps to the invoke block"
            );
            if early || MERGED.iter().any(|(merged, _)| *merged == name) {
                moved += 1;
            }
        }
    }
    assert_eq!(moved, MERGED.len() + EARLY.len());
    println!("EH_LINUX_MERGED_INVOKES moved={moved}");
}

/// A C++ catch-all function `name(x, a, b)` whose entry block computes `ops`
/// (ending in the i32 `%4`) and then invokes `cxx_callee(x + %4)`.
fn call_then_invoke_module(name: &str, operand: &str, ops: &str) -> Module {
    let text = format!(
        r#"; TrustIr text format v1
module "linux_eh_call_then_invoke"
target "aarch64-unknown-linux-gnu" 8 little abi="aapcs64"

functy.0 = (i32) -> (i32)
functy.1 = (ptr) -> (ptr)
functy.2 = () -> ()
functy.3 = (i32, {operand}, {operand}) -> (i32)

fn @cxx_callee(functy.0) {{
}}

fn @__cxa_begin_catch(functy.1) {{
}}

fn @__cxa_end_catch(functy.2) {{
}}

fn @{name}(functy.3) {{
bb0(%0: i32, %1: {operand}, %2: {operand}):
{ops}
    %5 = add i32 %0, %4
    %6 = invoke @func.0(%5) to bb1() unwind bb2
bb1:
    ret %6
bb2:
    %7, %8 = landingpad catch 0
    %9 = call @func.1(%7)
    %10 = load i32, ptr %9
    call @func.2()
    ret %10
}}
"#
    );
    trust_ir::parser::parse_module(&text).unwrap_or_else(|e| panic!("{name} parses: {e:?}"))
}

fn compile_result(module: &Module, level: OptLevel) -> Result<Vec<u8>, String> {
    let spec = trust_cg_codegen::target::TargetSpec::parse(LINUX_TRIPLE).expect("triple parses");
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: level,
            ..CompilerConfig::default()
        },
        spec,
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .map(|result| result.object_code)
    .map_err(|error| error.to_string())
}

/// Independently read actual helper BL bytes and their no-handler rows. This
/// is relocatable-object evidence, not native Linux execution or proof credit.
fn check_selection_helper_rows(object: &[u8], name: &str, runtime: &str, lsda: &Lsda) -> usize {
    let elf = Elf::parse(object);
    let symbol = elf.function(name);
    let relocations = elf.relocations(".text");
    let helpers: Vec<_> = relocations
        .values()
        .filter(|row| {
            symbol.value <= row.offset
                && row.offset < symbol.value + symbol.size
                && elf.symbols[row.symbol].name == runtime
        })
        .collect();
    assert!(
        !helpers.is_empty(),
        "{name}: real selected helper {runtime} must remain; actual function relocations: {:?}",
        relocations
            .values()
            .filter(|row| { symbol.value <= row.offset && row.offset < symbol.value + symbol.size })
            .map(|row| (
                row.offset - symbol.value,
                &elf.symbols[row.symbol].name,
                row.kind
            ))
            .collect::<Vec<_>>()
    );
    for helper in &helpers {
        assert_eq!(
            helper.kind, R_AARCH64_CALL26,
            "{name}: helper call relocation"
        );
        assert_eq!(
            u32_at(elf.data(".text"), helper.offset as usize) & 0xfc00_0000,
            0x9400_0000,
            "{name}: helper's actual encoded instruction is BL"
        );
        let pc = helper.offset - symbol.value;
        for byte in [pc, pc + 3] {
            let (_, row) = lsda
                .covering(byte)
                .expect("helper BL bytes have propagation rows");
            assert_eq!(
                row.lp, 0,
                "{name}: {runtime} must not inherit the Invoke's pad"
            );
        }
    }
    let protected: Vec<_> = lsda.call_sites.iter().filter(|row| row.lp != 0).collect();
    assert_eq!(protected.len(), 1, "{name}: exactly one selected Invoke");
    assert_eq!(
        protected[0].len, 4,
        "{name}: only the exact Invoke's BL bytes"
    );
    helpers.len()
}

/// Which calls before an invoke the adapter can see. A call the adapter
/// itself emits moves the invoke into a block of its own: a trust-ir `Call`,
/// `frem` (`fmod`/`fmodf`), and an i128 <-> f32/f64 cast (`__fix*ti`,
/// `__float*ti*`); the object then gives that call a no-handler row and the
/// invoke its pad. A call that instruction selection introduces stays in the
/// protected block; exact instruction custody keeps its no-handler row at O0-O3:
/// i128 `udiv`/`sdiv`/`urem`/`srem` (`__udivti3`, `__divti3`, `__umodti3`,
/// `__modti3`) here, and an aggregate copy (below).
#[test]
fn calls_before_an_invoke_split_when_the_adapter_emits_them() {
    let split = [
        (
            "tc_frem_f64",
            "f64",
            "    %3 = frem f64 %1, %2\n    %4 = fptosi f64 %3 to i32",
            "fmod",
        ),
        (
            "tc_frem_f32",
            "f32",
            "    %3 = frem f32 %1, %2\n    %4 = fptosi f32 %3 to i32",
            "fmodf",
        ),
        (
            "tc_fptosi_i128",
            "f64",
            "    %3 = fptosi f64 %1 to i128\n    %4 = trunc i128 %3 to i32",
            "__fixdfti",
        ),
        (
            "tc_sitofp_i128",
            "i128",
            "    %3 = sitofp i128 %1 to f64\n    %4 = fptosi f64 %3 to i32",
            "__floattidf",
        ),
    ];
    let selected = [
        (
            "tc_udiv_i128",
            "i128",
            "    %3 = udiv i128 %1, %2\n    %4 = trunc i128 %3 to i32",
            "__udivti3",
        ),
        (
            "tc_srem_i128",
            "i128",
            "    %3 = srem i128 %1, %2\n    %4 = trunc i128 %3 to i32",
            "__modti3",
        ),
    ];
    let (mut compiled, mut selection_rows, mut helper_calls) = (0, 0, 0);
    for level in LEVELS {
        for (name, operand, ops, runtime) in split {
            let module = call_then_invoke_module(name, operand, ops);
            let object = compile_result(&module, level)
                .unwrap_or_else(|error| panic!("{level:?} {name}: {error}"));
            let symbol = [runtime.as_bytes(), b"\0"].concat();
            assert!(
                object.windows(symbol.len()).any(|window| window == symbol),
                "{level:?} {name}: the object must call {runtime}"
            );
            let spec = FnSpec {
                name,
                invoke: Some(("cxx_callee", Pad::CatchAll)),
            };
            read_object_tables(&object, &[spec]);
            compiled += 1;
        }
        for (name, operand, ops, runtime) in selected {
            let object = compile_result(&call_then_invoke_module(name, operand, ops), level)
                .unwrap_or_else(|error| panic!("{level:?} {name}: {error}"));
            let tables = read_object_tables(
                &object,
                &[FnSpec {
                    name,
                    invoke: Some(("cxx_callee", Pad::CatchAll)),
                }],
            );
            helper_calls +=
                check_selection_helper_rows(&object, name, runtime, &tables.lsdas[name]);
            selection_rows += 1;
        }
    }
    assert_eq!(compiled, LEVELS.len() * split.len());
    assert_eq!(selection_rows, LEVELS.len() * selected.len());
    assert!(helper_calls >= selection_rows);
    println!(
        "EH_LINUX_ADAPTER_CALL_SPLITS compiled={compiled} selection_rows={selection_rows} helper_calls={helper_calls}"
    );
}

/// An aggregate copy in the invoke's own block lowers to copy-routine calls
/// in instruction selection. Exact instruction custody protects only the
/// Invoke, with independent ELF/LSDA and actual helper-byte readback at O0-O3.
#[test]
fn invoke_after_a_selection_introduced_copy_has_exact_handler_bytes() {
    use trust_cg_lower::instructions::Opcode;

    const TEXT: &str = r#"; TrustIr text format v1
module "linux_eh_selection_call"
target "aarch64-unknown-linux-gnu" 8 little abi="aapcs64"

struct @Big { g: [ty.0 x 40] @0 } size=320 align=8 repr=c id=0

type ty.0 = i64

functy.0 = (i64) -> (i64)
functy.1 = (ptr) -> (ptr)
functy.2 = () -> ()
functy.3 = (ptr, ptr, i64) -> (i64)

fn @cxx_callee(functy.0) {
}

fn @__cxa_begin_catch(functy.1) {
}

fn @__cxa_end_catch(functy.2) {
}

fn @tc_copy_then_invoke(functy.3) {
bb0(%0: ptr, %1: ptr, %2: i64):
    %3 = load struct.0, ptr %1
    store struct.0 %3, ptr %0
    %4 = invoke @func.0(%2) to bb1() unwind bb2
bb1:
    ret %4
bb2:
    %5, %6 = landingpad catch 0
    %7 = call @func.1(%5)
    call @func.2()
    %8 = const i64 -1
    ret %8
}
"#;
    let module = trust_ir::parser::parse_module(TEXT).expect("fixture parses");
    let lowered = permit_translate_module(&module).expect("original source lowers");
    let (function, _) = lowered
        .iter()
        .find(|(function, _)| function.name == "tc_copy_then_invoke")
        .expect("original aggregate-copy function lowers");
    let invokes: Vec<_> = function
        .blocks
        .iter()
        .flat_map(|(block, body)| {
            body.instructions.iter().enumerate().filter_map(move |(index, instruction)| {
                matches!(&instruction.opcode, Opcode::Invoke { name, .. } if name == "cxx_callee")
                    .then_some((*block, index))
            })
        })
        .collect();
    assert_eq!(
        invokes.len(),
        1,
        "original source has exactly one genuine Invoke"
    );
    let (invoke_block, invoke_index) = invokes[0];
    let copies: Vec<_> = function.blocks[&invoke_block].instructions[..invoke_index]
        .iter()
        .filter(|instruction| matches!(instruction.opcode, Opcode::Memmove))
        .collect();
    assert_eq!(
        copies.len(),
        2,
        "aggregate Load and Store remain selection-level copy carriers before Invoke"
    );
    assert!(
        copies
            .iter()
            .all(|copy| copy.args.len() == 3 && copy.results.is_empty())
    );
    assert_eq!(
        copies[0].args[0], copies[1].args[1],
        "the loaded aggregate's fresh slot is consumed by the external destination Store"
    );
    assert_eq!(function.eh_info.call_sites.len(), 1);
    assert_eq!(function.eh_info.call_sites[0].call_block, invoke_block);
    let (mut compiled, mut helper_calls) = (0, 0);
    for level in LEVELS {
        let object = compile_result(&module, level)
            .unwrap_or_else(|error| panic!("{level:?} tc_copy_then_invoke: {error}"));
        let tables = read_object_tables(
            &object,
            &[FnSpec {
                name: "tc_copy_then_invoke",
                invoke: Some(("cxx_callee", Pad::CatchAll)),
            }],
        );
        helper_calls += check_selection_helper_rows(
            &object,
            "tc_copy_then_invoke",
            "memmove",
            &tables.lsdas["tc_copy_then_invoke"],
        );
        compiled += 1;
    }
    assert_eq!(compiled, LEVELS.len());
    assert!(helper_calls >= compiled);
    println!("EH_LINUX_SELECTION_CALL_IDENTITIES compiled={compiled} helper_calls={helper_calls}");
}

/// Structural EH metadata without a personality (absent or empty) is
/// refused by name before instruction selection on the Linux path; it is
/// never emitted with a guessed or empty CIE personality.
#[test]
fn eh_function_without_personality_is_refused_by_name() {
    let lowered = permit_translate_module(&cxx_module()).expect("lowering");
    let (function, _) = lowered
        .into_iter()
        .find(|(function, _)| function.name == "tc_catch")
        .expect("tc_catch lowers");
    assert_eq!(
        function.eh_info.personality.as_deref(),
        Some(CXX_PERSONALITY)
    );
    let mut refusals = 0;
    for personality in [None, Some(String::new())] {
        let mut function = function.clone();
        function.eh_info.personality = personality.clone();
        for level in LEVELS {
            let pipeline = Pipeline::new(PipelineConfig {
                opt_level: level,
                target_triple: LINUX_TRIPLE.into(),
                ..PipelineConfig::default()
            });
            let error = pipeline
                .compile_function(&function)
                .expect_err("EH without a personality must be refused");
            let message = error.to_string();
            assert!(
                message.contains(
                    "function `tc_catch` contains EH opcodes but has no personality symbol"
                ),
                "{level:?} {personality:?}: refusal must name the missing personality, \
                 got: {message}"
            );
            refusals += 1;
        }
    }
    println!("EH_LINUX_PERSONALITY_REFUSALS refusals={refusals}");
}

// ---------------------------------------------------------------------------
// Linux GNU rows: link, run, independent tool readback, mutation controls
// ---------------------------------------------------------------------------

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[path = "common/rosetta.rs"]
mod process;

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[path = "common/llvm_tools.rs"]
mod llvm_tools;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
mod linux {
    use super::*;
    use crate::{llvm_tools, process};
    use std::fs;
    use std::os::unix::process::ExitStatusExt;
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::sync::Once;
    use std::time::Duration;

    /// Arguments of every run. Callees throw or panic on odd values and
    /// return `3x + 77` on even ones, so each function takes both invoke
    /// successors.
    const XS: [i32; 8] = [0, 1, 2, 7, -3, -8, 12345, 0x07ff_ffff];
    /// Second payload word, read back by the CG catch pads.
    const PAYLOAD_TAG: i32 = 0x5a;
    const SIGABRT: i32 = 6;

    /// A C++-personality module whose only C++ runtime import is the personality
    /// (no `__cxa_*` calls), for the missing-runtime link control.
    fn cleanup_only_module() -> Module {
        let mut module = Module::new("linux_eh_cleanup_only");
        pinned_target::pin(&mut module, "aarch64-unknown-linux-gnu");
        declare(&mut module, 0, "cxx_callee", vec![Ty::I32], vec![Ty::I32]);
        declare(&mut module, 1, "cg_stage", vec![Ty::I32], vec![]);
        declare(&mut module, 2, "cg_cleanup", vec![Ty::I32], vec![]);
        cleanup_function(&mut module, 3, "tc_cleanup", 0, 1, 2, [10, 11, 12], 1);
        module
    }

    // ---------------------------------------------------------------------------
    // Model: the exact line each driver prints for one call
    // ---------------------------------------------------------------------------

    fn join(stages: &[i32]) -> String {
        stages
            .iter()
            .map(i32::to_string)
            .collect::<Vec<_>>()
            .join(",")
    }

    /// `tc_early`: `cxx_first(x)` (stage 8) throws on odd `x`, which must
    /// pass this frame's catch-all to the driver's catch without entering it;
    /// otherwise `h = x / 2` and the invoke of `cxx_callee(h)` throws into the
    /// CG catch-all (odd `h`) or returns.
    fn cxx_early_expected(x: i32) -> String {
        let (ret, caught, obs, stages, payload) = if x & 1 != 0 {
            (
                "-".to_owned(),
                format!("{x}:{PAYLOAD_TAG}"),
                "-".to_owned(),
                "60,8,98,99,7",
                1,
            )
        } else if (x / 2) & 1 != 0 {
            let h = x / 2;
            (
                (h + 5000).to_string(),
                "-".to_owned(),
                format!("{h}:{PAYLOAD_TAG}"),
                "60,8,5,6,62,7,98",
                1,
            )
        } else {
            let r = (x / 2).wrapping_mul(3).wrapping_add(77);
            (
                (r + 5).to_string(),
                "-".to_owned(),
                "-".to_owned(),
                "60,8,5,6,61,98",
                0,
            )
        };
        format!(
            "tc_early x={x} ret={ret} caught={caught} obs={obs} stages={stages} cleanup=0/0 \
             payload={payload}/{payload} uncaught=0 current=0"
        )
    }

    /// `tr_early`: `rs_first(x)` (stage 8) panics on odd `x`, which must pass
    /// this frame's cleanup pad (no `rs_cleanup`, no stage 63) to
    /// `catch_unwind`; otherwise `h = x / 2` and the invoke of `rs_callee(h)`
    /// panics through the CG cleanup (odd `h`) or returns.
    fn rust_early_expected(x: i32) -> String {
        let (ret, caught, stages, cleanups, hook) = if x & 1 != 0 {
            (
                "-".to_owned(),
                format!("{x}:{PAYLOAD_TAG}"),
                "60,8,98,99,7",
                0,
                1,
            )
        } else if (x / 2) & 1 != 0 {
            let h = x / 2;
            (
                "-".to_owned(),
                format!("{h}:{PAYLOAD_TAG}"),
                "60,8,5,6,63,98,99,7",
                1,
                1,
            )
        } else {
            let r = (x / 2).wrapping_mul(3).wrapping_add(77);
            ((r + 5).to_string(), "-".to_owned(), "60,8,5,6,61,98", 0, 0)
        };
        format!(
            "tr_early x={x} ret={ret} caught={caught} stages={stages} cleanup={cleanups}/{} \
             hook={hook}",
            i64::from(cleanups) * i64::from(x)
        )
    }

    /// C++ driver line. Stages: 5/6 callee entry and RAII guard, 7 payload
    /// destructor, 8 the early-throw first callee, 98 caller guard, 99 caller
    /// catch handler; the rest are CG.
    fn cxx_expected(name: &str, x: i32) -> String {
        if name == "tc_early" {
            return cxx_early_expected(x);
        }
        let throws = x & 1 != 0;
        let r = x.wrapping_mul(3).wrapping_add(77);
        let payload = format!("{x}:{PAYLOAD_TAG}");
        let none = "-".to_owned();
        // (ret, caught, observed, stages, cleanups)
        let (ret, caught, obs, stages, cleanups): (String, String, String, Vec<i32>, i32) =
            match (name, throws) {
                ("tc_catch", true) => (
                    (x + 1000).to_string(),
                    none.clone(),
                    payload.clone(),
                    vec![1, 5, 6, 3, 7, 98],
                    0,
                ),
                ("tc_catch", false) => (r.to_string(), none.clone(), none, vec![1, 5, 6, 2, 98], 0),
                ("tc_cleanup", true) => (
                    none.clone(),
                    payload,
                    none,
                    vec![10, 5, 6, 12, 98, 99, 7],
                    1,
                ),
                ("tc_cleanup", false) => (
                    (r + 1).to_string(),
                    none.clone(),
                    none,
                    vec![10, 5, 6, 11, 98],
                    0,
                ),
                ("tc_nested", true) => (
                    (x + 2000).to_string(),
                    none,
                    payload,
                    vec![20, 10, 5, 6, 12, 22, 7, 98],
                    1,
                ),
                ("tc_nested", false) => (
                    (r + 3).to_string(),
                    none.clone(),
                    none,
                    vec![20, 10, 5, 6, 11, 21, 98],
                    0,
                ),
                ("tc_mid", true) => (none.clone(), payload, none, vec![5, 6, 98, 99, 7], 0),
                ("tc_mid", false) => (
                    (r + 3).to_string(),
                    none.clone(),
                    none,
                    vec![5, 6, 30, 98],
                    0,
                ),
                ("tc_through", true) => (
                    (x + 3000).to_string(),
                    none,
                    payload,
                    vec![40, 5, 6, 42, 7, 98],
                    0,
                ),
                ("tc_through", false) => (
                    (r + 3).to_string(),
                    none.clone(),
                    none,
                    vec![40, 5, 6, 30, 41, 98],
                    0,
                ),
                ("tc_merged", true) => (
                    (x + 4000).to_string(),
                    none,
                    payload,
                    vec![50, 5, 6, 52, 7, 98],
                    0,
                ),
                ("tc_merged", false) => (
                    (r + 4).to_string(),
                    none.clone(),
                    none,
                    vec![50, 5, 6, 51, 98],
                    0,
                ),
                _ => unreachable!("unknown C++ fixture {name}"),
            };
        let thrown = u8::from(throws);
        format!(
            "{name} x={x} ret={ret} caught={caught} obs={obs} stages={} cleanup={cleanups}/{} \
             payload={thrown}/{thrown} uncaught=0 current=0",
            join(&stages),
            i64::from(cleanups) * i64::from(x),
        )
    }

    /// Rust harness line. Same stage vocabulary; `hook` counts panic-hook calls.
    fn rust_expected(name: &str, x: i32) -> String {
        if name == "tr_early" {
            return rust_early_expected(x);
        }
        let throws = x & 1 != 0;
        let r = x.wrapping_mul(3).wrapping_add(77);
        let (ret, stages, cleanups): (String, Vec<i32>, i32) = match (name, throws) {
            ("tr_cleanup", true) => ("-".into(), vec![10, 5, 6, 12, 98, 99, 7], 1),
            ("tr_cleanup", false) => ((r + 1).to_string(), vec![10, 5, 6, 11, 98], 0),
            ("tr_mid", true) => ("-".into(), vec![5, 6, 98, 99, 7], 0),
            ("tr_mid", false) => ((r + 3).to_string(), vec![5, 6, 30, 98], 0),
            ("tr_nested", true) => ("-".into(), vec![20, 10, 5, 6, 12, 23, 98, 99, 7], 2),
            ("tr_nested", false) => ((r + 3).to_string(), vec![20, 10, 5, 6, 11, 21, 98], 0),
            ("tr_through", true) => ("-".into(), vec![40, 5, 6, 43, 98, 99, 7], 1),
            ("tr_through", false) => ((r + 3).to_string(), vec![40, 5, 6, 30, 41, 98], 0),
            ("tr_merged", true) => ("-".into(), vec![50, 5, 6, 53, 98, 99, 7], 1),
            ("tr_merged", false) => ((r + 4).to_string(), vec![50, 5, 6, 51, 98], 0),
            _ => unreachable!("unknown Rust fixture {name}"),
        };
        let caught = if throws {
            format!("{x}:{PAYLOAD_TAG}")
        } else {
            "-".into()
        };
        format!(
            "{name} x={x} ret={ret} caught={caught} stages={} cleanup={cleanups}/{} hook={}",
            join(&stages),
            i64::from(cleanups) * i64::from(x),
            u8::from(throws),
        )
    }

    // -----------------------------------------------------------------------
    // Drivers
    // -----------------------------------------------------------------------

    fn xs_list() -> String {
        XS.iter().map(i32::to_string).collect::<Vec<_>>().join(", ")
    }

    /// C++ caller and callee around the CG frames. With `<name> <x>` it runs
    /// one call (the mutation controls); otherwise every function on every
    /// argument.
    fn cxx_driver() -> String {
        format!(
            r#"#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstddef>
#include <exception>
#include <sys/prctl.h>
extern "C" {{
int tc_catch(int); int tc_cleanup(int); int tc_nested(int); int tc_mid(int); int tc_through(int);
int tc_merged(int); int tc_early(int);
}}
static int g_stages[32]; static int g_nstages;
static int g_cleanups; static long long g_cleanup_sum;
static int g_obs_set, g_obs_code, g_obs_tag;
static int g_payload_ctor, g_payload_dtor;
extern "C" void cg_stage(int s) {{ if (g_nstages == 32) abort(); g_stages[g_nstages++] = s; }}
extern "C" void cg_cleanup(int x) {{ ++g_cleanups; g_cleanup_sum += x; }}
extern "C" void cg_observe(int code, int tag) {{ g_obs_set = 1; g_obs_code = code; g_obs_tag = tag; }}
struct Payload {{
  int code; int tag;
  explicit Payload(int c) : code(c), tag({tag}) {{ ++g_payload_ctor; }}
  Payload(const Payload& o) : code(o.code), tag(o.tag) {{ ++g_payload_ctor; }}
  ~Payload() {{ ++g_payload_dtor; cg_stage(7); }}
}};
static_assert(sizeof(Payload) == 8 && offsetof(Payload, tag) == 4, "CG pads read code/tag at +0/+4");
struct Guard {{ int stage; ~Guard() {{ cg_stage(stage); }} }};
extern "C" int cxx_callee(int x) {{
  cg_stage(5);
  Guard g{{6}};
  if (x & 1) throw Payload(x);
  return x * 3 + 77;
}}
extern "C" int cxx_first(int x) {{
  cg_stage(8);
  if (x & 1) throw Payload(x);
  return x / 2;
}}
struct Case {{ const char* name; int (*fn)(int); }};
static const Case kCases[] = {{
  {{"tc_catch", tc_catch}}, {{"tc_cleanup", tc_cleanup}}, {{"tc_nested", tc_nested}},
  {{"tc_mid", tc_mid}}, {{"tc_through", tc_through}}, {{"tc_merged", tc_merged}},
  {{"tc_early", tc_early}},
}};
static void run_case(const Case& c, int x) {{
  g_nstages = 0; g_cleanups = 0; g_cleanup_sum = 0; g_obs_set = 0;
  g_payload_ctor = 0; g_payload_dtor = 0;
  int returned = 0, ret = 0, caught = 0, caught_code = 0, caught_tag = 0;
  try {{
    Guard caller{{98}};
    ret = c.fn(x);
    returned = 1;
  }} catch (const Payload& p) {{
    cg_stage(99); caught = 1; caught_code = p.code; caught_tag = p.tag;
  }} catch (...) {{
    cg_stage(99); caught = 2;
  }}
  printf("%s x=%d ret=", c.name, x);
  if (returned) printf("%d", ret); else printf("-");
  printf(" caught=");
  if (caught == 1) printf("%d:%d", caught_code, caught_tag);
  else printf(caught == 2 ? "foreign" : "-");
  printf(" obs=");
  if (g_obs_set) printf("%d:%d", g_obs_code, g_obs_tag); else printf("-");
  printf(" stages=");
  for (int i = 0; i < g_nstages; ++i) printf(i ? ",%d" : "%d", g_stages[i]);
  printf(" cleanup=%d/%lld payload=%d/%d uncaught=%d current=%d\n", g_cleanups, g_cleanup_sum,
         g_payload_ctor, g_payload_dtor, std::uncaught_exceptions(),
         std::current_exception() ? 1 : 0);
  fflush(stdout);
}}
int main(int argc, char** argv) {{
  // The mutation controls abort on purpose; skip the host's core handler.
  prctl(PR_SET_DUMPABLE, 0, 0, 0, 0);
  static const int xs[] = {{{xs}}};
  if (argc == 3) {{
    for (const Case& c : kCases)
      if (!strcmp(c.name, argv[1])) {{ run_case(c, atoi(argv[2])); return 0; }}
    return 3;
  }}
  for (const Case& c : kCases)
    for (int x : xs) run_case(c, x);
  return 0;
}}
"#,
            tag = PAYLOAD_TAG,
            xs = xs_list(),
        )
    }

    /// Rust caller and callee around the Rust-personality CG frames, catching
    /// with `catch_unwind` a real panic raised by `panic_any`.
    fn rust_harness() -> String {
        format!(
            r#"use std::cell::{{Cell, RefCell}};
use std::panic::{{self, AssertUnwindSafe}};

thread_local! {{
    static STAGES: RefCell<Vec<i32>> = const {{ RefCell::new(Vec::new()) }};
    static CLEANUPS: Cell<(i32, i64)> = const {{ Cell::new((0, 0)) }};
    static HOOK: Cell<i32> = const {{ Cell::new(0) }};
}}

fn stage(s: i32) {{
    STAGES.with(|v| v.borrow_mut().push(s));
}}

struct Payload {{
    code: i32,
    tag: i32,
}}

impl Drop for Payload {{
    fn drop(&mut self) {{
        stage(7);
    }}
}}

struct Guard(i32);

impl Drop for Guard {{
    fn drop(&mut self) {{
        stage(self.0);
    }}
}}

#[no_mangle]
pub extern "C" fn rs_stage(s: i32) {{
    stage(s);
}}

#[no_mangle]
pub extern "C" fn rs_cleanup(x: i32) {{
    CLEANUPS.with(|c| {{
        let (n, sum) = c.get();
        c.set((n + 1, sum + i64::from(x)));
    }});
}}

#[no_mangle]
pub extern "C-unwind" fn rs_callee(x: i32) -> i32 {{
    stage(5);
    let _guard = Guard(6);
    if x & 1 != 0 {{
        panic::panic_any(Payload {{ code: x, tag: {tag} }});
    }}
    x.wrapping_mul(3).wrapping_add(77)
}}

#[no_mangle]
pub extern "C-unwind" fn rs_first(x: i32) -> i32 {{
    stage(8);
    if x & 1 != 0 {{
        panic::panic_any(Payload {{ code: x, tag: {tag} }});
    }}
    x / 2
}}

extern "C-unwind" {{
    fn tr_cleanup(x: i32) -> i32;
    fn tr_mid(x: i32) -> i32;
    fn tr_nested(x: i32) -> i32;
    fn tr_through(x: i32) -> i32;
    fn tr_merged(x: i32) -> i32;
    fn tr_early(x: i32) -> i32;
}}

extern "C" {{
    fn prctl(option: i32, ...) -> i32;
}}

/// `PR_SET_DUMPABLE`: the mutation controls abort on purpose.
const PR_SET_DUMPABLE: i32 = 4;

type Entry = unsafe extern "C-unwind" fn(i32) -> i32;

fn run(name: &str, f: Entry, x: i32) {{
    STAGES.with(|v| v.borrow_mut().clear());
    CLEANUPS.with(|c| c.set((0, 0)));
    HOOK.with(|h| h.set(0));
    let result = panic::catch_unwind(AssertUnwindSafe(|| {{
        let _guard = Guard(98);
        unsafe {{ f(x) }}
    }}));
    let (ret, caught) = match result {{
        Ok(r) => (r.to_string(), "-".to_string()),
        Err(payload) => {{
            stage(99);
            match payload.downcast::<Payload>() {{
                Ok(p) => {{
                    let text = format!("{{}}:{{}}", p.code, p.tag);
                    drop(p);
                    ("-".to_string(), text)
                }}
                Err(_) => ("-".to_string(), "foreign".to_string()),
            }}
        }}
    }};
    let stages = STAGES.with(|v| {{
        v.borrow().iter().map(i32::to_string).collect::<Vec<_>>().join(",")
    }});
    let (n, sum) = CLEANUPS.with(Cell::get);
    println!(
        "{{name}} x={{x}} ret={{ret}} caught={{caught}} stages={{stages}} cleanup={{n}}/{{sum}} hook={{}}",
        HOOK.with(Cell::get)
    );
}}

fn main() {{
    unsafe {{ prctl(PR_SET_DUMPABLE, 0u64) }};
    panic::set_hook(Box::new(|_| HOOK.with(|h| h.set(h.get() + 1))));
    let cases: [(&str, Entry); 6] = [
        ("tr_cleanup", tr_cleanup),
        ("tr_mid", tr_mid),
        ("tr_nested", tr_nested),
        ("tr_through", tr_through),
        ("tr_merged", tr_merged),
        ("tr_early", tr_early),
    ];
    let args: Vec<String> = std::env::args().collect();
    if args.len() == 3 {{
        let x: i32 = args[2].parse().unwrap();
        let (name, f) = cases.iter().find(|(name, _)| *name == args[1]).unwrap();
        run(name, *f, x);
        return;
    }}
    for (name, f) in cases {{
        for x in [{xs}] {{
            run(name, f, x);
        }}
    }}
}}
"#,
            tag = PAYLOAD_TAG,
            xs = xs_list(),
        )
    }

    // -----------------------------------------------------------------------
    // Processes
    // -----------------------------------------------------------------------

    /// A scratch directory, removed when the test ends; kept (and named) when
    /// the test fails only while `TRUST_CG_KEEP_TEST_OBJECTS` is set.
    struct Scratch(PathBuf);

    impl Scratch {
        fn new(label: &str) -> Self {
            Self(crate::fresh_dir::create(&format!("trust-cg-eh-linux-{label}-")).keep())
        }

        fn path(&self, name: &str) -> PathBuf {
            self.0.join(name)
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            if std::thread::panicking()
                && std::env::var_os(crate::fresh_dir::KEEP_ON_FAILURE).is_some()
            {
                eprintln!("kept EH scratch directory {}", self.0.display());
            } else {
                let _ = fs::remove_dir_all(&self.0);
            }
        }
    }

    struct Outcome {
        code: Option<i32>,
        signal: Option<i32>,
        stdout: String,
        stderr: String,
    }

    fn run(command: &mut Command, budget: Duration) -> Outcome {
        let result = process::command_output_with_timeout(command, process::exec_timeout(budget))
            .unwrap_or_else(|error| panic!("launch {command:?}: {error}"));
        assert!(
            !result.timed_out,
            "{command:?} exceeded its polling deadline\nstderr: {}",
            String::from_utf8_lossy(&result.output.stderr)
        );
        Outcome {
            code: result.output.status.code(),
            signal: result.output.status.signal(),
            stdout: String::from_utf8_lossy(&result.output.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&result.output.stderr).into_owned(),
        }
    }

    /// Run a tool that must succeed; return its stdout.
    fn tool(command: &mut Command) -> String {
        let outcome = run(command, Duration::from_secs(120));
        assert_eq!(
            outcome.code,
            Some(0),
            "{command:?} failed\nstdout: {}\nstderr: {}",
            outcome.stdout,
            outcome.stderr
        );
        outcome.stdout
    }

    fn manifest_dir() -> &'static Path {
        Path::new(env!("CARGO_MANIFEST_DIR"))
    }

    /// A host tool without the TRUST_CG_*/TCG_* controls the Trust compiler
    /// (the installed package's `trustc`, used in its explicit unverified
    /// lane) refuses to run under; a gate may export them to this test.
    fn host_tool(name: &str) -> Command {
        let mut command = Command::new(name);
        for (key, _) in std::env::vars_os() {
            let key_text = key.to_string_lossy();
            if key_text.starts_with("TRUST_CG_") || key_text.starts_with("TCG_") {
                command.env_remove(&key);
            }
        }
        command
    }

    /// Record, once per process, which host tools produced the evidence.
    fn record_tools() {
        static ONCE: Once = Once::new();
        ONCE.call_once(|| {
            for (name, args, lines) in [
                ("g++", &["--version"][..], 1),
                ("cc", &["--version"][..], 1),
                ("readelf", &["--version"][..], 1),
                ("trustc", &["-vV"][..], 7),
            ] {
                let text = tool(host_tool(name).args(args).current_dir(manifest_dir()));
                let text: Vec<_> = text.lines().take(lines).collect();
                eprintln!("host tool {name}: {}", text.join(" | "));
            }
        });
    }

    struct Built {
        scratch: Scratch,
        object: PathBuf,
        exe: PathBuf,
    }

    /// Compile the C++ module at `level` and link it FIRST (so its weak
    /// `DW.ref` slot is the one the link keeps) with the C++ driver.
    fn build_cxx(level: OptLevel) -> Built {
        record_tools();
        let scratch = Scratch::new(&format!("cxx-{level:?}"));
        let object = scratch.path("cg_cxx.o");
        fs::write(&object, compile(&cxx_module(), level)).unwrap();
        let driver = scratch.path("driver.cpp");
        fs::write(&driver, cxx_driver()).unwrap();
        let exe = scratch.path("eh_cxx");
        tool(
            Command::new("g++")
                .args(["-O2", "-Wl,-z,noexecstack"])
                .arg(&object)
                .arg(&driver)
                .arg("-o")
                .arg(&exe),
        );
        Built {
            scratch,
            object,
            exe,
        }
    }

    /// Compile the Rust module at `level` and link it into a Rust binary
    /// built by the checkout's `rustc` at the same optimization level.
    fn build_rust(level: OptLevel) -> Built {
        record_tools();
        let scratch = Scratch::new(&format!("rust-{level:?}"));
        let object = scratch.path("cg_rust.o");
        fs::write(&object, compile(&rust_module(), level)).unwrap();
        let harness = scratch.path("harness.rs");
        fs::write(&harness, rust_harness()).unwrap();
        let exe = scratch.path("eh_rust");
        let opt = match level {
            OptLevel::O0 => "0",
            OptLevel::O1 => "1",
            OptLevel::O2 => "2",
            _ => "3",
        };
        tool(
            host_tool("trustc")
                .current_dir(manifest_dir())
                .arg("-Ztrust-verify=off")
                .args(["--edition", "2021", "--crate-type", "bin"])
                .args(["--crate-name", "eh_linux_harness"])
                .args(["-C", &format!("opt-level={opt}"), "-C", "panic=unwind"])
                .arg(&harness)
                .arg("-o")
                .arg(&exe)
                .arg("-C")
                .arg(format!("link-arg={}", object.display())),
        );
        Built {
            scratch,
            object,
            exe,
        }
    }

    fn assert_lines(label: &str, observed: &str, expected: &[String]) {
        let observed: Vec<&str> = observed.lines().collect();
        for (index, want) in expected.iter().enumerate() {
            assert_eq!(
                observed.get(index).copied(),
                Some(want.as_str()),
                "{label}: line {index} differs from the model"
            );
        }
        assert_eq!(observed.len(), expected.len(), "{label}: extra output");
    }

    // -----------------------------------------------------------------------
    // Execution rows
    // -----------------------------------------------------------------------

    /// C++ -> CG -> C++ at O0-O3: catch-all with payload read in the CG pad,
    /// cleanup then resume to the C++ catch, a CG catch around a CG cleanup
    /// frame, and unwinding through a plain CG frame to C++ and CG handlers.
    #[test]
    fn cxx_exceptions_run_cg_landing_pads_at_o0_to_o3() {
        let expected: Vec<String> = CXX_FUNCTIONS
            .iter()
            .flat_map(|spec| XS.iter().map(move |x| cxx_expected(spec.name, *x)))
            .collect();
        let throws = expected
            .iter()
            .filter(|line| line.contains(" payload=1/1 "))
            .count();
        // Early-throw calls whose exception must pass the CG frame's pad.
        let passed = expected
            .iter()
            .filter(|line| line.starts_with("tc_early ") && line.contains(" stages=60,8,98,"))
            .count();
        let mut calls = 0;
        for level in LEVELS {
            let built = build_cxx(level);
            let outcome = run(&mut Command::new(&built.exe), Duration::from_secs(20));
            assert_eq!(
                (outcome.code, outcome.signal),
                (Some(0), None),
                "{level:?}: driver failed\nstdout: {}\nstderr: {}",
                outcome.stdout,
                outcome.stderr
            );
            assert_lines(&format!("C++ {level:?}"), &outcome.stdout, &expected);
            calls += expected.len();
        }
        println!(
            "EH_LINUX_CXX calls={calls} exceptions={} past_pad={} levels=4",
            LEVELS.len() * throws,
            LEVELS.len() * passed
        );
    }

    /// Rust -> CG -> Rust at O0-O3: a real panic (panic hook, payload `Drop`,
    /// guard drops) resumes through CG cleanup pads and a plain CG frame to
    /// `catch_unwind` under `rust_eh_personality`.
    #[test]
    fn rust_panics_run_cg_cleanup_pads_at_o0_to_o3() {
        let expected: Vec<String> = RUST_FUNCTIONS
            .iter()
            .flat_map(|spec| XS.iter().map(move |x| rust_expected(spec.name, *x)))
            .collect();
        let throws = expected
            .iter()
            .filter(|line| line.ends_with(" hook=1"))
            .count();
        // Early-throw calls whose panic must pass the CG frame's cleanup.
        let passed = expected
            .iter()
            .filter(|line| line.starts_with("tr_early ") && line.contains(" stages=60,8,98,"))
            .count();
        let mut calls = 0;
        for level in LEVELS {
            let built = build_rust(level);
            let outcome = run(&mut Command::new(&built.exe), Duration::from_secs(20));
            assert_eq!(
                (outcome.code, outcome.signal),
                (Some(0), None),
                "{level:?}: harness failed\nstdout: {}\nstderr: {}",
                outcome.stdout,
                outcome.stderr
            );
            assert_lines(&format!("Rust {level:?}"), &outcome.stdout, &expected);
            calls += expected.len();
        }
        println!(
            "EH_LINUX_RUST calls={calls} panics={} past_pad={} levels=4",
            LEVELS.len() * throws,
            LEVELS.len() * passed
        );
    }

    // -----------------------------------------------------------------------
    // Independent tool readback
    // -----------------------------------------------------------------------

    struct Section {
        name: String,
        addr: u64,
        offset: u64,
        size: u64,
    }

    /// Linked-image facts read by GNU readelf.
    struct Image {
        sections: Vec<Section>,
        symbols: BTreeMap<String, (u64, u64)>,
        /// Dynamic relocations: offset -> (type, symbol, addend).
        relocs: BTreeMap<u64, (String, String, u64)>,
    }

    fn hex(text: &str) -> u64 {
        u64::from_str_radix(text.trim_start_matches("0x"), 16)
            .unwrap_or_else(|_| panic!("not hex: {text}"))
    }

    fn read_image(exe: &Path) -> Image {
        let text = tool(
            Command::new("readelf")
                .env("LC_ALL", "C")
                .args(["-W", "-S", "-s", "-r"])
                .arg(exe),
        );
        let mut sections = Vec::new();
        let mut symbols = BTreeMap::new();
        let mut relocs = BTreeMap::new();
        for line in text.lines() {
            let columns: Vec<&str> = line.split_whitespace().collect();
            if line.trim_start().starts_with('[')
                && let Some(close) = line.find("] ")
            {
                let rest: Vec<&str> = line[close + 2..].split_whitespace().collect();
                if rest.len() >= 5 && rest[0] != "NULL" && rest[0] != "Name" {
                    sections.push(Section {
                        name: rest[0].to_owned(),
                        addr: hex(rest[2]),
                        offset: hex(rest[3]),
                        size: hex(rest[4]),
                    });
                }
                continue;
            }
            if columns.len() == 8
                && columns[0].ends_with(':')
                && columns[6] != "UND"
                && matches!(columns[3], "FUNC" | "OBJECT")
            {
                let size = if columns[2].starts_with("0x") {
                    hex(columns[2])
                } else {
                    columns[2].parse().unwrap()
                };
                let name = columns[7].split('@').next().unwrap().to_owned();
                symbols.entry(name).or_insert((hex(columns[1]), size));
                continue;
            }
            if columns.len() >= 4 && columns[2].starts_with("R_AARCH64_") {
                let offset = hex(columns[0]);
                let row = if columns[2] == "R_AARCH64_RELATIVE" {
                    (columns[2].to_owned(), String::new(), hex(columns[3]))
                } else if columns.len() == 7 {
                    let symbol = columns[4].split('@').next().unwrap().to_owned();
                    (columns[2].to_owned(), symbol, hex(columns[6]))
                } else {
                    continue;
                };
                relocs.insert(offset, row);
            }
        }
        Image {
            sections,
            symbols,
            relocs,
        }
    }

    /// An FDE as llvm-dwarfdump decodes it.
    struct LlvmFde {
        cie: u64,
        start: u64,
        end: u64,
        lsda: Option<u64>,
    }

    struct LlvmFrames {
        /// CIE offset -> (augmentation, personality address).
        cies: BTreeMap<u64, (String, Option<u64>)>,
        fdes: Vec<LlvmFde>,
    }

    /// `.eh_frame` as `llvm-dwarfdump --eh-frame` decodes it.
    fn llvm_frames(exe: &Path) -> LlvmFrames {
        let text = llvm_tools::run_llvm("llvm-dwarfdump", &["--eh-frame"], exe);
        let mut cies = BTreeMap::new();
        let mut fdes: Vec<LlvmFde> = Vec::new();
        let mut current_cie = None;
        for line in text.lines() {
            let columns: Vec<&str> = line.split_whitespace().collect();
            if columns.len() >= 4 && columns[3] == "CIE" {
                let offset = hex(columns[0]);
                cies.insert(offset, (String::new(), None));
                current_cie = Some(offset);
            } else if columns.len() >= 6 && columns[3] == "FDE" {
                current_cie = None;
                let (start, end) = columns[5]
                    .trim_start_matches("pc=")
                    .split_once("...")
                    .unwrap();
                fdes.push(LlvmFde {
                    cie: hex(columns[4].trim_start_matches("cie=")),
                    start: hex(start),
                    end: hex(end),
                    lsda: None,
                });
            } else if let Some(value) = line.trim().strip_prefix("Augmentation:") {
                if let Some(cie) = current_cie {
                    cies.get_mut(&cie).unwrap().0 = value.trim().trim_matches('"').to_owned();
                }
            } else if let Some(value) = line.trim().strip_prefix("Personality Address:") {
                cies.get_mut(&current_cie.unwrap()).unwrap().1 = Some(hex(value.trim()));
            } else if let Some(value) = line.trim().strip_prefix("LSDA Address:") {
                fdes.last_mut().unwrap().lsda = Some(hex(value.trim()));
            }
        }
        LlvmFrames { cies, fdes }
    }

    /// A CIE or FDE as GNU `readelf --debug-dump=frames` prints it.
    struct GnuFrame {
        kind: String,
        range: Option<(u64, u64)>,
        augmentation_data: Vec<u8>,
    }

    fn gnu_frames(exe: &Path) -> BTreeMap<u64, GnuFrame> {
        let text = tool(
            Command::new("readelf")
                .env("LC_ALL", "C")
                .args(["-W", "--debug-dump=frames"])
                .arg(exe),
        );
        let mut rows = BTreeMap::new();
        let mut current = None;
        for line in text.lines() {
            let columns: Vec<&str> = line.split_whitespace().collect();
            if columns.len() >= 4 && matches!(columns[3], "CIE" | "FDE") {
                let offset = hex(columns[0]);
                let range = columns
                    .iter()
                    .find_map(|c| c.strip_prefix("pc="))
                    .map(|pc| {
                        let (start, end) = pc.split_once("..").unwrap();
                        (hex(start), hex(end))
                    });
                rows.insert(
                    offset,
                    GnuFrame {
                        kind: columns[3].to_owned(),
                        range,
                        augmentation_data: Vec::new(),
                    },
                );
                current = Some(offset);
            } else if let Some(data) = line.trim().strip_prefix("Augmentation data:") {
                rows.get_mut(&current.unwrap()).unwrap().augmentation_data = data
                    .split_whitespace()
                    .map(|b| u8::from_str_radix(b, 16).unwrap())
                    .collect();
            }
        }
        rows
    }

    /// Direct calls in each named function, as `llvm-objdump` disassembles
    /// the linked image: function -> [(absolute address, callee)].
    fn disassembled_calls(exe: &Path, names: &[&str]) -> BTreeMap<String, Vec<(u64, String)>> {
        let filter = format!("--disassemble-symbols={}", names.join(","));
        let text =
            // `--no-debuginfod`: an inherited DEBUGINFOD_URLS otherwise makes
            // each run wait on network symbol lookups for the C++ runtime.
            llvm_tools::run_llvm(
                "llvm-objdump",
                &["-d", "--no-show-raw-insn", "--no-debuginfod", &filter],
                exe,
            );
        let mut calls: BTreeMap<String, Vec<(u64, String)>> = BTreeMap::new();
        let mut current = None;
        for line in text.lines() {
            if let Some(header) = line.strip_suffix(">:")
                && let Some((_, name)) = header.split_once(" <")
            {
                current = Some(name.to_owned());
                calls.entry(name.to_owned()).or_default();
                continue;
            }
            let Some((address, rest)) = line.split_once(':') else {
                continue;
            };
            if rest.split_whitespace().next() != Some("bl") {
                continue;
            }
            let target = rest
                .split_once('<')
                .and_then(|(_, target)| target.trim_end().strip_suffix('>'))
                .unwrap_or_else(|| panic!("bl without a symbolic target: {line}"));
            calls
                .get_mut(current.as_ref().expect("bl before a function header"))
                .unwrap()
                .push((
                    hex(address.trim()),
                    target.trim_end_matches("@plt").to_owned(),
                ));
        }
        calls
    }

    /// One CG function's LSDA in the linked image.
    struct LinkedLsda {
        file_offset: usize,
        lsda: Lsda,
        invoke_row: Option<(usize, CallSite)>,
        /// The function's direct calls, function relative, in address order.
        calls: Vec<CallInsn>,
    }

    /// GNU readelf relocation rows (whitespace columns) of one section.
    fn relocation_rows(readelf: &str, section: &str) -> Vec<Vec<String>> {
        let header = format!("Relocation section '{section}'");
        let mut inside = false;
        let mut rows = Vec::new();
        for line in readelf.lines() {
            if line.starts_with("Relocation section '") {
                inside = line.starts_with(&header);
                continue;
            }
            let mut columns: Vec<String> = line.split_whitespace().map(str::to_owned).collect();
            if !inside || columns.len() < 6 || !columns[2].starts_with("R_AARCH64_") {
                continue;
            }
            // A nameless (section) symbol prints no name column.
            if columns.len() == 6 && columns[4] == "+" {
                columns.insert(4, String::new());
            }
            rows.push(columns);
        }
        rows
    }

    /// GNU readelf symbol index -> relocation target name: the symbol's
    /// name, or for an `STT_SECTION` symbol the name of its section.
    fn relocation_targets(readelf: &str) -> BTreeMap<u64, String> {
        let mut sections = BTreeMap::new();
        let mut symbols = BTreeMap::new();
        for line in readelf.lines() {
            let columns: Vec<&str> = line.split_whitespace().collect();
            if line.trim_start().starts_with('[')
                && let Some(close) = line.find(']')
                && let Ok(index) = line.trim_start()[1..]
                    .split(']')
                    .next()
                    .unwrap()
                    .trim()
                    .parse::<u64>()
            {
                let name = line[close + 1..].split_whitespace().next().unwrap_or("");
                sections.insert(index, name.to_owned());
                continue;
            }
            if columns.len() >= 7
                && let Some(index) = columns[0].strip_suffix(':')
                && let Ok(index) = index.parse::<u64>()
            {
                let name = columns.get(7).copied().unwrap_or("");
                symbols.insert(
                    index,
                    (
                        columns[3].to_owned(),
                        columns[6].to_owned(),
                        name.to_owned(),
                    ),
                );
            }
        }
        symbols
            .into_iter()
            .map(|(index, (kind, ndx, name))| {
                let target = if kind == "SECTION" {
                    sections[&ndx.parse::<u64>().expect("section symbol index")].clone()
                } else {
                    name
                };
                (index, target)
            })
            .collect()
    }

    /// Read the relocatable object with GNU readelf and the linked image with
    /// GNU readelf, llvm-dwarfdump and llvm-objdump, and check every CG
    /// function's unwind and exception tables. Returns each LSDA's location.
    fn check_linked_tables(
        built: &Built,
        specs: &[FnSpec],
        personality: &str,
    ) -> BTreeMap<String, LinkedLsda> {
        // The relocatable object, as GNU readelf reads it. Relocation targets
        // are resolved through the symbol index in `r_info` and, for section
        // symbols, the section they anchor.
        let object = tool(
            Command::new("readelf")
                .env("LC_ALL", "C")
                .args(["-W", "-S", "-r", "-s", "--debug-dump=frames"])
                .arg(&built.object),
        );
        let slot = format!("DW.ref.{personality}");
        let targets = relocation_targets(&object);
        let target_of = |row: &[String]| targets[&(hex(&row[1]) >> 32)].clone();
        let mut eh_targets: Vec<String> = relocation_rows(&object, ".rela.eh_frame")
            .iter()
            .map(|row| {
                assert_eq!(row[2], "R_AARCH64_PREL32", ".eh_frame relocation kind");
                target_of(row)
            })
            .collect();
        eh_targets.sort();
        let mut expected = vec![slot.clone()];
        expected.extend(std::iter::repeat_n(
            ".gcc_except_table".to_owned(),
            specs.len(),
        ));
        expected.extend(std::iter::repeat_n(".text".to_owned(), specs.len()));
        expected.sort();
        assert_eq!(
            eh_targets, expected,
            "one personality, one PC-begin and one LSDA relocation per FDE:\n{object}"
        );
        let slot_rows = relocation_rows(&object, &format!(".rela.data.{slot}"));
        assert!(
            slot_rows.len() == 1
                && slot_rows[0][2] == "R_AARCH64_ABS64"
                && target_of(&slot_rows[0]) == personality,
            "{slot} must hold the personality's address:\n{object}"
        );
        assert!(
            object.contains("Augmentation:          \"zPLR\"")
                && object.contains("Augmentation data:     9b "),
            "GNU readelf must decode a zPLR CIE with an indirect personality:\n{object}"
        );

        // The linked image.
        let image = read_image(&built.exe);
        let llvm = llvm_frames(&built.exe);
        let gnu = gnu_frames(&built.exe);
        let section = |name: &str| {
            image
                .sections
                .iter()
                .find(|s| s.name == name)
                .unwrap_or_else(|| panic!("linked image has no {name}"))
        };
        let eh_frame = section(".eh_frame");
        let except = section(".gcc_except_table");
        let (slot_address, _) = image.symbols[&slot];
        match image.relocs.get(&slot_address) {
            Some((kind, symbol, 0))
                if kind == "R_AARCH64_ABS64" || kind == "R_AARCH64_GLOB_DAT" =>
            {
                assert_eq!(symbol, personality, "{slot} is bound to the personality");
            }
            Some((kind, _, addend)) if kind == "R_AARCH64_RELATIVE" => {
                assert_eq!(
                    *addend, image.symbols[personality].0,
                    "{slot} holds the linked personality's address"
                );
            }
            other => panic!("{slot} at {slot_address:#x} has no personality relocation: {other:?}"),
        }
        let bytes = fs::read(&built.exe).unwrap();
        let names: Vec<&str> = specs.iter().map(|s| s.name).collect();
        let calls = disassembled_calls(&built.exe, &names);
        let mut out = BTreeMap::new();
        for spec in specs {
            let name = spec.name;
            let (start, size) = image.symbols[name];
            let fde: Vec<_> = llvm.fdes.iter().filter(|f| f.start == start).collect();
            assert_eq!(fde.len(), 1, "{name}: one FDE in llvm-dwarfdump");
            let fde = fde[0];
            assert_eq!(fde.end, start + size, "{name}: FDE covers the body");
            let (augmentation, personality_address) = &llvm.cies[&fde.cie];
            assert_eq!(augmentation, "zPLR", "{name}: CIE augmentation");
            assert_eq!(
                *personality_address,
                Some(slot_address),
                "{name}: personality"
            );
            let lsda_address = fde.lsda.expect("EH FDE carries an LSDA");

            // GNU readelf decodes the same FDE and CIE; its raw augmentation
            // bytes give the same LSDA pointer and the P/L/R encodings.
            let (fde_offset, gnu_fde) = gnu
                .iter()
                .find(|(_, row)| row.kind == "FDE" && row.range == Some((start, fde.end)))
                .unwrap_or_else(|| panic!("{name}: GNU readelf FDE"));
            let data = &gnu_fde.augmentation_data;
            assert_eq!(data.len(), 4, "{name}: FDE augmentation is one sdata4");
            // length, CIE pointer, PC begin, PC range, augmentation length.
            let field = eh_frame.addr + fde_offset + 17;
            let delta = i32::from_le_bytes(data[..4].try_into().unwrap());
            assert_eq!(
                field.wrapping_add_signed(i64::from(delta)),
                lsda_address,
                "{name}: GNU and LLVM readers agree on the LSDA"
            );
            let cie_data = &gnu[&fde.cie].augmentation_data;
            assert_eq!(
                (cie_data[0], cie_data[5], cie_data[6]),
                (
                    DW_EH_PE_INDIRECT_PCREL_SDATA4,
                    DW_EH_PE_PCREL_SDATA4,
                    DW_EH_PE_PCREL_SDATA4
                ),
                "{name}: CIE P/L/R encodings"
            );

            assert!(
                (except.addr..except.addr + except.size).contains(&lsda_address),
                "{name}: LSDA lies in .gcc_except_table"
            );
            let file_offset = (except.offset + lsda_address - except.addr) as usize;
            let lsda = Lsda::decode(&bytes[file_offset..])
                .unwrap_or_else(|error| panic!("{name}: {error}"));
            assert_eq!(
                lsda.encode(),
                bytes[file_offset..file_offset + lsda.len],
                "{name}: linked LSDA re-encodes byte for byte"
            );
            let call_insns: Vec<CallInsn> = calls[name]
                .iter()
                .map(|(address, callee)| CallInsn {
                    offset: address - start,
                    target: callee.clone(),
                })
                .collect();
            let invoke_row = check_function_table(spec, size, &call_insns, &lsda)
                .unwrap_or_else(|error| panic!("linked image: {error}"));
            out.insert(
                name.to_owned(),
                LinkedLsda {
                    file_offset,
                    lsda,
                    invoke_row,
                    calls: call_insns,
                },
            );
        }
        out
    }

    /// GNU readelf, llvm-dwarfdump and llvm-objdump read the relocatable
    /// objects and the linked images at O0-O3: the CIE is zPLR with the
    /// personality through its `DW.ref` slot (bound to the personality in the
    /// image), both readers agree on each FDE's range and LSDA, and the LSDA
    /// rows cover each disassembled invoke with its landing pad.
    #[test]
    fn linked_eh_tables_read_back_by_gnu_and_llvm_tools_at_o0_to_o3() {
        let mut functions = 0;
        for level in LEVELS {
            let cxx = build_cxx(level);
            functions += check_linked_tables(&cxx, &CXX_FUNCTIONS, CXX_PERSONALITY).len();
            let rust = build_rust(level);
            functions += check_linked_tables(&rust, &RUST_FUNCTIONS, RUST_PERSONALITY).len();
        }
        assert_eq!(
            functions,
            LEVELS.len() * (CXX_FUNCTIONS.len() + RUST_FUNCTIONS.len())
        );
        println!("EH_LINUX_TOOL_READBACK functions={functions} levels=4");
    }

    // -----------------------------------------------------------------------
    // Negative controls
    // -----------------------------------------------------------------------

    /// Write a copy of the linked image with one LSDA replaced (zero padded
    /// to the original length) and return its path.
    fn mutant(built: &Built, label: &str, at: &LinkedLsda, lsda: Vec<u8>) -> PathBuf {
        assert!(
            lsda.len() <= at.lsda.len,
            "{label}: mutation must fit in place"
        );
        let mut bytes = fs::read(&built.exe).unwrap();
        let slot = &mut bytes[at.file_offset..at.file_offset + at.lsda.len];
        slot.fill(0);
        slot[..lsda.len()].copy_from_slice(&lsda);
        let path = built.scratch.path(label);
        write_executable(&path, &bytes);
        path
    }

    /// Write `bytes` to `path` as an executable from a child shell. A file
    /// this process opened for writing can fail to exec with ETXTBSY ("Text
    /// file busy"): another test thread that forks while the descriptor is
    /// open hands a copy to its child, which keeps it until that child
    /// execs. Writing through a child leaves no writable descriptor here.
    fn write_executable(path: &Path, bytes: &[u8]) {
        use std::io::Write as _;
        let mut child = Command::new("/bin/sh")
            .arg("-c")
            .arg("cat > \"$1\" && chmod 755 \"$1\"")
            .arg("sh")
            .arg(path)
            .stdin(std::process::Stdio::piped())
            .spawn()
            .expect("spawn /bin/sh to write the executable");
        child
            .stdin
            .take()
            .expect("writer stdin")
            .write_all(bytes)
            .expect("write the executable");
        assert!(
            child.wait().expect("wait for the writer").success(),
            "writing {}",
            path.display()
        );
    }

    /// For a merged function: move the invoke row's landing pad and action
    /// onto the row covering the function's first call to `stage_fn` (the
    /// call before the invoke in its trust-ir block), leaving the invoke's
    /// row with no handler. The encoding keeps its length.
    fn move_pad_to_earlier_call(at: &LinkedLsda, stage_fn: &str) -> Vec<u8> {
        let (invoke_index, invoke_row) = at.invoke_row.expect("merged function invokes");
        let earlier = at
            .calls
            .iter()
            .find(|call| call.target == stage_fn)
            .expect("the entry stage call");
        assert!(
            earlier.offset < invoke_row.start,
            "the entry stage call precedes the invoke"
        );
        let (index, row) = at
            .lsda
            .covering(earlier.offset)
            .expect("the earlier call is covered");
        assert!(
            index != invoke_index && row.lp == 0,
            "the earlier call has its own no-handler row"
        );
        let mut edited = at.lsda.clone();
        edited.call_sites[index].lp = invoke_row.lp;
        edited.call_sites[index].action = invoke_row.action;
        edited.call_sites[invoke_index].lp = 0;
        edited.call_sites[invoke_index].action = 0;
        let bytes = edited.encode();
        assert_eq!(bytes.len(), at.lsda.len, "moving the pad keeps the length");
        bytes
    }

    /// For an early-throw function: give the row covering its call to
    /// `first_fn` (a plain call before the invoke) the invoke row's landing
    /// pad and action, leaving the invoke's row as it is.
    fn copy_pad_to_earlier_call(at: &LinkedLsda, first_fn: &str) -> Vec<u8> {
        let (invoke_index, invoke_row) = at.invoke_row.expect("early function invokes");
        let earlier = at
            .calls
            .iter()
            .find(|call| call.target == first_fn)
            .unwrap_or_else(|| panic!("the call to {first_fn}"));
        assert!(
            earlier.offset < invoke_row.start,
            "the call to {first_fn} precedes the invoke"
        );
        let (index, row) = at
            .lsda
            .covering(earlier.offset)
            .expect("the earlier call is covered");
        assert!(
            index != invoke_index && row.lp == 0,
            "the earlier call has its own no-handler row"
        );
        let mut edited = at.lsda.clone();
        edited.call_sites[index].lp = invoke_row.lp;
        edited.call_sites[index].action = invoke_row.action;
        edited.encode()
    }

    fn run_one(exe: &Path, name: &str, x: i32) -> Outcome {
        run(
            Command::new(exe).args([name, &x.to_string()]),
            Duration::from_secs(20),
        )
    }

    /// Dropping the invoke's call-site row makes the personality terminate;
    /// retargeting its landing pad to the call's return address resumes the
    /// normal path with the exception still in flight. For the merged
    /// function, moving the pad onto the row of the call before the invoke
    /// loses the handler: the exception reaches the driver's catch. For the
    /// early-throw function, giving the earlier call's row the invoke's pad
    /// (the invoke's row unchanged) makes the CG catch-all catch an exception
    /// from the earlier call, which the unmutated image passes to the driver;
    /// the invoke's own exception is still caught as the model says. Each
    /// case uses an argument whose invoke throws (`x`); the unmutated image
    /// runs the same calls exactly as the model says.
    #[test]
    fn mutated_cxx_lsda_rows_terminate_or_take_the_wrong_path() {
        // Each (level, function) case runs the unmutated image once as its
        // reference, then two mutated images (dropped row, retargeted pad),
        // a merged function a third (pad moved to the earlier call) and an
        // early-throw function a fourth (pad copied to the earlier call).
        let (mut references, mut dropped_runs, mut retargeted_runs) = (0, 0, 0);
        let (mut moved_runs, mut copied_runs) = (0, 0);
        for level in LEVELS {
            let built = build_cxx(level);
            let tables = check_linked_tables(&built, &CXX_FUNCTIONS, CXX_PERSONALITY);
            for (name, x, normal_stages) in [
                ("tc_catch", 7, "1,5,6,2,98"),
                ("tc_cleanup", 7, "10,5,6,11,98"),
                ("tc_nested", 7, "20,10,5,6,12,21,98"),
                ("tc_through", 7, "40,5,6,41,98"),
                ("tc_merged", 7, "50,5,6,51,98"),
                ("tc_early", 2, "60,8,5,6,61,98"),
            ] {
                let at = &tables[name];
                let (index, row) = at.invoke_row.unwrap();
                let clean = run_one(&built.exe, name, x);
                assert_eq!(
                    clean.stdout.trim_end(),
                    cxx_expected(name, x),
                    "{level:?} {name}"
                );
                references += 1;

                let dropped = mutant(
                    &built,
                    &format!("{name}_dropped"),
                    at,
                    drop_row(&at.lsda, index),
                );
                let outcome = run_one(&dropped, name, x);
                assert_eq!(
                    (outcome.code, outcome.signal),
                    (None, Some(SIGABRT)),
                    "{level:?} {name}: a dropped invoke row must terminate\nstdout: {}\nstderr: {}",
                    outcome.stdout,
                    outcome.stderr
                );
                assert!(
                    outcome.stdout.is_empty()
                        && outcome
                            .stderr
                            .contains("terminate called after throwing an instance of 'Payload'"),
                    "{level:?} {name}: std::terminate names the in-flight payload\n\
                     stdout: {}\nstderr: {}",
                    outcome.stdout,
                    outcome.stderr
                );
                dropped_runs += 1;

                let retargeted = mutant(
                    &built,
                    &format!("{name}_retargeted"),
                    at,
                    retarget_row(&at.lsda, index, row.start + row.len),
                );
                let outcome = run_one(&retargeted, name, x);
                assert_eq!(
                    (outcome.code, outcome.signal),
                    (Some(0), None),
                    "{level:?} {name}: retargeted run\nstderr: {}",
                    outcome.stderr
                );
                let line = outcome.stdout.trim_end();
                assert_ne!(
                    line,
                    cxx_expected(name, x),
                    "{level:?} {name}: mutation had no effect"
                );
                assert!(
                    line.contains(&format!(" stages={normal_stages} "))
                        && line.ends_with("uncaught=1 current=0"),
                    "{level:?} {name}: expected the normal path with the exception in flight: \
                     {line}"
                );
                retargeted_runs += 1;

                let Some(&(_, entry)) = MERGED.iter().find(|(merged, _)| *merged == name) else {
                    continue;
                };
                let moved = mutant(
                    &built,
                    &format!("{name}_moved"),
                    at,
                    move_pad_to_earlier_call(at, "cg_stage"),
                );
                let outcome = run_one(&moved, name, x);
                assert_eq!(
                    (outcome.code, outcome.signal),
                    (Some(0), None),
                    "{level:?} {name}: moved-pad run\nstderr: {}",
                    outcome.stderr
                );
                assert_eq!(
                    outcome.stdout.trim_end(),
                    format!(
                        "{name} x={x} ret=- caught={x}:{PAYLOAD_TAG} obs=- \
                         stages={entry},5,6,98,99,7 cleanup=0/0 payload=1/1 uncaught=0 current=0"
                    ),
                    "{level:?} {name}: with the pad on the earlier call the invoke has no handler"
                );
                moved_runs += 1;
            }
            for &(name, first, entry) in EARLY.iter().filter(|(name, ..)| name.starts_with("tc_")) {
                let at = &tables[name];
                // The unmutated image passes the earlier call's exception on.
                let early_x = 7;
                let clean = run_one(&built.exe, name, early_x);
                assert_eq!(
                    clean.stdout.trim_end(),
                    cxx_expected(name, early_x),
                    "{level:?} {name}"
                );
                references += 1;
                let copied = mutant(
                    &built,
                    &format!("{name}_copied"),
                    at,
                    copy_pad_to_earlier_call(at, first),
                );
                let outcome = run_one(&copied, name, early_x);
                assert_eq!(
                    (outcome.code, outcome.signal),
                    (Some(0), None),
                    "{level:?} {name}: copied-pad run\nstderr: {}",
                    outcome.stderr
                );
                let line = outcome.stdout.trim_end();
                assert_ne!(
                    line,
                    cxx_expected(name, early_x),
                    "{level:?} {name}: mutant survived"
                );
                assert_eq!(
                    line,
                    format!(
                        "{name} x={early_x} ret={} caught=- obs={early_x}:{PAYLOAD_TAG} \
                         stages={entry},8,62,7,98 cleanup=0/0 payload=1/1 uncaught=0 current=0",
                        early_x + 5000
                    ),
                    "{level:?} {name}: with the pad on the earlier call the CG catch-all \
                     catches the earlier call's exception"
                );
                // The invoke's own exception is unaffected by the copy.
                let outcome = run_one(&copied, name, 2);
                assert_eq!(
                    outcome.stdout.trim_end(),
                    cxx_expected(name, 2),
                    "{level:?} {name}: the copy must not change the invoke's row"
                );
                copied_runs += 1;
            }
        }
        // Six functions with an invoke at four levels; one merged and one
        // early-throw function.
        assert_eq!(
            (
                dropped_runs,
                retargeted_runs,
                moved_runs,
                copied_runs,
                references
            ),
            (24, 24, 4, 4, 28)
        );
        println!(
            "EH_LINUX_CXX_MUTATIONS mutants={} dropped={dropped_runs} \
             retargeted={retargeted_runs} moved={moved_runs} copied={copied_runs} \
             unmutated_references={references}",
            dropped_runs + retargeted_runs + moved_runs + copied_runs
        );
    }

    /// The same controls for a Rust panic: a dropped row makes
    /// `rust_eh_personality` refuse to unwind (the process aborts), and a
    /// retargeted pad resumes the normal path, so the cleanup never runs and
    /// `catch_unwind` sees no panic. For the merged function, moving the pad
    /// onto the row of the call before the invoke skips the cleanup while the
    /// panic still reaches `catch_unwind`. For the early-throw function,
    /// giving the earlier call's row the invoke's pad runs this frame's
    /// cleanup for a panic from the earlier call, which the unmutated image
    /// passes by.
    #[test]
    fn mutated_rust_lsda_rows_abort_or_take_the_wrong_path() {
        // Each (level, function) case runs the unmutated image once as its
        // reference, then two mutated images (dropped row, retargeted pad),
        // the merged function a third (pad moved to the earlier call) and the
        // early-throw function a fourth (pad copied to the earlier call).
        let (mut references, mut dropped_runs, mut retargeted_runs) = (0, 0, 0);
        let (mut moved_runs, mut copied_runs) = (0, 0);
        for level in LEVELS {
            let built = build_rust(level);
            let tables = check_linked_tables(&built, &RUST_FUNCTIONS, RUST_PERSONALITY);
            for (name, x, normal_stages) in [
                ("tr_cleanup", 7, "10,5,6,11,98"),
                ("tr_merged", 7, "50,5,6,51,98"),
                ("tr_early", 2, "60,8,5,6,61,98"),
            ] {
                let at = &tables[name];
                let (index, row) = at.invoke_row.unwrap();
                let clean = run_one(&built.exe, name, x);
                assert_eq!(
                    clean.stdout.trim_end(),
                    rust_expected(name, x),
                    "{level:?} {name}"
                );
                references += 1;

                let dropped = mutant(
                    &built,
                    &format!("{name}_dropped"),
                    at,
                    drop_row(&at.lsda, index),
                );
                let outcome = run_one(&dropped, name, x);
                assert_eq!(
                    (outcome.code, outcome.signal),
                    (None, Some(SIGABRT)),
                    "{level:?}: a dropped invoke row must abort\nstdout: {}\nstderr: {}",
                    outcome.stdout,
                    outcome.stderr
                );
                // Phase 1 meets a PC outside every call-site row, so the
                // personality stops the search and std aborts the panic.
                assert!(
                    outcome.stdout.is_empty()
                        && outcome
                            .stderr
                            .contains("fatal runtime error: failed to initiate panic"),
                    "{level:?}: std must refuse the panic\nstdout: {}\nstderr: {}",
                    outcome.stdout,
                    outcome.stderr
                );
                dropped_runs += 1;

                let retargeted = mutant(
                    &built,
                    &format!("{name}_retargeted"),
                    at,
                    retarget_row(&at.lsda, index, row.start + row.len),
                );
                let outcome = run_one(&retargeted, name, x);
                assert_eq!(
                    (outcome.code, outcome.signal),
                    (Some(0), None),
                    "{level:?} {name}: retargeted run\nstderr: {}",
                    outcome.stderr
                );
                let line = outcome.stdout.trim_end();
                assert_ne!(
                    line,
                    rust_expected(name, x),
                    "{level:?} {name}: mutation had no effect"
                );
                assert!(
                    line.contains(&format!(
                        " caught=- stages={normal_stages} cleanup=0/0 hook=1"
                    )),
                    "{level:?} {name}: expected the normal path after the panic hook: {line}\nstderr: {}",
                    outcome.stderr
                );
                retargeted_runs += 1;

                let Some(&(_, entry)) = MERGED.iter().find(|(merged, _)| *merged == name) else {
                    continue;
                };
                let moved = mutant(
                    &built,
                    &format!("{name}_moved"),
                    at,
                    move_pad_to_earlier_call(at, "rs_stage"),
                );
                let outcome = run_one(&moved, name, x);
                assert_eq!(
                    (outcome.code, outcome.signal),
                    (Some(0), None),
                    "{level:?} {name}: moved-pad run\nstderr: {}",
                    outcome.stderr
                );
                assert_eq!(
                    outcome.stdout.trim_end(),
                    format!(
                        "{name} x={x} ret=- caught={x}:{PAYLOAD_TAG} stages={entry},5,6,98,99,7 \
                     cleanup=0/0 hook=1"
                    ),
                    "{level:?} {name}: with the pad on the earlier call the cleanup never runs"
                );
                moved_runs += 1;
            }
            for &(name, first, entry) in EARLY.iter().filter(|(name, ..)| name.starts_with("tr_")) {
                let at = &tables[name];
                // The unmutated image passes the earlier call's panic on.
                let early_x = 7;
                let clean = run_one(&built.exe, name, early_x);
                assert_eq!(
                    clean.stdout.trim_end(),
                    rust_expected(name, early_x),
                    "{level:?} {name}"
                );
                references += 1;
                let copied = mutant(
                    &built,
                    &format!("{name}_copied"),
                    at,
                    copy_pad_to_earlier_call(at, first),
                );
                let outcome = run_one(&copied, name, early_x);
                assert_eq!(
                    (outcome.code, outcome.signal),
                    (Some(0), None),
                    "{level:?} {name}: copied-pad run\nstderr: {}",
                    outcome.stderr
                );
                let line = outcome.stdout.trim_end();
                assert_ne!(
                    line,
                    rust_expected(name, early_x),
                    "{level:?} {name}: mutant survived"
                );
                // The pad ran (its cleanup call and stage 63) for the earlier
                // call's panic and resumed it to `catch_unwind`. The cleanup's
                // argument is whatever the pad reads at a PC it was not
                // compiled for, so only the call is required.
                let prefix = format!(
                    "{name} x={early_x} ret=- caught={early_x}:{PAYLOAD_TAG} \
                     stages={entry},8,63,98,99,7 cleanup=1/"
                );
                assert!(
                    line.starts_with(&prefix) && line.ends_with(" hook=1"),
                    "{level:?} {name}: with the pad on the earlier call the cleanup runs for \
                     the earlier call's panic: {line}"
                );
                // The invoke's own panic is unaffected by the copy.
                let outcome = run_one(&copied, name, 2);
                assert_eq!(
                    outcome.stdout.trim_end(),
                    rust_expected(name, 2),
                    "{level:?} {name}: the copy must not change the invoke's row"
                );
                copied_runs += 1;
            }
        }
        assert_eq!(
            (
                dropped_runs,
                retargeted_runs,
                moved_runs,
                copied_runs,
                references
            ),
            (12, 12, 4, 4, 16)
        );
        println!(
            "EH_LINUX_RUST_MUTATIONS mutants={} dropped={dropped_runs} \
             retargeted={retargeted_runs} moved={moved_runs} copied={copied_runs} \
             unmutated_references={references}",
            dropped_runs + retargeted_runs + moved_runs + copied_runs
        );
    }

    /// Undefined references a failed GNU link reports.
    fn undefined_references(stderr: &str) -> Vec<String> {
        let mut names: Vec<String> = stderr
            .lines()
            .filter_map(|line| line.split_once("undefined reference to `"))
            .map(|(_, rest)| rest.split('\'').next().unwrap().to_owned())
            .collect();
        names.sort();
        names.dedup();
        names
    }

    /// Without the personality's runtime the link fails naming exactly the
    /// personality: a C driver (no libstdc++) for the C++-personality object
    /// and for the Rust-personality object (no Rust std). The same C++ object
    /// links and runs with the C++ runtime.
    #[test]
    fn missing_personality_runtime_fails_the_link_by_name() {
        record_tools();
        let scratch = Scratch::new("personality");
        let c_driver = scratch.path("driver.c");
        fs::write(
            &c_driver,
            "#include <stdio.h>\n\
             int tc_cleanup(int);\n\
             int cxx_callee(int x) { return x * 3 + 77; }\n\
             void cg_stage(int s) { (void)s; }\n\
             void cg_cleanup(int x) { (void)x; }\n\
             int main(void) { printf(\"%d\\n\", tc_cleanup(2)); return 0; }\n",
        )
        .unwrap();
        let rust_driver = scratch.path("rust_driver.c");
        fs::write(
            &rust_driver,
            "#include <stdio.h>\n\
             int tr_cleanup(int);\n\
             int rs_callee(int x) { return x * 3 + 77; }\n\
             int rs_first(int x) { return x / 2; }\n\
             void rs_stage(int s) { (void)s; }\n\
             void rs_cleanup(int x) { (void)x; }\n\
             int main(void) { printf(\"%d\\n\", tr_cleanup(2)); return 0; }\n",
        )
        .unwrap();
        let mut refusals = 0;
        for level in [OptLevel::O0, OptLevel::O3] {
            let cxx = scratch.path(&format!("cleanup_only_{level:?}.o"));
            fs::write(&cxx, compile(&cleanup_only_module(), level)).unwrap();
            let rust = scratch.path(&format!("rust_{level:?}.o"));
            fs::write(&rust, compile(&rust_module(), level)).unwrap();
            for (object, driver, personality) in [
                (&cxx, &c_driver, CXX_PERSONALITY),
                (&rust, &rust_driver, RUST_PERSONALITY),
            ] {
                let outcome = run(
                    Command::new("cc")
                        .arg(driver)
                        .arg(object)
                        .arg("-o")
                        .arg(scratch.path("unlinkable")),
                    Duration::from_secs(60),
                );
                assert_ne!(
                    outcome.code,
                    Some(0),
                    "{level:?}: link without {personality} must fail"
                );
                assert_eq!(
                    undefined_references(&outcome.stderr),
                    [personality],
                    "{level:?}: the link must fail on exactly the personality\n{}",
                    outcome.stderr
                );
                refusals += 1;
            }
            // `g++` adds libstdc++ only when it links (not when a `-x c`
            // source is on its command line), so compile the C driver first.
            let driver_object = scratch.path("driver.o");
            tool(
                Command::new("cc")
                    .arg("-c")
                    .arg(&c_driver)
                    .arg("-o")
                    .arg(&driver_object),
            );
            let exe = scratch.path("linked");
            tool(
                Command::new("g++")
                    .arg(&driver_object)
                    .arg(&cxx)
                    .arg("-o")
                    .arg(&exe),
            );
            let outcome = run(&mut Command::new(&exe), Duration::from_secs(20));
            assert_eq!(
                (outcome.code, outcome.stdout.trim()),
                (Some(0), "84"),
                "{level:?}: with the C++ runtime the same object links and runs"
            );
        }
        println!("EH_LINUX_PERSONALITY_LINK_REFUSALS refusals={refusals}");
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

/// `translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &trust_ir::Module,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}
