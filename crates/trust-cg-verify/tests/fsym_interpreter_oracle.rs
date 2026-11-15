// Symbolic execution: differential soundness oracle against trust-ir's reference interpreter
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Differential soundness oracle for the bounded trust_ir fsym scanner.
//!
//! The ORACLE is trust-ir's reference interpreter (`trust_ir::Interpreter`, at
//! the exact trust-ir rev this workspace pins). For every function below the
//! test runs the interpreter on concrete inputs and scans the function with
//! `fsym_trust_ir::scan_module`. It FAILS when the interpreter reports
//! `UndefinedBehavior` on some input while fsym claims the function CLEAN:
//! scanned, with no diagnostic, Unknown or coverage error — for it AND every
//! bodied function it calls (a callee's UB is its own scan's obligation) —
//! either as scanned or after the bounded local solver proves its Unknowns
//! safe. That is the only direction checked: fsym may be imprecise (a
//! diagnostic or an Unknown where the interpreter runs clean), never unsound.
//! A scanner panic is a failure too.
//!
//! Two corpora feed it:
//!
//! * a REGRESSION corpus: every fail-open an adversarial review measured, each
//!   in the shape it was reported in. A shape the interpreter cannot execute
//!   (a `Ptr`-typed `icmp`, a nonzero `Ptr` constant, a call to a body-less
//!   declaration) is paired with an executable twin (the same comparison
//!   through `ptrtoint`, the same address through `inttoptr`, the `MemSet`
//!   instruction), and the interpreter must report UB on the twin; the
//!   original shape is checked against fsym alone.
//! * a GENERATED corpus: a deterministic seeded generator (SplitMix64, fixed
//!   seeds, no wall-clock or OS entropy) of small straight-line, branching and
//!   statically-looping functions over EVERY instruction the admission gate
//!   admits (`fsym_ub_map::FSYM_INST_VARIANTS`; the one exception is named in
//!   `NOT_GENERATED` with why) — allocations, GEPs, constant and cast
//!   pointers, address arithmetic and comparisons, loads/stores/atomics,
//!   shifts, divisions, bulk memory, deallocation, floats and every float
//!   cast, `Bool` extensions, vectors/arrays and their elements, enums (built
//!   by `Const` / `MakeAggregate`, or passed in) and tuples and their lanes,
//!   borrows, fat pointers, globals, sequences, `unreachable`, calls to a
//!   bodied callee and to an external — on no target, x86_64 or wasm32
//!   (`Usize` at 64 and 32 bits). A function taking pointers, an enum or a
//!   vector runs under harnesses that hand it interpreter-made arguments: an
//!   allocation (initialized or not, at its base or inside it), null, a freed
//!   block, an address naming no allocation. Proof annotations are generated
//!   on any pointer — a parameter a harness hands null or a freed block
//!   included: an annotation is a claim nothing checks, never a proof. The
//!   LAYOUT world (`layout_structs`) adds what the interpreter lays out
//!   differently from the native backends: `<4 x bool>`, structs with a
//!   declared size and field offsets (and GEP strides by them), a struct
//!   with padding stored whole and read back byte-wise, a zero-sized type
//!   aligned to 2^63 (allocated with no explicit alignment, and a global of
//!   it), GEP chains with a wide constant index (wasm32's address space,
//!   checked after the local solver too), and initialization masks that are
//!   not byte-exact: an enum stored with its variant untracked (a select on
//!   an input), an aggregate with padding stored at an offset fsym cannot
//!   decide, a whole-enum load over a tag written alone or rewritten, a copy
//!   from a source whose initialization fsym does not track (8192 bytes) or
//!   from an offset it cannot decide, a load at an undecided offset, a fill
//!   whose count is a select. One case in ~16 is FOCUSED: one or two of
//!   those probes over a `u8` parameter, small enough to be claimed clean,
//!   so each probe's verdict is seen on its own. At 64 bits one case in ~25
//!   also runs under a caller that breaks the BUDGET premise (a refused
//!   function placing one-byte allocations at 2^63 down to 2^4 or 2^12
//!   before the call): `f`'s placements rest on its callers'. At 32 bits a
//!   focused case may start with an END PROBE (an allocation, then a pointer
//!   at, across or before its end) that a caller placing one-byte
//!   allocations at 2^31 .. 2^12 and a gap makes end exactly at 2^32, where
//!   a pointer one past it has no address. Every run of such a placing
//!   harness must reach its call of `f` (`harness_reaches_call`): one
//!   refused before the call tests nothing.
//!
//! fsym's verdicts are about the runs of its run model
//! (`fsym_trust_ir::FSYM_RUN_MODEL`: fuel below 2^50 steps, no forged entry
//! pointer or handle; since trust-ir v50 the interpreter has no memory
//! budget), so every generated
//! run must be one (`interpret` refuses any other), and a regression case
//! whose run is outside it must say why its verdict holds there
//! (`Case::outside_run_model`); its UB must still never be claimed clean.
//!
//! Every UB the oracle takes is ATTRIBUTED (`attribute`): re-run on a copy of
//! the module with each instruction in a block of its own, the error's block
//! names the one instruction (or block entry) that raised it, and its message
//! names the `fsym_ub_map` site. The map's stance for that site and raiser
//! must owe the UB there (`Owed` with its shape predicate accepting the
//! instruction) or where its poison was made (`AtSource`) — never say it
//! cannot arise (`NotRaised`, `Outside`, no stance); and where it owes a
//! verdict at the instruction and fsym walked the function to its end, fsym
//! must have reported that instruction with a verdict of that kind that is
//! not Safe (`owed_verdict_reported`). Every regression case's UB is
//! attributed, and up to `ATTRIBUTED_PER_CLASS` of each message class of the
//! generated corpus's.
//!
//! The generator keeps the corpus honest: the test asserts that the
//! interpreter executed a floor of the generated functions to completion, that
//! it found UB in a floor of them, that fsym reported a floor of them clean
//! (an oracle that never sees a clean verdict checks nothing), that every
//! required construct (`REQUIRED_CONSTRUCTS`) was generated, and that a
//! function using each construct whose `Safe` arm matters
//! (`CLEAN_CONSTRUCTS`) scanned clean and ran. `FSYM_ORACLE_FUNCTIONS` and
//! `FSYM_ORACLE_SEED` override the corpus size and seed for exploratory runs.

use std::time::{Duration, Instant};

use std::collections::{BTreeMap, BTreeSet, HashMap};

use trust_cg_verify::fsym_summary::{
    FsymFunctionOutcome, FsymLocalSolverAdapter, FsymSolverAdapter, FsymSolverEscalation,
    FsymSolverEscalationConfig, FsymSolverStatus, FsymSummary,
};
use trust_cg_verify::fsym_trust_ir::{
    FSYM_RUN_MODEL, FSYM_TRUST_IR_MAX_BLOCKS, FSYM_TRUST_IR_MAX_PATH_STATES,
    FsymTrustIrDiagnosticKind, FsymTrustIrReport, scan_function_in_module, scan_module,
};
use trust_cg_verify::fsym_ub_map::{
    CALLEE_FUNCTION, FSYM_INST_VARIANTS, FSYM_INTERPRETER_UB_SITES, FsymInterpreterUbSite,
    FsymUbStance, RAISER_ENTRY, RAISER_WALK, fsym_inst_variant_name, fsym_site_message_matches,
};
use trust_ir::inst::AllocOrigin;
use trust_ir::value::GlobalId;
use trust_ir::{
    AtomicRMWOp, BinOp, Block, BlockId, CastOp, Constant, EnumDef, EnumId, EnumVariant, FCmpOp,
    FatPtrKind, FieldDef, FuncId, FuncTy, FuncTyId, Function, ICmpOp, Inst, InstrNode,
    InterpretError, InterpretErrorCode, InterpretOptions, InterpretValue, InterpretValueKind,
    Interpreter, Module, Ordering, OverflowOp, ProofAnnotation, StructDef, StructId, StructRepr,
    SwitchCase, Ty, TyId, UnOp, ValueId,
};

// ---------------------------------------------------------------------------
// Verdicts
// ---------------------------------------------------------------------------

/// True when fsym claims `function` is free of UB: scanned, not skipped, and
/// with no diagnostic, Unknown or coverage error.
fn fsym_clean(report: &FsymTrustIrReport, function: &str) -> bool {
    report.scanned_function_names.iter().any(|f| f == function)
        && report
            .skipped_functions
            .iter()
            .all(|s| s.function != function)
        && report.diagnostics.iter().all(|d| d.function != function)
        && report
            .unknown_obligations
            .iter()
            .all(|u| u.function != function)
        && report
            .coverage_errors
            .iter()
            .all(|c| c.function != function)
}

fn fsym_summary_line(report: &FsymTrustIrReport, function: &str) -> String {
    let diagnostics = report
        .diagnostics
        .iter()
        .filter(|d| d.function == function)
        .map(|d| format!("{:?}@bb{}:{}", d.kind, d.block, d.inst_index))
        .collect::<Vec<_>>();
    let unknowns = report
        .unknown_obligations
        .iter()
        .filter(|u| u.function == function)
        .map(|u| format!("{:?}@bb{}:{}", u.kind, u.block, u.inst_index))
        .collect::<Vec<_>>();
    let skips = report
        .skipped_functions
        .iter()
        .filter(|s| s.function == function)
        .map(|s| s.detail.to_string())
        .collect::<Vec<_>>();
    format!(
        "scanned={} diag={diagnostics:?} unknown={unknowns:?} skipped={skips:?} coverage_errors={}",
        report.scanned_function_names.iter().any(|f| f == function),
        report
            .coverage_errors
            .iter()
            .filter(|c| c.function == function)
            .count()
    )
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Run {
    /// Executed to a `return`.
    Returned,
    /// The interpreter reported undefined behaviour.
    Ub(InterpretError),
    /// Any other refusal (type error, unsupported, out of fuel/memory, a
    /// false `assume`): no verdict about UB either way.
    Refused(InterpretErrorCode, String),
}

/// The interpreter's fuel for one run of a generated or regression case.
const FUEL: u64 = 20_000;

/// The interpreter's options for a run with `fuel`: inside fsym's run model
/// (`FSYM_RUN_MODEL`), whose verdicts are about no other run.
fn run_options(fuel: u64) -> InterpretOptions {
    InterpretOptions {
        fuel,
        max_call_depth: 8,
        panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
    }
}

fn interpret_with(
    module: &Module,
    entry: FuncId,
    args: &[InterpretValue],
    options: InterpretOptions,
) -> Run {
    let interpreter = Interpreter::with_module(module).with_options(options);
    match interpreter.execute_func(entry, args.to_vec()) {
        Ok(_) => Run::Returned,
        Err(error) if error.code == InterpretErrorCode::UndefinedBehavior => Run::Ub(error),
        Err(error) => Run::Refused(error.code, error.to_string()),
    }
}

/// A run of the generated corpus: one fsym's run model admits, or the
/// corpus would be checking claims fsym never makes.
fn interpret(module: &Module, entry: FuncId, args: &[InterpretValue]) -> Run {
    let options = run_options(FUEL);
    if let Some(breach) = FSYM_RUN_MODEL.breach(&options, args) {
        panic!("a generated run outside fsym's run model: {breach}");
    }
    interpret_with(module, entry, args, options)
}

// ---------------------------------------------------------------------------
// Attribution: the instruction that raised an observed UB, and the UB map's
// stance for it
// ---------------------------------------------------------------------------

/// Where a block of a `split_module` came from.
#[derive(Debug, Clone, Copy)]
enum Piece {
    /// The original block's parameters, bound when it is entered (the block
    /// walk's binding, or the entry's arguments).
    Head,
    /// The original block's `index`-th instruction, alone.
    Inst(usize),
}

/// A module whose every instruction sits in a block of its own.
struct Split {
    module: Module,
    /// Per split block id: (function index, original block, piece).
    origin: HashMap<u32, (usize, BlockId, Piece)>,
}

/// `module` with each block's parameters in a head block and each of its
/// instructions in a block of its own, joined by argument-less `br`s, and
/// block ids unique across the module. The interpreter keeps one value map
/// per call frame across blocks, so the split module executes exactly the
/// original's instructions in the original's order (plus the `br`s, which
/// raise nothing) — and the block an error names is the ONE instruction (or
/// block entry) that raised it.
fn split_module(mut split: Module) -> Split {
    let mut origin = HashMap::new();
    let mut next = 0u32;
    for (function_index, function) in split.functions.iter_mut().enumerate() {
        if function.blocks.is_empty() {
            continue;
        }
        let mut head = HashMap::new();
        for block in &function.blocks {
            head.insert(block.id, next);
            next += 1 + block.body.len() as u32;
        }
        let remap = |id: &mut BlockId| {
            *id = BlockId::new(head.get(id).copied().unwrap_or(u32::MAX));
        };
        let mut blocks = Vec::new();
        for block in std::mem::take(&mut function.blocks) {
            let start = head[&block.id];
            origin.insert(start, (function_index, block.id, Piece::Head));
            let body_len = block.body.len();
            blocks.push(Block {
                id: BlockId::new(start),
                params: block.params,
                body: if block.body.is_empty() {
                    Vec::new()
                } else {
                    vec![InstrNode::new(Inst::Br {
                        target: BlockId::new(start + 1),
                        args: Vec::new(),
                    })]
                },
            });
            for (index, mut node) in block.body.into_iter().enumerate() {
                let id = start + 1 + index as u32;
                origin.insert(id, (function_index, block.id, Piece::Inst(index)));
                match &mut node.inst {
                    Inst::Br { target, .. } => remap(target),
                    Inst::CondBr {
                        then_target,
                        else_target,
                        ..
                    } => {
                        remap(then_target);
                        remap(else_target);
                    }
                    Inst::Switch { default, cases, .. } => {
                        remap(default);
                        cases.iter_mut().for_each(|case| remap(&mut case.target));
                    }
                    Inst::Invoke {
                        normal_dest,
                        unwind_dest,
                        ..
                    } => {
                        remap(normal_dest);
                        remap(unwind_dest);
                    }
                    _ => {}
                }
                let mut body = vec![node];
                if index + 1 < body_len {
                    body.push(InstrNode::new(Inst::Br {
                        target: BlockId::new(id + 1),
                        args: Vec::new(),
                    }));
                }
                blocks.push(Block {
                    id: BlockId::new(id),
                    params: Vec::new(),
                    body,
                });
            }
        }
        function.entry = BlockId::new(head[&function.entry]);
        function.blocks = blocks;
    }
    Split {
        module: split,
        origin,
    }
}

/// One interpreter UB attributed to what raised it.
struct Observed {
    /// The function (index), original block and instruction that raised it
    /// (`None`: entering the block).
    function: usize,
    block: BlockId,
    inst_index: Option<usize>,
    /// The raiser: an `Inst` variant, or the block walk / entry.
    raiser: &'static str,
    /// The map sites its message is an instance of.
    sites: Vec<&'static FsymInterpreterUbSite>,
    /// The verdict kinds the map owes AT the instruction for it (empty when
    /// it is owed where a poison value is made, or at a pseudo-raiser).
    owed_here: Vec<FsymTrustIrDiagnosticKind>,
}

/// Confirm this one Unicode-validity site's exclusion against the actual
/// offending function's exact named refusal, never an unrelated scanner skip.
fn char_scope_refusal_confirmed(
    module: &Module,
    function: &Function,
    site: &FsymInterpreterUbSite,
    reason: &str,
) -> bool {
    use trust_cg_verify::fsym_trust_ir::{FSYM_CHAR_BINDING_REFUSAL, FsymTrustIrSkipReason};
    use trust_cg_verify::fsym_ub_map::{CHAR_BINDINGS_REFUSED, CLASS_CHAR_VALIDITY};
    if site.function != "check_char_validity"
        || site.message != "`char` value {:#x} is not a Unicode scalar value ("
        || site.class != CLASS_CHAR_VALIDITY
        || reason != CHAR_BINDINGS_REFUSED
    {
        return false;
    }
    // Re-run the actual gate on the offending function. An unrelated skip,
    // other UB site, forged reason, or a scan that proceeded grants nothing.
    let report = scan_function_in_module(module, function);
    matches!(
        report.skipped_functions.as_slice(),
        [skip] if skip.function == function.name
            && skip.reason == FsymTrustIrSkipReason::UnsupportedInstruction
            && skip.detail == FSYM_CHAR_BINDING_REFUSAL
    ) && report.scanned_functions == 0
        && report.scanned_function_names.is_empty()
}

/// Attribute the UB `error` (running `entry` of `module` on `args`) to the
/// instruction that raised it, by re-running the split module, and check the
/// UB map's stance for that site and raiser: `Err` when the map says the
/// site cannot arise there (`NotRaised`, `Outside`, an `Owed` shape
/// predicate rejecting the instruction, or no stance at all).
fn attribute(
    split: &Split,
    entry: FuncId,
    args: &[InterpretValue],
    error: &InterpretError,
    options: InterpretOptions,
) -> Result<Observed, String> {
    let module = &split.module;
    // Each original step is at most three split steps (block head, the
    // instruction, its `br`): with the original run's fuel tripled, the
    // split run reaches the same UB.
    let rerun_options = InterpretOptions {
        fuel: 3 * options.fuel + 16,
        ..options
    };
    let rerun = match interpret_with(&split.module, entry, args, rerun_options) {
        Run::Ub(rerun) if rerun.message == error.message => rerun,
        other => {
            return Err(format!(
                "the split module ran differently: {other:?} (original: {error})"
            ));
        }
    };
    let block = rerun
        .block
        .ok_or_else(|| format!("the UB names no block: {error}"))?;
    let &(function, original_block, piece) = split
        .origin
        .get(&block.index())
        .ok_or_else(|| format!("the UB names block {block}, which the split did not make"))?;
    let (raisers, inst, inst_index): (Vec<&'static str>, Option<&Inst>, Option<usize>) = match piece
    {
        Piece::Head => (vec![RAISER_WALK, RAISER_ENTRY], None, None),
        Piece::Inst(index) => {
            // The split block holds the original instruction first.
            let inst = &module.functions[function]
                .block(block)
                .expect("the split block exists")
                .body[0]
                .inst;
            let name = fsym_inst_variant_name(inst);
            // A `return` raises nothing itself: the walk checks the
            // values it returns.
            let raisers = if name == "Return" {
                vec![RAISER_WALK]
            } else {
                vec![name]
            };
            (raisers, Some(inst), Some(index))
        }
    };
    let sites = FSYM_INTERPRETER_UB_SITES
        .iter()
        .filter(|site| {
            site.function != CALLEE_FUNCTION
                && fsym_site_message_matches(site.message, &error.message)
        })
        .collect::<Vec<_>>();
    if sites.is_empty() {
        return Err(format!(
            "no FSYM_INTERPRETER_UB_SITES entry's message matches `{}`",
            error.message
        ));
    }
    let mut accepted = false;
    let mut owed_here = Vec::new();
    let mut refuted = Vec::new();
    for site in &sites {
        let mut stated = false;
        for raise in site.raisers {
            let Some(raiser) = raisers.iter().find(|raiser| raise.by.contains(raiser)) else {
                continue;
            };
            stated = true;
            match (raise.stance, inst) {
                (FsymUbStance::Owed { kind, applies, .. }, Some(inst)) => {
                    if applies(module, inst) {
                        accepted = true;
                        owed_here.push(kind);
                    } else {
                        refuted.push(format!(
                            "{} `{}`: the map owes {kind:?} only at the {raiser} shapes its predicate accepts, and it rejects this one",
                            site.function, site.message
                        ));
                    }
                }
                (FsymUbStance::Owed { .. }, None)
                | (FsymUbStance::AtSource { .. }, _)
                | (FsymUbStance::Refused, _) => accepted = true,
                (FsymUbStance::NotRaised(reason), _)
                    if char_scope_refusal_confirmed(
                        module,
                        &module.functions[function],
                        site,
                        reason,
                    ) =>
                {
                    // The map says "not in an admitted function", not that
                    // arbitrary Char execution is safe. The function remains
                    // skipped in the original report and cannot count clean.
                    accepted = true;
                }
                (FsymUbStance::NotRaised(reason), _) => refuted.push(format!(
                    "{} `{}`: the map says {raiser} cannot raise it: NotRaised({reason})",
                    site.function, site.message
                )),
                (FsymUbStance::Outside(reason), _) => refuted.push(format!(
                    "{} `{}`: the map says it is outside a scanned body for {raiser}: Outside({reason})",
                    site.function, site.message
                )),
            }
        }
        if !stated {
            refuted.push(format!(
                "{} `{}`: the map states no stance for {raisers:?}",
                site.function, site.message
            ));
        }
    }
    let observed = Observed {
        function,
        block: original_block,
        inst_index,
        raiser: raisers[0],
        sites,
        owed_here,
    };
    if accepted {
        Ok(observed)
    } else {
        Err(format!(
            "interpreter UB `{}` raised by {} at {} bb{}{}: {}",
            error.message,
            observed.raiser,
            module.functions[function].name,
            original_block.index(),
            inst_index.map_or(" (entry)".to_string(), |index| format!(":{index}")),
            refuted.join("; ")
        ))
    }
}

/// Whether fsym walked every path of `function` to its end: scanned, not
/// skipped, and nothing that cuts a path short (a concrete-UB diagnostic, a
/// coverage error, the path-state bound).
fn fully_walked(report: &FsymTrustIrReport, function: &str) -> bool {
    report.scanned_function_names.iter().any(|f| f == function)
        && report
            .skipped_functions
            .iter()
            .all(|s| s.function != function)
        && report.diagnostics.iter().all(|d| d.function != function)
        && report
            .coverage_errors
            .iter()
            .all(|c| c.function != function)
        && report
            .unknown_obligations
            .iter()
            .all(|u| u.function != function || u.kind != FsymTrustIrDiagnosticKind::ScanBound)
}

/// The map's stance is a claim about fsym's verdicts too: where it owes a
/// verdict of some kind AT the instruction that raised an observed UB, and
/// fsym walked that function to the end, fsym must have reported that
/// instruction with a verdict of one of those kinds that is not Safe.
fn owed_verdict_reported(
    module: &Module,
    report: &FsymTrustIrReport,
    observed: &Observed,
) -> Result<(), String> {
    let Some(inst_index) = observed.inst_index else {
        return Ok(());
    };
    if observed.owed_here.is_empty() {
        return Ok(());
    }
    let function = &module.functions[observed.function].name;
    if !fully_walked(report, function) {
        return Ok(());
    }
    let block = observed.block.index();
    let at = |f: &str, b: u32, i: usize| f == function && b == block && i == inst_index;
    let reported =
        report.unknown_obligations.iter().any(|u| {
            at(&u.function, u.block, u.inst_index) && observed.owed_here.contains(&u.kind)
        }) || report.diagnostics.iter().any(|d| {
            at(&d.function, d.block, d.inst_index) && observed.owed_here.contains(&d.kind)
        });
    if reported {
        Ok(())
    } else {
        Err(format!(
            "the map owes {:?} at {function} bb{block}:{inst_index} ({}) for interpreter UB at {:?}, and fsym walked the function but reported no such verdict there",
            observed.owed_here,
            observed.raiser,
            observed
                .sites
                .iter()
                .map(|site| format!("{} `{}`", site.function, site.message))
                .collect::<Vec<_>>()
        ))
    }
}

// ---------------------------------------------------------------------------
// A small IR builder
// ---------------------------------------------------------------------------

struct FnBuilder {
    name: String,
    params: Vec<Ty>,
    returns: Vec<Ty>,
    blocks: Vec<Block>,
    current: usize,
    next_value: u32,
}

impl FnBuilder {
    /// A function whose entry block takes `params`; returns the builder and
    /// the parameter values.
    fn new(name: &str, params: &[Ty], returns: &[Ty]) -> (Self, Vec<ValueId>) {
        let mut builder = Self {
            name: name.to_string(),
            params: params.to_vec(),
            returns: returns.to_vec(),
            blocks: Vec::new(),
            current: 0,
            next_value: 0,
        };
        let (_, values) = builder.block(params);
        (builder, values)
    }

    fn fresh(&mut self) -> ValueId {
        let value = ValueId::new(self.next_value);
        self.next_value += 1;
        value
    }

    /// Append a new block with `params` (not switched to).
    fn block(&mut self, params: &[Ty]) -> (BlockId, Vec<ValueId>) {
        let id = BlockId::new(self.blocks.len() as u32);
        let values = params.iter().map(|_| self.fresh()).collect::<Vec<_>>();
        self.blocks.push(Block {
            id,
            params: values.iter().copied().zip(params.iter().cloned()).collect(),
            body: Vec::new(),
        });
        (id, values)
    }

    fn switch_to(&mut self, block: BlockId) {
        self.current = block.index() as usize;
    }

    fn value(&mut self, inst: Inst) -> ValueId {
        let result = self.fresh();
        self.blocks[self.current]
            .body
            .push(InstrNode::new(inst).with_result(result));
        result
    }

    fn effect(&mut self, inst: Inst) {
        self.blocks[self.current].body.push(InstrNode::new(inst));
    }

    /// A one-result instruction carrying `proofs`.
    fn value_with(&mut self, inst: Inst, proofs: Vec<ProofAnnotation>) -> ValueId {
        let result = self.fresh();
        let mut node = InstrNode::new(inst).with_result(result);
        for proof in proofs {
            node = node.with_proof(proof);
        }
        self.blocks[self.current].body.push(node);
        result
    }

    /// A no-result instruction carrying `proofs`.
    fn effect_with(&mut self, inst: Inst, proofs: Vec<ProofAnnotation>) {
        let mut node = InstrNode::new(inst);
        for proof in proofs {
            node = node.with_proof(proof);
        }
        self.blocks[self.current].body.push(node);
    }

    /// A two-result instruction (`Overflow`, `CmpXchg`).
    fn values2(&mut self, inst: Inst) -> (ValueId, ValueId) {
        let first = self.fresh();
        let second = self.fresh();
        self.blocks[self.current]
            .body
            .push(InstrNode::new(inst).with_results([first, second]));
        (first, second)
    }

    fn int(&mut self, ty: Ty, value: i128) -> ValueId {
        self.value(Inst::Const {
            ty,
            value: Constant::Int(value),
        })
    }

    fn null(&mut self) -> ValueId {
        self.value(Inst::NullPtr)
    }

    fn const_ptr(&mut self, address: i128) -> ValueId {
        self.value(Inst::Const {
            ty: Ty::Ptr,
            value: Constant::Int(address),
        })
    }

    fn alloca(&mut self, ty: Ty, count: Option<ValueId>, align: Option<u64>) -> ValueId {
        self.value(Inst::Alloca { ty, count, align })
    }

    fn heap(&mut self, ty: Ty, count: Option<ValueId>) -> ValueId {
        self.value(Inst::HeapAlloc {
            ty,
            count,
            align: None,
            origin: AllocOrigin::CMalloc,
        })
    }

    fn gep(&mut self, pointee_ty: Ty, base: ValueId, index: ValueId) -> ValueId {
        self.value(Inst::GEP {
            pointee_ty,
            base,
            indices: vec![index],
            inbounds: false,
        })
    }

    fn load(&mut self, ty: Ty, ptr: ValueId, align: Option<u64>) -> ValueId {
        self.value(Inst::Load {
            ty,
            ptr,
            volatile: false,
            align,
        })
    }

    fn store(&mut self, ty: Ty, ptr: ValueId, value: ValueId) {
        self.effect(Inst::Store {
            ty,
            ptr,
            value,
            volatile: false,
            align: None,
        });
    }

    fn bin(&mut self, op: BinOp, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.value(Inst::BinOp { op, ty, lhs, rhs })
    }

    fn icmp(&mut self, op: ICmpOp, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.value(Inst::ICmp { op, ty, lhs, rhs })
    }

    fn cast(&mut self, op: CastOp, src_ty: Ty, dst_ty: Ty, operand: ValueId) -> ValueId {
        self.value(Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        })
    }

    fn ptrtoint(&mut self, ptr: ValueId) -> ValueId {
        self.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, ptr)
    }

    fn inttoptr(&mut self, int: ValueId) -> ValueId {
        self.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, int)
    }

    fn select(&mut self, ty: Ty, cond: ValueId, then_val: ValueId, else_val: ValueId) -> ValueId {
        self.value(Inst::Select {
            ty,
            cond,
            then_val,
            else_val,
        })
    }

    fn memset(&mut self, dst: ValueId, byte: ValueId, bytes: ValueId) {
        self.effect(Inst::MemSet { dst, byte, bytes });
    }

    fn dealloc(&mut self, ptr: ValueId) {
        self.effect(Inst::Dealloc { ptr });
    }

    fn call(&mut self, callee: FuncId, args: &[ValueId]) {
        self.effect(Inst::Call {
            callee,
            args: args.to_vec(),
        });
    }

    fn br(&mut self, target: BlockId, args: &[ValueId]) {
        self.effect(Inst::Br {
            target,
            args: args.to_vec(),
        });
    }

    fn condbr(&mut self, cond: ValueId, then_target: BlockId, else_target: BlockId) {
        self.effect(Inst::CondBr {
            cond,
            then_target,
            then_args: vec![],
            else_target,
            else_args: vec![],
        });
    }

    fn switch(&mut self, value: ValueId, default: BlockId, cases: Vec<(i128, BlockId)>) {
        self.effect(Inst::Switch {
            value,
            default,
            default_args: vec![],
            cases: cases
                .into_iter()
                .map(|(value, target)| SwitchCase {
                    value: Constant::Int(value),
                    target,
                    args: vec![],
                })
                .collect(),
            exhaustive_enum_unreachable: false,
        });
    }

    fn ret(&mut self, values: &[ValueId]) {
        self.effect(Inst::Return {
            values: values.to_vec(),
        });
    }

    fn ret_zero(&mut self) {
        let zero = self.int(Ty::I64, 0);
        self.ret(&[zero]);
    }

    fn unreachable(&mut self) {
        self.effect(Inst::Unreachable);
    }

    /// Append this function to `module` at the next function id.
    fn install(self, module: &mut Module) -> FuncId {
        let ty = FuncTyId::new(module.func_types.len() as u32);
        module.func_types.push(FuncTy {
            params: self.params,
            returns: self.returns,
            abi: None,
            is_vararg: false,
        });
        let id = FuncId::new(module.functions.len() as u32);
        let mut function = Function::new(id, self.name, ty, BlockId::new(0));
        function.blocks = self.blocks;
        module.functions.push(function);
        id
    }

    fn module(self, module_name: &str) -> Module {
        let mut module = Module::new(module_name);
        self.install(&mut module);
        module
    }
}

/// Append a body-less `External` declaration.
fn declare(module: &mut Module, name: &str, params: Vec<Ty>) -> FuncId {
    let ty = FuncTyId::new(module.func_types.len() as u32);
    module.func_types.push(FuncTy {
        params,
        returns: vec![],
        abi: None,
        is_vararg: false,
    });
    let id = FuncId::new(module.functions.len() as u32);
    module
        .functions
        .push(Function::new(id, name, ty, BlockId::new(0)));
    id
}

fn wasm32() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: "wasm32-unknown-unknown".to_string(),
        pointer_size: 4,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::default(),
    }
}

// ---------------------------------------------------------------------------
// Regression corpus
// ---------------------------------------------------------------------------

/// One measured fail-open. `f` (function 0) is the function under test.
struct Case {
    name: &'static str,
    module: Module,
    /// Entry arguments on which the interpreter must report UB, or `None`
    /// when the shape is not executable by the interpreter; fsym is then
    /// checked alone.
    ub_inputs: Option<Vec<InterpretValue>>,
    /// The entry the interpreter runs on `ub_inputs`: `f` itself, or a
    /// caller whose run reaches it.
    ub_entry: FuncId,
    /// The interpreter's options for that run.
    options: InterpretOptions,
    /// Why fsym's verdict on the case holds in a run outside its run model
    /// (`FSYM_RUN_MODEL`), when the case's run is one: its UB must still be
    /// reported, never claimed clean. `None` for a run inside the model.
    outside_run_model: Option<&'static str>,
}

fn case(name: &'static str, module: Module, ub_inputs: Option<Vec<InterpretValue>>) -> Case {
    Case {
        name,
        module,
        ub_inputs,
        ub_entry: FuncId::new(0),
        options: run_options(FUEL),
        outside_run_model: None,
    }
}

/// `f() -> i64` built by `body`, which must terminate the entry block.
fn unary_case(name: &'static str, executable: bool, body: impl FnOnce(&mut FnBuilder)) -> Case {
    let (mut f, _) = FnBuilder::new("f", &[], &[Ty::I64]);
    body(&mut f);
    case(name, f.module(name), executable.then(Vec::new))
}

/// Branch on `cond` (built by `prefix`): the THEN arm returns, the ELSE arm
/// (the one taken at run time) runs `bad` and returns.
fn pruned_arm_case(
    name: &'static str,
    executable: bool,
    prefix: impl FnOnce(&mut FnBuilder) -> ValueId,
    bad: impl FnOnce(&mut FnBuilder),
) -> Case {
    let (mut f, _) = FnBuilder::new("f", &[], &[Ty::I64]);
    let cond = prefix(&mut f);
    let (then_block, _) = f.block(&[]);
    let (else_block, _) = f.block(&[]);
    f.condbr(cond, then_block, else_block);
    f.switch_to(then_block);
    f.ret_zero();
    f.switch_to(else_block);
    bad(&mut f);
    f.ret_zero();
    case(name, f.module(name), executable.then(Vec::new))
}

fn null_store(f: &mut FnBuilder) {
    let null = f.null();
    let byte = f.int(Ty::U8, 0);
    f.store(Ty::U8, null, byte);
}

fn udiv_by_zero(f: &mut FnBuilder) {
    let eight = f.int(Ty::U64, 8);
    let zero = f.int(Ty::U64, 0);
    f.bin(BinOp::UDiv, Ty::U64, eight, zero);
}

fn regression_corpus() -> Vec<Case> {
    let mut cases = Vec::new();

    // Char binding UB applies even when the result is never used.
    // These grow the existing corpus; no prior case or floor is removed.
    for (name, raw) in [
        ("char_surrogate_binding", 0xD800),
        ("char_last_surrogate_binding", 0xDFFF),
        ("char_above_unicode_binding", 0x110000),
    ] {
        cases.push(unary_case(name, true, |f| {
            let raw = f.int(Ty::U32, raw);
            f.cast(CastOp::Trunc, Ty::U32, Ty::Char, raw);
            f.ret_zero();
        }));
    }
    let (mut f, params) = FnBuilder::new("f", &[Ty::Char], &[Ty::Char]);
    f.ret(&params);
    cases.push(case(
        "char_invalid_entry_binding",
        f.module("char_invalid_entry_binding"),
        Some(vec![
            InterpretValue::int(Ty::Char, 0xD800).expect("32-bit carrier"),
        ]),
    ));

    // (1) Pointer ICmp decided on object ids: `gep a, 1 == a` is TRUE in the
    // model, FALSE at run time, and the always-taken ELSE arm was pruned.
    cases.push(pruned_arm_case(
        "ptr_icmp_gep_vs_base_prunes_live_arm",
        false,
        |f| {
            let a = f.alloca(Ty::U8, None, None);
            let one = f.int(Ty::I64, 1);
            let g = f.gep(Ty::U8, a, one);
            f.icmp(ICmpOp::Eq, Ty::Ptr, g, a)
        },
        null_store,
    ));
    cases.push(pruned_arm_case(
        "ptrtoint_gep_vs_base_prunes_live_arm",
        true,
        |f| {
            let count = f.int(Ty::U64, 2);
            let a = f.alloca(Ty::U8, Some(count), None);
            let one = f.int(Ty::I64, 1);
            let g = f.gep(Ty::U8, a, one);
            let gi = f.ptrtoint(g);
            let ai = f.ptrtoint(a);
            f.icmp(ICmpOp::Eq, Ty::U64, gi, ai)
        },
        udiv_by_zero,
    ));
    // `icmp ult allocaA, allocaB` decided by object-id order.
    cases.push(pruned_arm_case(
        "ptr_icmp_ult_decided_by_object_id",
        false,
        |f| {
            let a = f.alloca(Ty::U8, None, None);
            let b = f.alloca(Ty::U8, None, None);
            f.icmp(ICmpOp::Ult, Ty::Ptr, a, b)
        },
        null_store,
    ));
    cases.push(pruned_arm_case(
        "ptrtoint_order_decided_by_object_id",
        true,
        |f| {
            let a = f.alloca(Ty::U8, None, None);
            let b = f.alloca(Ty::U8, None, None);
            let hundred = f.int(Ty::I64, 100);
            let far = f.gep(Ty::U8, a, hundred);
            let fi = f.ptrtoint(far);
            let bi = f.ptrtoint(b);
            f.icmp(ICmpOp::Ult, Ty::U64, fi, bi)
        },
        udiv_by_zero,
    ));
    // The same comparison feeding a bulk count: modeled 0 (a Safe no-op),
    // 8 at run time.
    {
        let (mut f, _) = FnBuilder::new("f", &[], &[Ty::I64]);
        let count = f.int(Ty::U64, 8);
        let a = f.alloca(Ty::U8, Some(count), None);
        let one = f.int(Ty::I64, 1);
        let g = f.gep(Ty::U8, a, one);
        let same = f.icmp(ICmpOp::Eq, Ty::Ptr, g, a);
        let zero = f.int(Ty::U64, 0);
        let bytes = f.select(Ty::U64, same, zero, count);
        let null = f.null();
        // C's `memset(void *, int, size_t) -> void *`, the prototype under
        // which trust-cg-lower (and fsym with it) reads the call as the
        // library routine.
        let fill = f.int(Ty::I32, 0);
        let mut module = Module::new("bulk_count_from_ptr_icmp_call");
        let memset_id = FuncId::new(1);
        f.value(Inst::Call {
            callee: memset_id,
            args: vec![null, fill, bytes],
        });
        f.ret_zero();
        f.install(&mut module);
        assert_eq!(
            declare(&mut module, "memset", vec![Ty::Ptr, Ty::I32, Ty::U64]),
            memset_id
        );
        let memset_ty = module.functions[memset_id.index() as usize].ty;
        module.func_types[memset_ty.index() as usize].returns = vec![Ty::Ptr];
        cases.push(case("bulk_count_from_ptr_icmp_call", module, None));
    }
    cases.push(unary_case(
        "bulk_count_from_ptrtoint_icmp_memset",
        true,
        |f| {
            let count = f.int(Ty::U64, 8);
            let a = f.alloca(Ty::U8, Some(count), None);
            let one = f.int(Ty::I64, 1);
            let g = f.gep(Ty::U8, a, one);
            let gi = f.ptrtoint(g);
            let ai = f.ptrtoint(a);
            let same = f.icmp(ICmpOp::Eq, Ty::U64, gi, ai);
            let zero = f.int(Ty::U64, 0);
            let bytes = f.select(Ty::U64, same, zero, count);
            let null = f.null();
            let fill = f.int(Ty::U8, 0);
            f.memset(null, fill, bytes);
            f.ret_zero();
        },
    ));

    // (2) ptrtoint of a tracked object yields its abstract id as a value.
    cases.push(unary_case("udiv_by_masked_alloca_address", true, |f| {
        let a = f.alloca(Ty::U8, None, Some(16));
        let address = f.ptrtoint(a);
        let fifteen = f.int(Ty::U64, 15);
        let low = f.bin(BinOp::And, Ty::U64, address, fifteen);
        let eight = f.int(Ty::U64, 8);
        f.bin(BinOp::UDiv, Ty::U64, eight, low);
        f.ret_zero();
    }));
    cases.push(unary_case("udiv_by_gep_address_difference", true, |f| {
        let count = f.int(Ty::U64, 2);
        let a = f.alloca(Ty::U8, Some(count), None);
        let one = f.int(Ty::I64, 1);
        let g = f.gep(Ty::U8, a, one);
        let gi = f.ptrtoint(g);
        let ai = f.ptrtoint(a);
        let diff = f.bin(BinOp::Sub, Ty::U64, gi, ai);
        let one_u = f.int(Ty::U64, 1);
        let divisor = f.bin(BinOp::Sub, Ty::U64, diff, one_u);
        let eight = f.int(Ty::U64, 8);
        f.bin(BinOp::UDiv, Ty::U64, eight, divisor);
        f.ret_zero();
    }));
    cases.push(unary_case("inttoptr_of_freed_alloca_load", true, |f| {
        let a = f.alloca(Ty::I64, None, None);
        let zero = f.int(Ty::I64, 0);
        f.store(Ty::I64, a, zero);
        let address = f.ptrtoint(a);
        f.dealloc(a);
        let p = f.inttoptr(address);
        let x = f.load(Ty::I64, p, None);
        f.ret(&[x]);
    }));
    cases.push(unary_case("inttoptr_of_freed_heap_load", true, |f| {
        let h = f.heap(Ty::I64, None);
        let zero = f.int(Ty::I64, 0);
        f.store(Ty::I64, h, zero);
        let address = f.ptrtoint(h);
        f.dealloc(h);
        let p = f.inttoptr(address);
        let x = f.load(Ty::I64, p, None);
        f.ret(&[x]);
    }));
    cases.push(unary_case("oob_store_through_inttoptr", true, |f| {
        let a = f.alloca(Ty::U8, None, None);
        let address = f.ptrtoint(a);
        let hundred = f.int(Ty::U64, 100);
        let moved = f.bin(BinOp::Add, Ty::U64, address, hundred);
        let p = f.inttoptr(moved);
        let byte = f.int(Ty::U8, 1);
        f.store(Ty::U8, p, byte);
        f.ret_zero();
    }));

    // (3) Constant pointers: no provenance; GEP kept the null model.
    cases.push(unary_case(
        "store_through_gep_of_wrapping_const_ptr",
        false,
        |f| {
            let c = f.const_ptr(0xFFFF_FFFF_FFFF_FFF8);
            let eight = f.int(Ty::I64, 8);
            let g = f.gep(Ty::U8, c, eight);
            let byte = f.int(Ty::U8, 1);
            f.store(Ty::U8, g, byte);
            f.ret_zero();
        },
    ));
    cases.push(unary_case("gep_of_wrapping_inttoptr_address", true, |f| {
        let address = f.int(Ty::U64, 0xFFFF_FFFF_FFFF_FFF8);
        let p = f.inttoptr(address);
        let eight = f.int(Ty::I64, 8);
        let g = f.gep(Ty::U8, p, eight);
        let byte = f.int(Ty::U8, 1);
        f.store(Ty::U8, g, byte);
        f.ret_zero();
    }));
    {
        let (mut f, _) = FnBuilder::new("f", &[], &[Ty::I64]);
        let c = f.const_ptr(0x1_0000_0000);
        let byte = f.int(Ty::U8, 1);
        f.store(Ty::U8, c, byte);
        f.ret_zero();
        let mut module = f.module("wasm32_const_ptr_past_address_space");
        module.target_info = Some(wasm32());
        cases.push(case("wasm32_const_ptr_past_address_space", module, None));
    }
    {
        let (mut f, _) = FnBuilder::new("f", &[], &[Ty::I64]);
        let address = f.int(Ty::U64, 0x1_0000_0000);
        let p = f.inttoptr(address);
        let byte = f.int(Ty::U8, 1);
        f.store(Ty::U8, p, byte);
        f.ret_zero();
        let mut module = f.module("wasm32_inttoptr_past_address_space");
        module.target_info = Some(wasm32());
        cases.push(case(
            "wasm32_inttoptr_past_address_space",
            module,
            Some(Vec::new()),
        ));
    }
    cases.push(unary_case("store_through_const_ptr_0x1000", false, |f| {
        let c = f.const_ptr(0x1000);
        let byte = f.int(Ty::U8, 1);
        f.store(Ty::U8, c, byte);
        f.ret_zero();
    }));
    cases.push(unary_case("store_through_inttoptr_0x1000", true, |f| {
        let address = f.int(Ty::U64, 0x1000);
        let p = f.inttoptr(address);
        let byte = f.int(Ty::U8, 1);
        f.store(Ty::U8, p, byte);
        f.ret_zero();
    }));

    // (4) Shifts were treated as total.
    cases.push(unary_case("shl_by_bit_width", true, |f| {
        let one = f.int(Ty::U64, 1);
        let width = f.int(Ty::U64, 64);
        f.bin(BinOp::Shl, Ty::U64, one, width);
        f.ret_zero();
    }));
    cases.push(pruned_arm_case(
        "out_of_range_shift_folded_and_pruned",
        true,
        |f| {
            let one = f.int(Ty::U64, 1);
            let width = f.int(Ty::U64, 64);
            let shifted = f.bin(BinOp::Shl, Ty::U64, one, width);
            let zero = f.int(Ty::U64, 0);
            f.icmp(ICmpOp::Ne, Ty::U64, shifted, zero)
        },
        |_| {},
    ));
    cases.push(unary_case("lshr_i8_by_eight", true, |f| {
        let value = f.int(Ty::U8, 0x80);
        let width = f.int(Ty::U8, 8);
        f.bin(BinOp::LShr, Ty::U8, value, width);
        f.ret_zero();
    }));

    // (5) Dealloc was not a coverage site.
    cases.push(unary_case("double_free_of_heap_alloc", true, |f| {
        let h = f.heap(Ty::I64, None);
        f.dealloc(h);
        f.dealloc(h);
        f.ret_zero();
    }));
    {
        let (mut f, params) = FnBuilder::new("f", &[Ty::Ptr], &[Ty::I64]);
        f.dealloc(params[0]);
        f.dealloc(params[0]);
        f.ret_zero();
        cases.push(case(
            "double_free_of_param",
            f.module("double_free_of_param"),
            None,
        ));
    }
    // The reference interpreter is origin-permissive on `Dealloc` (the
    // ub-numerics-policy engine-scope note); trust-cg-lower refuses a
    // `Dealloc` of an `Alloca` and a machine `free` of a stack address is UB.
    cases.push(unary_case("free_of_stack_object", false, |f| {
        let a = f.alloca(Ty::I64, None, None);
        f.dealloc(a);
        f.ret_zero();
    }));
    cases.push(unary_case("free_of_interior_heap_pointer", true, |f| {
        let count = f.int(Ty::U64, 8);
        let h = f.heap(Ty::U8, Some(count));
        let one = f.int(Ty::I64, 1);
        let interior = f.gep(Ty::U8, h, one);
        f.dealloc(interior);
        f.ret_zero();
    }));

    // (6) Pointer-carrying judged by the declaration only.
    {
        let (mut f, _) = FnBuilder::new("f", &[], &[Ty::I64]);
        let null = f.null();
        let eight = f.int(Ty::U64, 8);
        let bzero = FuncId::new(1);
        f.call(bzero, &[null, eight]);
        f.ret_zero();
        let mut module = Module::new("bzero_declared_with_integer_params");
        f.install(&mut module);
        assert_eq!(declare(&mut module, "bzero", vec![Ty::U64, Ty::U64]), bzero);
        cases.push(case("bzero_declared_with_integer_params", module, None));
    }

    // A bodied callee frees the caller's allocation; the caller then loads
    // it. The call was "accounted by the callee's own scan", and the callee
    // freed a parameter without a verdict.
    {
        let mut module = Module::new("callee_frees_callers_object");
        let (mut f, _) = FnBuilder::new("f", &[], &[Ty::I64]);
        let h = f.heap(Ty::I64, None);
        let zero = f.int(Ty::I64, 0);
        f.store(Ty::I64, h, zero);
        f.call(FuncId::new(1), &[h]);
        let x = f.load(Ty::I64, h, None);
        f.ret(&[x]);
        f.install(&mut module);
        let (mut g, params) = FnBuilder::new("g", &[Ty::Ptr], &[]);
        g.dealloc(params[0]);
        g.ret(&[]);
        assert_eq!(g.install(&mut module), FuncId::new(1));
        cases.push(case(
            "callee_frees_callers_object",
            module,
            Some(Vec::new()),
        ));
    }

    // (7) Out-of-class UB the scanner was silent on.
    cases.push(unary_case("unreachable_at_entry", true, |f| {
        f.unreachable();
    }));
    cases.push(unary_case("negative_gep_index", true, |f| {
        let count = f.int(Ty::U64, 4);
        let a = f.alloca(Ty::U8, Some(count), None);
        let minus_one = f.int(Ty::I64, -1);
        f.gep(Ty::U8, a, minus_one);
        f.ret_zero();
    }));
    cases.push(unary_case("misaligned_i64_load_align_8", true, |f| {
        let count = f.int(Ty::U64, 16);
        let a = f.alloca(Ty::U8, Some(count), Some(8));
        let fill = f.int(Ty::U8, 0);
        f.memset(a, fill, count);
        let one = f.int(Ty::I64, 1);
        let g = f.gep(Ty::U8, a, one);
        let x = f.load(Ty::I64, g, Some(8));
        f.ret(&[x]);
    }));
    cases.push(unary_case("gep_on_null_without_access", true, |f| {
        let null = f.null();
        let zero = f.int(Ty::I64, 0);
        f.gep(Ty::U8, null, zero);
        f.ret_zero();
    }));
    cases.push(unary_case("uninitialized_load_inspected", true, |f| {
        let a = f.alloca(Ty::I64, None, None);
        let x = f.load(Ty::I64, a, None);
        let one = f.int(Ty::I64, 1);
        let y = f.bin(BinOp::Add, Ty::I64, x, one);
        f.ret(&[y]);
    }));
    cases.push(unary_case("alloca_count_zero", true, |f| {
        let zero = f.int(Ty::U64, 0);
        f.alloca(Ty::U8, Some(zero), None);
        f.ret_zero();
    }));

    // Found by the generated corpus after the model was made abstract:
    // materializing the address of a pointer far past its object overflows
    // (the GEP itself stays within 64-bit offset arithmetic).
    cases.push(unary_case(
        "ptrtoint_of_pointer_far_past_its_object",
        true,
        |f| {
            let a = f.alloca(Ty::U64, None, Some(16));
            let far = f.int(Ty::U64, i128::from(u64::MAX));
            let g = f.gep(Ty::U8, a, far);
            f.ptrtoint(g);
            f.ret_zero();
        },
    ));
    cases.push(unary_case(
        "store_of_pointer_far_past_its_object",
        true,
        |f| {
            let slot = f.alloca(Ty::Ptr, None, None);
            let a = f.alloca(Ty::U8, None, None);
            let far = f.int(Ty::U64, i128::from(u64::MAX));
            let g = f.gep(Ty::U8, a, far);
            f.effect(Inst::Store {
                ty: Ty::Ptr,
                ptr: slot,
                value: g,
                volatile: false,
                align: None,
            });
            f.ret_zero();
        },
    ));
    // An alignment past what fsym models: the second base overflows.
    // Since trust-ir v50 an exhausted address space is `OutOfMemory`, not
    // UB: the case keeps its fsym check alone (never claimed clean).
    cases.push(unary_case("allocas_with_huge_alignment", false, |f| {
        f.alloca(Ty::U8, None, Some(1 << 63));
        f.alloca(Ty::U8, None, Some(1 << 63));
        f.ret_zero();
    }));

    // Round 4: the extended generator (floats, vectors, enums, borrows, bool
    // extensions, proof annotations). Each scanned clean on fd1068399 (or
    // crashed the scanner) while the interpreter reports UB.
    for (name, value, op, dst) in [
        ("fptosi_of_nan", f64::NAN, CastOp::FPToSI, Ty::I32),
        ("fptoui_of_negative", -1.0, CastOp::FPToUI, Ty::U8),
        (
            "fptosi_past_i32_max",
            2_147_483_648.0,
            CastOp::FPToSI,
            Ty::I32,
        ),
        ("fptoui_of_infinity", f64::INFINITY, CastOp::FPToUI, Ty::U64),
    ] {
        cases.push(unary_case(name, true, |f| {
            let x = f.value(Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(value),
            });
            f.cast(op, Ty::F64, dst, x);
            f.ret_zero();
        }));
    }
    // An integer converted to a float and back: `i32::MAX as f32` rounds up
    // to 2^31, which `fptosi` to i32 cannot hold; a negative integer
    // converted back UNSIGNED is negative.
    {
        let (mut f, params) = FnBuilder::new("f", &[Ty::I32], &[Ty::I64]);
        let x = f.cast(CastOp::SIToFP, Ty::I32, Ty::F32, params[0]);
        f.cast(CastOp::FPToSI, Ty::F32, Ty::I32, x);
        f.ret_zero();
        cases.push(case(
            "i32_as_f32_as_i32_rounds_past_i32_max",
            f.module("i32_as_f32_as_i32_rounds_past_i32_max"),
            Some(vec![
                InterpretValue::int(Ty::I32, i128::from(i32::MAX)).expect("i32"),
            ]),
        ));
    }
    {
        let (mut f, params) = FnBuilder::new("f", &[Ty::I64], &[Ty::I64]);
        let x = f.cast(CastOp::SIToFP, Ty::I64, Ty::F64, params[0]);
        f.cast(CastOp::FPToUI, Ty::F64, Ty::U64, x);
        f.ret_zero();
        cases.push(case(
            "negative_i64_as_f64_as_u64",
            f.module("negative_i64_as_f64_as_u64"),
            Some(vec![InterpretValue::int(Ty::I64, -1).expect("i64")]),
        ));
    }
    cases.push(unary_case(
        "fptosi_of_f32_rounding_past_i32_max",
        true,
        |f| {
            // 2147483647 as f32 rounds to 2^31, one past i32::MAX.
            let x = f.value(Inst::Const {
                ty: Ty::F32,
                value: Constant::Float(2_147_483_647.0),
            });
            f.cast(CastOp::FPToSI, Ty::F32, Ty::I32, x);
            f.ret_zero();
        },
    ));
    for (name, index_ty, index) in [
        ("extract_element_one_past_the_end", Ty::U64, 4),
        ("extract_element_negative_index", Ty::I64, -1),
    ] {
        cases.push(unary_case(name, true, |f| {
            let v = f.value(Inst::Const {
                ty: Ty::Vector(Box::new(Ty::I32), 4),
                value: Constant::Vector((0..4).map(Constant::Int).collect()),
            });
            let index = f.int(index_ty, index);
            f.value(Inst::ExtractElement {
                ty: Ty::I32,
                array: v,
                index,
            });
            f.ret_zero();
        }));
    }
    cases.push(unary_case("insert_element_past_the_end", true, |f| {
        let v = f.value(Inst::Const {
            ty: Ty::Vector(Box::new(Ty::I32), 4),
            value: Constant::Vector((0..4).map(Constant::Int).collect()),
        });
        let index = f.int(Ty::U8, 100);
        let lane = f.int(Ty::I32, 7);
        f.value(Inst::InsertElement {
            ty: Ty::Vector(Box::new(Ty::I32), 4),
            array: v,
            index,
            value: lane,
        });
        f.ret_zero();
    }));
    cases.push(enum_case("extract_field_of_inactive_variant", |f| {
        let e = f.value(Inst::Const {
            ty: Ty::Enum(EnumId::new(0)),
            value: Constant::Aggregate(vec![Constant::Int(0)]),
        });
        f.value(Inst::ExtractField {
            ty: Ty::I32,
            aggregate: e,
            field: 1,
        });
    }));
    cases.push(enum_case("extract_field_at_the_wrong_lane_type", |f| {
        let payload = f.int(Ty::I32, 5);
        let e = f.value(Inst::MakeAggregate {
            ty: Ty::Enum(EnumId::new(0)),
            variant: Some(1),
            fields: vec![payload],
        });
        f.value(Inst::ExtractField {
            ty: Ty::I64,
            aggregate: e,
            field: 1,
        });
    }));
    cases.push(enum_case("insert_field_rewrites_the_enum_tag", |f| {
        let e = f.value(Inst::Const {
            ty: Ty::Enum(EnumId::new(0)),
            value: Constant::Aggregate(vec![Constant::Int(1), Constant::Int(9)]),
        });
        let tag = f.int(Ty::U8, 0);
        f.value(Inst::InsertField {
            ty: Ty::Enum(EnumId::new(0)),
            aggregate: e,
            field: 0,
            value: tag,
        });
    }));
    {
        // The variant of an enum PARAMETER is unknown: the payload lane of
        // `B` read from a value of `A`.
        let (mut f, params) = FnBuilder::new("f", &[Ty::Enum(EnumId::new(0))], &[Ty::I64]);
        f.value(Inst::ExtractField {
            ty: Ty::I32,
            aggregate: params[0],
            field: 1,
        });
        f.ret_zero();
        let mut module = Module::new("extract_field_of_enum_parameter");
        module.enums.push(generated_enum());
        f.install(&mut module);
        let variant_a = InterpretValue {
            ty: Ty::Enum(EnumId::new(0)),
            kind: InterpretValueKind::Aggregate(vec![InterpretValue::int(Ty::U8, 0).expect("tag")]),
        };
        cases.push(case(
            "extract_field_of_enum_parameter",
            module,
            Some(vec![variant_a]),
        ));
    }
    cases.push(unary_case("extract_field_past_a_tuple", true, |f| {
        let t = f.value(Inst::Const {
            ty: Ty::Tuple(vec![Ty::I32, Ty::I64]),
            value: Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2)]),
        });
        f.value(Inst::ExtractField {
            ty: Ty::I32,
            aggregate: t,
            field: 2,
        });
        f.ret_zero();
    }));
    cases.push(unary_case("borrow_of_null", true, |f| {
        let null = f.null();
        f.value(Inst::Borrow { ptr: null });
        f.ret_zero();
    }));
    cases.push(unary_case(
        "borrow_mut_of_a_pointer_naming_no_allocation",
        true,
        |f| {
            let address = f.int(Ty::U64, 0x10_0000);
            let p = f.inttoptr(address);
            f.value(Inst::BorrowMut { ptr: p });
            f.ret_zero();
        },
    ));
    cases.push(unary_case("zext_of_bool_as_divisor", true, |f| {
        // `8 / ((1 < 0) as u64)`: crashed the scanner (a Bool asked for its
        // bit width in `zext`).
        let one = f.int(Ty::U64, 1);
        let zero = f.int(Ty::U64, 0);
        let lt = f.icmp(ICmpOp::Ult, Ty::U64, one, zero);
        let wide = f.cast(CastOp::ZExt, Ty::Bool, Ty::U64, lt);
        let eight = f.int(Ty::U64, 8);
        f.bin(BinOp::UDiv, Ty::U64, eight, wide);
        f.ret_zero();
    }));
    cases.push(unary_case("sext_of_bool_plus_one_as_divisor", true, |f| {
        // sext(true) is -1 (all bits set): `8 / (sext(0 < 1) + 1)` divides by 0.
        let one = f.int(Ty::I64, 1);
        let zero = f.int(Ty::I64, 0);
        let lt = f.icmp(ICmpOp::Slt, Ty::I64, zero, one);
        let wide = f.cast(CastOp::SExt, Ty::Bool, Ty::I64, lt);
        let divisor = f.bin(BinOp::Add, Ty::I64, wide, one);
        let eight = f.int(Ty::I64, 8);
        f.bin(BinOp::SDiv, Ty::I64, eight, divisor);
        f.ret_zero();
    }));
    cases.push(unary_case(
        "not_null_annotation_on_a_load_through_null",
        true,
        |f| {
            let null = f.null();
            let x = f.value_with(
                Inst::Load {
                    ty: Ty::I64,
                    ptr: null,
                    volatile: false,
                    align: None,
                },
                vec![ProofAnnotation::NotNull],
            );
            f.ret(&[x]);
        },
    ));
    cases.push(unary_case(
        "in_bounds_annotation_on_a_store_through_a_constant_address",
        true,
        |f| {
            let address = f.int(Ty::U64, 0x1000);
            let p = f.inttoptr(address);
            let byte = f.int(Ty::U8, 1);
            f.effect_with(
                Inst::Store {
                    ty: Ty::U8,
                    ptr: p,
                    value: byte,
                    volatile: false,
                    align: None,
                },
                vec![ProofAnnotation::NotNull, ProofAnnotation::InBounds],
            );
            f.ret_zero();
        },
    ));
    cases.push(unary_case(
        "in_bounds_annotation_on_a_store_past_a_tracked_object",
        true,
        |f| {
            let a = f.alloca(Ty::U8, None, None);
            let eight = f.int(Ty::I64, 8);
            let past = f.gep(Ty::U8, a, eight);
            let byte = f.int(Ty::U8, 1);
            f.effect_with(
                Inst::Store {
                    ty: Ty::U8,
                    ptr: past,
                    value: byte,
                    volatile: false,
                    align: None,
                },
                vec![ProofAnnotation::InBounds],
            );
            f.ret_zero();
        },
    ));
    cases.push(unary_case(
        "store_of_a_tuple_holding_a_pointer_far_past_its_object",
        true,
        |f| {
            let slot = f.alloca(Ty::Tuple(vec![Ty::Ptr, Ty::I64]), None, None);
            let a = f.alloca(Ty::U8, None, None);
            let far = f.int(Ty::U64, i128::from(u64::MAX));
            let g = f.gep(Ty::U8, a, far);
            let zero = f.int(Ty::I64, 0);
            let pair = f.value(Inst::MakeAggregate {
                ty: Ty::Tuple(vec![Ty::Ptr, Ty::I64]),
                variant: None,
                fields: vec![g, zero],
            });
            f.store(Ty::Tuple(vec![Ty::Ptr, Ty::I64]), slot, pair);
            f.ret_zero();
        },
    ));

    // Round 5. (1) The LAYOUT AUTHORITY: every size, offset, stride and
    // alignment is the interpreter's. `<4 x bool>` is 4 bytes (a byte a lane),
    // not the native backends' 16.
    cases.push(layout_case("bool_vector_store_past_its_four_bytes", |f| {
        let slot = f.alloca(bool_vector_ty(), None, None);
        let four = f.int(Ty::I64, 4);
        let at = f.gep(Ty::U8, slot, four);
        let byte = f.int(Ty::U8, 1);
        f.store(Ty::U8, at, byte);
    }));
    // A declared-layout struct is its DECLARED size (16, its byte at offset
    // 8), never a layout synthesized from its fields (1).
    cases.push(layout_case(
        "declared_struct_load_from_an_8_byte_buffer",
        |f| {
            let count = f.int(Ty::U64, 8);
            let buf = f.alloca(Ty::U8, Some(count), Some(8));
            let fill = f.int(Ty::U8, 1);
            f.memset(buf, fill, count);
            f.load(declared_ty(), buf, None);
        },
    ));
    cases.push(layout_case(
        "declared_struct_gep_stride_into_a_4_byte_buffer",
        |f| {
            let count = f.int(Ty::U64, 4);
            let buf = f.alloca(Ty::U8, Some(count), None);
            let one = f.int(Ty::I64, 1);
            let at = f.gep(declared_ty(), buf, one);
            let byte = f.int(Ty::U8, 1);
            f.store(Ty::U8, at, byte);
        },
    ));
    cases.push(layout_case("declared_struct_alloca_size_overflow", |f| {
        let count = f.int(Ty::U64, (1 << 60) + 1);
        f.alloca(declared_ty(), Some(count), None);
    }));
    cases.push(layout_case(
        "declared_struct_gep_byte_offset_overflow",
        |f| {
            let buf = f.alloca(Ty::U8, None, None);
            let four = f.int(Ty::I64, 4);
            f.gep(big_ty(), buf, four);
        },
    ));
    // (2) NATURAL alignment (`align: None`) places an allocation too: two of
    // a type aligned to 2^63 overflow the base address.
    // Since trust-ir v50 an exhausted address space is `OutOfMemory`, not
    // UB: the case keeps its fsym check alone (never claimed clean).
    cases.push(Case {
        ub_inputs: None,
        ..layout_case("natural_alignment_overflows_the_base_address", |f| {
            f.alloca(huge_ty(), None, None);
            f.heap(huge_ty(), None);
        })
    });
    // (3) So does materializing a GLOBAL of that type (at max(natural,
    // declared, 16)).
    {
        let (mut f, _) = FnBuilder::new("f", &[], &[Ty::I64]);
        f.value(Inst::GlobalAddr {
            global: GlobalId::new(0),
        });
        f.value(Inst::GlobalAddr {
            global: GlobalId::new(1),
        });
        f.ret_zero();
        let mut module = Module::new("global_placement_overflows_the_base_address");
        module.structs = layout_structs();
        module.globals.push(global_def("H0", huge_ty(), None));
        module.globals.push(global_def("H1", huge_ty(), None));
        f.install(&mut module);
        // Since trust-ir v50 an exhausted address space is `OutOfMemory`,
        // not UB: the case keeps its fsym check alone (never claimed clean).
        cases.push(case(
            "global_placement_overflows_the_base_address",
            module,
            None,
        ));
    }
    // (4) A whole aggregate store writes its padding (and an enum's inactive
    // tail) UNINITIALIZED: a byte-wise read across it is poison, and
    // inspecting it is UB.
    cases.push(layout_case(
        "padding_read_after_a_whole_struct_store",
        |f| {
            let slot = f.alloca(pad_ty(), None, Some(16));
            let a = f.int(Ty::U8, 1);
            let b = f.int(Ty::U64, 2);
            let value = f.value(Inst::MakeAggregate {
                ty: pad_ty(),
                variant: None,
                fields: vec![a, b],
            });
            // Explicit alignments, as the adversary's probe had them: the
            // store and the byte-wise load owe nothing but initialization.
            f.effect(Inst::Store {
                ty: pad_ty(),
                ptr: slot,
                value,
                volatile: false,
                align: Some(16),
            });
            let one = f.int(Ty::I64, 1);
            let at = f.gep(Ty::U8, slot, one);
            let x = f.load(Ty::I64, at, Some(1));
            f.bin(BinOp::Or, Ty::I64, x, x);
        },
    ));
    cases.push(layout_case(
        "padding_uninitialized_by_a_store_over_filled_bytes",
        |f| {
            let slot = f.alloca(pad_ty(), None, None);
            let fill = f.int(Ty::U8, 7);
            let sixteen = f.int(Ty::U64, 16);
            f.memset(slot, fill, sixteen);
            let value = f.value(Inst::Const {
                ty: pad_ty(),
                value: Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2)]),
            });
            f.store(pad_ty(), slot, value);
            let four = f.int(Ty::I64, 4);
            let at = f.gep(Ty::U8, slot, four);
            let x = f.load(Ty::U32, at, None);
            f.bin(BinOp::Or, Ty::U32, x, x);
        },
    ));
    cases.push(layout_case(
        "inactive_variant_tail_read_after_an_enum_store",
        |f| {
            let slot = f.alloca(Ty::Enum(EnumId::new(0)), None, None);
            let fill = f.int(Ty::U8, 0);
            let bytes = f.int(Ty::U64, 24);
            f.memset(slot, fill, bytes);
            let lane = f.int(Ty::I32, 5);
            let value = f.value(Inst::MakeAggregate {
                ty: Ty::Enum(EnumId::new(0)),
                variant: Some(1),
                fields: vec![lane],
            });
            f.store(Ty::Enum(EnumId::new(0)), slot, value);
            let sixteen = f.int(Ty::I64, 16);
            let at = f.gep(Ty::U8, slot, sixteen);
            let x = f.load(Ty::I64, at, None);
            f.bin(BinOp::Or, Ty::I64, x, x);
        },
    ));
    // (5) wasm32 and the local solver: the GEP candidate must encode the
    // 32-bit address space, or the solver proves the 64-bit condition and
    // the CLI prints proven_safe.
    {
        let (mut f, params) = FnBuilder::new("f", &[Ty::U8], &[Ty::I64]);
        let count = f.int(Ty::Usize, 16);
        let p = f.alloca(Ty::U64, Some(count), Some(16));
        let q = f.gep(Ty::I64, p, params[0]);
        let wide = f.int(Ty::Usize, 0xFFFF_FFFF);
        f.gep(Ty::U8, q, wide);
        f.ret_zero();
        let mut module = f.module("wasm32_gep_chain_past_the_address_space");
        module.target_info = Some(wasm32());
        cases.push(case(
            "wasm32_gep_chain_past_the_address_space",
            module,
            Some(vec![InterpretValue::int(Ty::U8, 3).expect("u8")]),
        ));
    }
    // (6) An annotation on an access through a PARAMETER is a claim about
    // every caller, which nothing checks: a caller handing null, a freed
    // block or an address naming no allocation runs into UB in the callee.
    for bad in 0..3 {
        let name = match bad {
            0 => "annotated_parameter_store_handed_null",
            1 => "annotated_parameter_store_handed_a_freed_block",
            _ => "annotated_parameter_store_handed_a_no_provenance_address",
        };
        let mut module = Module::new(name);
        let (mut f, _) = FnBuilder::new("f", &[], &[Ty::I64]);
        let p = match bad {
            0 => f.null(),
            1 => {
                let h = f.heap(Ty::U8, None);
                f.dealloc(h);
                h
            }
            _ => {
                let address = f.int(Ty::U64, 0x10_0000);
                f.inttoptr(address)
            }
        };
        f.call(FuncId::new(1), &[p]);
        f.ret_zero();
        f.install(&mut module);
        let (mut g, params) = FnBuilder::new("g", &[Ty::Ptr], &[]);
        let byte = g.int(Ty::U8, 1);
        g.effect_with(
            Inst::Store {
                ty: Ty::U8,
                ptr: params[0],
                value: byte,
                volatile: false,
                align: None,
            },
            vec![ProofAnnotation::NotNull, ProofAnnotation::InBounds],
        );
        g.ret(&[]);
        assert_eq!(g.install(&mut module), FuncId::new(1));
        cases.push(case(name, module, Some(Vec::new())));
    }

    // Round 6. (1) The BUDGET premise is the RUN's: `f` allocates 4096 bytes
    // at alignment 1 (modeled), but a caller placed 52 one-byte allocations
    // at alignments 2^63 .. 2^12 first, leaving the bump pointer at
    // 2^64 - 4095: `f`'s allocation overflows the next address. `f`'s own
    // claim rests on every caller's placements, so the module's placement
    // verdicts are Unknown by name.
    // The same with a caller fsym REFUSES to scan (an `undef` it never
    // admits): the premise is the module's, scanned or not.
    for refused_caller in [false, true] {
        let name = if refused_caller {
            "a_refused_caller_placing_past_4096_overflows_the_callees_allocation"
        } else {
            "a_caller_placing_past_4096_overflows_the_callees_allocation"
        };
        let mut module = Module::new(name);
        module.target_info = Some(x86_64());
        let (mut f, _) = FnBuilder::new("f", &[], &[Ty::I64]);
        let count = f.int(Ty::U64, 4096);
        f.alloca(Ty::U8, Some(count), None);
        f.ret_zero();
        f.install(&mut module);
        let (mut main, _) = FnBuilder::new("main", &[], &[Ty::I64]);
        if refused_caller {
            main.value(Inst::Undef { ty: Ty::I64 });
        }
        for shift in (12..=63).rev() {
            main.alloca(Ty::U8, None, Some(1u64 << shift));
        }
        let result = main.value(Inst::Call {
            callee: FuncId::new(0),
            args: Vec::new(),
        });
        main.ret(&[result]);
        let main = main.install(&mut module);
        let report = scan_module(&module);
        assert_eq!(
            report
                .skipped_functions
                .iter()
                .any(|skip| skip.function == "main"),
            refused_caller,
            "{name}: the caller is refused exactly when it holds an `undef`: {:?}",
            report.skipped_functions
        );
        // Since trust-ir v50 the callee's placement is `OutOfMemory` (an
        // exhausted address space), not UB: the case keeps its fsym check
        // alone (never claimed clean).
        cases.push(Case {
            ub_entry: main,
            ..case(name, module, None)
        });
    }
    // (2) Initialization masks. An enum stored with its variant UNTRACKED
    // (a select between two variants) writes its tag and the ACTIVE
    // variant's fields only: `B` leaves the bytes only `C` covers
    // uninitialized, over a filled slot.
    cases.push(layout_case_over_u8(
        "untracked_variant_enum_store_writes_only_the_active_variants_fields",
        0,
        |f, x| {
            let e = Ty::Enum(EnumId::new(0));
            let slot = f.alloca(e.clone(), None, None);
            let fill = f.int(Ty::U8, 7);
            let size = f.int(Ty::U64, 24);
            f.memset(slot, fill, size);
            let lane = f.int(Ty::I32, 5);
            let b = f.value(Inst::MakeAggregate {
                ty: e.clone(),
                variant: Some(1),
                fields: vec![lane],
            });
            let wide = f.int(Ty::I64, 6);
            let byte = f.int(Ty::U8, 7);
            let c = f.value(Inst::MakeAggregate {
                ty: e.clone(),
                variant: Some(2),
                fields: vec![wide, byte],
            });
            let zero = f.int(Ty::U8, 0);
            let is_zero = f.icmp(ICmpOp::Eq, Ty::U8, x, zero);
            let value = f.select(e.clone(), is_zero, b, c);
            f.store(e, slot, value);
            let sixteen = f.int(Ty::I64, 16);
            let at = f.gep(Ty::U8, slot, sixteen);
            let read = f.load(Ty::U8, at, None);
            f.bin(BinOp::Or, Ty::U8, read, read);
        },
    ));
    // A padded struct stored at an offset fsym cannot decide writes its
    // padding UNINITIALIZED wherever it lands: nothing of the filled buffer
    // stays proven initialized.
    cases.push(layout_case_over_u8(
        "padded_store_at_an_undecided_offset_uninitializes_its_padding",
        0,
        |f, x| {
            let count = f.int(Ty::U64, 32);
            let buf = f.alloca(Ty::U8, Some(count), Some(16));
            let fill = f.int(Ty::U8, 7);
            f.memset(buf, fill, count);
            let zero = f.int(Ty::U8, 0);
            let is_zero = f.icmp(ICmpOp::Eq, Ty::U8, x, zero);
            let low = f.int(Ty::I64, 0);
            let high = f.int(Ty::I64, 8);
            let offset = f.select(Ty::I64, is_zero, low, high);
            let at = f.gep(Ty::U8, buf, offset);
            let value = f.value(Inst::Const {
                ty: pad_ty(),
                value: Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2)]),
            });
            f.store(pad_ty(), at, value);
            let one = f.int(Ty::I64, 1);
            let padding = f.gep(Ty::U8, buf, one);
            let read = f.load(Ty::U8, padding, None);
            f.bin(BinOp::Or, Ty::U8, read, read);
        },
    ));
    // A whole-enum load needs the fields of the variant its tag names: a
    // tag written alone (`C`) leaves them uninitialized.
    cases.push(layout_case(
        "enum_load_needs_the_tagged_variants_fields",
        |f| {
            let e = Ty::Enum(EnumId::new(0));
            let slot = f.alloca(e.clone(), None, None);
            let tag = f.int(Ty::U8, 2);
            f.store(Ty::U8, slot, tag);
            f.load(e, slot, None);
        },
    ));

    // Round 7. (1) On wasm32 the interpreter keeps every placement inside
    // the 4 GiB address space (OutOfMemory past it) — but not one byte
    // short of its end: a non-empty object may END at 2^32, where a pointer
    // one past it has no address. Measured: a refused caller places 2^20 - 1
    // zero-sized allocations at alignment 4096 (padding and the byte a
    // zero-sized allocation advances are charged to no budget), leaving the
    // bump pointer at 2^32 - 4095; `f` allocates 4095 bytes and GEPs to
    // their end: "GEP: address 0x100000000 is outside the target's address
    // space". fsym judged it Safe (`end <= size`). The loop is unrolled 32
    // allocations an iteration (the run is the same, in fewer steps). Its
    // variants reach the same end cheaply (`placements_to_32_bit_end`): a GEP
    // across the end from the last byte, and the end pointer then exposed or
    // moved by zero.
    for (name, tail) in [
        (
            "a_gep_to_the_end_of_an_object_ending_at_2_pow_32_has_no_address",
            0,
        ),
        (
            "a_gep_across_the_end_of_an_object_ending_at_2_pow_32_has_no_address",
            1,
        ),
        ("a_gep_to_the_end_then_ptrtoint_at_2_pow_32", 2),
        ("a_gep_to_the_end_then_gep_0_at_2_pow_32", 3),
    ] {
        let mut module = Module::new(name);
        module.target_info = Some(wasm32());
        let (mut f, _) = FnBuilder::new("f", &[], &[Ty::I64]);
        let size = f.int(Ty::Usize, 4095);
        let p = f.alloca(Ty::U8, Some(size), None);
        let end = if tail == 1 {
            let last = f.int(Ty::I64, 4094);
            let last = f.gep(Ty::U8, p, last);
            let one = f.int(Ty::I64, 1);
            f.gep(Ty::U8, last, one)
        } else {
            let at = f.int(Ty::I64, 4095);
            f.gep(Ty::U8, p, at)
        };
        match tail {
            2 => {
                f.cast(CastOp::PtrToInt, Ty::Ptr, Ty::Usize, end);
            }
            3 => {
                let zero = f.int(Ty::I64, 0);
                f.gep(Ty::U8, end, zero);
            }
            _ => {}
        }
        f.ret_zero();
        f.install(&mut module);
        let (main, fuel) = if tail == 0 {
            (
                zero_sized_placements_then_call(&mut module, (1 << 20) - 1, FuncId::new(0)),
                1 << 24,
            )
        } else {
            (
                placements_to_32_bit_end(&mut module, 0, FuncId::new(0)),
                FUEL,
            )
        };
        cases.push(Case {
            ub_entry: main,
            options: run_options(fuel),
            ..case(name, module, Some(Vec::new()))
        });
    }
    // (2) The same end for a global: `G2 = symaddr<G1 + 4064>`,
    // `G1: [u8; 4064]`, after the same 2^20 - 1 zero-sized placements — `f`'s
    // `GlobalAddr G2` places G2, then G1 to end exactly at 2^32, and
    // encoding G2's initializer finds no address ("Store: pointer address
    // overflow"). fsym assumed every initializer window names an address.
    {
        let name = "a_global_initializer_pointing_to_a_global_ending_at_2_pow_32";
        let mut module = Module::new(name);
        module.target_info = Some(wasm32());
        module.types = vec![Ty::U8];
        module
            .globals
            .push(global_def("G1", Ty::Array(TyId::new(0), 4064), None));
        module.globals.push(global_def(
            "G2",
            Ty::PtrConst(Box::new(Ty::U8)),
            Some(Constant::SymbolAddr {
                symbol: "G1".to_string(),
                addend: 4064,
            }),
        ));
        let (mut f, _) = FnBuilder::new("f", &[], &[Ty::I64]);
        f.value(Inst::GlobalAddr {
            global: GlobalId::new(1),
        });
        f.ret_zero();
        f.install(&mut module);
        let main = zero_sized_placements_then_call(&mut module, (1 << 20) - 1, FuncId::new(0));
        cases.push(Case {
            ub_entry: main,
            options: run_options(1 << 24),
            ..case(name, module, Some(Vec::new()))
        });
    }
    // (3) A 64-bit GEP moves an allocation OFFSET and faults only when that
    // overflows u64: `gep p, u64::MAX` of a harness allocation succeeds, and
    // the `ptrtoint` after it faults ("PtrToInt: pointer address overflow").
    // fsym recorded the cast Safe ("an exact 64-bit address is its own
    // representation"): the owed verdict belongs at the raiser. Measured at
    // FSYM_ORACLE_SEED=0x1111222233334444 (case 0x89fdaf1bc259d4cd).
    // And the same pointer made by the CALLER: `f(p) { ptrtoint p }` is not
    // clean, whatever its caller hands it.
    for (name, in_callee) in [
        (
            "a_gep_past_the_address_space_then_ptrtoint_faults_at_the_cast",
            true,
        ),
        (
            "a_callers_pointer_past_the_address_space_has_no_address",
            false,
        ),
    ] {
        let mut module = Module::new(name);
        module.target_info = Some(x86_64());
        let (mut f, params) = FnBuilder::new("f", &[Ty::Ptr], &[Ty::I64]);
        let p = if in_callee {
            let wide = f.int(Ty::U64, i128::from(u64::MAX));
            f.gep(Ty::U8, params[0], wide)
        } else {
            params[0]
        };
        f.ptrtoint(p);
        f.ret_zero();
        f.install(&mut module);
        let (mut main, _) = FnBuilder::new("main", &[], &[Ty::I64]);
        let count = main.int(Ty::Usize, 16);
        let a = main.alloca(Ty::U8, Some(count), Some(8));
        let arg = if in_callee {
            a
        } else {
            let far = main.int(Ty::U64, i128::from(u64::MAX - 7));
            main.gep(Ty::U8, a, far)
        };
        let result = main.value(Inst::Call {
            callee: FuncId::new(0),
            args: vec![arg],
        });
        main.ret(&[result]);
        let main = main.install(&mut module);
        cases.push(Case {
            ub_entry: main,
            ..case(name, module, Some(Vec::new()))
        });
    }
    // The same from an address the function turns into a pointer itself
    // (`inttoptr` of the caller's allocation's address: a pointer WITH
    // provenance, whose address was checked): its address is exact, and a
    // GEP of it by u64::MAX moves the offset without faulting, so the moved
    // address is proven only where the GEP's no-wrap is.
    {
        let name = "an_integer_address_moved_past_the_address_space_faults_at_the_cast";
        let mut module = Module::new(name);
        module.target_info = Some(x86_64());
        let (mut f, params) = FnBuilder::new("f", &[Ty::U64], &[Ty::I64]);
        let p = f.inttoptr(params[0]);
        let wide = f.int(Ty::U64, i128::from(u64::MAX));
        let q = f.gep(Ty::U8, p, wide);
        f.ptrtoint(q);
        f.ret_zero();
        f.install(&mut module);
        let (mut main, _) = FnBuilder::new("main", &[], &[Ty::I64]);
        let count = main.int(Ty::Usize, 16);
        let a = main.alloca(Ty::U8, Some(count), Some(8));
        let address = main.ptrtoint(a);
        let result = main.value(Inst::Call {
            callee: FuncId::new(0),
            args: vec![address],
        });
        main.ret(&[result]);
        let main = main.install(&mut module);
        cases.push(Case {
            ub_entry: main,
            ..case(name, module, Some(Vec::new()))
        });
    }
    // (4) Initialization masks where the bytes are not decided. Each case is
    // the shape a one-line mutation of the init tracking got past every
    // committed test with: a copy from a source whose initialization is not
    // tracked (8192 bytes) or from an offset fsym cannot decide must leave
    // the destination bytes it may write UNinitialized (not "initialized");
    // a load at an undecided offset needs the whole object initialized (not
    // one byte of it); a fill whose count fsym cannot decide initializes
    // nothing proven (not the whole object).
    cases.push(layout_case(
        "a_copy_from_an_untracked_source_moves_uninitialized_bytes",
        |f| {
            let big = f.int(Ty::U64, 8192);
            let src = f.alloca(Ty::U8, Some(big), Some(8));
            let eight = f.int(Ty::U64, 8);
            let dst = f.alloca(Ty::U8, Some(eight), Some(8));
            f.effect(Inst::MemCopy {
                dst,
                src,
                bytes: eight,
                overlap: false,
            });
            let read = f.load(Ty::U64, dst, None);
            f.bin(BinOp::Or, Ty::U64, read, read);
        },
    ));
    cases.push(layout_case_over_u8(
        "a_copy_from_an_undecided_source_offset_moves_uninitialized_bytes",
        0,
        |f, x| {
            let sixteen = f.int(Ty::U64, 16);
            let src = f.alloca(Ty::U8, Some(sixteen), Some(8));
            let fill = f.int(Ty::U8, 7);
            let eight = f.int(Ty::U64, 8);
            f.memset(src, fill, eight);
            let zero = f.int(Ty::U8, 0);
            let is_zero = f.icmp(ICmpOp::Eq, Ty::U8, x, zero);
            let high = f.int(Ty::I64, 8);
            let low = f.int(Ty::I64, 0);
            let offset = f.select(Ty::I64, is_zero, high, low);
            let from = f.gep(Ty::U8, src, offset);
            let dst = f.alloca(Ty::U8, Some(eight), Some(8));
            f.effect(Inst::MemCopy {
                dst,
                src: from,
                bytes: eight,
                overlap: false,
            });
            let read = f.load(Ty::U8, dst, None);
            f.bin(BinOp::Or, Ty::U8, read, read);
        },
    ));
    cases.push(layout_case_over_u8(
        "a_load_at_an_undecided_offset_needs_every_byte_it_may_read",
        0,
        |f, x| {
            let sixteen = f.int(Ty::U64, 16);
            let buf = f.alloca(Ty::U8, Some(sixteen), Some(8));
            let fill = f.int(Ty::U8, 7);
            let eight = f.int(Ty::U64, 8);
            f.memset(buf, fill, eight);
            let zero = f.int(Ty::U8, 0);
            let is_zero = f.icmp(ICmpOp::Eq, Ty::U8, x, zero);
            let high = f.int(Ty::I64, 8);
            let low = f.int(Ty::I64, 0);
            let offset = f.select(Ty::I64, is_zero, high, low);
            let at = f.gep(Ty::U8, buf, offset);
            let read = f.load(Ty::U8, at, None);
            f.bin(BinOp::Or, Ty::U8, read, read);
        },
    ));
    cases.push(layout_case_over_u8(
        "a_fill_of_an_undecided_count_initializes_only_what_it_must",
        0,
        |f, x| {
            let sixteen = f.int(Ty::U64, 16);
            let buf = f.alloca(Ty::U8, Some(sixteen), Some(8));
            let zero = f.int(Ty::U8, 0);
            let is_zero = f.icmp(ICmpOp::Eq, Ty::U8, x, zero);
            let one = f.int(Ty::U64, 1);
            let bytes = f.select(Ty::U64, is_zero, one, sixteen);
            let fill = f.int(Ty::U8, 7);
            f.memset(buf, fill, bytes);
            let eight = f.int(Ty::I64, 8);
            let at = f.gep(Ty::U8, buf, eight);
            let read = f.load(Ty::U8, at, None);
            f.bin(BinOp::Or, Ty::U8, read, read);
        },
    ));
    // A fill of a count fsym cannot decide is in bounds only if its start,
    // its length and its end are (`check_symbolic_bulk_bounds`): each of the
    // three is needed, since 64-bit arithmetic on the end alone wraps — from
    // an offset past the address space (u64::MAX, a count of 2 or 3), or for
    // a count longer than it (2^64 - 7 or - 6 bytes from offset 8), the end
    // wraps into the object while the interpreter faults ("access range
    // overflow").
    for (name, at, low, high) in [
        (
            "a_fill_of_an_undecided_count_from_past_the_address_space",
            u64::MAX,
            2,
            3,
        ),
        (
            "a_fill_of_an_undecided_count_longer_than_the_address_space",
            8,
            u64::MAX - 6,
            u64::MAX - 5,
        ),
    ] {
        cases.push(layout_case_over_u8(name, 0, |f, x| {
            let sixteen = f.int(Ty::U64, 16);
            let buf = f.alloca(Ty::U8, Some(sixteen), Some(8));
            let at = f.int(Ty::U64, i128::from(at));
            let dst = f.gep(Ty::U8, buf, at);
            let zero = f.int(Ty::U8, 0);
            let is_zero = f.icmp(ICmpOp::Eq, Ty::U8, x, zero);
            let low = f.int(Ty::U64, i128::from(low));
            let high = f.int(Ty::U64, i128::from(high));
            let bytes = f.select(Ty::U64, is_zero, low, high);
            let fill = f.int(Ty::U8, 7);
            f.memset(dst, fill, bytes);
        }));
    }
    // Round 8 (the round-7 verifier). A placement whose own footprint reaches
    // 2^62 bytes was decided on a budget bound alone. Measured before trust-ir
    // v50: `alloca u8 x u64::MAX` scanned clean on wasm32 and x86_64 while the
    // interpreter with an unbounded memory budget faulted "Alloca: next
    // address overflow"; at 32 bits `alloca u8 x 2^63, align 2^63` faulted
    // the same way from its 2^63 base; so did a heap block and a global that
    // large. Since v50 the interpreter has no budget and exhausting the
    // address space is `OutOfMemory`, not UB, so these shapes raise no UB to
    // attribute: fsym is checked alone, and must still never claim them
    // clean (each placement is an Unknown naming the 2^62-byte bound).
    for (name, target, count, align, heap) in [
        (
            "an_allocation_as_large_as_the_address_space_on_wasm32",
            wasm32(),
            u64::MAX,
            Some(1),
            false,
        ),
        (
            "an_allocation_as_large_as_the_address_space_on_x86_64",
            x86_64(),
            u64::MAX,
            Some(1),
            false,
        ),
        (
            "a_heap_allocation_as_large_as_the_address_space_on_wasm32",
            wasm32(),
            u64::MAX,
            None,
            true,
        ),
        (
            "a_heap_allocation_as_large_as_the_address_space_on_x86_64",
            x86_64(),
            u64::MAX,
            None,
            true,
        ),
        (
            "a_2_pow_63_allocation_at_alignment_2_pow_63_on_wasm32",
            wasm32(),
            1 << 63,
            Some(1 << 63),
            false,
        ),
    ] {
        let mut module = Module::new(name);
        module.target_info = Some(target);
        let (mut f, _) = FnBuilder::new("f", &[], &[Ty::I64]);
        let count = f.int(Ty::U64, i128::from(count));
        if heap {
            f.heap(Ty::U8, Some(count));
        } else {
            f.alloca(Ty::U8, Some(count), align);
        }
        f.ret_zero();
        f.install(&mut module);
        cases.push(case(name, module, None));
    }
    for (name, target) in [
        ("a_global_as_large_as_the_address_space_on_wasm32", wasm32()),
        ("a_global_as_large_as_the_address_space_on_x86_64", x86_64()),
    ] {
        let mut module = Module::new(name);
        module.target_info = Some(target);
        module.types = vec![Ty::U8];
        module
            .globals
            .push(global_def("Huge", Ty::Array(TyId::new(0), u64::MAX), None));
        let (mut f, _) = FnBuilder::new("f", &[], &[Ty::I64]);
        f.value(Inst::GlobalAddr {
            global: GlobalId::new(0),
        });
        f.ret_zero();
        f.install(&mut module);
        cases.push(case(name, module, None));
    }
    cases
}

/// Append `main() -> i64`: an `undef` (fsym refuses it), `count`
/// zero-sized allocations at alignment 4096 — 32 an iteration of a loop,
/// the rest straight — then a call of `f`. From fresh memory the bump
/// pointer ends at `4096 * count + 1`.
fn zero_sized_placements_then_call(module: &mut Module, count: u64, f: FuncId) -> FuncId {
    let (mut main, _) = FnBuilder::new("main", &[], &[Ty::I64]);
    main.value(Inst::Undef { ty: Ty::I64 });
    let place = |main: &mut FnBuilder| {
        main.alloca(Ty::Unit, None, Some(4096));
    };
    let (header, counter) = main.block(&[Ty::U64]);
    let (body, _) = main.block(&[]);
    let (exit, _) = main.block(&[]);
    let zero = main.int(Ty::U64, 0);
    main.br(header, &[zero]);
    main.switch_to(header);
    let trips = main.int(Ty::U64, i128::from(count / 32));
    let more = main.icmp(ICmpOp::Ult, Ty::U64, counter[0], trips);
    main.condbr(more, body, exit);
    main.switch_to(body);
    for _ in 0..32 {
        place(&mut main);
    }
    let one = main.int(Ty::U64, 1);
    let next = main.bin(BinOp::Add, Ty::U64, counter[0], one);
    main.br(header, &[next]);
    main.switch_to(exit);
    for _ in 0..count % 32 {
        place(&mut main);
    }
    let result = main.value(Inst::Call {
        callee: f,
        args: Vec::new(),
    });
    main.ret(&[result]);
    main.install(module)
}

/// Append `main() -> i64` for a 32-bit target: one-byte allocations at
/// alignments `2^31 .. 2^12` (the bump pointer then at `2^32 - 4095`), then
/// `gap` more bytes, then a call of `f`: an allocation `f` makes next of
/// `4095 - gap` bytes (at alignment 1) ends exactly at 2^32.
fn placements_to_32_bit_end(module: &mut Module, gap: u64, f: FuncId) -> FuncId {
    let (mut main, _) = FnBuilder::new("main", &[], &[Ty::I64]);
    for shift in (12..=31).rev() {
        main.alloca(Ty::U8, None, Some(1u64 << shift));
    }
    if gap > 0 {
        let gap = main.int(Ty::Usize, i128::from(gap));
        main.alloca(Ty::U8, Some(gap), Some(1));
    }
    let result = main.value(Inst::Call {
        callee: f,
        args: Vec::new(),
    });
    main.ret(&[result]);
    main.install(module)
}

/// `f(x: u8) -> i64` over the layout world: `body` builds the entry block
/// over `x`, the function returns zero, and the interpreter must report UB
/// on `input`.
fn layout_case_over_u8(
    name: &'static str,
    input: i128,
    body: impl FnOnce(&mut FnBuilder, ValueId),
) -> Case {
    let (mut f, params) = FnBuilder::new("f", &[Ty::U8], &[Ty::I64]);
    body(&mut f, params[0]);
    f.ret_zero();
    let mut module = Module::new(name);
    module.types = vec![Ty::I32, Ty::Bool];
    module.enums.push(generated_enum());
    module.structs = layout_structs();
    f.install(&mut module);
    case(
        name,
        module,
        Some(vec![InterpretValue::int(Ty::U8, input).expect("u8")]),
    )
}

/// `f() -> i64` over a module declaring the layout world (`layout_structs`,
/// `generated_enum`): `body` builds the entry block, the function returns
/// zero, and the interpreter must report UB.
fn layout_case(name: &'static str, body: impl FnOnce(&mut FnBuilder)) -> Case {
    let (mut f, _) = FnBuilder::new("f", &[], &[Ty::I64]);
    body(&mut f);
    f.ret_zero();
    let mut module = Module::new(name);
    module.types = vec![Ty::I32, Ty::Bool];
    module.enums.push(generated_enum());
    module.structs = layout_structs();
    f.install(&mut module);
    case(name, module, Some(Vec::new()))
}

/// `f() -> i64` over a module declaring `generated_enum()`: `body` builds
/// the entry block, the function returns zero.
fn enum_case(name: &'static str, body: impl FnOnce(&mut FnBuilder)) -> Case {
    let (mut f, _) = FnBuilder::new("f", &[], &[Ty::I64]);
    body(&mut f);
    f.ret_zero();
    let mut module = Module::new(name);
    module.enums.push(generated_enum());
    f.install(&mut module);
    case(name, module, Some(Vec::new()))
}

#[test]
fn char_scope_attribution_requires_the_exact_site_and_actual_named_refusal() {
    use trust_cg_verify::fsym_ub_map::CHAR_BINDINGS_REFUSED;
    let site = FSYM_INTERPRETER_UB_SITES
        .iter()
        .find(|site| site.function == "check_char_validity")
        .expect("the newly mapped site");
    let (mut f, params) = FnBuilder::new("f", &[Ty::Char], &[Ty::Char]);
    f.ret(&params);
    let module = f.module("char_scope");
    assert!(char_scope_refusal_confirmed(
        &module,
        &module.functions[0],
        site,
        CHAR_BINDINGS_REFUSED
    ));
    let mut wrong_site = *site;
    wrong_site.function = "expect_pointer";
    assert!(!char_scope_refusal_confirmed(
        &module,
        &module.functions[0],
        &wrong_site,
        CHAR_BINDINGS_REFUSED
    ));
    assert!(!char_scope_refusal_confirmed(
        &module,
        &module.functions[0],
        site,
        "unreviewed scope claim"
    ));

    let (mut f, _) = FnBuilder::new("f", &[], &[Ty::I64]);
    f.value(Inst::Undef { ty: Ty::I64 });
    f.ret_zero();
    let unrelated = f.module("unrelated_skip");
    assert!(
        !scan_function_in_module(&unrelated, &unrelated.functions[0])
            .skipped_functions
            .is_empty()
    );
    assert!(!char_scope_refusal_confirmed(
        &unrelated,
        &unrelated.functions[0],
        site,
        CHAR_BINDINGS_REFUSED
    ));
    let (mut f, _) = FnBuilder::new("f", &[], &[Ty::I64]);
    f.ret_zero();
    let admitted = f.module("ordinary_integer");
    assert!(!char_scope_refusal_confirmed(
        &admitted,
        &admitted.functions[0],
        site,
        CHAR_BINDINGS_REFUSED
    ));
}

#[test]
fn regression_corpus_is_never_reported_clean() {
    let mut failures = Vec::new();
    for case in regression_corpus() {
        let Some(report) = scan_catching_panics(&case.module) else {
            failures.push(format!("{}: scan_module panicked", case.name));
            continue;
        };
        if let Some(inputs) = &case.ub_inputs {
            // A case outside the run model says so, and why its verdict does
            // not rest on the model; every other case runs inside it.
            match (
                FSYM_RUN_MODEL.breach(&case.options, inputs),
                case.outside_run_model,
            ) {
                (None, None) | (Some(_), Some(_)) => {}
                (Some(breach), None) => failures.push(format!(
                    "{}: its run is outside fsym's run model ({breach}), and the case does not say why the verdict holds there",
                    case.name
                )),
                (None, Some(_)) => failures.push(format!(
                    "{}: says its run is outside fsym's run model, and it is inside",
                    case.name
                )),
            }
            match interpret_with(&case.module, case.ub_entry, inputs, case.options) {
                Run::Ub(error) => {
                    // The UB map must owe it where it was raised.
                    let split = split_module(case.module.clone());
                    match attribute(&split, case.ub_entry, inputs, &error, case.options).and_then(
                        |observed| owed_verdict_reported(&split.module, &report, &observed),
                    ) {
                        Ok(()) => {}
                        Err(why) => failures.push(format!("{}: {why}", case.name)),
                    }
                }
                other => failures.push(format!(
                    "{}: the interpreter must report UB on this case, got {other:?}",
                    case.name
                )),
            }
        }
        // The claim is the function's AND its callees', as scanned or after
        // the bounded local solver (the generated corpus's claim).
        let f = FuncId::new(0);
        if claimed_clean(&case.module, &report, f)
            || claimed_clean_after_solver(&case.module, &report, f)
        {
            failures.push(format!(
                "{}: fsym reports the function clean: {}",
                case.name,
                fsym_summary_line(&report, "f")
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "{} regression case(s) failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// `scan_module`, with a panic (a scanner crash) reported as `None`.
fn scan_catching_panics(module: &Module) -> Option<FsymTrustIrReport> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| scan_module(module))).ok()
}

/// A caller handing an alloca to a bodied callee the scanner refuses
/// (`CallIndirect`) was CLEAN in the per-function codegen summary.
#[test]
fn caller_handing_a_pointer_to_a_skipped_callee_is_not_clean() {
    let mut module = Module::new("skipped_callee");
    let (mut f, _) = FnBuilder::new("f", &[], &[Ty::I64]);
    let a = f.alloca(Ty::I64, None, None);
    f.call(FuncId::new(1), &[a]);
    f.ret_zero();
    f.install(&mut module);
    let (mut g, params) = FnBuilder::new("g", &[Ty::Ptr], &[]);
    g.effect(Inst::CallIndirect {
        callee: params[0],
        sig: FuncTyId::new(1),
        args: vec![],
        calling_conv: trust_ir::CallingConv::default(),
    });
    g.ret(&[]);
    assert_eq!(g.install(&mut module), FuncId::new(1));

    let caller = &module.functions[0];
    let report = scan_function_in_module(&module, caller);
    let summary = FsymSummary::from_trust_ir_report(report.clone());
    let outcome = summary
        .functions
        .iter()
        .find(|summary| summary.function == "f")
        .map(|summary| summary.outcome);
    assert_ne!(
        outcome,
        Some(FsymFunctionOutcome::NoConcreteUb),
        "caller summary is clean: {}",
        fsym_summary_line(&report, "f")
    );
    let callee = scan_function_in_module(&module, &module.functions[1]);
    assert_eq!(callee.skipped_functions.len(), 1, "the callee is refused");
}

/// A chain of `levels` `Switch` blocks on a free `u8` selector, each forking
/// 9 ways (8 cases and the default) to the next: `9^levels` paths through
/// `levels + 2` blocks, and no obligation anywhere.
fn switch_chain(levels: usize) -> Module {
    let (mut f, params) = FnBuilder::new("f", &[Ty::U8], &[Ty::I64]);
    let mut blocks = Vec::new();
    for _ in 0..levels {
        blocks.push(f.block(&[]).0);
    }
    let (exit, _) = f.block(&[]);
    blocks.push(exit);
    f.br(blocks[0], &[]);
    for level in 0..levels {
        f.switch_to(blocks[level]);
        let next = blocks[level + 1];
        f.switch(params[0], next, (1..=8).map(|case| (case, next)).collect());
    }
    f.switch_to(exit);
    f.ret_zero();
    f.module("switch_chain")
}

/// The walk stays bounded and, past its bound, names the function Unknown by
/// `ScanBound` — and ONLY by it: the same chain below the bound scans clean,
/// so the bound (not some other obligation) is what keeps it from clean.
#[test]
fn switch_chain_is_bounded_and_never_clean() {
    // As many levels as the block bound admits (entry + levels + exit), so
    // the function is WALKED, not refused as TooLarge.
    let levels = FSYM_TRUST_IR_MAX_BLOCKS - 2;
    let paths = 9f64.powi(levels as i32);
    assert!(paths > FSYM_TRUST_IR_MAX_PATH_STATES as f64);
    let module = switch_chain(levels);
    assert_eq!(module.functions[0].blocks.len(), FSYM_TRUST_IR_MAX_BLOCKS);

    let started = Instant::now();
    let report = scan_module(&module);
    let elapsed = started.elapsed();
    assert!(
        elapsed < Duration::from_secs(20),
        "a {levels}-level switch chain took {elapsed:?}"
    );
    assert!(
        report.skipped_functions.is_empty(),
        "the chain must be walked, not refused: {:?}",
        report.skipped_functions
    );
    assert!(
        !fsym_clean(&report, "f"),
        "a walk cut short by its bound must not be clean: {}",
        fsym_summary_line(&report, "f")
    );
    assert!(report.diagnostics.is_empty() && report.coverage_errors.is_empty());
    assert!(
        !report.unknown_obligations.is_empty()
            && report
                .unknown_obligations
                .iter()
                .all(|unknown| unknown.kind == FsymTrustIrDiagnosticKind::ScanBound),
        "the only Unknown must be the ScanBound one: {}",
        fsym_summary_line(&report, "f")
    );

    // The same chain with the most levels whose every path fits the bound
    // (1 + 9 + ... + 9^k block visits) scans CLEAN.
    let mut short = 0;
    while (0..=short + 1)
        .map(|level| 9usize.pow(level as u32))
        .sum::<usize>()
        < FSYM_TRUST_IR_MAX_PATH_STATES
    {
        short += 1;
    }
    assert!(short >= 2, "the bound admits a {short}-level chain only");
    let report = scan_module(&switch_chain(short));
    assert!(
        fsym_clean(&report, "f"),
        "a {short}-level chain within the bound must scan clean: {}",
        fsym_summary_line(&report, "f")
    );
}

// ---------------------------------------------------------------------------
// Generated corpus
// ---------------------------------------------------------------------------

/// SplitMix64: a fixed, portable PRNG so the corpus is identical on every run.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, bound: u64) -> u64 {
        self.next() % bound
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.below(100) < percent
    }

    fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.below(items.len() as u64) as usize]
    }
}

/// The module-level facts one generated case is built against: its target
/// (none, 64-bit, or wasm32 — `Usize` / `Isize` exist only on a pinned
/// target), the enum / tuple / vector / array / sequence types its values
/// use, and the callees and global it may reach.
struct World {
    pointer_bits: Option<u32>,
    enum_ty: Ty,
    enum_tag_ty: Ty,
    tuple_ty: Ty,
    vector_ty: Ty,
    array_ty: Ty,
    seq_ty: Ty,
    bool_seq_ty: Ty,
    /// A bodied module function `g(params) -> i64` the function under test
    /// may call (its own scan must be clean for the caller to be).
    callee: Option<(FuncId, Vec<Ty>)>,
    /// A body-less declaration: the interpreter cannot run it, fsym owes an
    /// UnsummarizedCall verdict for a pointer handed to it.
    external: Option<(FuncId, Vec<Ty>)>,
    global: Option<GlobalId>,
    /// The first of two globals of `huge_ty()` (natural alignment 2^63):
    /// materializing one after another such allocation overflows the
    /// interpreter's base address.
    huge_global: Option<GlobalId>,
}

/// The layout world's structs. Every size, offset, stride and alignment of
/// them is the interpreter's, which fsym must use exactly:
///
/// * `Pad { a: u8, b: u64 }`, no declared layout: synthesized a@0, b@8,
///   size 16, align 8 — bytes 1..8 are padding a whole store leaves
///   uninitialized;
/// * `Declared { x: u8 }` declared at offset 8, size 16, align 1;
/// * `Big { x: u8 }` declared size 2^62, align 1 (a GEP stride that
///   overflows at index 4);
/// * `Huge`, zero-sized, declared align 2^63: two allocations of it (or of a
///   global of it) overflow the interpreter's base address.
fn layout_structs() -> Vec<StructDef> {
    let field = |name: &str, ty: Ty, offset: Option<u64>| FieldDef {
        name: name.to_string(),
        ty,
        offset,
    };
    let def = |id: u32, name: &str, fields: Vec<FieldDef>, size, align| StructDef {
        origin: None,
        id: StructId::new(id),
        name: name.to_string(),
        fields,
        size,
        align,
        repr: StructRepr::Rust,
    };
    vec![
        def(
            0,
            "Pad",
            vec![field("a", Ty::U8, None), field("b", Ty::U64, None)],
            None,
            None,
        ),
        def(
            1,
            "Declared",
            vec![field("x", Ty::U8, Some(8))],
            Some(16),
            Some(1),
        ),
        def(
            2,
            "Big",
            vec![field("x", Ty::U8, Some(0))],
            Some(1 << 62),
            Some(1),
        ),
        def(3, "Huge", vec![], Some(0), Some(1 << 63)),
    ]
}

fn pad_ty() -> Ty {
    Ty::Struct(StructId::new(0))
}

fn declared_ty() -> Ty {
    Ty::Struct(StructId::new(1))
}

fn big_ty() -> Ty {
    Ty::Struct(StructId::new(2))
}

fn huge_ty() -> Ty {
    Ty::Struct(StructId::new(3))
}

/// `<4 x bool>`: one byte a lane (4 bytes, align 1) to the interpreter.
fn bool_vector_ty() -> Ty {
    Ty::Vector(Box::new(Ty::Bool), 4)
}

/// `enum E { A, B(i32), C(i64, u8) }` (implicit discriminants 0, 1, 2).
fn generated_enum() -> EnumDef {
    let variant = |name: &str, fields: Vec<Ty>| EnumVariant {
        name: name.to_string(),
        fields,
        field_names: Vec::new(),
    };
    EnumDef::new(
        EnumId::new(0),
        "E",
        vec![
            variant("A", vec![]),
            variant("B", vec![Ty::I32]),
            variant("C", vec![Ty::I64, Ty::U8]),
        ],
    )
}

/// The payload lanes of `E`, per variant.
fn enum_lanes(variant: u32) -> Vec<Ty> {
    match variant {
        0 => vec![],
        1 => vec![Ty::I32],
        _ => vec![Ty::I64, Ty::U8],
    }
}

fn x86_64() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: "x86_64-unknown-linux-gnu".to_string(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::default(),
    }
}

fn world(rng: &mut Rng) -> World {
    let pointer_bits = match rng.below(10) {
        0..=5 => None,
        6 | 7 => Some(64),
        _ => Some(32),
    };
    let enum_tag_ty = generated_enum()
        .canonical_tag_repr()
        .expect("E has a canonical tag")
        .ty();
    World {
        pointer_bits,
        enum_ty: Ty::Enum(EnumId::new(0)),
        enum_tag_ty,
        tuple_ty: Ty::Tuple(vec![Ty::I32, Ty::I64]),
        vector_ty: Ty::Vector(Box::new(Ty::I32), 4),
        array_ty: Ty::Array(TyId::new(0), 4),
        seq_ty: Ty::Sequence(TyId::new(0)),
        bool_seq_ty: Ty::Sequence(TyId::new(1)),
        callee: None,
        external: None,
        global: None,
        huge_global: None,
    }
}

/// An empty module carrying `world`'s target, type tables, enum and global.
fn world_module(name: &str, world: &World) -> Module {
    let mut module = Module::new(name);
    module.target_info = match world.pointer_bits {
        None => None,
        Some(64) => Some(x86_64()),
        Some(_) => Some(wasm32()),
    };
    module.types = vec![Ty::I32, Ty::Bool];
    module.enums.push(generated_enum());
    module.structs = layout_structs();
    if world.global.is_some() || world.huge_global.is_some() {
        module
            .globals
            .push(global_def("G", Ty::I64, Some(Constant::Int(7))));
        module.globals.push(global_def("H", huge_ty(), None));
        module.globals.push(global_def("H2", huge_ty(), None));
    }
    module
}

fn global_def(name: &str, ty: Ty, initializer: Option<Constant>) -> trust_ir::Global {
    trust_ir::Global {
        name: name.to_string(),
        ty,
        mutable: true,
        initializer,
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    }
}

const FLOATS: [f64; 22] = [
    0.0,
    -0.0,
    0.5,
    -0.5,
    1.5,
    -1.0,
    3.0,
    100.25,
    127.0,
    128.0,
    255.0,
    256.0,
    -128.0,
    -129.0,
    2_147_483_647.0,
    2_147_483_648.0,
    -2_147_483_649.0,
    4_294_967_296.0,
    9.3e18,
    1.9e19,
    f64::INFINITY,
    f64::NAN,
];

/// A pointer value in scope; `exact` when it is built from constants only
/// (an allocation, null, a constant or `inttoptr` of one, a GEP of an exact
/// pointer by a constant, a borrow of one) — the scanner then knows its
/// provenance or address EXACTLY, so a proof annotation on an access through
/// it must never be honored against those facts. Annotations are generated on
/// exact pointers only: on a parameter or a loaded pointer an annotation is a
/// precondition fsym assumes (the interpreter would be free to violate it).
#[derive(Clone, Copy)]
struct PtrVal {
    id: ValueId,
    exact: bool,
}

/// Values in scope in one block.
#[derive(Clone, Default)]
struct Scope {
    ints: Vec<(ValueId, Ty)>,
    ptrs: Vec<PtrVal>,
    bools: Vec<ValueId>,
    floats: Vec<(ValueId, Ty)>,
    /// `Vector(I32, 4)` / `Array(I32, 4)` values with their type.
    lanes: Vec<(ValueId, Ty)>,
    enums: Vec<ValueId>,
    tuples: Vec<ValueId>,
}

impl Scope {
    fn int_of(&self, rng: &mut Rng, ty: &Ty) -> Option<ValueId> {
        let candidates = self
            .ints
            .iter()
            .filter(|(_, candidate)| candidate == ty)
            .map(|(value, _)| *value)
            .collect::<Vec<_>>();
        (!candidates.is_empty()).then(|| *rng.pick(&candidates))
    }

    fn float_of(&self, rng: &mut Rng, ty: &Ty) -> Option<ValueId> {
        let candidates = self
            .floats
            .iter()
            .filter(|(_, candidate)| candidate == ty)
            .map(|(value, _)| *value)
            .collect::<Vec<_>>();
        (!candidates.is_empty()).then(|| *rng.pick(&candidates))
    }
}

struct Gen<'r> {
    rng: &'r mut Rng,
    f: FnBuilder,
    world: &'r World,
    /// Only the function under test calls (the callee does not).
    may_call: bool,
}

impl Gen<'_> {
    fn int_tys(&self) -> Vec<Ty> {
        let mut tys = vec![Ty::I64, Ty::U64, Ty::I32, Ty::U8, Ty::I8];
        if self.world.pointer_bits.is_some() {
            tys.extend([Ty::Usize, Ty::Isize]);
        }
        tys
    }

    fn index_tys(&self) -> Vec<Ty> {
        let mut tys = vec![Ty::I64, Ty::U64, Ty::I32, Ty::U8, Ty::I8];
        if self.world.pointer_bits.is_some() {
            tys.push(Ty::Usize);
        }
        tys
    }

    /// The byte-count type of `MemSet` / `MemCopy` (and a count's usual
    /// type): `Usize` on a pinned target, `U64` otherwise.
    fn size_ty(&self) -> Ty {
        if self.world.pointer_bits.is_some() {
            Ty::Usize
        } else {
            Ty::U64
        }
    }

    fn width(&self, ty: &Ty) -> u32 {
        world_width(self.world, ty)
    }

    fn interesting(&mut self, ty: &Ty) -> i128 {
        let bits = self.width(ty);
        interesting_at(self.rng, bits, ty.is_signed())
    }

    fn fresh_int(&mut self, scope: &mut Scope, ty: &Ty) -> ValueId {
        let value = self.interesting(ty);
        let id = self.f.int(ty.clone(), value);
        scope.ints.push((id, ty.clone()));
        id
    }

    fn int_value(&mut self, scope: &mut Scope, ty: &Ty) -> ValueId {
        if self.rng.chance(60)
            && let Some(value) = scope.int_of(self.rng, ty)
        {
            return value;
        }
        self.fresh_int(scope, ty)
    }

    fn ptr_value(&mut self, scope: &mut Scope) -> PtrVal {
        if !scope.ptrs.is_empty() && self.rng.chance(85) {
            return *self.rng.pick(&scope.ptrs);
        }
        self.alloca(scope)
    }

    fn bool_value(&mut self, scope: &mut Scope) -> ValueId {
        if !scope.bools.is_empty() && self.rng.chance(50) {
            return *self.rng.pick(&scope.bools);
        }
        let id = if self.rng.chance(15) {
            // A Bool from an integer's low bit.
            let ty = self.rng.pick(&self.int_tys()).clone();
            let int = self.int_value(scope, &ty);
            self.f.cast(CastOp::Trunc, ty, Ty::Bool, int)
        } else if self.rng.chance(10) {
            let ty = self.rng.pick(&[Ty::F64, Ty::F32]).clone();
            let lhs = self.float_value(scope, &ty);
            let rhs = self.float_value(scope, &ty);
            let op = *self.rng.pick(&[
                FCmpOp::OEq,
                FCmpOp::OLt,
                FCmpOp::OGe,
                FCmpOp::UNe,
                FCmpOp::ULt,
            ]);
            self.f.value(Inst::FCmp { op, ty, lhs, rhs })
        } else {
            let ty = self.rng.pick(&self.int_tys()).clone();
            let lhs = self.int_value(scope, &ty);
            let rhs = self.int_value(scope, &ty);
            let op = *self.rng.pick(&[
                ICmpOp::Eq,
                ICmpOp::Ne,
                ICmpOp::Ult,
                ICmpOp::Ule,
                ICmpOp::Ugt,
                ICmpOp::Uge,
                ICmpOp::Slt,
                ICmpOp::Sle,
                ICmpOp::Sgt,
                ICmpOp::Sge,
            ]);
            self.f.icmp(op, ty, lhs, rhs)
        };
        scope.bools.push(id);
        id
    }

    fn float_value(&mut self, scope: &mut Scope, ty: &Ty) -> ValueId {
        if self.rng.chance(50)
            && let Some(value) = scope.float_of(self.rng, ty)
        {
            return value;
        }
        let id = if self.rng.chance(25) {
            // An integer converted to a float.
            let src = self.rng.pick(&self.int_tys()).clone();
            let int = self.int_value(scope, &src);
            let op = if src.is_signed() {
                CastOp::SIToFP
            } else {
                CastOp::UIToFP
            };
            self.f.cast(op, src, ty.clone(), int)
        } else {
            let value = *self.rng.pick(&FLOATS);
            self.f.value(Inst::Const {
                ty: ty.clone(),
                value: Constant::Float(value),
            })
        };
        scope.floats.push((id, ty.clone()));
        id
    }

    fn count(&mut self, scope: &mut Scope) -> Option<ValueId> {
        match self.rng.below(10) {
            0..=5 => None,
            6..=8 => {
                let count = *self.rng.pick(&[1, 2, 4, 8, 16, 0]);
                let mut tys = vec![Ty::U64, Ty::I64, Ty::U8];
                if self.world.pointer_bits.is_some() {
                    tys.push(Ty::Usize);
                }
                let ty = self.rng.pick(&tys).clone();
                Some(self.f.int(ty, count))
            }
            _ => {
                let ty = self.rng.pick(&[Ty::U64, Ty::U8, self.size_ty()]).clone();
                Some(self.int_value(scope, &ty))
            }
        }
    }

    fn alloca(&mut self, scope: &mut Scope) -> PtrVal {
        let ty = self.rng.pick(&access_tys()).clone();
        let count = self.count(scope);
        let align = if self.rng.chance(60) {
            None
        } else {
            Some(*self.rng.pick(&[1, 2, 4, 8, 16]))
        };
        let id = self.f.alloca(ty, count, align);
        let ptr = PtrVal { id, exact: true };
        scope.ptrs.push(ptr);
        ptr
    }

    /// Proof annotations for an access through `ptr`: often on exact
    /// pointers (whose facts an annotation must never override), and
    /// sometimes on any pointer — a parameter a caller hands null, a freed
    /// block or an address naming no allocation, a pointer loaded from
    /// memory: an annotation nothing checks is a claim, never a proof.
    fn proofs(&mut self, ptr: PtrVal) -> Vec<ProofAnnotation> {
        let chance = if ptr.exact { 25 } else { 12 };
        if !self.rng.chance(chance) {
            return Vec::new();
        }
        match self.rng.below(3) {
            0 => vec![ProofAnnotation::NotNull],
            1 => vec![ProofAnnotation::InBounds],
            _ => vec![ProofAnnotation::NotNull, ProofAnnotation::InBounds],
        }
    }

    fn gep(&mut self, scope: &mut Scope) {
        let base = self.ptr_value(scope);
        let pointee = self.rng.pick(&[Ty::U8, Ty::U32, Ty::I64]).clone();
        let (inst, exact) = if self.rng.chance(8) {
            (
                Inst::GEP {
                    pointee_ty: pointee,
                    base: base.id,
                    indices: vec![],
                    inbounds: self.rng.chance(50),
                },
                base.exact,
            )
        } else {
            let index_ty = self.rng.pick(&self.index_tys()).clone();
            // A fresh constant index keeps an exact base exact.
            let (index, fresh) = if self.rng.chance(50) {
                (self.fresh_int(scope, &index_ty), true)
            } else {
                (self.int_value(scope, &index_ty), false)
            };
            (
                Inst::GEP {
                    pointee_ty: pointee,
                    base: base.id,
                    indices: vec![index],
                    inbounds: self.rng.chance(50),
                },
                base.exact && fresh,
            )
        };
        let proofs = if base.exact && self.rng.chance(15) {
            vec![ProofAnnotation::NotNull]
        } else {
            Vec::new()
        };
        let id = self.f.value_with(inst, proofs);
        scope.ptrs.push(PtrVal { id, exact });
    }

    fn load(&mut self, scope: &mut Scope) {
        let ptr = self.ptr_value(scope);
        let proofs = self.proofs(ptr);
        let align = if self.rng.chance(75) {
            None
        } else {
            Some(*self.rng.pick(&[1, 2, 4, 8, 16]))
        };
        if self.rng.chance(10) {
            // A pointer loaded from memory: no tracked provenance.
            let id = self.f.value_with(
                Inst::Load {
                    ty: Ty::Ptr,
                    ptr: ptr.id,
                    volatile: false,
                    align,
                },
                proofs,
            );
            scope.ptrs.push(PtrVal { id, exact: false });
            return;
        }
        let ty = self.rng.pick(&access_tys()).clone();
        let id = self.f.value_with(
            Inst::Load {
                ty: ty.clone(),
                ptr: ptr.id,
                volatile: self.rng.chance(10),
                align,
            },
            proofs,
        );
        scope.ints.push((id, ty));
    }

    fn store(&mut self, scope: &mut Scope) {
        let ptr = self.ptr_value(scope);
        let proofs = self.proofs(ptr);
        let align = if self.rng.chance(80) {
            None
        } else {
            Some(*self.rng.pick(&[1, 2, 4, 8, 16]))
        };
        let (ty, value) = match self.rng.below(10) {
            // A pointer value stored to memory.
            0 => (Ty::Ptr, self.ptr_value(scope).id),
            1 if self.world.pointer_bits.is_some() => {
                let value = self.int_value(scope, &Ty::Usize);
                (Ty::Usize, value)
            }
            _ => {
                let ty = self.rng.pick(&access_tys()).clone();
                let value = self.int_value(scope, &ty);
                (ty, value)
            }
        };
        self.f.effect_with(
            Inst::Store {
                ty,
                ptr: ptr.id,
                value,
                volatile: false,
                align,
            },
            proofs,
        );
    }

    fn int_binop(&mut self, scope: &mut Scope) {
        let ty = self.rng.pick(&self.int_tys()).clone();
        let op = *self.rng.pick(&[
            BinOp::Add,
            BinOp::Sub,
            BinOp::Mul,
            BinOp::UDiv,
            BinOp::SDiv,
            BinOp::URem,
            BinOp::SRem,
            BinOp::Shl,
            BinOp::LShr,
            BinOp::AShr,
            BinOp::And,
            BinOp::Or,
            BinOp::Xor,
            BinOp::RotL,
        ]);
        let lhs = self.int_value(scope, &ty);
        let rhs = self.int_value(scope, &ty);
        let id = self.f.bin(op, ty.clone(), lhs, rhs);
        scope.ints.push((id, ty));
    }

    /// `Bool` <-> integer casts: `(a < b) as u64` (zext / sext of a Bool),
    /// and truncation of an integer to `Bool`; the widened value is often
    /// used at once as a divisor or shift amount.
    fn bool_cast(&mut self, scope: &mut Scope) {
        if self.rng.chance(25) {
            let ty = self.rng.pick(&self.int_tys()).clone();
            let int = self.int_value(scope, &ty);
            let id = self.f.cast(CastOp::Trunc, ty, Ty::Bool, int);
            scope.bools.push(id);
            return;
        }
        let cond = self.bool_value(scope);
        let dst = self.rng.pick(&self.int_tys()).clone();
        let op = if self.rng.chance(50) {
            CastOp::ZExt
        } else {
            CastOp::SExt
        };
        let id = self.f.cast(op, Ty::Bool, dst.clone(), cond);
        scope.ints.push((id, dst.clone()));
        if self.rng.chance(60) {
            let lhs = self.int_value(scope, &dst);
            let op = *self.rng.pick(&[
                BinOp::UDiv,
                BinOp::SDiv,
                BinOp::URem,
                BinOp::Shl,
                BinOp::Add,
            ]);
            let result = self.f.bin(op, dst.clone(), lhs, id);
            scope.ints.push((result, dst));
        }
    }

    fn int_cast(&mut self, scope: &mut Scope) {
        let src = self.rng.pick(&self.int_tys()).clone();
        let dst = self.rng.pick(&self.int_tys()).clone();
        let operand = self.int_value(scope, &src);
        let (src_width, dst_width) = (self.width(&src), self.width(&dst));
        let op = if dst_width < src_width {
            CastOp::Trunc
        } else if dst_width == src_width {
            CastOp::Bitcast
        } else if self.rng.chance(50) {
            CastOp::ZExt
        } else {
            CastOp::SExt
        };
        let id = self.f.cast(op, src, dst.clone(), operand);
        scope.ints.push((id, dst));
    }

    fn float_op(&mut self, scope: &mut Scope) {
        let ty = self.rng.pick(&[Ty::F64, Ty::F32]).clone();
        match self.rng.below(4) {
            0 => {
                self.float_value(scope, &ty);
            }
            1 | 2 => {
                let op = *self
                    .rng
                    .pick(&[BinOp::FAdd, BinOp::FSub, BinOp::FMul, BinOp::FDiv]);
                let lhs = self.float_value(scope, &ty);
                let rhs = self.float_value(scope, &ty);
                let id = self.f.bin(op, ty.clone(), lhs, rhs);
                scope.floats.push((id, ty));
            }
            _ => {
                let op = *self.rng.pick(&[UnOp::FNeg, UnOp::FAbs]);
                let operand = self.float_value(scope, &ty);
                let id = self.f.value(Inst::UnOp {
                    op,
                    ty: ty.clone(),
                    operand,
                });
                scope.floats.push((id, ty));
            }
        }
    }

    /// Float -> integer conversions (NaN / out-of-range is UB for the raw
    /// casts), float resizing, and float comparisons.
    fn float_cast(&mut self, scope: &mut Scope) {
        match self.rng.below(10) {
            // An integer converted to a float and straight back (`x as f64 as
            // i32`), across signedness and widths: in range only when every
            // value of the source fits the destination after rounding.
            0 | 1 => {
                let src = self.rng.pick(&self.int_tys()).clone();
                let float = self.rng.pick(&[Ty::F64, Ty::F32]).clone();
                let dst = self.rng.pick(&self.int_tys()).clone();
                let to_float = *self.rng.pick(&[CastOp::SIToFP, CastOp::UIToFP]);
                let back = *self.rng.pick(&[CastOp::FPToSI, CastOp::FPToUI]);
                let int = self.int_value(scope, &src);
                let x = self.f.cast(to_float, src, float.clone(), int);
                scope.floats.push((x, float.clone()));
                let id = self.f.cast(back, float, dst.clone(), x);
                scope.ints.push((id, dst));
            }
            2..=6 => {
                let src = self.rng.pick(&[Ty::F64, Ty::F32]).clone();
                let dst = self.rng.pick(&self.int_tys()).clone();
                let op = *self.rng.pick(&[
                    CastOp::FPToSI,
                    CastOp::FPToUI,
                    CastOp::FPToSI,
                    CastOp::FPToUI,
                    CastOp::FPToSISat,
                    CastOp::FPToUISat,
                ]);
                let operand = self.float_value(scope, &src);
                let id = self.f.cast(op, src, dst.clone(), operand);
                scope.ints.push((id, dst));
            }
            7 => {
                let operand = self.float_value(scope, &Ty::F32);
                let id = self.f.cast(CastOp::FPExt, Ty::F32, Ty::F64, operand);
                scope.floats.push((id, Ty::F64));
            }
            8 => {
                let operand = self.float_value(scope, &Ty::F64);
                let id = self.f.cast(CastOp::FPTrunc, Ty::F64, Ty::F32, operand);
                scope.floats.push((id, Ty::F32));
            }
            _ => {
                self.bool_value(scope);
            }
        }
    }

    fn lanes_value(&mut self, scope: &mut Scope) -> (ValueId, Ty) {
        if !scope.lanes.is_empty() && self.rng.chance(60) {
            return self.rng.pick(&scope.lanes).clone();
        }
        let ty = if self.rng.chance(60) {
            self.world.vector_ty.clone()
        } else {
            self.world.array_ty.clone()
        };
        let id = if !matches!(ty, Ty::Vector(..)) && self.rng.chance(30) {
            // trust-ir v50: the register spelling of a uniform array.
            let lane = self.int_value(scope, &Ty::I32);
            self.f.value(Inst::ArraySplat {
                ty: ty.clone(),
                value: lane,
            })
        } else {
            let lanes = (0..4)
                .map(|_| Constant::Int(i128::from(self.rng.below(3))))
                .collect::<Vec<_>>();
            let value = if matches!(ty, Ty::Vector(..)) {
                Constant::Vector(lanes)
            } else {
                // The one canonical spelling (§3.1): equal lanes are a splat.
                Constant::array(lanes)
            };
            self.f.value(Inst::Const {
                ty: ty.clone(),
                value,
            })
        };
        scope.lanes.push((id, ty.clone()));
        (id, ty)
    }

    /// `ExtractElement` / `InsertElement` with an index that is often out of
    /// range or negative, and lane-wise vector arithmetic.
    fn element(&mut self, scope: &mut Scope) {
        let (array, ty) = self.lanes_value(scope);
        let index_ty = self.rng.pick(&self.index_tys()).clone();
        let index = if self.rng.chance(50) {
            let value = *self.rng.pick(&[0, 1, 3, 4, 5, 100, -1]);
            let value = if index_ty.is_signed() || value >= 0 {
                value
            } else {
                3
            };
            self.f.int(index_ty.clone(), value)
        } else {
            self.int_value(scope, &index_ty)
        };
        match self.rng.below(5) {
            0..=2 => {
                let id = self.f.value(Inst::ExtractElement {
                    ty: Ty::I32,
                    array,
                    index,
                });
                scope.ints.push((id, Ty::I32));
            }
            3 => {
                let value = self.int_value(scope, &Ty::I32);
                let id = self.f.value(Inst::InsertElement {
                    ty: ty.clone(),
                    array,
                    index,
                    value,
                });
                scope.lanes.push((id, ty));
            }
            _ if matches!(ty, Ty::Vector(..)) => {
                let (other, other_ty) = self.lanes_value(scope);
                if other_ty != ty {
                    return;
                }
                let op =
                    *self
                        .rng
                        .pick(&[BinOp::Add, BinOp::And, BinOp::UDiv, BinOp::Shl, BinOp::SRem]);
                let id = self.f.bin(op, ty.clone(), array, other);
                scope.lanes.push((id, ty));
            }
            _ => {}
        }
    }

    fn enum_value(&mut self, scope: &mut Scope) -> ValueId {
        if !scope.enums.is_empty() && self.rng.chance(50) {
            return *self.rng.pick(&scope.enums);
        }
        let variant = self.rng.below(3) as u32;
        let id = if self.rng.chance(50) {
            let mut elems = vec![Constant::Int(i128::from(variant))];
            elems.extend(enum_lanes(variant).iter().map(|_| Constant::Int(1)));
            self.f.value(Inst::Const {
                ty: self.world.enum_ty.clone(),
                value: Constant::Aggregate(elems),
            })
        } else {
            let fields = enum_lanes(variant)
                .iter()
                .map(|ty| self.int_value(scope, ty))
                .collect();
            self.f.value(Inst::MakeAggregate {
                ty: self.world.enum_ty.clone(),
                variant: Some(variant),
                fields,
            })
        };
        scope.enums.push(id);
        id
    }

    /// `ExtractField` / `InsertField` of an enum lane: lane 0 is the tag;
    /// a payload lane is UB unless the ACTIVE variant has a field there of
    /// that type; rewriting the tag is always UB.
    fn enum_field(&mut self, scope: &mut Scope) {
        let aggregate = self.enum_value(scope);
        let (field, ty) = self
            .rng
            .pick(&[
                (0, self.world.enum_tag_ty.clone()),
                (1, Ty::I32),
                (1, Ty::I64),
                (2, Ty::U8),
            ])
            .clone();
        if self.rng.chance(70) {
            let id = self.f.value(Inst::ExtractField {
                ty: ty.clone(),
                aggregate,
                field,
            });
            if ty.is_integer() {
                scope.ints.push((id, ty));
            }
        } else {
            let value = self.int_value(scope, &ty);
            let id = self.f.value(Inst::InsertField {
                ty: self.world.enum_ty.clone(),
                aggregate,
                field,
                value,
            });
            scope.enums.push(id);
        }
    }

    fn tuple_field(&mut self, scope: &mut Scope) {
        let tuple = if !scope.tuples.is_empty() && self.rng.chance(50) {
            *self.rng.pick(&scope.tuples)
        } else if self.rng.chance(50) {
            let a = self.int_value(scope, &Ty::I32);
            let b = self.int_value(scope, &Ty::I64);
            self.f.value(Inst::MakeAggregate {
                ty: self.world.tuple_ty.clone(),
                variant: None,
                fields: vec![a, b],
            })
        } else {
            self.f.value(Inst::Const {
                ty: self.world.tuple_ty.clone(),
                value: Constant::Aggregate(vec![Constant::Int(3), Constant::Int(0)]),
            })
        };
        scope.tuples.push(tuple);
        let (field, ty) = self
            .rng
            .pick(&[(0, Ty::I32), (1, Ty::I64), (0, Ty::I32), (2, Ty::I32)])
            .clone();
        if self.rng.chance(70) {
            let id = self.f.value(Inst::ExtractField {
                ty: ty.clone(),
                aggregate: tuple,
                field,
            });
            scope.ints.push((id, ty));
        } else {
            let value = self.int_value(scope, &ty);
            let id = self.f.value(Inst::InsertField {
                ty: self.world.tuple_ty.clone(),
                aggregate: tuple,
                field,
                value,
            });
            scope.tuples.push(id);
        }
    }

    fn borrow(&mut self, scope: &mut Scope) {
        let ptr = self.ptr_value(scope);
        let inst = if self.rng.chance(50) {
            Inst::Borrow { ptr: ptr.id }
        } else {
            Inst::BorrowMut { ptr: ptr.id }
        };
        let id = self.f.value(inst);
        scope.ptrs.push(PtrVal {
            id,
            exact: ptr.exact,
        });
        if self.rng.chance(30) {
            self.f.effect(Inst::EndBorrow { borrow_ptr: id });
        }
    }

    fn call(&mut self, scope: &mut Scope) {
        let external = self.world.external.is_some() && self.rng.chance(15);
        let target = if external {
            self.world.external.clone()
        } else {
            self.world.callee.clone()
        };
        let Some((callee, params)) = target.filter(|_| self.may_call) else {
            self.int_binop(scope);
            return;
        };
        let args = params
            .iter()
            .map(|ty| match ty {
                Ty::Ptr => self.ptr_value(scope).id,
                ty => self.int_value(scope, ty),
            })
            .collect::<Vec<_>>();
        if external {
            self.f.call(callee, &args);
        } else {
            let id = self.f.value(Inst::Call { callee, args });
            scope.ints.push((id, Ty::I64));
        }
    }

    fn atomic(&mut self, scope: &mut Scope) {
        let ordering = *self
            .rng
            .pick(&[Ordering::SeqCst, Ordering::Relaxed, Ordering::AcqRel]);
        let ty = self.rng.pick(&[Ty::U32, Ty::I64, Ty::U8]).clone();
        match self.rng.below(5) {
            0 => {
                let ptr = self.ptr_value(scope);
                let id = self.f.value(Inst::AtomicLoad {
                    ty: ty.clone(),
                    ptr: ptr.id,
                    ordering: Ordering::SeqCst,
                });
                scope.ints.push((id, ty));
            }
            1 => {
                let ptr = self.ptr_value(scope);
                let value = self.int_value(scope, &ty);
                self.f.effect(Inst::AtomicStore {
                    ty,
                    ptr: ptr.id,
                    value,
                    ordering: Ordering::SeqCst,
                });
            }
            2 => {
                let ptr = self.ptr_value(scope);
                let value = self.int_value(scope, &ty);
                let op = *self.rng.pick(&[
                    AtomicRMWOp::Add,
                    AtomicRMWOp::Xchg,
                    AtomicRMWOp::And,
                    AtomicRMWOp::UMax,
                ]);
                let id = self.f.value(Inst::AtomicRMW {
                    op,
                    ty: ty.clone(),
                    ptr: ptr.id,
                    value,
                    ordering,
                });
                scope.ints.push((id, ty));
            }
            3 => {
                let ptr = self.ptr_value(scope);
                let expected = self.int_value(scope, &ty);
                let desired = self.int_value(scope, &ty);
                let (value, flag) = self.f.values2(Inst::CmpXchg {
                    ty: ty.clone(),
                    ptr: ptr.id,
                    expected,
                    desired,
                    success: Ordering::SeqCst,
                    failure: Ordering::SeqCst,
                    weak: false,
                });
                scope.ints.push((value, ty));
                scope.bools.push(flag);
            }
            _ => self.f.effect(Inst::Fence { ordering }),
        }
    }

    fn global(&mut self, scope: &mut Scope) {
        let Some(global) = self.world.global else {
            self.load(scope);
            return;
        };
        let id = self.f.value(Inst::GlobalAddr { global });
        scope.ptrs.push(PtrVal { id, exact: false });
    }

    fn unop_or_overflow(&mut self, scope: &mut Scope) {
        let ty = self.rng.pick(&self.int_tys()).clone();
        if self.rng.chance(40) {
            let op = *self.rng.pick(&[
                OverflowOp::AddOverflow,
                OverflowOp::SubOverflow,
                OverflowOp::MulOverflow,
            ]);
            let lhs = self.int_value(scope, &ty);
            let rhs = self.int_value(scope, &ty);
            let (value, flag) = self.f.values2(Inst::Overflow {
                op,
                ty: ty.clone(),
                lhs,
                rhs,
            });
            scope.ints.push((value, ty));
            scope.bools.push(flag);
            return;
        }
        let op = *self
            .rng
            .pick(&[UnOp::Neg, UnOp::Not, UnOp::CtPop, UnOp::CtLz, UnOp::CtTz]);
        let operand = self.int_value(scope, &ty);
        let id = self.f.value(Inst::UnOp {
            op,
            ty: ty.clone(),
            operand,
        });
        scope.ints.push((id, ty));
    }

    /// Fat pointers (a pinned target only: the metadata is a `Usize`):
    /// `PtrFromParts` of a data pointer and a length, `PtrData` back to a
    /// thin pointer (then used for accesses), `PtrMetadata`.
    fn fat_pointer(&mut self, scope: &mut Scope) {
        if self.world.pointer_bits.is_none() {
            let ptr = self.ptr_value(scope);
            let id = self.f.value(Inst::PtrData {
                ptr_ty: Ty::Ptr,
                ptr: ptr.id,
            });
            scope.ptrs.push(PtrVal { id, exact: false });
            return;
        }
        let data = self.ptr_value(scope);
        let len = self.int_value(scope, &Ty::Usize);
        let fat_ty = Ty::FatPtr(FatPtrKind::Str);
        let fat = self.f.value(Inst::PtrFromParts {
            ptr_ty: fat_ty.clone(),
            metadata_ty: Ty::Usize,
            data: data.id,
            metadata: len,
        });
        if self.rng.chance(60) {
            let id = self.f.value(Inst::PtrData {
                ptr_ty: fat_ty,
                ptr: fat,
            });
            scope.ptrs.push(PtrVal { id, exact: false });
        } else {
            let id = self.f.value(Inst::PtrMetadata {
                ptr_ty: fat_ty,
                metadata_ty: Ty::Usize,
                ptr: fat,
            });
            scope.ints.push((id, Ty::Usize));
        }
    }

    fn sequence(&mut self, _scope: &mut Scope) {
        if self.rng.chance(50) {
            let seq = self.f.value(Inst::Const {
                ty: self.world.seq_ty.clone(),
                value: Constant::Sequence(vec![Constant::Int(1), Constant::Int(2)]),
            });
            self.f.value(Inst::SeqMapAddK {
                ty: self.world.seq_ty.clone(),
                seq,
                k: 1,
            });
        } else {
            let seq = self.f.value(Inst::Const {
                ty: self.world.bool_seq_ty.clone(),
                value: Constant::Sequence(vec![Constant::Bool(true)]),
            });
            self.f.value(Inst::SeqMapNot {
                ty: self.world.bool_seq_ty.clone(),
                seq,
            });
        }
    }

    /// Layout-sensitive shapes: every size, offset, stride and alignment
    /// below is the interpreter's, which fsym must use exactly — aggregates
    /// stored whole and read back byte-wise (their padding and an inactive
    /// variant's tail are written UNINITIALIZED), declared-layout structs and
    /// their GEP strides, `<4 x bool>` (a byte a lane), huge natural
    /// alignment (allocations and a global), a GEP chain whose second index
    /// is a wide constant (a 32-bit address space, and the local solver's
    /// candidate for it), and annotated accesses through any pointer.
    /// A 32-bit end-of-space probe, placed FIRST in `f` so the end-of-space
    /// harness (`Placements::EndOfSpace`) makes its allocation end exactly
    /// at 2^32: `p = alloca u8 x size` (alignment 1), then a pointer at or
    /// across its end — a GEP to the end, from the last byte by one, the end
    /// then moved by zero or exposed — or its last byte exposed (defined).
    /// Returns `size`.
    fn end_probe(&mut self, scope: &mut Scope) -> u64 {
        let size = *self.rng.pick(&[1u64, 16, 4095]);
        let count = self.f.int(Ty::Usize, i128::from(size));
        let p = self.f.alloca(Ty::U8, Some(count), None);
        scope.ptrs.push(PtrVal { id: p, exact: true });
        let at = |gn: &mut Self, base: ValueId, offset: u64| {
            let index = gn.f.int(Ty::I64, i128::from(offset));
            gn.f.gep(Ty::U8, base, index)
        };
        match self.rng.below(5) {
            0 => {
                at(self, p, size);
            }
            1 => {
                let last = at(self, p, size - 1);
                at(self, last, 1);
            }
            2 => {
                let end = at(self, p, size);
                at(self, end, 0);
            }
            3 => {
                let end = at(self, p, size);
                self.f.cast(CastOp::PtrToInt, Ty::Ptr, Ty::Usize, end);
            }
            _ => {
                let last = at(self, p, size - 1);
                self.f.cast(CastOp::PtrToInt, Ty::Ptr, Ty::Usize, last);
            }
        }
        size
    }

    fn layout_probe(&mut self, scope: &mut Scope) {
        match self.rng.below(15) {
            0..=2 => self.aggregate_store(scope),
            3..=5 => self.declared_struct(scope),
            6 | 7 => self.bool_vector(scope),
            8 => self.huge_alignment(scope),
            9 | 10 => self.gep_chain(scope),
            11 => self.annotated_access(scope),
            _ => self.init_mask(scope),
        }
    }

    /// An `E` of `variant`, built by `MakeAggregate` (the scanner tracks its
    /// variant) or a constant.
    fn enum_of_variant(&mut self, scope: &mut Scope, variant: u32) -> ValueId {
        if self.rng.chance(50) {
            let mut elems = vec![Constant::Int(i128::from(variant))];
            elems.extend(enum_lanes(variant).iter().map(|_| Constant::Int(3)));
            return self.f.value(Inst::Const {
                ty: self.world.enum_ty.clone(),
                value: Constant::Aggregate(elems),
            });
        }
        let fields = enum_lanes(variant)
            .iter()
            .map(|ty| self.int_value(scope, ty))
            .collect();
        self.f.value(Inst::MakeAggregate {
            ty: self.world.enum_ty.clone(),
            variant: Some(variant),
            fields,
        })
    }

    /// Initialization masks where a store or a load is not byte-exact
    /// (`E = { A, B(i32), C(i64, u8) }`: tag at 0, `B`'s field at 8..12,
    /// `C`'s at 8..16 and 16): an enum stored with its variant UNTRACKED (a
    /// select on an input between two variants) writes its tag and the
    /// ACTIVE variant's fields only, over a filled slot; an aggregate with
    /// padding stored at an offset fsym cannot decide writes that padding
    /// UNINITIALIZED wherever it lands; a whole-enum load needs the fields of
    /// the variant the tag in memory names, whatever wrote the tag. And
    /// where the bytes a copy moves, a load reads or a fill writes are not
    /// decided: a copy from a source whose initialization fsym does not
    /// track (8192 bytes) or from an offset it cannot decide moves possibly
    /// uninitialized bytes; a load at an undecided offset of a partly filled
    /// buffer; a fill whose count is a select writes only its smaller count
    /// for sure.
    fn init_mask(&mut self, scope: &mut Scope) {
        let x = match scope.int_of(self.rng, &Ty::U8) {
            Some(x) => x,
            None => self.fresh_int(scope, &Ty::U8),
        };
        let bound = self.f.int(Ty::U8, *self.rng.pick(&[1, 2, 128]));
        let cond = self.f.icmp(ICmpOp::Ult, Ty::U8, x, bound);
        let e = self.world.enum_ty.clone();
        let size_ty = self.size_ty();
        let fill_slot = |gn: &mut Self, slot: ValueId, bytes: i128| {
            let fill = gn.f.int(Ty::U8, *gn.rng.pick(&[0, 7]));
            let size_ty = gn.size_ty();
            let bytes = gn.f.int(size_ty, bytes);
            gn.f.memset(slot, fill, bytes);
        };
        match self.rng.below(7) {
            0 => {
                let slot = if self.rng.chance(50) {
                    self.f.alloca(e.clone(), None, None)
                } else {
                    let count = self.f.int(size_ty, 32);
                    self.f.alloca(Ty::U8, Some(count), Some(8))
                };
                scope.ptrs.push(PtrVal {
                    id: slot,
                    exact: true,
                });
                if self.rng.chance(80) {
                    fill_slot(self, slot, 24);
                }
                let first = self.rng.below(3) as u32;
                let second = (first + 1 + self.rng.below(2) as u32) % 3;
                let a = self.enum_of_variant(scope, first);
                let b = self.enum_of_variant(scope, second);
                let value = self.f.select(e.clone(), cond, a, b);
                scope.enums.push(value);
                self.f.store(e, slot, value);
                let offset = self.f.int(Ty::I64, *self.rng.pick(&[1, 8, 12, 16, 20]));
                let at = self.f.gep(Ty::U8, slot, offset);
                let read_ty = self.rng.pick(&[Ty::U8, Ty::U32]).clone();
                self.inspected_load(scope, read_ty, at, Some(1));
            }
            1 => {
                let count = self.f.int(size_ty, 32);
                let buf = self.f.alloca(Ty::U8, Some(count), Some(16));
                scope.ptrs.push(PtrVal {
                    id: buf,
                    exact: true,
                });
                fill_slot(self, buf, 32);
                let (ty, value) = match self.rng.below(3) {
                    0 => (
                        pad_ty(),
                        self.f.value(Inst::Const {
                            ty: pad_ty(),
                            value: Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2)]),
                        }),
                    ),
                    1 => {
                        let a = self.int_value(scope, &Ty::I32);
                        let b = self.int_value(scope, &Ty::I64);
                        let value = self.f.value(Inst::MakeAggregate {
                            ty: self.world.tuple_ty.clone(),
                            variant: None,
                            fields: vec![a, b],
                        });
                        (self.world.tuple_ty.clone(), value)
                    }
                    _ => {
                        let variant = 1 + self.rng.below(2) as u32;
                        (e.clone(), self.enum_of_variant(scope, variant))
                    }
                };
                let low = self.f.int(Ty::I64, 0);
                let high = self.f.int(Ty::I64, *self.rng.pick(&[8, 16]));
                let offset = self.f.select(Ty::I64, cond, low, high);
                let at = self.f.gep(Ty::U8, buf, offset);
                self.f.store(ty, at, value);
                let read = self.f.int(Ty::I64, *self.rng.pick(&[1, 4, 9, 12, 20, 28]));
                let at = self.f.gep(Ty::U8, buf, read);
                self.inspected_load(scope, Ty::U8, at, Some(1));
            }
            3 => {
                // A copy from a source fsym tracks no initialization of.
                let big = self.f.int(size_ty.clone(), 8192);
                let src = self.f.alloca(Ty::U8, Some(big), Some(8));
                let sixteen = self.f.int(size_ty.clone(), 16);
                let dst = self.f.alloca(Ty::U8, Some(sixteen), Some(8));
                if self.rng.chance(60) {
                    fill_slot(self, dst, 16);
                }
                let at = if self.rng.chance(50) {
                    dst
                } else {
                    let eight = self.f.int(Ty::I64, 8);
                    self.f.gep(Ty::U8, dst, eight)
                };
                let bytes = self.f.int(size_ty, *self.rng.pick(&[4, 8]));
                self.f.effect(Inst::MemCopy {
                    dst: at,
                    src,
                    bytes,
                    overlap: false,
                });
                scope.ptrs.push(PtrVal {
                    id: dst,
                    exact: true,
                });
                let read = self.f.int(Ty::I64, *self.rng.pick(&[0, 4, 8, 12]));
                let at = self.f.gep(Ty::U8, dst, read);
                self.inspected_load(scope, Ty::U8, at, Some(1));
            }
            4 => {
                // A copy from an offset fsym cannot decide, of a source whose
                // first 8 bytes are filled.
                let sixteen = self.f.int(size_ty.clone(), 16);
                let src = self.f.alloca(Ty::U8, Some(sixteen), Some(8));
                fill_slot(self, src, 8);
                let low = self.f.int(Ty::I64, 0);
                let high = self.f.int(Ty::I64, *self.rng.pick(&[4, 8]));
                let offset = self.f.select(Ty::I64, cond, low, high);
                let from = self.f.gep(Ty::U8, src, offset);
                let eight = self.f.int(size_ty.clone(), 8);
                let dst = self.f.alloca(Ty::U8, Some(eight), Some(8));
                if self.rng.chance(50) {
                    fill_slot(self, dst, 8);
                }
                let bytes = self.f.int(size_ty, *self.rng.pick(&[4, 8]));
                self.f.effect(Inst::MemCopy {
                    dst,
                    src: from,
                    bytes,
                    overlap: false,
                });
                scope.ptrs.push(PtrVal {
                    id: dst,
                    exact: true,
                });
                let read = self.f.int(Ty::I64, *self.rng.pick(&[0, 4, 7]));
                let at = self.f.gep(Ty::U8, dst, read);
                self.inspected_load(scope, Ty::U8, at, Some(1));
            }
            5 => {
                // A load at an offset fsym cannot decide, of a buffer filled
                // in part or whole.
                let sixteen = self.f.int(size_ty.clone(), 16);
                let buf = self.f.alloca(Ty::U8, Some(sixteen), Some(8));
                let filled = *self.rng.pick(&[8, 16]);
                fill_slot(self, buf, filled);
                scope.ptrs.push(PtrVal {
                    id: buf,
                    exact: true,
                });
                let low = self.f.int(Ty::I64, 0);
                let high = self.f.int(Ty::I64, *self.rng.pick(&[4, 8, 12]));
                let offset = self.f.select(Ty::I64, cond, low, high);
                let at = self.f.gep(Ty::U8, buf, offset);
                self.inspected_load(scope, Ty::U8, at, Some(1));
            }
            6 => {
                // A fill whose count is a select: only the smaller count is
                // written for sure. At 64 bits one in four starts at byte 8
                // and may run 2^64 - 7 bytes: its 64-bit end wraps to byte
                // 1, so only its length shows it leaves the object (and it
                // reads nothing back, so nothing else keeps it from clean).
                let sixteen = self.f.int(size_ty.clone(), 16);
                let buf = self.f.alloca(Ty::U8, Some(sixteen), Some(8));
                scope.ptrs.push(PtrVal {
                    id: buf,
                    exact: true,
                });
                let small = self.f.int(size_ty.clone(), *self.rng.pick(&[1, 4, 8]));
                let long = self.world.pointer_bits != Some(32) && self.rng.chance(25);
                let (dst, whole) = if long {
                    let eight = self.f.int(Ty::I64, 8);
                    (
                        self.f.gep(Ty::U8, buf, eight),
                        self.f.int(size_ty.clone(), i128::from(u64::MAX - 6)),
                    )
                } else {
                    (buf, self.f.int(size_ty.clone(), 16))
                };
                let bytes = self.f.select(size_ty, cond, small, whole);
                let fill = self.f.int(Ty::U8, 7);
                self.f.memset(dst, fill, bytes);
                if !long {
                    let read = self.f.int(Ty::I64, *self.rng.pick(&[0, 2, 8, 15]));
                    let at = self.f.gep(Ty::U8, buf, read);
                    self.inspected_load(scope, Ty::U8, at, Some(1));
                }
            }
            _ => {
                let slot = if self.rng.chance(50) {
                    self.f.alloca(e.clone(), None, None)
                } else {
                    let count = self.f.int(size_ty, 24);
                    self.f.alloca(Ty::U8, Some(count), Some(8))
                };
                scope.ptrs.push(PtrVal {
                    id: slot,
                    exact: true,
                });
                let tag = i128::from(self.rng.below(3));
                match self.rng.below(3) {
                    // The tag alone.
                    0 => {
                        let tag = self.f.int(self.world.enum_tag_ty.clone(), tag);
                        self.f.store(self.world.enum_tag_ty.clone(), slot, tag);
                    }
                    // A prefix of the slot filled with the tag's byte.
                    1 => {
                        let fill = self.f.int(Ty::U8, tag);
                        let size_ty = self.size_ty();
                        let bytes = self.f.int(size_ty, *self.rng.pick(&[1, 8, 12, 16, 17, 24]));
                        self.f.memset(slot, fill, bytes);
                    }
                    // A whole variant stored, then its tag rewritten.
                    _ => {
                        if self.rng.chance(50) {
                            fill_slot(self, slot, 24);
                        }
                        let variant = self.rng.below(3) as u32;
                        let value = self.enum_of_variant(scope, variant);
                        self.f.store(e.clone(), slot, value);
                        let tag = self.f.int(self.world.enum_tag_ty.clone(), tag);
                        self.f.store(self.world.enum_tag_ty.clone(), slot, tag);
                    }
                }
                let value = self.f.load(e, slot, None);
                scope.enums.push(value);
            }
        }
    }

    /// Read `ty` at `at` and inspect it at once (a poison value is UB only
    /// when inspected).
    fn inspected_load(&mut self, scope: &mut Scope, ty: Ty, at: ValueId, align: Option<u64>) {
        let x = self.f.load(ty.clone(), at, align);
        let y = self.f.bin(BinOp::Or, ty.clone(), x, x);
        scope.ints.push((y, ty));
    }

    fn aggregate_store(&mut self, scope: &mut Scope) {
        let (ty, value) = match self.rng.below(3) {
            0 => {
                let value = if self.rng.chance(50) {
                    let a = self.int_value(scope, &Ty::U8);
                    let b = self.int_value(scope, &Ty::U64);
                    self.f.value(Inst::MakeAggregate {
                        ty: pad_ty(),
                        variant: None,
                        fields: vec![a, b],
                    })
                } else {
                    self.f.value(Inst::Const {
                        ty: pad_ty(),
                        value: Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2)]),
                    })
                };
                (pad_ty(), value)
            }
            1 => {
                let a = self.int_value(scope, &Ty::I32);
                let b = self.int_value(scope, &Ty::I64);
                let value = self.f.value(Inst::MakeAggregate {
                    ty: self.world.tuple_ty.clone(),
                    variant: None,
                    fields: vec![a, b],
                });
                scope.tuples.push(value);
                (self.world.tuple_ty.clone(), value)
            }
            _ => (self.world.enum_ty.clone(), self.enum_value(scope)),
        };
        // The slot: one of the aggregate, or a byte buffer, sometimes filled
        // first (the whole store then UN-initializes its padding).
        let slot = if self.rng.chance(60) {
            let align = self.rng.chance(40).then_some(16);
            self.f.alloca(ty.clone(), None, align)
        } else {
            let size_ty = self.size_ty();
            let count = self.f.int(size_ty, 32);
            self.f.alloca(Ty::U8, Some(count), Some(16))
        };
        scope.ptrs.push(PtrVal {
            id: slot,
            exact: true,
        });
        if self.rng.chance(50) {
            let fill = self.f.int(Ty::U8, 7);
            let size_ty = self.size_ty();
            let bytes = self.f.int(size_ty, 16);
            self.f.memset(slot, fill, bytes);
        }
        self.f.store(ty.clone(), slot, value);
        if self.rng.chance(30) {
            // Read back whole: only the live fields must be initialized.
            let id = self.f.load(ty.clone(), slot, None);
            match ty {
                Ty::Tuple(_) => scope.tuples.push(id),
                Ty::Enum(_) => scope.enums.push(id),
                _ => {}
            }
            return;
        }
        // Read back byte-wise, often across padding or an inactive tail.
        let offset = self.f.int(Ty::I64, *self.rng.pick(&[0, 1, 4, 8, 12, 16]));
        let at = self.f.gep(Ty::U8, slot, offset);
        let read_ty = self.rng.pick(&[Ty::U8, Ty::U32, Ty::I64]).clone();
        self.inspected_load(scope, read_ty, at, Some(1));
    }

    fn declared_struct(&mut self, scope: &mut Scope) {
        let size_ty = self.size_ty();
        match self.rng.below(4) {
            // A whole `Declared` (16 bytes, its byte at offset 8) read from a
            // byte buffer that may be shorter.
            0 => {
                let n = *self.rng.pick(&[1, 8, 9, 15, 16, 32]);
                let count = self.f.int(size_ty, n);
                let buf = self.f.alloca(Ty::U8, Some(count), Some(8));
                let fill = self.f.int(Ty::U8, 1);
                self.f.memset(buf, fill, count);
                scope.ptrs.push(PtrVal {
                    id: buf,
                    exact: true,
                });
                self.f.load(declared_ty(), buf, None);
            }
            // The GEP stride of a declared-layout (or padded) struct, then a
            // store into a small buffer.
            1 => {
                let n = *self.rng.pick(&[4, 16, 32, 64]);
                let count = self.f.int(size_ty, n);
                let buf = self.f.alloca(Ty::U8, Some(count), Some(8));
                let stride = self.rng.pick(&[declared_ty(), big_ty(), pad_ty()]).clone();
                let index = self.f.int(Ty::I64, *self.rng.pick(&[0, 1, 2, 4]));
                let at = self.f.gep(stride, buf, index);
                scope.ptrs.push(PtrVal {
                    id: at,
                    exact: true,
                });
                let byte = self.f.int(Ty::U8, 1);
                self.f.store(Ty::U8, at, byte);
            }
            // `Declared` allocated by a count whose byte size may overflow.
            2 => {
                let count = *self.rng.pick(&[1i128, 2, 1 << 59, (1 << 60) + 1, 1 << 62]);
                let count = self.f.int(Ty::U64, count);
                let a = if self.rng.chance(50) {
                    self.f.alloca(declared_ty(), Some(count), None)
                } else {
                    self.f.heap(declared_ty(), Some(count))
                };
                scope.ptrs.push(PtrVal { id: a, exact: true });
            }
            // A `Declared` stored whole, then one byte read: only offset 8
            // is written.
            _ => {
                let slot = self.f.alloca(declared_ty(), None, None);
                let x = self.int_value(scope, &Ty::U8);
                let value = self.f.value(Inst::MakeAggregate {
                    ty: declared_ty(),
                    variant: None,
                    fields: vec![x],
                });
                self.f.store(declared_ty(), slot, value);
                scope.ptrs.push(PtrVal {
                    id: slot,
                    exact: true,
                });
                let offset = self.f.int(Ty::I64, *self.rng.pick(&[0, 7, 8, 15]));
                let at = self.f.gep(Ty::U8, slot, offset);
                self.inspected_load(scope, Ty::U8, at, None);
            }
        }
    }

    fn bool_vector(&mut self, scope: &mut Scope) {
        let ty = bool_vector_ty();
        let lanes = (0..4).map(|lane| Constant::Bool(lane % 2 == 0)).collect();
        let value = self.f.value(Inst::Const {
            ty: ty.clone(),
            value: Constant::Vector(lanes),
        });
        let size_ty = self.size_ty();
        let slot = match self.rng.below(3) {
            0 => {
                let count = self.f.int(size_ty, *self.rng.pick(&[1, 2]));
                self.f.alloca(ty.clone(), Some(count), None)
            }
            1 => self.f.alloca(ty.clone(), None, None),
            _ => {
                let count = self.f.int(size_ty, *self.rng.pick(&[4, 8, 16]));
                self.f.alloca(Ty::U8, Some(count), None)
            }
        };
        scope.ptrs.push(PtrVal {
            id: slot,
            exact: true,
        });
        self.f.store(ty.clone(), slot, value);
        match self.rng.below(3) {
            0 => {
                let offset = self.f.int(Ty::I64, *self.rng.pick(&[3, 4, 8, 15]));
                let at = self.f.gep(Ty::U8, slot, offset);
                let byte = self.f.int(Ty::U8, 1);
                self.f.store(Ty::U8, at, byte);
            }
            1 => {
                let one = self.f.int(Ty::I64, 1);
                let at = self.f.gep(ty, slot, one);
                self.inspected_load(scope, Ty::U8, at, None);
            }
            _ => {
                self.f.load(ty, slot, None);
            }
        }
    }

    /// Allocations (and a global) of a type whose NATURAL alignment is 2^63:
    /// the second one overflows the interpreter's base address.
    fn huge_alignment(&mut self, scope: &mut Scope) {
        for _ in 0..=self.rng.below(2) {
            let (id, exact) = match self.rng.below(3) {
                0 => (self.f.alloca(huge_ty(), None, None), true),
                1 => (self.f.heap(huge_ty(), None), true),
                // One of two globals of it (each placed on its first use).
                _ => match self.world.huge_global {
                    Some(global) => {
                        let global = GlobalId::new(global.index() + self.rng.below(2) as u32);
                        (self.f.value(Inst::GlobalAddr { global }), false)
                    }
                    None => (self.f.alloca(huge_ty(), None, None), true),
                },
            };
            scope.ptrs.push(PtrVal { id, exact });
        }
    }

    /// `q = gep i64, base, x; r = gep u8, q, WIDE`: on a 32-bit target the
    /// result may leave the address space whatever the (small, often
    /// symbolic) `x` — the verdict, and any solver candidate for it, must
    /// say so.
    fn gep_chain(&mut self, scope: &mut Scope) {
        let base = if self.rng.chance(60) {
            let size_ty = self.size_ty();
            let count = self.f.int(size_ty, 16);
            let a = self.f.alloca(Ty::U64, Some(count), Some(16));
            scope.ptrs.push(PtrVal { id: a, exact: true });
            a
        } else {
            self.ptr_value(scope).id
        };
        let small = self.int_value(scope, &Ty::U8);
        let q = self.f.gep(Ty::I64, base, small);
        let (wide_ty, wide) = match self.world.pointer_bits {
            Some(32) if self.rng.chance(60) => (
                Ty::Usize,
                *self
                    .rng
                    .pick(&[0xFFFF_FFFFi128, 0x7FFF_FFFF, 0xFFFF_FF00, 0x100]),
            ),
            _ => (
                Ty::U64,
                *self
                    .rng
                    .pick(&[0xFFFF_FFFFi128, 0x7FFF_FFFF, 0x1_0000_0000, 0x100]),
            ),
        };
        let wide = self.f.int(wide_ty, wide);
        let r = self.f.gep(Ty::U8, q, wide);
        scope.ptrs.push(PtrVal {
            id: r,
            exact: false,
        });
    }

    /// An access annotated `NotNull` / `InBounds` through ANY pointer in
    /// scope — a parameter (the harness hands null, a freed block, an
    /// address naming no allocation), a loaded pointer, a GEP result.
    fn annotated_access(&mut self, scope: &mut Scope) {
        let ptr = self.ptr_value(scope);
        let proofs = vec![ProofAnnotation::NotNull, ProofAnnotation::InBounds];
        if self.rng.chance(50) {
            let byte = self.int_value(scope, &Ty::U8);
            self.f.effect_with(
                Inst::Store {
                    ty: Ty::U8,
                    ptr: ptr.id,
                    value: byte,
                    volatile: false,
                    align: None,
                },
                proofs,
            );
        } else {
            let x = self.f.value_with(
                Inst::Load {
                    ty: Ty::U8,
                    ptr: ptr.id,
                    volatile: false,
                    align: None,
                },
                proofs,
            );
            let y = self.f.bin(BinOp::Or, Ty::U8, x, x);
            scope.ints.push((y, Ty::U8));
        }
    }

    fn instruction(&mut self, scope: &mut Scope) {
        match self.rng.below(110) {
            0..=2 => {
                let ty = self.rng.pick(&self.int_tys()).clone();
                self.fresh_int(scope, &ty);
            }
            3..=6 => {
                self.alloca(scope);
            }
            7 | 8 => {
                let ty = self.rng.pick(&access_tys()).clone();
                let count = self.count(scope);
                let id = self.f.heap(ty, count);
                scope.ptrs.push(PtrVal { id, exact: true });
            }
            9 => {
                let id = if self.rng.chance(50) {
                    self.f.null()
                } else {
                    self.f.const_ptr(0)
                };
                scope.ptrs.push(PtrVal { id, exact: true });
            }
            10..=13 => self.gep(scope),
            14..=18 => self.load(scope),
            19..=23 => self.store(scope),
            24..=28 => self.int_binop(scope),
            29 => {
                self.bool_value(scope);
            }
            30 | 31 => {
                let ptr = self.ptr_value(scope);
                let ty = self.rng.pick(&[Ty::U64, Ty::I64]).clone();
                let id = self.f.cast(CastOp::PtrToInt, Ty::Ptr, ty.clone(), ptr.id);
                scope.ints.push((id, ty));
            }
            32 => {
                let ty = self.rng.pick(&[Ty::U64, Ty::I64]).clone();
                let (int, exact) = if self.rng.chance(50) {
                    (self.fresh_int(scope, &ty), true)
                } else {
                    (self.int_value(scope, &ty), false)
                };
                let id = self.f.cast(CastOp::IntToPtr, ty, Ty::Ptr, int);
                scope.ptrs.push(PtrVal { id, exact });
            }
            33 => self.int_cast(scope),
            34 => {
                let cond = self.bool_value(scope);
                match self.rng.below(3) {
                    0 => {
                        let then_val = self.ptr_value(scope).id;
                        let else_val = self.ptr_value(scope).id;
                        let id = self.f.select(Ty::Ptr, cond, then_val, else_val);
                        scope.ptrs.push(PtrVal { id, exact: false });
                    }
                    1 => {
                        let ty = self.rng.pick(&[Ty::F64, Ty::F32]).clone();
                        let then_val = self.float_value(scope, &ty);
                        let else_val = self.float_value(scope, &ty);
                        let id = self.f.select(ty.clone(), cond, then_val, else_val);
                        scope.floats.push((id, ty));
                    }
                    _ => {
                        let ty = self.rng.pick(&self.int_tys()).clone();
                        let then_val = self.int_value(scope, &ty);
                        let else_val = self.int_value(scope, &ty);
                        let id = self.f.select(ty.clone(), cond, then_val, else_val);
                        scope.ints.push((id, ty));
                    }
                }
            }
            35 => {
                let dst = self.ptr_value(scope).id;
                let fill = self.int_value(scope, &Ty::U8);
                let size_ty = self.size_ty();
                let bytes = self.int_value(scope, &size_ty);
                self.f.memset(dst, fill, bytes);
            }
            36 => {
                let dst = self.ptr_value(scope).id;
                let src = self.ptr_value(scope).id;
                let size_ty = self.size_ty();
                let bytes = self.int_value(scope, &size_ty);
                let overlap = self.rng.chance(50);
                self.f.effect(Inst::MemCopy {
                    dst,
                    src,
                    bytes,
                    overlap,
                });
            }
            // Address arithmetic: an integer derived from a pointer's
            // address, often used at once as a divisor or shift amount. The
            // model must not take an abstract address for a value.
            37 | 38 => {
                let ptr = self.ptr_value(scope).id;
                let address = self.f.ptrtoint(ptr);
                let derived = match self.rng.below(4) {
                    0 => {
                        let mask = *self.rng.pick(&[1, 3, 7, 15, 31]);
                        let mask = self.f.int(Ty::U64, mask);
                        self.f.bin(BinOp::And, Ty::U64, address, mask)
                    }
                    1 => {
                        let pointee = self.rng.pick(&[Ty::U8, Ty::U32, Ty::I64]).clone();
                        let steps = self.f.int(Ty::I64, i128::from(self.rng.below(4)));
                        let moved = self.f.gep(pointee, ptr, steps);
                        let moved = self.f.ptrtoint(moved);
                        self.f.bin(BinOp::Sub, Ty::U64, moved, address)
                    }
                    2 => {
                        let other = self.ptr_value(scope).id;
                        let other = self.f.ptrtoint(other);
                        self.f.bin(BinOp::Sub, Ty::U64, other, address)
                    }
                    _ => address,
                };
                scope.ints.push((derived, Ty::U64));
                if self.rng.chance(60) {
                    let bias = self.f.int(Ty::U64, i128::from(self.rng.below(3)));
                    let amount = self.f.bin(BinOp::Sub, Ty::U64, derived, bias);
                    let lhs = self.int_value(scope, &Ty::U64);
                    let op = *self
                        .rng
                        .pick(&[BinOp::UDiv, BinOp::URem, BinOp::Shl, BinOp::LShr]);
                    let id = self.f.bin(op, Ty::U64, lhs, amount);
                    scope.ints.push((id, Ty::U64));
                }
            }
            // Address comparison: a condition the model must not decide on
            // abstract addresses.
            39 => {
                let ptr = self.ptr_value(scope).id;
                let other = if self.rng.chance(50) {
                    let pointee = self.rng.pick(&[Ty::U8, Ty::U32, Ty::I64]).clone();
                    let steps = self.f.int(Ty::I64, i128::from(self.rng.below(200)));
                    self.f.gep(pointee, ptr, steps)
                } else {
                    self.ptr_value(scope).id
                };
                let lhs = self.f.ptrtoint(ptr);
                let rhs = self.f.ptrtoint(other);
                let op = *self.rng.pick(&[
                    ICmpOp::Eq,
                    ICmpOp::Ne,
                    ICmpOp::Ult,
                    ICmpOp::Ugt,
                    ICmpOp::Slt,
                    ICmpOp::Sge,
                ]);
                let id = self.f.icmp(op, Ty::U64, lhs, rhs);
                scope.bools.push(id);
            }
            40 | 41 => {
                let ptr = self.ptr_value(scope).id;
                self.f.dealloc(ptr);
            }
            42 => {
                let cond = self.bool_value(scope);
                self.f.effect(Inst::Assume { cond });
            }
            43..=46 => self.bool_cast(scope),
            47..=49 => self.float_op(scope),
            50..=54 => self.float_cast(scope),
            55..=58 => self.element(scope),
            59..=62 => self.enum_field(scope),
            63 | 64 => self.tuple_field(scope),
            65..=67 => self.borrow(scope),
            68..=71 => self.call(scope),
            72..=75 => self.atomic(scope),
            76 => self.global(scope),
            77 | 78 => self.unop_or_overflow(scope),
            79 | 80 => self.fat_pointer(scope),
            81 => {
                let cond = self.bool_value(scope);
                self.f.effect(Inst::Assert {
                    cond,
                    kind: trust_ir::AssertKind::Unspecified,
                    site: None,
                });
            }
            82 => self.sequence(scope),
            83 => {
                let ty = self.rng.pick(&self.int_tys()).clone();
                let operand = self.int_value(scope, &ty);
                let id = self.f.value(Inst::Copy {
                    ty: ty.clone(),
                    operand,
                });
                scope.ints.push((id, ty));
            }
            84..=88 => self.load(scope),
            89..=93 => self.store(scope),
            94..=96 => self.gep(scope),
            100..=109 => self.layout_probe(scope),
            _ => self.int_binop(scope),
        }
    }

    fn straight_line(&mut self, scope: &mut Scope, max: u64) {
        for _ in 0..=self.rng.below(max) {
            self.instruction(scope);
        }
    }

    fn ret(&mut self, scope: &mut Scope) {
        let value = self.int_value(scope, &Ty::I64);
        self.f.ret(&[value]);
    }
}

fn access_tys() -> [Ty; 4] {
    [Ty::U8, Ty::U32, Ty::I64, Ty::U64]
}

fn world_width(world: &World, ty: &Ty) -> u32 {
    match ty {
        Ty::Usize | Ty::Isize => world.pointer_bits.expect("a pinned target"),
        ty => ty.bit_width().expect("fixed-width integer"),
    }
}

/// A value of `bits` width biased toward the boundaries UB conditions live
/// on.
fn interesting_at(rng: &mut Rng, bits: u32, signed: bool) -> i128 {
    let max_unsigned = if bits == 128 {
        i128::MAX
    } else {
        (1i128 << bits) - 1
    };
    let raw = match rng.below(14) {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 4,
        4 => 8,
        5 => 15,
        6 => 16,
        7 => i128::from(bits) - 1,
        8 => i128::from(bits),
        9 => 100,
        10 => max_unsigned,        // -1 when signed
        11 => 1i128 << (bits - 1), // the signed minimum's bit pattern
        12 => 3,
        _ => i128::from(rng.below(64)),
    };
    let raw = raw & max_unsigned;
    if signed && raw >= (1i128 << (bits - 1)) {
        raw - (1i128 << bits)
    } else {
        raw
    }
}

/// The parameters of the function under test: integers first, then
/// pointers, then at most one enum and one vector.
#[derive(Clone)]
struct Params {
    ints: Vec<Ty>,
    ptrs: usize,
    enum_param: bool,
    vector_param: bool,
}

impl Params {
    fn tys(&self, world: &World) -> Vec<Ty> {
        let mut tys = self.ints.clone();
        tys.extend(std::iter::repeat_n(Ty::Ptr, self.ptrs));
        if self.enum_param {
            tys.push(world.enum_ty.clone());
        }
        if self.vector_param {
            tys.push(world.vector_ty.clone());
        }
        tys
    }

    /// Whether the function can be run directly (integer parameters only).
    fn direct(&self) -> bool {
        self.ptrs == 0 && !self.enum_param && !self.vector_param
    }
}

/// Generate a function body into `gn` over `params` (already in scope).
fn generate_body(gn: &mut Gen<'_>, mut entry_scope: Scope) {
    gn.straight_line(&mut entry_scope, 12);
    match gn.rng.below(10) {
        // Straight line.
        0..=2 => gn.ret(&mut entry_scope),
        // A statically bounded loop (the scanner unrolls it): its body
        // re-executes every allocation and access in it per iteration.
        3 => {
            let (header, counter) = gn.f.block(&[Ty::I64]);
            let (body, _) = gn.f.block(&[]);
            let (exit, _) = gn.f.block(&[]);
            let zero = gn.f.int(Ty::I64, 0);
            gn.f.br(header, &[zero]);
            gn.f.switch_to(header);
            let trips = gn.f.int(Ty::I64, 1 + i128::from(gn.rng.below(4)));
            let more = gn.f.icmp(ICmpOp::Slt, Ty::I64, counter[0], trips);
            gn.f.condbr(more, body, exit);
            gn.f.switch_to(body);
            let mut scope = entry_scope.clone();
            scope.ints.push((counter[0], Ty::I64));
            gn.straight_line(&mut scope, 8);
            let one = gn.f.int(Ty::I64, 1);
            let next = gn.f.bin(BinOp::Add, Ty::I64, counter[0], one);
            gn.f.br(header, &[next]);
            gn.f.switch_to(exit);
            let mut scope = entry_scope.clone();
            gn.straight_line(&mut scope, 4);
            gn.ret(&mut scope);
        }
        // Two or more arms, joined or not.
        _ => {
            let (join, join_params) = gn.f.block(&[Ty::I64]);
            let arm_count = if gn.rng.chance(60) {
                2
            } else {
                2 + gn.rng.below(3) as usize
            };
            let arms = (0..arm_count)
                .map(|_| gn.f.block(&[]).0)
                .collect::<Vec<_>>();
            if arm_count == 2 && gn.rng.chance(70) {
                let cond = gn.bool_value(&mut entry_scope);
                gn.f.condbr(cond, arms[0], arms[1]);
            } else {
                let mut selector_tys = vec![Ty::U8, Ty::I64, Ty::U64];
                if gn.world.pointer_bits.is_some() {
                    selector_tys.push(Ty::Usize);
                }
                let ty = gn.rng.pick(&selector_tys).clone();
                let selector = gn.int_value(&mut entry_scope, &ty);
                let cases = arms[1..]
                    .iter()
                    .map(|arm| (gn.interesting(&ty), *arm))
                    .collect::<Vec<(i128, BlockId)>>();
                let mut seen = Vec::new();
                let cases = cases
                    .into_iter()
                    .filter(|(value, _)| {
                        let fresh = !seen.contains(value);
                        seen.push(*value);
                        fresh
                    })
                    .collect();
                gn.f.switch(selector, arms[0], cases);
            }
            let mut joined = false;
            for arm in &arms {
                gn.f.switch_to(*arm);
                let mut scope = entry_scope.clone();
                gn.straight_line(&mut scope, 6);
                match gn.rng.below(10) {
                    0..=6 => {
                        let value = gn.int_value(&mut scope, &Ty::I64);
                        gn.f.br(join, &[value]);
                        joined = true;
                    }
                    7 | 8 => gn.ret(&mut scope),
                    _ => gn.f.unreachable(),
                }
            }
            gn.f.switch_to(join);
            let mut scope = entry_scope.clone();
            scope.ints.push((join_params[0], Ty::I64));
            if joined {
                gn.straight_line(&mut scope, 5);
            }
            gn.ret(&mut scope);
        }
    }
}

/// A pointer argument the harness hands the function under test: an
/// interpreter-supplied allocation (initialized or not, at its base or
/// inside it), null, a freed heap block, an address naming no allocation,
/// or — at 64 bits — a pointer 2^64 - 8 bytes past an allocation, which a
/// 64-bit GEP makes without faulting and which has no address (exposing it
/// faults: a parameter's address is never one fsym may take as computed).
fn harness_pointer(h: &mut FnBuilder, rng: &mut Rng, world: &World) -> ValueId {
    let size_ty = if world.pointer_bits.is_some() {
        Ty::Usize
    } else {
        Ty::U64
    };
    let size = *rng.pick(&[1, 4, 8, 16, 64]);
    match rng.below(8) {
        0..=2 => {
            let count = h.int(size_ty.clone(), size);
            let a = h.alloca(Ty::U8, Some(count), Some(8));
            let fill = h.int(Ty::U8, 1);
            h.memset(a, fill, count);
            a
        }
        3 => {
            let count = h.int(size_ty, size);
            h.alloca(Ty::U8, Some(count), Some(8))
        }
        4 => h.null(),
        5 => {
            let count = h.int(size_ty.clone(), size);
            let p = h.heap(Ty::U8, Some(count));
            let fill = h.int(Ty::U8, 1);
            h.memset(p, fill, count);
            h.dealloc(p);
            p
        }
        6 => {
            let address = h.int(Ty::U64, 0x10_0000);
            h.inttoptr(address)
        }
        _ => {
            let count = h.int(size_ty.clone(), 16);
            let a = h.alloca(Ty::U8, Some(count), Some(8));
            let fill = h.int(Ty::U8, 1);
            h.memset(a, fill, count);
            let offset = if world.pointer_bits != Some(32) && rng.chance(25) {
                h.int(Ty::U64, i128::from(u64::MAX - 7))
            } else {
                h.int(Ty::I64, *rng.pick(&[1, 4, 8, 15, 16]))
            };
            h.gep(Ty::U8, a, offset)
        }
    }
}

/// `main_k(ints) -> i64`: builds the non-integer arguments of `f` and calls
/// it.
fn harness(name: &str, params: &Params, world: &World, f: FuncId, rng: &mut Rng) -> FnBuilder {
    harness_after(name, params, world, f, rng, Placements::None)
}

/// The harness that breaks the 64-bit BUDGET premise (`Placements::BreaksBudget`).
const BREAKS_BUDGET: &str = "exhaust";
/// The harness that ends a 32-bit object at 2^32 (`Placements::EndOfSpace`).
const END_OF_SPACE: &str = "end_of_space";

/// What a harness places after building `f`'s arguments (so they are
/// ordinary) and right before calling it.
#[derive(Debug, Clone, Copy)]
enum Placements {
    None,
    /// One-byte allocations at alignments `2^63, 2^62, .., 2^lowest`: a
    /// caller breaking the 64-bit BUDGET premise, which leaves the bump
    /// pointer at `2^64 - 2^lowest + 1`, so the allocations `f` makes can
    /// overflow. The caller also holds an `undef`, which fsym refuses: it is
    /// never scanned, and `f`'s placements still owe it.
    BreaksBudget(u32),
    /// On a 32-bit target: one-byte allocations at alignments `2^31 .. 2^12`
    /// (the bump pointer then at `2^32 - 4095`) and `gap` bytes more, so the
    /// allocation `f` makes first — an `end_probe` of `4095 - gap` bytes —
    /// ends exactly at 2^32.
    EndOfSpace(u64),
}

/// A harness that places `placements` right before the call.
fn harness_after(
    name: &str,
    params: &Params,
    world: &World,
    f: FuncId,
    rng: &mut Rng,
    placements: Placements,
) -> FnBuilder {
    let (mut h, ints) = FnBuilder::new(name, &params.ints, &[Ty::I64]);
    if matches!(placements, Placements::BreaksBudget(_)) {
        // An `undef` fsym never admits: the caller is refused (not scanned),
        // and the premise must still be the module's.
        h.value(Inst::Undef { ty: Ty::I64 });
    }
    let mut args = ints;
    for _ in 0..params.ptrs {
        args.push(harness_pointer(&mut h, rng, world));
    }
    if params.enum_param {
        let variant = rng.below(3) as u32;
        let mut elems = vec![Constant::Int(i128::from(variant))];
        elems.extend(enum_lanes(variant).iter().map(|_| Constant::Int(2)));
        args.push(h.value(Inst::Const {
            ty: world.enum_ty.clone(),
            value: Constant::Aggregate(elems),
        }));
    }
    if params.vector_param {
        args.push(h.value(Inst::Const {
            ty: world.vector_ty.clone(),
            value: Constant::Vector((0..4).map(Constant::Int).collect()),
        }));
    }
    match placements {
        Placements::None => {}
        Placements::BreaksBudget(lowest) => {
            for shift in (lowest..=63).rev() {
                h.alloca(Ty::U8, None, Some(1u64 << shift));
            }
        }
        Placements::EndOfSpace(gap) => {
            for shift in (12..=31).rev() {
                h.alloca(Ty::U8, None, Some(1u64 << shift));
            }
            if gap > 0 {
                let gap = h.int(Ty::Usize, i128::from(gap));
                h.alloca(Ty::U8, Some(gap), Some(1));
            }
        }
    }
    let result = h.value(Inst::Call { callee: f, args });
    h.ret(&[result]);
    h
}

/// Whether running `entry` on `args` reaches its call of `f` (function 0):
/// the same module with `f` returning at once runs to completion. A harness
/// whose own placements are refused tests nothing about `f`.
fn harness_reaches_call(module: &Module, entry: FuncId, args: &[InterpretValue]) -> bool {
    let mut stubbed = module.clone();
    let f = &mut stubbed.functions[0];
    let params = f
        .blocks
        .iter()
        .find(|block| block.id == f.entry)
        .map(|block| block.params.clone())
        .unwrap_or_default();
    let zero = ValueId::new(u32::MAX);
    f.blocks = vec![Block {
        id: f.entry,
        params,
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(zero),
            InstrNode::new(Inst::Return { values: vec![zero] }),
        ],
    }];
    matches!(interpret(&stubbed, entry, args), Run::Returned)
}

/// One generated case: the module, the function under test (`f`, function
/// 0), and the entry points and inputs the interpreter runs.
struct Generated {
    module: Module,
    /// `(entry, inputs)`: `f` itself when it takes integers only, else the
    /// harnesses that call it.
    entries: Vec<FuncId>,
    inputs: Vec<Vec<InterpretValue>>,
}

/// The constructs a generated module exercises in the function under test
/// and its callee: every `Inst` variant name, and the sub-shapes the oracle
/// must cover (see `REQUIRED_CONSTRUCTS`).
fn constructs(module: &Module) -> BTreeSet<String> {
    let mut tags = BTreeSet::new();
    let pointer_bits = module
        .target_info
        .as_ref()
        .map(|target| target.pointer_size * 8);
    for function in module
        .functions
        .iter()
        .filter(|function| function.name == "f" || function.name == "g")
    {
        let ty_of = |value: ValueId| function.typed_value(module, value).map(|meta| meta.ty);
        let int_to_float = function
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .filter(|node| {
                matches!(
                    node.inst,
                    Inst::Cast {
                        op: CastOp::SIToFP | CastOp::UIToFP,
                        ..
                    }
                )
            })
            .filter_map(|node| node.results.first().copied())
            .collect::<BTreeSet<_>>();
        // Constant integers and the entry parameters, for the layout tags.
        let constants = function
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .filter_map(|node| match (&node.inst, node.results.first()) {
                (
                    Inst::Const {
                        value: Constant::Int(value),
                        ..
                    },
                    Some(result),
                ) => Some((*result, *value)),
                _ => None,
            })
            .collect::<BTreeMap<_, _>>();
        let entry_params = function
            .blocks
            .iter()
            .find(|block| block.id == function.entry)
            .map(|block| block.params.iter().map(|(value, _)| *value).collect())
            .unwrap_or_else(BTreeSet::new);
        let layout_tag = |ty: &Ty| -> Option<&'static str> {
            if *ty == huge_ty() {
                Some("Layout.HugeAlign")
            } else if *ty == declared_ty() || *ty == big_ty() {
                Some("Layout.DeclaredStruct")
            } else if *ty == bool_vector_ty() {
                Some("Layout.BoolVector")
            } else {
                None
            }
        };
        // What each value is defined by, and the pointers written byte-wise
        // (a scalar tag store or a fill), for the initialization-mask tags.
        let defs = function
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .filter_map(|node| node.results.first().map(|result| (*result, &node.inst)))
            .collect::<BTreeMap<_, _>>();
        let is_select = |value: &ValueId| matches!(defs.get(value), Some(Inst::Select { .. }));
        let at_undecided_offset = |ptr: &ValueId| matches!(defs.get(ptr), Some(Inst::GEP { indices, .. }) if indices.iter().any(is_select));
        let untracked_source = |ptr: &ValueId| {
            matches!(
                defs.get(ptr),
                Some(Inst::Alloca { count: Some(count), .. })
                    if constants.get(count).is_some_and(|count| *count > 4096)
            )
        };
        let partially_written = function
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .filter_map(|node| match &node.inst {
                Inst::Store { ty, ptr, .. } if !matches!(ty, Ty::Enum(_)) => Some(*ptr),
                Inst::MemSet { dst, .. } => Some(*dst),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        let mut mentions_usize = false;
        let note_ty = |ty: &Ty, mentions_usize: &mut bool| {
            if matches!(ty, Ty::Usize | Ty::Isize) {
                *mentions_usize = true;
            }
        };
        for block in &function.blocks {
            for (value, ty) in &block.params {
                note_ty(ty, &mut mentions_usize);
                if function.name == "f" && block.id == function.entry {
                    let _ = value;
                    match ty {
                        Ty::Ptr => tags.insert("Param.Ptr".to_string()),
                        Ty::Enum(_) => tags.insert("Param.Enum".to_string()),
                        Ty::Vector(..) => tags.insert("Param.Vector".to_string()),
                        _ => false,
                    };
                }
            }
            for node in &block.body {
                let name = fsym_inst_variant_name(&node.inst);
                tags.insert(name.to_string());
                for proof in &node.proofs {
                    tags.insert(format!("Proof.{proof:?}"));
                }
                let kind = |ty: Option<Ty>| match ty {
                    Some(Ty::Enum(_)) => "Enum",
                    Some(Ty::Tuple(_)) => "Tuple",
                    Some(Ty::Vector(..)) => "Vector",
                    Some(Ty::Array(..)) => "Array",
                    _ => "other",
                };
                match &node.inst {
                    Inst::Alloca { ty, .. } | Inst::HeapAlloc { ty, .. } => {
                        if let Some(tag) = layout_tag(ty) {
                            tags.insert(tag.to_string());
                        }
                    }
                    Inst::GEP {
                        pointee_ty,
                        indices,
                        ..
                    } => {
                        if *pointee_ty == declared_ty() || *pointee_ty == big_ty() {
                            tags.insert("Layout.DeclaredStride".to_string());
                        } else if let Some(tag) = layout_tag(pointee_ty) {
                            tags.insert(tag.to_string());
                        }
                        if pointer_bits == Some(32)
                            && indices.iter().any(|index| {
                                constants.get(index).is_some_and(|value| *value >= 1 << 31)
                            })
                        {
                            tags.insert("GEP.Wide@32".to_string());
                        }
                    }
                    Inst::Load { ty, ptr, .. } | Inst::Store { ty, ptr, .. } => {
                        if let Some(tag) = layout_tag(ty) {
                            tags.insert(tag.to_string());
                        }
                        if matches!(node.inst, Inst::Store { .. })
                            && matches!(ty, Ty::Struct(_) | Ty::Tuple(_) | Ty::Enum(_))
                        {
                            tags.insert("Store.Aggregate".to_string());
                            if let Inst::Store { value, .. } = &node.inst
                                && matches!(ty, Ty::Enum(_))
                                && is_select(value)
                            {
                                tags.insert("Store.UntrackedVariant".to_string());
                            }
                            if let Some(Inst::GEP { indices, .. }) = defs.get(ptr)
                                && indices.iter().any(is_select)
                            {
                                tags.insert("Store.AggregateAtUndecidedOffset".to_string());
                            }
                        }
                        if matches!(node.inst, Inst::Load { .. })
                            && matches!(ty, Ty::Enum(_))
                            && partially_written.contains(ptr)
                        {
                            tags.insert("Load.EnumOverPartialWrites".to_string());
                        }
                        if matches!(node.inst, Inst::Load { .. }) && at_undecided_offset(ptr) {
                            tags.insert("Load.AtUndecidedOffset".to_string());
                        }
                        if !node.proofs.is_empty() && entry_params.contains(ptr) {
                            tags.insert("Proof.OnParam".to_string());
                        }
                    }
                    Inst::GlobalAddr { global } if global.index() >= 1 => {
                        tags.insert("GlobalAddr.HugeAlign".to_string());
                    }
                    Inst::MemCopy { src, .. } => {
                        if untracked_source(src) {
                            tags.insert("MemCopy.FromUntrackedSource".to_string());
                        }
                        if at_undecided_offset(src) {
                            tags.insert("MemCopy.AtUndecidedSource".to_string());
                        }
                    }
                    Inst::MemSet { bytes, .. } if is_select(bytes) => {
                        tags.insert("MemSet.SymbolicCount".to_string());
                        if let Some(Inst::Select {
                            then_val, else_val, ..
                        }) = defs.get(bytes)
                            && [then_val, else_val].into_iter().any(|count| {
                                constants.get(count).is_some_and(|count| *count >= 1 << 63)
                            })
                        {
                            tags.insert("MemSet.SymbolicCountPastTheSpace".to_string());
                        }
                    }
                    Inst::Cast {
                        op,
                        src_ty,
                        dst_ty,
                        operand,
                    } => {
                        tags.insert(format!("Cast.{op:?}"));
                        if matches!(op, CastOp::FPToSI | CastOp::FPToUI)
                            && int_to_float.contains(operand)
                        {
                            tags.insert("Cast.IntFloatIntRoundTrip".to_string());
                        }
                        if *src_ty == Ty::Bool || *dst_ty == Ty::Bool {
                            tags.insert(format!("Cast.{op:?}.Bool"));
                        }
                        note_ty(src_ty, &mut mentions_usize);
                        note_ty(dst_ty, &mut mentions_usize);
                    }
                    Inst::BinOp { ty, .. } | Inst::UnOp { ty, .. } => {
                        if ty.is_float() {
                            tags.insert(format!("{name}.float"));
                        } else if matches!(ty, Ty::Vector(..)) {
                            tags.insert(format!("{name}.vector"));
                        }
                        note_ty(ty, &mut mentions_usize);
                    }
                    Inst::Const { ty, .. } | Inst::ICmp { ty, .. } => {
                        note_ty(ty, &mut mentions_usize)
                    }
                    Inst::ExtractField { aggregate, .. } => {
                        tags.insert(format!("{name}.{}", kind(ty_of(*aggregate))));
                    }
                    Inst::InsertField { ty, .. } | Inst::MakeAggregate { ty, .. } => {
                        tags.insert(format!("{name}.{}", kind(Some(ty.clone()))));
                    }
                    Inst::ExtractElement { array, .. } => {
                        tags.insert(format!("{name}.{}", kind(ty_of(*array))));
                    }
                    Inst::InsertElement { ty, .. } => {
                        tags.insert(format!("{name}.{}", kind(Some(ty.clone()))));
                    }
                    Inst::Call { callee, .. } => {
                        let bodied = module
                            .function_by_id(*callee)
                            .is_some_and(|callee| !callee.blocks.is_empty());
                        tags.insert(
                            if bodied {
                                "Call.module-body"
                            } else {
                                "Call.external"
                            }
                            .to_string(),
                        );
                    }
                    _ => {}
                }
            }
        }
        if mentions_usize && let Some(bits) = pointer_bits {
            tags.insert(format!("Usize@{bits}"));
        }
    }
    // A harness handing `f` a pointer 2^64 - 8 bytes past an allocation.
    let far = Constant::Int(i128::from(u64::MAX - 7));
    if module
        .functions
        .iter()
        .filter(|function| function.name != "f" && function.name != "g")
        .any(|function| {
            let body = || function.blocks.iter().flat_map(|block| &block.body);
            body().any(|node| match &node.inst {
                Inst::GEP { indices, .. } => indices.iter().any(|index| {
                    body().any(|def| {
                        def.results.first() == Some(index)
                            && matches!(&def.inst, Inst::Const { ty: Ty::U64, value } if *value == far)
                    })
                }),
                _ => false,
            })
        })
    {
        tags.insert("Harness.FarPointer".to_string());
    }
    for (harness, tag) in [
        (BREAKS_BUDGET, "Harness.BreaksBudget"),
        (END_OF_SPACE, "Harness.EndOfSpace"),
    ] {
        if module
            .functions
            .iter()
            .any(|function| function.name == harness)
        {
            tags.insert(tag.to_string());
        }
    }
    tags
}

/// Sub-shapes the generated corpus must exercise (besides every admitted
/// `Inst` variant): the constructs each adversarial round found unguarded.
const REQUIRED_CONSTRUCTS: &[&str] = &[
    "Call.module-body",
    "Call.external",
    "Param.Ptr",
    "Param.Enum",
    "Param.Vector",
    "Cast.FPToSI",
    "Cast.FPToUI",
    "Cast.FPToSISat",
    "Cast.FPToUISat",
    "Cast.SIToFP",
    "Cast.UIToFP",
    "Cast.FPExt",
    "Cast.FPTrunc",
    "Cast.IntFloatIntRoundTrip",
    "Cast.ZExt.Bool",
    "Cast.SExt.Bool",
    "Cast.Trunc.Bool",
    "Cast.PtrToInt",
    "Cast.IntToPtr",
    "BinOp.float",
    "BinOp.vector",
    "UnOp.float",
    "ExtractElement.Vector",
    "ExtractElement.Array",
    "InsertElement.Vector",
    "InsertElement.Array",
    "ExtractField.Enum",
    "ExtractField.Tuple",
    "InsertField.Enum",
    "InsertField.Tuple",
    "MakeAggregate.Enum",
    "MakeAggregate.Tuple",
    "Proof.NotNull",
    "Proof.InBounds",
    "Usize@32",
    "Usize@64",
    // Layout (every size, offset, stride and alignment is the interpreter's).
    "Layout.HugeAlign",
    "Layout.DeclaredStruct",
    "Layout.DeclaredStride",
    "Layout.BoolVector",
    "Store.Aggregate",
    "GlobalAddr.HugeAlign",
    "GEP.Wide@32",
    // Annotations nothing checks: on a parameter's access.
    "Proof.OnParam",
    // Initialization masks that are not byte-exact, and a caller breaking
    // the BUDGET premise the callee's placements rest on.
    "Store.UntrackedVariant",
    "Store.AggregateAtUndecidedOffset",
    "Load.EnumOverPartialWrites",
    "Harness.BreaksBudget",
    // Bytes a copy moves, a load reads or a fill writes, undecided (a fill
    // that may run the length of the address space among them); a harness
    // handing `f` a pointer past the address space; and a 32-bit object
    // ending exactly at the end of the address space.
    "MemCopy.FromUntrackedSource",
    "MemCopy.AtUndecidedSource",
    "Load.AtUndecidedOffset",
    "MemSet.SymbolicCount",
    "MemSet.SymbolicCountPastTheSpace",
    "Harness.FarPointer",
    "Harness.EndOfSpace",
];

/// Admitted `Inst` variants the generator does not produce, each with why.
/// Every other admitted variant (`FSYM_INST_VARIANTS`) must be generated.
const NOT_GENERATED: &[(&str, &str)] = &[(
    "LandingPad",
    "the reference interpreter refuses to execute it (UnsupportedInstruction: no unwind edge under panic=abort), so no run can give it an oracle verdict; it raises no interpreter UB",
)];

const HARNESSES: usize = 2;

fn generate(seed: u64) -> Generated {
    let mut rng = Rng(seed);
    let mut world = world(&mut rng);
    let int_choices = |world: &World| {
        let mut tys = vec![Ty::I64, Ty::U64, Ty::U8];
        if world.pointer_bits.is_some() {
            tys.push(Ty::Usize);
        }
        tys
    };
    // A FOCUSED case is a small function of one or two layout probes over a
    // `u8` parameter (and sometimes a pointer): small enough that fsym can
    // claim it clean — as scanned or after the local solver — so the oracle
    // sees the verdict of each probe on its own.
    let focused = rng.chance(6);
    let params = if focused {
        Params {
            ints: vec![Ty::U8],
            ptrs: usize::from(rng.chance(30)),
            enum_param: false,
            vector_param: false,
        }
    } else {
        Params {
            ints: (0..rng.below(3))
                .map(|_| rng.pick(&int_choices(&world)).clone())
                .collect(),
            ptrs: if rng.chance(35) {
                1 + rng.below(2) as usize
            } else {
                0
            },
            enum_param: rng.chance(10),
            vector_param: rng.chance(8),
        }
    };

    // Module layout: f = 0, then the callee g, then the external
    // declaration, then the harnesses.
    let mut next_id = 1u32;
    if rng.chance(20) {
        let tys = if rng.chance(50) {
            vec![Ty::I64, Ty::Ptr]
        } else {
            vec![Ty::U64]
        };
        world.callee = Some((FuncId::new(next_id), tys));
        next_id += 1;
    }
    if rng.chance(5) {
        let tys = if rng.chance(50) {
            vec![Ty::Ptr, Ty::U64]
        } else {
            vec![Ty::I64]
        };
        world.external = Some((FuncId::new(next_id), tys));
    }
    if rng.chance(10) {
        world.global = Some(GlobalId::new(0));
    }
    if rng.chance(8) {
        world.huge_global = Some(GlobalId::new(1));
    }

    let param_tys = params.tys(&world);
    let (f, values) = FnBuilder::new("f", &param_tys, &[Ty::I64]);
    let mut entry_scope = Scope::default();
    for (value, ty) in values.iter().zip(&param_tys) {
        match ty {
            Ty::Ptr => entry_scope.ptrs.push(PtrVal {
                id: *value,
                exact: false,
            }),
            Ty::Enum(_) => entry_scope.enums.push(*value),
            Ty::Vector(..) => entry_scope.lanes.push((*value, ty.clone())),
            ty => entry_scope.ints.push((*value, ty.clone())),
        }
    }
    let mut gn = Gen {
        rng: &mut rng,
        f,
        world: &world,
        may_call: true,
    };
    let mut end_probe = None;
    if focused {
        let mut scope = entry_scope;
        if let Some(global) = gn.world.huge_global {
            // Globals of a type aligned to 2^63: materializing both places
            // the second past the address space.
            for index in 0..=gn.rng.below(2) {
                let global = GlobalId::new(global.index() + index as u32);
                let id = gn.f.value(Inst::GlobalAddr { global });
                scope.ptrs.push(PtrVal { id, exact: false });
            }
        } else if gn.world.pointer_bits == Some(32) && gn.rng.chance(35) {
            // First, so the end-of-space harness can place it.
            end_probe = Some(gn.end_probe(&mut scope));
            if gn.rng.chance(30) {
                gn.layout_probe(&mut scope);
            }
        } else {
            for _ in 0..=gn.rng.below(2) {
                gn.layout_probe(&mut scope);
            }
        }
        gn.ret(&mut scope);
    } else {
        generate_body(&mut gn, entry_scope);
    }
    let mut f = gn.f;
    // A zero-capture closure of f itself has exactly f's apparent signature.
    // Construct it first so every generated run exercises the newly admitted
    // pure value operation, including runs that later find UB. It is not called.
    let environment = f.fresh();
    f.blocks[0].body.insert(
        0,
        InstrNode::new(Inst::MakeClosure {
            ty: trust_ir::ClosureTyId::new(0),
            func: FuncId::new(0),
            captures: vec![],
        })
        .with_result(environment),
    );

    let callee = world.callee.clone().map(|(_, tys)| {
        let (g, values) = FnBuilder::new("g", &tys, &[Ty::I64]);
        let mut scope = Scope::default();
        for (value, ty) in values.iter().zip(&tys) {
            match ty {
                Ty::Ptr => scope.ptrs.push(PtrVal {
                    id: *value,
                    exact: false,
                }),
                ty => scope.ints.push((*value, ty.clone())),
            }
        }
        let mut gn = Gen {
            rng: &mut rng,
            f: g,
            world: &world,
            may_call: false,
        };
        gn.straight_line(&mut scope, 6);
        gn.ret(&mut scope);
        gn.f
    });

    let mut module = world_module(&format!("oracle_{seed:016x}"), &world);
    f.install(&mut module);
    module.closure_types.push(trust_ir::ClosureTy {
        func: module.functions[0].ty,
        captures: vec![],
    });
    if let Some(g) = callee {
        g.install(&mut module);
    }
    if let Some((_, tys)) = &world.external {
        declare(&mut module, "ext", tys.clone());
    }
    let mut entries = Vec::new();
    if params.direct() {
        entries.push(FuncId::new(0));
    } else {
        for index in 0..HARNESSES {
            let h = harness(
                &format!("main{index}"),
                &params,
                &world,
                FuncId::new(0),
                &mut rng,
            );
            entries.push(h.install(&mut module));
        }
    }
    // Sometimes, at 64 bits, a caller that breaks the BUDGET premise before
    // calling `f`: `f`'s own allocations are modeled, but its claim rests on
    // the run's. (At 32 bits its first 2^63-aligned placement is refused
    // outright: it would test nothing.) At 32 bits, after an `end_probe`, a
    // caller that ends the probe's object exactly at 2^32.
    let placements = match (world.pointer_bits, end_probe) {
        (Some(32), Some(size)) => Placements::EndOfSpace(4095 - size),
        (Some(32), None) => Placements::None,
        _ if rng.chance(4) => Placements::BreaksBudget(*rng.pick(&[4, 12])),
        _ => Placements::None,
    };
    let name = match placements {
        Placements::None => None,
        Placements::BreaksBudget(_) => Some(BREAKS_BUDGET),
        Placements::EndOfSpace(_) => Some(END_OF_SPACE),
    };
    if let Some(name) = name {
        let h = harness_after(name, &params, &world, FuncId::new(0), &mut rng, placements);
        entries.push(h.install(&mut module));
    }

    let mut inputs = Vec::new();
    for pattern in 0..4u64 {
        let args = params
            .ints
            .iter()
            .map(|ty| {
                let bits = world_width(&world, ty);
                let value = match pattern {
                    0 => 0,
                    1 => 1,
                    2 => {
                        if ty.is_signed() {
                            -1
                        } else {
                            (1i128 << bits) - 1
                        }
                    }
                    _ => i128::from(rng.below(20)),
                };
                InterpretValue::int_at(ty.clone(), value, world.pointer_bits.unwrap_or(64))
                    .expect("entry argument")
            })
            .collect();
        inputs.push(args);
    }
    Generated {
        module,
        entries,
        inputs,
    }
}

/// The bodied functions `function` can call, transitively (itself
/// included): UB in a callee's body is the callee's own obligation, so fsym
/// claims `function` free of UB only when every one of them is clean.
fn call_closure(module: &Module, function: FuncId) -> Vec<FuncId> {
    let mut seen = vec![function];
    let mut index = 0;
    while index < seen.len() {
        let Some(current) = module.function_by_id(seen[index]) else {
            index += 1;
            continue;
        };
        for node in current.blocks.iter().flat_map(|block| &block.body) {
            if let Inst::Call { callee, .. } = &node.inst
                && module
                    .function_by_id(*callee)
                    .is_some_and(|callee| !callee.blocks.is_empty())
                && !seen.contains(callee)
            {
                seen.push(*callee);
            }
        }
        index += 1;
    }
    seen
}

fn claimed_clean(module: &Module, report: &FsymTrustIrReport, function: FuncId) -> bool {
    call_closure(module, function).iter().all(|id| {
        module
            .function_by_id(*id)
            .is_some_and(|function| fsym_clean(report, &function.name))
    })
}

/// fsym's claim after the bounded LOCAL solver escalation (the
/// `--fsym --fsym-solver` lane): every Unknown of the function and its
/// callees proven safe, and nothing else reported against them.
fn claimed_clean_after_solver(
    module: &Module,
    report: &FsymTrustIrReport,
    function: FuncId,
) -> bool {
    let names = call_closure(module, function)
        .iter()
        .filter_map(|id| module.function_by_id(*id).map(|f| f.name.clone()))
        .collect::<Vec<_>>();
    let ours = |name: &String| names.contains(name);
    if names.iter().any(|name| {
        !report.scanned_function_names.contains(name)
            || report.skipped_functions.iter().any(|s| &s.function == name)
    }) || report.diagnostics.iter().any(|d| ours(&d.function))
        || report.coverage_errors.iter().any(|c| ours(&c.function))
    {
        return false;
    }
    let unknowns = report
        .unknown_obligations
        .iter()
        .filter(|u| ours(&u.function))
        .collect::<Vec<_>>();
    if unknowns.is_empty() {
        return true;
    }
    if unknowns.iter().any(|u| u.solver_candidate.is_none()) {
        return false;
    }
    // One obligation at a time, stopping at the first the solver does not
    // prove (the claim needs all of them).
    let config = FsymSolverEscalationConfig::enabled();
    unknowns.into_iter().all(|unknown| {
        let obligation = FsymSolverEscalation {
            label: unknown.label.clone(),
            kind: unknown.kind,
            module: unknown.module.clone(),
            function: unknown.function.clone(),
            block: unknown.block,
            inst_index: unknown.inst_index,
            reason: unknown.reason.clone(),
            path_guards: unknown.path_guards.clone(),
            candidate_expression: unknown.candidate_expression.clone(),
            solver_candidate: unknown.solver_candidate.clone(),
        };
        FsymLocalSolverAdapter.solve(&obligation, &config).status == FsymSolverStatus::ProvenSafe
    })
}

const GENERATED_FUNCTIONS: u64 = 20_000;
/// How many first UBs of each message class (`ub_message_class`) the
/// generated corpus attributes to their raiser (`attribute`).
const ATTRIBUTED_PER_CLASS: usize = 64;
const ORACLE_SEED: u64 = 0x0FA5_7EED_2026_0923;

/// `name` from the environment as a number (decimal or `0x` hex), else
/// `default`: the corpus is fixed unless an exploratory run asks otherwise.
fn env_u64(name: &str, default: u64) -> u64 {
    std::env::var(name).ok().map_or(default, |value| {
        let parsed = match value.strip_prefix("0x") {
            Some(hex) => u64::from_str_radix(hex, 16),
            None => value.parse(),
        };
        parsed.unwrap_or_else(|_| panic!("{name}={value} is not a number"))
    })
}

/// Per construct: how many generated modules exercise it, how many of those
/// fsym claims clean, and how many of those the interpreter also ran to
/// completion.
#[derive(Default, Debug)]
struct ConstructStats {
    generated: usize,
    clean: usize,
    clean_and_executed: usize,
}

/// Keep the generator's new construction in the executed denominator without
/// rerunning the full randomized/solver corpus for this focused value extension.
#[test]
fn generated_runtime_closure_prefix_executes_with_its_exact_signature() {
    let mut executed = 0;
    for seed in 0..64 {
        let mut generated = generate(seed);
        if generated.entries.first() != Some(&FuncId::new(0)) {
            continue;
        }
        let function = &mut generated.module.functions[0];
        let prefix = function.blocks[0].body[0].clone();
        assert!(matches!(&prefix.inst, Inst::MakeClosure { captures, .. } if captures.is_empty()));
        let result = ValueId::new(
            function
                .blocks
                .iter()
                .flat_map(|b| &b.body)
                .flat_map(|n| &n.results)
                .map(|id| id.index())
                .max()
                .unwrap()
                + 1,
        );
        function.blocks.truncate(1);
        function.blocks[0].body = vec![
            prefix,
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(result),
            InstrNode::new(Inst::Return {
                values: vec![result],
            }),
        ];
        let outcome = Interpreter::with_module(&generated.module)
            .execute_func(FuncId::new(0), generated.inputs[0].clone())
            .unwrap();
        assert_eq!(outcome.returns[0].as_int().unwrap().as_signed(), 0);
        let report = scan_function_in_module(&generated.module, &generated.module.functions[0]);
        assert!(fsym_clean(&report, "f"), "seed {seed}: {report:?}");
        executed += 1;
    }
    assert!(
        executed >= 10,
        "only {executed} generated constructor executions"
    );
    eprintln!("executed {executed} generated zero-capture constructors");
}

#[test]
fn generated_functions_with_interpreter_ub_are_never_clean() {
    let started = Instant::now();
    let mut failures = Vec::new();
    let mut crashes = Vec::new();
    let mut executed = 0usize;
    let mut with_ub = 0usize;
    let mut clean = 0usize;
    let mut clean_and_executed = 0usize;
    let mut clean_after_solver = 0usize;
    let mut ub_by_class: BTreeMap<String, usize> = BTreeMap::new();
    let mut missed_by_class: BTreeMap<String, usize> = BTreeMap::new();
    let mut stats: BTreeMap<String, ConstructStats> = BTreeMap::new();
    let mut attributed = 0usize;
    let mut attributed_by_class: BTreeMap<String, usize> = BTreeMap::new();
    let mut attributions: BTreeMap<(&str, &str, &str), usize> = BTreeMap::new();
    let mut stance_failures = Vec::new();
    // Per placing harness: its runs, and those that reach their call of `f`.
    let mut harness_runs: BTreeMap<&str, (usize, usize)> = BTreeMap::new();
    let mut vacuous = Vec::new();
    let functions = env_u64("FSYM_ORACLE_FUNCTIONS", GENERATED_FUNCTIONS);
    let oracle_seed = env_u64("FSYM_ORACLE_SEED", ORACLE_SEED);
    for index in 0..functions {
        let seed = oracle_seed ^ index.wrapping_mul(0xD1B5_4A32_D192_ED03);
        let generated = generate(seed);
        let module = &generated.module;
        let Some(report) = scan_catching_panics(module) else {
            crashes.push(format!("seed {seed:#018x}: scan_module panicked"));
            continue;
        };
        let is_clean = claimed_clean(module, &report, FuncId::new(0));
        // The claim after the bounded local solver: stronger, never weaker.
        let is_clean_after_solver =
            is_clean || claimed_clean_after_solver(module, &report, FuncId::new(0));
        clean += usize::from(is_clean);
        clean_after_solver += usize::from(is_clean_after_solver);
        let mut ran = false;
        let mut ub = None;
        for entry in &generated.entries {
            let harness = [BREAKS_BUDGET, END_OF_SPACE].into_iter().find(|name| {
                module
                    .function_by_id(*entry)
                    .is_some_and(|function| function.name == *name)
            });
            for args in &generated.inputs {
                if let Some(harness) = harness {
                    let (runs, reached) = harness_runs.entry(harness).or_insert((0usize, 0usize));
                    *runs += 1;
                    if harness_reaches_call(module, *entry, args) {
                        *reached += 1;
                    } else if vacuous.len() < 12 {
                        vacuous.push(format!(
                            "seed {seed:#018x}: harness `{harness}` never reaches its call of `f`"
                        ));
                    }
                }
                match interpret(module, *entry, args) {
                    Run::Returned => ran = true,
                    Run::Ub(error) => {
                        ub.get_or_insert((*entry, args.clone(), error));
                    }
                    Run::Refused(..) => {}
                }
            }
        }
        executed += usize::from(ran);
        clean_and_executed += usize::from(ran && is_clean);
        for construct in constructs(module) {
            let entry = stats.entry(construct).or_default();
            entry.generated += 1;
            entry.clean += usize::from(is_clean);
            entry.clean_and_executed += usize::from(is_clean && ran);
        }
        if let Some((entry, args, error)) = ub {
            let message = error.to_string();
            with_ub += 1;
            let class = ub_message_class(&message);
            *ub_by_class.entry(class.clone()).or_default() += 1;
            if is_clean_after_solver {
                *missed_by_class.entry(class.clone()).or_default() += 1;
                let claim = if is_clean {
                    "scans clean"
                } else {
                    "is clean after the local solver"
                };
                if failures.len() < 12 {
                    failures.push(format!(
                        "seed {seed:#018x}: interpreter UB via f{} on {:?}: {message}\n  fsym {claim}: {}\n  module: {:#?}",
                        entry.index(),
                        args.iter().map(|arg| arg.as_int().map(|int| int.as_signed())).collect::<Vec<_>>(),
                        fsym_summary_line(&report, "f"),
                        module.functions[0].blocks
                    ));
                } else {
                    failures.push(format!("seed {seed:#018x} ({claim}): {message}"));
                }
            }
            // The UB map's stance for the site and the instruction that
            // raised it: it must owe the UB there (or where its poison was
            // made), never say it cannot arise — up to
            // `ATTRIBUTED_PER_CLASS` of each message class (the message
            // names the raising operation, so each class keeps its raisers).
            let seen = attributed_by_class.entry(class).or_insert(0usize);
            if *seen < ATTRIBUTED_PER_CLASS {
                *seen += 1;
                let split = split_module(generated.module);
                match attribute(&split, entry, &args, &error, run_options(FUEL)) {
                    Ok(observed) => {
                        attributed += 1;
                        for site in &observed.sites {
                            *attributions
                                .entry((site.function, site.message, observed.raiser))
                                .or_default() += 1;
                        }
                        if let Err(why) = owed_verdict_reported(&split.module, &report, &observed) {
                            stance_failures.push(format!("seed {seed:#018x}: {why}"));
                        }
                    }
                    Err(why) => stance_failures.push(format!("seed {seed:#018x}: {why}")),
                }
            }
        }
    }
    let elapsed = started.elapsed();
    eprintln!(
        "fsym oracle: {functions} generated functions (seed {oracle_seed:#x}) in {elapsed:?}: executed={executed} ub={with_ub} fsym_clean={clean} clean_after_local_solver={clean_after_solver} clean_and_executed={clean_and_executed} unsound={} crashes={}",
        failures.len(),
        crashes.len()
    );
    eprintln!("fsym oracle: interpreter UB by class: {ub_by_class:?}");
    eprintln!("fsym oracle: unsound by class: {missed_by_class:?}");
    for (construct, stat) in &stats {
        eprintln!(
            "fsym oracle: construct {construct}: generated={} clean={} clean_and_executed={}",
            stat.generated, stat.clean, stat.clean_and_executed
        );
    }
    assert!(
        crashes.is_empty(),
        "{} generated function(s) crash the scanner:\n{}",
        crashes.len(),
        crashes
            .iter()
            .take(12)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert!(
        failures.is_empty(),
        "{} generated function(s) have interpreter UB but fsym claims them clean:\n{}",
        failures.len(),
        failures.join("\n")
    );
    eprintln!(
        "fsym oracle: {attributed} of {with_ub} first UBs attributed to their raiser (at most {ATTRIBUTED_PER_CLASS} per message class); (site, raiser) pairs seen: {}",
        attributions.len()
    );
    assert!(
        stance_failures.is_empty(),
        "{} observed interpreter UB(s) contradict the UB map's stance for the site and raiser:\n{}",
        stance_failures.len(),
        stance_failures
            .iter()
            .take(12)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert_eq!(
        attributed,
        attributed_by_class.values().sum::<usize>(),
        "every UB taken for attribution is attributed"
    );
    assert!(
        attributions.len() >= 60,
        "only {} distinct (site, raiser) pairs observed",
        attributions.len()
    );

    // Coverage: every instruction the admission gate admits is generated
    // (`FSYM_INST_VARIANTS`, checked against the gate in fsym_ub_map.rs), and
    // every required sub-shape; a construct the generator cannot produce
    // is named in `NOT_GENERATED` with why.
    let mut missing = Vec::new();
    for (name, admitted) in FSYM_INST_VARIANTS {
        let excused = NOT_GENERATED.iter().any(|(excused, _)| excused == name);
        let generated = stats.contains_key(*name);
        match (*admitted, excused, generated) {
            (true, false, false) => missing.push(format!("admitted instruction `{name}`")),
            (_, true, true) => missing.push(format!(
                "`{name}` is generated but NOT_GENERATED excuses it: drop the excuse"
            )),
            (false, true, _) => missing.push(format!(
                "`{name}` is refused at admission; NOT_GENERATED need not excuse it"
            )),
            _ => {}
        }
    }
    for construct in REQUIRED_CONSTRUCTS {
        if !stats.contains_key(*construct) {
            missing.push(format!("construct `{construct}`"));
        }
    }
    assert!(
        missing.is_empty(),
        "the generator does not cover: {}",
        missing.join(", ")
    );

    // Non-vacuity floors (see the module docs). A placing harness tests
    // `f` only when its own placements leave it to call `f`.
    eprintln!("fsym oracle: placing harness runs (runs, reaching the call): {harness_runs:?}");
    assert!(
        vacuous.is_empty(),
        "placing harnesses test nothing:\n{}",
        vacuous.join("\n")
    );
    let total = functions as usize;
    assert!(
        executed * 10 >= total,
        "only {executed} of {total} executed"
    );
    assert!(with_ub * 5 >= total, "only {with_ub} of {total} hit UB");
    assert!(clean * 25 >= total, "only {clean} of {total} scanned clean");
    assert!(
        clean_and_executed * 40 >= total,
        "only {clean_and_executed} of {total} scanned clean AND executed"
    );
    // A clean verdict must be seen on the constructs whose UB each round
    // found unguarded, or the oracle checks nothing about their Safe arms.
    for construct in CLEAN_CONSTRUCTS {
        let seen = stats
            .get(*construct)
            .map_or(0, |stat| stat.clean_and_executed);
        assert!(
            seen > 0,
            "no generated function using `{construct}` scanned clean and executed"
        );
    }
}

/// Constructs with a `Safe` verdict fsym can reach: some generated function
/// using each must scan clean AND run to completion.
const CLEAN_CONSTRUCTS: &[&str] = &[
    "Cast.FPToSI",
    "Cast.FPToUI",
    "Cast.IntFloatIntRoundTrip",
    "Cast.ZExt.Bool",
    "Cast.SExt.Bool",
    "ExtractElement.Vector",
    "ExtractElement.Array",
    "InsertElement.Vector",
    "ExtractField.Enum",
    "ExtractField.Tuple",
    "InsertField.Enum",
    "MakeAggregate.Enum",
    "Borrow",
    "BorrowMut",
    "Call.module-body",
    "Usize@32",
    "Usize@64",
    "Store.Aggregate",
    "Layout.DeclaredStruct",
    "Layout.DeclaredStride",
    "Layout.BoolVector",
    "Harness.EndOfSpace",
];

/// A coarse class of an interpreter UB message (for the report only): its
/// text with numbers and quoted details stripped.
fn ub_message_class(message: &str) -> String {
    let message = message
        .split_once("undefined_behavior")
        .map_or(message, |(_, rest)| rest);
    let mut class = String::new();
    for word in message.split_whitespace().take(7) {
        let word = if word.chars().any(|c| c.is_ascii_digit()) {
            "#"
        } else {
            word
        };
        if !class.is_empty() {
            class.push(' ');
        }
        class.push_str(word);
    }
    class
}
