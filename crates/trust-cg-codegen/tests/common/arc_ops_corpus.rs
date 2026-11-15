// Copyright 2026 Andrew Yates | Apache-2.0
//! Shared TrustIR corpus, C driver and reference-interpreter oracle for the
//! AArch64 ELF ARC-op controls (`e2e_aarch64_arc_ops_linux.rs`, ledger
//! L05-P3).
//!
//! The corpus declares the exact Clean RC-runtime triple as bodyless
//! externals (`clean_inc(ptr) -> ()`, `clean_dec(ptr) -> ()`,
//! `clean_is_exclusive(ptr) -> u8`), which is what makes the backend lower
//! `Inst::Retain`/`Inst::Release`/`Inst::IsUnique` to calls, and drives those
//! ops on `Inst::HeapAlloc` cells of the `CMalloc` and `RustHeap` origins:
//! unique, then shared, then unique again; release to zero; `IsUnique`
//! polarity in straight-line code, loops and across blocks; and a cell
//! retained and released back to one, then freed by a CALL to its
//! allocator's release entry (`__rust_dealloc(ptr, size, align)` / `free`) —
//! the spelling producers use; `Inst::Dealloc` is refused for codegen in every
//! body (G18-1, re-decided 2026-09-27).
//!
//! **trust-ir calls the compiled program undefined.** `Retain`, `Release` and
//! `IsUnique` are defined only on a reference-counted cell, a live allocation
//! that `HeapAlloc { SwiftHeap | CleanHeap }` produced; on any other live
//! allocation (a `CMalloc` or `RustHeap` cell among them) each is undefined
//! behaviour. Lean gives a non-RC `HeapAlloc` cell `owned` permission and
//! `requireArcRef` refuses the three ops on it; trust-ir's
//! `SPEC_RATIFICATIONS.md` §10 says the pinned RC runtime "counts no Rust
//! allocation". trust-ir's reference interpreter takes the same origin check
//! since `25624afd` (at this crate's pin): its `arc_allocation_mut` /
//! `is_unique` refuse the three ops on a non-RC allocation as
//! `UndefinedBehavior` naming the rule ("not a reference-counted cell"), so
//! [`interpret_as_compiled`] refuses every row of the corpus as compiled.
//! This backend refuses `SwiftHeap`/`CleanHeap` cells, so
//! the module it compiles drives the ops on malloc'd cells. The NATIVE run is
//! therefore an execution of an undefined program against the C driver's
//! side-table model of the triple below, not against the pinned Clean
//! runtime: it tests the backend's LOWERING of the three ops (the call, its
//! argument, the narrow result, their order against loads and frees). It is
//! not evidence that the program is defined.
//!
//! What is compared with what:
//!
//! * Every corpus function returns its `IsUnique` answers (one `Bool`, or the
//!   answers packed into bits with the cell's payload above them).
//! * The oracle is the trust-ir reference interpreter run on
//!   [`oracle_twin`]: the same bodies with every `CMalloc`/`RustHeap`
//!   `HeapAlloc` rewritten to `CleanHeap`, the origin whose cells the ops are
//!   defined on, and the release bodies of [`with_release_bodies`]. A fresh
//!   `CleanHeap` cell has count 1 and the `Release` that takes it to 0 frees
//!   it, so the twin's return values are an independent oracle for the
//!   native results, pinned to the closed forms in [`ORACLE`]. Only the heap
//!   the cells come from differs from the compiled module, whose own runs
//!   the interpreter refuses ([`interpret_as_compiled`]).
//! * `arc_dealloc_at_one` has no oracle value: in the twin its cells are
//!   `CleanHeap` and the release bodies free them with `Dealloc`, which
//!   trust-ir refuses (a reference-counted cell is released only by the
//!   `Release` that takes its count to zero). It is an [`INTERPRETER_UB`]
//!   row; the driver prints no result for it and checks its closed form and
//!   allocator balance natively.
//! * Compiled code writes no header: a `CMalloc`/`RustHeap` `HeapAlloc` is a
//!   plain `malloc(size)`/`__rust_alloc(size, align)` call. The C driver is
//!   the counting runtime: it keeps a side table keyed by pointer, seeded
//!   with count 1 when `--wrap=malloc` or its `__rust_alloc` sees the
//!   allocation, implements exactly the declared triple over that table, and
//!   frees the cell when `clean_dec` reaches zero. Per-step counts, the
//!   free at zero and the balance of every call are DRIVER observations,
//!   checked against the constant traces in the driver; the interpreter does
//!   not expose its allocation table, so they are not interpreter values.
//! * `clean_is_exclusive` sets bits 8-63 of its result register (AAPCS64
//!   leaves them unspecified for a `uint8_t` result), so a consumer that
//!   reads more than the byte fails the comparison.
//!
//! Two functions are negative controls mirroring the heap corpus: a retain
//! without its release (the driver must observe the live cell at count 2)
//! and a conditional release past zero (the driver must observe the unknown
//! pointer and not forward it; the interpreter refuses the same run of the
//! twin as undefined behaviour). The C driver is a stand-in for, not, the
//! Clean runtime (whose Perceus cells come from `CleanHeap`, which stays
//! refused for codegen): the correctness of the triple rests on this driver,
//! not on a proof. Execution evidence, not proof.
#![allow(dead_code)]

use trust_ir::inst::AllocOrigin;
use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::{BinOp, CastOp, Endianness, ICmpOp, Module, StructPassingPolicy, TargetInfo, Ty};
use trust_ir_build::{FunctionBuilder, ModuleBuilder, validate_module};

/// Exact last line of the driver's output for a complete, successful run.
pub const EXPECTED_PASS: &str = "PASS 95 arc checks";

/// `(symbol, direct call sites)` the corpus lowers to at every opt level.
pub const CALL_SITES: &[(&str, usize)] = &[
    ("clean_inc", 7),
    ("clean_dec", 10),
    ("clean_is_exclusive", 12),
    ("malloc", 6),
    ("free", 1),
    ("__rust_alloc", 1),
    ("__rust_dealloc", 1),
];

/// The RC-runtime entry points, the subset of [`CALL_SITES`] the ARC ops
/// lower to.
pub const RC_TRIPLE: [&str; 3] = ["clean_inc", "clean_dec", "clean_is_exclusive"];

/// `(function, arguments, closed form)` for every call the driver prints as
/// `function(arguments)=value` and the reference interpreter replays on the
/// [`oracle_twin`].
pub const ORACLE: &[(&str, &[u64], u64)] = &[
    // IsUnique answers 1,0,0,0,1 in bits 0-4, the payload from bit 5.
    ("arc_share_cycle", &[7], 0b10001 | (7 << 5)),
    ("arc_share_cycle", &[1000], 0b10001 | (1000 << 5)),
    // A Bool: unique exactly when nothing was retained.
    ("arc_is_unique_after", &[0], 1),
    ("arc_is_unique_after", &[1], 0),
    ("arc_is_unique_after", &[3], 0),
    // The answer in bit 0, the payload above it.
    ("arc_branch_share", &[0, 9], 1 | (9 << 1)),
    ("arc_branch_share", &[1, 9], 9 << 1),
    // Negative control: the answer after the unpaired retain (shared).
    ("arc_retain_leak", &[4], 0),
    ("arc_release_past_zero", &[0], 0),
];

/// `(function, arguments, error text)` runs the reference interpreter must
/// refuse as undefined behaviour on the [`oracle_twin`]. The driver prints
/// no result line for them, so the native comparison covers exactly
/// [`ORACLE`].
pub const INTERPRETER_UB: &[(&str, &[u64], &str)] = &[
    // Dealloc of a CleanHeap cell: the twin's release bodies free each cell
    // with `Dealloc`, and a reference-counted cell is released only by the
    // `Release` that takes its count to zero. The driver still checks the
    // closed form natively: answers 0,1 (Rust cell) and 0,1 (libc cell) in
    // bits 0-3, then the sum of the two payloads (x and x + 1) above them.
    ("arc_dealloc_at_one", &[5], "Dealloc of a CleanHeap cell"),
    // The second release of a cell already released to zero.
    (
        "arc_release_past_zero",
        &[1],
        "Release: pointer references a freed allocation",
    ),
];

/// Which RC-runtime declarations a module carries.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RcRuntime {
    /// The exact Clean triple as bodyless externals.
    CleanTriple,
    /// No RC runtime at all.
    Missing,
    /// `clean_inc` and `clean_dec` only.
    Partial,
    /// `clean_is_exclusive(ptr) -> bool` instead of `-> u8`.
    ExclusiveReturnsBool,
    /// `clean_inc(u64)` instead of `clean_inc(ptr)`.
    IncTakesInteger,
    /// `clean_inc` defined in the module (a body, not an import).
    IncDefinedHere,
}

impl RcRuntime {
    /// Every declaration set that is not the exact Clean triple.
    pub const NOT_THE_TRIPLE: [RcRuntime; 5] = [
        RcRuntime::Missing,
        RcRuntime::Partial,
        RcRuntime::ExclusiveReturnsBool,
        RcRuntime::IncTakesInteger,
        RcRuntime::IncDefinedHere,
    ];

    /// The pinned trust-ir validator's own refusal of a mis-declared RC
    /// entry point (its `TRUSTED_RC_RUNTIMES` row), or `None` when the module
    /// validates. The backend's refusal is checked separately: `compile`
    /// does not rely on this verdict.
    pub fn validator_refusal(self) -> Option<&'static str> {
        match self {
            RcRuntime::CleanTriple | RcRuntime::Missing | RcRuntime::Partial => None,
            RcRuntime::ExclusiveReturnsBool | RcRuntime::IncTakesInteger => {
                Some("RcEntryPointSignatureMismatch")
            }
            RcRuntime::IncDefinedHere => Some("RcEntryPointDefinedLocally"),
        }
    }
}

fn target(triple: &str) -> TargetInfo {
    TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

/// Declare `runtime`'s RC entry points in `m`.
fn declare_rc_runtime(m: &mut ModuleBuilder, runtime: RcRuntime) {
    let rc_void = m.add_func_type(vec![Ty::Ptr], vec![]);
    let rc_flag = m.add_func_type(vec![Ty::Ptr], vec![Ty::U8]);
    match runtime {
        RcRuntime::Missing => {}
        RcRuntime::CleanTriple | RcRuntime::Partial => {
            m.declare_function("clean_inc", rc_void);
            m.declare_function("clean_dec", rc_void);
            if runtime == RcRuntime::CleanTriple {
                m.declare_function("clean_is_exclusive", rc_flag);
            }
        }
        RcRuntime::ExclusiveReturnsBool => {
            let rc_bool = m.add_func_type(vec![Ty::Ptr], vec![Ty::Bool]);
            m.declare_function("clean_inc", rc_void);
            m.declare_function("clean_dec", rc_void);
            m.declare_function("clean_is_exclusive", rc_bool);
        }
        RcRuntime::IncTakesInteger => {
            let rc_int = m.add_func_type(vec![Ty::U64], vec![]);
            m.declare_function("clean_inc", rc_int);
            m.declare_function("clean_dec", rc_void);
            m.declare_function("clean_is_exclusive", rc_flag);
        }
        RcRuntime::IncDefinedHere => {
            let mut f = m.function("clean_inc", rc_void);
            let entry = f.create_block();
            f.add_block_param(entry, Ty::Ptr);
            f.switch_to_block(entry);
            f.ret(vec![]);
            f.build();
            m.declare_function("clean_dec", rc_void);
            m.declare_function("clean_is_exclusive", rc_flag);
        }
    }
}

/// `acc | (zext(flag) << shift)`.
fn or_bit(
    f: &mut FunctionBuilder<'_>,
    acc: trust_ir::ValueId,
    flag: trust_ir::ValueId,
    shift: i128,
) -> trust_ir::ValueId {
    let wide = f.cast(CastOp::ZExt, Ty::Bool, Ty::U64, flag);
    let amount = f.iconst(Ty::U64, shift);
    let shifted = f.binop(BinOp::Shl, Ty::U64, wide, amount);
    f.binop(BinOp::Or, Ty::U64, acc, shifted)
}

/// The positive corpus and its two negative controls, with the exact Clean
/// triple declared.
pub fn corpus(triple: &str) -> Module {
    corpus_with(triple, RcRuntime::CleanTriple)
}

/// The same function bodies with `runtime`'s declarations. Only
/// [`RcRuntime::CleanTriple`] lowers; every other set must be refused.
pub fn corpus_with(triple: &str, runtime: RcRuntime) -> Module {
    let mut m = ModuleBuilder::new_with_target_info("arc_ops", target(triple));
    declare_rc_runtime(&mut m, runtime);
    let unary = m.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let binary = m.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let predicate = m.add_func_type(vec![Ty::U64], vec![Ty::Bool]);
    let rust_dealloc_ty = m.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::U64], vec![]);
    let free_ty = m.add_func_type(vec![Ty::Ptr], vec![]);
    let rust_dealloc = m.declare_function(RUST_DEALLOC, rust_dealloc_ty);
    let free = m.declare_function(LIBC_FREE, free_ty);

    // arc_share_cycle(x): one libc cell holding x goes unique -> shared
    // (count 2, then 3) -> unique again, and its last release frees it.
    {
        let mut f = m.function("arc_share_cycle", unary);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let cell = f.heap_alloc(Ty::U64, None, None, AllocOrigin::CMalloc);
        f.store(Ty::U64, cell, x);
        let zero = f.iconst(Ty::U64, 0);
        let q0 = f.is_unique(cell);
        let bits = or_bit(&mut f, zero, q0, 0);
        f.retain(cell);
        let q1 = f.is_unique(cell);
        let bits = or_bit(&mut f, bits, q1, 1);
        f.retain(cell);
        let q2 = f.is_unique(cell);
        let bits = or_bit(&mut f, bits, q2, 2);
        f.release(cell);
        let q3 = f.is_unique(cell);
        let bits = or_bit(&mut f, bits, q3, 3);
        f.release(cell);
        let q4 = f.is_unique(cell);
        let bits = or_bit(&mut f, bits, q4, 4);
        let payload = f.load(Ty::U64, cell);
        f.release(cell);
        let five = f.iconst(Ty::U64, 5);
        let high = f.binop(BinOp::Shl, Ty::U64, payload, five);
        let result = f.binop(BinOp::Or, Ty::U64, bits, high);
        f.ret(vec![result]);
        f.build();
    }

    // arc_dealloc_at_one(x): a Rust cell (x) and a libc cell (x + 1) are
    // each retained, released back to one and then freed by a call to
    // __rust_dealloc / free, not by the RC runtime.
    {
        let mut f = m.function("arc_dealloc_at_one", unary);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let rust = f.heap_alloc(Ty::U64, None, None, AllocOrigin::RustHeap);
        let libc = f.heap_alloc(Ty::U64, None, None, AllocOrigin::CMalloc);
        f.store(Ty::U64, rust, x);
        let one = f.iconst(Ty::U64, 1);
        let next = f.binop(BinOp::Add, Ty::U64, x, one);
        f.store(Ty::U64, libc, next);
        f.retain(rust);
        f.retain(libc);
        let zero = f.iconst(Ty::U64, 0);
        let q0 = f.is_unique(rust);
        let bits = or_bit(&mut f, zero, q0, 0);
        f.release(rust);
        let q1 = f.is_unique(rust);
        let bits = or_bit(&mut f, bits, q1, 1);
        let q2 = f.is_unique(libc);
        let bits = or_bit(&mut f, bits, q2, 2);
        f.release(libc);
        let q3 = f.is_unique(libc);
        let bits = or_bit(&mut f, bits, q3, 3);
        let a = f.load(Ty::U64, rust);
        let b = f.load(Ty::U64, libc);
        let sum = f.binop(BinOp::Add, Ty::U64, a, b);
        let size = f.iconst(Ty::U64, 8);
        let align = f.iconst(Ty::U64, 8);
        f.call_void(rust_dealloc, vec![rust, size, align]);
        f.call_void(free, vec![libc]);
        let four = f.iconst(Ty::U64, 4);
        let high = f.binop(BinOp::Shl, Ty::U64, sum, four);
        let result = f.binop(BinOp::Or, Ty::U64, bits, high);
        f.ret(vec![result]);
        f.build();
    }

    // arc_is_unique_after(n): retain a libc cell n times in a loop, answer
    // IsUnique as the Bool result, then release it n + 1 times in a second
    // loop (the last release frees it).
    {
        let mut f = m.function("arc_is_unique_after", predicate);
        let entry = f.create_block();
        let share = f.create_block();
        let share_body = f.create_block();
        let answer = f.create_block();
        let drop_loop = f.create_block();
        let drop_body = f.create_block();
        let done = f.create_block();
        let n = f.add_block_param(entry, Ty::U64);
        let i = f.add_block_param(share, Ty::U64);
        let unique = f.add_block_param(drop_loop, Ty::Bool);
        let j = f.add_block_param(drop_loop, Ty::U64);
        let result = f.add_block_param(done, Ty::Bool);

        f.switch_to_block(entry);
        let cell = f.heap_alloc(Ty::U64, None, None, AllocOrigin::CMalloc);
        let zero = f.iconst(Ty::U64, 0);
        f.br(share, vec![zero]);

        f.switch_to_block(share);
        let more = f.icmp(ICmpOp::Ult, Ty::U64, i, n);
        f.condbr(more, share_body, vec![], answer, vec![]);

        f.switch_to_block(share_body);
        f.retain(cell);
        let one = f.iconst(Ty::U64, 1);
        let next = f.binop(BinOp::Add, Ty::U64, i, one);
        f.br(share, vec![next]);

        f.switch_to_block(answer);
        let q = f.is_unique(cell);
        f.br(drop_loop, vec![q, zero]);

        f.switch_to_block(drop_loop);
        let more = f.icmp(ICmpOp::Ule, Ty::U64, j, n);
        f.condbr(more, drop_body, vec![], done, vec![unique]);

        f.switch_to_block(drop_body);
        f.release(cell);
        let one = f.iconst(Ty::U64, 1);
        let next = f.binop(BinOp::Add, Ty::U64, j, one);
        f.br(drop_loop, vec![unique, next]);

        f.switch_to_block(done);
        f.ret(vec![result]);
        f.build();
    }

    // arc_branch_share(c, x): the libc cell is retained only on the c != 0
    // path; the join answers IsUnique and reads x, the matching release
    // happens on the same condition, and the final release frees it.
    {
        let mut f = m.function("arc_branch_share", binary);
        let entry = f.create_block();
        let share = f.create_block();
        let join = f.create_block();
        let unshare = f.create_block();
        let done = f.create_block();
        let c = f.add_block_param(entry, Ty::U64);
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let cell = f.heap_alloc(Ty::U64, None, None, AllocOrigin::CMalloc);
        f.store(Ty::U64, cell, x);
        let zero = f.iconst(Ty::U64, 0);
        let cond = f.icmp(ICmpOp::Ne, Ty::U64, c, zero);
        f.condbr(cond, share, vec![], join, vec![]);

        f.switch_to_block(share);
        f.retain(cell);
        f.br(join, vec![]);

        f.switch_to_block(join);
        let q = f.is_unique(cell);
        let payload = f.load(Ty::U64, cell);
        f.condbr(cond, unshare, vec![], done, vec![]);

        f.switch_to_block(unshare);
        f.release(cell);
        f.br(done, vec![]);

        f.switch_to_block(done);
        f.release(cell);
        let bits = or_bit(&mut f, zero, q, 0);
        let one = f.iconst(Ty::U64, 1);
        let high = f.binop(BinOp::Shl, Ty::U64, payload, one);
        let result = f.binop(BinOp::Or, Ty::U64, bits, high);
        f.ret(vec![result]);
        f.build();
    }

    // Negative control: arc_retain_leak(x) retains its libc cell and never
    // releases it, so the driver must observe one live cell at count 2.
    {
        let mut f = m.function("arc_retain_leak", unary);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let cell = f.heap_alloc(Ty::U64, None, None, AllocOrigin::CMalloc);
        f.store(Ty::U64, cell, x);
        f.retain(cell);
        let q = f.is_unique(cell);
        let zero = f.iconst(Ty::U64, 0);
        let result = or_bit(&mut f, zero, q, 0);
        f.ret(vec![result]);
        f.build();
    }

    // Negative control: arc_release_past_zero(c) releases its libc cell to
    // zero, and once more when c != 0. The driver must observe the second
    // release of a pointer it no longer tracks and not forward it; the
    // reference interpreter refuses that run.
    {
        let mut f = m.function("arc_release_past_zero", unary);
        let entry = f.create_block();
        let again = f.create_block();
        let done = f.create_block();
        let c = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let cell = f.heap_alloc(Ty::U64, None, None, AllocOrigin::CMalloc);
        f.release(cell);
        let zero = f.iconst(Ty::U64, 0);
        let cond = f.icmp(ICmpOp::Ne, Ty::U64, c, zero);
        f.condbr(cond, again, vec![], done, vec![]);
        f.switch_to_block(again);
        f.release(cell);
        f.br(done, vec![]);
        f.switch_to_block(done);
        f.ret(vec![zero]);
        f.build();
    }

    let module = m.build().expect("ModuleBuilder::build: test fixture");
    let errors = format!("{:?}", validate_module(&module));
    match runtime.validator_refusal() {
        None => assert_eq!(errors, "[]", "{runtime:?}"),
        Some(name) => assert!(errors.contains(name), "{runtime:?}: {errors}"),
    }
    module
}

/// A module whose only function takes a `Ty::Rc` parameter, which the
/// backend must refuse: reference-counted ownership has no modelled ABI.
pub fn rc_type_module(triple: &str) -> Module {
    let mut m = ModuleBuilder::new_with_target_info("arc_rc_type", target(triple));
    declare_rc_runtime(&mut m, RcRuntime::CleanTriple);
    let sig = m.add_func_type(vec![Ty::Rc(Box::new(Ty::U64))], vec![]);
    let mut f = m.function("arc_rc_param", sig);
    let entry = f.create_block();
    f.add_block_param(entry, Ty::Rc(Box::new(Ty::U64)));
    f.switch_to_block(entry);
    f.ret(vec![]);
    f.build();
    m.build().expect("ModuleBuilder::build: test fixture")
}

/// A module that allocates a `origin` cell and drives the ARC ops on it,
/// with the Clean triple declared; `SwiftHeap`/`CleanHeap` must be refused.
pub fn foreign_heap_module(triple: &str, origin: AllocOrigin) -> Module {
    let mut m = ModuleBuilder::new_with_target_info("arc_foreign_heap", target(triple));
    declare_rc_runtime(&mut m, RcRuntime::CleanTriple);
    let sig = m.add_func_type(vec![], vec![Ty::Bool]);
    let mut f = m.function("arc_foreign_cell", sig);
    let entry = f.create_block();
    f.switch_to_block(entry);
    let cell = f.heap_alloc(Ty::U64, None, None, origin);
    f.retain(cell);
    let q = f.is_unique(cell);
    f.release(cell);
    f.release(cell);
    f.ret(vec![q]);
    f.build();
    let module = m.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), []);
    module
}

/// A module that frees a cell allocated by its caller (`Inst::Dealloc` of a
/// parameter): refused, as every `Inst::Dealloc` is (G18-1).
pub fn cross_function_dealloc_module(triple: &str) -> Module {
    let mut m = ModuleBuilder::new_with_target_info("arc_cross_dealloc", target(triple));
    declare_rc_runtime(&mut m, RcRuntime::CleanTriple);
    let sig = m.add_func_type(vec![Ty::Ptr], vec![]);
    let mut f = m.function("arc_free_callers_cell", sig);
    let entry = f.create_block();
    let cell = f.add_block_param(entry, Ty::Ptr);
    f.switch_to_block(entry);
    f.release(cell);
    f.dealloc(cell);
    f.ret(vec![]);
    f.build();
    let module = m.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), []);
    module
}

/// The Rust allocator's release entry the corpus calls.
pub const RUST_DEALLOC: &str = "__rust_dealloc";
/// The libc release entry the corpus calls.
pub const LIBC_FREE: &str = "free";

/// The ORACLE's copy of `module`: the bodyless `__rust_dealloc` and `free`
/// declarations are given the bodies `__rust_dealloc(p, size, align) {
/// Dealloc p }` and `free(p) { Dealloc p }`, so the reference interpreter
/// executes each release in-format (it releases the region, so a double
/// free or a use after free still faults) instead of refusing the call as
/// one no host model serves. The same mapping `trust-ir run` makes for the
/// Rust frontend's mangled `__rust_dealloc` shim (`BuiltinKind::Dealloc`);
/// like it, the size/align arguments are not checked here — the C driver
/// checks them natively. Only the oracle sees these bodies; the compiled
/// module keeps the declarations. Applied to the [`oracle_twin`], each
/// `Dealloc` meets a `CleanHeap` cell, which trust-ir refuses as undefined
/// behaviour, so the one corpus function that calls them,
/// `arc_dealloc_at_one`, is an [`INTERPRETER_UB`] row, refused by name
/// rather than as a call no host model serves.
pub fn with_release_bodies(module: &Module) -> Module {
    use trust_ir::{Block, BlockId, Inst, InstrNode, ValueId};
    let mut oracle = module.clone();
    for function in &mut oracle.functions {
        let params: &[Ty] = match function.name.as_str() {
            RUST_DEALLOC => &[Ty::Ptr, Ty::U64, Ty::U64],
            LIBC_FREE => &[Ty::Ptr],
            _ => continue,
        };
        assert!(
            function.blocks.is_empty(),
            "@{} is a declaration",
            function.name
        );
        let entry = BlockId::new(0);
        let mut block = Block::new(entry);
        block.params = params
            .iter()
            .enumerate()
            .map(|(index, ty)| (ValueId::new(index as u32), ty.clone()))
            .collect();
        block.body.push(InstrNode::new(Inst::Dealloc {
            ptr: ValueId::new(0),
        }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        function.entry = entry;
        function.blocks.push(block);
    }
    oracle
}

/// The ORACLE's twin of `module`: every `HeapAlloc` of the `CMalloc` or
/// `RustHeap` origin becomes `CleanHeap`, and nothing else changes. The ARC
/// ops are defined only on a reference-counted cell (see the module docs), so
/// the corpus as compiled is undefined in trust-ir while its twin is not;
/// the backend refuses `CleanHeap` cells, so only the oracle sees the twin.
pub fn oracle_twin(module: &Module) -> Module {
    use trust_ir::Inst;
    let mut twin = module.clone();
    for function in &mut twin.functions {
        for block in &mut function.blocks {
            for node in &mut block.body {
                if let Inst::HeapAlloc { origin, .. } = &mut node.inst
                    && matches!(origin, AllocOrigin::CMalloc | AllocOrigin::RustHeap)
                {
                    *origin = AllocOrigin::CleanHeap;
                }
            }
        }
    }
    twin
}

/// The origin of every `HeapAlloc` in `module`, in function, block and
/// instruction order.
pub fn heap_origins(module: &Module) -> Vec<AllocOrigin> {
    use trust_ir::Inst;
    module
        .functions
        .iter()
        .flat_map(|function| &function.blocks)
        .flat_map(|block| &block.body)
        .filter_map(|node| match node.inst {
            Inst::HeapAlloc { origin, .. } => Some(origin),
            _ => None,
        })
        .collect()
}

/// Run `name(args)` under the trust-ir reference interpreter over the
/// oracle's copy of `module`, `with_release_bodies(oracle_twin(module))`
/// (no host model: the module never calls the triple, it executes the ARC
/// ops in-format).
pub fn interpret(module: &Module, name: &str, args: &[u64]) -> Result<u64, String> {
    run(&with_release_bodies(&oracle_twin(module)), name, args)
}

/// Run `name(args)` under the trust-ir reference interpreter over the corpus
/// AS COMPILED: `with_release_bodies(module)` with no twin, so every cell
/// keeps the `CMalloc`/`RustHeap` origin the backend compiles and the ARC
/// ops meet a cell that is not reference-counted. The pinned interpreter
/// refuses each such op as undefined behaviour (trust-ir `25624afd`), which
/// is why [`ORACLE`] is replayed on the twin. The two runs differ only in
/// the origin of the cells.
pub fn interpret_as_compiled(module: &Module, name: &str, args: &[u64]) -> Result<u64, String> {
    run(&with_release_bodies(module), name, args)
}

fn run(module: &Module, name: &str, args: &[u64]) -> Result<u64, String> {
    let function = module
        .function_by_name(name)
        .unwrap_or_else(|| panic!("corpus defines @{name}"));
    let args = args
        .iter()
        .map(|arg| InterpretValue::int(Ty::U64, i128::from(*arg)).expect("u64 argument"));
    let outcome = Interpreter::with_module(module)
        .execute_function(function, args)
        .map_err(|error| format!("{error:?}"))?;
    assert_eq!(outcome.host_calls, 0, "@{name}: the run must be in-format");
    let [ret] = outcome.returns.as_slice() else {
        panic!("@{name}: expected one result, got {:?}", outcome.returns)
    };
    match &ret.kind {
        InterpretValueKind::Int(int) => Ok(u64::try_from(int.as_unsigned()).expect("u64 result")),
        InterpretValueKind::Bool(flag) => Ok(u64::from(*flag)),
        other => panic!("@{name}: scalar result expected, got {other:?}"),
    }
}

/// `function(a,b)` as the driver prints it.
pub fn call_key(name: &str, args: &[u64]) -> String {
    let args: Vec<String> = args.iter().map(u64::to_string).collect();
    format!("{name}({})", args.join(","))
}

/// The C driver and counting RC runtime (Linux: the link wraps the module's
/// `malloc` and `free` references with `-Wl,--wrap=malloc,--wrap=free`).
/// Compile with `-DCG_INVERT_EXCLUSIVE` or `-DCG_NEVER_FREE` for the harness
/// self-checks: a runtime answering the wrong polarity, or one that never
/// frees at zero, must make the driver fail.
pub const DRIVER: &str = r#"
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* The module's malloc/free references are wrapped; the driver's own
   releases go to the real symbols. */
#define CG_MALLOC __wrap_malloc
#define CG_FREE __wrap_free
extern void *__real_malloc(size_t);
extern void __real_free(void *);

enum { RUST = 'r', LIBC = 'c' };
/* The side table: compiled code writes no header, so the count of each
   live cell is kept here, keyed by the pointer the allocator returned. */
struct cell { void *p; size_t size, align; int kind; uint64_t count; };
static struct cell table[16];
static unsigned live_count, armed;
static unsigned c_allocs, rust_allocs, frees_at_zero, rust_deallocs, c_frees, errors;
/* Per-call step trace: <kind><op><count or answer>[F], or ?<op> for a
   pointer the table does not hold. */
static char trace[512];
static size_t trace_len;

static void note(int kind, char op, uint64_t value, int freed) {
  int n = kind == '?'
    ? snprintf(trace + trace_len, sizeof trace - trace_len, "%s?%c", trace_len ? " " : "", op)
    : snprintf(trace + trace_len, sizeof trace - trace_len, "%s%c%c%llu%s", trace_len ? " " : "",
               kind, op, (unsigned long long)value, freed ? "F" : "");
  if (n < 0 || (size_t)n >= sizeof trace - trace_len) { errors++; return; }
  trace_len += (size_t)n;
}
static struct cell *find(void *p) {
  for (unsigned i = 0; i < live_count; i++)
    if (table[i].p == p) return &table[i];
  return 0;
}
/* A new allocation starts uniquely owned: count 1, the interpreter's rule for
   the fresh CleanHeap cell the oracle twin allocates in its place. */
static void track(void *p, size_t size, size_t align, int kind) {
  if (!p || live_count == 16) { errors++; return; }
  table[live_count].p = p; table[live_count].size = size; table[live_count].align = align;
  table[live_count].kind = kind; table[live_count].count = 1;
  live_count++;
}
/* Poison, forget and free a cell: a load the backend moved past its
   release then cannot see the value stored before it. */
static void release_storage(struct cell *c) {
  void *p = c->p;
  memset(p, 0xa5, c->size);
  *c = table[--live_count];
  __real_free(p);
}

void *__rust_alloc(size_t size, size_t align) {
  void *p = 0;
  if (posix_memalign(&p, align < 16 ? 16 : align, size ? size : 1)) p = 0;
  rust_allocs++;
  if (!armed) errors++;
  track(p, size, align, RUST);
  return p;
}
/* The module's __rust_dealloc call on a Rust cell: exact layout, and only
   while uniquely owned. */
void __rust_dealloc(void *p, size_t size, size_t align) {
  struct cell *c = find(p);
  rust_deallocs++;
  if (!c || c->kind != RUST || c->size != size || c->align != align || c->count != 1) { errors++; return; }
  release_storage(c);
}
void *CG_MALLOC(size_t n) {
  void *p = __real_malloc(n);
  if (armed) { c_allocs++; track(p, n, 0, LIBC); }
  return p;
}
/* The module's free call on a libc cell: only while uniquely owned. */
void CG_FREE(void *p) {
  struct cell *c;
  if (!armed) { __real_free(p); return; }
  c_frees++;
  c = find(p);
  if (!c || c->kind != LIBC || c->count != 1) { errors++; return; }
  release_storage(c);
}

/* clean_inc(ptr) -> (): count + 1. */
void clean_inc(void *p) {
  struct cell *c = find(p);
  if (!c || c->count == 0) { errors++; note('?', 'I', 0, 0); return; }
  c->count++;
  note(c->kind, 'I', c->count, 0);
}
/* clean_dec(ptr) -> (): count - 1, freeing the cell at zero. A release of a
   pointer the table does not hold (past zero, or foreign) is an error and is
   not forwarded to the allocator. */
void clean_dec(void *p) {
  struct cell *c = find(p);
  int kind;
  if (!c || c->count == 0) { errors++; note('?', 'D', 0, 0); return; }
  kind = c->kind;
  c->count--;
#ifndef CG_NEVER_FREE
  if (c->count == 0) {
    frees_at_zero++;
    release_storage(c);
    note(kind, 'D', 0, 1);
    return;
  }
#endif
  note(kind, 'D', c->count, 0);
}
/* The answer of clean_is_exclusive: count == 1, the IsUnique predicate. */
uint8_t cg_exclusive_answer(void *p) {
  struct cell *c = find(p);
  uint8_t unique;
  if (!c || c->count == 0) { errors++; note('?', 'Q', 0, 0); return 0; }
  unique = c->count == 1;
#ifdef CG_INVERT_EXCLUSIVE
  unique = !unique;
#endif
  note(c->kind, 'Q', unique, 0);
  return unique;
}
/* clean_is_exclusive(ptr) -> u8. AAPCS64 leaves bits 8-63 of a narrow
   result unspecified; this entry sets them (w0 = 0xa5a5ff00 | answer, and
   the upper word of x0), so a caller that reads more than the byte fails. */
__asm__(
  ".text\n"
  ".globl clean_is_exclusive\n"
  ".type clean_is_exclusive, %function\n"
  ".p2align 2\n"
  "clean_is_exclusive:\n"
  "  stp x29, x30, [sp, #-16]!\n"
  "  mov x29, sp\n"
  "  bl cg_exclusive_answer\n"
  "  and w0, w0, #0xff\n"
  "  orr w0, w0, #0xff00\n"
  "  movk w0, #0xa5a5, lsl #16\n"
  "  orr x0, x0, #0xffffffff00000000\n"
  "  ldp x29, x30, [sp], #16\n"
  "  ret\n"
  ".size clean_is_exclusive, .-clean_is_exclusive\n");

extern uint64_t arc_share_cycle(uint64_t), arc_dealloc_at_one(uint64_t);
extern uint8_t arc_is_unique_after(uint64_t);
extern uint64_t arc_branch_share(uint64_t, uint64_t);
extern uint64_t arc_retain_leak(uint64_t), arc_release_past_zero(uint64_t);

static unsigned checks, failures;
static char key[64];
static void arm(void) {
  c_allocs = rust_allocs = frees_at_zero = rust_deallocs = c_frees = errors = 0;
  trace_len = 0; trace[0] = 0;
  armed = 1;
}
static void check(const char *what, unsigned line, uint64_t actual, uint64_t expected) {
  checks++;
  if (actual != expected) {
    failures++;
    printf("FAIL %s %s (line %u): %llu != %llu\n", key, what, line,
           (unsigned long long)actual, (unsigned long long)expected);
  }
}
#define EQ(actual, expected) check(#actual, __LINE__, (uint64_t)(actual), (uint64_t)(expected))
/* The step trace of the last call must equal the constant expectation. */
static void steps(unsigned line, const char *expected) {
  checks++;
  printf("trace %s: %s\n", key, trace);
  if (strcmp(trace, expected) != 0) {
    failures++;
    printf("FAIL %s trace (line %u): \"%s\" != \"%s\"\n", key, line, trace, expected);
  }
}
#define STEPS(expected) steps(__LINE__, expected)
/* The call's result, printed for the interpreter comparison. */
static void result(uint64_t value) { printf("%s=%llu\n", key, (unsigned long long)value); }
/* A balanced call: every cell was freed exactly once, by the runtime at
   zero or by a release call, nothing is live and nothing was refused. */
static void balanced(unsigned libc, unsigned rust, unsigned at_zero, unsigned dealloc_rust, unsigned dealloc_libc) {
  EQ(c_allocs, libc); EQ(rust_allocs, rust); EQ(frees_at_zero, at_zero);
  EQ(rust_deallocs, dealloc_rust); EQ(c_frees, dealloc_libc);
  EQ(errors, 0); EQ(live_count, 0);
}

int main(void) {
  const uint64_t shares[] = {7, 1000};
  for (unsigned k = 0; k < 2; k++) {
    uint64_t x = shares[k];
    snprintf(key, sizeof key, "arc_share_cycle(%llu)", (unsigned long long)x);
    arm(); uint64_t r = arc_share_cycle(x); armed = 0;
    result(r); EQ(r, 17 | (x << 5));
    STEPS("cQ1 cI2 cQ0 cI3 cQ0 cD2 cQ0 cD1 cQ1 cD0F");
    balanced(1, 0, 1, 0, 0);
  }

  /* No result line: the interpreter refuses this run of the oracle twin as
     undefined behaviour (Dealloc of a CleanHeap cell); the closed form is
     checked here. */
  snprintf(key, sizeof key, "arc_dealloc_at_one(5)");
  arm(); uint64_t r = arc_dealloc_at_one(5); armed = 0;
  EQ(r, 10 | (11 << 4));
  STEPS("rI2 cI2 rQ0 rD1 rQ1 cQ0 cD1 cQ1");
  balanced(1, 1, 0, 1, 1);

  const uint64_t counts[] = {0, 1, 3};
  const char *const traces[] = {
    "cQ1 cD0F",
    "cI2 cQ0 cD1 cD0F",
    "cI2 cI3 cI4 cQ0 cD3 cD2 cD1 cD0F",
  };
  for (unsigned k = 0; k < 3; k++) {
    uint64_t n = counts[k];
    snprintf(key, sizeof key, "arc_is_unique_after(%llu)", (unsigned long long)n);
    arm(); uint8_t u = arc_is_unique_after(n); armed = 0;
    result(u); EQ(u, n == 0);
    STEPS(traces[k]);
    balanced(1, 0, 1, 0, 0);
  }

  for (uint64_t c = 0; c < 2; c++) {
    snprintf(key, sizeof key, "arc_branch_share(%llu,9)", (unsigned long long)c);
    arm(); r = arc_branch_share(c, 9); armed = 0;
    result(r); EQ(r, (c ? 0 : 1) | (9 << 1));
    STEPS(c ? "cI2 cQ0 cD1 cD0F" : "cQ1 cD0F");
    balanced(1, 0, 1, 0, 0);
  }

  /* Negative control: the unpaired retain must leave one live cell at count
     2 holding the payload; the driver then frees it itself. */
  snprintf(key, sizeof key, "arc_retain_leak(4)");
  arm(); r = arc_retain_leak(4); armed = 0;
  result(r); EQ(r, 0);
  STEPS("cI2 cQ0");
  EQ(c_allocs, 1); EQ(frees_at_zero, 0); EQ(errors, 0); EQ(live_count, 1);
  EQ(table[0].count, 2); EQ(*(uint64_t *)table[0].p, 4);
  if (live_count == 1) release_storage(&table[0]);
  EQ(live_count, 0);

  snprintf(key, sizeof key, "arc_release_past_zero(0)");
  arm(); r = arc_release_past_zero(0); armed = 0;
  result(r); EQ(r, 0);
  STEPS("cD0F");
  balanced(1, 0, 1, 0, 0);

  /* Negative control: the release past zero must be observed and refused,
     not forwarded to the allocator. No result line: the interpreter refuses
     this run as undefined behaviour. */
  snprintf(key, sizeof key, "arc_release_past_zero(1)");
  arm(); arc_release_past_zero(1); armed = 0;
  STEPS("cD0F ?D");
  EQ(c_allocs, 1); EQ(frees_at_zero, 1); EQ(errors, 1); EQ(live_count, 0);

  if (failures) {
    printf("FAILED %u of %u arc checks\n", failures, checks);
    return 1;
  }
  printf("PASS %u arc checks\n", checks);
  return 0;
}
"#;
