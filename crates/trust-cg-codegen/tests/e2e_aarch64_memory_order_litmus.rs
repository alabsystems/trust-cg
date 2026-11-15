// trust-cg-codegen/tests/e2e_aarch64_memory_order_litmus.rs - native litmus
// tests of trust-cg's C11/Rust -> AArch64 memory-order mapping
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Ledger L03-P3, testing half: a litmus harness on this host for every
//! ordering class trust-cg compiles.
//!
//! Every litmus THREAD BODY is a trust-cg function: all of one thread's
//! accesses and fences for one round, compiled through the real pipeline at
//! O0-O3 (the Darwin AOT profile, LSE and LSE2; the LL/SC variants through the
//! baseline profile), so compiler reordering is under test as well as the
//! selected instructions. `tests/fixtures/memory_order/litmus_driver.c` runs
//! them on 2 or 4 threads for many rounds and reports, per test, how many
//! rounds showed the outcome C11/Rust forbids, with an outcome histogram:
//!
//! * MP (message passing) with release/acquire, SeqCst, release+acquire
//!   fences, AcqRel and SeqCst fences, release/acquire RMWs, a release CAS
//!   read back through an ACQUIRE FAILURE ordering (the lifted CASA), 128-bit
//!   release/acquire, and LL/SC release/acquire RMWs;
//! * SB (store buffering) with SeqCst loads/stores, SeqCst fences, SeqCst
//!   RMWs, SeqCst CAS, SeqCst 128-bit atomics, a mixed 64/128-bit SeqCst pair
//!   and LL/SC SeqCst RMWs;
//! * LB (load buffering) with a RELEASE FENCE AFTER A LOAD paired with an
//!   acquire fence (the shape the pre-L03-P3 `DMB ISHST` release fence
//!   permitted), release/acquire, SeqCst, and RMW and LL/SC acquire/release;
//! * IRIW with SeqCst atomics and with SeqCst fences between the reads;
//! * 2+2W with SeqCst stores and SeqCst fences between the stores.
//!
//! Each of those must show ZERO forbidden outcomes. Fence variants surround
//! the fence with trust-ir volatile accesses, which lower to the plain
//! `LDR`/`STR` LLVM selects for Relaxed atomics; trust-cg's own Relaxed
//! atomics are strengthened to `LDAR`/`STLR`, which would order the accesses
//! without the fence and hide what the fence contributes.
//!
//! Variants whose outcome C11 ALLOWS (SB with release/acquire or release
//! fences, IRIW with acquire loads, 2+2W with release stores) are reported,
//! never asserted. C controls report whether this host produces each weak
//! outcome at all: plain accesses, and inline-assembly replicas of the
//! pre-L03-P3 selections (`DMB ISHST` as the release fence; the SeqCst
//! 128-bit `ldp; dmb ish` load without its entry barrier). The plain
//! message-passing and store-buffering controls must each observe their weak
//! outcome at least once across the run, showing the harness overlaps the
//! threads closely enough for the forbidden lines to discriminate.
//!
//! Measured on this Apple M4 in one run (2026-10-07, O0-O3, load average
//! 30-45): the plain MP control showed its weak outcome in 166,690 of 2^20
//! reads and the plain SB control in 52,185 of 2^20 rounds; plain IRIW and
//! 2+2W showed theirs (218 and 2,650 of 2^18). The replica of the pre-L03-P3
//! SeqCst 128-bit pair showed the SeqCst-forbidden SB outcome 4,501 times in
//! 2^20 rounds (0, 1 and 8,512 in three other runs: the rate varies with
//! load), the fixed trust-cg form never. The load-buffering weak outcome was
//! never observed, by the plain control or by the `DMB ISHST` replica, so the
//! release-fence fix is pinned at the word level by
//! `aarch64_memory_order_obligations.rs`; the LB variants are kept for hosts
//! that do reorder loads with later stores. Testing evidence over finite runs
//! on one host, not a memory-model proof.

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_ir::{
    AtomicRMWOp, BinOp, Block, BlockId, CastOp, Constant, FuncId, FuncTy, Function, Inst,
    InstrNode, Linkage, Module, Ordering, Ty, ValueId,
};

#[path = "common/native_host.rs"]
mod native_host;

const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

// =============================================================================
// trust-ir thread bodies
// =============================================================================

/// How one shared access is performed.
#[derive(Debug, Clone, Copy)]
enum Access {
    /// A trust-ir volatile access: plain `LDR`/`STR`.
    Plain,
    /// An atomic load or store with this ordering.
    Atomic(Ordering),
    /// A store as `swap`, a load as `fetch_add(0)`.
    Rmw(Ordering),
    /// A store as `compare_exchange(r - 1, r)` (the writer owns the location,
    /// so it always succeeds); a load as `compare_exchange(-1, -1)`, which
    /// always FAILS and so reads through the failure ordering.
    Cas(Ordering, Ordering),
    /// A 128-bit atomic load or store (zero-extended value, low half read).
    Wide(Ordering),
}

/// A function under construction: values are numbered after the parameters.
struct Body {
    params: Vec<Ty>,
    insts: Vec<InstrNode>,
    next: u32,
}

impl Body {
    fn new(params: Vec<Ty>) -> Self {
        let next = params.len() as u32;
        Self {
            params,
            insts: Vec::new(),
            next,
        }
    }

    fn param(&self, index: u32) -> ValueId {
        ValueId::new(index)
    }

    fn value(&mut self, inst: Inst) -> ValueId {
        let value = ValueId::new(self.next);
        self.next += 1;
        self.insts.push(InstrNode::new(inst).with_result(value));
        value
    }

    fn pair(&mut self, inst: Inst) -> ValueId {
        let (old, ok) = (ValueId::new(self.next), ValueId::new(self.next + 1));
        self.next += 2;
        self.insts
            .push(InstrNode::new(inst).with_results(vec![old, ok]));
        old
    }

    fn effect(&mut self, inst: Inst) {
        self.insts.push(InstrNode::new(inst));
    }

    fn int(&mut self, value: i128) -> ValueId {
        self.value(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(value),
        })
    }

    fn fence(&mut self, ordering: Option<Ordering>) {
        if let Some(ordering) = ordering {
            self.effect(Inst::Fence { ordering });
        }
    }

    fn store(&mut self, access: Access, ptr: ValueId, value: ValueId) {
        match access {
            Access::Plain => self.effect(Inst::Store {
                ty: Ty::I64,
                ptr,
                value,
                volatile: true,
                align: Some(8),
            }),
            Access::Atomic(ordering) => self.effect(Inst::AtomicStore {
                ty: Ty::I64,
                ptr,
                value,
                ordering,
            }),
            Access::Rmw(ordering) => {
                self.value(Inst::AtomicRMW {
                    op: AtomicRMWOp::Xchg,
                    ty: Ty::I64,
                    ptr,
                    value,
                    ordering,
                });
            }
            Access::Cas(success, failure) => {
                let one = self.int(1);
                let expected = self.value(Inst::BinOp {
                    op: BinOp::Sub,
                    ty: Ty::I64,
                    lhs: value,
                    rhs: one,
                });
                self.pair(Inst::CmpXchg {
                    ty: Ty::I64,
                    ptr,
                    expected,
                    desired: value,
                    success,
                    failure,
                    weak: false,
                });
            }
            Access::Wide(ordering) => {
                let wide = self.value(Inst::Cast {
                    op: CastOp::ZExt,
                    src_ty: Ty::I64,
                    dst_ty: Ty::I128,
                    operand: value,
                });
                self.effect(Inst::AtomicStore {
                    ty: Ty::I128,
                    ptr,
                    value: wide,
                    ordering,
                });
            }
        }
    }

    fn load(&mut self, access: Access, ptr: ValueId) -> ValueId {
        match access {
            Access::Plain => self.value(Inst::Load {
                ty: Ty::I64,
                ptr,
                volatile: true,
                align: Some(8),
            }),
            Access::Atomic(ordering) => self.value(Inst::AtomicLoad {
                ty: Ty::I64,
                ptr,
                ordering,
            }),
            Access::Rmw(ordering) => {
                let zero = self.int(0);
                self.value(Inst::AtomicRMW {
                    op: AtomicRMWOp::Add,
                    ty: Ty::I64,
                    ptr,
                    value: zero,
                    ordering,
                })
            }
            Access::Cas(success, failure) => {
                let never = self.int(-1);
                self.pair(Inst::CmpXchg {
                    ty: Ty::I64,
                    ptr,
                    expected: never,
                    desired: never,
                    success,
                    failure,
                    weak: false,
                })
            }
            Access::Wide(ordering) => {
                let wide = self.value(Inst::AtomicLoad {
                    ty: Ty::I128,
                    ptr,
                    ordering,
                });
                self.value(Inst::Cast {
                    op: CastOp::Trunc,
                    src_ty: Ty::I128,
                    dst_ty: Ty::I64,
                    operand: wide,
                })
            }
        }
    }

    fn finish(mut self, module: &mut Module, name: &str, result: Option<ValueId>) {
        self.insts.push(InstrNode::new(Inst::Return {
            values: result.into_iter().collect(),
        }));
        let sig = module
            .add_func_type(FuncTy {
                params: self.params.clone(),
                returns: if result.is_some() {
                    vec![Ty::I64]
                } else {
                    vec![]
                },
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let id = FuncId::new(module.functions.len() as u32);
        let mut function = Function::new(id, name, sig, BlockId::new(0));
        function.linkage = Linkage::External;
        function.blocks = vec![Block {
            id: BlockId::new(0),
            params: self
                .params
                .into_iter()
                .enumerate()
                .map(|(index, ty)| (ValueId::new(index as u32), ty))
                .collect(),
            body: self.insts,
        }];
        module.functions.push(function);
    }
}

fn ptr() -> Ty {
    Ty::PtrMut(Box::new(Ty::I64))
}

/// SB `(mine, other, r) -> v`: `mine := r; [fence]; v := other`.
fn sb(module: &mut Module, name: &str, store: Access, fence: Option<Ordering>, load: Access) {
    let mut body = Body::new(vec![ptr(), ptr(), Ty::I64]);
    let (mine, other, r) = (body.param(0), body.param(1), body.param(2));
    body.store(store, mine, r);
    body.fence(fence);
    let seen = body.load(load, other);
    body.finish(module, name, Some(seen));
}

/// LB `(read_from, write_to, r) -> v`: `v := read_from; [fence]; write_to := r`.
fn lb(module: &mut Module, name: &str, load: Access, fence: Option<Ordering>, store: Access) {
    let mut body = Body::new(vec![ptr(), ptr(), Ty::I64]);
    let (read_from, write_to, r) = (body.param(0), body.param(1), body.param(2));
    let seen = body.load(load, read_from);
    body.fence(fence);
    body.store(store, write_to, r);
    body.finish(module, name, Some(seen));
}

/// IRIW writer `(p, r)`: `p := r`; reader `(first, second, out) -> a`:
/// `a := first; [fence]; *out := second`.
fn iriw(module: &mut Module, name: &str, write: Access, read: Access, fence: Option<Ordering>) {
    let mut w = Body::new(vec![ptr(), Ty::I64]);
    let (p, r) = (w.param(0), w.param(1));
    w.store(write, p, r);
    w.finish(module, &format!("iriw_{name}_w"), None);

    let mut reader = Body::new(vec![ptr(), ptr(), ptr()]);
    let (first, second, out) = (reader.param(0), reader.param(1), reader.param(2));
    let a = reader.load(read, first);
    reader.fence(fence);
    let b = reader.load(read, second);
    reader.store(Access::Plain, out, b);
    reader.finish(module, &format!("iriw_{name}_r"), Some(a));
}

/// 2+2W `(first, second)`: `first := 1; [fence]; second := 2`.
fn w2(module: &mut Module, name: &str, store: Access, fence: Option<Ordering>) {
    let mut body = Body::new(vec![ptr(), ptr()]);
    let (first, second) = (body.param(0), body.param(1));
    let one = body.int(1);
    let two = body.int(2);
    body.store(store, first, one);
    body.fence(fence);
    body.store(store, second, two);
    body.finish(module, name, None);
}

/// Every thread body the driver links, except the LL/SC ones.
fn litmus_module() -> Module {
    use Access::{Atomic, Cas, Plain, Rmw, Wide};
    use Ordering::{AcqRel, Acquire, Relaxed, Release, SeqCst};
    let mut m = Module::new("memory_order_litmus");
    // Message passing.
    let rel_acq = (Atomic(Release), Atomic(Acquire));
    mp(&mut m, "relacq", rel_acq, (None, None));
    mp(
        &mut m,
        "seqcst",
        (Atomic(SeqCst), Atomic(SeqCst)),
        (None, None),
    );
    mp(
        &mut m,
        "fence",
        (Plain, Plain),
        (Some(Release), Some(Acquire)),
    );
    mp(
        &mut m,
        "fence_acqrel",
        (Plain, Plain),
        (Some(AcqRel), Some(AcqRel)),
    );
    mp(
        &mut m,
        "fence_seqcst",
        (Plain, Plain),
        (Some(SeqCst), Some(SeqCst)),
    );
    mp(&mut m, "rmw", (Rmw(Release), Rmw(Acquire)), (None, None));
    mp(
        &mut m,
        "cas",
        (Cas(Release, Relaxed), Cas(Relaxed, Acquire)),
        (None, None),
    );
    mp(&mut m, "wide", (Wide(Release), Wide(Acquire)), (None, None));
    mp(
        &mut m,
        "relaxed",
        (Atomic(Relaxed), Atomic(Relaxed)),
        (None, None),
    );
    // Store buffering.
    sb(&mut m, "sb_seqcst", Atomic(SeqCst), None, Atomic(SeqCst));
    sb(&mut m, "sb_fence_seqcst", Plain, Some(SeqCst), Plain);
    sb(&mut m, "sb_rmw_seqcst", Rmw(SeqCst), None, Rmw(SeqCst));
    sb(
        &mut m,
        "sb_cas_seqcst",
        Cas(SeqCst, SeqCst),
        None,
        Cas(SeqCst, SeqCst),
    );
    sb(&mut m, "sb_wide_seqcst", Wide(SeqCst), None, Wide(SeqCst));
    sb(
        &mut m,
        "sb_mixed_narrow",
        Atomic(SeqCst),
        None,
        Wide(SeqCst),
    );
    sb(&mut m, "sb_mixed_wide", Wide(SeqCst), None, Atomic(SeqCst));
    sb(&mut m, "sb_relacq", Atomic(Release), None, Atomic(Acquire));
    sb(&mut m, "sb_fence_release", Plain, Some(Release), Plain);
    sb(&mut m, "sb_fence_acqrel", Plain, Some(AcqRel), Plain);
    // Load buffering.
    lb(&mut m, "lb_fence_release", Plain, Some(Release), Plain);
    lb(&mut m, "lb_fence_acquire", Plain, Some(Acquire), Plain);
    lb(&mut m, "lb_relacq", Atomic(Acquire), None, Atomic(Release));
    lb(&mut m, "lb_seqcst", Atomic(SeqCst), None, Atomic(SeqCst));
    lb(&mut m, "lb_rmw", Rmw(Acquire), None, Rmw(Release));
    // IRIW.
    iriw(&mut m, "seqcst", Atomic(SeqCst), Atomic(SeqCst), None);
    iriw(&mut m, "fence", Plain, Plain, Some(SeqCst));
    iriw(&mut m, "acquire", Atomic(Release), Atomic(Acquire), None);
    // 2+2W.
    w2(&mut m, "w2_seqcst", Atomic(SeqCst), None);
    w2(&mut m, "w2_fence_seqcst", Plain, Some(SeqCst));
    w2(&mut m, "w2_release", Atomic(Release), None);
    w2(&mut m, "w2_fence_release", Plain, Some(Release));
    m
}

/// The LL/SC thread bodies, compiled through the baseline (no LSE) profile.
fn llsc_module() -> Module {
    use Access::Rmw;
    use Ordering::{Acquire, Release, SeqCst};
    let mut m = Module::new("memory_order_litmus_llsc");
    mp(&mut m, "llsc", (Rmw(Release), Rmw(Acquire)), (None, None));
    sb(&mut m, "sb_llsc_seqcst", Rmw(SeqCst), None, Rmw(SeqCst));
    lb(&mut m, "lb_llsc", Rmw(Acquire), None, Rmw(Release));
    m
}

/// MP writer `(data, flag, r)`: `data := r (plain); [fence]; flag := r` and
/// reader `(flag, data, out) -> f`: `f := flag; [fence]; *out := data`.
fn mp(
    module: &mut Module,
    name: &str,
    (write, read): (Access, Access),
    fences: (Option<Ordering>, Option<Ordering>),
) {
    let mut w = Body::new(vec![ptr(), ptr(), Ty::I64]);
    let (data, flag_ptr, r) = (w.param(0), w.param(1), w.param(2));
    w.store(Access::Plain, data, r);
    w.fence(fences.0);
    w.store(write, flag_ptr, r);
    w.finish(module, &format!("mp_{name}_w"), None);

    let mut reader = Body::new(vec![ptr(), ptr(), ptr()]);
    let (flag_ptr, data, out) = (reader.param(0), reader.param(1), reader.param(2));
    let seen = reader.load(read, flag_ptr);
    reader.fence(fences.1);
    let value = reader.load(Access::Plain, data);
    reader.store(Access::Plain, out, value);
    reader.finish(module, &format!("mp_{name}_r"), Some(seen));
}

fn compile(module: &Module, opt_level: OptLevel) -> Vec<u8> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse("aarch64-apple-darwin").expect("triple parses"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .unwrap_or_else(|error| panic!("litmus {opt_level:?}: {error}"))
    .object_code
}

/// The thread bodies compile for the Darwin target at every level on every
/// host (the native runs below need an Apple arm64 host).
#[test]
fn litmus_thread_bodies_compile_at_every_level() {
    for opt_level in OPT_LEVELS {
        native_host::assert_macho_arm64_object(&compile(&litmus_module(), opt_level));
        let llsc = native_host::compile_with_isa_profile_for(
            "aarch64-apple-darwin",
            &llsc_module(),
            opt_level,
            trust_cg_codegen::target::AArch64IsaProfile::BASELINE,
        )
        .unwrap_or_else(|error| panic!("llsc {opt_level:?}: {error}"));
        native_host::assert_macho_arm64_object(&llsc);
    }
}

// =============================================================================
// Native execution (Apple arm64)
// =============================================================================

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[path = "common/rosetta.rs"]
mod rosetta;

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
mod native {
    use super::*;
    use std::collections::BTreeMap;
    use std::process::Command;
    use std::time::Duration;

    const DRIVER: &str = include_str!("fixtures/memory_order/litmus_driver.c");

    #[derive(Debug, Clone)]
    struct Line {
        lane: String,
        expect: String,
        rounds: u64,
        forbidden: u64,
        histogram: [u64; 4],
    }

    fn field(fields: &[&str], key: &str) -> String {
        fields
            .iter()
            .find_map(|field| field.strip_prefix(key)?.strip_prefix('='))
            .unwrap_or_else(|| panic!("{key} missing from {fields:?}"))
            .to_string()
    }

    fn parse(label: &str, stdout: &str) -> BTreeMap<(String, String), Line> {
        let mut lines = BTreeMap::new();
        let mut done = false;
        for line in stdout.lines() {
            if line == "done" {
                done = true;
                continue;
            }
            let fields: Vec<&str> = line.split(' ').collect();
            assert!(fields.len() == 10, "{label}: malformed line {line:?}");
            let number = |key: &str| field(&fields, key).parse::<u64>().unwrap();
            let parsed = Line {
                lane: field(&fields, "lane"),
                expect: field(&fields, "expect"),
                rounds: number("rounds"),
                forbidden: number("forbidden"),
                histogram: [number("o00"), number("o01"), number("o10"), number("o11")],
            };
            let key = (fields[0].to_string(), fields[1].to_string());
            assert!(
                lines.insert(key, parsed).is_none(),
                "{label}: duplicate line {line:?}"
            );
        }
        assert!(done, "{label}: driver did not finish: {stdout}");
        lines
    }

    /// Link the driver with both CG objects and run it under a watchdog.
    fn run(label: &str, main: &[u8], llsc: &[u8]) -> String {
        let directory = tempfile::Builder::new()
            .prefix("trust-cg-memory-order-litmus-")
            .tempdir()
            .unwrap();
        let source = directory.path().join("driver.c");
        let main_object = directory.path().join("cg.o");
        let llsc_object = directory.path().join("cg_llsc.o");
        let binary = directory.path().join("litmus");
        std::fs::write(&source, DRIVER).unwrap();
        std::fs::write(&main_object, main).unwrap();
        std::fs::write(&llsc_object, llsc).unwrap();
        let link = Command::new(native_host::C_COMPILER)
            .args(["-O2", "-std=gnu11", "-pthread"])
            .arg(&source)
            .arg(&main_object)
            .arg(&llsc_object)
            .args(native_host::link_hardening_args())
            .arg("-o")
            .arg(&binary)
            .output()
            .expect("host C compiler");
        assert!(
            link.status.success(),
            "{label}: link failed: {}",
            String::from_utf8_lossy(&link.stderr)
        );
        let output = rosetta::command_output_with_timeout(
            &mut Command::new(&binary),
            Duration::from_secs(900),
        )
        .unwrap_or_else(|error| panic!("{label}: {error}"));
        assert!(!output.timed_out, "{label}: timed out");
        let stdout = String::from_utf8(output.output.stdout).unwrap();
        assert_eq!(
            output.output.status.code(),
            Some(0),
            "{label}: stdout={stdout} stderr={}",
            String::from_utf8_lossy(&output.output.stderr)
        );
        stdout
    }

    /// The tests that must never show their forbidden outcome, by shape.
    const FORBIDDEN: [(&str, &str); 23] = [
        ("mp", "relacq"),
        ("mp", "seqcst"),
        ("mp", "fence_release_acquire"),
        ("mp", "fence_acqrel"),
        ("mp", "fence_seqcst"),
        ("mp", "rmw_release_acquire"),
        ("mp", "cas_release_failure_acquire"),
        ("mp", "wide_release_acquire"),
        ("mp", "llsc_release_acquire"),
        ("sb", "seqcst"),
        ("sb", "fence_seqcst"),
        ("sb", "rmw_seqcst"),
        ("sb", "cas_seqcst"),
        ("sb", "wide_seqcst"),
        ("sb", "mixed_seqcst"),
        ("sb", "llsc_seqcst"),
        ("lb", "fence_release_acquire"),
        ("lb", "relacq"),
        ("lb", "seqcst"),
        ("lb", "rmw_acquire_release"),
        ("lb", "llsc_acquire_release"),
        ("iriw", "seqcst"),
        ("iriw", "fence_seqcst"),
    ];

    #[test]
    fn litmus_tests_never_show_an_outcome_their_orderings_forbid() {
        let mut store_buffering_seen = 0;
        let mut message_passing_seen = 0;
        let mut totals: BTreeMap<(String, String), (u64, u64)> = BTreeMap::new();
        for opt_level in OPT_LEVELS {
            let label = format!("{} {opt_level:?}", native_host::HOST);
            let main = compile(&litmus_module(), opt_level);
            let llsc = native_host::compile_with_isa_profile(
                &llsc_module(),
                opt_level,
                trust_cg_codegen::target::AArch64IsaProfile::BASELINE,
            )
            .unwrap_or_else(|error| panic!("{label}: llsc: {error}"));
            let lines = parse(&label, &run(&label, &main, &llsc));
            assert_eq!(lines.len(), 40, "{label}: {lines:#?}");
            // The two forbidden-shape 2+2W lines are asserted too.
            let forbidden: Vec<(&str, &str)> = FORBIDDEN
                .iter()
                .copied()
                .chain([("2+2w", "seqcst"), ("2+2w", "fence_seqcst")])
                .collect();
            for (shape, variant) in &forbidden {
                let line = &lines[&(shape.to_string(), variant.to_string())];
                assert_eq!(
                    (line.lane.as_str(), line.expect.as_str()),
                    ("cg", "forbidden"),
                    "{label}: {shape} {variant}"
                );
                assert_eq!(
                    line.forbidden, 0,
                    "{label}: {shape} {variant}: forbidden outcome observed: {line:?}"
                );
            }
            for ((shape, variant), line) in &lines {
                eprintln!(
                    "{label}: {shape:5} {variant:28} {}/{:9} rounds={} forbidden={} \
                     histogram={:?}",
                    line.lane, line.expect, line.rounds, line.forbidden, line.histogram
                );
                let total = totals
                    .entry((
                        shape.clone(),
                        format!("{variant} {}/{}", line.lane, line.expect),
                    ))
                    .or_default();
                total.0 += line.rounds;
                total.1 += line.forbidden;
                if line.expect == "forbidden" {
                    assert!(
                        forbidden.contains(&(shape.as_str(), variant.as_str())),
                        "{label}: unasserted forbidden line {shape} {variant}"
                    );
                }
            }
            store_buffering_seen += lines[&("sb".to_string(), "plain".to_string())].forbidden;
            message_passing_seen += lines[&("mp".to_string(), "plain".to_string())].forbidden;
        }
        for ((shape, variant), (rounds, forbidden)) in &totals {
            eprintln!("total: {shape:5} {variant:40} rounds={rounds} weak={forbidden}");
        }
        assert!(
            message_passing_seen > 0,
            "the plain message-passing control never showed its weak outcome, so the \
             harness did not overlap writer and reader closely enough for its \
             release/acquire lines to discriminate"
        );
        assert!(
            store_buffering_seen > 0,
            "the plain store-buffering control never showed its weak outcome, so the \
             harness did not overlap the threads closely enough for its SeqCst lines to \
             discriminate"
        );
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes, and no refusal is the license's, by accident.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
