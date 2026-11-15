// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 13 of the x86-64 source-bound body theorem: the memory and value
//! domain. A private stack slot's address stored as data (into incoming
//! memory, or into another slot, which takes it along when it escapes) and
//! read back; integer parameters past the six argument registers (the
//! incoming stack area) and integer or private-address arguments past them
//! (the outgoing argument area, `sub rsp`/`add rsp` around the call); the
//! bulk-memory intrinsics as calls to the C runtime routine; and scalar
//! atomic loads and stores as their plain-memory counterparts (OD-83).
//!
//! Fixtures are real: LIR from the trust-ir adapter and the machine stream
//! from the real x86-64 instruction selector (`super::select`). Negative
//! controls mutate that stream and must end as a typed mismatch, a refuted
//! theorem or an unsupported (uncredited) body, never as Formal credit.
//!
//! Every test here runs without a solver, and the soundness check runs them
//! all (the `x86_source_bound_body::tests::slice13::` library gate). The
//! replay on AY and Clean and the verifier-credit tests are in
//! `slice13_qualification`.

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice11::{theorem_holds, theorem_refuted};
use super::slice22::{fixture_module, fixture_owner};
use super::*;
use trust_ir::Ordering;

/// Slice-13 fixture shapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MemShape {
    // ---- (a) a private stack address stored as data
    /// `fn(out: *mut *mut u64, x: u64) { let mut v = x; *out = &mut v }`:
    /// the address leaves through incoming memory.
    AddrToOut,
    /// `fn(out, x) -> u64 { let mut v = x; *out = &mut v; g0(); v }`: from
    /// the store on, the call may read and write the slot.
    AddrToOutThenCall,
    /// `fn(x) -> u64 { let v = x; let c = &v; peek_ref(&c) + v }`: a slot
    /// holding another slot's address escapes, and takes that slot along (a
    /// closure's capture of a local).
    AddrInLocalPassed,
    /// `fn(x) -> u64 { let v = x; let c = &v; *c }`: the stored address read
    /// back and loaded through.
    AddrInLocalReadBack,
    /// `fn(x, y) -> u64 { let mut c = 0; fill(&mut c); let v = y; c = &v;
    /// g0(); v }`: an address stored into a slot that escaped already
    /// escapes at the store.
    AddrIntoEscapedSlot,
    /// `fn(out: *mut [*mut u64; 2], x, y) { let v = x; let w = y; out[0] =
    /// &v; out[1] = &w }`: two slots' addresses, each its own term.
    TwoAddrsToOut,
    // ---- (b) the incoming stack area
    /// `fn(a, b, c, d, e, f, g: u64) -> u64 { a + g }`.
    StackParam,
    /// `fn(a, .., f: u64, g: u32, h: u16) -> u32 { g + h as u32 }`.
    StackParamsNarrow,
    // ---- (c) the outgoing argument area
    /// `fn(x: u64, y: u32) -> u64 { many(x, x, x, x, x, x, y, x) }`.
    StackArgs,
    /// `fn(x: u64) -> u64 { let v = x; seven(x, x, x, x, x, x, &v) }`: a
    /// private address passed on the stack.
    StackArgAddress,
    // ---- (d) the C memory routines
    /// `fn(d: *mut u8, s: *const u8, n: usize) { memcpy(d, s, n) }`.
    Memcpy,
    /// `fn(d: *mut u8, s: *const u8, n: usize) { memmove(d, s, n) }`.
    Memmove,
    /// `fn(d: *mut u8, b: u8, n: usize) { memset(d, b, n) }`.
    Memset,
    /// `fn(s: *const u64) -> u64 { let t: [u64; 2]; memcpy(&t, s, 16);
    /// t[1] }`: the copy fills a private slot, which escapes to it.
    MemcpyIntoLocal,
    // ---- (e) atomics (OD-83)
    /// `fn(p: *const u64) -> u64 { atomic_load(p, Relaxed) }`.
    AtomicLoadRelaxed,
    /// `fn(p: *const u32) -> u32 { atomic_load(p, Acquire) }`.
    AtomicLoadAcquire,
    /// `fn(p: *const bool) -> bool { atomic_load(p, SeqCst) }`: `byte != 0`.
    AtomicLoadBool,
    /// `fn(p: *mut u64, x: u64) { atomic_store(p, x, Release) }`.
    AtomicStoreRelease,
    /// `fn(p: *mut u16, x: u16) -> u16 { store Relaxed; load Relaxed }`.
    AtomicStoreThenLoad,
    // ---- (f) a `bool` read of another store's byte
    /// `fn(x: u8) -> bool { let b = x; *(&b as *const bool) }`: trust-ir's
    /// `Load Bool` of the stored byte, `byte != 0`.
    BoolFromByte,
}

/// Every slice-13 shape whose real selection the owner admits and whose
/// theorem holds ([`every_admitted_slice_thirteen_fixture_is_qualified`]
/// checks that none is left out).
pub(crate) const SLICE_THIRTEEN: [MemShape; 20] = [
    MemShape::AddrToOut,
    MemShape::AddrToOutThenCall,
    MemShape::AddrInLocalPassed,
    MemShape::AddrInLocalReadBack,
    MemShape::AddrIntoEscapedSlot,
    MemShape::TwoAddrsToOut,
    MemShape::StackParam,
    MemShape::StackParamsNarrow,
    MemShape::StackArgs,
    MemShape::StackArgAddress,
    MemShape::Memcpy,
    MemShape::Memmove,
    MemShape::Memset,
    MemShape::MemcpyIntoLocal,
    MemShape::AtomicLoadRelaxed,
    MemShape::AtomicLoadAcquire,
    MemShape::AtomicLoadBool,
    MemShape::AtomicStoreRelease,
    MemShape::AtomicStoreThenLoad,
    MemShape::BoolFromByte,
];

impl MemShape {
    fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("s13_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }
}

/// The LIR the trust-ir adapter produces for a slice-13 shape.
pub(crate) fn slice13_lir(shape: MemShape) -> Function {
    use MemShape::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice13");
    let u64x2 = {
        let element = builder.add_type(Ty::U64);
        Ty::Array(element, 2)
    };
    let ptr_u64 = Ty::PtrMut(Box::new(Ty::U64));
    let ptr_ptr = Ty::PtrMut(Box::new(ptr_u64.clone()));
    let mut declare = |name: &str, params: Vec<Ty>, results: Vec<Ty>| {
        let ty = builder.add_func_type(params, results);
        builder.declare_function(name, ty)
    };
    let g0 = declare("g0", vec![], vec![]);
    let peek_ref = declare("peek_ref", vec![ptr_ptr.clone()], vec![Ty::U64]);
    let fill = declare("fill", vec![ptr_ptr.clone()], vec![]);
    let many = declare(
        "many",
        vec![
            Ty::U64,
            Ty::U64,
            Ty::U64,
            Ty::U64,
            Ty::U64,
            Ty::U64,
            Ty::U32,
            Ty::U64,
        ],
        vec![Ty::U64],
    );
    let seven = declare(
        "seven",
        vec![
            Ty::U64,
            Ty::U64,
            Ty::U64,
            Ty::U64,
            Ty::U64,
            Ty::U64,
            ptr_u64.clone(),
        ],
        vec![Ty::U64],
    );
    let (params, results): (Vec<Ty>, Vec<Ty>) = match shape {
        AddrToOut => (vec![ptr_ptr.clone(), Ty::U64], vec![]),
        AddrToOutThenCall => (vec![ptr_ptr.clone(), Ty::U64], vec![Ty::U64]),
        AddrInLocalPassed | AddrInLocalReadBack | StackArgAddress => (vec![Ty::U64], vec![Ty::U64]),
        AddrIntoEscapedSlot => (vec![Ty::U64, Ty::U64], vec![Ty::U64]),
        TwoAddrsToOut => (vec![ptr_ptr.clone(), Ty::U64, Ty::U64], vec![]),
        StackParam => (vec![Ty::U64; 7], vec![Ty::U64]),
        StackParamsNarrow => {
            let mut params = vec![Ty::U64; 6];
            params.extend([Ty::U32, Ty::U16]);
            (params, vec![Ty::U32])
        }
        StackArgs => (vec![Ty::U64, Ty::U32], vec![Ty::U64]),
        Memcpy | Memmove => (vec![Ty::Ptr, Ty::Ptr, Ty::U64], vec![]),
        Memset => (vec![Ty::Ptr, Ty::U8, Ty::U64], vec![]),
        MemcpyIntoLocal => (vec![Ty::Ptr], vec![Ty::U64]),
        AtomicLoadRelaxed => (vec![Ty::Ptr], vec![Ty::U64]),
        AtomicLoadAcquire => (vec![Ty::Ptr], vec![Ty::U32]),
        AtomicLoadBool => (vec![Ty::Ptr], vec![Ty::Bool]),
        AtomicStoreRelease => (vec![Ty::Ptr, Ty::U64], vec![]),
        AtomicStoreThenLoad => (vec![Ty::Ptr, Ty::U16], vec![Ty::U16]),
        BoolFromByte => (vec![Ty::U8], vec![Ty::Bool]),
    };
    let signature = builder.add_func_type(params.clone(), results);
    let mut f = builder.function(shape.name(), signature);
    let entry = f.create_block();
    let args: Vec<_> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    match shape {
        AddrToOut | AddrToOutThenCall => {
            let v = f.alloca(Ty::U64);
            f.store(Ty::U64, v, args[1]);
            f.store(ptr_u64.clone(), args[0], v);
            if shape == AddrToOut {
                f.ret(vec![]);
            } else {
                f.call_void(g0, vec![]);
                let back = f.load(Ty::U64, v);
                f.ret(vec![back]);
            }
        }
        AddrInLocalPassed | AddrInLocalReadBack => {
            let v = f.alloca(Ty::U64);
            f.store(Ty::U64, v, args[0]);
            let c = f.alloca(ptr_u64.clone());
            f.store(ptr_u64.clone(), c, v);
            if shape == AddrInLocalPassed {
                let seen = f.call(peek_ref, vec![c]);
                let back = f.load(Ty::U64, v);
                let sum = f.add(Ty::U64, seen, back);
                f.ret(vec![sum]);
            } else {
                let p = f.load(ptr_u64.clone(), c);
                let back = f.load(Ty::U64, p);
                f.ret(vec![back]);
            }
        }
        AddrIntoEscapedSlot => {
            let c = f.alloca(ptr_u64.clone());
            let null = f.null_ptr();
            f.store(ptr_u64.clone(), c, null);
            f.call_void(fill, vec![c]);
            let v = f.alloca(Ty::U64);
            f.store(Ty::U64, v, args[1]);
            f.store(ptr_u64.clone(), c, v);
            f.call_void(g0, vec![]);
            let back = f.load(Ty::U64, v);
            let sum = f.add(Ty::U64, back, args[0]);
            f.ret(vec![sum]);
        }
        TwoAddrsToOut => {
            let v = f.alloca(Ty::U64);
            f.store(Ty::U64, v, args[1]);
            let w = f.alloca(Ty::U64);
            f.store(Ty::U64, w, args[2]);
            f.store(ptr_u64.clone(), args[0], v);
            let second = f.gep_byte_offset(args[0], 8);
            f.store(ptr_u64.clone(), second, w);
            f.ret(vec![]);
        }
        StackParam => {
            let sum = f.add(Ty::U64, args[0], args[6]);
            f.ret(vec![sum]);
        }
        StackParamsNarrow => {
            let wide = f.zext(Ty::U16, Ty::U32, args[7]);
            let sum = f.add(Ty::U32, args[6], wide);
            f.ret(vec![sum]);
        }
        StackArgs => {
            let x = args[0];
            let result = f.call(many, vec![x, x, x, x, x, x, args[1], x]);
            f.ret(vec![result]);
        }
        StackArgAddress => {
            let v = f.alloca(Ty::U64);
            f.store(Ty::U64, v, args[0]);
            let x = args[0];
            let result = f.call(seven, vec![x, x, x, x, x, x, v]);
            f.ret(vec![result]);
        }
        Memcpy | Memmove => {
            f.memcopy(args[0], args[1], args[2], shape == Memmove);
            f.ret(vec![]);
        }
        Memset => {
            f.memset(args[0], args[1], args[2]);
            f.ret(vec![]);
        }
        MemcpyIntoLocal => {
            let t = f.alloca(u64x2.clone());
            let sixteen = f.iconst(Ty::U64, 16);
            f.memcopy(t, args[0], sixteen, false);
            let second = f.gep_byte_offset(t, 8);
            let value = f.load(Ty::U64, second);
            f.ret(vec![value]);
        }
        AtomicLoadRelaxed | AtomicLoadAcquire | AtomicLoadBool => {
            let (ty, ordering) = match shape {
                AtomicLoadRelaxed => (Ty::U64, Ordering::Relaxed),
                AtomicLoadAcquire => (Ty::U32, Ordering::Acquire),
                _ => (Ty::Bool, Ordering::SeqCst),
            };
            let value = f.atomic_load(ty, args[0], ordering);
            f.ret(vec![value]);
        }
        AtomicStoreRelease => {
            f.atomic_store(Ty::U64, args[0], args[1], Ordering::Release);
            f.ret(vec![]);
        }
        AtomicStoreThenLoad => {
            f.atomic_store(Ty::U16, args[0], args[1], Ordering::Relaxed);
            let value = f.atomic_load(Ty::U16, args[0], Ordering::Relaxed);
            f.ret(vec![value]);
        }
        BoolFromByte => {
            let b = f.alloca(Ty::U8);
            f.store(Ty::U8, b, args[0]);
            let truth = f.load(Ty::Bool, b);
            f.ret(vec![truth]);
        }
    }
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{shape:?}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == shape.name())
    .unwrap_or_else(|| panic!("{shape:?}: no translated function"))
}

pub(crate) fn slice13_pair(shape: MemShape) -> (Function, X86ISelFunction) {
    let source = slice13_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

/// Every fixture shape, in declaration order.
pub(crate) fn all_slice_thirteen_shapes() -> Vec<MemShape> {
    use MemShape::*;
    let all = SLICE_THIRTEEN.to_vec();
    // Exhaustive: a new shape does not compile until it is listed here.
    for shape in &all {
        match shape {
            AddrToOut | AddrToOutThenCall | AddrInLocalPassed | AddrInLocalReadBack
            | AddrIntoEscapedSlot | TwoAddrsToOut | StackParam | StackParamsNarrow | StackArgs
            | StackArgAddress | Memcpy | Memmove | Memset | MemcpyIntoLocal | AtomicLoadRelaxed
            | AtomicLoadAcquire | AtomicLoadBool | AtomicStoreRelease | AtomicStoreThenLoad
            | BoolFromByte => {}
        }
    }
    all
}

#[track_caller]
fn owner(source: &Function, machine: &X86ISelFunction, what: &str) -> ProofObligation {
    fixture_owner(source, machine)
        .unwrap_or_else(|refusal| {
            panic!(
                "{what}: {refusal}\n{}{}",
                describe_lir(source),
                describe(machine)
            )
        })
        .obligation()
        .clone()
}

/// The pair makes no claim, for the reason `needle` names (another refusal
/// later in the walk would hide a missing rule).
#[track_caller]
fn expect_unsupported_naming(source: &Function, machine: &X86ISelFunction, needle: &str) {
    match fixture_owner(source, machine) {
        Err(X86BodyRefusal::Unsupported(reason)) => {
            let reason = reason.to_string();
            assert!(
                reason.contains(needle),
                "expected `{needle}`, got: {reason}"
            );
        }
        Err(other) => panic!("{needle}: expected Unsupported, got {other}"),
        Ok(_) => panic!("{needle}: an out-of-domain pair built a body theorem"),
    }
}

/// The walk ordinal of the first row satisfying `predicate`.
#[track_caller]
fn row_where(machine: &X86ISelFunction, predicate: impl Fn(&X86ISelInst) -> bool) -> usize {
    rows(machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .find(|ordinal| predicate(inst(machine, *ordinal)))
        .unwrap_or_else(|| panic!("no such row\n{}", describe(machine)))
}

/// Whether a row reads or writes memory through `[base + disp]` with a
/// physical base register `root`.
fn through(inst: &X86ISelInst, root: u16) -> bool {
    inst.operands
        .iter()
        .any(|operand| matches!(operand, O::MemAddr { base, .. } if **base == preg(root)))
}

// ---------------------------------------------------------------------------
// Construction (no solver)
// ---------------------------------------------------------------------------

#[test]
fn owner_builds_for_every_slice_thirteen_shape_and_covers_every_value_row() {
    for shape in SLICE_THIRTEEN {
        let (source, machine) = slice13_pair(shape);
        let body = fixture_owner(&source, &machine).unwrap_or_else(|refusal| {
            panic!(
                "{shape:?}: {refusal}\n{}{}",
                describe_lir(&source),
                describe(&machine)
            )
        });
        let expected: Vec<usize> = rows(&machine)
            .into_iter()
            .filter(|(_, block, index)| {
                let opcode = machine.blocks[block].insts[*index].opcode;
                !opcode.is_pseudo()
                    && !matches!(
                        opcode,
                        X86Opcode::Jmp
                            | X86Opcode::Ret
                            | X86Opcode::Call
                            | X86Opcode::CallR
                            | X86Opcode::Ud2
                    )
            })
            .map(|(ordinal, _, _)| ordinal)
            .collect();
        assert_eq!(
            body.bound_rows(),
            expected,
            "{shape:?}\n{}",
            describe(&machine)
        );
        let entries = free_inputs_of(body.obligation());
        assert_eq!(
            owner_check(&source, &machine, body.obligation(), &entries),
            Ok(()),
            "{shape:?}"
        );
        assert!(body.obligation().is_genuinely_proven(), "{shape:?}");
        assert!(source_admits_x86_body_owner(&source, SYSV), "{shape:?}");
    }
}

#[test]
fn slice_thirteen_theorems_hold_on_samples() {
    for shape in SLICE_THIRTEEN {
        let (source, machine) = slice13_pair(shape);
        let obligation = owner(&source, &machine, &format!("{shape:?}"));
        assert!(
            theorem_holds(&obligation),
            "{shape:?}\n{}",
            describe(&machine)
        );
    }
}

/// The golden, owner, credit and host-qualification tests run over
/// [`SLICE_THIRTEEN`]: every fixture whose real selection the owner admits
/// with a theorem that holds must be in it.
#[test]
fn every_admitted_slice_thirteen_fixture_is_qualified() {
    for shape in all_slice_thirteen_shapes() {
        let (source, machine) = slice13_pair(shape);
        let holds =
            fixture_owner(&source, &machine).is_ok_and(|owner| theorem_holds(owner.obligation()));
        assert_eq!(SLICE_THIRTEEN.contains(&shape), holds, "{shape:?}");
    }
}

// ---------------------------------------------------------------------------
// Mutation helpers
// ---------------------------------------------------------------------------

/// The walk ordinal of the first load row after the `n`-th call.
fn load_after_call(machine: &X86ISelFunction, n: usize) -> usize {
    let call = find(machine, X86Opcode::Call)[n];
    (call + 1..rows(machine).len())
        .find(|ordinal| memory_access(inst(machine, *ordinal).opcode).is_some_and(|f| f.load))
        .expect("a load after the call")
}

/// The walk ordinals of every store row.
fn stores(machine: &X86ISelFunction) -> Vec<usize> {
    rows(machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .filter(|ordinal| {
            memory_access(inst(machine, *ordinal).opcode).is_some_and(|form| !form.load)
        })
        .collect()
}

/// The register operand a store row writes from.
fn stored_register_at(machine: &X86ISelFunction, store: usize) -> O {
    inst(machine, store).operands[1].clone()
}

/// A fresh 64-bit virtual register.
fn fresh(id: u32) -> O {
    O::VReg(VReg::new(id, RegClass::Gpr64))
}

/// The copy row into the argument register `root` before the `n`-th call.
fn argument_copy(machine: &X86ISelFunction, n: usize, root: u16) -> usize {
    let call = find(machine, X86Opcode::Call)[n];
    (0..call)
        .rev()
        .find(|ordinal| {
            inst(machine, *ordinal)
                .operands
                .first()
                .and_then(gpr)
                .is_some_and(|reg| reg.root == Root::Physical(root))
        })
        .unwrap_or_else(|| panic!("no copy into root {root}\n{}", describe(machine)))
}

/// The virtual register the entry copy of argument register `root` defines.
fn parameter_register(machine: &X86ISelFunction, root: u16) -> O {
    let copy = row_where(machine, |row| {
        matches!(row.opcode, X86Opcode::MovRR | X86Opcode::MovRR32)
            && row
                .operands
                .get(1)
                .and_then(gpr)
                .is_some_and(|reg| reg.root == Root::Physical(root))
    });
    inst(machine, copy).operands[0].clone()
}

// ---------------------------------------------------------------------------
// The model's rules (no solver)
// ---------------------------------------------------------------------------

/// A private address stored as data escapes its slot from the store on: to
/// incoming memory at once, into a private slot when that slot escapes
/// (taking along every slot whose address it holds), into an escaped slot
/// at once. The source's calls read exactly those slots.
#[test]
fn a_stored_address_escapes_its_slot_where_the_memory_it_went_to_is_shared() {
    let reads = |shape: MemShape| -> Vec<Vec<u32>> {
        let body = admitted_body(&slice13_lir(shape)).expect("admitted");
        body.paths[0]
            .calls
            .iter()
            .map(|call| call.slot_reads.iter().map(|(slot, _)| *slot).collect())
            .collect()
    };
    // `*out = &v`: v escapes at the store, so `g0` reads and redefines it.
    assert_eq!(reads(MemShape::AddrToOutThenCall), vec![vec![0]]);
    // `c = &v; peek_ref(&c)`: c escapes at the call and takes v along.
    assert_eq!(reads(MemShape::AddrInLocalPassed), vec![vec![0, 1]]);
    // `fill(&c)` lets c escape; `c = &v` then lets v escape at the store.
    assert_eq!(
        reads(MemShape::AddrIntoEscapedSlot),
        vec![vec![0], vec![0, 1]]
    );
    // `c = &v; *c`: no call, nothing escapes, and the read through the
    // stored address is a private read of v.
    let body = admitted_body(&slice13_lir(MemShape::AddrInLocalReadBack)).expect("admitted");
    assert!(body.paths[0].calls.is_empty());
    assert!(body.paths[0].accesses.is_empty());
}

/// Reading part of a stored private address, on either side, makes no
/// claim: an address is tracked, never bytes.
#[test]
fn a_partial_read_of_a_stored_address_is_outside_the_domain() {
    let mut source = slice13_lir(MemShape::AddrInLocalReadBack);
    let mut retyped = None;
    for block in source.blocks.values_mut() {
        for inst in &mut block.instructions {
            if let L::Load { ty, .. } = &mut inst.opcode
                && *ty == Type::I64
                && retyped.is_none()
            {
                *ty = Type::I32;
                retyped = Some(inst.results[0]);
            }
        }
    }
    if let Some(value) = retyped {
        source.value_types.insert(value, Type::I32);
    }
    let refusal = match admitted_body(&source) {
        Ok(_) => panic!("a partial read of a stored address is admitted"),
        Err(refusal) => refusal.to_string(),
    };
    assert!(
        refusal.contains("reads part of a private stack address"),
        "{refusal}"
    );
    // The machine reads 4 of the address's 8 bytes.
    let (source, mut machine) = slice13_pair(MemShape::AddrInLocalReadBack);
    let load = row_where(&machine, |row| row.opcode == X86Opcode::MovRM);
    inst_mut(&mut machine, load).opcode = X86Opcode::MovRM32;
    expect_unsupported_naming(
        &source,
        &machine,
        "reads part of a private stack address stored as data",
    );
}

/// When the machine lets other slots escape than the source does at a call
/// (here: it stores the parameter where the source stores `&v`), no single
/// trace states both, and the body makes no claim.
#[test]
fn different_escaped_slots_at_a_call_make_no_claim() {
    let (source, mut machine) = slice13_pair(MemShape::AddrInLocalPassed);
    let parameter = parameter_register(&machine, RDI);
    let address_store = *stores(&machine)
        .iter()
        .filter(|store| inst(&machine, **store).opcode == X86Opcode::MovMR)
        .find(|store| inst(&machine, **store).operands[1] != parameter)
        .expect("the store of the address");
    inst_mut(&mut machine, address_store).operands[1] = parameter;
    expect_unsupported(&source, &machine, "the address never stored");
}

/// An atomic source access pairs only with a row of the selector's atomic
/// origin and a plain one only with a plain row (OD-83); a sequentially
/// consistent store stays outside by name.
#[test]
fn atomics_pair_only_with_atomic_rows_and_a_seq_cst_store_is_refused() {
    // The origin dropped from the atomic load: a plain `mov`.
    let (source, mut machine) = slice13_pair(MemShape::AtomicLoadRelaxed);
    let load = row_where(&machine, |row| row.proof_origin.is_some());
    inst_mut(&mut machine, load).proof_origin = None;
    expect_unsupported(&source, &machine, "an atomic load paired with a plain row");
    // A plain source load paired with the atomic row.
    let (mut source, machine) = slice13_pair(MemShape::AtomicLoadRelaxed);
    for block in source.blocks.values_mut() {
        for inst in &mut block.instructions {
            if let L::AtomicLoad { ty, .. } = &inst.opcode {
                inst.opcode = L::Load {
                    ty: ty.clone(),
                    align: None,
                };
            }
        }
    }
    expect_unsupported(&source, &machine, "a plain load paired with an atomic row");
    // A sequentially consistent store.
    let mut source = slice13_lir(MemShape::AtomicStoreRelease);
    for block in source.blocks.values_mut() {
        for inst in &mut block.instructions {
            if let L::AtomicStore { ordering, .. } = &mut inst.opcode {
                *ordering = trust_cg_lower::instructions::AtomicOrdering::SeqCst;
            }
        }
    }
    let refusal = match admitted_body(&source) {
        Ok(_) => panic!("a SeqCst atomic store is admitted"),
        Err(refusal) => refusal.to_string(),
    };
    assert!(
        refusal.contains("sequentially consistent atomic store"),
        "{refusal}"
    );
}

/// The frame pointer names only an incoming stack parameter's eightbyte, and
/// RSP only the outgoing argument area of one call: anything else there
/// makes no claim, and an unwritten outgoing byte is a named undefined read.
#[test]
fn the_stack_argument_areas_admit_only_their_exact_rows() {
    // A read of the frame above the parameters.
    let (source, mut machine) = slice13_pair(MemShape::StackParam);
    let load = row_where(&machine, |row| through(row, RBP));
    if let O::MemAddr { disp, .. } = &mut inst_mut(&mut machine, load).operands[1] {
        *disp += 8;
    }
    expect_unsupported_naming(
        &source,
        &machine,
        "accesses the frame through RBP other than to read an incoming stack parameter",
    );
    // A store through the frame pointer.
    let (source, mut machine) = slice13_pair(MemShape::StackParam);
    let load = row_where(&machine, |row| through(row, RBP));
    let destination = inst(&machine, load).operands[0].clone();
    insert_at(
        &mut machine,
        load + 1,
        X86ISelInst::new(
            X86Opcode::MovMR,
            vec![
                O::MemAddr {
                    base: Box::new(preg(RBP)),
                    disp: 16,
                },
                destination,
            ],
        ),
    );
    expect_unsupported_naming(
        &source,
        &machine,
        "accesses the frame through RBP other than to read an incoming stack parameter",
    );
    // An `add rsp` that does not close the area the `sub rsp` opened.
    let (source, mut machine) = slice13_pair(MemShape::StackArgs);
    let close = row_where(&machine, |row| {
        row.opcode == X86Opcode::AddRI && row.operands.first() == Some(&preg(RSP))
    });
    inst_mut(&mut machine, close).operands[1] = O::Imm(32);
    expect_unsupported(&source, &machine, "an unbalanced add rsp");
    // The `add rsp` dropped: the function returns with RSP not restored (the
    // slice-13 robustness probe found the walk crediting it before the
    // return checked the area closed).
    let (source, mut machine) = slice13_pair(MemShape::StackArgs);
    let close = row_where(&machine, |row| {
        row.opcode == X86Opcode::AddRI && row.operands.first() == Some(&preg(RSP))
    });
    remove_at(&mut machine, close);
    expect_mismatch(&source, &machine, "RSP not restored", |m| {
        matches!(
            m,
            X86BodyMismatch::PreservedWrite {
                register: "rsp",
                ..
            }
        )
    });
    // A 64-bit stack argument whose upper bytes no store wrote.
    let (source, mut machine) = slice13_pair(MemShape::StackArgs);
    let store = row_where(&machine, |row| {
        row.opcode == X86Opcode::MovMR && through(row, RSP)
    });
    inst_mut(&mut machine, store).opcode = X86Opcode::MovMR32;
    expect_mismatch(&source, &machine, "an unwritten stack argument byte", |m| {
        matches!(m, X86BodyMismatch::UndefinedRead { .. })
    });
}

/// A private address passed on the stack must be exactly the paired slot
/// and offset (a named mismatch otherwise), and its slot escapes.
#[test]
fn a_private_address_stack_argument_is_checked_exactly() {
    let (source, mut machine) = slice13_pair(MemShape::StackArgAddress);
    let body = admitted_body(&source).expect("admitted");
    assert_eq!(body.paths[0].calls[0].stack_args.len(), 1);
    assert_eq!(
        body.paths[0].calls[0]
            .slot_reads
            .iter()
            .map(|(slot, _)| *slot)
            .collect::<Vec<_>>(),
        vec![0]
    );
    owner(&source, &machine, "StackArgAddress");
    // The slot's address 8 bytes in stored instead.
    let store = row_where(&machine, |row| {
        row.opcode == X86Opcode::MovMR && through(row, RSP)
    });
    let shifted = fresh(9_100);
    insert_at(
        &mut machine,
        store,
        X86ISelInst::new(
            X86Opcode::Lea,
            vec![
                shifted.clone(),
                O::MemAddr {
                    base: Box::new(O::StackSlot(0)),
                    disp: 8,
                },
            ],
        ),
    );
    inst_mut(&mut machine, store + 1).operands[1] = shifted;
    expect_mismatch(&source, &machine, "another offset on the stack", |m| {
        matches!(m, X86BodyMismatch::CallStackAddress { .. })
    });
}

/// The verify-owned placement of parameters past the six integer registers
/// ([`parameter_locations`]) agrees with the selector's own incoming stack
/// area, read from the formal-argument bindings it records.
#[test]
fn the_verify_owned_stack_placement_agrees_with_the_selector() {
    let signatures: Vec<Vec<Ty>> = vec![
        vec![Ty::U64; 7],
        vec![Ty::U64; 9],
        {
            let mut params = vec![Ty::U8; 6];
            params.extend([Ty::U16, Ty::U32, Ty::I64]);
            params
        },
        vec![
            Ty::U64,
            Ty::F64,
            Ty::U32,
            Ty::U32,
            Ty::U32,
            Ty::U32,
            Ty::U32,
            Ty::U16,
        ],
    ];
    for (n, params) in signatures.into_iter().enumerate() {
        let mut builder = ModuleBuilder::new("x86_source_bound_body_slice13_placement");
        let signature = builder.add_func_type(params.clone(), vec![]);
        let name = format!("s13_placement_{n}");
        let mut f = builder.function(name.clone(), signature);
        let entry = f.create_block();
        for ty in &params {
            f.add_block_param(entry, ty.clone());
        }
        f.switch_to_block(entry);
        f.ret(vec![]);
        f.build();
        let module = builder.build().expect("ModuleBuilder::build: test fixture");
        let source = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::X86_64,
            trust_cg_lower::TlsDialect::default(),
            &crate::license_test_support::permit_unlicensed(),
        )
        .expect("translates")
        .into_iter()
        .map(|(function, _)| function)
        .find(|function| function.name == name)
        .expect("translated");
        let machine = select(&source, X86CallAbi::SystemV);
        let selector: HashMap<u32, i32> = machine
            .formal_argument_bindings()
            .sorted_entries()
            .into_iter()
            .filter_map(|(_, binding)| match binding.location {
                trust_cg_lower::x86_64_isel::X86FormalArgumentLocation::IncomingStack {
                    rbp_disp,
                } => Some((binding.param_index, rbp_disp)),
                _ => None,
            })
            .collect();
        let frame = admitted_frame(&source).expect("admitted frame");
        let verify_owned: HashMap<u32, i32> = frame
            .params
            .iter()
            .enumerate()
            .filter_map(|(i, param)| Some((i as u32, param.stack?)))
            .collect();
        assert!(!verify_owned.is_empty(), "{name}: a stack parameter");
        assert_eq!(verify_owned, selector, "{name}");
    }
}

/// The C memory routines are calls by symbol with the routine's own
/// signature: another routine, or an operand of another type, is refused.
#[test]
fn the_memory_routines_are_calls_to_the_c_runtime() {
    for (shape, symbol) in [
        (MemShape::Memcpy, "memcpy"),
        (MemShape::Memmove, "memmove"),
        (MemShape::Memset, "memset"),
    ] {
        let body = admitted_body(&slice13_lir(shape)).expect("admitted");
        let call = &body.paths[0].calls[0];
        assert_eq!(call.name, symbol, "{shape:?}");
        assert!(!call.exact_module, "{shape:?}");
        assert!(call.results.is_empty(), "{shape:?}");
    }
    // The machine calls another routine.
    let (source, mut machine) = slice13_pair(MemShape::Memcpy);
    let call = find(&machine, X86Opcode::Call)[0];
    inst_mut(&mut machine, call).operands[0] = O::Symbol("memmove".into());
    expect_mismatch(&source, &machine, "memmove for memcpy", |m| {
        matches!(m, X86BodyMismatch::CallTarget { .. })
    });
    // A copy into a private slot lets it escape to the routine.
    let body = admitted_body(&slice13_lir(MemShape::MemcpyIntoLocal)).expect("admitted");
    assert_eq!(
        body.paths[0].calls[0]
            .slot_reads
            .iter()
            .map(|(slot, _)| *slot)
            .collect::<Vec<_>>(),
        vec![0]
    );
}

// ---------------------------------------------------------------------------
// Refutations
// ---------------------------------------------------------------------------

/// Wrong lowerings the Rust walk cannot judge, each one refuted by the
/// theorem on samples (and replayed to a counterexample on the qualification
/// host).
pub(crate) fn slice_thirteen_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    let mut cases = Vec::new();
    // AddrToOut: the address 8 bytes into the slot stored.
    let (source, mut machine) = slice13_pair(MemShape::AddrToOut);
    let store = *stores(&machine).last().expect("the store to *out");
    let shifted = fresh(9_000);
    insert_at(
        &mut machine,
        store,
        X86ISelInst::new(
            X86Opcode::Lea,
            vec![
                shifted.clone(),
                O::MemAddr {
                    base: Box::new(O::StackSlot(0)),
                    disp: 8,
                },
            ],
        ),
    );
    inst_mut(&mut machine, store + 1).operands[1] = shifted;
    cases.push(("AddrToOut/another-offset", source, machine));
    // AddrToOutThenCall: v's value kept across the call, which may write it.
    let (source, mut machine) = slice13_pair(MemShape::AddrToOutThenCall);
    let load = load_after_call(&machine, 0);
    let destination = inst(&machine, load).operands[0].clone();
    let x = parameter_register(&machine, RSI);
    *inst_mut(&mut machine, load) = X86ISelInst::new(X86Opcode::MovRR, vec![destination, x]);
    cases.push(("AddrToOutThenCall/kept-across-call", source, machine));
    // AddrInLocalPassed: v kept across the call c's escape took it along to.
    let (source, mut machine) = slice13_pair(MemShape::AddrInLocalPassed);
    let load = load_after_call(&machine, 0);
    let destination = inst(&machine, load).operands[0].clone();
    let x = parameter_register(&machine, RDI);
    *inst_mut(&mut machine, load) = X86ISelInst::new(X86Opcode::MovRR, vec![destination, x]);
    cases.push(("AddrInLocalPassed/kept-across-call", source, machine));
    // AddrIntoEscapedSlot: y kept across the call after `c = &v`.
    let (source, mut machine) = slice13_pair(MemShape::AddrIntoEscapedSlot);
    let load = load_after_call(&machine, 1);
    let destination = inst(&machine, load).operands[0].clone();
    let y = parameter_register(&machine, RSI);
    *inst_mut(&mut machine, load) = X86ISelInst::new(X86Opcode::MovRR, vec![destination, y]);
    cases.push(("AddrIntoEscapedSlot/kept-across-call", source, machine));
    // TwoAddrsToOut: the two addresses stored the other way round.
    let (source, mut machine) = slice13_pair(MemShape::TwoAddrsToOut);
    let pair: Vec<usize> = stores(&machine)
        .into_iter()
        .filter(|store| {
            let row = inst(&machine, *store);
            row.opcode == X86Opcode::MovMR && !matches!(&row.operands[0], O::MemAddr { base, .. } if matches!(**base, O::StackSlot(_)))
        })
        .rev()
        .take(2)
        .collect();
    let (a, b) = (
        stored_register_at(&machine, pair[0]),
        stored_register_at(&machine, pair[1]),
    );
    inst_mut(&mut machine, pair[0]).operands[1] = b;
    inst_mut(&mut machine, pair[1]).operands[1] = a;
    cases.push(("TwoAddrsToOut/swapped", source, machine));
    // AddrInLocalReadBack: v read through the address at 4 bytes.
    let (source, mut machine) = slice13_pair(MemShape::AddrInLocalReadBack);
    let load = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .rfind(|ordinal| inst(&machine, *ordinal).opcode == X86Opcode::MovRM)
        .expect("the read through the address");
    inst_mut(&mut machine, load).opcode = X86Opcode::MovRM32;
    cases.push(("AddrInLocalReadBack/narrow-read", source, machine));
    // StackParamsNarrow: the two stack parameters' eightbytes swapped.
    let (source, mut machine) = slice13_pair(MemShape::StackParamsNarrow);
    let reads: Vec<usize> = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .filter(|ordinal| through(inst(&machine, *ordinal), RBP))
        .collect();
    for (row, disp) in reads.iter().zip([24, 16]) {
        if let O::MemAddr { disp: d, .. } = &mut inst_mut(&mut machine, *row).operands[1] {
            *d = disp;
        }
    }
    cases.push(("StackParamsNarrow/swapped-eightbytes", source, machine));
    // StackParamsNarrow: the `u16` read as four bytes.
    let (source, mut machine) = slice13_pair(MemShape::StackParamsNarrow);
    let read = row_where(&machine, |row| {
        row.opcode == X86Opcode::MovzxRM16 && through(row, RBP)
    });
    inst_mut(&mut machine, read).opcode = X86Opcode::MovRM32;
    cases.push(("StackParamsNarrow/wide-read", source, machine));
    // StackArgs: x stored where the `u32` y goes.
    let (source, mut machine) = slice13_pair(MemShape::StackArgs);
    let store = row_where(&machine, |row| {
        row.opcode == X86Opcode::MovMR32 && through(row, RSP)
    });
    let x = parameter_register(&machine, RDI);
    let narrow = O::VReg(VReg::new(9_200, RegClass::Gpr32));
    insert_at(
        &mut machine,
        store,
        X86ISelInst::new(X86Opcode::MovRR32, vec![narrow.clone(), x]),
    );
    inst_mut(&mut machine, store + 1).operands[1] = narrow;
    cases.push(("StackArgs/other-value", source, machine));
    // Memcpy: destination and source swapped.
    let (source, mut machine) = slice13_pair(MemShape::Memcpy);
    let (to_rdi, to_rsi) = (
        argument_copy(&machine, 0, RDI),
        argument_copy(&machine, 0, RSI),
    );
    let a = inst(&machine, to_rdi).operands[1].clone();
    let b = inst(&machine, to_rsi).operands[1].clone();
    inst_mut(&mut machine, to_rdi).operands[1] = b;
    inst_mut(&mut machine, to_rsi).operands[1] = a;
    cases.push(("Memcpy/swapped", source, machine));
    // MemcpyIntoLocal: the first copied word read for the second.
    let (source, mut machine) = slice13_pair(MemShape::MemcpyIntoLocal);
    let load = load_after_call(&machine, 0);
    if let O::MemAddr { disp, .. } = &mut inst_mut(&mut machine, load).operands[1] {
        *disp -= 8;
    }
    cases.push(("MemcpyIntoLocal/other-word", source, machine));
    // AtomicLoadRelaxed: eight bytes further.
    let (source, mut machine) = slice13_pair(MemShape::AtomicLoadRelaxed);
    let load = row_where(&machine, |row| row.proof_origin.is_some());
    if let O::MemAddr { disp, .. } = &mut inst_mut(&mut machine, load).operands[1] {
        *disp = 8;
    }
    cases.push(("AtomicLoadRelaxed/other-address", source, machine));
    // AtomicLoadBool: the byte returned without `!= 0`.
    let (source, mut machine) = slice13_pair(MemShape::AtomicLoadBool);
    for opcode in [X86Opcode::ShrRI, X86Opcode::AddRI] {
        let row = row_where(&machine, |row| row.opcode == opcode);
        let destination = inst(&machine, row).operands[0].clone();
        let operand = inst(&machine, row).operands[1].clone();
        *inst_mut(&mut machine, row) =
            X86ISelInst::new(X86Opcode::MovRR32, vec![destination, operand]);
    }
    cases.push(("AtomicLoadBool/raw-byte", source, machine));
    // BoolFromByte: the stored byte returned without `!= 0`.
    let (source, mut machine) = slice13_pair(MemShape::BoolFromByte);
    for opcode in [X86Opcode::ShrRI, X86Opcode::AddRI] {
        let row = row_where(&machine, |row| row.opcode == opcode);
        let destination = inst(&machine, row).operands[0].clone();
        let operand = inst(&machine, row).operands[1].clone();
        *inst_mut(&mut machine, row) =
            X86ISelInst::new(X86Opcode::MovRR32, vec![destination, operand]);
    }
    cases.push(("BoolFromByte/raw-byte", source, machine));
    // AtomicStoreRelease: the pointer stored instead of the value.
    let (source, mut machine) = slice13_pair(MemShape::AtomicStoreRelease);
    let store = row_where(&machine, |row| row.proof_origin.is_some());
    let pointer = parameter_register(&machine, RDI);
    inst_mut(&mut machine, store).operands[1] = pointer;
    cases.push(("AtomicStoreRelease/pointer-stored", source, machine));
    cases
}

#[test]
fn every_slice_thirteen_refutation_is_refuted_on_samples() {
    for (label, source, machine) in slice_thirteen_refutations() {
        let theorem = theorem_without_affine_refusal(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}\n{}", describe(&machine)));
        assert!(theorem_refuted(&theorem), "{label}\n{}", describe(&machine));
    }
}

/// The real x86 optimizer's output at O1, O2 and O3 for every slice-13
/// fixture: the owner never names a mismatch for a correct lowering, and
/// every theorem it builds holds.
#[test]
fn optimized_slice_thirteen_fixtures_are_judged_without_false_mismatches() {
    use trust_cg_codegen::x86_64::pipeline::{X86Pipeline, X86PipelineConfig};
    let mut built = 0;
    for opt_level in [
        trust_cg_opt::OptLevel::O1,
        trust_cg_opt::OptLevel::O2,
        trust_cg_opt::OptLevel::O3,
    ] {
        let pipeline = X86Pipeline::new(X86PipelineConfig {
            opt_level,
            call_abi: X86CallAbi::SystemV,
            ..X86PipelineConfig::default()
        });
        for shape in all_slice_thirteen_shapes() {
            let (source, mut machine) = slice13_pair(shape);
            pipeline.run_x86_optimization_passes(&mut machine);
            match fixture_owner(&source, &machine) {
                Ok(owner) => {
                    built += 1;
                    assert!(
                        theorem_holds(owner.obligation()),
                        "{shape:?} at {opt_level:?}\n{}",
                        describe(&machine)
                    );
                    eprintln!("{opt_level:?} {shape:?}: theorem holds on samples");
                }
                Err(X86BodyRefusal::Unsupported(refusal)) => {
                    eprintln!("{opt_level:?} {shape:?}: no claim ({refusal})");
                }
                Err(other) => panic!(
                    "{shape:?} at {opt_level:?}: {other}\n{}",
                    describe(&machine)
                ),
            }
        }
    }
    assert!(built > 0, "no optimized fixture built a theorem");
}

const SLICE_THIRTEEN_SNAPSHOT_SHA256: &str =
    "5e5cd1ef121b9b081b536e592f0c6988037d7c296b8cc0a3796f611a69ecae53";

#[test]
fn slice_thirteen_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    const GOLDEN: &str =
        include_str!("../tests/fixtures/x86_source_bound_body/slice13_snapshots.smt2");
    let mut rendered = String::new();
    for shape in SLICE_THIRTEEN {
        let (source, machine) = slice13_pair(shape);
        let owner = fixture_owner(&source, &machine).unwrap();
        let smt2 = generate_smt2_query_raw(owner.obligation(), &replay_config());
        rendered.push_str(&format!(";;;; {shape:?}\n{smt2}\n"));
        let (mut source, mut machine) = (source.clone(), machine.clone());
        source.name = "renamed_function".into();
        machine.name = "renamed_function".into();
        let renamed = fixture_owner(&source, &machine).unwrap();
        assert_eq!(
            generate_smt2_query_raw(renamed.obligation(), &replay_config()),
            smt2
        );
    }
    if std::env::var_os("TCG_X86_BODY_SNAPSHOT_WRITE").is_some() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/x86_source_bound_body/slice13_snapshots.smt2");
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SLICE_THIRTEEN_SNAPSHOT_SHA256 to {:x} and re-run \
             without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display(),
            Sha256::digest(rendered.as_bytes())
        );
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(GOLDEN.as_bytes())),
        SLICE_THIRTEEN_SNAPSHOT_SHA256,
        "the golden file changed without the reviewed digest pin"
    );
    assert_eq!(rendered, GOLDEN, "slice-13 snapshots drifted");
}

// ---------------------------------------------------------------------------
// OD-217: the C memory routines are routine contracts (OD-210's guard)
// ---------------------------------------------------------------------------

/// Every slice-13 shape that calls a C memory routine, and the routine.
pub(crate) const MEMORY_ROUTINES: [(MemShape, &str); 4] = [
    (MemShape::Memcpy, "memcpy"),
    (MemShape::Memmove, "memmove"),
    (MemShape::Memset, "memset"),
    (MemShape::MemcpyIntoLocal, "memcpy"),
];

/// The symbol of every `call` row of `machine`, in walk order.
fn called_symbols(machine: &X86ISelFunction) -> Vec<String> {
    rows(machine)
        .into_iter()
        .map(|(ordinal, _, _)| inst(machine, ordinal))
        .filter(|row| row.opcode == X86Opcode::Call)
        .map(|row| match row.operands.first() {
            Some(O::Symbol(symbol)) => symbol.clone(),
            other => panic!("call row: {other:?}"),
        })
        .collect()
}

/// The refusal OD-217 gives a theorem that trusts `routine`'s contract.
#[track_caller]
fn assert_memory_routine_refused(
    what: &str,
    refusal: Result<SourceBoundX86Body<'_>, X86BodyRefusal>,
    routine: &str,
    expected: X86RoutineDefinition,
) {
    match refusal {
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::TrustedRoutine {
            routine: refused,
            definition,
        })) => {
            assert_eq!(refused, routine, "{what}");
            assert_eq!(definition, expected, "{what}");
        }
        Err(other) => panic!("{what}: refused otherwise: {other}"),
        Ok(owner) => panic!(
            "{what}: a theorem trusting {:?} was built",
            owner.trusted_routines().collect::<Vec<_>>()
        ),
    }
}

/// The fixture modules define no C memory routine (they declare `g0`,
/// `peek_ref`, `fill`, `many` and `seven`, and name the routines only as
/// intrinsics), so the owner the slice-13 tests use ([`fixture_owner`]) is
/// the production owner in their real module.
#[test]
fn the_slice_thirteen_fixture_modules_define_no_memory_routine() {
    for shape in all_slice_thirteen_shapes() {
        let source = slice13_lir(shape);
        let module = fixture_module(&source);
        for routine in ["memcpy", "memmove", "memset"] {
            assert!(!module.defines(routine), "{shape:?}: {routine}");
        }
    }
}

/// OD-217, OD-210's guard extended to slice 13's routine contract. A
/// `Memcpy`, `Memmove` or `Memset` is the selector's call of `memcpy`,
/// `memmove` or `memset` by symbol, and the theorem trusts that the routine
/// the call binds to has the intrinsic's effect. A module that defines the
/// routine itself, or (the frontend says) a sibling unit of its crate that
/// does, binds the call to that unchecked definition ahead of the C
/// library's, which may copy nothing. Before OD-217 the theorem was built
/// and holds (the call is a call of the world on both sides), and nothing
/// was refused; now no theorem is built: the module defines it
/// ([`X86RoutineDefinition::TheModule`]), another unit of its link unit does
/// ([`X86RoutineDefinition::TheLinkUnit`]), or no module is named
/// ([`X86RoutineDefinition::Unnamed`]). A routine the module only calls
/// (bound elsewhere in the link, the C library) stays trusted.
#[test]
fn a_memory_routine_the_module_or_its_crate_defines_is_never_trusted() {
    for (shape, routine) in MEMORY_ROUTINES {
        let what = format!("{shape:?}");
        let (source, machine) = slice13_pair(shape);
        assert_eq!(called_symbols(&machine), [routine], "{what}");
        // What the owner stated before OD-217: a theorem that holds and
        // trusts the routine.
        let unchecked = build_x86_body(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{what} before OD-217: {refusal}"));
        assert_eq!(
            unchecked.trusted_routines().collect::<Vec<_>>(),
            [routine],
            "{what}"
        );
        assert!(theorem_holds(unchecked.obligation()), "{what}");
        // Called only: the theorem stands, and trusts the routine.
        let owner = fixture_owner(&source, &machine)
            .unwrap_or_else(|refusal| panic!("{what}, the C library's {routine}: {refusal}"));
        assert_eq!(owner.trusted_routines().collect::<Vec<_>>(), [routine]);
        // The module defines it.
        let module = X86ModuleDefinitions::of_symbols([source.name.as_str(), routine]);
        assert_memory_routine_refused(
            &format!("{what}: the module's own {routine}"),
            source_bound_x86_body_in_module(&source, &machine, SYSV, Some(&module)),
            routine,
            X86RoutineDefinition::TheModule,
        );
        // Another unit of its crate defines it.
        let crate_unit = fixture_module(&source).with_link_unit([routine, "main"]);
        assert!(crate_unit.defines(routine), "{what}");
        assert_memory_routine_refused(
            &format!("{what}: a sibling unit's {routine}"),
            source_bound_x86_body_in_module(&source, &machine, SYSV, Some(&crate_unit)),
            routine,
            X86RoutineDefinition::TheLinkUnit,
        );
        // Another routine of the crate's is no reason.
        let other = ["memcpy", "memmove", "memset"]
            .into_iter()
            .filter(|other| *other != routine)
            .collect::<Vec<_>>();
        let unrelated = fixture_module(&source).with_link_unit(other);
        assert!(
            source_bound_x86_body_in_module(&source, &machine, SYSV, Some(&unrelated)).is_ok(),
            "{what}"
        );
        // No module named.
        assert_memory_routine_refused(
            &format!("{what}: no module named"),
            source_bound_x86_body(&source, &machine, SYSV),
            routine,
            X86RoutineDefinition::Unnamed,
        );
    }
}

/// OD-217, the circular case: a crate's own `memcpy`, `memmove` or `memset`
/// whose body copies or fills through the intrinsic calls itself (the
/// selector's call by symbol), and its theorem would assume the routine's
/// effect of the very body under proof. Before OD-217 it was built and holds;
/// now it is refused whatever module is named
/// ([`X86RoutineDefinition::TheFunction`]).
#[test]
fn a_memory_routine_never_copies_through_itself() {
    for (shape, routine) in MEMORY_ROUTINES {
        let what = format!("{shape:?} named {routine}");
        let (mut source, mut machine) = slice13_pair(shape);
        source.name = routine.into();
        machine.name = routine.into();
        assert_eq!(called_symbols(&machine), [routine], "{what}");
        let unchecked = build_x86_body(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{what} before OD-217: {refusal}"));
        assert!(theorem_holds(unchecked.obligation()), "{what}");
        for (label, module) in [
            ("its own module", Some(fixture_module(&source))),
            (
                "a module said to define nothing",
                Some(X86ModuleDefinitions::default()),
            ),
            ("no module", None),
        ] {
            assert_memory_routine_refused(
                &format!("{what}: {label}"),
                source_bound_x86_body_in_module(&source, &machine, SYSV, module.as_ref()),
                routine,
                X86RoutineDefinition::TheFunction,
            );
        }
    }
}

/// `name(v: u8) -> u8 { let mut a = [0u8; 1024]; for i in 0..1024 { a[i] = v
/// } a[0] }`: a write-only fill of a local array at the x86-64 vectorizer's
/// 1024-byte floor, which its fill tier routes to one `memset` call at O2 and
/// above (`x86_vectorize::fill_memset_route`), after the LIR the body theorem
/// reads. 1024 bytes is also the most candidate offsets slice 17 admits for
/// an indexed store, so the source is inside the body domain.
fn fill_local_lir(name: &str) -> Function {
    use trust_ir::ICmpOp;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_od216_fill");
    let u8x1024 = {
        let element = builder.add_type(Ty::U8);
        Ty::Array(element, 1024)
    };
    let signature = builder.add_func_type(vec![Ty::U8], vec![Ty::U8]);
    let mut f = builder.function(name, signature);
    let entry = f.create_block();
    let v = f.add_block_param(entry, Ty::U8);
    f.switch_to_block(entry);
    let a = f.alloca(u8x1024);
    let zero = f.iconst(Ty::U64, 0);
    let n = f.iconst(Ty::U64, 1024);
    let (header, body, exit) = (f.create_block(), f.create_block(), f.create_block());
    let i = f.add_block_param(header, Ty::U64);
    f.br(header, vec![zero]);
    f.switch_to_block(header);
    let go = f.icmp(ICmpOp::Ult, Ty::U64, i, n);
    f.condbr(go, body, vec![], exit, vec![]);
    f.switch_to_block(body);
    let at = f.gep(Ty::U8, a, vec![i]);
    f.store(Ty::U8, at, v);
    let one = f.iconst(Ty::U64, 1);
    let next = f.add(Ty::U64, i, one);
    f.br(header, vec![next]);
    f.switch_to_block(exit);
    let first = f.load(Ty::U8, a);
    f.ret(vec![first]);
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{name}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == name)
    .unwrap_or_else(|| panic!("{name}: no translated function"))
}

/// OD-218, the rewrite into a call: the only pass that turns code that is not
/// already a memory routine into a call of one after the LIR is the x86-64
/// vectorizer's fill tier (a constant-trip, write-only fill of a local of
/// 1024 bytes or more, SystemV, O2 and above), which emits `call memset`. That
/// call binds to whatever `memset` the link unit defines, a crate's own
/// included. The body theorem never credits it: the selector's own lowering
/// of the fill has its theorem, and the vectorized machine function has none,
/// whatever module is named (refused on the machine side; were its rows
/// admitted, the walk pairs calls by position and the LIR has no call there,
/// `X86BodyMismatch::CallCount`). In a function named `memset` the route is
/// withheld (its fill would call itself without end; LLVM's loop-idiom
/// recognizer withholds the same rewrite by name), and the loop stays a
/// store loop.
#[test]
fn the_vectorizers_memset_call_is_never_credited_and_never_recursive() {
    use trust_cg_codegen::x86_64::pipeline::{X86Pipeline, X86PipelineConfig};
    for opt_level in [trust_cg_opt::OptLevel::O2, trust_cg_opt::OptLevel::O3] {
        let pipeline = X86Pipeline::new(X86PipelineConfig {
            opt_level,
            call_abi: X86CallAbi::SystemV,
            ..X86PipelineConfig::default()
        });
        let source = fill_local_lir("fill_local");
        assert!(
            !source
                .blocks
                .values()
                .flat_map(|block| &block.instructions)
                .any(|inst| trusted_routine_of(&inst.opcode).is_some()),
            "the LIR calls no routine:\n{}",
            describe_lir(&source)
        );
        let mut machine = select(&source, X86CallAbi::SystemV);
        // The selector's own lowering: a store loop, and its theorem.
        let selected = fixture_owner(&source, &machine)
            .unwrap_or_else(|refusal| panic!("the selector's fill loop: {refusal}"));
        assert!(selected.trusted_routines().next().is_none());
        assert!(called_symbols(&machine).is_empty());
        pipeline.run_x86_optimization_passes(&mut machine);
        assert_eq!(
            called_symbols(&machine),
            ["memset"],
            "{opt_level:?}: the fill tier's memset route\n{}",
            describe(&machine)
        );
        for (label, module) in [
            ("its own module", Some(fixture_module(&source))),
            (
                "a crate that defines memset",
                Some(fixture_module(&source).with_link_unit(["memset"])),
            ),
            ("no module", None),
        ] {
            match source_bound_x86_body_in_module(&source, &machine, SYSV, module.as_ref()) {
                Ok(owner) => panic!(
                    "{opt_level:?}, {label}: a theorem over the vectorizer's memset call, \
                     trusting {:?}\n{}",
                    owner.trusted_routines().collect::<Vec<_>>(),
                    describe(&machine)
                ),
                Err(refusal) => {
                    // The source is inside the body domain (its selected
                    // lowering has a theorem): the vectorized machine refuses.
                    let reason = refusal.to_string();
                    eprintln!("{opt_level:?} fill_local, {label}: {reason}");
                    assert!(
                        !reason.contains("LIR source is outside the body domain"),
                        "{opt_level:?}, {label}: the fixture left the domain: {reason}"
                    );
                }
            }
        }
        let source = fill_local_lir("memset");
        let mut machine = select(&source, X86CallAbi::SystemV);
        pipeline.run_x86_optimization_passes(&mut machine);
        assert!(
            called_symbols(&machine).is_empty(),
            "{opt_level:?}: memset's own fill calls memset\n{}",
            describe(&machine)
        );
    }
}
