// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// The Rust-panic arm of the Darwin mixed-codegen exception/RAII campaign
// (tests/e2e_aarch64_eh_raii_darwin.rs, ledger X-DARWIN-P7).
//
// This file is shared: rustc compiles it into the AOT drivers (rust_main.rs,
// once linked with the trust-cg object and once as the Rust-only reference),
// and the test crate includes it for the in-memory JIT arm. It holds the Rust
// helpers the trust-cg chain functions call (a panicking leaf, a RAII guard
// whose drop glue a CG cleanup pad runs, a Rust frame between CG frames that
// catches and resumes the panic), the Rust-only reference chains, and the case
// matrix: every chain twin, three kinds (no panic, `panic_any`,
// `resume_unwind`), the throwing call, and four inputs, each observed by
// `catch_unwind` under a driver-frame guard and printed as one line.
#![allow(dead_code)]

use std::any::Any;
use std::cell::RefCell;
use std::mem::MaybeUninit;
use std::panic::{self, AssertUnwindSafe};

pub type ChainFn = unsafe extern "C-unwind" fn(u32) -> u32;

/// Chain functions in table order; the trust-cg twins are `tcgr_NAME` and
/// `tcgr_NAME_dyn`, the Rust references `ref_NAME` and `ref_NAME_dyn`.
pub const CHAINS: [&str; NCHAINS] = [
    "cleanup",
    "empty_cleanup",
    "plain",
    "nested",
    "through",
    "two_guards",
    "rust_mid",
];
pub const NCHAINS: usize = 7;
pub const TABLE_LEN: usize = 2 * NCHAINS;
pub type Table = [ChainFn; TABLE_LEN];

const TWO_GUARDS: usize = 5;
const CLEANUP: usize = 0;
const INPUTS: [u32; 4] = [0, 7, 0x7fff_ffff, 0x9e37_79b9];

// ---------------------------------------------------------------------------
// Per-case state (one test thread runs one matrix at a time)
// ---------------------------------------------------------------------------

#[derive(Default)]
struct State {
    kind: u32,
    at: u32,
    calls: u32,
    family: usize,
    log: String,
    live_payloads: i64,
    live_guards: i64,
    errors: u32,
    table: Option<Table>,
}

thread_local! {
    static STATE: RefCell<State> = RefCell::new(State::default());
}

fn with<R>(f: impl FnOnce(&mut State) -> R) -> R {
    STATE.with(|state| f(&mut state.borrow_mut()))
}

fn ev(token: &str) {
    with(|state| {
        if !state.log.is_empty() {
            state.log.push(' ');
        }
        state.log.push_str(token);
    });
}

fn panicking() -> u32 {
    u32::from(std::thread::panicking())
}

/// Integrity failures observed on this thread (a bad guard, a bad kind).
pub fn errors() -> u32 {
    with(|state| state.errors)
}

// ---------------------------------------------------------------------------
// Payloads and the panic hook
// ---------------------------------------------------------------------------

/// `panic_any` payload (kind 1): the panic hook runs for it.
pub struct CasePanic {
    payload: u32,
}

impl CasePanic {
    fn new(payload: u32) -> Self {
        with(|state| state.live_payloads += 1);
        Self { payload }
    }
}

impl Drop for CasePanic {
    fn drop(&mut self) {
        with(|state| state.live_payloads -= 1);
        ev("x1");
    }
}

/// `resume_unwind` payload (kind 2): no panic hook.
pub struct ResumePayload {
    payload: u32,
}

impl ResumePayload {
    fn new(payload: u32) -> Self {
        with(|state| state.live_payloads += 1);
        Self { payload }
    }
}

impl Drop for ResumePayload {
    fn drop(&mut self) {
        with(|state| state.live_payloads -= 1);
        ev("x2");
    }
}

/// Route `CasePanic` panics to the event log and every other panic to the
/// hook that was installed before (so unrelated test failures still print).
pub fn install_quiet_hook() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| {
        let previous = panic::take_hook();
        panic::set_hook(Box::new(move |info| {
            if let Some(payload) = info.payload().downcast_ref::<CasePanic>() {
                ev(&format!("H{:x}", payload.payload));
                return;
            }
            previous(info);
        }));
    });
}

// ---------------------------------------------------------------------------
// RAII guard run by CG cleanup pads
// ---------------------------------------------------------------------------

const GUARD_MAGIC: u32 = 0x6a09_e667;
const GUARD_DEAD: u32 = 0xdead_beef;

/// A guard living in a frame's own 16-byte slot. The CG frames construct it
/// with `rs_guard_init` and run its drop glue with `rs_guard_drop`; the drop
/// checks the object's address and magic.
#[repr(C)]
pub struct RsGuard {
    magic: u32,
    id: u32,
    this: *const RsGuard,
}

const _: () = assert!(std::mem::size_of::<RsGuard>() == 16);
const _: () = assert!(std::mem::align_of::<RsGuard>() == 8);

impl Drop for RsGuard {
    fn drop(&mut self) {
        if self.magic != GUARD_MAGIC || !std::ptr::eq(self.this, self) {
            with(|state| state.errors += 1);
            ev("BADGUARD");
            return;
        }
        ev(&format!("D{}p{}", self.id, panicking()));
        self.magic = GUARD_DEAD;
        self.this = std::ptr::null();
        with(|state| state.live_guards -= 1);
    }
}

/// # Safety
/// `slot` is writable, 8-aligned storage for an `RsGuard` holding no live one.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rs_guard_init(slot: *mut RsGuard, id: u32) {
    // SAFETY: the caller provides the storage (a CG frame slot or a
    // reference `MaybeUninit`).
    unsafe {
        slot.write(RsGuard {
            magic: GUARD_MAGIC,
            id,
            this: slot,
        })
    };
    with(|state| state.live_guards += 1);
    ev(&format!("G{id}"));
}

/// # Safety
/// `slot` holds a guard `rs_guard_init` constructed and nothing dropped yet.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rs_guard_drop(slot: *mut RsGuard) {
    // SAFETY: the caller's contract; this runs `RsGuard`'s drop glue.
    unsafe { std::ptr::drop_in_place(slot) };
}

/// # Safety
/// `buffer` is writable for `length` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rs_scratch(buffer: *mut u8, length: u64) {
    for index in 0..length {
        // SAFETY: the caller's contract.
        unsafe { buffer.add(index as usize).write((index ^ length) as u8) };
    }
}

// ---------------------------------------------------------------------------
// The panicking leaf and the Rust middle frame
// ---------------------------------------------------------------------------

struct LeafGuard;

impl Drop for LeafGuard {
    fn drop(&mut self) {
        ev(&format!("l{}", panicking()));
    }
}

/// Panics on its `at`-th call of the case with the case's kind.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn rs_leaf(x: u32) -> u32 {
    let _guard = LeafGuard;
    let (call, kind, at) = with(|state| {
        state.calls += 1;
        (state.calls, state.kind, state.at)
    });
    ev(&format!("L{call}"));
    if kind != 0 && call == at {
        let payload = x
            .wrapping_mul(2_654_435_761)
            .wrapping_add(call.wrapping_mul(40_503))
            .wrapping_add(kind);
        match kind {
            1 => panic::panic_any(CasePanic::new(payload)),
            2 => panic::resume_unwind(Box::new(ResumePayload::new(payload))),
            _ => with(|state| state.errors += 1),
        }
    }
    x.wrapping_mul(3).wrapping_add(call)
}

struct MidGuard;

impl Drop for MidGuard {
    fn drop(&mut self) {
        ev(&format!("m{}", panicking()));
    }
}

/// A Rust frame between CG frames: calls the current implementation's
/// `cleanup` chain, catches whatever panic crosses it and resumes it.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn rs_mid(x: u32) -> u32 {
    ev("M");
    let inner = with(|state| {
        state
            .table
            .map(|table| table[state.family * NCHAINS + CLEANUP])
    });
    let Some(inner) = inner else {
        with(|state| state.errors += 1);
        return 0;
    };
    let _guard = MidGuard;
    // SAFETY: every table entry has the `(u32) -> u32` C-unwind signature.
    match panic::catch_unwind(AssertUnwindSafe(|| unsafe { inner(x) })) {
        Ok(value) => value.wrapping_add(5),
        Err(payload) => {
            ev(&format!("R{}", panicking()));
            panic::resume_unwind(payload)
        }
    }
}

// ---------------------------------------------------------------------------
// Rust-only reference chains
// ---------------------------------------------------------------------------

/// Runs `rs_guard_drop` on its slot when the reference frame unwinds or
/// returns: the reference's RAII around the same guard object.
struct Scoped(*mut RsGuard);

impl Drop for Scoped {
    fn drop(&mut self) {
        // SAFETY: `self.0` was initialised by `rs_guard_init` in this frame.
        unsafe { rs_guard_drop(self.0) };
    }
}

macro_rules! guard {
    ($slot:ident, $scope:ident, $id:expr) => {
        let mut $slot = MaybeUninit::<RsGuard>::uninit();
        // SAFETY: fresh, aligned storage owned by this frame.
        unsafe { rs_guard_init($slot.as_mut_ptr(), $id) };
        let $scope = Scoped($slot.as_mut_ptr());
    };
}

fn prologue<const D: bool>(x: u32) {
    if D {
        let length = u64::from(x & 63) + 8;
        let mut buffer = [0u8; 72];
        // SAFETY: `length <= 71`, within the buffer.
        unsafe { rs_scratch(buffer.as_mut_ptr(), length) };
    }
}

fn r_cleanup<const D: bool>(x: u32) -> u32 {
    prologue::<D>(x);
    guard!(slot, _scope, 1);
    rs_leaf(x).wrapping_add(1)
}

fn r_empty_cleanup<const D: bool>(x: u32) -> u32 {
    prologue::<D>(x);
    rs_leaf(x).wrapping_add(2)
}

fn r_plain<const D: bool>(x: u32) -> u32 {
    prologue::<D>(x);
    rs_leaf(x).wrapping_add(3)
}

fn r_nested<const D: bool>(x: u32) -> u32 {
    prologue::<D>(x);
    guard!(slot, _scope, 4);
    let inner = if D {
        ref_cleanup_dyn(x)
    } else {
        ref_cleanup(x)
    };
    inner.wrapping_add(4)
}

fn r_through<const D: bool>(x: u32) -> u32 {
    prologue::<D>(x);
    guard!(slot, _scope, 5);
    let inner = if D { ref_plain_dyn(x) } else { ref_plain(x) };
    inner.wrapping_add(5)
}

fn r_two_guards<const D: bool>(x: u32) -> u32 {
    prologue::<D>(x);
    guard!(first_slot, _first, 61);
    let r1 = rs_leaf(x);
    guard!(second_slot, _second, 62);
    let r2 = rs_leaf(r1);
    r1 ^ r2
}

fn r_rust_mid<const D: bool>(x: u32) -> u32 {
    prologue::<D>(x);
    guard!(slot, _scope, 7);
    rs_mid(x).wrapping_add(7)
}

macro_rules! reference_chains {
    ($($name:ident => $compact:ident, $dynamic:ident;)*) => {
        $(
            #[inline(never)]
            pub extern "C-unwind" fn $compact(x: u32) -> u32 {
                $name::<false>(x)
            }
            #[inline(never)]
            pub extern "C-unwind" fn $dynamic(x: u32) -> u32 {
                $name::<true>(x)
            }
        )*
    };
}

reference_chains! {
    r_cleanup => ref_cleanup, ref_cleanup_dyn;
    r_empty_cleanup => ref_empty_cleanup, ref_empty_cleanup_dyn;
    r_plain => ref_plain, ref_plain_dyn;
    r_nested => ref_nested, ref_nested_dyn;
    r_through => ref_through, ref_through_dyn;
    r_two_guards => ref_two_guards, ref_two_guards_dyn;
    r_rust_mid => ref_rust_mid, ref_rust_mid_dyn;
}

/// The Rust-only reference table (compact twins, then dynamic twins).
pub fn reference_table() -> Table {
    [
        ref_cleanup,
        ref_empty_cleanup,
        ref_plain,
        ref_nested,
        ref_through,
        ref_two_guards,
        ref_rust_mid,
        ref_cleanup_dyn,
        ref_empty_cleanup_dyn,
        ref_plain_dyn,
        ref_nested_dyn,
        ref_through_dyn,
        ref_two_guards_dyn,
        ref_rust_mid_dyn,
    ]
}

// ---------------------------------------------------------------------------
// The matrix
// ---------------------------------------------------------------------------

fn describe(payload: &(dyn Any + Send)) -> (u32, u32) {
    if let Some(case) = payload.downcast_ref::<CasePanic>() {
        (1, case.payload)
    } else if let Some(resumed) = payload.downcast_ref::<ResumePayload>() {
        (2, resumed.payload)
    } else {
        (9, 0)
    }
}

fn run_case(table: &Table, family: usize, chain: usize, kind: u32, at: u32, x: u32) -> String {
    with(|state| {
        state.kind = kind;
        state.at = at;
        state.calls = 0;
        state.family = family;
        state.log.clear();
        // Each line reports its own case's residue: a leak stays in that line.
        state.live_payloads = 0;
        state.live_guards = 0;
        state.table = Some(*table);
    });
    let function = table[family * NCHAINS + chain];
    let outcome = panic::catch_unwind(AssertUnwindSafe(|| {
        guard!(slot, _scope, 900);
        // SAFETY: every table entry has the `(u32) -> u32` C-unwind signature.
        unsafe { function(x) }
    }));
    let (result, caught, payload) = match outcome {
        Ok(value) => (value, 0, 0),
        Err(payload) => {
            let (caught, value) = describe(payload.as_ref());
            drop(payload);
            (0, caught, value)
        }
    };
    let suffix = if family == 1 { "_dyn" } else { "" };
    with(|state| {
        format!(
            "{}{suffix} k={kind} a={at} x={x:08x} ret={result:08x} caught={caught} pay={payload:08x} \
             ev=[{}] live={} guards={} panicking={}",
            CHAINS[chain],
            state.log,
            state.live_payloads,
            state.live_guards,
            panicking()
        )
    })
}

/// Every case of the Rust arm over `table`, one line each, then a summary.
/// `on_line` sees each line as soon as its case has run, so a driver that
/// prints it leaves every earlier case behind when a later one crashes.
pub fn run_matrix(table: &Table, mut on_line: impl FnMut(&str)) -> Vec<String> {
    let mut lines = Vec::new();
    for family in 0..2 {
        for chain in 0..NCHAINS {
            for kind in 0..3 {
                let throwing_calls = if chain == TWO_GUARDS && kind != 0 {
                    2
                } else {
                    1
                };
                for at in 1..=throwing_calls {
                    for x in INPUTS {
                        let line = run_case(table, family, chain, kind, at, x);
                        on_line(&line);
                        lines.push(line);
                    }
                }
            }
        }
    }
    let summary = format!("cases={} errors={}", lines.len(), errors());
    on_line(&summary);
    lines.push(summary);
    lines
}
