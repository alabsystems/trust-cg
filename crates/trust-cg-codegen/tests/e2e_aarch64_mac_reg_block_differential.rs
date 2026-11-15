// trust-cg-codegen/tests/e2e_aarch64_mac_reg_block_differential.rs
//
// Native on/off/reference differential for the matmul register-blocking pass
// `mac-reg-block` (ledger L10-P4). The pass is scheduled by default at O2 and
// O3; this is the release gate the publication review asked for.
//
// Coverage (nine tests: four host-neutral, five on the native hosts), in
// three check forms.
// - Generated kernels whose failed check branches to a block returning -1:
//   two compile tests (admitted nests rewritten exactly once; negative
//   controls left untransformed) and three native differentials (admitted
//   nests, negative controls, seeded sweep) against a C reference.
// - The current rustc bridge's p4_matmul nest, whose failed check branches
//   to a raise block that calls `panic_bounds_check`: a compile test (the
//   nest rewritten exactly once; a copy with one check a single element
//   short left untransformed) and a native differential through the JIT,
//   with the panic entry bound to a recording stub.
// - The rustc bridge's pre-TrustIR-v52 spelling, a `const` + `icmp ult` +
//   kindless `assert` triple, refused at the shared codegen admission floor:
//   two admission controls (object path on every host, JIT on the native
//   hosts) require that refusal for every kernel in that spelling and for
//   the p4_matmul nest captured in it.
//
// Every kernel is a trust-ir function `k(ptr a_in, ptr b_in, ptr c_io) -> i64`
// in the shape the pass models: it copies its inputs into three stack-local
// i64 arrays, runs the bounds-checked `for i { for k { aik = a[i*N+k]; for j
// { c[i*N+j] += aik * b[k*N+j] } } }` nest (each index checked against the
// array length, the failure path returning -1), and copies `c` back out.
// Each array carries an 8-element pad that is copied in and out, so a fast
// path that touched an element past `N*N` would change the observed buffer.
//
// Each kernel is compiled four ways through the public `Pipeline`, at O2 and
// O3 with the pass ON and OFF. OFF uses the pipeline's own in-process
// disable list (`PipelineConfig::disabled_passes_override`), never the
// ambient `TRUST_CG_DISABLE_PASSES`; ON passes an explicit empty list so the
// ambient variable cannot switch the pass off either. The four objects are
// linked with a C reference (the same loops, checks and copies, unsigned
// wrapping arithmetic, `-ffp-contract=off`) and a C driver that runs every
// build and the reference on the same seeded inputs and compares the return
// value and every byte of all three buffers plus trailing canaries.
//
// Non-vacuity: the compile of each ON build reports how many times
// `mac-reg-block` changed the function
// (`PreparationMetrics::optimization_pass_changes`); every admitted nest must
// report exactly one rewrite at O2 and at O3, the OFF build must not schedule
// the pass at all, and for the writeback-shape nests (N <= 63) the ON object
// must carry the fast path's `ldp xA, xB, [xP], #N*8` word. Nests outside the
// admitted envelope and every negative control must report zero rewrites and
// produce the same machine code ON and OFF.
//
// Shapes: square N in {1, 7, 8, 9, 12, 16, 24, 32, 36, 56, 63, 64, 65, 72,
// 128} (fires exactly for the multiples of 8 or 12; a multiple of 12 takes the
// 12-lane tile, any other multiple of 8 the 8-lane tile), the nest inside an outer repeat
// loop (the benchmark shape), and — outside the envelope — the dot-product
// (ijk) loop order, a rectangular 16x24x32 nest, f64 and i32 elements.
// Negative controls (otherwise admissible N = 16 nests): c overlapping a or
// b in one local array, a nest on caller pointers called with c overlapping
// a, a bypassed loop live-out (the last a element is returned), an early exit
// inside the j-loop, i32 values in 8-byte cells (wrong element width), bounds
// checks one element short on c/b and on a, an index computed in a loop
// header before its test and checked again after the loop exits (c and a),
// the whole j body run in the j-header before its test, and j (or k) carried
// across parent iterations instead of reset. Before the recognizer's header
// and placement rules, the stale-index and header-work nests were rewritten
// and miscompiled here (the fast path returned 0 where the scalar nest
// returned -1, or skipped the header's extra store).
//
// The seeded sweep ports the generator of scripts/fuzz/matmulfuzz.py (a
// neon_map fuzzer on pointer parameters) to this pass's shape: both loop
// orders, its adversarial fill (0, -1, MIN, MAX, 1, 2 every 17 elements over
// a xorshift stream), edge sizes and fixed-seed random sizes.
//
// The driver runs each build in a forked child with shared buffers, so a
// crash or trap is an observed outcome, not a lost test; no reference run of
// a generated kernel traps, and the gate requires none to.
//
// The pre-v52 bridge check spelling: admission controls. Before TrustIR v52
// (acb3403fe, c876e3bd0) the rustc bridge emitted a constant-length slice
// or array check (MIR `Assert(BoundsCheck)`) as the canonical `%l = const
// i64 L ; %t = icmp ult i64 %idx, %l ; assert %t` triple, which the adapter
// fused into a trapping `TrapBoundsCheckExact` carrier. The current bridge
// emits no trust-ir `assert`: it lowers the same MIR check to `icmp` +
// `condbr` to a raise block that calls the real
// `core::panicking::panic_bounds_check(index, len, &Location)` and then
// `unreachable` (crates/rustc-codegen-trust-cg/src/lib.rs
// `lower_assert_terminator`, src/assert_panic.rs). The triple is kept here
// as a historical fixture. In TrustIR v52 its `assert` is a kindless source
// assert (`AssertKind::Unspecified`), and the shared admission floor refuses
// a function at its first one, before lowering or optimization
// (`require_assert_panic_kinds`); an assert with a stated kind refuses too
// until native panic lowering exists
// (crates/trust-cg-lower/src/adapter_assert_panics.rs). Every kernel list
// above in that spelling (`Check::Assert`, names prefixed `tr_`) and the
// p4_matmul nest captured in it are retained unchanged as admission
// controls: at O2 and O3, through the object path and the JIT, each must be
// refused with the floor's diagnostic naming the function, its first
// assert's coordinate and `require_assert_panic_kinds`. They are not
// converted to another check form, so `mac-reg-block`'s recognition of
// `TrapBoundsCheckExact` carriers is exercised by nothing here
// (reports/2026-10-01-assert-panic-cohort/README.md).
//
// The pre-v52 p4_matmul nest. `P4_PRE_V52_BRIDGE_MAIN` is the trust-ir the
// rustc bridge emitted before TrustIR v52 for `main` of
// benchmarks/beat-llvm/progs/p4_matmul.rs, with the repetition count made a
// parameter, `acc` returned instead of passed to `process::exit`, and the
// array-fill helper renamed. Its index checks are the kindless-assert
// triple, so it is refused like the `tr_` kernels.
//
// The current bridge's p4_matmul nest. `P4_BRIDGE_MAIN` is the trust-ir the
// rustc bridge of 25f0d2efc emits for the same `main`, with the same three
// edits. Its 24x24 i64 nest checks every index against 576 with a
// compare and branch to a raise block passing the index, the length and a
// `Location` constant to `panic_bounds_check`. It is admitted at the shared
// floor and prepared four ways like the kernels; `mac-reg-block` must
// rewrite it exactly once at O2 and at O3 (the 12-lane tile, `ldp ..,
// #192`). A copy whose `b[k*N+j]` check (compare and panic length) is 575
// must not be rewritten. Each build's prepared functions are installed in
// the unchecked JIT with `p4_fill_i64` and `panic_bounds_check` bound to
// stubs in this test, and no process-symbol fallback, so the real panic
// runtime is never reached. Each build runs in a forked child per
// repetition count. The stub records its index, length and `Location` (file,
// line, column) and ends the child with a distinct exit status. Every
// outcome must equal the C reference's: the same return value, or the same
// `panic_bounds_check` call at the `b` check's source location (575, 575 in
// the short copy for every count but 0). A trap, a signal or a missing
// record is a mismatch, never a pass.
//
// Evidence strength: for the generated kernels and the current bridge's
// p4_matmul nest, a bounded native differential on the sizes, seeds, shapes
// and repetition counts listed here; it is testing, not a proof that the
// rewrite preserves semantics. The p4_matmul capture is the bridge's output
// at its stamped revision; a bridge change does not update it. For the
// pre-v52 bridge spelling, refusal at admission only: no native execution
// and no rewrite evidence.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fmt::Write as _;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::{ObjectGlobal, OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_cg_ir::function::MachFunction;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;
#[path = "common/native_host.rs"]
mod native_host;

/// The pass's registered name, as the pass manager reports it.
const PASS: &str = "mac-reg-block";
/// The pipeline's disable-list key for the pass.
const DISABLE_KEY: &str = "mac_reg_block";
/// Elements appended to every array (copied in and out, never indexed).
const PAD: u64 = 8;
/// Value an early-exit kernel returns from inside its j-loop.
const SENTINEL: u64 = 0x5eed;

/// The four compiled builds, in the driver's column order after the reference.
const BUILDS: [(OptLevel, bool, &str); 4] = [
    (OptLevel::O2, true, "on_o2"),
    (OptLevel::O2, false, "off_o2"),
    (OptLevel::O3, true, "on_o3"),
    (OptLevel::O3, false, "off_o3"),
];

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Elem {
    I64,
    F64,
    I32,
    /// i32 values stored in 8-byte cells: `gep i64` addressing (the admitted
    /// 8-byte stride) with `load/store i32` (a 32-bit value).
    I32InI64Cells,
}

impl Elem {
    /// `(data type, gep element type, whole-cell copy type)` in trust-ir.
    fn trust_ir(self) -> (&'static str, &'static str, &'static str) {
        match self {
            Elem::I64 => ("i64", "i64", "i64"),
            Elem::F64 => ("f64", "f64", "f64"),
            Elem::I32 => ("i32", "i32", "i32"),
            Elem::I32InI64Cells => ("i32", "i64", "i64"),
        }
    }

    /// Bytes per array element (the cell).
    fn cell_bytes(self) -> u64 {
        match self {
            Elem::I32 => 4,
            _ => 8,
        }
    }

    /// Fill family the driver uses for this element type.
    fn fill(self) -> u32 {
        match self {
            Elem::I64 | Elem::I32InI64Cells => 0,
            Elem::I32 => 1,
            Elem::F64 => 2,
        }
    }
}

/// A trust-ir reshaping of the ikj nest that the pass must leave alone. Each
/// is valid SSA whose scalar semantics the fast path would not replay.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Reshape {
    None,
    /// The c index is computed in the j-header, before its test, and checked
    /// again after the j-loop exits, where it is `i*N+N`: the check fails for
    /// `i = N-1`.
    StaleCIndex,
    /// The a index is computed in the k-header and checked again after the
    /// k-loop exits, where it is `i*K+K`.
    StaleAIndex,
    /// The whole j body (indices, loads, multiply-add, store) runs in the
    /// j-header before its test, so the scalar nest runs it `N+1` times per
    /// j-loop and its extra store writes `c[i*N+N]`.
    HeaderWork,
    /// `j` is carried across k iterations (reset once per i), so only the
    /// first k iteration of each row runs the j-loop.
    JCarriedAcrossK,
    /// `k` is carried across i iterations (reset once per call), so only the
    /// first row runs the k-loop.
    KCarriedAcrossI,
}

/// How the kernel's bounds checks are expressed in trust-ir.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Check {
    /// `icmp ult` + `condbr` to a failure block that returns -1: the expanded
    /// `cmp; b.lo; b` diamond.
    Branch,
    /// The rustc bridge's pre-TrustIR-v52 spelling: a same-block `const` +
    /// `icmp ult` + kindless `assert` (`AssertKind::Unspecified`), which the
    /// shared admission floor refuses.
    Assert,
}

/// Which storage the nest's `c` operand uses.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum COperand {
    Own,
    SameAsA,
    SameAsB,
}

#[derive(Clone, Debug)]
struct Kernel {
    name: String,
    elem: Elem,
    m: u64,
    kd: u64,
    n: u64,
    /// Dot-product loop order `for i { for j { for k } } }`.
    ijk: bool,
    c_operand: COperand,
    /// Run the nest directly on the three pointer parameters (no locals).
    direct_ptrs: bool,
    /// Length the c and b checks compare against (default: the logical size).
    l_cb: Option<u64>,
    /// Length the a check compares against (default: the logical size).
    l_a: Option<u64>,
    /// Carry the last loaded a element out of the nest and return it.
    live_out: bool,
    /// Return -2 from inside the j-loop when the loaded c element is SENTINEL.
    early_exit: bool,
    /// Outer repeat loop count around the nest.
    repeat: u64,
    /// Reshaping of the ikj nest (a negative control).
    reshape: Reshape,
    /// How the bounds checks are expressed.
    check: Check,
    /// Whether the pass must rewrite this kernel.
    fires: bool,
}

impl Kernel {
    fn square(name: impl Into<String>, n: u64) -> Self {
        Kernel {
            name: name.into(),
            elem: Elem::I64,
            m: n,
            kd: n,
            n,
            ijk: false,
            c_operand: COperand::Own,
            direct_ptrs: false,
            l_cb: None,
            l_a: None,
            live_out: false,
            early_exit: false,
            repeat: 1,
            reshape: Reshape::None,
            check: Check::Branch,
            fires: false,
        }
    }

    /// An i64 square ikj nest; it fires exactly for the admitted N: a
    /// multiple of the 12- or 8-lane tile whose row stride `N*8` is an
    /// encodable immediate.
    fn admitted_square(n: u64) -> Self {
        Kernel {
            fires: n >= 8 && (n.is_multiple_of(8) || n.is_multiple_of(12)) && n * 8 <= 4095,
            ..Kernel::square(format!("sq{n}"), n)
        }
    }

    /// The same kernel with its bounds checks in the pre-v52 bridge's assert
    /// spelling.
    fn in_assert_form(&self) -> Self {
        Kernel {
            name: format!("tr_{}", self.name),
            check: Check::Assert,
            ..self.clone()
        }
    }

    fn len_a(&self) -> u64 {
        self.m * self.kd + PAD
    }
    fn len_b(&self) -> u64 {
        self.kd * self.n + PAD
    }
    fn len_c(&self) -> u64 {
        self.m * self.n + PAD
    }

    /// Elements of the third (c) buffer the driver passes.
    fn len_c_io(&self) -> u64 {
        match self.c_operand {
            COperand::Own => self.len_c(),
            COperand::SameAsA => self.len_a(),
            COperand::SameAsB => self.len_b(),
        }
    }

    /// For a direct-pointer kernel, the element offset of c inside a's buffer
    /// (c overlapping a), else `None`.
    fn alias_offset(&self) -> Option<u64> {
        self.direct_ptrs.then(|| self.m * self.n / 2 + 3)
    }

    /// Index of the c element the driver sets to SENTINEL on the last seed.
    fn sentinel_at(&self) -> Option<u64> {
        self.early_exit.then(|| self.m * self.n / 2 + 3)
    }
}

/// The trust-ir text of one kernel, named `symbol`.
#[allow(clippy::too_many_lines)]
fn kernel_ir(k: &Kernel, symbol: &str) -> String {
    let (dt, gt, ct) = k.elem.trust_ir();
    let (mul, add) = if k.elem == Elem::F64 {
        ("fmul", "fadd")
    } else {
        ("mul", "add")
    };
    let (a, b, c) = if k.direct_ptrs {
        ("%0", "%1", "%2")
    } else {
        (
            "%10",
            "%11",
            match k.c_operand {
                COperand::Own => "%12",
                COperand::SameAsA => "%10",
                COperand::SameAsB => "%11",
            },
        )
    };
    let mut s = String::new();
    let _ = write!(
        s,
        "fn @{symbol}(functy.0) {{\n\
bb0(%0: ptr, %1: ptr, %2: ptr):\n\
    %3 = const i64 0\n\
    %4 = const i64 1\n\
    %5 = const i64 {m}\n\
    %6 = const i64 {kd}\n\
    %7 = const i64 {n}\n\
    %8 = const i64 -1\n\
    %9 = const i64 -2\n\
    %13 = const i64 {len_a}\n\
    %14 = const i64 {len_b}\n\
    %15 = const i64 {len_c}\n\
    %16 = const i64 {l_a}\n\
    %17 = const i64 {l_b}\n\
    %18 = const i64 {l_c}\n\
    %19 = const i64 {rep}\n",
        m = k.m,
        kd = k.kd,
        n = k.n,
        len_a = k.len_a(),
        len_b = k.len_b(),
        len_c = k.len_c(),
        l_a = k.l_a.unwrap_or(k.m * k.kd),
        l_b = k.l_cb.unwrap_or(k.kd * k.n),
        l_c = k.l_cb.unwrap_or(k.m * k.n),
        rep = k.repeat,
    );
    let r_entry = if k.live_out { "bb4(%3, %3)" } else { "bb4(%3)" };
    if k.direct_ptrs {
        let _ = writeln!(s, "    br {r_entry}");
    } else {
        let _ = write!(
            s,
            "    %10 = alloca {ct}, %13\n\
    %11 = alloca {ct}, %14\n\
    %12 = alloca {ct}, %15\n\
    br bb1(%3)\n"
        );
        // Whole-cell copy loop `dst[t] = src[t]` for t in 0..len.
        let copy =
            |s: &mut String, bb: u32, next: &str, src: &str, dst: &str, len: &str, v: u32| {
                let _ = write!(
                    s,
                    "bb{bb}(%{v}: i64):\n\
    %{v1} = icmp ult i64 %{v}, {len}\n\
    condbr %{v1}, bb{body}, {next}\n\
bb{body}:\n\
    %{v2} = gep {ct}, ptr {src}, %{v}\n\
    %{v3} = load {ct}, ptr %{v2}\n\
    %{v4} = gep {ct}, ptr {dst}, %{v}\n\
    store {ct} %{v3}, ptr %{v4}\n\
    %{v5} = add i64 %{v}, %4\n\
    br bb{bb}(%{v5})\n",
                    v1 = v + 1,
                    v2 = v + 2,
                    v3 = v + 3,
                    v4 = v + 4,
                    v5 = v + 5,
                    body = bb + 100,
                );
            };
        copy(&mut s, 1, "bb2(%3)", "%0", a, "%13", 200);
        if k.c_operand == COperand::Own {
            copy(&mut s, 2, "bb3(%3)", "%1", b, "%14", 210);
            copy(&mut s, 3, r_entry, "%2", c, "%15", 220);
        } else {
            copy(&mut s, 2, r_entry, "%1", b, "%14", 210);
        }
    }
    // Outer repeat loop, carrying `last` when the live-out is modeled.
    let lo = k.live_out;
    let _ = write!(
        s,
        "bb4(%30: i64{rp}):\n\
    %31 = icmp ult i64 %30, %19\n\
    condbr %31, bb5(%3{ra}), bb40(%3{ra})\n\
bb5(%40: i64{ip}):\n\
    %42 = icmp ult i64 %40, %5\n\
    condbr %42, bb6, bb39{ix}\n\
bb6:\n",
        rp = if lo { ", %34: i64" } else { "" },
        ra = if lo { ", %34" } else { "" },
        ip = if lo { ", %41: i64" } else { "" },
        ix = if lo { "(%41)" } else { "" },
    );
    if k.ijk {
        let _ = write!(
            s,
            "    br bb7(%3)\n\
bb7(%50: i64):\n\
    %52 = icmp ult i64 %50, %7\n\
    condbr %52, bb8, bb14\n\
bb8:\n\
    %53 = mul i64 %40, %7\n\
    %54 = add i64 %53, %50\n\
    %55 = icmp ult i64 %54, %18\n\
    condbr %55, bb9, bb90\n\
bb9:\n\
    %56 = gep {gt}, ptr {c}, %54\n\
    %57 = load {dt}, ptr %56\n\
    br bb10(%3, %57)\n\
bb10(%60: i64, %58: {dt}):\n\
    %61 = icmp ult i64 %60, %6\n\
    condbr %61, bb11, bb13\n\
bb11:\n\
    %62 = mul i64 %40, %6\n\
    %63 = add i64 %62, %60\n\
    %64 = icmp ult i64 %63, %16\n\
    condbr %64, bb12, bb90\n\
bb12:\n\
    %65 = mul i64 %60, %7\n\
    %66 = add i64 %65, %50\n\
    %67 = icmp ult i64 %66, %17\n\
    condbr %67, bb15, bb90\n\
bb15:\n\
    %68 = gep {gt}, ptr {a}, %63\n\
    %69 = load {dt}, ptr %68\n\
    %70 = gep {gt}, ptr {b}, %66\n\
    %71 = load {dt}, ptr %70\n\
    %72 = {mul} {dt} %69, %71\n\
    %73 = {add} {dt} %58, %72\n\
    %74 = add i64 %60, %4\n\
    br bb10(%74, %73)\n\
bb13:\n\
    store {dt} %58, ptr %56\n\
    %75 = add i64 %50, %4\n\
    br bb7(%75)\n\
bb14:\n\
    %76 = add i64 %40, %4\n\
    br bb5(%76)\n",
        );
    } else {
        let _ = write!(
            s,
            "    br bb7(%3{ka})\n\
bb7(%50: i64{kp}):\n\
    %52 = icmp ult i64 %50, %6\n\
    condbr %52, bb8, bb14{kx}\n\
bb8:\n\
    %53 = mul i64 %40, %6\n\
    %54 = add i64 %53, %50\n\
    %55 = icmp ult i64 %54, %16\n\
    condbr %55, bb9, bb90\n\
bb9:\n\
    %56 = gep {gt}, ptr {a}, %54\n\
    %57 = load {dt}, ptr %56\n\
    br bb10(%3)\n\
bb10(%60: i64):\n\
    %61 = icmp ult i64 %60, %7\n\
    condbr %61, bb11, bb13\n\
bb11:\n\
    %62 = mul i64 %40, %7\n\
    %63 = add i64 %62, %60\n\
    %64 = icmp ult i64 %63, %18\n\
    condbr %64, bb12, bb90\n\
bb12:\n\
    %65 = mul i64 %50, %7\n\
    %66 = add i64 %65, %60\n\
    %67 = icmp ult i64 %66, %17\n\
    condbr %67, bb15, bb90\n\
bb15:\n\
    %68 = gep {gt}, ptr {c}, %63\n\
    %69 = load {dt}, ptr %68\n",
            ka = if lo { ", %41" } else { "" },
            kp = if lo { ", %51: i64" } else { "" },
            kx = if lo { "(%51)" } else { "" },
        );
        if k.early_exit {
            let _ = write!(
                s,
                "    %100 = const {dt} {SENTINEL}\n\
    %101 = icmp eq {dt} %69, %100\n\
    condbr %101, bb91, bb16\n\
bb16:\n"
            );
        }
        let _ = write!(
            s,
            "    %70 = gep {gt}, ptr {b}, %66\n\
    %71 = load {dt}, ptr %70\n\
    %72 = {mul} {dt} %57, %71\n\
    %73 = {add} {dt} %69, %72\n\
    store {dt} %73, ptr %68\n\
    %74 = add i64 %60, %4\n\
    br bb10(%74)\n\
bb13:\n\
    %75 = add i64 %50, %4\n\
    br bb7(%75{kl})\n\
bb14{ixp}:\n\
    %76 = add i64 %40, %4\n\
    br bb5(%76{il})\n",
            kl = if lo { ", %57" } else { "" },
            ixp = if lo { "(%77: i64)" } else { "" },
            il = if lo { ", %77" } else { "" },
        );
    }
    let _ = write!(
        s,
        "bb39{lp}:\n\
    %32 = add i64 %30, %4\n\
    br bb4(%32{la})\n\
bb40(%80: i64{cp}):\n",
        lp = if lo { "(%33: i64)" } else { "" },
        la = if lo { ", %33" } else { "" },
        cp = if lo { ", %86: i64" } else { "" },
    );
    let ret = if lo { "%86" } else { "%3" };
    if k.direct_ptrs {
        let _ = writeln!(s, "    ret {ret}");
    } else {
        let clen = match k.c_operand {
            COperand::Own => "%15",
            COperand::SameAsA => "%13",
            COperand::SameAsB => "%14",
        };
        let _ = write!(
            s,
            "    %81 = icmp ult i64 %80, {clen}\n\
    condbr %81, bb41, bb42\n\
bb41:\n\
    %82 = gep {ct}, ptr {c}, %80\n\
    %83 = load {ct}, ptr %82\n\
    %84 = gep {ct}, ptr %2, %80\n\
    store {ct} %83, ptr %84\n\
    %85 = add i64 %80, %4\n\
    br bb40(%85{ca})\n\
bb42:\n\
    ret {ret}\n",
            ca = if lo { ", %86" } else { "" },
        );
    }
    s.push_str("bb90:\n    ret %8\nbb91:\n    ret %9\n}\n");
    let s = reshape_ir(k, s);
    match k.check {
        Check::Branch => s,
        Check::Assert => assert_form_ir(k, &s),
    }
}

/// Rewrite every bounds check `%t = icmp ult i64 %idx, %L ; condbr %t, bbOK,
/// bb90` (with `%L` one of the length registers `%16`, `%17`, `%18`) into the
/// rustc bridge's pre-v52 canonical form: a same-block `const` of the length,
/// the compare, a kindless `assert` and a branch to `bbOK`. Loop tests and the
/// early exit are left alone; a generator change that leaves fewer than three
/// checks to rewrite fails.
fn assert_form_ir(k: &Kernel, s: &str) -> String {
    let lengths = [
        ("%16", k.l_a.unwrap_or(k.m * k.kd)),
        ("%17", k.l_cb.unwrap_or(k.kd * k.n)),
        ("%18", k.l_cb.unwrap_or(k.m * k.n)),
    ];
    let lines: Vec<&str> = s.lines().collect();
    let mut out = String::new();
    let mut rewritten = 0usize;
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i].trim();
        let next = lines.get(i + 1).map(|l| l.trim()).unwrap_or("");
        let check = line.split_once(" = icmp ult i64 ").and_then(|(t, rest)| {
            let (idx, len) = rest.split_once(", ")?;
            let value = lengths.iter().find(|(reg, _)| *reg == len)?.1;
            let tail = next.strip_prefix(&format!("condbr {t}, "))?;
            let ok = tail.strip_suffix(", bb90")?;
            Some((t, idx, value, ok))
        });
        match check {
            Some((t, idx, value, ok)) => {
                let id: u32 = t[1..].parse().expect("a numbered check value");
                let _ = write!(
                    out,
                    "%{c} = const i64 {value}\n{t} = icmp ult i64 {idx}, %{c}\nassert {t}\nbr {ok}\n",
                    c = id + 1000,
                );
                rewritten += 1;
                i += 2;
            }
            None => {
                out.push_str(lines[i]);
                out.push('\n');
                i += 1;
            }
        }
    }
    assert!(
        rewritten >= 3,
        "{}: only {rewritten} checks rewritten",
        k.name
    );
    drop_unreferenced_exit_blocks(&out)
}

/// `s` without each one-line exit block (`bb90:` / `bb91:` followed by its
/// `ret`) that no edge names any more. The assert form removes every branch
/// to the bounds-failure exit, and trust-ir refuses a block no edge reaches
/// (`UnreachableBlock`) — since WS7.3 at every ingestion entry, before the
/// floor this module is built to reach. The bridge's pre-v52 form has no such
/// block either.
fn drop_unreferenced_exit_blocks(s: &str) -> String {
    let mut lines: Vec<&str> = s.lines().collect();
    for label in ["bb90", "bb91"] {
        let header = format!("{label}:");
        let Some(at) = lines.iter().position(|line| line.trim() == header) else {
            continue;
        };
        let named = lines
            .iter()
            .enumerate()
            .any(|(index, line)| index != at && line.contains(label));
        if !named {
            assert!(
                lines
                    .get(at + 1)
                    .is_some_and(|line| line.trim().starts_with("ret ")),
                "{label} is a one-line exit block"
            );
            lines.drain(at..at + 2);
        }
    }
    let mut out = lines.join("\n");
    out.push('\n');
    out
}

/// `s` with its single occurrence of `anchor` replaced; a generator change
/// that moves an anchor fails loudly instead of testing the unreshaped nest.
fn anchored(s: &str, anchor: &str, with: &str) -> String {
    assert_eq!(
        s.matches(anchor).count(),
        1,
        "reshape anchor {anchor:?} must occur exactly once in:\n{s}"
    );
    s.replacen(anchor, with, 1)
}

/// Apply `k.reshape` to the generated ikj nest (instruction lines carry no
/// indentation: the generator's string continuations strip it).
fn reshape_ir(k: &Kernel, s: String) -> String {
    assert!(
        k.reshape == Reshape::None
            || (k.elem == Elem::I64
                && k.c_operand == COperand::Own
                && !(k.ijk || k.live_out || k.early_exit || k.direct_ptrs)),
        "{}: a reshape applies to the plain ikj nest only",
        k.name
    );
    match k.reshape {
        Reshape::None => s,
        Reshape::StaleCIndex => {
            let s = anchored(
                &s,
                "bb10(%60: i64):\n%61 = icmp",
                "bb10(%60: i64):\n%62 = mul i64 %40, %7\n%63 = add i64 %62, %60\n%61 = icmp",
            );
            let s = anchored(
                &s,
                "bb11:\n%62 = mul i64 %40, %7\n%63 = add i64 %62, %60\n",
                "bb11:\n",
            );
            anchored(
                &s,
                "bb13:\n%75 = add i64 %50, %4\n",
                "bb13:\n%190 = icmp ult i64 %63, %18\ncondbr %190, bb17, bb90\nbb17:\n%75 = add i64 %50, %4\n",
            )
        }
        Reshape::StaleAIndex => {
            let s = anchored(
                &s,
                "bb7(%50: i64):\n%52 = icmp",
                "bb7(%50: i64):\n%53 = mul i64 %40, %6\n%54 = add i64 %53, %50\n%52 = icmp",
            );
            let s = anchored(
                &s,
                "bb8:\n%53 = mul i64 %40, %6\n%54 = add i64 %53, %50\n",
                "bb8:\n",
            );
            anchored(
                &s,
                "bb14:\n%76 = add i64 %40, %4\n",
                "bb14:\n%191 = icmp ult i64 %54, %16\ncondbr %191, bb18, bb90\nbb18:\n%76 = add i64 %40, %4\n",
            )
        }
        Reshape::HeaderWork => {
            let (dt, gt, _) = k.elem.trust_ir();
            let start = s.find("bb10(%60: i64):\n").expect("j-header");
            let latch = "br bb10(%74)\n";
            let end = s.find(latch).expect("j-latch") + latch.len();
            let j_loop = format!(
                "bb10(%60: i64):\n\
%62 = mul i64 %40, %7\n\
%63 = add i64 %62, %60\n\
%65 = mul i64 %50, %7\n\
%66 = add i64 %65, %60\n\
%68 = gep {gt}, ptr %12, %63\n\
%69 = load {dt}, ptr %68\n\
%70 = gep {gt}, ptr %11, %66\n\
%71 = load {dt}, ptr %70\n\
%72 = mul {dt} %57, %71\n\
%73 = add {dt} %69, %72\n\
store {dt} %73, ptr %68\n\
%61 = icmp ult i64 %60, %7\n\
condbr %61, bb11, bb13\n\
bb11:\n\
%64 = icmp ult i64 %63, %18\n\
condbr %64, bb12, bb90\n\
bb12:\n\
%67 = icmp ult i64 %66, %17\n\
condbr %67, bb15, bb90\n\
bb15:\n\
%74 = add i64 %60, %4\n\
br bb10(%74)\n"
            );
            format!("{}{j_loop}{}", &s[..start], &s[end..])
        }
        Reshape::JCarriedAcrossK => {
            let s = anchored(
                &s,
                "br bb7(%3)\nbb7(%50: i64):",
                "br bb7(%3, %3)\nbb7(%50: i64, %192: i64):",
            );
            let s = anchored(&s, "br bb10(%3)\n", "br bb10(%192)\n");
            anchored(&s, "br bb7(%75)\n", "br bb7(%75, %60)\n")
        }
        Reshape::KCarriedAcrossI => {
            let s = anchored(&s, "bb5(%40: i64):", "bb5(%40: i64, %193: i64):");
            let s = anchored(
                &s,
                "condbr %31, bb5(%3), bb40(%3)",
                "condbr %31, bb5(%3, %3), bb40(%3)",
            );
            let s = anchored(&s, "br bb7(%3)\nbb7(", "br bb7(%193)\nbb7(");
            anchored(&s, "br bb5(%76)\n", "br bb5(%76, %50)\n")
        }
    }
}

/// A one-function module holding `k` under `symbol`.
fn module(k: &Kernel, symbol: &str) -> trust_ir::Module {
    let text = format!(
        "; TrustIr text format v1\nmodule \"mrb\"\ntarget \"{}\" 8 little abi=\"aapcs64\"\n\
         functy.0 = (ptr, ptr, ptr) -> (i64)\n{}",
        native_host::TRIPLE,
        kernel_ir(k, symbol)
    );
    trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|error| panic!("{symbol}: trust-ir parse: {error:?}\n{text}"))
}

/// One compiled build of one kernel.
struct Compiled {
    object: Vec<u8>,
    /// Runs of `mac-reg-block` that changed the function; `None` when the
    /// pass was not scheduled.
    rewrites: Option<u32>,
}

/// One module prepared by the public `Pipeline` at one level with the pass
/// on or off: the final machine functions, the module's data globals and
/// the pass's rewrite count. The object and the JIT image of a build are
/// both emitted from these same functions.
struct Prepared {
    pipeline: Pipeline,
    functions: Vec<MachFunction>,
    globals: Vec<ObjectGlobal>,
    /// Runs of `mac-reg-block` that changed a function; `None` when the
    /// pass was not scheduled.
    rewrites: Option<u32>,
}

impl Prepared {
    fn object(&self, symbol: &str) -> Compiled {
        let object = self
            .pipeline
            .compile_module_with_globals(&self.functions, &self.globals)
            .unwrap_or_else(|error| panic!("{symbol}: object emission: {error}"));
        native_host::assert_native_object(&object);
        Compiled {
            object,
            rewrites: self.rewrites,
        }
    }
}

fn compile(k: &Kernel, symbol: &str, opt: OptLevel, pass_on: bool) -> Compiled {
    prepare(&module(k, symbol), symbol, opt, pass_on).object(symbol)
}

/// Lower `module` (through the shared codegen admission floor) and prepare
/// every function at `opt` with the pass on or off through the pipeline's
/// in-process disable list.
fn prepare(module: &trust_ir::Module, symbol: &str, opt: OptLevel, pass_on: bool) -> Prepared {
    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{symbol}: lowering: {error}"));
    let globals = trust_cg_codegen::compiler::module_object_globals(module)
        .unwrap_or_else(|error| panic!("{symbol}: globals: {error}"));
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: opt,
        target_triple: native_host::TRIPLE.into(),
        disabled_passes_override: Some(if pass_on {
            String::new()
        } else {
            DISABLE_KEY.to_string()
        }),
        ..PipelineConfig::default()
    });
    let mut functions = Vec::new();
    let mut rewrites = None;
    for (function, _) in &lowered {
        let (function, metrics) = pipeline
            .prepare_function_with_metrics(function, None)
            .unwrap_or_else(|error| panic!("{symbol} {opt:?} pass_on={pass_on}: {error}"));
        for (name, count) in &metrics.optimization_pass_changes {
            if name == PASS {
                *rewrites.get_or_insert(0) += count;
            }
        }
        functions.push(function);
    }
    Prepared {
        pipeline,
        functions,
        globals,
        rewrites,
    }
}

/// `LDP Xt1, Xt2, [Xn], #imm` (64-bit, post-index) with `imm == n * 8`.
fn is_ldp_post_index_by_row(word: u32, n: u64) -> bool {
    word & 0xffc0_0000 == 0xa8c0_0000 && u64::from((word >> 15) & 0x7f) == n
}

/// The widest `b` lane pair the register-blocked k-loop loads off the base
/// of its row post-increment `ldp .., [xB], #N*8`: the highest `lane` of an
/// `LDP Xt1, Xt2, [xB, #lane*8]` (64-bit, signed offset) in the
/// `window` words before a row post-increment, per k-loop found. A 12-lane
/// tile's top pair is lane 10, an 8-lane tile's lane 6.
fn k_loop_top_lane_pairs(words: &[u32], n: u64, window: usize) -> Vec<u32> {
    let base = |word: u32| (word >> 5) & 0x1f;
    let mut tops = Vec::new();
    for (at, &word) in words.iter().enumerate() {
        if !is_ldp_post_index_by_row(word, n) {
            continue;
        }
        let top = words[at.saturating_sub(window)..at]
            .iter()
            .filter(|&&w| w & 0xffc0_0000 == 0xa940_0000 && base(w) == base(word))
            .map(|&w| (w >> 15) & 0x7f)
            .max()
            .unwrap_or(0);
        tops.push(top);
    }
    tops
}

/// All four builds of `k`, checked against the pass's firing contract.
fn compile_all_builds(k: &Kernel) -> Vec<(String, Compiled)> {
    let builds: Vec<(String, Compiled)> = BUILDS
        .iter()
        .map(|&(opt, on, tag)| {
            let symbol = format!("{}_{tag}", k.name);
            let compiled = compile(k, &symbol, opt, on);
            (symbol, compiled)
        })
        .collect();
    check_firing_contract(&k.name, k.fires, k.n, &builds);
    builds
}

/// The pass's firing contract over the four builds of one kernel: the OFF
/// builds never schedule it, each ON build rewrites exactly `fires` times,
/// and per opt level the ON code differs from the OFF code exactly when the
/// pass fired (carrying the writeback fast path's row `ldp` for `n*8 <= 504`).
fn check_firing_contract(name: &str, fires: bool, n: u64, builds: &[(String, Compiled)]) {
    for ((opt, on, tag), (_, compiled)) in BUILDS.iter().zip(builds) {
        let label = format!("{name} {tag} ({opt:?})");
        if !on {
            assert_eq!(
                compiled.rewrites, None,
                "{label}: the in-process disable list must unschedule {PASS}"
            );
            continue;
        }
        let expected = u32::from(fires);
        assert_eq!(
            compiled.rewrites,
            Some(expected),
            "{label}: {PASS} must rewrite this nest exactly {expected} time(s)"
        );
    }
    // Per opt level: the ON build's code differs from the OFF build's exactly
    // when the pass fired; the writeback-shape fast path carries its row
    // post-increment `ldp` word.
    for (on, off) in [(0usize, 1usize), (2, 3)] {
        let on_words = native_host::text_words(&builds[on].1.object);
        let off_words = native_host::text_words(&builds[off].1.object);
        let label = format!("{name} {}", BUILDS[on].2);
        if fires {
            assert_ne!(
                on_words, off_words,
                "{label}: a rewrite must change the code"
            );
            if n * 8 <= 504 {
                assert!(
                    on_words.iter().any(|&w| is_ldp_post_index_by_row(w, n)),
                    "{label}: the register-blocked k-loop's `ldp .., #{}` is missing",
                    n * 8
                );
                // The tile width: 12 lanes (top pair at `#80`) exactly when 12
                // divides N, else 8 lanes (top pair at `#48`).
                // (A later unroller may replicate the k-loop body.)
                let top = if n.is_multiple_of(12) { 10 } else { 6 };
                let tops = k_loop_top_lane_pairs(&on_words, n, 24);
                assert!(
                    !tops.is_empty() && tops.iter().all(|&t| t == top),
                    "{label}: the register-blocked k-loop must use a {}-lane tile \
                     (top lane pairs {tops:?})",
                    top + 2
                );
            }
        } else {
            assert_eq!(
                on_words, off_words,
                "{label}: an unrewritten nest must compile to the same code ON and OFF"
            );
        }
    }
}

/// The admitted envelope: square i64 nests across tile and writeback limits,
/// plus the outer-repeat benchmark shape.
fn admitted_kernels() -> Vec<Kernel> {
    let mut kernels: Vec<Kernel> = [1, 7, 8, 9, 12, 16, 24, 32, 36, 56, 63, 64, 65, 72, 128]
        .into_iter()
        .map(Kernel::admitted_square)
        .collect();
    kernels.push(Kernel {
        repeat: 2,
        fires: true,
        ..Kernel::square("repeat2_16", 16)
    });
    kernels
}

/// Shapes outside the envelope and the negative controls. None may fire.
fn untransformed_kernels() -> Vec<Kernel> {
    vec![
        Kernel {
            ijk: true,
            ..Kernel::square("ijk16", 16)
        },
        Kernel {
            m: 16,
            kd: 24,
            n: 32,
            ..Kernel::square("rect16x24x32", 16)
        },
        Kernel {
            elem: Elem::F64,
            ..Kernel::square("f64_16", 16)
        },
        Kernel {
            elem: Elem::I32,
            ..Kernel::square("i32_16", 16)
        },
        // c overlapping a / b inside one local array.
        Kernel {
            c_operand: COperand::SameAsA,
            ..Kernel::square("alias_ca16", 16)
        },
        Kernel {
            c_operand: COperand::SameAsB,
            ..Kernel::square("alias_cb16", 16)
        },
        // The nest on caller pointers, called with c overlapping a.
        Kernel {
            direct_ptrs: true,
            ..Kernel::square("ptr_alias16", 16)
        },
        // Bypassed loop live-out: the last a element leaves the nest.
        Kernel {
            live_out: true,
            ..Kernel::square("live_out16", 16)
        },
        // Mandatory control flow: an early exit from the j-loop.
        Kernel {
            early_exit: true,
            ..Kernel::square("early_exit16", 16)
        },
        // Wrong element width: i32 values in 8-byte cells.
        Kernel {
            elem: Elem::I32InI64Cells,
            ..Kernel::square("narrow16", 16)
        },
        // Under-sized bounds: c/b checks one element short, then a's.
        Kernel {
            l_cb: Some(16 * 16 - 1),
            ..Kernel::square("short_cb16", 16)
        },
        Kernel {
            l_a: Some(16 * 16 - 1),
            ..Kernel::square("short_a16", 16)
        },
        // Mandatory control flow in loop headers: an index computed before
        // the header's test and checked after the loop exits (it is `i*N+N`
        // there), and the whole j body run in the j-header, N+1 times.
        Kernel {
            reshape: Reshape::StaleCIndex,
            ..Kernel::square("stale_c_index16", 16)
        },
        Kernel {
            reshape: Reshape::StaleAIndex,
            ..Kernel::square("stale_a_index16", 16)
        },
        Kernel {
            reshape: Reshape::HeaderWork,
            ..Kernel::square("header_work16", 16)
        },
        // Counters not reset once per parent iteration.
        Kernel {
            reshape: Reshape::JCarriedAcrossK,
            ..Kernel::square("j_carry16", 16)
        },
        Kernel {
            reshape: Reshape::KCarriedAcrossI,
            ..Kernel::square("k_carry16", 16)
        },
    ]
}

/// xorshift64 stream for the seeded size choice (the C driver's fill uses
/// the same shifts).
fn xorshift64(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

/// Fixed seed for the sweep's random sizes; a failure names the kernel, so a
/// run is reproducible from this constant alone.
const SWEEP_SEED: u64 = 0x6d61_635f_7265_675f;

/// The ported matmulfuzz sweep: edge sizes plus fixed-seed random sizes (and
/// random multiples of 8, so the admitted path is sampled too), in both loop
/// orders.
fn sweep_kernels() -> Vec<Kernel> {
    let mut sizes = vec![0u64, 2, 3, 4, 5, 15, 17, 40, 48];
    let mut state = SWEEP_SEED;
    while sizes.len() < 12 {
        let n = xorshift64(&mut state) % 100 + 1;
        if !sizes.contains(&n) {
            sizes.push(n);
        }
    }
    while sizes.len() < 14 {
        let n = (xorshift64(&mut state) % 15 + 1) * 8;
        if !sizes.contains(&n) {
            sizes.push(n);
        }
    }
    let mut kernels = Vec::new();
    for n in sizes {
        let mut ikj = Kernel::admitted_square(n);
        ikj.name = format!("sweep_ikj{n}");
        kernels.push(ikj);
        kernels.push(Kernel {
            ijk: true,
            ..Kernel::square(format!("sweep_ijk{n}"), n)
        });
    }
    kernels
}

// ---------------------------------------------------------------------------
// C reference and driver
// ---------------------------------------------------------------------------

/// The C reference for `k`: the same copies, loops, checks, early exit and
/// live-out, in unsigned wrapping (or unfused IEEE) arithmetic.
#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
fn c_reference(k: &Kernel) -> String {
    assert_eq!(
        k.check,
        Check::Branch,
        "{}: only the branch check form is admitted for native execution",
        k.name
    );
    let (data, cell) = match k.elem {
        Elem::I64 => ("uint64_t", "uint64_t"),
        Elem::F64 => ("double", "double"),
        Elem::I32 => ("uint32_t", "uint32_t"),
        Elem::I32InI64Cells => ("uint32_t", "uint64_t"),
    };
    let narrow = k.elem == Elem::I32InI64Cells;
    let load = |arr: &str, idx: &str| {
        if narrow {
            format!("((uint32_t){arr}[{idx}])")
        } else {
            format!("{arr}[{idx}]")
        }
    };
    let store = |arr: &str, idx: &str, v: &str| {
        if narrow {
            format!(
                "{arr}[{idx}] = ({arr}[{idx}] & 0xffffffff00000000ull) | (uint64_t)(uint32_t)({v});"
            )
        } else {
            format!("{arr}[{idx}] = {v};")
        }
    };
    let (m, kd, n) = (k.m, k.kd, k.n);
    let l_a = k.l_a.unwrap_or(m * kd);
    let l_b = k.l_cb.unwrap_or(kd * n);
    let l_c = k.l_cb.unwrap_or(m * n);
    let mut s = String::new();
    let _ = writeln!(
        s,
        "int64_t ref_{name}(void* p0, void* p1, void* p2) {{",
        name = k.name
    );
    if k.direct_ptrs {
        let _ = writeln!(
            s,
            "  {cell}* a = ({cell}*)p0; {cell}* b = ({cell}*)p1; {cell}* c = ({cell}*)p2;"
        );
    } else {
        let _ = writeln!(
            s,
            "  static {cell} a[{la}], b[{lb}], c_own[{lc}];\n  \
             for (uint64_t t = 0; t < {la}; t++) a[t] = (({cell}*)p0)[t];\n  \
             for (uint64_t t = 0; t < {lb}; t++) b[t] = (({cell}*)p1)[t];",
            la = k.len_a(),
            lb = k.len_b(),
            lc = k.len_c(),
        );
        match k.c_operand {
            COperand::Own => {
                let _ = writeln!(
                    s,
                    "  for (uint64_t t = 0; t < {lc}; t++) c_own[t] = (({cell}*)p2)[t];\n  \
                     {cell}* c = c_own;",
                    lc = k.len_c()
                );
            }
            COperand::SameAsA => {
                let _ = writeln!(s, "  (void)c_own; {cell}* c = a;");
            }
            COperand::SameAsB => {
                let _ = writeln!(s, "  (void)c_own; {cell}* c = b;");
            }
        }
    }
    let _ = writeln!(s, "  uint64_t last = 0; (void)last;");
    let reshape = k.reshape;
    let _ = writeln!(
        s,
        "  for (uint64_t r = 0; r < {rep}; r++) {{\n  {k_outer}for (uint64_t i = 0; i < {m}; i++) {{",
        rep = k.repeat,
        k_outer = if reshape == Reshape::KCarriedAcrossI {
            "uint64_t k = 0;\n  "
        } else {
            ""
        },
    );
    if k.ijk {
        let _ = writeln!(
            s,
            "    for (uint64_t j = 0; j < {n}; j++) {{\n      \
             uint64_t cidx = i * {n} + j; if (!(cidx < {l_c})) return -1;\n      \
             {data} acc = {cload};\n      \
             for (uint64_t k = 0; k < {kd}; k++) {{\n        \
             uint64_t aidx = i * {kd} + k; if (!(aidx < {l_a})) return -1;\n        \
             uint64_t bidx = k * {n} + j; if (!(bidx < {l_b})) return -1;\n        \
             {data} av = {aload}; {data} bv = {bload};\n        \
             acc = ({data})(acc + ({data})(av * bv));\n      }}\n      \
             {cstore}\n    }}",
            cload = load("c", "cidx"),
            aload = load("a", "aidx"),
            bload = load("b", "bidx"),
            cstore = store("c", "cidx", "acc"),
        );
    } else {
        let early = if k.early_exit {
            format!("if (cv == ({data}){SENTINEL}ull) return -2;")
        } else {
            String::new()
        };
        let record_last = if k.live_out {
            "last = (uint64_t)aik;"
        } else {
            ""
        };
        let (aload, cload, bload) = (load("a", "aidx"), load("c", "cidx"), load("b", "bidx"));
        let cstore = store("c", "cidx", &format!("({data})(cv + ({data})(aik * bv))"));
        let j_loop = if reshape == Reshape::HeaderWork {
            // The header's loads, multiply-add and store run before its test,
            // once more than the body (the extra access lands in the pad).
            format!(
                "for (uint64_t j = 0; ; j++) {{\n        \
                 uint64_t cidx = i * {n} + j; uint64_t bidx = k * {n} + j;\n        \
                 {data} cv = {cload}; {data} bv = {bload};\n        \
                 {cstore}\n        \
                 if (!(j < {n})) break;\n        \
                 if (!(cidx < {l_c})) return -1;\n        \
                 if (!(bidx < {l_b})) return -1;\n      }}"
            )
        } else {
            format!(
                "for ({j_init}; j < {n}; j++) {{\n        \
                 uint64_t cidx = i * {n} + j; if (!(cidx < {l_c})) return -1;\n        \
                 uint64_t bidx = k * {n} + j; if (!(bidx < {l_b})) return -1;\n        \
                 {data} cv = {cload}; {early}\n        \
                 {data} bv = {bload};\n        \
                 {cstore}\n      }}",
                j_init = if reshape == Reshape::JCarriedAcrossK {
                    ""
                } else {
                    "uint64_t j = 0"
                },
            )
        };
        // The reshaped nests' extra checks of an exited loop's index.
        let stale_c = if reshape == Reshape::StaleCIndex {
            format!("if (!((i * {n} + {n}) < {l_c})) return -1;")
        } else {
            String::new()
        };
        let stale_a = if reshape == Reshape::StaleAIndex {
            format!("\n    if (!((i * {kd} + {kd}) < {l_a})) return -1;")
        } else {
            String::new()
        };
        let _ = writeln!(
            s,
            "    {j_outer}for ({k_init}; k < {kd}; k++) {{\n      \
             uint64_t aidx = i * {kd} + k; if (!(aidx < {l_a})) return -1;\n      \
             {data} aik = {aload};\n      \
             {j_loop}\n      \
             {record_last}{stale_c}\n    }}{stale_a}",
            j_outer = if reshape == Reshape::JCarriedAcrossK {
                "uint64_t j = 0;\n    "
            } else {
                ""
            },
            k_init = if reshape == Reshape::KCarriedAcrossI {
                ""
            } else {
                "uint64_t k = 0"
            },
        );
    }
    let _ = writeln!(s, "  }}\n  }}");
    if !k.direct_ptrs {
        let _ = writeln!(
            s,
            "  for (uint64_t t = 0; t < {lio}; t++) (({cell}*)p2)[t] = c[t];",
            lio = k.len_c_io()
        );
    }
    let _ = writeln!(
        s,
        "  return {};\n}}",
        if k.live_out { "(int64_t)last" } else { "0" }
    );
    s
}

const DRIVER_PRELUDE: &str = r#"
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>

typedef int64_t (*kfn)(void*, void*, void*);
typedef struct {
    const char* name;
    uint64_t es, la, lb, lc, fill;
    int direct;
    uint64_t alias_off;
    int has_sentinel;
    uint64_t sentinel_at, sentinel;
    kfn f[5];
} kcase;

static const char* COLUMN[5] = {"reference", "on_o2", "off_o2", "on_o3", "off_o3"};
#define CANARY 64

/* The matmulfuzz fill: a xorshift stream with 0, all-ones, MIN, MAX, 1 and 2
   planted every 17 elements. Family 1 is the 32-bit form; family 2 draws
   exact eighths in [-125, 125] so no rounding ever occurs. */
static void fill(unsigned char* p, uint64_t n, uint64_t fam, uint64_t seed) {
    uint64_t s = seed ? seed : 1;
    for (uint64_t i = 0; i < n; i++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        uint64_t r = (i * 7 + seed % 17) % 17;
        if (fam == 1) {
            uint32_t v = (uint32_t)s;
            if (r == 0) v = 0; else if (r == 1) v = 0xffffffffu; else if (r == 2) v = 0x80000000u;
            else if (r == 3) v = 0x7fffffffu; else if (r == 4) v = 1; else if (r == 5) v = 2;
            memcpy(p + 4 * i, &v, 4);
        } else if (fam == 2) {
            double d = (double)((int64_t)(s % 2001) - 1000) * 0.125;
            memcpy(p + 8 * i, &d, 8);
        } else {
            uint64_t v = s;
            if (r == 0) v = 0; else if (r == 1) v = ~0ull; else if (r == 2) v = 1ull << 63;
            else if (r == 3) v = ~0ull >> 1; else if (r == 4) v = 1; else if (r == 5) v = 2;
            memcpy(p + 8 * i, &v, 8);
        }
    }
}

/* Buffers are shared mappings, so writes a column makes in its forked child
   are visible to the comparison. */
static unsigned char* buffer(uint64_t bytes) {
    unsigned char* p = mmap(0, bytes + CANARY, PROT_READ | PROT_WRITE,
                            MAP_SHARED | MAP_ANON, -1, 0);
    if (p == MAP_FAILED) { perror("mmap"); exit(2); }
    memset(p + bytes, 0xa5, CANARY);
    return p;
}

static void release(unsigned char* p, uint64_t bytes) { munmap(p, bytes + CANARY); }

static void on_trap(int sig) { _exit(100 + sig); }

/* Run one column in a child: 0 when it returned (the value in *ret), the
   signal number when it trapped, -1 for any other end. A caught signal exits
   the child normally, so no crash report or core file is written. */
static int call_column(kfn f, void* p0, void* p1, void* p2, int64_t* ret) {
    int64_t* slot = mmap(0, sizeof *slot, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANON, -1, 0);
    if (slot == MAP_FAILED) { perror("mmap"); exit(2); }
    fflush(stdout);
    pid_t pid = fork();
    if (pid < 0) { perror("fork"); exit(2); }
    if (pid == 0) {
        struct rlimit none = {0, 0};
        setrlimit(RLIMIT_CORE, &none);
        signal(SIGTRAP, on_trap); signal(SIGILL, on_trap);
        signal(SIGSEGV, on_trap); signal(SIGBUS, on_trap);
        *slot = f(p0, p1, p2);
        _exit(0);
    }
    int status = 0, outcome = -1;
    if (waitpid(pid, &status, 0) != pid) { perror("waitpid"); exit(2); }
    if (WIFEXITED(status) && WEXITSTATUS(status) == 0) { *ret = *slot; outcome = 0; }
    else if (WIFEXITED(status) && WEXITSTATUS(status) > 100) outcome = WEXITSTATUS(status) - 100;
    munmap(slot, sizeof *slot);
    return outcome;
}

static int canary_intact(const unsigned char* p, uint64_t bytes) {
    for (uint64_t i = 0; i < CANARY; i++) if (p[bytes + i] != 0xa5) return 0;
    return 1;
}

static uint64_t first_diff(const unsigned char* x, const unsigned char* y, uint64_t bytes) {
    for (uint64_t i = 0; i < bytes; i++) if (x[i] != y[i]) return i;
    return bytes;
}

/* Runs whose reference trapped; the branch-form kernels never trap. */
static unsigned trapping_runs;

static int run_case(const kcase* k, uint64_t seed, int plant) {
    /* Direct kernels get one a/c buffer with c at an element offset (c
       overlapping a); the others get three buffers. */
    uint64_t ab = k->la * k->es, bb = k->lb * k->es;
    uint64_t cb = k->direct ? 0 : k->lc * k->es;
    if (k->direct) {
        uint64_t end = (k->alias_off + k->lc) * k->es;
        if (end > ab) ab = end;
    }
    unsigned char *a0 = buffer(ab), *b0 = buffer(bb), *c0 = buffer(cb);
    fill(a0, ab / k->es, k->fill, seed);
    fill(b0, bb / k->es, k->fill, seed * 3 + 1);
    fill(c0, cb / k->es, k->fill, seed * 5 + 2);
    if (plant && k->has_sentinel) memcpy(c0 + k->sentinel_at * k->es, &k->sentinel, k->es);
    unsigned char *a[5], *b[5], *c[5];
    int64_t ret[5] = {0, 0, 0, 0, 0};
    int outcome[5];
    int bad = 0;
    for (int v = 0; v < 5; v++) {
        a[v] = buffer(ab); b[v] = buffer(bb); c[v] = buffer(cb);
        memcpy(a[v], a0, ab); memcpy(b[v], b0, bb); memcpy(c[v], c0, cb);
        if (k->direct)
            outcome[v] = call_column(k->f[v], a[v], b[v], a[v] + k->alias_off * k->es, &ret[v]);
        else
            outcome[v] = call_column(k->f[v], a[v], b[v], c[v], &ret[v]);
        if (outcome[v] < 0) {
            printf("CRASH %s seed=%llu %s ended abnormally\n", k->name,
                   (unsigned long long)seed, COLUMN[v]);
            bad = 1;
        }
        if (!canary_intact(a[v], ab) || !canary_intact(b[v], bb) || !canary_intact(c[v], cb)) {
            printf("CANARY %s seed=%llu %s wrote past a buffer\n", k->name,
                   (unsigned long long)seed, COLUMN[v]);
            bad = 1;
        }
    }
    if (outcome[0] > 0) trapping_runs++;
    for (int v = 1; v < 5; v++) {
        uint64_t da = first_diff(a[0], a[v], ab), db = first_diff(b[0], b[v], bb);
        uint64_t dc = first_diff(c[0], c[v], cb);
        if (outcome[v] != outcome[0] || ret[v] != ret[0] || da != ab || db != bb || dc != cb) {
            printf("MISMATCH %s seed=%llu %s: trap signal %d vs reference %d, ret %lld vs "
                   "reference %lld; first differing byte a=%llu/%llu b=%llu/%llu c=%llu/%llu\n",
                   k->name, (unsigned long long)seed, COLUMN[v], outcome[v], outcome[0],
                   (long long)ret[v], (long long)ret[0], (unsigned long long)da, (unsigned long long)ab,
                   (unsigned long long)db, (unsigned long long)bb, (unsigned long long)dc,
                   (unsigned long long)cb);
            bad = 1;
        }
    }
    for (int v = 0; v < 5; v++) { release(a[v], ab); release(b[v], bb); release(c[v], cb); }
    release(a0, ab); release(b0, bb); release(c0, cb);
    return bad;
}
"#;

/// The C driver running every kernel's four builds against its reference on
/// three seeds (the last one plants the early-exit sentinel).
#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
fn c_driver(kernels: &[Kernel]) -> String {
    let mut s = String::from(DRIVER_PRELUDE);
    for k in kernels {
        let _ = writeln!(s, "int64_t ref_{}(void*, void*, void*);", k.name);
        for (_, _, tag) in BUILDS {
            let _ = writeln!(s, "int64_t {}_{tag}(void*, void*, void*);", k.name);
        }
    }
    s.push_str("static const kcase CASES[] = {\n");
    for k in kernels {
        let _ = writeln!(
            s,
            "  {{\"{name}\", {es}, {la}, {lb}, {lc}, {fill}, {direct}, {off}, {has}, {at}, {sent}ull, \
             {{ref_{name}, {name}_on_o2, {name}_off_o2, {name}_on_o3, {name}_off_o3}}}},",
            name = k.name,
            es = k.elem.cell_bytes(),
            la = k.len_a(),
            lb = k.len_b(),
            lc = if k.direct_ptrs {
                k.m * k.n
            } else {
                k.len_c_io()
            },
            fill = k.elem.fill(),
            direct = i32::from(k.direct_ptrs),
            off = k.alias_offset().unwrap_or(0),
            has = i32::from(k.early_exit),
            at = k.sentinel_at().unwrap_or(0),
            sent = SENTINEL,
        );
    }
    s.push_str(
        "};\n\
         int main(void) {\n\
           static const uint64_t SEEDS[3] = {0x9e3779b97f4a7c15ull, 0x85ebca6b1b873593ull, 0xc2b2ae3d27d4eb4full};\n\
           int bad = 0; unsigned runs = 0;\n\
           for (unsigned i = 0; i < sizeof CASES / sizeof CASES[0]; i++)\n\
             for (int s = 0; s < 3; s++) { bad |= run_case(&CASES[i], SEEDS[s], s == 2); runs++; }\n\
           printf(\"mac-reg-block differential: %u kernel runs x 5 columns, %u trapping, %s\\n\", runs, trapping_runs, bad ? \"MISMATCH\" : \"all equal\");\n\
           return bad;\n\
         }\n",
    );
    s
}

/// Compile every kernel (checking the firing contract), link the objects
/// with the C reference and driver, run it, and require every build to
/// match the reference byte for byte. `trapping` is the number of kernel
/// runs whose reference must trap (and every build with it).
#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
fn run_differential(tag: &str, kernels: &[Kernel], trapping: usize) {
    use std::process::Command;

    let dir = fresh_dir::create(&format!("trust_cg_mrb_{tag}_"));
    let mut objects = Vec::new();
    let mut reference = String::from("#include <stdint.h>\n");
    for k in kernels {
        for (symbol, compiled) in compile_all_builds(k) {
            let path = dir.join(format!("{symbol}.o"));
            std::fs::write(&path, &compiled.object).expect("write object");
            objects.push(path);
        }
        reference.push_str(&c_reference(k));
    }
    let ref_c = dir.join("reference.c");
    let ref_o = dir.join("reference.o");
    let driver_c = dir.join("driver.c");
    let binary = dir.join("differential");
    std::fs::write(&ref_c, reference).expect("write reference");
    std::fs::write(&driver_c, c_driver(kernels)).expect("write driver");
    let cc = Command::new(native_host::C_COMPILER)
        .args(["-O2", "-ffp-contract=off", "-c"])
        .arg(&ref_c)
        .arg("-o")
        .arg(&ref_o)
        .output()
        .expect("run the C compiler");
    assert!(
        cc.status.success(),
        "C reference:\n{}",
        String::from_utf8_lossy(&cc.stderr)
    );
    let link = Command::new(native_host::C_COMPILER)
        .arg("-O1")
        .arg(&driver_c)
        .arg(&ref_o)
        .args(&objects)
        .args(native_host::link_hardening_args())
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("run the linker");
    assert!(
        link.status.success(),
        "link:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = Command::new(&binary)
        .output()
        .expect("run the differential");
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        run.status.success(),
        "{tag}: native results differ from the C reference (scratch kept at {}):\n{stdout}{}",
        dir.display(),
        String::from_utf8_lossy(&run.stderr)
    );
    assert!(stdout.contains("all equal"), "{tag}: {stdout}");
    assert!(
        stdout.contains(&format!(" {trapping} trapping,")),
        "{tag}: expected {trapping} trapping runs: {stdout}"
    );
    eprintln!(
        "{tag}: {} kernels on {}: {stdout}",
        kernels.len(),
        native_host::HOST
    );
    let _ = std::fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// Host-neutral compile checks (every host, native-triple objects)
// ---------------------------------------------------------------------------

/// Every admitted nest is rewritten exactly once at O2 and at O3, the
/// in-process disable list unschedules the pass, and the rewritten code
/// differs from the scalar code (carrying the fast path's `ldp` row
/// post-increment where the writeback shape encodes).
#[test]
fn admitted_nests_are_rewritten_exactly_once() {
    let kernels = admitted_kernels();
    // N in {8, 12, 16, 24, 32, 36, 56, 64, 72, 128} plus the outer-repeat shape.
    assert_eq!(kernels.iter().filter(|k| k.fires).count(), 11);
    for k in &kernels {
        compile_all_builds(k);
    }
}

/// Shapes outside the envelope and every negative control are left
/// untransformed: zero rewrites, identical code ON and OFF.
#[test]
fn negative_controls_are_left_untransformed() {
    let kernels = untransformed_kernels();
    assert!(kernels.iter().all(|k| !k.fires));
    for k in &kernels {
        compile_all_builds(k);
    }
}

// ---------------------------------------------------------------------------
// Native differentials (AArch64 Linux GNU and macOS hosts)
// ---------------------------------------------------------------------------

/// Admitted nests: pass ON and OFF at O2 and O3 all equal the C reference.
#[cfg_attr(
    any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    ),
    test
)]
#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
fn admitted_nests_match_the_c_reference_on_and_off() {
    run_differential("admitted", &admitted_kernels(), 0);
}

/// Negative controls still compute the reference result in every build.
#[cfg_attr(
    any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    ),
    test
)]
#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
fn negative_controls_match_the_c_reference_on_and_off() {
    run_differential("negative", &untransformed_kernels(), 0);
}

/// The ported matmulfuzz sweep: both loop orders over edge and fixed-seed
/// random sizes, firing exactly on the admitted ikj sizes.
#[cfg_attr(
    any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    ),
    test
)]
#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
fn seeded_size_sweep_matches_the_c_reference() {
    let kernels = sweep_kernels();
    assert_eq!(kernels.len(), 28);
    assert!(
        kernels.iter().any(|k| k.fires),
        "the sweep must sample the admitted path"
    );
    run_differential("sweep", &kernels, 0);
}

// ---------------------------------------------------------------------------
// The rustc bridge's pre-v52 check spelling: admission controls (TrustIR v52)
// ---------------------------------------------------------------------------

/// `main` of benchmarks/beat-llvm/progs/p4_matmul.rs as the rustc bridge
/// lowered it to trust-ir before TrustIR v52 (trustc 1.99.0-dev
/// `321aaeda7`, Trust package 9192, `-Copt-level=3 -Cpanic=abort`, printed
/// from the module the bridge handed to the `Compiler` on 2026-09-28), with
/// three edits: the repetition count `bb(20_000u32)` is the parameter `%0`,
/// the exit block returns `acc` instead of calling `done`
/// (`process::exit(acc % 126)`), and the calls to the array-fill helper
/// `__trustcg_array_fill_i64` name the external `p4_fill_i64` (function 1).
/// The `[0i64; 576]` arrays are three allocas, every index is a `const` +
/// `icmp ult` + kindless `assert` check (the first one, in block order, is
/// the 37-stride read of `c` in `bb20`), element addresses are `ptrtoint` +
/// `mul` + `add` + `inttoptr`, and the outer loop's values are threaded
/// through the inner loops as block parameters.
const P4_PRE_V52_BRIDGE_MAIN: &str = r#"fn @{SYMBOL}(functy.0) {
bb0(%0: u32):
    %77 = alloca [ty.0 x 576], align 8
    %78 = alloca [ty.0 x 576], align 8
    %79 = alloca [ty.0 x 576], align 8
    %80 = const u64 3
    br bb24
bb24:
    %81 = const i64 0
    %82 = copy i64 %81
    %83 = const i64 576
    call @func.1(%77, %82, %83)
    %84 = const i64 0
    %85 = copy i64 %84
    %86 = const i64 576
    call @func.1(%78, %85, %86)
    %87 = const u64 0
    br bb1(%80, %87)
bb1(%88: u64, %89: u64):
    %90 = copy u64 %89
    %92 = const u64 576
    %91 = icmp ult u64 %90, %92
    condbr %91, bb2, bb5
bb5:
    %93 = copy u32 %0
    br bb25
bb25:
    %94 = const i64 0
    %95 = const u32 0
    br bb6(%93, %94, %95)
bb6(%96: u32, %97: i64, %98: u32):
    %99 = copy u32 %98
    %100 = icmp ult u32 %99, %96
    condbr %100, bb7, bb23
bb23:
    ret %97
bb7:
    %102 = const i64 0
    %103 = copy i64 %102
    %104 = const i64 576
    call @func.1(%79, %103, %104)
    %105 = const u64 0
    br bb8(%96, %97, %98, %105)
bb8(%106: u32, %107: i64, %108: u32, %109: u64):
    %110 = copy u64 %109
    %112 = const u64 24
    %111 = icmp ult u64 %110, %112
    condbr %111, bb9, bb20
bb20:
    %113 = copy u32 %108
    %114 = zext u32 %113 to u64
    %116 = const u64 37
    %115 = mul u64 %114, %116
    %118 = const u64 576
    %117 = urem u64 %115, %118
    %120 = const u64 576
    %119 = icmp ult u64 %117, %120
    assert %119
    br bb21
bb21:
    %122 = copy ptr %79
    %123 = ptrtoint ptr %122 to i64
    %124 = bitcast u64 %117 to i64
    %125 = const i64 8
    %126 = mul i64 %124, %125
    %127 = add i64 %123, %126
    %128 = inttoptr i64 %127 to ptr
    %121 = load i64, ptr %128
    %129 = add i64 %107, %121
    %130 = copy i64 %129
    %131 = copy i64 %130
    %132 = copy u32 %108
    %133 = zext u32 %132 to u64
    %135 = const u64 13
    %134 = mul u64 %133, %135
    %137 = const u64 576
    %136 = urem u64 %134, %137
    %139 = const u64 576
    %138 = icmp ult u64 %136, %139
    assert %138
    br bb22
bb22:
    %140 = copy ptr %77
    %141 = ptrtoint ptr %140 to i64
    %142 = bitcast u64 %136 to i64
    %143 = const i64 8
    %144 = mul i64 %142, %143
    %145 = add i64 %141, %144
    %146 = inttoptr i64 %145 to ptr
    %148 = const i64 255
    %147 = and i64 %131, %148
    store i64 %147, ptr %146
    %150 = const u32 1
    %149 = add u32 %108, %150
    br bb6(%106, %130, %149)
bb9:
    %151 = const u64 0
    br bb10(%106, %107, %108, %109, %151)
bb10(%152: u32, %153: i64, %154: u32, %155: u64, %156: u64):
    %157 = copy u64 %156
    %159 = const u64 24
    %158 = icmp ult u64 %157, %159
    condbr %158, bb11, bb19
bb19:
    %161 = const u64 1
    %160 = add u64 %155, %161
    br bb8(%152, %153, %154, %160)
bb11:
    %162 = copy u64 %155
    %164 = const u64 24
    %163 = mul u64 %162, %164
    %165 = copy u64 %156
    %166 = add u64 %163, %165
    %168 = const u64 576
    %167 = icmp ult u64 %166, %168
    assert %167
    br bb12
bb12:
    %170 = copy ptr %77
    %171 = ptrtoint ptr %170 to i64
    %172 = bitcast u64 %166 to i64
    %173 = const i64 8
    %174 = mul i64 %172, %173
    %175 = add i64 %171, %174
    %176 = inttoptr i64 %175 to ptr
    %169 = load i64, ptr %176
    %177 = const u64 0
    br bb13(%152, %153, %154, %155, %156, %169, %177)
bb13(%178: u32, %179: i64, %180: u32, %181: u64, %182: u64, %183: i64, %184: u64):
    %185 = copy u64 %184
    %187 = const u64 24
    %186 = icmp ult u64 %185, %187
    condbr %186, bb14, bb18
bb18:
    %189 = const u64 1
    %188 = add u64 %182, %189
    br bb10(%178, %179, %180, %181, %188)
bb14:
    %190 = copy u64 %181
    %192 = const u64 24
    %191 = mul u64 %190, %192
    %193 = copy u64 %184
    %194 = add u64 %191, %193
    %196 = const u64 576
    %195 = icmp ult u64 %194, %196
    assert %195
    br bb15
bb15:
    %198 = copy ptr %79
    %199 = ptrtoint ptr %198 to i64
    %200 = bitcast u64 %194 to i64
    %201 = const i64 8
    %202 = mul i64 %200, %201
    %203 = add i64 %199, %202
    %204 = inttoptr i64 %203 to ptr
    %197 = load i64, ptr %204
    %205 = copy u64 %182
    %207 = const u64 24
    %206 = mul u64 %205, %207
    %208 = copy u64 %184
    %209 = add u64 %206, %208
    %211 = const u64 576
    %210 = icmp ult u64 %209, %211
    assert %210
    br bb16
bb16:
    %213 = copy ptr %78
    %214 = ptrtoint ptr %213 to i64
    %215 = bitcast u64 %209 to i64
    %216 = const i64 8
    %217 = mul i64 %215, %216
    %218 = add i64 %214, %217
    %219 = inttoptr i64 %218 to ptr
    %212 = load i64, ptr %219
    %220 = mul i64 %183, %212
    %221 = add i64 %197, %220
    %222 = copy u64 %181
    %224 = const u64 24
    %223 = mul u64 %222, %224
    %225 = copy u64 %184
    %226 = add u64 %223, %225
    %228 = const u64 576
    %227 = icmp ult u64 %226, %228
    assert %227
    br bb17
bb17:
    %229 = copy ptr %79
    %230 = ptrtoint ptr %229 to i64
    %231 = bitcast u64 %226 to i64
    %232 = const i64 8
    %233 = mul i64 %231, %232
    %234 = add i64 %230, %233
    %235 = inttoptr i64 %234 to ptr
    %236 = copy i64 %221
    store i64 %236, ptr %235
    %238 = const u64 1
    %237 = add u64 %184, %238
    br bb13(%178, %179, %180, %181, %182, %183, %237)
bb2:
    %239 = copy u64 %89
    %240 = copy u64 %239
    %241 = mul u64 %240, %88
    %243 = const u64 7
    %242 = add u64 %241, %243
    %245 = const u64 100
    %244 = urem u64 %242, %245
    %246 = copy u64 %89
    %248 = const u64 576
    %247 = icmp ult u64 %246, %248
    assert %247
    br bb3
bb3:
    %249 = copy ptr %77
    %250 = ptrtoint ptr %249 to i64
    %251 = bitcast u64 %246 to i64
    %252 = const i64 8
    %253 = mul i64 %251, %252
    %254 = add i64 %250, %253
    %255 = inttoptr i64 %254 to ptr
    %256 = bitcast u64 %244 to i64
    store i64 %256, ptr %255
    %257 = copy u64 %89
    %258 = copy u64 %257
    %260 = const u64 11
    %259 = add u64 %88, %260
    %261 = mul u64 %258, %259
    %263 = const u64 3
    %262 = add u64 %261, %263
    %265 = const u64 100
    %264 = urem u64 %262, %265
    %266 = copy u64 %89
    %268 = const u64 576
    %267 = icmp ult u64 %266, %268
    assert %267
    br bb4
bb4:
    %269 = copy ptr %78
    %270 = ptrtoint ptr %269 to i64
    %271 = bitcast u64 %266 to i64
    %272 = const i64 8
    %273 = mul i64 %271, %272
    %274 = add i64 %270, %273
    %275 = inttoptr i64 %274 to ptr
    %276 = bitcast u64 %264 to i64
    store i64 %276, ptr %275
    %278 = const u64 1
    %277 = add u64 %89, %278
    br bb1(%88, %277)
}"#;

/// The module holding the pre-v52 p4 kernel under `symbol`.
fn p4_module(symbol: &str) -> trust_ir::Module {
    let text = format!(
        "; TrustIr text format v1\nmodule \"mrb_p4\"\ntarget \"{}\" 8 little abi=\"aapcs64\"\n\n\
         functy.0 = (u32) -> (i64)\n\nfuncty.1 = (ptr, i64, i64) -> ()\n\ntype ty.0 = i64\n\n\
         {}\nfn @p4_fill_i64(functy.1) {{\n}}\n",
        native_host::TRIPLE,
        P4_PRE_V52_BRIDGE_MAIN.replace("{SYMBOL}", symbol)
    );
    trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|error| panic!("{symbol}: trust-ir parse: {error:?}\n{text}"))
}

/// The levels at which `mac-reg-block` is scheduled.
const PASS_LEVELS: [OptLevel; 2] = [OptLevel::O2, OptLevel::O3];

fn assert_form(kernels: &[Kernel]) -> Vec<Kernel> {
    kernels.iter().map(Kernel::in_assert_form).collect()
}

/// Every module in the pre-v52 bridge check spelling with the symbol of its
/// function and the coordinate of that function's first kindless `assert`,
/// where the shared floor refuses it: each kernel list above as `tr_`
/// kernels (the a check, or the c check in the ijk order, at `bb8`), then
/// the pre-v52 p4_matmul nest.
fn pre_v52_bridge_form_modules() -> Vec<(String, &'static str, trust_ir::Module)> {
    let mut kernels = assert_form(&admitted_kernels());
    kernels.extend(assert_form(&untransformed_kernels()));
    kernels.extend(assert_form(&sweep_kernels()));
    // 16 kernels in the modeled shape, 17 left untransformed in the branch
    // form, and the 28-kernel sweep.
    assert_eq!(kernels.len(), 61);
    let mut modules: Vec<(String, &'static str, trust_ir::Module)> = kernels
        .iter()
        .map(|k| {
            // The stale-a-index nest computes the a index in the k-header.
            let first = if k.reshape == Reshape::StaleAIndex {
                "bb8#2"
            } else {
                "bb8#4"
            };
            (k.name.clone(), first, module(k, &k.name))
        })
        .collect();
    modules.push(("p4_matmul".into(), "bb20#8", p4_module("p4_matmul")));
    modules
}

/// The shared floor's refusal of `symbol`'s first kindless `assert`, at
/// `first`, on the compile path `route`.
fn assert_floor_refusal(
    symbol: &str,
    first: &str,
    route: &str,
    opt: OptLevel,
    error: impl std::fmt::Display,
) {
    let text = error.to_string();
    for needle in [
        "trust-ir codegen admission refused the module".to_string(),
        format!("fn {symbol}: {first}: assert of unspecified panic kind"),
        "(require_assert_panic_kinds)".to_string(),
    ] {
        assert!(
            text.contains(&needle),
            "{symbol} {route} {opt:?}: the refusal must contain {needle:?}: {text}"
        );
    }
}

/// Every kernel in the pre-v52 bridge check spelling and the pre-v52
/// p4_matmul nest are refused at admission on the object path at O2 and O3.
#[test]
fn pre_v52_bridge_form_is_refused_at_object_admission() {
    for (symbol, first, module) in pre_v52_bridge_form_modules() {
        for opt_level in PASS_LEVELS {
            let config = CompilerConfig {
                target: Target::Aarch64,
                opt_level,
                ..CompilerConfig::default()
            };
            let Err(error) = Compiler::new(config)
                .with_codegen_license(permit_unlicensed())
                .compile(&module)
            else {
                panic!("{symbol} object {opt_level:?}: a kindless source assert was admitted");
            };
            assert_floor_refusal(&symbol, first, "object", opt_level, error);
        }
    }
}

/// Every kernel in the pre-v52 bridge check spelling and the pre-v52
/// p4_matmul nest are refused at admission on the JIT path at O2 and O3,
/// before any code is installed. The JIT compiles only for its host, so this
/// runs on the native hosts.
#[cfg_attr(
    any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    ),
    test
)]
#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
fn pre_v52_bridge_form_is_refused_before_jit_installation() {
    for (symbol, first, module) in pre_v52_bridge_form_modules() {
        for opt_level in PASS_LEVELS {
            let mut config = CompilerConfig::jit_fast(Target::Aarch64);
            config.opt_level = opt_level;
            let Err(error) = Compiler::new(config)
                .with_codegen_license(permit_unlicensed())
                .compile_module_to_jit(&module, &std::collections::HashMap::new())
            else {
                panic!("{symbol} JIT {opt_level:?}: a kindless source assert was admitted");
            };
            assert_floor_refusal(&symbol, first, "JIT", opt_level, error);
        }
    }
}

// ---------------------------------------------------------------------------
// The current rustc bridge's p4_matmul nest: compare and branch to a raise
// ---------------------------------------------------------------------------

/// `core::panicking::panic_bounds_check` as the Trust package 9192 sysroot
/// mangles it; the bridge's raise blocks call it by this name.
const PANIC_BOUNDS_CHECK: &str = "_RNvNtCsiHPWGBzRfGA_4core9panicking18panic_bounds_check";

/// The declarations of the module the current rustc bridge hands to the
/// `Compiler` for `main` of benchmarks/beat-llvm/progs/p4_matmul.rs: one
/// 24-byte `core::panic::Location` constant per index check (file pointer,
/// file length, line, column) over one file-name string. Two edits match
/// `P4_BRIDGE_MAIN`'s: `functy.0` is `(u32) -> (i64)` (the bridge's `main`
/// is `() -> ()`), and `done`'s `(u64) -> ()` is dropped, so the panic
/// entry's `(usize, usize, &Location)` is `functy.2`.
const P4_BRIDGE_DECLS: &str = r#"struct @_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc75.allocation { part0: ptr @0, part1: [ty.5 x 16] @8 } size=24 align=1 repr=packed(1) id=0

struct @_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc76.allocation { part0: ptr @0, part1: [ty.5 x 16] @8 } size=24 align=1 repr=packed(1) id=1

struct @_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc77.allocation { part0: ptr @0, part1: [ty.5 x 16] @8 } size=24 align=1 repr=packed(1) id=2

struct @_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc78.allocation { part0: ptr @0, part1: [ty.5 x 16] @8 } size=24 align=1 repr=packed(1) id=3

struct @_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc79.allocation { part0: ptr @0, part1: [ty.5 x 16] @8 } size=24 align=1 repr=packed(1) id=4

struct @_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc80.allocation { part0: ptr @0, part1: [ty.5 x 16] @8 } size=24 align=1 repr=packed(1) id=5

struct @_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc81.allocation { part0: ptr @0, part1: [ty.5 x 16] @8 } size=24 align=1 repr=packed(1) id=6

struct @_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc82.allocation { part0: ptr @0, part1: [ty.5 x 16] @8 } size=24 align=1 repr=packed(1) id=7

functy.0 = (u32) -> (i64)

functy.1 = (ptr, i64, i64) -> ()

functy.2 = (u64, u64, &[ty.3 x 3]) -> ()

type ty.0 = i8

type ty.1 = i16

type ty.2 = i32

type ty.3 = i64

type ty.4 = i128

type ty.5 = u8

global internal align(8) @_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc75 struct.0 = { symaddr<_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc74>, bytes<27000000000000002300000020000000> }

global internal align(1) @_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc74 [ty.5 x 40] = bytes<62656e63686d61726b732f626561742d6c6c766d2f70726f67732f70345f6d61746d756c2e727300>

global internal align(8) @_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc76 struct.1 = { symaddr<_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc74>, bytes<27000000000000002400000009000000> }

global internal align(8) @_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc77 struct.2 = { symaddr<_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc74>, bytes<2700000000000000190000001b000000> }

global internal align(8) @_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc78 struct.3 = { symaddr<_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc74>, bytes<27000000000000001c00000024000000> }

global internal align(8) @_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc79 struct.4 = { symaddr<_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc74>, bytes<27000000000000001c0000004f000000> }

global internal align(8) @_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc80 struct.5 = { symaddr<_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc74>, bytes<27000000000000001c00000015000000> }

global internal align(8) @_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc81 struct.6 = { symaddr<_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc74>, bytes<27000000000000000c00000009000000> }

global internal align(8) @_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc82 struct.7 = { symaddr<_RNvCsb6fFRicCy6c_9p4_matmul4main.const.alloc74>, bytes<27000000000000000d00000009000000> }"#;

/// `main` of benchmarks/beat-llvm/progs/p4_matmul.rs as the rustc bridge
/// lowers it to trust-ir under TrustIR v52 (captured 2026-10-01: the bridge
/// sources of 25f0d2efc, trustc 1.99.0-dev `321aaeda7` from Trust package
/// 9192, `--target aarch64-apple-darwin` `-Copt-level=3` `-Cpanic=abort`
/// `-Ztrust-verify=off`, the source named by its repository-relative path,
/// the module written by `-Ztrust-ir-cg-args=dump-trust-ir` and printed by
/// the pinned trust-ir). Every index check is `icmp ult` + `condbr` to a
/// raise block that passes the index, the constant length and the address
/// of its `Location` to `panic_bounds_check` and ends in `unreachable`; no
/// `assert` remains. The pre-v52 capture's three edits are repeated: the
/// repetition count (the bridge folds `bb(20_000u32)` to `const u32 20000`)
/// is the parameter `%0`, the exit block returns `acc` instead of calling
/// `done` (`process::exit(acc % 126)`), and the array-fill helper
/// `__trustcg_array_fill_i64` is the external `p4_fill_i64`. The dump
/// numbers its functions 0, 2, 3 and 4, which the text form cannot carry,
/// so the calls are renumbered: the fill helper `func.2` is `func.1`, and
/// `panic_bounds_check` `func.4` is `func.2`.
const P4_BRIDGE_MAIN: &str = r#"fn @{SYMBOL}(functy.0) {
bb0(%0: u32):
    %77 = alloca [ty.3 x 576], align 8
    %78 = alloca [ty.3 x 576], align 8
    %79 = alloca [ty.3 x 576], align 8
    %80 = const u64 3
    br bb24
bb24:
    %81 = const i64 0
    %82 = copy i64 %81
    %83 = const i64 576
    call @func.1(%77, %82, %83)
    %84 = const i64 0
    %85 = copy i64 %84
    %86 = const i64 576
    call @func.1(%78, %85, %86)
    %87 = const u64 0
    br bb1(%80, %87)
bb1(%88: u64, %89: u64):
    %90 = copy u64 %89
    %92 = const u64 576
    %91 = icmp ult u64 %90, %92
    condbr %91, bb2, bb5
bb5:
    %93 = copy u32 %0
    br bb25
bb25:
    %94 = const i64 0
    %95 = const u32 0
    br bb6(%93, %94, %95)
bb6(%96: u32, %97: i64, %98: u32):
    %99 = copy u32 %98
    %100 = icmp ult u32 %99, %96
    condbr %100, bb7, bb23
bb23:
    ret %97
bb7:
    %102 = const i64 0
    %103 = copy i64 %102
    %104 = const i64 576
    call @func.1(%79, %103, %104)
    %105 = const u64 0
    br bb8(%96, %97, %98, %105)
bb8(%106: u32, %107: i64, %108: u32, %109: u64):
    %110 = copy u64 %109
    %112 = const u64 24
    %111 = icmp ult u64 %110, %112
    condbr %111, bb9, bb20
bb20:
    %113 = copy u32 %108
    %114 = zext u32 %113 to u64
    %116 = const u64 37
    %115 = mul u64 %114, %116
    %118 = const u64 576
    %117 = urem u64 %115, %118
    %120 = const u64 576
    %119 = icmp ult u64 %117, %120
    condbr %119, bb21, bb27
bb27:
    %121 = const u64 576
    %122 = global_addr @global.0
    %123 = ptrtoptr ptr %122 to &[ty.3 x 3]
    call @func.2(%117, %121, %123)
    unreachable
bb21:
    %125 = copy ptr %79
    %126 = ptrtoint ptr %125 to i64
    %127 = bitcast u64 %117 to i64
    %128 = const i64 8
    %129 = mul i64 %127, %128
    %130 = add i64 %126, %129
    %131 = inttoptr i64 %130 to ptr
    %124 = load i64, ptr %131
    %132 = add i64 %107, %124
    %133 = copy i64 %132
    %134 = copy i64 %133
    %135 = copy u32 %108
    %136 = zext u32 %135 to u64
    %138 = const u64 13
    %137 = mul u64 %136, %138
    %140 = const u64 576
    %139 = urem u64 %137, %140
    %142 = const u64 576
    %141 = icmp ult u64 %139, %142
    condbr %141, bb22, bb28
bb28:
    %143 = const u64 576
    %144 = global_addr @global.2
    %145 = ptrtoptr ptr %144 to &[ty.3 x 3]
    call @func.2(%139, %143, %145)
    unreachable
bb22:
    %146 = copy ptr %77
    %147 = ptrtoint ptr %146 to i64
    %148 = bitcast u64 %139 to i64
    %149 = const i64 8
    %150 = mul i64 %148, %149
    %151 = add i64 %147, %150
    %152 = inttoptr i64 %151 to ptr
    %154 = const i64 255
    %153 = and i64 %134, %154
    store i64 %153, ptr %152
    %156 = const u32 1
    %155 = add u32 %108, %156
    br bb6(%106, %133, %155)
bb9:
    %157 = const u64 0
    br bb10(%106, %107, %108, %109, %157)
bb10(%158: u32, %159: i64, %160: u32, %161: u64, %162: u64):
    %163 = copy u64 %162
    %165 = const u64 24
    %164 = icmp ult u64 %163, %165
    condbr %164, bb11, bb19
bb19:
    %167 = const u64 1
    %166 = add u64 %161, %167
    br bb8(%158, %159, %160, %166)
bb11:
    %168 = copy u64 %161
    %170 = const u64 24
    %169 = mul u64 %168, %170
    %171 = copy u64 %162
    %172 = add u64 %169, %171
    %174 = const u64 576
    %173 = icmp ult u64 %172, %174
    condbr %173, bb12, bb29
bb29:
    %175 = const u64 576
    %176 = global_addr @global.3
    %177 = ptrtoptr ptr %176 to &[ty.3 x 3]
    call @func.2(%172, %175, %177)
    unreachable
bb12:
    %179 = copy ptr %77
    %180 = ptrtoint ptr %179 to i64
    %181 = bitcast u64 %172 to i64
    %182 = const i64 8
    %183 = mul i64 %181, %182
    %184 = add i64 %180, %183
    %185 = inttoptr i64 %184 to ptr
    %178 = load i64, ptr %185
    %186 = const u64 0
    br bb13(%158, %159, %160, %161, %162, %178, %186)
bb13(%187: u32, %188: i64, %189: u32, %190: u64, %191: u64, %192: i64, %193: u64):
    %194 = copy u64 %193
    %196 = const u64 24
    %195 = icmp ult u64 %194, %196
    condbr %195, bb14, bb18
bb18:
    %198 = const u64 1
    %197 = add u64 %191, %198
    br bb10(%187, %188, %189, %190, %197)
bb14:
    %199 = copy u64 %190
    %201 = const u64 24
    %200 = mul u64 %199, %201
    %202 = copy u64 %193
    %203 = add u64 %200, %202
    %205 = const u64 576
    %204 = icmp ult u64 %203, %205
    condbr %204, bb15, bb30
bb30:
    %206 = const u64 576
    %207 = global_addr @global.4
    %208 = ptrtoptr ptr %207 to &[ty.3 x 3]
    call @func.2(%203, %206, %208)
    unreachable
bb15:
    %210 = copy ptr %79
    %211 = ptrtoint ptr %210 to i64
    %212 = bitcast u64 %203 to i64
    %213 = const i64 8
    %214 = mul i64 %212, %213
    %215 = add i64 %211, %214
    %216 = inttoptr i64 %215 to ptr
    %209 = load i64, ptr %216
    %217 = copy u64 %191
    %219 = const u64 24
    %218 = mul u64 %217, %219
    %220 = copy u64 %193
    %221 = add u64 %218, %220
    %223 = const u64 576
    %222 = icmp ult u64 %221, %223
    condbr %222, bb16, bb31
bb31:
    %224 = const u64 576
    %225 = global_addr @global.5
    %226 = ptrtoptr ptr %225 to &[ty.3 x 3]
    call @func.2(%221, %224, %226)
    unreachable
bb16:
    %228 = copy ptr %78
    %229 = ptrtoint ptr %228 to i64
    %230 = bitcast u64 %221 to i64
    %231 = const i64 8
    %232 = mul i64 %230, %231
    %233 = add i64 %229, %232
    %234 = inttoptr i64 %233 to ptr
    %227 = load i64, ptr %234
    %235 = mul i64 %192, %227
    %236 = add i64 %209, %235
    %237 = copy u64 %190
    %239 = const u64 24
    %238 = mul u64 %237, %239
    %240 = copy u64 %193
    %241 = add u64 %238, %240
    %243 = const u64 576
    %242 = icmp ult u64 %241, %243
    condbr %242, bb17, bb32
bb32:
    %244 = const u64 576
    %245 = global_addr @global.6
    %246 = ptrtoptr ptr %245 to &[ty.3 x 3]
    call @func.2(%241, %244, %246)
    unreachable
bb17:
    %247 = copy ptr %79
    %248 = ptrtoint ptr %247 to i64
    %249 = bitcast u64 %241 to i64
    %250 = const i64 8
    %251 = mul i64 %249, %250
    %252 = add i64 %248, %251
    %253 = inttoptr i64 %252 to ptr
    %254 = copy i64 %236
    store i64 %254, ptr %253
    %256 = const u64 1
    %255 = add u64 %193, %256
    br bb13(%187, %188, %189, %190, %191, %192, %255)
bb2:
    %257 = copy u64 %89
    %258 = copy u64 %257
    %259 = mul u64 %258, %88
    %261 = const u64 7
    %260 = add u64 %259, %261
    %263 = const u64 100
    %262 = urem u64 %260, %263
    %264 = copy u64 %89
    %266 = const u64 576
    %265 = icmp ult u64 %264, %266
    condbr %265, bb3, bb33
bb33:
    %267 = const u64 576
    %268 = global_addr @global.7
    %269 = ptrtoptr ptr %268 to &[ty.3 x 3]
    call @func.2(%264, %267, %269)
    unreachable
bb3:
    %270 = copy ptr %77
    %271 = ptrtoint ptr %270 to i64
    %272 = bitcast u64 %264 to i64
    %273 = const i64 8
    %274 = mul i64 %272, %273
    %275 = add i64 %271, %274
    %276 = inttoptr i64 %275 to ptr
    %277 = bitcast u64 %262 to i64
    store i64 %277, ptr %276
    %278 = copy u64 %89
    %279 = copy u64 %278
    %281 = const u64 11
    %280 = add u64 %88, %281
    %282 = mul u64 %279, %280
    %284 = const u64 3
    %283 = add u64 %282, %284
    %286 = const u64 100
    %285 = urem u64 %283, %286
    %287 = copy u64 %89
    %289 = const u64 576
    %288 = icmp ult u64 %287, %289
    condbr %288, bb4, bb34
bb34:
    %290 = const u64 576
    %291 = global_addr @global.8
    %292 = ptrtoptr ptr %291 to &[ty.3 x 3]
    call @func.2(%287, %290, %292)
    unreachable
bb4:
    %293 = copy ptr %78
    %294 = ptrtoint ptr %293 to i64
    %295 = bitcast u64 %287 to i64
    %296 = const i64 8
    %297 = mul i64 %295, %296
    %298 = add i64 %294, %297
    %299 = inttoptr i64 %298 to ptr
    %300 = bitcast u64 %285 to i64
    store i64 %300, ptr %299
    %302 = const u64 1
    %301 = add u64 %89, %302
    br bb1(%88, %301)
}"#;

/// The length every array of `P4_BRIDGE_MAIN` is checked against.
const P4_LEN: u64 = 576;

/// The source location of the nest's `b[k * N + j]` check (the `Location`
/// constant at `@global.5`): file, line, column.
const P4_B_CHECK_LOCATION: (&str, u32, u32) = ("benchmarks/beat-llvm/progs/p4_matmul.rs", 28, 79);

/// The module holding the current bridge's p4 kernel under `symbol`, with the
/// nest's `b[k * N + j]` check (its compare and its raise block's length
/// argument) against `b_len`; `P4_LEN` is the bridge's own nest.
fn p4_bridge_module(symbol: &str, b_len: u64) -> trust_ir::Module {
    let mut main = P4_BRIDGE_MAIN.replace("{SYMBOL}", symbol);
    if b_len != P4_LEN {
        for anchor in ["%223 = const u64 576\n", "%224 = const u64 576\n"] {
            main = anchored(&main, anchor, &anchor.replace("576", &b_len.to_string()));
        }
    }
    let text = format!(
        "; TrustIr text format v1\nmodule \"mrb_p4_bridge\"\ntarget \"{}\" 8 little abi=\"aapcs64\"\n\n\
         {P4_BRIDGE_DECLS}\n\n{main}\n\nfn @p4_fill_i64(functy.1) {{\n}}\n\n\
         fn @{PANIC_BOUNDS_CHECK}(functy.2) {{\n}}\n",
        native_host::TRIPLE,
    );
    trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|error| panic!("{symbol}: trust-ir parse: {error:?}\n{text}"))
}

/// The four builds of the current bridge's p4 kernel (`b_len` as in
/// [`p4_bridge_module`]), named `<tag>_<build>`, each lowered through the
/// shared admission floor, checked against the pass's firing contract with
/// `fires`.
fn p4_bridge_builds(tag: &str, b_len: u64, fires: bool) -> Vec<(String, Prepared)> {
    let builds: Vec<(String, Prepared)> = BUILDS
        .iter()
        .map(|&(opt, on, build)| {
            let symbol = format!("{tag}_{build}");
            let prepared = prepare(&p4_bridge_module(&symbol, b_len), &symbol, opt, on);
            (symbol, prepared)
        })
        .collect();
    let objects: Vec<(String, Compiled)> = builds
        .iter()
        .map(|(symbol, prepared)| (symbol.clone(), prepared.object(symbol)))
        .collect();
    check_firing_contract(tag, fires, 24, &objects);
    builds
}

/// The current bridge's p4_matmul nest is admitted at the shared floor and
/// rewritten exactly once at O2 and at O3, with the 12-lane tile and its
/// `ldp .., #192` row post-increment; the off builds do not schedule the
/// pass. Its copy with the nest's `b` check one element short is left
/// unrewritten, with identical code on and off.
#[test]
fn current_bridge_p4_matmul_nest_is_rewritten_exactly_once() {
    p4_bridge_builds("p4_bridge", P4_LEN, true);
    p4_bridge_builds("p4_bridge_short_b", P4_LEN - 1, false);
}

/// A C transcription of p4_matmul.rs (wrapping u64 arithmetic) that prints
/// its outcome for each repetition count in `REPS` and each `b` check length
/// in `LB`: `R <lb> <reps> <acc>` when it returns, and `P <lb> <reps>
/// <index> <len>` at the first failed `b` check, with the index and length
/// `panic_bounds_check` is passed. The `a` and `c` indices never reach 576,
/// so only the `b` check can fail.
const P4_REFERENCE: &str = r#"
#include <stdint.h>
#include <stdio.h>

static const uint32_t REPS[] = {0, 1, 2, 3, 7, 50, 577, 2000, 20000};
static const uint64_t LB[] = {576, 575};

static int ref_p4(uint32_t reps, uint64_t lb, uint64_t* value, uint64_t* index) {
    const uint64_t seed = 3;
    uint64_t a[576], b[576], c[576];
    for (uint64_t i = 0; i < 576; i++) {
        a[i] = (i * seed + 7) % 100;
        b[i] = (i * (seed + 11) + 3) % 100;
    }
    uint64_t acc = 0;
    for (uint32_t r = 0; r < reps; r++) {
        for (uint64_t t = 0; t < 576; t++) c[t] = 0;
        for (uint64_t i = 0; i < 24; i++)
            for (uint64_t k = 0; k < 24; k++) {
                uint64_t aik = a[i * 24 + k];
                for (uint64_t j = 0; j < 24; j++) {
                    uint64_t bidx = k * 24 + j;
                    if (!(bidx < lb)) { *index = bidx; return 1; }
                    c[i * 24 + j] += aik * b[bidx];
                }
            }
        acc += c[((uint64_t)r * 37) % 576];
        a[((uint64_t)r * 13) % 576] = acc & 0xff;
    }
    *value = acc;
    return 0;
}

int main(void) {
    for (unsigned l = 0; l < sizeof LB / sizeof LB[0]; l++)
        for (unsigned i = 0; i < sizeof REPS / sizeof REPS[0]; i++) {
            uint64_t value = 0, index = 0;
            if (ref_p4(REPS[i], LB[l], &value, &index))
                printf("P %llu %u %llu %llu\n", (unsigned long long)LB[l], REPS[i],
                       (unsigned long long)index, (unsigned long long)LB[l]);
            else
                printf("R %llu %u %lld\n", (unsigned long long)LB[l], REPS[i], (long long)value);
        }
    return 0;
}
"#;

/// How one build ended in its forked child.
#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
#[derive(Clone, Debug, PartialEq, Eq)]
enum Outcome {
    Returned(i64),
    /// The `panic_bounds_check` stub was called, recorded its arguments and
    /// ended the child.
    Panicked {
        index: u64,
        len: u64,
        file: String,
        line: u32,
        column: u32,
    },
    /// The child ended on a signal: a trap, never a Rust panic.
    Signalled(i32),
    /// Any other end (no complete record, an unexpected exit status).
    Other(String),
}

/// The C reference's outcome for each `(b_len, reps)` it prints; a failed
/// check carries the `b` check's source location, which the reference
/// cannot know but the stub must observe.
#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
fn p4_reference_outcomes() -> std::collections::BTreeMap<(u64, u32), Outcome> {
    use std::process::Command;

    let dir = fresh_dir::create("trust_cg_mrb_p4_bridge_");
    let source = dir.join("reference.c");
    let binary = dir.join("reference");
    std::fs::write(&source, P4_REFERENCE).expect("write the reference");
    let cc = Command::new(native_host::C_COMPILER)
        .args(["-O2", "-ffp-contract=off"])
        .arg(&source)
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("run the C compiler");
    assert!(
        cc.status.success(),
        "p4 reference:\n{}",
        String::from_utf8_lossy(&cc.stderr)
    );
    let run = Command::new(&binary)
        .output()
        .expect("run the p4 reference");
    assert!(run.status.success(), "the p4 reference failed: {run:?}");
    let (file, line, column) = P4_B_CHECK_LOCATION;
    let mut outcomes = std::collections::BTreeMap::new();
    for row in String::from_utf8_lossy(&run.stdout).lines() {
        let fields: Vec<&str> = row.split(' ').collect();
        let number = |at: usize| -> u64 { fields[at].parse().expect("a reference number") };
        let outcome = match fields[0] {
            "R" => Outcome::Returned(fields[3].parse().expect("a reference value")),
            "P" => Outcome::Panicked {
                index: number(3),
                len: number(4),
                file: file.to_string(),
                line,
                column,
            },
            other => panic!("unexpected reference row {other:?}: {row}"),
        };
        let reps = u32::try_from(number(2)).expect("a repetition count");
        outcomes.insert((number(1), reps), outcome);
    }
    assert_eq!(outcomes.len(), 18, "two b lengths x nine repetition counts");
    // The benchmark's own exit code `acc % 126` for 20000 repetitions.
    let Outcome::Returned(acc) = outcomes[&(P4_LEN, 20_000)] else {
        panic!("the reference nest must return at 20000 repetitions");
    };
    assert_eq!(acc.cast_unsigned() % 126, 111, "p4_matmul's exit code");
    outcomes
}

/// The forked child that runs one JIT build. Its path is raw FFI calls, the
/// JIT code and the two stubs, ended by `_exit`: no allocation, no lock and
/// no Rust panic, so it is safe after `fork` in the multi-threaded harness.
#[cfg(any(
    all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
    all(target_arch = "aarch64", target_os = "macos")
))]
mod child {
    use super::Outcome;
    use std::ffi::c_void;
    use std::sync::atomic::{AtomicI32, Ordering};

    unsafe extern "C" {
        fn fork() -> i32;
        fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
        fn _exit(status: i32) -> !;
        fn pipe(fds: *mut i32) -> i32;
        fn read(fd: i32, buf: *mut c_void, count: usize) -> isize;
        fn write(fd: i32, buf: *const c_void, count: usize) -> isize;
        fn close(fd: i32) -> i32;
        fn signal(signum: i32, handler: usize) -> usize;
    }

    /// Words of the record a child writes to its pipe: tag, return value or
    /// index, length, line, column, file length, then up to 80 bytes of the
    /// file name.
    const RECORD_WORDS: usize = 16;
    const FILE_BYTES: usize = (RECORD_WORDS - 6) * 8;
    const TAG_RETURNED: u64 = 1;
    const TAG_PANICKED: u64 = 2;
    /// Exit status of a child whose `panic_bounds_check` stub ran.
    const PANIC_STATUS: i32 = 64;
    /// A trap signal ends the child with this plus the signal number, so no
    /// crash report or core file is written.
    const TRAP_STATUS_BASE: i32 = 128;
    /// SIGILL, SIGTRAP, SIGSEGV and the host's SIGBUS.
    const TRAP_SIGNALS: [i32; 4] = [4, 5, 11, if cfg!(target_os = "macos") { 10 } else { 7 }];

    /// The write end of the running child's pipe.
    static RECORD_FD: AtomicI32 = AtomicI32::new(-1);

    fn publish(record: &[u64; RECORD_WORDS]) {
        // One 128-byte write to a pipe is atomic (PIPE_BUF is at least 512).
        // SAFETY: `record` is a live buffer of that many bytes.
        unsafe {
            write(
                RECORD_FD.load(Ordering::Relaxed),
                record.as_ptr().cast(),
                std::mem::size_of_val(record),
            )
        };
    }

    extern "C" fn on_trap(signum: i32) {
        // SAFETY: `_exit` is async-signal-safe.
        unsafe { _exit(TRAP_STATUS_BASE + signum) }
    }

    /// The stub the JIT binds to `panic_bounds_check(index, len, &Location)`:
    /// it records the two arguments and the `Location` it is passed (file
    /// pointer, file length, then line and column as two u32), and ends the
    /// child. Like the real entry under `panic=abort`, it never returns.
    pub(super) extern "C" fn panic_bounds_check(
        index: u64,
        len: u64,
        location: *const [u64; 3],
    ) -> ! {
        let mut record = [0u64; RECORD_WORDS];
        record[0] = TAG_PANICKED;
        record[1] = index;
        record[2] = len;
        // SAFETY: the bridge passes the address of a 24-byte `Location`
        // constant whose first word points at `file_len` file-name bytes.
        unsafe {
            let [file, file_len, line_column] = *location;
            record[3] = line_column & 0xffff_ffff;
            record[4] = line_column >> 32;
            record[5] = file_len;
            let copied = usize::try_from(file_len).map_or(FILE_BYTES, |n| n.min(FILE_BYTES));
            std::ptr::copy_nonoverlapping(
                file as *const u8,
                record.as_mut_ptr().add(6).cast::<u8>(),
                copied,
            );
            publish(&record);
            _exit(PANIC_STATUS)
        }
    }

    /// The array-fill helper the bridge calls to zero its arrays.
    pub(super) extern "C" fn p4_fill_i64(base: *mut i64, value: i64, count: i64) {
        for at in 0..usize::try_from(count).unwrap_or(0) {
            // SAFETY: the bridge passes a stack array of `count` elements.
            unsafe { base.add(at).write(value) };
        }
    }

    /// Run `entry(reps)` in a forked child and report how it ended.
    pub(super) fn run(entry: extern "C" fn(u32) -> i64, reps: u32) -> Outcome {
        let mut fds = [-1i32; 2];
        // SAFETY: `fds` holds two descriptors.
        assert_eq!(unsafe { pipe(fds.as_mut_ptr()) }, 0, "pipe");
        // SAFETY: the child runs only the async-signal-safe path below.
        let pid = unsafe { fork() };
        assert!(pid >= 0, "fork");
        if pid == 0 {
            // SAFETY: descriptor and signal calls in the forked child, which
            // ends in `_exit` (or in a stub's `_exit`).
            unsafe {
                close(fds[0]);
                RECORD_FD.store(fds[1], Ordering::Relaxed);
                for signum in TRAP_SIGNALS {
                    signal(signum, on_trap as extern "C" fn(i32) as usize);
                }
                let value = entry(reps);
                let mut record = [0u64; RECORD_WORDS];
                record[0] = TAG_RETURNED;
                record[1] = value.cast_unsigned();
                publish(&record);
                _exit(0)
            }
        }
        // SAFETY: the parent's copy of the write end.
        unsafe { close(fds[1]) };
        let mut record = [0u64; RECORD_WORDS];
        let wanted = std::mem::size_of_val(&record);
        let mut got = 0usize;
        while got < wanted {
            // SAFETY: reads into the unread tail of `record`.
            let n = unsafe {
                read(
                    fds[0],
                    record.as_mut_ptr().cast::<u8>().add(got).cast(),
                    wanted - got,
                )
            };
            if n <= 0 {
                break;
            }
            got += n.cast_unsigned();
        }
        let mut status = 0i32;
        // SAFETY: waits for the child forked above.
        let waited = unsafe { waitpid(pid, &raw mut status, 0) };
        // SAFETY: the parent's read end.
        unsafe { close(fds[0]) };
        assert_eq!(waited, pid, "waitpid");
        let signalled = status & 0x7f;
        let exit_status = (status >> 8) & 0xff;
        match (signalled, exit_status, got == wanted, record[0]) {
            (0, 0, true, TAG_RETURNED) => Outcome::Returned(record[1].cast_signed()),
            (0, PANIC_STATUS, true, TAG_PANICKED) => {
                let file_len = usize::try_from(record[5]).map_or(FILE_BYTES, |n| n.min(FILE_BYTES));
                let bytes: Vec<u8> = record[6..].iter().flat_map(|w| w.to_ne_bytes()).collect();
                Outcome::Panicked {
                    index: record[1],
                    len: record[2],
                    file: String::from_utf8_lossy(&bytes[..file_len]).into_owned(),
                    line: u32::try_from(record[3]).unwrap_or(u32::MAX),
                    column: u32::try_from(record[4]).unwrap_or(u32::MAX),
                }
            }
            (0, code, _, _) if code > TRAP_STATUS_BASE => {
                Outcome::Signalled(code - TRAP_STATUS_BASE)
            }
            (signum, _, _, _) if signum != 0 && signum != 0x7f => Outcome::Signalled(signum),
            _ => Outcome::Other(format!(
                "wait status {status:#x}, {got} record bytes, tag {}",
                record[0]
            )),
        }
    }
}

/// JIT each build with stub `p4_fill_i64` and `panic_bounds_check` symbols
/// and no process-symbol fallback (unchecked execution, not a proof lane),
/// run it in a forked child for every repetition count, and require the C
/// reference's outcome for `b_len`: the same return value, or the same
/// `panic_bounds_check(index, len, &Location)` call with the `b` check's
/// source location. A trap or any other end is a mismatch. Returns the
/// numbers of returning and panicking runs.
#[cfg(any(
    all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
    all(target_arch = "aarch64", target_os = "macos")
))]
fn p4_bridge_differential(
    builds: &[(String, Prepared)],
    b_len: u64,
    reference: &std::collections::BTreeMap<(u64, u32), Outcome>,
) -> (usize, usize) {
    use trust_cg_codegen::jit::{JitCompiler, JitConfig, JitExternalSymbolResolutionPolicy};

    let stubs: std::collections::HashMap<String, *const u8> = [
        ("p4_fill_i64".to_string(), child::p4_fill_i64 as *const u8),
        (
            PANIC_BOUNDS_CHECK.to_string(),
            child::panic_bounds_check as *const u8,
        ),
    ]
    .into_iter()
    .collect();
    let jit = JitCompiler::new(JitConfig {
        external_symbol_resolution: JitExternalSymbolResolutionPolicy::ExplicitOnly,
        ..JitConfig::default()
    });
    let (mut returned, mut panicked) = (0, 0);
    let mut mismatches = Vec::new();
    for (symbol, prepared) in builds {
        let buffer = jit
            .compile_raw_with_globals(&prepared.functions, &prepared.globals, &stubs)
            .unwrap_or_else(|error| panic!("{symbol}: JIT: {error}"));
        // SAFETY: the bridge's `main` with the repetition count as its
        // parameter and `acc` as its return value.
        let entry = unsafe { buffer.get_fn_bound::<extern "C" fn(u32) -> i64>(symbol) }
            .unwrap_or_else(|| panic!("{symbol}: no JIT entry"));
        let entry = *entry.as_ref();
        buffer.ensure_current_thread_execute_mode();
        for (&(_, reps), want) in reference.range((b_len, 0)..=(b_len, u32::MAX)) {
            let got = child::run(entry, reps);
            match got {
                Outcome::Returned(_) => returned += 1,
                Outcome::Panicked { .. } => panicked += 1,
                _ => {}
            }
            if &got != want {
                mismatches.push(format!("{symbol} reps={reps}: {got:?}, reference {want:?}"));
            }
        }
    }
    assert!(
        mismatches.is_empty(),
        "the current bridge's p4_matmul nest differs from the C reference:\n{}",
        mismatches.join("\n")
    );
    (returned, panicked)
}

/// The current bridge's p4_matmul nest, pass on and off at O2 and O3, run
/// natively through the JIT: every build equals the C transcription over
/// nine repetition counts (20000 included) and none calls
/// `panic_bounds_check`. In its copy with the nest's `b` check one element
/// short, every build calls the `panic_bounds_check` stub with index 575,
/// length 575 and the check's source location for every count but 0: a
/// failed check is an observed panic call, never a trap.
#[cfg(any(
    all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
    all(target_arch = "aarch64", target_os = "macos")
))]
#[test]
fn current_bridge_p4_matmul_nest_matches_the_c_reference_on_and_off() {
    let reference = p4_reference_outcomes();
    let builds = p4_bridge_builds("p4_bridge", P4_LEN, true);
    let runs = p4_bridge_differential(&builds, P4_LEN, &reference);
    assert_eq!(runs, (36, 0), "four builds x nine counts, none panicking");
    let short = p4_bridge_builds("p4_bridge_short_b", P4_LEN - 1, false);
    let runs = p4_bridge_differential(&short, P4_LEN - 1, &reference);
    assert_eq!(runs, (4, 32), "only the zero-count runs return");
    eprintln!(
        "current-bridge p4_matmul on {}: 72 JIT runs equal the C reference, 32 of them \
         observed panic_bounds_check calls",
        native_host::HOST
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
