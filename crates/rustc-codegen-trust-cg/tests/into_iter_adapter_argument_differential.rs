#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: a two-source iterator adapter whose second (or both)
// arguments are an `IntoIterator` rather than an iterator.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE HAZARD. The bridge intercepts the `zip` / `chain` constructor call and
// writes the adapter's sub-iterator states itself. `Iterator::zip(self, other:
// U)` and `Iterator::chain(self, other: U)` take `U: IntoIterator`, and the free
// `iter::zip(a, b)` / `iter::chain(a, b)` take two; std's body calls
// `into_iter()` before storing. For `U = &[T]` the argument's bytes are the fat
// pointer `{ data, len }`, not `slice::Iter`'s `{ ptr, end }`, and `&[T; N]` /
// `&Vec<T>` are one pointer. Copying those bytes as the sub-iterator state gave
// `zip` the length `min(p.len, (len - data) / size)` and `chain` an end pointer
// of `len`. Measured on f349c8652 (proofs-off lane, LLVM caller, bridge
// library): `p.iter().zip(a)` over `p` of 5 and `a` of 0..2 elements folded
// all five pairs (10441555 where LLVM prints 0 / 11 / 350) at -O0 and -O3,
// `zip(a).count()` was 5 where LLVM prints 0..2, and every `chain(a)` /
// `iter::zip(p, a)` / `iter::chain(p, a)` row died with SIGBUS.
//
// THE GATE, per row. Each row is ONE library function `k` compiled by LLVM
// (the oracle) and by the bridge at the row's optimization level; the caller is
// always compiled by LLVM, as in the census lane that found the defect. The
// caller runs `k` over every `(p.len(), a.len())` pair in `LENGTHS` — empty,
// one element, `a` shorter than, equal to, and longer than `p` — where `a` is a
// PREFIX of a longer buffer, so a read past `a`'s end returns plausible values
// instead of faulting.
//   * `Expect::Match`: the bridge must compile the library and the program must
//     print exactly what the oracle prints and exit with its code.
//   * `Expect::MatchOrRefusal`: the same, OR the bridge refuses with the named
//     `[code]` and a root line that names `root` and carries `root_line` (the
//     bracketed code for a typed refusal, the reason for an untyped
//     `[TCG-MIR-UNSUPPORTED]` one).
//   * Anything else fails: a different stdout or exit code (the miscompile), a
//     run past `RUN_TIMEOUT`, a signal, an ICE, or any other refusal.
// The oracle is asserted first on every row, so a row cannot pass vacuously.
//
// The conversion admits a `&Vec<T>` only as a borrow of a non-argument `Vec`
// local of the kernel's own body: `zip(&v)` of a Vec the body builds itself
// compiles and must match. A `&Vec<T>` PARAMETER, and a borrow of a by-value
// `Vec<T>` parameter, name a header the LLVM caller built; the conversion
// refuses them with `[TCG-ITER-INTOITER-ARG]` (their rows accept a match too,
// never a wrong answer). On f349c8652, whose collections were a pointer to the
// bridge's own slot rather than rustc's header, converting the by-value form
// read rustc's `Vec` as that slot and died with SIGSEGV.
// Those rows build `v` with `collect()`, not `to_vec()`: on f349c8652 a
// bridge-compiled `<[u32]>::to_vec` at -O3 overran its heap allocation (guard
// malloc faulted on a 5-element copy), which would fail the rows for a reason
// unrelated to the conversion under test.
//
// HOST-NATIVE: no `--target` is passed. The bridge side passes `no-proof-certs`
// for the reason `fat_thin_cast_differential.rs` gives: with certificates on,
// AArch64 objects stop at `[TCG-PROOF-465]` after lowering and would pin nothing.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

const INTO_ITER_ARG: &str = "TCG-ITER-INTOITER-ARG";
const MIR_UNSUPPORTED: &str = "TCG-MIR-UNSUPPORTED";
const RUN_TIMEOUT: Duration = Duration::from_secs(30);
/// `(p.len(), a.len())`: `a` empty, one element, shorter than `p`, equal,
/// longer, both empty, and `p` empty.
const LENGTHS: &str =
    "[(5usize, 0usize), (5, 1), (5, 2), (5, 5), (2, 5), (5, 8), (0, 5), (0, 0), (1, 1)]";
const LENGTH_COUNT: usize = 9;

/// The v0-mangled tail of the kernel `klib::k`, as a refused root is listed.
const KERNEL_ROOT: &str = "4klib1k ";

#[derive(Clone, Copy, Debug)]
enum Expect {
    /// Compiles, and the program's stdout and exit code equal LLVM's.
    Match,
    /// `Match`, or a `[code]` refusal whose root line names `root` and carries
    /// `root_line`.
    MatchOrRefusal {
        code: &'static str,
        root: &'static str,
        root_line: &'static str,
    },
}

/// `Match`, or the typed `[code]` refusing the kernel `k` itself.
const fn or_refused(code: &'static str, bracketed: &'static str) -> Expect {
    Expect::MatchOrRefusal {
        code,
        root: KERNEL_ROOT,
        root_line: bracketed,
    }
}

/// `Match`, or `[TCG-MIR-UNSUPPORTED]` refusing the kernel `k` for `reason`.
const fn or_unsupported(reason: &'static str) -> Expect {
    Expect::MatchOrRefusal {
        code: MIR_UNSUPPORTED,
        root: KERNEL_ROOT,
        root_line: reason,
    }
}

/// How the LLVM caller passes `p` and `a` to `k`.
#[derive(Clone, Copy, Debug)]
enum Args {
    /// `k(p: &[E], a: &[E])`.
    Shared,
    /// `k(p: &[E], a: &mut [E])`; the caller also prints `a` afterwards.
    MutA,
    /// `k(p: &mut [E], a: &mut [E])`; the caller also prints both afterwards.
    MutBoth,
    /// `k(p: &[E], a: &Vec<E>)` with `a` a fresh `Vec` the caller built.
    VecRef,
    /// `k(p: &[E], mut a: Vec<E>)` with `a` a fresh `Vec` the caller built and
    /// moved in.
    VecValue,
}

struct Row {
    name: &'static str,
    opt: &'static str,
    elem: &'static str,
    args: Args,
    body: &'static str,
    expect: Expect,
}

/// A loop over the zipped pairs that folds each pair order-sensitively, so a
/// wrong length or a wrong element changes the result.
macro_rules! fold_pairs {
    ($iter:literal) => {
        concat!(
            "let mut n = 0u64;\n",
            "    for (&x, &y) in ",
            $iter,
            " {\n",
            "        n = n.wrapping_mul(31).wrapping_add((x ^ y) as u64);\n",
            "    }\n",
            "    n"
        )
    };
}

/// An order-sensitive fold of a `u32`-item iterator's values.
macro_rules! fold_items {
    ($iter:literal) => {
        concat!(
            $iter,
            ".map(|&x| x as u64).fold(0u64, |n, x| n.wrapping_mul(31).wrapping_add(x))"
        )
    };
}

fn rows() -> Vec<Row> {
    let tuple_fold = or_unsupported("iterator fold over a tuple-yielding chain is not modeled");
    let zip_side =
        or_unsupported("zip() is only modeled over slice::Iter / 64-bit Range sub-sources");
    let chain_state = or_unsupported("iterator chain inner argument is not memory-backed");
    let into_iter_arg = or_refused(INTO_ITER_ARG, "[TCG-ITER-INTOITER-ARG]");
    // `for` over a `Chain` at -O0 calls std's `Chain::next`, whose `or_else`
    // closure takes its environment by value across the backend boundary.
    let chain_next_abi = Expect::MatchOrRefusal {
        code: "TCG-ARG-ABI",
        root: "8adapters5chain",
        root_line: "[TCG-ARG-ABI]",
    };
    // `Iterator::eq` / `cmp` convert their argument inside std's own body and
    // then drive `iter_compare`'s `try_for_each`, which is not modeled.
    let iter_compare = Expect::MatchOrRefusal {
        code: MIR_UNSUPPORTED,
        root: "12iter_compare",
        root_line: "iterator try_fold with a by-value capturing check closure is not modeled",
    };
    // (name, element, arguments, kernel body, -O0 expectation, -O3 expectation)
    let table: [(&str, &str, Args, &str, Expect, Expect); 39] = [
        // `zip(a)` with `a: &[T]`: the defect, across element sizes.
        (
            "zip_slice_u32",
            "u32",
            Args::Shared,
            fold_pairs!("p.iter().zip(a)"),
            Expect::Match,
            Expect::Match,
        ),
        (
            "zip_slice_u8",
            "u8",
            Args::Shared,
            fold_pairs!("p.iter().zip(a)"),
            Expect::Match,
            Expect::Match,
        ),
        (
            "zip_slice_u64",
            "u64",
            Args::Shared,
            fold_pairs!("p.iter().zip(a)"),
            Expect::Match,
            Expect::Match,
        ),
        (
            "zip_slice_i16",
            "i16",
            Args::Shared,
            fold_pairs!("p.iter().zip(a)"),
            Expect::Match,
            Expect::Match,
        ),
        (
            "zip_slice_f64",
            "f64",
            Args::Shared,
            "let mut n = 0.0f64;\n    \
             for (&x, &y) in p.iter().zip(a) {\n        \
             n = n * 3.0 + x * y;\n    \
             }\n    \
             n as u64",
            Expect::Match,
            Expect::Match,
        ),
        // The control: an explicit `.iter()` is already the iterator.
        (
            "zip_iter_control",
            "u32",
            Args::Shared,
            fold_pairs!("p.iter().zip(a.iter())"),
            Expect::Match,
            Expect::Match,
        ),
        (
            "zip_slice_left",
            "u32",
            Args::Shared,
            fold_pairs!("a.iter().zip(p)"),
            Expect::Match,
            Expect::Match,
        ),
        (
            "zip_slice_count",
            "u32",
            Args::Shared,
            "p.iter().zip(a).count() as u64",
            Expect::Match,
            tuple_fold,
        ),
        (
            "zip_slice_map_sum",
            "u32",
            Args::Shared,
            "p.iter().zip(a).map(|(&x, &y)| x as u64 * (y as u64 + 1)).sum()",
            Expect::Match,
            Expect::Match,
        ),
        (
            "zip_slice_collect",
            "u32",
            Args::Shared,
            "let v: Vec<u32> = p.iter().zip(a).map(|(&x, &y)| x ^ y).collect();\n    \
             v.len() as u64 * 1000 + v.iter().map(|&x| x as u64).sum::<u64>()",
            Expect::Match,
            Expect::Match,
        ),
        (
            "zip_slice_for_each",
            "u32",
            Args::Shared,
            "let mut n = 0u64;\n    \
             p.iter().zip(a).for_each(|(&x, &y)| n = n.wrapping_mul(31).wrapping_add((x ^ y) as u64));\n    \
             n",
            Expect::Match,
            tuple_fold,
        ),
        (
            "zip_slice_rev",
            "u32",
            Args::Shared,
            fold_pairs!("p.iter().zip(a).rev()"),
            Expect::Match,
            Expect::Match,
        ),
        (
            "zip_subslice",
            "u32",
            Args::Shared,
            fold_pairs!("p.iter().zip(&a[a.len() / 2..])"),
            Expect::Match,
            Expect::Match,
        ),
        // The free function converts BOTH arguments.
        (
            "zip_free_fn",
            "u32",
            Args::Shared,
            fold_pairs!("std::iter::zip(p, a)"),
            Expect::Match,
            Expect::Match,
        ),
        (
            "zip_range_slice",
            "u32",
            Args::Shared,
            "let mut n = 0u64;\n    \
             for (i, &y) in (0..p.len() as u64).zip(a) {\n        \
             n = n.wrapping_mul(31).wrapping_add(i ^ y as u64);\n    \
             }\n    \
             n",
            Expect::Match,
            Expect::Match,
        ),
        // `&[T; N]`: a thin pointer whose length is the type's `N`.
        (
            "zip_array_ref",
            "u32",
            Args::Shared,
            "let arr: [u32; 3] = [a.len() as u32, 7, 9];\n    \
             let mut n = 0u64;\n    \
             for (&x, &y) in p.iter().zip(&arr) {\n        \
             n = n.wrapping_mul(31).wrapping_add((x ^ y) as u64);\n    \
             }\n    \
             n",
            Expect::Match,
            Expect::Match,
        ),
        (
            "zip_promoted_array_ref",
            "u32",
            Args::Shared,
            fold_pairs!("p.iter().zip(&[10u32, 11, 12])"),
            Expect::Match,
            Expect::Match,
        ),
        // `&Vec<T>` of a Vec this body built.
        (
            "zip_local_vec_ref",
            "u32",
            Args::Shared,
            "let v: Vec<u32> = a.iter().copied().collect();\n    \
             let mut n = 0u64;\n    \
             for (&x, &y) in p.iter().zip(&v) {\n        \
             n = n.wrapping_mul(31).wrapping_add((x ^ y) as u64);\n    \
             }\n    \
             n",
            Expect::Match,
            Expect::Match,
        ),
        // The shapes the conversion does not model refuse by name.
        (
            "zip_vec_param",
            "u32",
            Args::VecRef,
            fold_pairs!("p.iter().zip(a)"),
            into_iter_arg,
            into_iter_arg,
        ),
        (
            "zip_box_slice_ref",
            "u32",
            Args::Shared,
            "let b: Box<[u32]> = a.into();\n    \
             let mut n = 0u64;\n    \
             for (&x, &y) in p.iter().zip(&b) {\n        \
             n = n.wrapping_mul(31).wrapping_add((x ^ y) as u64);\n    \
             }\n    \
             n",
            into_iter_arg,
            into_iter_arg,
        ),
        (
            "zip_const_slice",
            "u32",
            Args::Shared,
            "const C: &[u32] = &[10, 11, 12];\n    \
             let _ = a;\n    \
             let mut n = 0u64;\n    \
             for (&x, &y) in p.iter().zip(C) {\n        \
             n = n.wrapping_mul(31).wrapping_add((x ^ y) as u64);\n    \
             }\n    \
             n",
            into_iter_arg,
            into_iter_arg,
        ),
        // `&mut [T]` makes a `slice::IterMut` side, which `zip` does not model.
        (
            "zip_mut_slice",
            "u32",
            Args::MutA,
            "let mut n = 0u64;\n    \
             for (&x, y) in p.iter().zip(a) {\n        \
             *y ^= x;\n        \
             n = n.wrapping_mul(31).wrapping_add(*y as u64);\n    \
             }\n    \
             n",
            zip_side,
            zip_side,
        ),
        // A by-value array is an owning `array::IntoIter`.
        (
            "zip_array_by_value",
            "u32",
            Args::Shared,
            "let arr = [a.len() as u32, 7, 9];\n    \
             let mut n = 0u64;\n    \
             for (&x, y) in p.iter().zip(arr) {\n        \
             n = n.wrapping_mul(31).wrapping_add((x ^ y) as u64);\n    \
             }\n    \
             n",
            Expect::MatchOrRefusal {
                code: "TCG-OWNING-ITER-METHOD",
                root: "5array4iter8IntoIter",
                root_line: "[TCG-OWNING-ITER-METHOD]",
            },
            Expect::MatchOrRefusal {
                code: "TCG-OWNING-ITER-METHOD",
                root: "5array4iter8IntoIter",
                root_line: "[TCG-OWNING-ITER-METHOD]",
            },
        ),
        // `chain(a)`: the same defect, where it gave the second half an end
        // pointer equal to `a.len()`.
        (
            "chain_slice_for",
            "u32",
            Args::Shared,
            "let mut n = 0u64;\n    \
             for &x in p.iter().chain(a) {\n        \
             n = n.wrapping_mul(31).wrapping_add(x as u64);\n    \
             }\n    \
             n",
            chain_next_abi,
            Expect::Match,
        ),
        (
            "chain_slice_fold",
            "u32",
            Args::Shared,
            fold_items!("p.iter().chain(a)"),
            Expect::Match,
            Expect::Match,
        ),
        (
            "chain_slice_count",
            "u32",
            Args::Shared,
            "p.iter().chain(a).count() as u64",
            Expect::Match,
            Expect::Match,
        ),
        (
            "chain_iter_control",
            "u32",
            Args::Shared,
            fold_items!("p.iter().chain(a.iter())"),
            Expect::Match,
            Expect::Match,
        ),
        (
            "chain_free_fn",
            "u32",
            Args::Shared,
            fold_items!("std::iter::chain(p, a)"),
            Expect::Match,
            Expect::Match,
        ),
        (
            "chain_array_ref",
            "u32",
            Args::Shared,
            "let arr: [u32; 3] = [a.len() as u32, 7, 9];\n    \
             p.iter().chain(&arr).map(|&x| x as u64).fold(0u64, |n, x| n.wrapping_mul(31).wrapping_add(x))",
            Expect::Match,
            Expect::Match,
        ),
        (
            "chain_local_vec_ref",
            "u32",
            Args::Shared,
            "let v: Vec<u32> = a.iter().copied().collect();\n    \
             p.iter().chain(&v).map(|&x| x as u64).fold(0u64, |n, x| n.wrapping_mul(31).wrapping_add(x))",
            Expect::Match,
            Expect::Match,
        ),
        (
            "chain_vec_param",
            "u32",
            Args::VecRef,
            fold_items!("p.iter().chain(a)"),
            into_iter_arg,
            into_iter_arg,
        ),
        // A by-value `Vec` parameter is a header the LLVM caller built, so a
        // borrow of it is refused like a `&Vec` parameter.
        (
            "zip_vec_value_param",
            "u32",
            Args::VecValue,
            fold_pairs!("p.iter().zip(&a)"),
            into_iter_arg,
            into_iter_arg,
        ),
        (
            "chain_vec_value_param",
            "u32",
            Args::VecValue,
            fold_items!("p.iter().chain(&a)"),
            into_iter_arg,
            into_iter_arg,
        ),
        (
            "chain_mut_vec_value_param",
            "u32",
            Args::VecValue,
            "let mut q: Vec<u32> = p.iter().copied().collect();\n    \
             q.iter_mut().chain(&mut a).map(|y| { *y += 1; *y as u64 }).fold(0u64, |n, x| n.wrapping_mul(31).wrapping_add(x))",
            into_iter_arg,
            chain_state,
        ),
        // `&mut [T]` arguments make `slice::IterMut` sub-iterators, which
        // `chain` models; the writes must land in the caller's buffers.
        (
            "chain_mut_free_fn",
            "u32",
            Args::MutBoth,
            "std::iter::chain(p, a).map(|y| { *y += 1; *y as u64 }).fold(0u64, |n, x| n.wrapping_mul(31).wrapping_add(x))",
            Expect::Match,
            Expect::Match,
        ),
        (
            "chain_mut_method",
            "u32",
            Args::MutBoth,
            "p.iter_mut().chain(a).map(|y| { *y += 1; *y as u64 }).fold(0u64, |n, x| n.wrapping_mul(31).wrapping_add(x))",
            Expect::Match,
            chain_state,
        ),
        // Adapters that convert their argument inside std's own body.
        (
            "iterator_eq_slice",
            "u32",
            Args::Shared,
            "p.iter().eq(a) as u64",
            iter_compare,
            iter_compare,
        ),
        (
            "iterator_cmp_slice",
            "u32",
            Args::Shared,
            "(p.iter().cmp(a) as i8 + 1) as u64",
            iter_compare,
            iter_compare,
        ),
        (
            "vec_extend_slice",
            "u32",
            Args::Shared,
            "let mut v: Vec<u32> = Vec::new();\n    \
             v.extend(p);\n    \
             v.extend(a);\n    \
             v.len() as u64 * 1000 + v.iter().map(|&x| x as u64).fold(0u64, |n, x| n.wrapping_mul(31).wrapping_add(x))",
            Expect::Match,
            Expect::Match,
        ),
    ];
    let mut rows = Vec::new();
    for (opt, pick_o3) in [("0", false), ("3", true)] {
        for &(name, elem, args, body, o0, o3) in &table {
            rows.push(Row {
                name,
                opt,
                elem,
                args,
                body,
                expect: if pick_o3 { o3 } else { o0 },
            });
        }
    }
    rows
}

fn lib_source(row: &Row) -> String {
    let e = row.elem;
    let params = match row.args {
        Args::Shared => format!("p: &[{e}], a: &[{e}]"),
        Args::MutA => format!("p: &[{e}], a: &mut [{e}]"),
        Args::MutBoth => format!("p: &mut [{e}], a: &mut [{e}]"),
        Args::VecRef => format!("p: &[{e}], a: &Vec<{e}>"),
        Args::VecValue => format!("p: &[{e}], #[allow(unused_mut)] mut a: Vec<{e}>"),
    };
    format!(
        "#[inline(never)]\npub fn k({params}) -> u64 {{\n    {}\n}}\n",
        row.body
    )
}

fn main_source(row: &Row) -> String {
    let (call, show) = match row.args {
        Args::Shared => (
            "klib::k(black_box(&p[..pl]), black_box(&b[..al]))",
            "String::new()",
        ),
        Args::MutA => (
            "klib::k(black_box(&p[..pl]), black_box(&mut b[..al]))",
            "format!(\"{:?}\", &b[..al])",
        ),
        Args::MutBoth => (
            "klib::k(black_box(&mut p[..pl]), black_box(&mut b[..al]))",
            "format!(\"{:?} {:?}\", &p[..pl], &b[..al])",
        ),
        Args::VecRef => (
            "klib::k(black_box(&p[..pl]), black_box(&b[..al].to_vec()))",
            "String::new()",
        ),
        Args::VecValue => (
            "klib::k(black_box(&p[..pl]), black_box(b[..al].to_vec()))",
            "String::new()",
        ),
    };
    format!(
        "use std::hint::black_box;\n\
         fn main() {{\n\
         \x20   let p0: Vec<{elem}> = (1..6u32).map(|i| i as {elem}).collect();\n\
         \x20   let big: Vec<{elem}> = (10..18u32).map(|i| i as {elem}).collect();\n\
         \x20   for &(pl, al) in &{LENGTHS} {{\n\
         \x20       #[allow(unused_mut)]\n\
         \x20       let mut p = p0.clone();\n\
         \x20       #[allow(unused_mut)]\n\
         \x20       let mut b = big.clone();\n\
         \x20       let k = {call};\n\
         \x20       println!(\"p={{}} a={{}} k={{}} {{}}\", pl, al, k, {show});\n\
         \x20   }}\n\
         }}\n",
        elem = row.elem,
    )
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_intoiter_arg_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn base_command(opt: &str) -> Command {
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["-Cpanic=abort", "-Ccodegen-units=1"]);
    cmd.arg(format!("-Copt-level={opt}"));
    cmd
}

fn add_backend(cmd: &mut Command, dylib: &Path) {
    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(dylib);
    cmd.arg(backend_arg);
    cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
}

/// Compile the row's library; `Err` carries the compiler's stderr.
fn compile_lib(dir: &Path, row: &Row, backend: Option<&Path>, rlib: &Path) -> Result<(), String> {
    let src = dir.join("klib.rs");
    std::fs::write(&src, lib_source(row)).expect("write library source");
    let mut cmd = base_command(row.opt);
    cmd.args(["--crate-type", "rlib", "--crate-name", "klib"]);
    if let Some(dylib) = backend {
        add_backend(&mut cmd, dylib);
    }
    cmd.arg("-o").arg(rlib).arg(&src);
    let output = cmd.output().expect("spawn the compiler");
    if output.status.success() {
        Ok(())
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

/// Link the LLVM-compiled caller against `rlib`.
fn compile_main(dir: &Path, row: &Row, rlib: &Path, bin: &Path) {
    let src = dir.join("kmain.rs");
    std::fs::write(&src, main_source(row)).expect("write caller source");
    let mut cmd = base_command("3");
    cmd.args(["--crate-type", "bin", "--crate-name", "kmain"]);
    let mut extern_arg = std::ffi::OsString::from("klib=");
    extern_arg.push(rlib);
    cmd.arg("--extern").arg(extern_arg);
    cmd.arg("-o").arg(bin).arg(&src);
    let output = cmd.output().expect("spawn the compiler");
    assert!(
        output.status.success(),
        "row {}@O{}: the LLVM-compiled caller did not build: <<<{}>>>",
        row.name,
        row.opt,
        String::from_utf8_lossy(&output.stderr)
    );
}

fn run_with_timeout(bin: &Path) -> Option<Output> {
    let mut child = Command::new(bin)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn the compiled program");
    let start = Instant::now();
    loop {
        if child
            .try_wait()
            .expect("poll the compiled program")
            .is_some()
        {
            return Some(child.wait_with_output().expect("collect program output"));
        }
        if start.elapsed() >= RUN_TIMEOUT {
            child.kill().expect("kill the timed-out program");
            let _ = child.wait_with_output();
            return None;
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

/// Every `[TCG-...]` code in `stderr`.
fn refusal_codes(stderr: &str) -> Vec<String> {
    let mut codes = Vec::new();
    let mut rest = stderr;
    while let Some(start) = rest.find("[TCG-") {
        let tail = &rest[start + 1..];
        let Some(end) = tail.find(']') else {
            break;
        };
        codes.push(tail[..end].to_owned());
        rest = &tail[end..];
    }
    codes
}

/// Whether `stderr` is a `[code]` refusal with a root line naming `root` and
/// carrying `root_line`.
fn names_refusal(stderr: &str, code: &str, root: &str, root_line: &str) -> bool {
    stderr.contains(&format!("[{code}]"))
        && stderr
            .lines()
            .any(|line| line.contains(root) && line.contains(root_line))
}

/// The oracle's output, then the bridge's verdict for one row.
fn check_row(dylib: &Path, row: &Row) -> String {
    let label = format!("{}@O{}", row.name, row.opt);
    let dir = workdir(&label);
    let oracle_rlib = dir.join("llvm").join("libklib.rlib");
    let bridge_rlib = dir.join("bridge").join("libklib.rlib");
    std::fs::create_dir_all(oracle_rlib.parent().unwrap()).expect("create oracle dir");
    std::fs::create_dir_all(bridge_rlib.parent().unwrap()).expect("create bridge dir");

    compile_lib(&dir, row, None, &oracle_rlib).unwrap_or_else(|e| {
        panic!("row {label}: the LLVM oracle library did not build: <<<{e}>>>")
    });
    let oracle_bin = dir.join("llvm_kmain");
    compile_main(&dir, row, &oracle_rlib, &oracle_bin);
    let oracle = run_with_timeout(&oracle_bin)
        .unwrap_or_else(|| panic!("row {label}: the LLVM oracle did not finish"));
    let oracle_stdout = String::from_utf8_lossy(&oracle.stdout).into_owned();
    assert!(
        oracle.status.success() && oracle_stdout.lines().count() == LENGTH_COUNT,
        "row {label}: the LLVM oracle must print one line per length pair and exit 0; \
         status {:?}, stdout <<<{oracle_stdout}>>>",
        oracle.status
    );

    let verdict = match compile_lib(&dir, row, Some(dylib), &bridge_rlib) {
        Ok(()) => {
            let bridge_bin = dir.join("bridge_kmain");
            compile_main(&dir, row, &bridge_rlib, &bridge_bin);
            let Some(bridge) = run_with_timeout(&bridge_bin) else {
                panic!(
                    "row {label}: the bridge-compiled library did not finish within \
                     {RUN_TIMEOUT:?}; oracle printed <<<{oracle_stdout}>>>"
                );
            };
            let bridge_stdout = String::from_utf8_lossy(&bridge.stdout).into_owned();
            assert_eq!(
                (bridge.status.code(), bridge_stdout.as_str()),
                (oracle.status.code(), oracle_stdout.as_str()),
                "row {label}: the bridge-compiled library disagrees with LLVM (exit code \
                 None is a signal). An `IntoIterator` argument's own bytes were stored as \
                 sub-iterator state: convert it, or refuse the shape with \
                 [{INTO_ITER_ARG}], rather than relaxing this assertion. stderr <<<{}>>>",
                String::from_utf8_lossy(&bridge.stderr)
            );
            "MATCHED LLVM".to_owned()
        }
        Err(stderr) => {
            assert!(
                !stderr.contains("internal compiler error") && !stderr.contains("panicked at"),
                "row {label}: the bridge crashed instead of failing closed: <<<{stderr}>>>"
            );
            let codes = refusal_codes(&stderr);
            match row.expect {
                Expect::Match => panic!(
                    "row {label}: this shape compiles and runs correctly and must not be \
                     refused (codes {codes:?}): <<<{stderr}>>>"
                ),
                Expect::MatchOrRefusal {
                    code,
                    root,
                    root_line,
                } => {
                    assert!(
                        names_refusal(&stderr, code, root, root_line),
                        "row {label}: expected a match or the [{code}] refusal of the root \
                         `…{root}` for `{root_line}`; got codes {codes:?}: <<<{stderr}>>>"
                    );
                    format!("REFUSED [{code}] (fail-closed)")
                }
            }
        }
    };
    let _ = std::fs::remove_dir_all(&dir);
    verdict
}

#[test]
fn into_iter_adapter_arguments_match_llvm_or_refuse() {
    if toolchain_support::skip_without_backend_knobs(
        "into_iter_adapter_arguments_match_llvm_or_refuse",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let rows = rows();
    let mut report = Vec::new();
    for row in &rows {
        let verdict = check_row(&dylib, row);
        eprintln!("row {}@O{}: {verdict}", row.name, row.opt);
        report.push(format!("{}@O{} {verdict}", row.name, row.opt));
    }
    eprintln!(
        "into_iter adapter-argument rows ({}): {report:#?}",
        rows.len()
    );
}

/// The same shapes with the WHOLE program compiled by the bridge. Measured on
/// f349c8652: without `zip_local_vec` the program died with SIGBUS before its
/// first line at both -O0 and -O3; with it, `zip(&v)` was refused
/// (`iterator zip inner argument is not memory-backed`).
#[test]
fn whole_program_into_iter_adapter_arguments_match_llvm() {
    if toolchain_support::skip_without_backend_knobs(
        "whole_program_into_iter_adapter_arguments_match_llvm",
    ) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("whole_program");
    let src = dir.join("whole.rs");
    std::fs::write(
        &src,
        format!(
            "use std::hint::black_box;\n\
             #[inline(never)]\n\
             fn zip_slice(p: &[u32], a: &[u32]) -> u64 {{\n    {}\n}}\n\
             #[inline(never)]\n\
             fn zip_free(p: &[u32], a: &[u32]) -> u64 {{\n    {}\n}}\n\
             #[inline(never)]\n\
             fn chain_slice(p: &[u32], a: &[u32]) -> u64 {{\n    {}\n}}\n\
             #[inline(never)]\n\
             fn zip_local_vec(p: &[u32], a: &[u32]) -> u64 {{\n    \
             let v: Vec<u32> = a.iter().copied().collect();\n    {}\n}}\n\
             fn main() {{\n\
             \x20   let p: Vec<u32> = (1..6u32).collect();\n\
             \x20   let big: Vec<u32> = (10..18u32).collect();\n\
             \x20   for &(pl, al) in &{LENGTHS} {{\n\
             \x20       let (q, a) = (black_box(&p[..pl]), black_box(&big[..al]));\n\
             \x20       println!(\"p={{}} a={{}} zip={{}} free={{}} chain={{}} vec={{}}\", pl, al,\n\
             \x20           zip_slice(q, a), zip_free(q, a), chain_slice(q, a), zip_local_vec(q, a));\n\
             \x20   }}\n\
             }}\n",
            fold_pairs!("p.iter().zip(a)"),
            fold_pairs!("std::iter::zip(p, a)"),
            fold_items!("p.iter().chain(a)"),
            fold_pairs!("p.iter().zip(&v)"),
        ),
    )
    .expect("write program source");
    for opt in ["0", "3"] {
        let build = |backend: Option<&Path>, bin: &Path| -> Result<(), String> {
            let mut cmd = base_command(opt);
            cmd.args(["--crate-type", "bin", "--crate-name", "whole"]);
            if let Some(dylib) = backend {
                add_backend(&mut cmd, dylib);
            }
            cmd.arg("-o").arg(bin).arg(&src);
            let output = cmd.output().expect("spawn the compiler");
            if output.status.success() {
                Ok(())
            } else {
                Err(String::from_utf8_lossy(&output.stderr).into_owned())
            }
        };
        let oracle_bin = dir.join(format!("llvm_whole_O{opt}"));
        build(None, &oracle_bin)
            .unwrap_or_else(|e| panic!("O{opt}: the LLVM oracle did not build: <<<{e}>>>"));
        let oracle = run_with_timeout(&oracle_bin)
            .unwrap_or_else(|| panic!("O{opt}: the LLVM oracle did not finish"));
        let oracle_stdout = String::from_utf8_lossy(&oracle.stdout).into_owned();
        assert!(
            oracle.status.success()
                && oracle_stdout.contains("p=5 a=2 zip=350 free=350 chain=947656836 vec=350\n"),
            "O{opt}: the LLVM oracle must pair only a's two elements: <<<{oracle_stdout}>>>"
        );
        let bridge_bin = dir.join(format!("bridge_whole_O{opt}"));
        build(Some(&dylib), &bridge_bin).unwrap_or_else(|e| {
            panic!(
                "O{opt}: the bridge must compile the whole program (codes {:?}): <<<{e}>>>",
                refusal_codes(&e)
            )
        });
        let bridge = run_with_timeout(&bridge_bin).unwrap_or_else(|| {
            panic!("O{opt}: the bridge-compiled program did not finish within {RUN_TIMEOUT:?}")
        });
        assert_eq!(
            (
                bridge.status.code(),
                String::from_utf8_lossy(&bridge.stdout).as_ref()
            ),
            (oracle.status.code(), oracle_stdout.as_str()),
            "O{opt}: the bridge-compiled program disagrees with LLVM (exit code None is a signal)"
        );
        eprintln!("whole program O{opt}: MATCHED LLVM");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn refusal_match_needs_the_code_and_the_root_line() {
    let stderr = "error: [TCG-MIR-UNSUPPORTED] rustc_codegen_trust_cg: cannot compile\n  \
                  - _RNvCs0_4klib1k (reachable): [TCG-ITER-INTOITER-ARG] the `zip` constructor";
    assert_eq!(
        refusal_codes(stderr),
        vec![MIR_UNSUPPORTED.to_owned(), INTO_ITER_ARG.to_owned()]
    );
    assert!(names_refusal(
        stderr,
        INTO_ITER_ARG,
        KERNEL_ROOT,
        "[TCG-ITER-INTOITER-ARG]"
    ));
    assert!(names_refusal(
        stderr,
        MIR_UNSUPPORTED,
        KERNEL_ROOT,
        "the `zip` constructor"
    ));
    assert!(!names_refusal(
        stderr,
        "TCG-ARG-ABI",
        KERNEL_ROOT,
        "[TCG-ARG-ABI]"
    ));
    assert!(!names_refusal(
        stderr,
        INTO_ITER_ARG,
        "8adapters5chain",
        "[TCG-ITER-INTOITER-ARG]"
    ));
    assert!(refusal_codes("no codes here").is_empty());
}
