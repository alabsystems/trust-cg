//! The whole-program rows of trust-cg-opt's loop-state contract, ITERATION
//! COVERAGE clause: a rewrite that runs new code in place of scalar
//! iterations must, together with the scalar remainder, run exactly the
//! iterations it replaces. Run by `opt_loop_state_run.rs` for aarch64
//! (native) and x86-64 (under Rosetta), LLVM as the oracle.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! THE PROGRAM. One `no_std` program, identical source on both targets. Every
//! kernel is an `#[inline(never)]` function over its own local arrays, reached
//! through raw pointers so no bounds check stands between the loop and the
//! passes. Its loop runs from a start `s` to a bound `n`, both RUN-TIME values
//! (`black_box`), in one of several loop FORMS ([`FORMS`]): `<`, `<=`, `!=`,
//! a stride of 2, counting down, bottom-tested, and 32-bit inductions. `main`
//! calls each (kernel, form) for every `s` in [`STARTS`] and `n` in
//! [`BOUNDS`]: 0, 1, and one short of, at, and one past every vector width
//! the passes use (2, 4, 8, 16, 32, 48, 64), their multiples, and
//! non-multiples (100, 1000). A second set of kernels ([`CONST_KERNELS`])
//! takes `s` and `n` as const generics, so the trip count is a compile-time
//! constant the passes divide.
//!
//! Each call prints `kernel form s n value`, where `value` folds the
//! kernel's accumulator, the induction the loop left, and a checksum of every
//! array element, so a lane run twice, a lane skipped, a lane past the bound
//! and a remainder never run all change the line. The bridge's output must
//! equal LLVM's line for line.
//!
//! The arrays are hidden from the optimizer through their POINTERS
//! (`black_box(a.as_mut_ptr())`), never by passing an array through
//! `black_box` by value: the bridge lowers a by-value `[T; LEN]` move to one
//! load and one store per element, which made a single kernel a
//! 42418-instruction function on aarch64 and the whole program an 8 GB,
//! half-hour bridge compile. Through pointers the same kernel is 83
//! instructions and the program compiles in about a minute.
//!
//! This is test-rung evidence; nothing here is a proof.
#![allow(dead_code)]

/// Array length of every runtime kernel: past the largest bound plus one
/// (the `<=` form reads index `n`) plus the stencil's `i + 1`.
pub const LEN: usize = 1040;

pub const STARTS: &[usize] = &[0, 1, 3, 17];

/// Kernel functions (symbol fragments) the aarch64 bridge binary must keep
/// vector code in: every one whose bridge build kept vector code at O2 and O3
/// both on `main` before the iteration-coverage clause (`b4da4cb65`) and with
/// it, from the census each run prints. In `fill8_lt`, `zero32_lt` and
/// `fill64_lt` (their kernel loops) and the `iota32` and `rbit` forms (their
/// zero-initializing loops) that code is a store loop of 64 bytes per trip
/// in front of the scalar loop, `neon_fill`'s shape.
pub const AARCH64_CONTROLS: &[&str] = &[
    "fill8_lt",
    "fill8_c",
    "zero32_lt",
    "zero32_c",
    "fill64_lt",
    "bsum_c",
    "cnt0_c",
    "map32_c",
    "iota32_lt",
    "iota32_le",
    "iota32_ne",
    "iota32_step2",
    "iota32_down",
    "iota32_rot",
    "iota32_range",
    "iota32_i32",
    "iota32_u32",
    "iota32_c",
    "rbit_lt",
    "rbit_le",
    "rbit_ne",
    "rbit_step2",
    "rbit_down",
    "rbit_rot",
    "rbit_range",
    "rbit_i32",
    "rbit_u32",
    "rbit_c",
];

/// The same for x86-64 (no x86-64 rewrite goes through the clause yet; these
/// are `x86_vectorize`'s constant-trip kernels).
pub const X86_64_CONTROLS: &[&str] = &[
    "fill8_c", "zero32_c", "bsum_c", "cnt0_c", "isum_c", "usum64_c",
];

pub const BOUNDS: &[usize] = &[
    0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 47, 48, 49, 63, 64, 65, 96, 100, 127, 128,
    129, 191, 192, 193, 255, 256, 257, 1000, 1023, 1024, 1025,
];

/// One kernel: element type of `a` (read and written) and of `b` (the second
/// array, zero-initialized), accumulator type, initializer of `a` (over `k`),
/// and the loop body over `i: usize`, `pa`, `pb` and `acc`.
pub struct Kernel {
    pub name: &'static str,
    pub elem: &'static str,
    pub belem: &'static str,
    pub acc: &'static str,
    pub init: &'static str,
    pub body: &'static str,
}

pub const KERNELS: &[Kernel] = &[
    Kernel {
        name: "fill8",
        elem: "u8",
        belem: "u8",
        acc: "u64",
        init: "((k * 7) % 13) as u8",
        body: "*pa.add(i) = 7;",
    },
    Kernel {
        name: "zero32",
        elem: "u32",
        belem: "u8",
        acc: "u64",
        init: "(k as u32) | 1",
        body: "*pa.add(i) = 0;",
    },
    Kernel {
        name: "fill64",
        elem: "u64",
        belem: "u8",
        acc: "u64",
        init: "k as u64",
        body: "*pa.add(i) = 0x0102_0304_0506_0708;",
    },
    Kernel {
        name: "bsum",
        elem: "u8",
        belem: "u8",
        acc: "u64",
        init: "((k * 37) % 251) as u8",
        body: "acc += *pa.add(i) as u64;",
    },
    Kernel {
        name: "cnt0",
        elem: "u8",
        belem: "u8",
        acc: "u64",
        init: "if k % 7 == 3 || k % 11 == 5 { 0 } else { 1 }",
        body: "if *pa.add(i) == 0 { acc += 1; }",
    },
    Kernel {
        name: "pop",
        elem: "u8",
        belem: "u8",
        acc: "u64",
        init: "((k * 37) % 251) as u8",
        body: "acc += (*pa.add(i) as u32).count_ones() as u64;",
    },
    Kernel {
        name: "isum",
        elem: "i32",
        belem: "u8",
        acc: "i32",
        init: "((k * 37) % 251) as i32 - 100",
        body: "acc = acc.wrapping_add(*pa.add(i));",
    },
    Kernel {
        name: "usum64",
        elem: "u64",
        belem: "u8",
        acc: "u64",
        init: "((k * 37) % 251) as u64",
        body: "acc = acc.wrapping_add(*pa.add(i));",
    },
    Kernel {
        name: "map32",
        elem: "i32",
        belem: "u8",
        acc: "u64",
        init: "((k * 37) % 251) as i32 - 100",
        body: "*pa.add(i) = (*pa.add(i)).wrapping_mul(3).wrapping_add(1);",
    },
    Kernel {
        name: "map8",
        elem: "u8",
        belem: "u8",
        acc: "u64",
        init: "((k * 37) % 251) as u8",
        body: "*pa.add(i) = (*pa.add(i)).wrapping_add(5);",
    },
    Kernel {
        name: "iota32",
        elem: "u32",
        belem: "u8",
        acc: "u64",
        init: "0",
        body: "*pa.add(i) = (i as u32).wrapping_add(1);",
    },
    Kernel {
        name: "rbit",
        elem: "u8",
        belem: "u8",
        acc: "u64",
        init: "0",
        body: "acc = acc.wrapping_sub((i as u32).reverse_bits() as u64);",
    },
    Kernel {
        name: "max8",
        elem: "u8",
        belem: "u8",
        acc: "u8",
        init: "((k * 37) % 251) as u8",
        body: "let x = *pa.add(i); if x > acc { acc = x; }",
    },
    Kernel {
        name: "maxi32",
        elem: "i32",
        belem: "u8",
        acc: "i32",
        init: "((k * 37) % 251) as i32 - 100",
        body: "let x = *pa.add(i); if x > acc { acc = x; }",
    },
    Kernel {
        name: "fmap",
        elem: "f32",
        belem: "u8",
        acc: "u64",
        init: "k as f32",
        body: "*pa.add(i) = *pa.add(i) * 2.0 + 1.0;",
    },
    Kernel {
        name: "copy8",
        elem: "u8",
        belem: "u8",
        acc: "u64",
        init: "((k * 37) % 251) as u8",
        body: "*pb.add(i) = *pa.add(i);",
    },
    Kernel {
        name: "stencil",
        elem: "u8",
        belem: "u8",
        acc: "u64",
        init: "((k * 37) % 251) as u8",
        body: "*pb.add(i) = (*pa.add(i)).wrapping_add(*pa.add(i + 1));",
    },
    Kernel {
        name: "condst",
        elem: "u8",
        belem: "u8",
        acc: "u64",
        init: "((k * 37) % 251) as u8",
        body: "if *pa.add(i) > 100 { *pb.add(i) = 1; }",
    },
    Kernel {
        name: "addacc",
        elem: "i32",
        belem: "i32",
        acc: "u64",
        init: "((k * 37) % 251) as i32 - 100",
        body: "*pb.add(i) = (*pb.add(i)).wrapping_add(*pa.add(i));",
    },
];

/// One loop form: the loop over `i` from `s` to `n`, `{BODY}` the kernel's
/// body (which reads `i: usize`). `admits(s, n)` says whether `main` calls the
/// form for that pair (`!=` needs `s <= n`; the 32-bit forms keep `n` in
/// range).
pub struct Form {
    pub name: &'static str,
    pub code: &'static str,
}

pub const FORMS: &[Form] = &[
    Form {
        name: "lt",
        code: "let mut i = s; while i < n { {BODY} i += 1; }",
    },
    Form {
        name: "le",
        code: "let mut i = s; while i <= n { {BODY} i += 1; }",
    },
    Form {
        name: "ne",
        code: "let mut i = s; if s <= n { while i != n { {BODY} i += 1; } }",
    },
    Form {
        name: "step2",
        code: "let mut i = s; while i < n { {BODY} i += 2; }",
    },
    Form {
        name: "down",
        code: "let mut i = n; while i > s { i -= 1; {BODY} }",
    },
    Form {
        name: "rot",
        code: "let mut i = s; if i < n { loop { {BODY} i += 1; if i >= n { break; } } }",
    },
    Form {
        name: "range",
        code: "let mut i = s; for j in s..n { i = j; {BODY} } let i = if s < n { i + 1 } else { s };",
    },
    Form {
        name: "i32",
        code: "let mut k32: i32 = s as i32; let n32 = n as i32; \
               while k32 < n32 { let i = k32 as usize; {BODY} k32 += 1; } let i = k32 as usize;",
    },
    Form {
        name: "u32",
        code: "let mut k32: u32 = s as u32; let n32 = n as u32; \
               while k32 < n32 { let i = k32 as usize; {BODY} k32 += 1; } let i = k32 as usize;",
    },
];

/// Kernels with a const-generic start and bound (`for i in S..N`, `<`).
pub const CONST_KERNELS: &[&str] = &[
    "fill8", "zero32", "bsum", "cnt0", "isum", "map32", "iota32", "rbit", "usum64", "copy8",
];
pub const CONST_STARTS: &[usize] = &[0, 1];
pub const CONST_BOUNDS: &[usize] = &[
    0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 100, 127, 128, 129, 1000, 1023,
    1024, 1025,
];

fn kernel(name: &str) -> &'static Kernel {
    KERNELS
        .iter()
        .find(|kernel| kernel.name == name)
        .unwrap_or_else(|| panic!("no kernel {name}"))
}

fn function(kernel: &Kernel, form: &str, params: &str, args: &str, code: &str) -> String {
    let code = code.replace("{BODY}", &format!("unsafe {{ {} }}", kernel.body));
    format!(
        "#[inline(never)]\n#[allow(unused_mut, unused_assignments, unused_variables, unused_unsafe)]\n\
         fn {name}_{form}{params}({args}) -> u64 {{\n\
         \x20   let mut a = [0 as {elem}; LEN];\n    let mut b = [0 as {belem}; LEN];\n\
         \x20   let len = black_box(LEN);\n\
         \x20   let mut k = 0usize;\n    let pi = a.as_mut_ptr();\n\
         \x20   while k < len {{ unsafe {{ *pi.add(k) = {init}; }} k += 1; }}\n\
         \x20   let pa = black_box(pi);\n    let pb = black_box(b.as_mut_ptr());\n\
         \x20   let mut acc: {acc} = 0 as {acc};\n\
         \x20   {code}\n\
         \x20   let (qa, qb) = (black_box(pa as *const {elem}), black_box(pb as *const {belem}));\n\
         \x20   let mut h: u64 = 0;\n    let mut z = 0usize;\n\
         \x20   while z < len {{ unsafe {{ h = h.wrapping_mul(31).wrapping_add(*qa.add(z) as u64).wrapping_mul(17).wrapping_add(*qb.add(z) as u64); }} z += 1; }}\n\
         \x20   black_box(h ^ (acc as u64).wrapping_mul(0x9e37_79b9) ^ (i as u64).wrapping_mul(0x51))\n}}\n",
        name = kernel.name,
        elem = kernel.elem,
        belem = kernel.belem,
        acc = kernel.acc,
        init = kernel.init,
    )
}

/// Whether `main` calls `form` for `(s, n)`.
pub fn admits(form: &str, s: usize, n: usize) -> bool {
    match form {
        "ne" => s <= n,
        _ => true,
    }
}

/// The `no_std` program: one function per (kernel, form), plus the const
/// instances, each printed for every admitted `(s, n)`.
pub fn program_source() -> String {
    let mut src = format!(
        "#![no_std]\n#![no_main]\n\
         use core::hint::black_box;\n\
         const LEN: usize = {LEN};\n\
         extern \"C\" {{\n    fn write(fd: i32, buf: *const u8, len: usize) -> isize;\n    fn abort() -> !;\n}}\n\
         #[panic_handler]\nfn panic(_: &core::panic::PanicInfo) -> ! {{ unsafe {{ abort() }} }}\n\
         #[inline(never)]\nfn put(name: &[u8], s: usize, n: usize, value: u64) {{\n\
         \x20   let mut line = [0u8; 128];\n    let mut len = 0usize;\n\
         \x20   for &c in name {{ line[len] = c; len += 1; }}\n\
         \x20   for v in [s as u64, n as u64, value] {{\n\
         \x20       line[len] = b' '; len += 1;\n\
         \x20       let mut digits = [0u8; 20];\n        let mut count = 0usize;\n        let mut x = v;\n\
         \x20       loop {{ digits[count] = b'0' + (x % 10) as u8; count += 1; x /= 10; if x == 0 {{ break; }} }}\n\
         \x20       while count > 0 {{ count -= 1; line[len] = digits[count]; len += 1; }}\n\
         \x20   }}\n\
         \x20   line[len] = b'\\n'; len += 1;\n\
         \x20   unsafe {{ write(1, line.as_ptr(), len); }}\n}}\n"
    );
    for kernel in KERNELS {
        for form in FORMS {
            src.push_str(&function(
                kernel,
                form.name,
                "",
                "s: usize, n: usize",
                form.code,
            ));
        }
    }
    for &name in CONST_KERNELS {
        src.push_str(&function(
            kernel(name),
            "c",
            "<const S: usize, const N: usize>",
            "",
            "let s = S; let n = N; let mut i = s; while i < n { {BODY} i += 1; }",
        ));
    }
    src.push_str(
        "#[no_mangle]\npub extern \"C\" fn main(_argc: i32, _argv: *const *const u8) -> i32 {\n",
    );
    let starts = STARTS
        .iter()
        .map(|s| s.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let bounds = BOUNDS
        .iter()
        .map(|n| n.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    src.push_str(&format!(
        "    let starts: [usize; {}] = [{starts}];\n    let bounds: [usize; {}] = [{bounds}];\n",
        STARTS.len(),
        BOUNDS.len()
    ));
    for kernel in KERNELS {
        for form in FORMS {
            let guard = match form.name {
                "ne" => "s <= n",
                _ => "true",
            };
            src.push_str(&format!(
                "    for &s in starts.iter() {{ for &n in bounds.iter() {{ if {guard} {{ \
                 let (s, n) = (black_box(s), black_box(n)); \
                 put(b\"{name} {form}\", s, n, {name}_{form}(s, n)); }} }} }}\n",
                name = kernel.name,
                form = form.name,
            ));
        }
    }
    for &name in CONST_KERNELS {
        for &s in CONST_STARTS {
            for &n in CONST_BOUNDS {
                src.push_str(&format!(
                    "    put(b\"{name} c\", {s}, {n}, {name}_c::<{s}, {n}>());\n"
                ));
            }
        }
    }
    src.push_str("    0\n}\n");
    src
}

/// How many lines the program prints.
pub fn row_count() -> usize {
    let mut rows = 0;
    for _ in KERNELS {
        for form in FORMS {
            for &s in STARTS {
                for &n in BOUNDS {
                    if admits(form.name, s, n) {
                        rows += 1;
                    }
                }
            }
        }
    }
    rows + CONST_KERNELS.len() * CONST_STARTS.len() * CONST_BOUNDS.len()
}

/// The rows for one target: every line equals LLVM's, at O2 and O3.
/// `controls` are kernel functions (symbol fragments) in which the bridge
/// binary must keep vector code, so the rows are not bought by vectorizing
/// nothing. Every kernel function's vector-op count is printed.
pub fn check_target(
    target: crate::loop_state::Target,
    bridge: crate::loop_state::Bridge<'_>,
    controls: &[&str],
) -> Vec<String> {
    use crate::loop_state::{OPTS, compile, run, vector_ops, workdir};
    let src = program_source();
    let rows = row_count();
    let mut failures = Vec::new();
    for &opt in OPTS {
        let dir = workdir(&format!("coverage_{target:?}_O{opt}"));
        let oracle_bin = compile(&dir, "coverage", &src, target, opt, None, true)
            .unwrap_or_else(|e| panic!("{target:?} O{opt}: LLVM failed to compile:\n{e}"));
        let (oracle_code, oracle_out) = run(&oracle_bin, target, opt);
        assert_eq!(
            oracle_code,
            Some(0),
            "{target:?} O{opt}: the LLVM oracle ran"
        );
        assert_eq!(
            oracle_out.lines().count(),
            rows,
            "{target:?} O{opt}: the oracle printed every row"
        );
        let started = std::time::Instant::now();
        let compiled = compile(&dir, "coverage", &src, target, opt, Some(bridge), true);
        eprintln!(
            "{target:?} O{opt}: bridge compile {:.0} s",
            started.elapsed().as_secs_f64()
        );
        let bridge_bin = match compiled {
            Ok(bin) => bin,
            Err(e) => {
                failures.push(format!(
                    "{target:?} O{opt}: the bridge failed to compile:\n{e}"
                ));
                continue;
            }
        };
        let (bridge_code, bridge_out) = run(&bridge_bin, target, opt);
        if bridge_code != Some(0) {
            failures.push(format!(
                "{target:?} O{opt}: the bridge binary exited {bridge_code:?}"
            ));
        }
        let bridge_lines: Vec<&str> = bridge_out.lines().collect();
        let mut wrong = 0usize;
        for (index, expected) in oracle_out.lines().enumerate() {
            let got = bridge_lines.get(index).copied().unwrap_or("<missing>");
            if got != expected {
                wrong += 1;
                if wrong <= 40 {
                    failures.push(format!(
                        "{target:?} O{opt}: WRONG `{got}`, LLVM `{expected}`"
                    ));
                }
            }
        }
        if wrong > 40 {
            failures.push(format!("{target:?} O{opt}: ... {wrong} wrong rows in all"));
        }
        eprintln!("{target:?} O{opt}: {wrong} of {rows} rows differ from LLVM");
        let functions = functions_of(&bridge_bin);
        let ops_of = |name: &str| -> Option<usize> {
            let mut found = false;
            let mut ops = 0;
            for (header, body) in &functions {
                if header.contains(name) {
                    found = true;
                    ops += vector_ops(body, target);
                }
            }
            found.then_some(ops)
        };
        let census: Vec<String> = kernel_functions()
            .iter()
            .map(|name| match ops_of(name) {
                Some(ops) => format!("{name}={ops}"),
                None => format!("{name}=absent"),
            })
            .collect();
        eprintln!("{target:?} O{opt}: vector ops: {}", census.join(" "));
        for &control in controls {
            match ops_of(control) {
                None => failures.push(format!(
                    "{target:?} O{opt}: no symbol {control} in the bridge binary"
                )),
                Some(0) => {
                    failures.push(format!("{target:?} O{opt}: {control} lost its vector code"))
                }
                Some(_) => {}
            }
        }
        let _ = std::fs::remove_dir_all(&dir);
    }
    failures
}

/// Every kernel function's name (a symbol fragment): one per (kernel, form),
/// and one per const kernel (`<kernel>_c`, every instance).
pub fn kernel_functions() -> Vec<String> {
    let mut names = Vec::new();
    for kernel in KERNELS {
        for form in FORMS {
            names.push(format!("{}_{}", kernel.name, form.name));
        }
    }
    for &name in CONST_KERNELS {
        names.push(format!("{name}_c"));
    }
    names
}

/// Every function in `bin`'s disassembly, as its `<symbol>:` header line and
/// its instruction lines, from one `objdump` run (the program has hundreds of
/// kernels; disassembling the binary once per kernel cost minutes).
fn functions_of(bin: &std::path::Path) -> Vec<(String, String)> {
    let output = std::process::Command::new("objdump")
        .args(["-d", "--no-show-raw-insn"])
        .arg(bin)
        .output()
        .expect("run objdump");
    assert!(
        output.status.success(),
        "objdump failed for {bin:?} ({}): {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8_lossy(&output.stdout);
    let mut functions: Vec<(String, String)> = Vec::new();
    let mut inside = false;
    for line in text.lines() {
        if line.ends_with(">:") {
            functions.push((line.to_string(), String::new()));
            inside = true;
        } else if line.is_empty() {
            inside = false;
        } else if inside {
            if let Some((_, body)) = functions.last_mut() {
                body.push_str(line);
                body.push('\n');
            }
        }
    }
    functions
}
