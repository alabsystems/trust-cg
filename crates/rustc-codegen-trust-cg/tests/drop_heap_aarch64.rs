// Compiled only on an aarch64-apple-darwin host: another host builds this
// target with no test in it, never one that passes without running (L06-P10).
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// E2E (aarch64-apple-darwin): Drop of a heap value frees it via __rust_dealloc.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// This pins the Drop feature END-TO-END on aarch64: a `Box<T>` value (scalar and
// aggregate payload) that is heap-allocated, computed through, and DROPPED on a
// normal return path. The bridge's `lower_drop_terminator` -> `lower_box_drop`
// (crates/rustc-codegen-trust-cg/src/lib.rs) emits the matching
// `__rust_dealloc(ptr, size, align)` call as an `AArch64Opcode::Bl` to the
// allocator shim's exported `__rust_dealloc` wrapper, carried by an
// `ARM64_RELOC_BRANCH26` direct-call relocation.
//
// WHY THIS COVERAGE MATTERS: the drop's symbolic BRANCH26 call must survive
// object emission, linking, and execution. This regression proves the boxed
// value is correct before drop and deallocation is observed at runtime. It is
// not production Certified authority: the AY-backed relocation formula remains
// Trusted evidence, and a non-empty relocation inventory still fails closed.
//
// HOW THE FREE IS OBSERVED: the bridge emits a default-allocator shim whose
// `__rust_alloc`/`__rust_dealloc` exported wrappers FORWARD to libstd's
// System-allocator entry points `__rdl_alloc`/`__rdl_dealloc` (the
// `#[rustc_std_internal_symbol]`-mangled names, see `build_allocator_shim_inner`).
// Rather than link libstd, the C driver DEFINES those `__rdl_*` symbols itself as
// instrumented malloc/free hooks that bump a counter — exactly the
// malloc/free-hook pattern of `trust-cg-codegen`'s `e2e_x86_64_heap_alloc.rs`,
// here observed through the real bridge-emitted shim chain
// (drop -> Bl __rust_dealloc -> __rust_dealloc wrapper -> Bl __rdl_dealloc ->
// our hooked `free`). The exact mangled `__rdl_*` symbol names are DISCOVERED at
// test time from the shim object's `nm` output, so the test does not bake in the
// toolchain's `___rustc` crate hash.
//
// THE ALLOCATION-FAILURE PATH: an intercepted `Box::new` checks the pointer
// `__rust_alloc` returns and, on null, calls `__rust_alloc_error_handler(size,
// align)` exactly as std's `box_new_uninit` -> `handle_alloc_error` does. In
// a real link that symbol comes from libstd, the same object that defines the
// `__rdl_*` entry points (measured with `llvm-nm` on the LLVM-built
// `libdropheap.a`: the `std-*.rcgu.o` member defines both `___rdl_alloc` and
// `___rust_alloc_error_handler`, and the `alloc-*` member references the
// latter). This harness stands in for libstd's allocator, so the driver
// defines the handler too, as a hook that reports `(size, align)` and exits,
// and the scalar driver drives one allocation to failure through it: a missing
// null check stores through null (SIGSEGV) instead.
//
// HOW THE OBJECTS ARE LINKED: every object the bridge emits goes on the link
// line, and the linker keeps what the C `main` reaches (`-Wl,-dead_strip`, which
// rustc itself passes when it links an Apple executable: `--print link-args`,
// measured at -O0). The bridge's default batched mode
// emits ONE object per codegen unit, and that object also carries the bodies
// the mono collector pulled in from the ORIGINAL MIR of the intercepted calls
// (`Box::<T>::new` -> `box_new_uninit` -> `Global::alloc_impl_runtime`, the
// `Box` drop glue): dead here, but `box_new_uninit` references
// `alloc::alloc::handle_alloc_error`, which no object of this link defines.
// LLVM's -O0 object for the same crate carries the same reference from the
// same object (live there, since LLVM does not intercept `Box::new`); a real
// consumer resolves it from the staticlib archive's bundled `liballoc`
// (`box_drop_staticlib_archive_matches_llvm_aarch64` below links exactly
// that way). This file used to pick whole objects by the symbols they define,
// which only worked while every function had its own object: the legacy
// per-function mode, or the batch FALLBACK this crate took until trust-cg
// 5a08e1475 typed the intercepted `__rust_alloc`/`__rust_dealloc` arguments as
// `usize` (`U64`), so the merged module stopped failing with `Call argument 0
// type mismatch .. got I64, expected U64`. The hooked run below is pinned on
// BOTH partitions, so the harness can no longer depend on either.
//
// PROOFS-OFF DIAGNOSTIC: every bridge compile passes the backend's
// `no-proof-certs` knob (`-Ztrust-ir-cg-args=no-proof-certs`; trustc refuses
// the former `TCG_NO_PROOF_CERTS=1` environment spelling). A pass pins native
// runtime semantics only and is never certified-object or exact-object-binding
// evidence. With certificates on, `DROP_CRATE` is refused at proof promotion
// (`[TCG-PROOF-465]`, measured 2026-09-29 on Trust 9192: the frame's
// `StpPreIndex` is statistical sampling; the proof wall of ledger L07-P2).

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "aarch64-apple-darwin";

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_drop_a64_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Every object file a compile wrote into `dir`.
fn objects_in(dir: &Path) -> Vec<PathBuf> {
    let mut objects: Vec<PathBuf> = std::fs::read_dir(dir)
        .expect("read workdir")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
        .collect();
    objects.sort();
    objects
}

/// Run `tool args.. object` and return its stdout; a tool failure fails the test.
fn tool_stdout(tool: &str, args: &[&str], object: &Path) -> String {
    let out = Command::new(tool)
        .args(args)
        .arg(object)
        .output()
        .unwrap_or_else(|e| panic!("spawn {tool} {args:?} {}: {e}", object.display()));
    assert!(
        out.status.success(),
        "{tool} {args:?} {} failed: {}",
        object.display(),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// Address and size of `object`'s `__TEXT,__text` section (`otool -l`).
fn text_section(object: &Path) -> (u64, u64) {
    let listing = tool_stdout("otool", &["-l"], object);
    let mut lines = listing.lines().map(str::trim);
    while let Some(line) = lines.next() {
        if line != "sectname __text" || lines.next() != Some("segname __TEXT") {
            continue;
        }
        let mut field = |key: &str| -> u64 {
            let value = lines
                .next()
                .and_then(|line| line.strip_prefix(key))
                .and_then(|value| value.trim().strip_prefix("0x"))
                .unwrap_or_else(|| {
                    panic!(
                        "otool -l {}: no `{key}` after __TEXT,__text",
                        object.display()
                    )
                });
            u64::from_str_radix(value, 16).expect("hex section field")
        };
        let addr = field("addr");
        let size = field("size");
        return (addr, size);
    }
    panic!(
        "{} has no __TEXT,__text section:\n{listing}",
        object.display()
    )
}

/// `[start, end)` of `symbol`'s body when `object` DEFINES it in
/// `__TEXT,__text`: from its address to the next defined text symbol above it,
/// or to the section end. A batched object holds many functions, so a check
/// about one function must read only this range, never the whole object.
fn function_range(object: &Path, symbol: &str) -> Option<(u64, u64)> {
    let listing = tool_stdout("nm", &["-n", "-m"], object);
    let text: Vec<(u64, &str)> = listing
        .lines()
        .filter_map(|line| {
            let mut fields = line.split_whitespace();
            let addr = u64::from_str_radix(fields.next()?, 16).ok()?;
            if fields.next()? != "(__TEXT,__text)" {
                return None;
            }
            Some((addr, line.split_whitespace().last()?))
        })
        .collect();
    let (start, _) = *text.iter().find(|(_, name)| *name == symbol)?;
    let end = text
        .iter()
        .map(|(addr, _)| *addr)
        .filter(|addr| *addr > start)
        .min()
        .unwrap_or_else(|| {
            let (base, size) = text_section(object);
            base + size
        });
    Some((start, end))
}

/// The one object of `objects` that defines the function `symbol`.
fn defining_object<'a>(objects: &'a [PathBuf], symbol: &str) -> &'a Path {
    let defining: Vec<&PathBuf> = objects
        .iter()
        .filter(|object| function_range(object, symbol).is_some())
        .collect();
    assert_eq!(
        defining.len(),
        1,
        "expected exactly one object to define `{symbol}`; got {defining:?} of {objects:?}"
    );
    defining[0]
}

/// `(type, target)` of each `__TEXT,__text` relocation whose site lies in
/// `symbol`'s body (`otool -rv` prints a site as its offset into the section).
fn function_relocations(object: &Path, symbol: &str) -> Vec<(String, String)> {
    let (start, end) = function_range(object, symbol)
        .unwrap_or_else(|| panic!("{} does not define `{symbol}`", object.display()));
    let (base, _) = text_section(object);
    let mut in_text = false;
    let mut relocations = Vec::new();
    for line in tool_stdout("otool", &["-rv"], object).lines() {
        if line.starts_with("Relocation information") {
            in_text = line.contains("(__TEXT,__text)");
            continue;
        }
        // address pcrel length extern type scattered symbolnum/value
        let fields: Vec<&str> = line.split_whitespace().collect();
        let Some(offset) = fields.first().and_then(|f| u64::from_str_radix(f, 16).ok()) else {
            continue;
        };
        if in_text && fields.len() >= 7 && (start..end).contains(&(base + offset)) {
            relocations.push((fields[4].to_owned(), fields[fields.len() - 1].to_owned()));
        }
    }
    relocations
}

/// The BRANCH26 call sites in `symbol`'s body in `object`: each `bl`'s address
/// (as `otool -tvV` prints it) and its relocation's target symbol. An object's
/// disassembly prints a `bl` to an undefined symbol as a bare address; the
/// relocation names the callee.
fn function_branch_targets(object: &Path, symbol: &str) -> Vec<(u64, String)> {
    let (start, end) = function_range(object, symbol)
        .unwrap_or_else(|| panic!("{} does not define `{symbol}`", object.display()));
    let (base, _) = text_section(object);
    let mut in_text = false;
    let mut targets = Vec::new();
    for line in tool_stdout("otool", &["-rv"], object).lines() {
        if line.starts_with("Relocation information") {
            in_text = line.contains("(__TEXT,__text)");
            continue;
        }
        let fields: Vec<&str> = line.split_whitespace().collect();
        let Some(offset) = fields.first().and_then(|f| u64::from_str_radix(f, 16).ok()) else {
            continue;
        };
        let address = base + offset;
        if in_text && fields.len() >= 7 && fields[4] == "BR26" && (start..end).contains(&address) {
            targets.push((address, fields[fields.len() - 1].to_owned()));
        }
    }
    targets
}

/// The `otool -tvV` lines of `symbol`'s body in `object`.
fn function_disassembly(object: &Path, symbol: &str) -> String {
    let (start, end) = function_range(object, symbol)
        .unwrap_or_else(|| panic!("{} does not define `{symbol}`", object.display()));
    tool_stdout("otool", &["-tvV"], object)
        .lines()
        .filter(|line| {
            line.split('\t')
                .next()
                .and_then(|addr| u64::from_str_radix(addr, 16).ok())
                .is_some_and(|addr| (start..end).contains(&addr))
        })
        .map(|line| format!("{line}\n"))
        .collect()
}

/// Link the C `driver` with EVERY bridge object the way rustc links an Apple
/// executable: `-Wl,-dead_strip` keeps what `main` reaches (the objects carry
/// `MH_SUBSECTIONS_VIA_SYMBOLS`, so each function is its own atom), and an
/// undefined symbol referenced only from a stripped body needs no definition.
/// A symbol a REACHED body references must still resolve, so the link still
/// fails closed on everything the program can run.
fn link_dead_stripped(dir: &Path, bin: &Path, driver: &Path, objects: &[PathBuf]) {
    let mut link = Command::new("cc");
    link.arg("-Wl,-dead_strip").arg("-o").arg(bin).arg(driver);
    link.args(objects);
    link.arg(toolchain_support::write_abort_stubs(dir, objects));
    let link = link.output().expect("cc link");
    assert!(
        link.status.success(),
        "link failed (every symbol a reached body references must resolve). \
         stderr: <<<{}>>>",
        String::from_utf8_lossy(&link.stderr)
    );
}

/// The heap-Drop crate: two exported functions, each boxing a value, computing
/// through the box pointer, and letting the `Box` drop on a normal return — the
/// drop the bridge lowers to `__rust_dealloc(ptr, size, align)`. Both payloads
/// are `Copy`/no-drop (the only destruction is the deallocation itself), which is
/// exactly the slice `lower_box_drop` admits.
///
///   * `ay_box_scalar_drop(x)`     boxes `x: i64`, returns `*b + 1`, drops the box.
///   * `ay_box_struct_drop()`      boxes a 2-field struct, returns `x + y`, drops it.
const DROP_CRATE: &str = "\
#![crate_type = \"staticlib\"]\n\
\n\
#[no_mangle]\n\
pub extern \"C\" fn ay_box_scalar_drop(x: i64) -> i64 {\n\
    let b = Box::new(x);\n\
    let v = *b;\n\
    v + 1\n\
}\n\
\n\
struct S { x: i64, y: i64 }\n\
\n\
#[no_mangle]\n\
pub extern \"C\" fn ay_box_struct_drop() -> i64 {\n\
    let b = Box::new(S { x: 20, y: 22 });\n\
    let s = b.x + b.y;\n\
    s\n\
}\n";

/// The `__rdl_*` mangled symbols the allocator shim forwards to. We discover the
/// exact mangled names (which embed the toolchain's `___rustc` crate hash) from
/// the shim object so the C driver can DEFINE them without baking in that hash.
struct RdlSymbols {
    alloc: String,
    dealloc: String,
    realloc: String,
    alloc_zeroed: String,
    /// `__rust_alloc_error_handler`, when a bridge object calls it (the null
    /// branch of a checked allocation); libstd defines it in a real link.
    alloc_error_handler: Option<String>,
}

/// The `__rust_alloc_error_handler` symbol some object of `objects` calls but
/// none defines, if any (`nm -u` lists undefined symbols by name).
fn undefined_alloc_error_handler(objects: &[PathBuf]) -> Option<String> {
    objects.iter().find_map(|object| {
        tool_stdout("nm", &["-u"], object)
            .lines()
            .map(str::trim)
            .find(|name| name.ends_with("_rust_alloc_error_handler"))
            .map(str::to_owned)
    })
}

/// The C definition of the allocation-error hook: report the failed layout,
/// then exit 0 (the driver's expected end once it has driven a failure). The
/// mangled symbol starts with `__`, used verbatim as the `__asm__` label.
fn alloc_error_handler_definition(syms: &RdlSymbols) -> String {
    syms.alloc_error_handler
        .as_ref()
        .map(|symbol| {
            format!(
                "void ay_alloc_error_handler(unsigned long size, unsigned long align)\n\
                     __asm__(\"{symbol}\");\n\
                 void ay_alloc_error_handler(unsigned long size, unsigned long align) {{\n\
                     printf(\"alloc_error size=%lu align=%lu\\n\", size, align);\n\
                     exit(0);\n\
                 }}\n"
            )
        })
        .unwrap_or_default()
}

/// Read the allocator-shim object's UNDEFINED `__rdl_*` symbols (`nm` prints
/// undefined symbols with a `U` kind). On Mach-O each carries a leading `_` C
/// prefix on top of the Rust `_RNv...` mangling, so the printed name is
/// `__RNv..._rdl_dealloc`; that is the exact symbol the C driver must define.
fn discover_rdl_symbols(shim_obj: &Path, objects: &[PathBuf]) -> RdlSymbols {
    let out = Command::new("nm")
        .arg(shim_obj)
        .output()
        .expect("nm on allocator shim object");
    let text = String::from_utf8_lossy(&out.stdout);
    let find = |suffix: &str| -> String {
        text.lines()
            .filter_map(|l| {
                let mut it = l.split_whitespace();
                let kind = it.next();
                // `U <name>` (undefined): the leading address column is absent.
                if kind == Some("U") {
                    return it.next();
                }
                None
            })
            .find(|name| name.ends_with(suffix))
            .unwrap_or_else(|| {
                panic!("allocator shim object did not reference an `{suffix}` symbol.\nnm:\n{text}")
            })
            .to_string()
    };
    RdlSymbols {
        alloc: find("_rdl_alloc"),
        dealloc: find("_rdl_dealloc"),
        realloc: find("_rdl_realloc"),
        alloc_zeroed: find("_rdl_alloc_zeroed"),
        alloc_error_handler: undefined_alloc_error_handler(objects),
    }
}

/// The C driver: defines the System-allocator entry points the shim forwards to
/// (`__rdl_*`) as instrumented malloc/free hooks, calls each exported Drop
/// function, and exits 0 iff (1) the boxed value is correct and (2) the Drop ran
/// the deallocation (a free was observed for each allocation). A `__asm__` label
/// binds each C definition to the exact discovered mangled symbol.
fn build_driver(syms: &RdlSymbols) -> String {
    // The mangled symbols start with `__` (C-prefix `_` + Rust `_RNv...`); inside
    // a `__asm__("...")` label clang emits the literal text verbatim (it does NOT
    // add a further leading underscore), so the label IS the full object symbol.
    format!(
        "#include <stdio.h>\n\
         #include <stdlib.h>\n\
         \n\
         extern long ay_box_scalar_drop(long x);\n\
         extern long ay_box_struct_drop(void);\n\
         \n\
         static long alloc_calls = 0;\n\
         static long dealloc_calls = 0;\n\
         static int fail_next_alloc = 0;\n\
         \n\
         void *ay_rdl_alloc(unsigned long size, unsigned long align)\n\
             __asm__(\"{alloc}\");\n\
         void *ay_rdl_alloc(unsigned long size, unsigned long align) {{\n\
             (void)align; alloc_calls++;\n\
             if (fail_next_alloc) {{ fail_next_alloc = 0; return NULL; }}\n\
             return malloc(size);\n\
         }}\n\
         \n\
         void ay_rdl_dealloc(void *ptr, unsigned long size, unsigned long align)\n\
             __asm__(\"{dealloc}\");\n\
         void ay_rdl_dealloc(void *ptr, unsigned long size, unsigned long align) {{\n\
             (void)size; (void)align; dealloc_calls++; free(ptr);\n\
         }}\n\
         \n\
         void *ay_rdl_realloc(void *ptr, unsigned long old_size, unsigned long align,\n\
                              unsigned long new_size)\n\
             __asm__(\"{realloc}\");\n\
         void *ay_rdl_realloc(void *ptr, unsigned long old_size, unsigned long align,\n\
                              unsigned long new_size) {{\n\
             (void)old_size; (void)align; return realloc(ptr, new_size);\n\
         }}\n\
         \n\
         void *ay_rdl_alloc_zeroed(unsigned long size, unsigned long align)\n\
             __asm__(\"{alloc_zeroed}\");\n\
         void *ay_rdl_alloc_zeroed(unsigned long size, unsigned long align) {{\n\
             (void)align; alloc_calls++; return calloc(1, size);\n\
         }}\n\
         \n\
         {handler}\
         \n\
         int main(void) {{\n\
             long scalar = ay_box_scalar_drop(41);\n\
             long aggregate = ay_box_struct_drop();\n\
             printf(\"scalar=%ld aggregate=%ld alloc_calls=%ld dealloc_calls=%ld\\n\",\n\
                    scalar, aggregate, alloc_calls, dealloc_calls);\n\
             if (scalar != 42) return 1;          /* value through the scalar box */\n\
             if (aggregate != 42) return 2;       /* value through the aggregate box */\n\
             if (alloc_calls < 2) return 3;       /* both boxes heap-allocated */\n\
             if (dealloc_calls < 2) return 4;     /* both Drops freed (the point) */\n\
             fflush(stdout);\n\
             /* Allocation failure: the box's allocation returns NULL, so the\n\
                handler must run (it exits 0) before anything is stored. */\n\
             fail_next_alloc = 1;\n\
             ay_box_scalar_drop(41);\n\
             return 5;                            /* failure path returned */\n\
         }}\n",
        alloc = syms.alloc,
        dealloc = syms.dealloc,
        realloc = syms.realloc,
        alloc_zeroed = syms.alloc_zeroed,
        handler = alloc_error_handler_definition(syms),
    )
}

/// Allocator-hook driver for the address-taken `Box::new` case. This path must
/// call the real monomorphized constructor through a function pointer, return
/// the stored value, and still deallocate exactly once.
fn build_indirect_box_driver(syms: &RdlSymbols) -> String {
    format!(
        "#include <stdio.h>\n\
         #include <stdlib.h>\n\
         \n\
         extern int ay_indirect_box_new(int x);\n\
         \n\
         static long alloc_calls = 0;\n\
         static long dealloc_calls = 0;\n\
         \n\
         void *ay_rdl_alloc(unsigned long size, unsigned long align)\n\
             __asm__(\"{alloc}\");\n\
         void *ay_rdl_alloc(unsigned long size, unsigned long align) {{\n\
             (void)align; alloc_calls++; return malloc(size);\n\
         }}\n\
         \n\
         void ay_rdl_dealloc(void *ptr, unsigned long size, unsigned long align)\n\
             __asm__(\"{dealloc}\");\n\
         void ay_rdl_dealloc(void *ptr, unsigned long size, unsigned long align) {{\n\
             (void)size; (void)align; dealloc_calls++; free(ptr);\n\
         }}\n\
         \n\
         void *ay_rdl_realloc(void *ptr, unsigned long old_size, unsigned long align,\n\
                              unsigned long new_size)\n\
             __asm__(\"{realloc}\");\n\
         void *ay_rdl_realloc(void *ptr, unsigned long old_size, unsigned long align,\n\
                              unsigned long new_size) {{\n\
             (void)old_size; (void)align; return realloc(ptr, new_size);\n\
         }}\n\
         \n\
         void *ay_rdl_alloc_zeroed(unsigned long size, unsigned long align)\n\
             __asm__(\"{alloc_zeroed}\");\n\
         void *ay_rdl_alloc_zeroed(unsigned long size, unsigned long align) {{\n\
             (void)align; alloc_calls++; return calloc(1, size);\n\
         }}\n\
         \n\
         {handler}\
         \n\
         int main(void) {{\n\
             int value = ay_indirect_box_new(42);\n\
             printf(\"value=%d alloc_calls=%ld dealloc_calls=%ld\\n\",\n\
                    value, alloc_calls, dealloc_calls);\n\
             if (value != 42) return 1;\n\
             if (alloc_calls != 1) return 2;\n\
             if (dealloc_calls != 1) return 3;\n\
             return 0;\n\
         }}\n",
        alloc = syms.alloc,
        dealloc = syms.dealloc,
        realloc = syms.realloc,
        alloc_zeroed = syms.alloc_zeroed,
        handler = alloc_error_handler_definition(syms),
    )
}

/// Compile `DROP_CRATE` through the bridge with `knobs` to objects, link EVERY
/// object it emits into the hooked C driver, and run it (`label` names the work
/// directory and the failure messages). Returns how many objects the compile
/// emitted and whether ONE object defines both exported entries.
fn hooked_box_drop_links_and_runs(dylib: &Path, label: &str, knobs: &[&str]) -> (usize, bool) {
    let dir = workdir(label);

    // 1. Compile the heap-Drop crate THROUGH THE BRIDGE to objects.
    let src_path = dir.join("dropheap.rs");
    std::fs::write(&src_path, DROP_CRATE).expect("write source");
    let backend_arg = {
        let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
        s.push(dylib);
        s
    };
    let obj_out = dir.join("dropheap");
    let output = toolchain_support::rustc_command()
        .args(["--crate-type", "staticlib"])
        .arg(&backend_arg)
        .arg(toolchain_support::backend_knobs_arg(knobs))
        .args(["--target", TARGET, "-Cpanic=abort", "-Copt-level=0"])
        .arg("--emit=obj")
        .arg("-o")
        .arg(&obj_out)
        .arg(&src_path)
        .output()
        .expect("failed to spawn trustc");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "{label}: bridge failed to compile the heap-Drop crate. stderr: <<<{stderr}>>>"
    );
    let objs = objects_in(&dir);
    assert!(
        !objs.is_empty(),
        "{label}: bridge produced no object file. stderr: <<<{stderr}>>>"
    );

    // The drop's `__rust_dealloc` call must be a BRANCH26 direct-call relocation
    // in the body of EACH exported entry (`lower_box_drop` emits it in place of a
    // call to the `Box` drop glue). Read inside the entry's own address range: a
    // batched object also holds the collector's `Box` drop glue, whose own
    // `__rust_dealloc` call must not stand in for the entry's. This pins
    // emission behavior; it does not grant production Certified relocation
    // authority. (`otool -rv` prints the relocation type `BR26`.)
    for entry in ["_ay_box_scalar_drop", "_ay_box_struct_drop"] {
        let object = defining_object(&objs, entry);
        let relocations = function_relocations(object, entry);
        assert!(
            relocations
                .iter()
                .any(|(kind, target)| kind == "BR26" && target.ends_with("_rust_dealloc")),
            "{label}: expected a BRANCH26 (BR26) relocation targeting `__rust_dealloc` (the \
             drop's deallocation call) inside `{entry}` in {}; its relocations: {relocations:?}",
            object.display()
        );
        // The entry's `Box::new` allocation is checked: its null branch calls
        // the allocation-error entry from inside the same body.
        assert!(
            relocations
                .iter()
                .any(|(kind, target)| kind == "BR26"
                    && target.ends_with("_rust_alloc_error_handler")),
            "{label}: expected a BRANCH26 call to `__rust_alloc_error_handler` (the \
             allocation-failure branch of the intercepted `Box::new`) inside `{entry}` in {}; \
             its relocations: {relocations:?}",
            object.display()
        );
    }

    // The allocator shim object references the `__rdl_*` System-allocator symbols
    // the wrappers forward to; discover their exact mangled names from the one
    // object that has the undefined references (the shim CGU).
    let shim_obj = objs
        .iter()
        .find(|o| tool_stdout("nm", &[], o).contains("_rdl_dealloc"))
        .unwrap_or_else(|| {
            panic!("{label}: no bridge object references `__rdl_dealloc` (allocator shim missing)")
        });
    let syms = discover_rdl_symbols(shim_obj, &objs);
    assert!(
        syms.alloc_error_handler.is_some(),
        "{label}: no bridge object calls `__rust_alloc_error_handler`, so an intercepted \
         `Box::new` has no allocation-failure path (`emit_rust_alloc_checked`)"
    );

    // 2. Link EVERY bridge object with the C driver (which defines the `__rdl_*`
    //    hooks + main), dead-stripped from `main` (see the file comment). The
    //    drop's `Bl __rust_dealloc` BRANCH26 relocation, the `Bl __rust_alloc`,
    //    and the shim's `Bl __rdl_*` all resolve here.
    let driver_path = dir.join("driver.c");
    std::fs::write(&driver_path, build_driver(&syms)).expect("write driver.c");
    let bin = dir.join("bin");
    link_dead_stripped(&dir, &bin, &driver_path, &objs);

    // 3. RUN natively on aarch64: exit 0 iff the boxed values are correct AND the
    //    Drops freed them (the hooked __rdl_dealloc was reached >= 2 times).
    let run = Command::new(&bin).output().expect("run linked binary");
    let stdout = String::from_utf8_lossy(&run.stdout);
    let code = run.status.code().expect("process terminated by signal");
    assert_eq!(
        code, 0,
        "{label}: drop-heap driver returned {code} (1=wrong scalar value, 2=wrong aggregate \
         value, 3=no allocation observed, 4=NO DEALLOCATION observed == the Drop's \
         __rust_dealloc never ran, 5=a failed allocation RETURNED instead of reaching the \
         allocation-error handler). stdout: {stdout:?}"
    );
    assert!(
        stdout.contains("scalar=42")
            && stdout.contains("aggregate=42")
            && stdout.contains("dealloc_calls=2"),
        "{label}: expected both boxed values correct and exactly two observed deallocations; \
         got stdout: {stdout:?}"
    );
    assert!(
        stdout.contains("alloc_error size=8 align=8"),
        "{label}: the failed 8-byte, 8-aligned `Box<i64>` allocation did not reach the \
         allocation-error handler with its layout; got stdout: {stdout:?}"
    );

    let shared = defining_object(&objs, "_ay_box_scalar_drop")
        == defining_object(&objs, "_ay_box_struct_drop");
    let count = objs.len();
    let _ = std::fs::remove_dir_all(&dir);
    (count, shared)
}

#[test]
fn box_drop_frees_heap_value_and_links_runs_aarch64() {
    // The backend knob option, Darwin rust-std and `cc` are required here; a
    // missing one fails the test by name instead of returning early.
    darwin_native::require("drop_heap_aarch64", &["cc"]);
    let dylib = ensure_dylib_built();

    // The default (batched) mode: one object per codegen unit, holding the
    // entries AND the collector-only glue. The legacy per-function mode: one
    // object per function. The same link and run must pass on both.
    let batched = hooked_box_drop_links_and_runs(&dylib, "batched", &["no-proof-certs"]);
    let per_function =
        hooked_box_drop_links_and_runs(&dylib, "per_fn", &["no-proof-certs", "batch-cgu=0"]);

    // The two rows must really be two partitions, or one of them tests nothing
    // new: if the batched compile FELL BACK to per-function objects (a merge or
    // merged-compile failure, as it did for this crate before trust-cg
    // 5a08e1475), the batched row would silently re-run the per-function shape.
    // Read by DEFINED symbol: batched, one object defines both entries.
    assert!(
        batched.1 && !per_function.1 && batched.0 < per_function.0,
        "the two compiles are not the batched and the per-function partitions \
         ((objects, entries share one object): batched {batched:?}, per-function \
         {per_function:?}); a batched compile that fell back to per-function objects \
         would leave the batched link untested"
    );

    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// A reified `Box::new` function item bypasses direct-call interception, so the
/// indirect call reaches the real monomorphized `Box::<i32>::new` symbol. That
/// body must remain live and executable; classifying every collected
/// `Box::<T>::new` as dead would replace this reachable symbol with a trap.
#[test]
fn address_taken_box_new_links_runs_without_reachable_trap_aarch64() {
    // The backend knob option, Darwin rust-std and `cc` are required here; a
    // missing one fails the test by name instead of returning early.
    darwin_native::require("drop_heap_aarch64", &["cc"]);

    let dylib = ensure_dylib_built();
    let dir = workdir("indirect_box_new");
    let src = "\
#![crate_type = \"staticlib\"]\n\
#[no_mangle]\n\
pub extern \"C\" fn ay_indirect_box_new(x: i32) -> i32 {\n\
    let ctor: fn(i32) -> Box<i32> = Box::new;\n\
    let boxed = ctor(x);\n\
    *boxed\n\
}\n";
    let src_path = dir.join("indirect_box_new.rs");
    std::fs::write(&src_path, src).expect("write source");
    let backend_arg = {
        let mut value = std::ffi::OsString::from("-Zcodegen-backend=");
        value.push(&dylib);
        value
    };
    let output = toolchain_support::rustc_command()
        .args(["--crate-type", "staticlib"])
        .arg(&backend_arg)
        .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]))
        .args(["--target", TARGET, "-Cpanic=abort", "-Copt-level=0"])
        .arg("--emit=obj")
        .arg("-o")
        .arg(dir.join("indirect_box_new"))
        .arg(&src_path)
        .output()
        .expect("spawn rustc through bridge");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "bridge failed to compile address-taken Box::new. stderr: <<<{stderr}>>>"
    );

    let all_objs = objects_in(&dir);
    const ENTRY: &str = "_ay_indirect_box_new";
    let entry_obj = defining_object(&all_objs, ENTRY);
    // The entry takes Box::new's address: a PAGE21/PAGEOFF12 pair naming the
    // monomorphized symbol (CGU-private when it shares the entry's object, a
    // plain undefined symbol when it does not). Read from the entry's own body.
    let entry_relocations = function_relocations(entry_obj, ENTRY);
    let box_new_symbol = entry_relocations
        .iter()
        .map(|(_, target)| target.as_str())
        .find(|symbol| symbol.contains("5boxed") && symbol.contains("3new"))
        .unwrap_or_else(|| {
            panic!(
                "entry does not reference the monomorphized Box::new symbol; its \
                 relocations: {entry_relocations:?}"
            )
        });
    let box_new_obj = defining_object(&all_objs, box_new_symbol);
    let box_new_relocations = function_relocations(box_new_obj, box_new_symbol);
    assert!(
        box_new_relocations
            .iter()
            .any(|(kind, target)| kind == "BR26" && target.ends_with("_rust_alloc")),
        "real Box::new body must allocate rather than be a body-less stub; its \
         relocations: {box_new_relocations:?}"
    );
    let box_new_disassembly = function_disassembly(box_new_obj, box_new_symbol);
    // The body must not be REPLACED by a trap. Outlined guard stubs (bl ->
    // brk sequences appended after the terminal ret) are legitimate: since
    // 30ea9c0e the register-bound TrapBoundsCheckExact carriers expand to
    // real runtime checks, and without replayed elision authority those
    // checks are RETAINED — the fail-closed contract. Police the hot path
    // (everything before the first ret) for traps instead.
    let hot_path = box_new_disassembly
        .split_once("\tret")
        .map_or(box_new_disassembly.as_ref(), |(before, _)| before);
    // A `brk` right after a `bl` whose relocation targets
    // `__rust_alloc_error_handler` is the unreachable marker that follows that
    // call, which does not return — the allocation-failure branch of the
    // checked allocation (LLVM emits the same `bl; brk` after a noreturn call)
    // — not a trap standing in for the body. Any other `brk` (including one
    // after a `bl` to anything else) is a trap.
    let handler_calls: Vec<u64> = function_branch_targets(box_new_obj, box_new_symbol)
        .into_iter()
        .filter(|(_, target)| target.ends_with("_rust_alloc_error_handler"))
        .map(|(address, _)| address)
        .collect();
    assert!(
        !handler_calls.is_empty(),
        "real Box::new body's allocation has no allocation-failure call to \
         `__rust_alloc_error_handler`; its relocations: {box_new_relocations:?}"
    );
    let mut after_handler_call = false;
    let mut trap_in_hot_path = false;
    for line in hot_path.lines() {
        let mut fields = line.split('\t');
        let address = fields.next().and_then(|a| u64::from_str_radix(a, 16).ok());
        let mnemonic = fields.next().unwrap_or("");
        if mnemonic == "brk" && !after_handler_call {
            trap_in_hot_path = true;
        }
        after_handler_call =
            mnemonic == "bl" && address.is_some_and(|a| handler_calls.contains(&a));
    }
    assert!(
        !hot_path.is_empty() && !trap_in_hot_path,
        "reachable Box::new body was replaced by a trap:\n{box_new_disassembly}"
    );
    let entry_disassembly = function_disassembly(entry_obj, ENTRY);
    assert!(
        entry_disassembly.contains("\tblr\t"),
        "fixture no longer exercises an indirect call:\n{entry_disassembly}"
    );

    let shim_obj = all_objs
        .iter()
        .find(|object| tool_stdout("nm", &[], object).contains("_rdl_dealloc"))
        .expect("no allocator shim object was emitted");
    let syms = discover_rdl_symbols(shim_obj, &all_objs);
    let driver_path = dir.join("indirect_driver.c");
    std::fs::write(&driver_path, build_indirect_box_driver(&syms))
        .expect("write indirect Box::new driver");
    let bin = dir.join("indirect_box_new_bin");
    link_dead_stripped(&dir, &bin, &driver_path, &all_objs);

    let run = Command::new(&bin)
        .output()
        .expect("run address-taken Box::new driver");
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert_eq!(
        run.status.code(),
        Some(0),
        "address-taken Box::new trapped or returned the wrong result. stdout: \
         {stdout:?}; stderr: {:?}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert!(
        stdout.contains("value=42 alloc_calls=1 dealloc_calls=1"),
        "address-taken Box::new did not allocate, return, and deallocate once: {stdout:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// The C program of the archive differential: the same two entries, printed.
const ARCHIVE_DRIVER: &str = "\
#include <stdio.h>
extern long ay_box_scalar_drop(long x);
extern long ay_box_struct_drop(void);
int main(void) {
    printf(\"scalar=%ld aggregate=%ld\\n\", ay_box_scalar_drop(41), ay_box_struct_drop());
    return 0;
}
";

/// `DROP_CRATE` consumed the way a staticlib ships: rustc builds
/// `libdropheap.a` (the crate's objects plus the bundled `std`/`alloc`/`core`
/// that define `__rdl_*` and `handle_alloc_error`), and the C driver links the
/// ARCHIVE with a plain `cc`. Bridge against LLVM at -O0..-O3, one and four
/// codegen units: exit status and stdout must match.
#[test]
fn box_drop_staticlib_archive_matches_llvm_aarch64() {
    const TEST: &str = "box_drop_staticlib_archive_matches_llvm_aarch64";
    darwin_native::require(TEST, &["cc"]);
    let dylib = ensure_dylib_built();
    let dir = workdir("archive");
    let src = dir.join("dropheap.rs");
    std::fs::write(&src, DROP_CRATE).expect("write source");
    let driver = dir.join("driver.c");
    std::fs::write(&driver, ARCHIVE_DRIVER).expect("write driver");

    // (exit code, signal, stdout) of one build's run, or why it did not build.
    type Ending = (Option<i32>, Option<i32>, String);
    let build = |backend: Option<&Path>, opt: &str, cgus: &str| -> Result<Ending, String> {
        use std::os::unix::process::ExitStatusExt;
        let out = dir.join(format!(
            "{}_O{opt}_c{cgus}",
            if backend.is_some() { "cg" } else { "llvm" }
        ));
        std::fs::create_dir_all(&out).expect("create row dir");
        let mut cmd = toolchain_support::rustc_command();
        cmd.args(["--crate-type", "staticlib", "--crate-name", "dropheap"])
            .args(["--target", TARGET, "-Cpanic=abort"])
            .arg(format!("-Copt-level={opt}"))
            .arg(format!("-Ccodegen-units={cgus}"));
        if let Some(dylib) = backend {
            let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
            backend_arg.push(dylib);
            cmd.arg(backend_arg);
            cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
        }
        let compiled = cmd
            .arg("--out-dir")
            .arg(&out)
            .arg(&src)
            .output()
            .expect("spawn trustc");
        if !compiled.status.success() {
            return Err(format!(
                "compile failed ({}): <<<{}>>>",
                compiled.status,
                String::from_utf8_lossy(&compiled.stderr)
            ));
        }
        let bin = out.join("prog");
        let link = Command::new("cc")
            .arg("-o")
            .arg(&bin)
            .arg(&driver)
            .arg(out.join("libdropheap.a"))
            .output()
            .expect("spawn cc");
        if !link.status.success() {
            return Err(format!(
                "archive link failed: <<<{}>>>",
                String::from_utf8_lossy(&link.stderr)
            ));
        }
        let run = Command::new(&bin).output().expect("run the linked program");
        Ok((
            run.status.code(),
            run.status.signal(),
            String::from_utf8_lossy(&run.stdout).into_owned(),
        ))
    };

    let mut rows = 0;
    let mut failures = Vec::new();
    for opt in ["0", "1", "2", "3"] {
        let oracle = build(None, opt, "1")
            .unwrap_or_else(|error| panic!("-O{opt}: the LLVM oracle: {error}"));
        assert_eq!(
            oracle,
            (Some(0), None, "scalar=42 aggregate=42\n".to_owned()),
            "-O{opt}: the LLVM oracle's own result changed"
        );
        for cgus in ["1", "4"] {
            rows += 1;
            match build(Some(&dylib), opt, cgus) {
                Ok(bridge) if bridge == oracle => {
                    eprintln!("archive -O{opt} -Ccodegen-units={cgus}: MATCH");
                }
                Ok(bridge) => failures.push(format!(
                    "-O{opt} -Ccodegen-units={cgus}: DIVERGES — LLVM {oracle:?}, trust-cg {bridge:?}"
                )),
                Err(error) => failures.push(format!("-O{opt} -Ccodegen-units={cgus}: {error}")),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "{} of {rows} archive row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    assert_eq!(rows, 8, "the archive row denominator changed");
    eprintln!("BOX_DROP_ARCHIVE rows=8 matched=8");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

// Linux ELF twin: `drop_heap_linux.rs` compiles `DROP_CRATE` and the
// address-taken crate and runs these drivers (`build_driver`,
// `build_indirect_box_driver`, `ARCHIVE_DRIVER`) for aarch64-unknown-linux-gnu;
// keep the two byte-identical.
