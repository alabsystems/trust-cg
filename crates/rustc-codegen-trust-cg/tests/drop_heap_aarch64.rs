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
// PROOF GATE: compiled with `TCG_NO_PROOF_CERTS=1`. The drop's BRANCH26 row and
// the per-instruction mappings are proven, but the final Mach-O object also
// emits compact-unwind `ARM64_RELOC_UNSIGNED` rows. Those rows are now included
// in the complete production-surface inventory and remain unproven, so this
// runtime lane must not claim certified-object authority or exact-object binding.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "aarch64-apple-darwin";

fn pinned_toolchain() -> String {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let toolchain = std::fs::read_to_string(crate_dir.join("rust-toolchain.toml"))
        .expect("failed to read rust-toolchain.toml");
    for line in toolchain.lines() {
        let line = line.trim();
        if let Some(raw_channel) = line.strip_prefix("channel") {
            let Some((_, value)) = raw_channel.split_once('=') else {
                continue;
            };
            return value.trim().trim_matches('"').to_owned();
        }
    }
    panic!("rust-toolchain.toml did not contain a channel");
}

fn ensure_dylib_built() -> PathBuf {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let target_dir = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| crate_dir.join("target"));
    let candidates = [
        target_dir
            .join("release")
            .join("librustc_codegen_trust_cg.dylib"),
        target_dir
            .join("debug")
            .join("librustc_codegen_trust_cg.dylib"),
    ];
    for cand in &candidates {
        if cand.exists() {
            return cand.clone();
        }
    }
    let status = Command::new("cargo")
        .arg(format!("+{}", pinned_toolchain()))
        .args(["build"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run drop-heap test");
    let built = target_dir
        .join("debug")
        .join("librustc_codegen_trust_cg.dylib");
    assert!(built.exists(), "expected dylib at {built:?} but none produced");
    built
}

fn aarch64_std_available() -> bool {
    let output = Command::new("rustup")
        .args(["target", "list", "--installed", "--toolchain"])
        .arg(pinned_toolchain())
        .output();
    match output {
        Ok(output) => String::from_utf8_lossy(&output.stdout)
            .lines()
            .any(|line| line.trim() == TARGET),
        Err(_) => false,
    }
}

fn host_is_aarch64_macos() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

fn has_cc() -> bool {
    Command::new("cc")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_drop_a64_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
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
}

/// Read the allocator-shim object's UNDEFINED `__rdl_*` symbols (`nm` prints
/// undefined symbols with a `U` kind). On Mach-O each carries a leading `_` C
/// prefix on top of the Rust `_RNv...` mangling, so the printed name is
/// `__RNv..._rdl_dealloc`; that is the exact symbol the C driver must define.
fn discover_rdl_symbols(shim_obj: &Path) -> RdlSymbols {
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
         int main(void) {{\n\
             long scalar = ay_box_scalar_drop(41);\n\
             long aggregate = ay_box_struct_drop();\n\
             printf(\"scalar=%ld aggregate=%ld alloc_calls=%ld dealloc_calls=%ld\\n\",\n\
                    scalar, aggregate, alloc_calls, dealloc_calls);\n\
             if (scalar != 42) return 1;          /* value through the scalar box */\n\
             if (aggregate != 42) return 2;       /* value through the aggregate box */\n\
             if (alloc_calls < 2) return 3;       /* both boxes heap-allocated */\n\
             if (dealloc_calls < 2) return 4;     /* both Drops freed (the point) */\n\
             return 0;\n\
         }}\n",
        alloc = syms.alloc,
        dealloc = syms.dealloc,
        realloc = syms.realloc,
        alloc_zeroed = syms.alloc_zeroed,
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
    )
}

#[test]
fn box_drop_frees_heap_value_and_links_runs_aarch64() {
    if !host_is_aarch64_macos() {
        eprintln!("skipping: requires an aarch64-apple-darwin host");
        return;
    }
    if !aarch64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    if !has_cc() {
        eprintln!("skipping: cc not available");
        return;
    }

    let dylib = ensure_dylib_built();
    let dir = workdir("box");

    // 1. Compile the heap-Drop crate THROUGH THE BRIDGE to objects.
    let src_path = dir.join("dropheap.rs");
    std::fs::write(&src_path, DROP_CRATE).expect("write source");
    let backend_arg = {
        let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
        s.push(&dylib);
        s
    };
    let obj_out = dir.join("dropheap");
    let output = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "staticlib"])
        .arg(&backend_arg)
        .env("TCG_NO_PROOF_CERTS", "1")
        .args(["--target", TARGET, "-Cpanic=abort", "-Copt-level=0"])
        .arg("--emit=obj")
        .arg("-o")
        .arg(&obj_out)
        .arg(&src_path)
        .output()
        .expect("failed to spawn rustc via rustup");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "bridge failed to compile the heap-Drop crate. stderr: <<<{stderr}>>>"
    );

    // rustc places each function in its own CGU, so the bridge emits one object
    // per function plus the allocator shim. Collect them ALL first.
    let all_objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    assert!(
        !all_objs.is_empty(),
        "bridge produced no object file. stderr: <<<{stderr}>>>"
    );

    // Link only the program-REACHABLE object closure: the exported `ay_box_*`
    // entry points and the allocator-shim wrappers (`__rust_*`). Because the
    // bridge INTERCEPTS `Box::new`/`Box`-drop (synthesizing the alloc/free inline
    // against `__rust_alloc`/`__rust_dealloc`, see `lower_box_drop`), the real
    // `alloc::boxed::Box::new` / `drop_in_place` and deeper CGUs the compiler
    // still mono-collected for these direct-only call sites are outside the
    // bridge-emitted call closure. Some collector-only glue references
    // Rust-internal functions the bridge legitimately skipped (e.g.
    // `box_new_uninit`), and the bridge itself warns they "must be unreachable
    // from the program for the link to succeed". The entry objects reference
    // only `__rust_alloc`/`__rust_dealloc`/`abort` (the alloc/free is fully
    // described by the shim chain), so this closure is sound and complete.
    // Selection is by DEFINED symbol, never by filename.
    let defines_reachable = |obj: &Path| -> bool {
        let nm = String::from_utf8_lossy(
            &Command::new("nm").arg(obj).output().expect("nm").stdout,
        )
        .into_owned();
        nm.lines().any(|l| {
            let mut it = l.split_whitespace();
            let kind = it.nth(1); // address, KIND, name
            let name = it.next();
            // A DEFINED (non-`U`) symbol that is an exported entry point or an
            // allocator-shim wrapper.
            kind.map(|k| k != "U").unwrap_or(false)
                && name
                    .map(|n| {
                        n == "_ay_box_scalar_drop"
                            || n == "_ay_box_struct_drop"
                            || n.contains("___rust_alloc")
                            || n.contains("___rust_dealloc")
                            || n.contains("___rust_realloc")
                            || n.contains("___rust_alloc_zeroed")
                            || n.contains("_no_alloc_shim_is_unstable")
                    })
                    .unwrap_or(false)
        })
    };
    let objs: Vec<PathBuf> = all_objs
        .iter()
        .filter(|o| defines_reachable(o))
        .cloned()
        .collect();
    assert!(
        objs.iter().any(|o| {
            String::from_utf8_lossy(&Command::new("nm").arg(o).output().expect("nm").stdout)
                .contains("_ay_box_scalar_drop")
        }) && objs.iter().any(|o| {
            String::from_utf8_lossy(&Command::new("nm").arg(o).output().expect("nm").stdout)
                .contains("___rust_dealloc")
        }),
        "did not find both the exported entry objects and the allocator-shim object \
         among the bridge output. objects: {all_objs:?}"
    );

    // The drop's `__rust_dealloc` call must be present as a BRANCH26 direct-call
    // relocation in some object. This pins emission behavior; it does not grant
    // production Certified relocation authority.
    // (`otool -rv` prints the relocation type `BR26` and the target symbol.)
    let reloc_dump: String = objs
        .iter()
        .map(|o| {
            String::from_utf8_lossy(
                &Command::new("otool")
                    .args(["-rv"])
                    .arg(o)
                    .output()
                    .expect("otool -rv")
                    .stdout,
            )
            .into_owned()
        })
        .collect();
    assert!(
        reloc_dump
            .lines()
            .any(|l| l.contains("BR26") && l.contains("_rust_dealloc")),
        "expected a BRANCH26 (BR26) relocation targeting `__rust_dealloc` (the drop's \
         deallocation call). otool -rv across objects:\n{reloc_dump}"
    );

    // The allocator shim object references the `__rdl_*` System-allocator symbols
    // the wrappers forward to; discover their exact mangled names from any object
    // that has the undefined references (the shim CGU).
    let shim_obj = objs
        .iter()
        .find(|o| {
            String::from_utf8_lossy(&Command::new("nm").arg(o).output().expect("nm").stdout)
                .contains("_rdl_dealloc")
        })
        .expect("no bridge object references `__rdl_dealloc` (allocator shim missing)");
    let syms = discover_rdl_symbols(shim_obj);

    // 2. Link ALL bridge objects with the C driver (which defines the `__rdl_*`
    //    hooks + main). The drop's `Bl __rust_dealloc` BRANCH26 relocation, the
    //    `Bl __rust_alloc`, and the shim's `Bl __rdl_*` all resolve here.
    let driver_path = dir.join("driver.c");
    std::fs::write(&driver_path, build_driver(&syms)).expect("write driver.c");
    let bin = dir.join("bin");
    let mut link = Command::new("cc");
    link.arg("-o").arg(&bin).arg(&driver_path);
    for o in &objs {
        link.arg(o);
    }
    let link = link.output().expect("cc link");
    assert!(
        link.status.success(),
        "link failed (the drop's __rust_dealloc / shim symbols must resolve). \
         stderr: <<<{}>>>",
        String::from_utf8_lossy(&link.stderr)
    );

    // 3. RUN natively on aarch64: exit 0 iff the boxed values are correct AND the
    //    Drops freed them (the hooked __rdl_dealloc was reached >= 2 times).
    let run = Command::new(&bin).output().expect("run linked binary");
    let stdout = String::from_utf8_lossy(&run.stdout);
    let code = run.status.code().expect("process terminated by signal");
    assert_eq!(
        code, 0,
        "drop-heap driver returned {code} (1=wrong scalar value, 2=wrong aggregate \
         value, 3=no allocation observed, 4=NO DEALLOCATION observed == the Drop's \
         __rust_dealloc never ran). stdout: {stdout:?}"
    );
    assert!(
        stdout.contains("scalar=42")
            && stdout.contains("aggregate=42")
            && stdout.contains("dealloc_calls=2"),
        "expected both boxed values correct and exactly two observed deallocations; \
         got stdout: {stdout:?}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

/// A reified `Box::new` function item bypasses direct-call interception, so the
/// indirect call reaches the real monomorphized `Box::<i32>::new` symbol. That
/// body must remain live and executable; classifying every collected
/// `Box::<T>::new` as dead would replace this reachable symbol with a trap.
#[test]
fn address_taken_box_new_links_runs_without_reachable_trap_aarch64() {
    if !host_is_aarch64_macos() || !aarch64_std_available() {
        eprintln!("skipping: requires an aarch64-apple-darwin host with rust-std for {TARGET}");
        return;
    }
    if !has_cc() {
        eprintln!("skipping: cc not available");
        return;
    }

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
    let output = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "staticlib"])
        .arg(&backend_arg)
        .env("TCG_NO_PROOF_CERTS", "1")
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

    let all_objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read address-taken Box::new workdir")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
        .collect();
    let nm_text = |object: &Path| {
        String::from_utf8_lossy(
            &Command::new("nm")
                .arg(object)
                .output()
                .expect("nm address-taken Box::new object")
                .stdout,
        )
        .into_owned()
    };
    let entry_obj = all_objs
        .iter()
        .find(|object| nm_text(object).contains(" T _ay_indirect_box_new"))
        .expect("no object defines ay_indirect_box_new");
    let entry_nm = nm_text(entry_obj);
    let box_new_symbol = entry_nm
        .lines()
        .filter_map(|line| {
            let mut fields = line.split_whitespace();
            (fields.next() == Some("U"))
                .then(|| fields.next())
                .flatten()
        })
        .find(|symbol| symbol.contains("5boxed") && symbol.contains("3new"))
        .expect("entry object does not reference the monomorphized Box::new symbol");
    let box_new_obj = all_objs
        .iter()
        .find(|object| nm_text(object).contains(&format!(" T {box_new_symbol}")))
        .expect("no object defines the address-taken Box::new symbol");
    let box_new_nm = nm_text(box_new_obj);
    assert!(
        box_new_nm.lines().any(|line| {
            line.split_whitespace()
                .last()
                .is_some_and(|symbol| symbol.ends_with("_rust_alloc"))
                && line.split_whitespace().next() == Some("U")
        }),
        "real Box::new body must allocate rather than be a body-less stub. nm:\n{box_new_nm}"
    );
    let box_new_disassembly = String::from_utf8_lossy(
        &Command::new("otool")
            .args(["-tvV"])
            .arg(box_new_obj)
            .output()
            .expect("otool address-taken Box::new body")
            .stdout,
    )
    .into_owned();
    // The body must not be REPLACED by a trap. Outlined guard stubs (bl ->
    // brk sequences appended after the terminal ret) are legitimate: since
    // 30ea9c0e the register-bound TrapBoundsCheckExact carriers expand to
    // real runtime checks, and without replayed elision authority those
    // checks are RETAINED — the fail-closed contract. Police the hot path
    // (everything before the first ret) for traps instead.
    let hot_path = box_new_disassembly
        .split_once("\tret")
        .map_or(box_new_disassembly.as_ref(), |(before, _)| before);
    assert!(
        !hot_path.contains("\tbrk\t"),
        "reachable Box::new body was replaced by a trap:\n{box_new_disassembly}"
    );
    let entry_disassembly = String::from_utf8_lossy(
        &Command::new("otool")
            .args(["-tvV"])
            .arg(entry_obj)
            .output()
            .expect("otool indirect caller")
            .stdout,
    )
    .into_owned();
    assert!(
        entry_disassembly.contains("\tblr\t"),
        "fixture no longer exercises an indirect call:\n{entry_disassembly}"
    );

    let shim_obj = all_objs
        .iter()
        .find(|object| nm_text(object).contains("_rdl_dealloc"))
        .expect("no allocator shim object was emitted");
    let syms = discover_rdl_symbols(shim_obj);
    let driver_path = dir.join("indirect_driver.c");
    std::fs::write(&driver_path, build_indirect_box_driver(&syms))
        .expect("write indirect Box::new driver");
    let bin = dir.join("indirect_box_new_bin");
    let link = Command::new("cc")
        .arg("-o")
        .arg(&bin)
        .arg(&driver_path)
        .arg(entry_obj)
        .arg(box_new_obj)
        .arg(shim_obj)
        .output()
        .expect("link address-taken Box::new driver");
    assert!(
        link.status.success(),
        "address-taken Box::new link failed. stderr: <<<{}>>>",
        String::from_utf8_lossy(&link.stderr)
    );

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
}
