//! Native Linux ELF twin of `drop_heap_aarch64.rs`: `Box` and `Vec` values
//! allocated, dropped and freed by code the rustc bridge compiled for
//! `aarch64-unknown-linux-gnu`, run natively with an LLVM twin of every lane
//! that has one.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates
//! License: Apache-2.0
//!
//! This target is mandatory on its named host, not a portable skip; the shared
//! harness (`support/linux_runtime_twin.rs`) fails it by name when a
//! prerequisite is missing and binds the backend the runner supplies.
//!
//! FIXTURES. The Darwin twin's `DROP_CRATE`, address-taken `Box::new` crate,
//! hooked C drivers (`build_driver`, `build_indirect_box_driver`) and
//! `ARCHIVE_DRIVER` are kept byte-identical (the script test
//! `test_runtime_twins_keep_the_darwin_crates_and_drivers` pins them).
//! A Linux crate adds what the task names: user `Drop` payloads in a `Box`
//! and a `Vec`, `Vec` growth through `realloc`, an early explicit drop and an
//! overwrite drop, each pointer passed to `black_box` so that neither compiler
//! may elide an allocation. Its driver is an LLVM-compiled Rust program whose
//! `#[global_allocator]` logs every allocation, reallocation and free, with
//! size and alignment, in order, interleaved with the payload drops.
//!
//! WHAT IS CHECKED, AT O0-O3.
//! * `hooked` (bridge only, as on Darwin): the Darwin crate's objects with the
//!   C driver that defines the allocator shim's `__rdl_*` entries and
//!   `__rust_alloc_error_handler`. Each entry's own bytes carry
//!   `R_AARCH64_CALL26` calls of `__rust_alloc`, `__rust_dealloc` and the
//!   allocation-error handler (the intercepted, null-checked `Box::new` and
//!   its drop). The run prints both values, two allocations and two frees,
//!   then drives one allocation to failure into the handler with its 8/8
//!   layout. At O0 the per-function partition (`batch-cgu=0`) must link and
//!   run the same, from more objects than the batched one, with the two
//!   entries in different objects. An LLVM object does not intercept
//!   `Box::new` (its allocation path is the library's) and LLVM removes the
//!   never-escaping boxes above O0, so this lane has no LLVM twin; the
//!   `archive` and `events` lanes do.
//! * `indirect` (bridge only, as on Darwin): `Box::new` reified as a `fn`
//!   pointer. The entry calls through `BLR`, takes the address of a function
//!   whose bytes call `__rust_alloc` and the allocation-error handler and
//!   whose path to its first `RET` holds no `BRK` except the one after that
//!   non-returning handler call; the hooked run allocates and frees once.
//! * `archive` (CG and LLVM, one and four codegen units): the Darwin crate as
//!   a staticlib archive with its bundled `std`, linked by plain `cc` with the
//!   compiler's `native-static-libs`; stdout and exit status must match.
//! * `events` (CG and LLVM): the Linux crate as an rlib, linked into the
//!   logging driver; every run's event log must equal the model exactly.
//!
//! CONTROLS. A crate with a `Vec<Box<Tracked>>` and a struct of two
//! `Box<Tracked>` fields is refused by the bridge at every level, by name
//! (`[TCG-MIR-UNSUPPORTED]`: "per-element drop glue not lowered" for the
//! vector, "recursive drop glue not lowered" for the struct's drop glue), with
//! no object defining the vector function; LLVM compiles the same valid Rust
//! and its run prints that crate's model event log. The Darwin dead-strip
//! link (`-Wl,-dead_strip` over `MH_SUBSECTIONS_VIA_SYMBOLS` atoms) has no
//! ELF equivalent here, since a bridge object keeps one `.text` section: the
//! dead library body's one non-panic diverging import,
//! `alloc::alloc::handle_alloc_error`, gets an aborting stub named here, so a
//! reached stub still fails the lane.
//!
//! EVIDENCE BOUNDARY. Native TESTING evidence without certificates: the
//! frontend runs with `-Ztrust-verify=off` and every bridge compile with the
//! `no-proof-certs` knob. The relocation and disassembly rows are unproven
//! object-side facts; GNU cc/ld, binutils, glibc, the LLVM-compiled drivers
//! and the standard library are trusted.
//!
//! The artifacts directory is removed when the test passes; setting
//! `DROP_HEAP_LINUX_KEEP_ARTIFACTS=1` retains it.

#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;
#[path = "support/linux_runtime_twin.rs"]
mod twin;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use twin::{Bridge, Ending, LaneRow, ObjectFacts};

const MARKER: &str = "TCG_BRIDGE_DROP_HEAP_EXECUTION";
const KEEP_ARTIFACTS: &str = "DROP_HEAP_LINUX_KEEP_ARTIFACTS";
/// Native executions of each linked executable.
const RUNS_PER_LANE: usize = 3;
const CODEGEN_UNITS: [u32; 2] = [1, 4];
/// The aborting stub of the dead library body's diverging import (see the
/// module doc), matched on the v0-mangled path's tail.
const DEAD_BODY_DIVERGING_IMPORT: &str = "5alloc5alloc18handle_alloc_error";

/// Byte-identical to `DROP_CRATE` in `drop_heap_aarch64.rs`.
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

/// Byte-identical to the address-taken test's `src` in `drop_heap_aarch64.rs`.
const INDIRECT_CRATE: &str = "\
#![crate_type = \"staticlib\"]\n\
#[no_mangle]\n\
pub extern \"C\" fn ay_indirect_box_new(x: i32) -> i32 {\n\
    let ctor: fn(i32) -> Box<i32> = Box::new;\n\
    let boxed = ctor(x);\n\
    *boxed\n\
}\n";

/// Byte-identical to `ARCHIVE_DRIVER` in `drop_heap_aarch64.rs`.
const ARCHIVE_DRIVER: &str = "\
#include <stdio.h>
extern long ay_box_scalar_drop(long x);
extern long ay_box_struct_drop(void);
int main(void) {
    printf(\"scalar=%ld aggregate=%ld\\n\", ay_box_scalar_drop(41), ay_box_struct_drop());
    return 0;
}
";

const HOOKED_MODEL: &str =
    "scalar=42 aggregate=42 alloc_calls=2 dealloc_calls=2\nalloc_error size=8 align=8\n";
const INDIRECT_MODEL: &str = "value=42 alloc_calls=1 dealloc_calls=1\n";
const ARCHIVE_MODEL: &str = "scalar=42 aggregate=42\n";

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

/// Shared by the Linux crates: a payload whose `Drop` reports its id to the
/// driver's event log.
const TRACKED_PRELUDE: &str = r#"use std::hint::black_box;

extern "C" {
    fn ay_record_drop(id: i32);
}

pub struct Tracked {
    pub id: i32,
}
impl Drop for Tracked {
    fn drop(&mut self) {
        unsafe { ay_record_drop(self.id) }
    }
}
"#;

/// The Linux `events` crate (after [`TRACKED_PRELUDE`]).
const EVENTS_CRATE: &str = r#"
/// A `Box<Tracked>`: the payload's `Drop` runs before the box is freed.
#[no_mangle]
pub extern "C" fn ay_box_tracked(id: i32) -> i32 {
    let b = Box::new(Tracked { id });
    black_box(&*b);
    b.id + 1
}

/// `Vec::with_capacity` then pushes within capacity: one allocation, the
/// elements drop front to back, then the buffer is freed.
#[no_mangle]
pub extern "C" fn ay_vec_tracked(n: i32) -> i32 {
    let mut v: Vec<Tracked> = Vec::with_capacity(4);
    let mut i = 0;
    while i < n {
        v.push(Tracked { id: 10 + i });
        i += 1;
    }
    black_box(&v);
    let mut s = 0;
    for t in &v {
        s += t.id;
    }
    s
}

/// Growth: pushes past the capacity reallocate.
#[no_mangle]
pub extern "C" fn ay_vec_growth(n: i32) -> i64 {
    let mut v: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        v.push(i as i64 * 3);
        black_box(&v);
        i += 1;
    }
    let mut s = 0i64;
    for x in &v {
        s += *x;
    }
    s + v.capacity() as i64 * 1000
}

/// An early explicit drop and an overwrite drop.
#[no_mangle]
pub extern "C" fn ay_drop_order(base: i32) -> i32 {
    let a = Box::new(Tracked { id: base });
    let mut b = Box::new(Tracked { id: base + 1 });
    black_box(&*a);
    black_box(&*b);
    drop(a);
    b = Box::new(Tracked { id: base + 2 });
    black_box(&*b);
    b.id
}
"#;

/// The refusal-control crate (after [`TRACKED_PRELUDE`]).
const REFUSED_CRATE: &str = r#"
/// Two boxed fields drop in declaration order, after the owner's body.
pub struct Pair {
    pub first: Box<Tracked>,
    pub second: Box<Tracked>,
}
#[no_mangle]
pub extern "C" fn ay_box_pair(base: i32) -> i32 {
    let p = Pair { first: Box::new(Tracked { id: base }), second: Box::new(Tracked { id: base + 1 }) };
    black_box(&p);
    p.first.id + p.second.id
}

/// A `Vec<Box<Tracked>>`: each element's payload drop, then its box free, in order.
#[no_mangle]
pub extern "C" fn ay_vec_of_boxes(n: i32) -> i32 {
    let mut v: Vec<Box<Tracked>> = Vec::with_capacity(3);
    let mut i = 0;
    while i < n {
        let b = Box::new(Tracked { id: 20 + i });
        black_box(&*b);
        v.push(b);
        i += 1;
    }
    black_box(&v);
    v.len() as i32
}
"#;

/// The logging driver, before its `main`: a `#[global_allocator]` that
/// records, without allocating, each allocation (`alloc#id(size,align)`),
/// reallocation (`realloc#id(old->new)`) and free (`free#id(size,align)`)
/// with per-call allocation ids, and `ay_record_drop` for the payloads.
const EVENTS_DRIVER: &str = r#"extern crate dropheap;
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

const CAP: usize = 256;
static KINDS: [AtomicUsize; CAP] = [const { AtomicUsize::new(0) }; CAP];
static A: [AtomicUsize; CAP] = [const { AtomicUsize::new(0) }; CAP];
static B: [AtomicUsize; CAP] = [const { AtomicUsize::new(0) }; CAP];
static C: [AtomicUsize; CAP] = [const { AtomicUsize::new(0) }; CAP];
static LEN: AtomicUsize = AtomicUsize::new(0);
static ON: AtomicBool = AtomicBool::new(false);
static ADDR: [AtomicUsize; CAP] = [const { AtomicUsize::new(0) }; CAP];
static NEXT_ID: AtomicUsize = AtomicUsize::new(0);

fn push(kind: usize, a: usize, b: usize, c: usize) {
    let at = LEN.fetch_add(1, Ordering::SeqCst);
    assert!(at < CAP, "event log overflow");
    KINDS[at].store(kind, Ordering::SeqCst);
    A[at].store(a, Ordering::SeqCst);
    B[at].store(b, Ordering::SeqCst);
    C[at].store(c, Ordering::SeqCst);
}
fn id_of(ptr: *mut u8) -> usize {
    let id = ADDR.iter().position(|slot| slot.load(Ordering::SeqCst) == ptr as usize);
    id.expect("free or realloc of an allocation the log never saw")
}
struct Logging;
unsafe impl GlobalAlloc for Logging {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let p = unsafe { System.alloc(layout) };
        if ON.load(Ordering::SeqCst) {
            let id = NEXT_ID.fetch_add(1, Ordering::SeqCst);
            ADDR[id].store(p as usize, Ordering::SeqCst);
            push(1, id, layout.size(), layout.align());
        }
        p
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if ON.load(Ordering::SeqCst) {
            let id = id_of(ptr);
            ADDR[id].store(0, Ordering::SeqCst);
            push(2, id, layout.size(), layout.align());
        }
        unsafe { System.dealloc(ptr, layout) }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let id = if ON.load(Ordering::SeqCst) { Some(id_of(ptr)) } else { None };
        let p = unsafe { System.realloc(ptr, layout, new_size) };
        if let Some(id) = id {
            ADDR[id].store(p as usize, Ordering::SeqCst);
            push(3, id, layout.size(), new_size);
        }
        p
    }
}
#[global_allocator]
static GLOBAL: Logging = Logging;

#[no_mangle]
pub extern "C" fn ay_record_drop(id: i32) {
    push(4, id as u32 as usize, 0, 0);
}

fn report(label: &str, call: &dyn Fn() -> i64) {
    LEN.store(0, Ordering::SeqCst);
    NEXT_ID.store(0, Ordering::SeqCst);
    for slot in &ADDR {
        slot.store(0, Ordering::SeqCst);
    }
    ON.store(true, Ordering::SeqCst);
    let value = call();
    ON.store(false, Ordering::SeqCst);
    let mut text = String::new();
    for at in 0..LEN.load(Ordering::SeqCst) {
        let (a, b, c) = (A[at].load(Ordering::SeqCst), B[at].load(Ordering::SeqCst), C[at].load(Ordering::SeqCst));
        let event = match KINDS[at].load(Ordering::SeqCst) {
            1 => format!("alloc#{a}({b},{c})"),
            2 => format!("free#{a}({b},{c})"),
            3 => format!("realloc#{a}({b}->{c})"),
            4 => format!("drop:{}", a as u32 as i32),
            _ => unreachable!(),
        };
        if !text.is_empty() {
            text.push(' ');
        }
        text.push_str(&event);
    }
    let live = ADDR.iter().filter(|slot| slot.load(Ordering::SeqCst) != 0).count();
    println!("{label} = {value} [{text}] live={live}");
}
"#;

const EVENTS_MAIN: &str = r#"
fn main() {
    report("box_tracked(5)", &|| dropheap::ay_box_tracked(5) as i64);
    report("vec_tracked(3)", &|| dropheap::ay_vec_tracked(3) as i64);
    report("vec_growth(9)", &|| dropheap::ay_vec_growth(9));
    report("drop_order(40)", &|| dropheap::ay_drop_order(40) as i64);
}
"#;

const REFUSED_MAIN: &str = r#"
fn main() {
    report("box_pair(7)", &|| dropheap::ay_box_pair(7) as i64);
    report("vec_of_boxes(3)", &|| dropheap::ay_vec_of_boxes(3) as i64);
}
"#;

/// Each payload drop precedes its box's free; a `Vec` drops its elements
/// front to back before freeing its buffer; growth reallocates 4 -> 8 -> 16
/// elements; `b = Box::new(..)` allocates the new box before dropping the old.
const EVENTS_MODEL: &str = "\
box_tracked(5) = 6 [alloc#0(4,4) drop:5 free#0(4,4)] live=0
vec_tracked(3) = 33 [alloc#0(16,4) drop:10 drop:11 drop:12 free#0(16,4)] live=0
vec_growth(9) = 16108 [alloc#0(32,8) realloc#0(32->64) realloc#0(64->128) free#0(128,8)] live=0
drop_order(40) = 42 [alloc#0(4,4) alloc#1(4,4) drop:40 free#0(4,4) alloc#2(4,4) drop:41 free#1(4,4) drop:42 free#2(4,4)] live=0
";

const REFUSED_MODEL: &str = "\
box_pair(7) = 15 [alloc#0(4,4) alloc#1(4,4) drop:7 free#0(4,4) drop:8 free#1(4,4)] live=0
vec_of_boxes(3) = 3 [alloc#0(24,8) alloc#1(4,4) alloc#2(4,4) alloc#3(4,4) drop:20 free#1(4,4) drop:21 free#2(4,4) drop:22 free#3(4,4) free#0(24,8)] live=0
";

/// (row prefix, fragments, row suffix) of each refusal the bridge must print
/// for [`REFUSED_CRATE`], exactly once. The drop-glue row is matched on its
/// symbol's `drop_glue` and `dropheap` `Pair` components, not on the
/// crate hash or mangling back-references.
const REFUSALS: [(&str, &[&str], &str); 2] = [
    (
        "- ay_vec_of_boxes: ",
        &[],
        "TerminatorKind::Drop of Vec<std::boxed::Box<Tracked, std::alloc::Global>> whose \
         element needs drop (per-element drop glue not lowered)",
    ),
    (
        "- _R",
        &["9drop_glue", "8dropheap4Pair"],
        " (reachable Rust-internal monomorphization, not a std-internal shim): \
         TerminatorKind::Drop of Box<Tracked> whose payload needs drop (recursive drop glue \
         not lowered)",
    ),
];

/// Every `*.rcgu.o` object of a compile that ran with `-Csave-temps`: the
/// codegen-unit (or, with `batch-cgu=0`, per-function) objects and the
/// allocator shim, not rustc's combined `<crate>.o`.
fn rcgu_objects(dir: &Path) -> Vec<ObjectFacts> {
    twin::inspect_objects(dir)
        .into_iter()
        .filter(|facts| facts.file_name().ends_with(".rcgu.o"))
        .collect()
}

/// Compile a staticlib crate through the bridge to its retained objects.
fn compile_objects(
    lane: &Path,
    name: &str,
    source: &str,
    opt: u32,
    bridge: Option<Bridge<'_>>,
) -> (std::process::Output, String, PathBuf) {
    let path = lane.join(format!("{name}.rs"));
    std::fs::write(&path, source).unwrap();
    let object_dir = lane.join(format!("{name}-objects"));
    std::fs::create_dir(&object_dir).unwrap();
    let mut command = twin::rustc_command();
    command.args(["--crate-type", "staticlib"]);
    twin::select_backend(&mut command, bridge);
    command
        .args(["-Ccodegen-units=1", "-Cpanic=abort", "-Csave-temps"])
        .args(["--target", twin::TARGET])
        .arg(format!("-Copt-level={opt}"))
        .arg("--emit=obj")
        .arg("--out-dir")
        .arg(&object_dir)
        .arg(&path);
    let (output, transcript) =
        twin::run_bounded(&mut command, 180, &lane.join(format!("{name}-compile.log")));
    (output, transcript, object_dir)
}

/// The allocator shim's forwarding targets and the handler a bridge object calls.
fn discover_rdl_symbols(objects: &[ObjectFacts]) -> RdlSymbols {
    let shims: Vec<&ObjectFacts> = objects.iter().filter(|o| o.is_allocator_shim()).collect();
    assert_eq!(shims.len(), 1, "exactly one allocator shim object");
    let find = |suffix: &str| -> String {
        let names: Vec<&str> = shims[0]
            .symbols
            .iter()
            .filter(|symbol| symbol.section == "UND" && symbol.name.ends_with(suffix))
            .map(|symbol| symbol.name.as_str())
            .collect();
        assert_eq!(
            names.len(),
            1,
            "the shim must import exactly one `*{suffix}`"
        );
        names[0].to_owned()
    };
    let handler = objects
        .iter()
        .flat_map(|facts| facts.symbols.iter())
        .find(|symbol| {
            symbol.section == "UND" && symbol.name.ends_with("_rust_alloc_error_handler")
        })
        .map(|symbol| symbol.name.clone());
    RdlSymbols {
        alloc: find("_rdl_alloc"),
        dealloc: find("_rdl_dealloc"),
        realloc: find("_rdl_realloc"),
        alloc_zeroed: find("_rdl_alloc_zeroed"),
        alloc_error_handler: handler,
    }
}

/// Link `objects` with a C `driver` and the aborting stubs (the core panic
/// entries and [`DEAD_BODY_DIVERGING_IMPORT`]).
fn link_hooked(dir: &Path, name: &str, driver: &str, objects: &[ObjectFacts]) -> (PathBuf, usize) {
    let linked: Vec<&ObjectFacts> = objects.iter().collect();
    let source = dir.join(format!("{name}.c"));
    std::fs::write(&source, driver).unwrap();
    let defined: std::collections::BTreeSet<&str> = linked
        .iter()
        .flat_map(|facts| facts.symbols.iter())
        .filter(|symbol| symbol.section != "UND")
        .map(|symbol| symbol.name.as_str())
        .collect();
    let dead: Vec<&str> = linked
        .iter()
        .flat_map(|facts| facts.symbols.iter())
        .filter(|symbol| {
            symbol.section == "UND"
                && symbol.name.ends_with(DEAD_BODY_DIVERGING_IMPORT)
                && !defined.contains(symbol.name.as_str())
        })
        .map(|symbol| symbol.name.as_str())
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect();
    let executable = dir.join(format!("{name}.elf"));
    let mut command = Command::new("cc");
    command.arg("-o").arg(&executable).arg(&source);
    let (stubs, mut count) = twin::abort_stubs(dir, &linked);
    if let Some(stubs) = stubs {
        command.arg(stubs);
    }
    if !dead.is_empty() {
        let mut text = String::from("#include <stdlib.h>\n");
        for (index, symbol) in dead.iter().enumerate() {
            text.push_str(&format!(
                "void tcg_dead_body_stub_{index}(void) __asm__(\"{symbol}\");\n\
                 void tcg_dead_body_stub_{index}(void) {{ abort(); }}\n"
            ));
        }
        let path = dir.join("dead_body_stubs.c");
        std::fs::write(&path, text).unwrap();
        command.arg(path);
        count += dead.len();
    }
    for facts in &linked {
        command.arg(&facts.path);
    }
    twin::checked(&mut command, 60, &dir.join(format!("{name}-link.log")));
    (executable, count)
}

/// The `R_AARCH64_CALL26` targets inside `function`'s bytes.
fn calls_in<'a>(facts: &'a ObjectFacts, function: &str) -> Vec<(u64, &'a str)> {
    let symbol = facts
        .defined(function)
        .unwrap_or_else(|| panic!("{} does not define {function}", facts.file_name()));
    facts
        .relocations_in(symbol)
        .into_iter()
        .filter(|row| row.kind == "R_AARCH64_CALL26")
        .map(|row| (row.offset, facts.symbol(row.symbol_index).name.as_str()))
        .collect()
}

/// The hooked Darwin crate at one level and partition: returns the lane row,
/// the number of objects and whether one object defines both entries.
fn hooked_lane(
    artifacts: &Path,
    label: &str,
    opt: u32,
    bridge: Bridge<'_>,
) -> (LaneRow, usize, bool) {
    let lane = artifacts.join(format!("hooked_{label}_O{opt}"));
    std::fs::create_dir(&lane).unwrap();
    let (output, transcript, dir) =
        compile_objects(&lane, "dropheap", DROP_CRATE, opt, Some(bridge));
    assert!(
        output.status.success(),
        "hooked {label} O{opt} compile failed: {transcript}"
    );
    let objects = rcgu_objects(&dir);
    let refs: Vec<&ObjectFacts> = objects.iter().collect();
    for entry in ["ay_box_scalar_drop", "ay_box_struct_drop"] {
        let calls = calls_in(twin::definer(&refs, entry), entry);
        for callee in ["_rust_alloc", "_rust_dealloc", "_rust_alloc_error_handler"] {
            assert!(
                calls.iter().any(|(_, target)| target.ends_with(callee)),
                "hooked {label} O{opt}: `{entry}` must call `{callee}` itself: {calls:?}"
            );
        }
    }
    let syms = discover_rdl_symbols(&objects);
    assert!(
        syms.alloc_error_handler.is_some(),
        "no bridge object calls `__rust_alloc_error_handler`"
    );
    let (executable, _) = link_hooked(&lane, "hooked", &build_driver(&syms), &objects);
    let row = twin::model_runs(
        &lane,
        &executable,
        if label == "batched" {
            "hooked"
        } else {
            "hooked_per_function"
        },
        "cg",
        opt,
        RUNS_PER_LANE,
        Ending::Exit(0),
        HOOKED_MODEL,
    );
    let shared = twin::definer(&refs, "ay_box_scalar_drop").path
        == twin::definer(&refs, "ay_box_struct_drop").path;
    (row, objects.len(), shared)
}

/// The instruction words of `function` in `facts`, as (offset, mnemonic).
fn disassembly(lane: &Path, facts: &ObjectFacts, function: &str) -> Vec<(u64, String)> {
    let symbol = facts.defined(function).unwrap();
    let output = twin::checked(
        Command::new("objdump")
            .args(["-d", "--no-show-raw-insn"])
            .arg(&facts.path),
        30,
        &lane.join(format!("{}.disassembly.txt", facts.file_name())),
    );
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| {
            let (address, rest) = line.split_once(':')?;
            let address = u64::from_str_radix(address.trim(), 16).ok()?;
            let mnemonic = rest.split_whitespace().next()?.to_owned();
            (symbol.value <= address && address < symbol.value + symbol.size)
                .then_some((address, mnemonic))
        })
        .collect()
}

/// The address-taken `Box::new` crate at one level (bridge only).
fn indirect_lane(artifacts: &Path, opt: u32, bridge: Bridge<'_>) -> LaneRow {
    let lane = artifacts.join(format!("indirect_O{opt}"));
    std::fs::create_dir(&lane).unwrap();
    let (output, transcript, dir) =
        compile_objects(&lane, "indirect", INDIRECT_CRATE, opt, Some(bridge));
    assert!(
        output.status.success(),
        "indirect O{opt} compile failed: {transcript}"
    );
    let objects = rcgu_objects(&dir);
    let refs: Vec<&ObjectFacts> = objects.iter().collect();
    const ENTRY: &str = "ay_indirect_box_new";
    let entry_object = twin::definer(&refs, ENTRY);
    let entry = entry_object.defined(ENTRY).unwrap();
    // The entry takes the constructor's address (ADRP + ADD) and calls it
    // through a register.
    let targets: Vec<&str> = entry_object
        .relocations_in(entry)
        .into_iter()
        .filter(|row| row.kind == "R_AARCH64_ADR_PREL_PG_HI21")
        .map(|row| entry_object.symbol(row.symbol_index))
        .filter(|symbol| symbol.kind == "FUNC" || symbol.section == "UND")
        .map(|symbol| symbol.name.as_str())
        .collect();
    assert_eq!(
        targets.len(),
        1,
        "indirect O{opt}: the entry must take exactly one function's address: {targets:?}"
    );
    assert!(
        disassembly(&lane, entry_object, ENTRY)
            .iter()
            .any(|(_, mnemonic)| mnemonic == "blr"),
        "indirect O{opt}: the entry no longer calls through a function pointer"
    );
    let constructor = targets[0];
    let constructor_object = twin::definer(&refs, constructor);
    let calls = calls_in(constructor_object, constructor);
    let handler_calls: Vec<u64> = calls
        .iter()
        .filter(|(_, target)| target.ends_with("_rust_alloc_error_handler"))
        .map(|(offset, _)| *offset)
        .collect();
    assert!(
        calls
            .iter()
            .any(|(_, target)| target.ends_with("_rust_alloc"))
            && !handler_calls.is_empty(),
        "indirect O{opt}: the reified Box::new body must allocate and check: {calls:?}"
    );
    // The body must not be replaced by a trap: on its path to the first `ret`,
    // a `brk` may only follow the non-returning allocation-error call.
    let words = disassembly(&lane, constructor_object, constructor);
    let hot = words
        .iter()
        .position(|(_, mnemonic)| mnemonic == "ret")
        .map_or(&words[..], |end| &words[..end]);
    assert!(!hot.is_empty(), "indirect O{opt}: empty constructor body");
    for (index, (_, mnemonic)) in hot.iter().enumerate() {
        if mnemonic == "brk" {
            let after_handler =
                index > 0 && hot[index - 1].1 == "bl" && handler_calls.contains(&hot[index - 1].0);
            assert!(
                after_handler,
                "indirect O{opt}: reachable trap in Box::new: {words:?}"
            );
        }
    }
    let syms = discover_rdl_symbols(&objects);
    let (executable, _) = link_hooked(
        &lane,
        "indirect",
        &build_indirect_box_driver(&syms),
        &objects,
    );
    twin::model_runs(
        &lane,
        &executable,
        "indirect",
        "cg",
        opt,
        RUNS_PER_LANE,
        Ending::Exit(0),
        INDIRECT_MODEL,
    )
}

/// The `native-static-libs` a staticlib compile printed.
fn native_static_libs(stderr: &str) -> Vec<String> {
    let line = stderr
        .lines()
        .find_map(|line| {
            line.split_once("native-static-libs: ")
                .map(|(_, libs)| libs)
        })
        .expect("the staticlib compile must print its native-static-libs");
    line.split_whitespace().map(str::to_owned).collect()
}

/// The Darwin crate as a staticlib archive, linked by plain `cc`.
fn archive_lane(artifacts: &Path, opt: u32, units: u32, bridge: Option<Bridge<'_>>) -> LaneRow {
    let compiler = twin::compiler_name(bridge);
    let lane = artifacts.join(format!("archive_{compiler}_O{opt}_c{units}"));
    std::fs::create_dir(&lane).unwrap();
    let source = lane.join("dropheap.rs");
    std::fs::write(&source, DROP_CRATE).unwrap();
    let mut command = twin::rustc_command();
    command.args(["--crate-type", "staticlib", "--crate-name", "dropheap"]);
    twin::select_backend(&mut command, bridge);
    command
        .args(["-Cpanic=abort", "--target", twin::TARGET])
        .arg(format!("-Copt-level={opt}"))
        .arg(format!("-Ccodegen-units={units}"))
        .args(["--print", "native-static-libs"])
        .arg("--out-dir")
        .arg(&lane)
        .arg(&source);
    let output = twin::checked(&mut command, 180, &lane.join("compile.log"));
    let libs = native_static_libs(&String::from_utf8_lossy(&output.stderr));
    let driver = lane.join("driver.c");
    std::fs::write(&driver, ARCHIVE_DRIVER).unwrap();
    let executable = lane.join("prog.elf");
    twin::checked(
        Command::new("cc")
            .arg("-o")
            .arg(&executable)
            .arg(&driver)
            .arg(lane.join("libdropheap.a"))
            .args(&libs),
        60,
        &lane.join("link.log"),
    );
    twin::model_runs(
        &lane,
        &executable,
        if units == 1 {
            "archive_c1"
        } else {
            "archive_c4"
        },
        compiler,
        opt,
        RUNS_PER_LANE,
        Ending::Exit(0),
        ARCHIVE_MODEL,
    )
}

/// Compile a Linux crate as the `dropheap` rlib and link it into the logging
/// driver with `main`; returns the executable.
fn events_executable(
    lane: &Path,
    crate_source: &str,
    main: &str,
    opt: u32,
    bridge: Option<Bridge<'_>>,
) -> PathBuf {
    let source = lane.join("dropheap.rs");
    std::fs::write(&source, format!("{TRACKED_PRELUDE}{crate_source}")).unwrap();
    let mut command = twin::rustc_command();
    command.args(["--crate-type", "rlib", "--crate-name", "dropheap"]);
    twin::select_backend(&mut command, bridge);
    command
        .args([
            "-Ccodegen-units=1",
            "-Cpanic=abort",
            "--target",
            twin::TARGET,
        ])
        .arg(format!("-Copt-level={opt}"))
        .arg("--out-dir")
        .arg(lane)
        .arg(&source);
    twin::checked(&mut command, 180, &lane.join("compile.log"));
    let driver = lane.join("driver.rs");
    std::fs::write(&driver, format!("{EVENTS_DRIVER}{main}")).unwrap();
    let executable = lane.join("events.elf");
    let mut command = twin::rustc_command();
    command
        .args([
            "--crate-type",
            "bin",
            "-Cpanic=abort",
            "--target",
            twin::TARGET,
        ])
        .arg(format!("-Copt-level={opt}"))
        .arg("--extern")
        .arg(format!(
            "dropheap={}",
            lane.join("libdropheap.rlib").display()
        ))
        .arg("-o")
        .arg(&executable)
        .arg(&driver);
    twin::checked(&mut command, 180, &lane.join("driver-compile.log"));
    executable
}

fn events_lane(artifacts: &Path, opt: u32, bridge: Option<Bridge<'_>>) -> LaneRow {
    let compiler = twin::compiler_name(bridge);
    let lane = artifacts.join(format!("events_{compiler}_O{opt}"));
    std::fs::create_dir(&lane).unwrap();
    let executable = events_executable(&lane, EVENTS_CRATE, EVENTS_MAIN, opt, bridge);
    twin::model_runs(
        &lane,
        &executable,
        "events",
        compiler,
        opt,
        RUNS_PER_LANE,
        Ending::Exit(0),
        EVENTS_MODEL,
    )
}

/// The refusal control at one level: the exact named bridge refusal with no
/// object defining the vector function, and the LLVM twin's model run.
fn refusal_control(artifacts: &Path, opt: u32, bridge: Bridge<'_>) -> (serde_json::Value, LaneRow) {
    let lane = artifacts.join(format!("refused_O{opt}"));
    std::fs::create_dir(&lane).unwrap();
    let source = format!("{TRACKED_PRELUDE}{REFUSED_CRATE}");
    let (output, transcript, dir) = compile_objects(&lane, "dropheap", &source, opt, Some(bridge));
    assert_eq!(
        output.status.code(),
        Some(1),
        "refused O{opt}: expected a compiler refusal, not success, timeout or crash: {transcript}"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("[TCG-MIR-UNSUPPORTED]"),
        "wrong refusal boundary: {transcript}"
    );
    let rows: Vec<&str> = stderr.lines().map(str::trim).collect();
    for (prefix, fragments, suffix) in REFUSALS {
        assert_eq!(
            rows.iter()
                .filter(|row| {
                    row.starts_with(prefix)
                        && fragments.iter().all(|fragment| row.contains(fragment))
                        && row.ends_with(suffix)
                })
                .count(),
            1,
            "refused O{opt}: the refusal `{prefix}..{suffix}` must appear exactly once: {transcript}"
        );
    }
    let leftover = twin::inspect_objects(&dir);
    let definitions = leftover
        .iter()
        .filter(|facts| facts.defined("ay_vec_of_boxes").is_some())
        .count();
    assert_eq!(
        definitions, 0,
        "refused O{opt}: an object defines ay_vec_of_boxes"
    );
    let llvm_lane = artifacts.join(format!("refused_llvm_O{opt}"));
    std::fs::create_dir(&llvm_lane).unwrap();
    let executable = events_executable(&llvm_lane, REFUSED_CRATE, REFUSED_MAIN, opt, None);
    let row = twin::model_runs(
        &llvm_lane,
        &executable,
        "refused",
        "llvm",
        opt,
        RUNS_PER_LANE,
        Ending::Exit(0),
        REFUSED_MODEL,
    );
    let control = serde_json::json!({
        "name": "refused_drop_glue",
        "opt_level": opt,
        "cg_refusals": 1,
        "refusal_rows": REFUSALS.len(),
        "cg_definitions": definitions,
        "llvm_runs": RUNS_PER_LANE,
    });
    (control, row)
}

#[test]
fn heap_drops_match_llvm_and_the_model_linux() {
    twin::require_knobs("drop_heap_linux");
    let artifacts = twin::Artifacts::new("trust-cg-drop-heap-linux", KEEP_ARTIFACTS);
    let root = artifacts.root.clone();
    twin::require_host(&root);
    let (backend, digest) = twin::backend();
    let bridge = Bridge {
        path: &backend,
        knobs: twin::NO_PROOF_CERTS,
    };
    let mut lanes = Vec::new();
    let mut controls = Vec::new();
    let mut partitions = Vec::new();
    for opt in twin::OPT_LEVELS {
        let (row, batched_objects, batched_shared) = hooked_lane(&root, "batched", opt, bridge);
        lanes.push(row);
        assert!(
            batched_shared,
            "O{opt}: the batched partition puts both entries in one object"
        );
        if opt == 0 {
            let per_function = Bridge {
                path: &backend,
                knobs: &["no-proof-certs", "batch-cgu=0"],
            };
            let (row, objects, shared) = hooked_lane(&root, "per_function", opt, per_function);
            lanes.push(row);
            // Two partitions really: a batched compile that fell back to
            // per-function objects would leave the batched link untested.
            assert!(
                !shared && batched_objects < objects,
                "the batched ({batched_objects} objects) and per-function ({objects} objects, \
                 shared entry object {shared}) compiles are not two partitions"
            );
            partitions.push(serde_json::json!({
                "opt_level": opt, "batched_objects": batched_objects,
                "per_function_objects": objects, "per_function_shared_entry_object": shared,
            }));
        }
        lanes.push(indirect_lane(&root, opt, bridge));
        for units in CODEGEN_UNITS {
            lanes.push(archive_lane(&root, opt, units, Some(bridge)));
            lanes.push(archive_lane(&root, opt, units, None));
        }
        lanes.push(events_lane(&root, opt, Some(bridge)));
        lanes.push(events_lane(&root, opt, None));
        let (control, row) = refusal_control(&root, opt, bridge);
        controls.push(control);
        lanes.push(row);
        assert_eq!(
            twin::sha256(&backend),
            digest,
            "backend changed during O{opt}"
        );
    }
    twin::assert_twins_agree(&lanes, &["archive_c1", "archive_c4", "events"]);
    let models: BTreeMap<&str, String> = [
        ("hooked", HOOKED_MODEL),
        ("hooked_per_function", HOOKED_MODEL),
        ("indirect", INDIRECT_MODEL),
        ("archive_c1", ARCHIVE_MODEL),
        ("archive_c4", ARCHIVE_MODEL),
        ("events", EVENTS_MODEL),
        ("refused", REFUSED_MODEL),
    ]
    .into_iter()
    .map(|(name, model)| {
        (
            name,
            twin::sha256_of(model.as_bytes(), &root.join("model.txt")),
        )
    })
    .collect();
    twin::print_marker(
        MARKER,
        serde_json::json!({
            "runs_per_lane": RUNS_PER_LANE,
            "lanes": lanes.iter().map(LaneRow::json).collect::<Vec<_>>(),
            "partitions": partitions,
            "refusal_controls": controls,
            "model_sha256": models,
        }),
        &digest,
    );
    artifacts.finish();
}

#[test]
fn event_models_account_for_every_allocation() {
    // Every allocation id the model names is freed exactly once, after its
    // payload's drop, and nothing stays live.
    for model in [EVENTS_MODEL, REFUSED_MODEL] {
        for line in model.lines() {
            assert!(line.ends_with(" live=0"), "{line}");
            let events = line.split_once('[').unwrap().1.split_once(']').unwrap().0;
            let mut allocated = Vec::new();
            let mut freed = Vec::new();
            for event in events.split_whitespace() {
                if let Some(rest) = event.strip_prefix("alloc#") {
                    allocated.push(rest.split('(').next().unwrap().to_owned());
                } else if let Some(rest) = event.strip_prefix("free#") {
                    freed.push(rest.split('(').next().unwrap().to_owned());
                }
            }
            allocated.sort();
            freed.sort();
            assert_eq!(allocated, freed, "{line}");
        }
    }
    assert_eq!(REFUSALS.len(), 2);
    assert!(
        DROP_CRATE.contains("ay_box_scalar_drop") && ARCHIVE_DRIVER.contains("ay_box_struct_drop")
    );
}
