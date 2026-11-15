// Copyright 2026 Andrew Yates | Apache-2.0
//! Shared TrustIR corpus and C driver for the AArch64 heap allocation native
//! controls (`e2e_aarch64_heap_dealloc.rs` on Darwin,
//! `e2e_aarch64_heap_dealloc_linux.rs` on Linux).
//!
//! Every function allocates through `Inst::HeapAlloc`, uses the memory and
//! releases it through a CALL to a declared deallocation entry point —
//! `__rust_dealloc(ptr, size, align)` for a `RustHeap` block, `free(ptr)` for
//! a `CMalloc` one — the way producers spell a release (a Rust `Box` drop is a
//! `__rust_dealloc` call; Clean releases a cell with `Release`). `Inst::Dealloc`
//! is refused for codegen in every body (G18-1, re-decided 2026-09-27; trust-ir
//! `docs/SPEC_RATIFICATIONS.md` "Deallocation is refused for codegen, whatever
//! its provenance"), so no function here uses it; the lowering that recovered
//! a release from `HeapAlloc` provenance (2887cbf01) is retired.
//!
//! What pairing a `HeapAlloc` with a hand-sized `__rust_dealloc` pins, stated
//! exactly: THIS BACKEND's own allocation layout for these element types
//! (`u64`, `u32`, `[u64; 3]` at align 64) — trust-cg sizes a `HeapAlloc` by
//! its natural-C LIR type times the count — agreeing with the layout the
//! release names. That is a backend self-consistency check, not a format
//! guarantee: trust-ir states no layout a lowered `HeapAlloc` passes its
//! allocator, and producers spell the allocation as a call too.
//!
//! The driver interposes `__rust_alloc`,
//! `__rust_dealloc`, `malloc` and `free`, records every live allocation with
//! its size, alignment and allocator, and checks that each release names the
//! right allocator with the exact allocation layout and that every call leaves
//! nothing live. Every accepted release poisons the block before handing it
//! back, so a use after the release is observable on either host. The leak
//! and double-free functions are negative controls: the driver must observe
//! the leaked block and the second release, which shows the balance checks
//! can fail. Execution evidence, not proof.
#![allow(dead_code)]

use trust_ir::inst::AllocOrigin;
use trust_ir::{BinOp, CastOp, Endianness, ICmpOp, Module, StructPassingPolicy, TargetInfo, Ty};
use trust_ir_build::{ModuleBuilder, validate_module};

/// Exact driver output for a complete, successful run.
pub const EXPECTED_PASS: &str = "PASS 138 heap checks";

/// `(symbol, direct call sites)` the corpus lowers to at every opt level.
pub const CALL_SITES: &[(&str, usize)] = &[
    ("__rust_alloc", 9),
    ("__rust_dealloc", 8),
    ("malloc", 1),
    ("free", 1),
];

fn target(triple: &str) -> TargetInfo {
    TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

/// The positive corpus and its two negative controls, for `triple`.
pub fn corpus(triple: &str) -> Module {
    let mut m = ModuleBuilder::new_with_target_info("heap_dealloc", target(triple));
    let unary = m.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let binary = m.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let rust_dealloc_ty = m.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::U64], vec![]);
    let free_ty = m.add_func_type(vec![Ty::Ptr], vec![]);
    let rust_dealloc = m.declare_function("__rust_dealloc", rust_dealloc_ty);
    let free = m.declare_function("free", free_ty);

    // cg_rust_box(x) = x + 1 through one __rust_alloc(8, 8) cell.
    {
        let mut f = m.function("cg_rust_box", unary);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let cell = f.heap_alloc(Ty::U64, None, None, AllocOrigin::RustHeap);
        f.store(Ty::U64, cell, x);
        let loaded = f.load(Ty::U64, cell);
        let size = f.iconst(Ty::U64, 8);
        let align = f.iconst(Ty::U64, 8);
        f.call_void(rust_dealloc, vec![cell, size, align]);
        let one = f.iconst(Ty::U64, 1);
        let result = f.binop(BinOp::Add, Ty::U64, loaded, one);
        f.ret(vec![result]);
        f.build();
    }

    // cg_rust_array(n) = sum(3 * i for i < n) over a runtime-sized [u32; n],
    // freed in a later block with the size the allocation was made with.
    {
        let mut f = m.function("cg_rust_array", unary);
        let entry = f.create_block();
        let fill = f.create_block();
        let fill_body = f.create_block();
        let sum = f.create_block();
        let sum_body = f.create_block();
        let done = f.create_block();
        let n = f.add_block_param(entry, Ty::U64);
        let i = f.add_block_param(fill, Ty::U64);
        let j = f.add_block_param(sum, Ty::U64);
        let acc = f.add_block_param(sum, Ty::U64);

        f.switch_to_block(entry);
        let array = f.heap_alloc(Ty::U32, Some(n), None, AllocOrigin::RustHeap);
        let zero = f.iconst(Ty::U64, 0);
        f.br(fill, vec![zero]);

        f.switch_to_block(fill);
        let more = f.icmp(ICmpOp::Ult, Ty::U64, i, n);
        f.condbr(more, fill_body, vec![], sum, vec![zero, zero]);

        f.switch_to_block(fill_body);
        let slot = f.gep(Ty::U32, array, vec![i]);
        let three = f.iconst(Ty::U64, 3);
        let wide = f.binop(BinOp::Mul, Ty::U64, i, three);
        let narrow = f.cast(CastOp::Trunc, Ty::U64, Ty::U32, wide);
        f.store(Ty::U32, slot, narrow);
        let one = f.iconst(Ty::U64, 1);
        let next = f.binop(BinOp::Add, Ty::U64, i, one);
        f.br(fill, vec![next]);

        f.switch_to_block(sum);
        let more = f.icmp(ICmpOp::Ult, Ty::U64, j, n);
        f.condbr(more, sum_body, vec![], done, vec![]);

        f.switch_to_block(sum_body);
        let slot = f.gep(Ty::U32, array, vec![j]);
        let element = f.load(Ty::U32, slot);
        let element = f.cast(CastOp::ZExt, Ty::U32, Ty::U64, element);
        let total = f.binop(BinOp::Add, Ty::U64, acc, element);
        let one = f.iconst(Ty::U64, 1);
        let next = f.binop(BinOp::Add, Ty::U64, j, one);
        f.br(sum, vec![next, total]);

        f.switch_to_block(done);
        let four = f.iconst(Ty::U64, 4);
        let size = f.binop(BinOp::Mul, Ty::U64, n, four);
        let align = f.iconst(Ty::U64, 4);
        f.call_void(rust_dealloc, vec![array, size, align]);
        f.ret(vec![acc]);
        f.build();
    }

    // cg_rust_overaligned(x) = x via element 2 of a 64-byte-aligned [u64; 3],
    // released through a Copy of its base.
    {
        let mut f = m.function("cg_rust_overaligned", unary);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let three = f.iconst(Ty::U64, 3);
        let base = f.heap_alloc(Ty::U64, Some(three), Some(64), AllocOrigin::RustHeap);
        let copied = f.copy(Ty::Ptr, base);
        let two = f.iconst(Ty::U64, 2);
        let slot = f.gep(Ty::U64, base, vec![two]);
        f.store(Ty::U64, slot, x);
        let loaded = f.load(Ty::U64, slot);
        let size = f.iconst(Ty::U64, 24);
        let align = f.iconst(Ty::U64, 64);
        f.call_void(rust_dealloc, vec![copied, size, align]);
        f.ret(vec![loaded]);
        f.build();
    }

    // cg_c_malloc(x) = x + (x+1) + (x+2) + (x+3) through malloc(32)/free.
    {
        let mut f = m.function("cg_c_malloc", unary);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let four = f.iconst(Ty::U64, 4);
        let block = f.heap_alloc(Ty::I64, Some(four), None, AllocOrigin::CMalloc);
        let mut total = f.iconst(Ty::U64, 0);
        for index in 0..4 {
            let offset = f.iconst(Ty::U64, index);
            let slot = f.gep(Ty::I64, block, vec![offset]);
            let value = f.binop(BinOp::Add, Ty::U64, x, offset);
            f.store(Ty::U64, slot, value);
        }
        for index in 0..4 {
            let offset = f.iconst(Ty::U64, index);
            let slot = f.gep(Ty::I64, block, vec![offset]);
            let value = f.load(Ty::U64, slot);
            total = f.binop(BinOp::Add, Ty::U64, total, value);
        }
        f.call_void(free, vec![block]);
        f.ret(vec![total]);
        f.build();
    }

    // cg_select_free(c, x) = c ? x : 2x; both cells are released through a
    // Select of two same-layout allocations.
    {
        let mut f = m.function("cg_select_free", binary);
        let entry = f.create_block();
        let c = f.add_block_param(entry, Ty::U64);
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let left = f.heap_alloc(Ty::U64, None, None, AllocOrigin::RustHeap);
        let right = f.heap_alloc(Ty::I64, None, None, AllocOrigin::RustHeap);
        f.store(Ty::U64, left, x);
        let doubled = f.binop(BinOp::Add, Ty::U64, x, x);
        f.store(Ty::U64, right, doubled);
        let zero = f.iconst(Ty::U64, 0);
        let cond = f.icmp(ICmpOp::Ne, Ty::U64, c, zero);
        let first = f.select(Ty::Ptr, cond, left, right);
        let second = f.select(Ty::Ptr, cond, right, left);
        let result = f.load(Ty::U64, first);
        for cell in [first, second] {
            let size = f.iconst(Ty::U64, 8);
            let align = f.iconst(Ty::U64, 8);
            f.call_void(rust_dealloc, vec![cell, size, align]);
        }
        f.ret(vec![result]);
        f.build();
    }

    // cg_join_free(c, x) = c ? x : x + 5; each arm allocates a 16-aligned
    // cell and the join block releases its parameter.
    {
        let mut f = m.function("cg_join_free", binary);
        let entry = f.create_block();
        let left = f.create_block();
        let right = f.create_block();
        let join = f.create_block();
        let c = f.add_block_param(entry, Ty::U64);
        let x = f.add_block_param(entry, Ty::U64);
        let cell = f.add_block_param(join, Ty::Ptr);
        f.switch_to_block(entry);
        let zero = f.iconst(Ty::U64, 0);
        let cond = f.icmp(ICmpOp::Ne, Ty::U64, c, zero);
        f.condbr(cond, left, vec![], right, vec![]);
        f.switch_to_block(left);
        let a = f.heap_alloc(Ty::U64, None, Some(16), AllocOrigin::RustHeap);
        f.store(Ty::U64, a, x);
        f.br(join, vec![a]);
        f.switch_to_block(right);
        let b = f.heap_alloc(Ty::I64, None, Some(16), AllocOrigin::RustHeap);
        let five = f.iconst(Ty::U64, 5);
        let shifted = f.binop(BinOp::Add, Ty::U64, x, five);
        f.store(Ty::U64, b, shifted);
        f.br(join, vec![b]);
        f.switch_to_block(join);
        let result = f.load(Ty::U64, cell);
        let size = f.iconst(Ty::U64, 8);
        let align = f.iconst(Ty::U64, 16);
        f.call_void(rust_dealloc, vec![cell, size, align]);
        f.ret(vec![result]);
        f.build();
    }

    // Negative control: cg_leak(x) never releases its cell and returns its
    // address, so the driver must observe exactly one live block.
    {
        let mut f = m.function("cg_leak", unary);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let cell = f.heap_alloc(Ty::U64, None, None, AllocOrigin::RustHeap);
        f.store(Ty::U64, cell, x);
        let address = f.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, cell);
        f.ret(vec![address]);
        f.build();
    }

    // Negative control: cg_maybe_double_free(c) releases its cell once, and a
    // second time when c != 0 (two calls the backend lowers as written); the
    // driver must observe the repeat.
    {
        let mut f = m.function("cg_maybe_double_free", unary);
        let entry = f.create_block();
        let again = f.create_block();
        let join = f.create_block();
        let c = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let cell = f.heap_alloc(Ty::U64, None, None, AllocOrigin::RustHeap);
        let zero = f.iconst(Ty::U64, 0);
        let cond = f.icmp(ICmpOp::Ne, Ty::U64, c, zero);
        f.condbr(cond, again, vec![], join, vec![]);
        f.switch_to_block(again);
        let size = f.iconst(Ty::U64, 8);
        let align = f.iconst(Ty::U64, 8);
        f.call_void(rust_dealloc, vec![cell, size, align]);
        f.br(join, vec![]);
        f.switch_to_block(join);
        let size = f.iconst(Ty::U64, 8);
        let align = f.iconst(Ty::U64, 8);
        f.call_void(rust_dealloc, vec![cell, size, align]);
        f.ret(vec![zero]);
        f.build();
    }

    let module = m.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&module), []);
    module
}

/// Modules whose only function releases a `HeapAlloc` result through
/// `Inst::Dealloc`, which the backend must refuse whatever the provenance:
/// the most resolvable shape (a same-function `RustHeap` cell of one static
/// layout, and a `CMalloc` block — the shapes the retired lowering emitted
/// `__rust_dealloc` / `free` for), a `Select` of a Rust and a libc
/// allocation, and one cell freed twice. Each is well-formed for
/// `validate_module`; trust-ir refuses each for codegen
/// (`UnlowerableForCodegen`, G18-1).
pub fn dealloc_modules(triple: &str) -> Vec<(&'static str, Module)> {
    let build = |name: &str, body: &dyn Fn(&mut trust_ir_build::FunctionBuilder<'_>)| {
        let mut m = ModuleBuilder::new_with_target_info(name, target(triple));
        let sig = m.add_func_type(vec![Ty::U64], vec![]);
        let mut f = m.function(name, sig);
        let entry = f.create_block();
        let c = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let _ = c;
        body(&mut f);
        f.ret(vec![]);
        f.build();
        let module = m.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(validate_module(&module), []);
        module
    };
    vec![
        (
            "a same-function RustHeap cell",
            build("heap_dealloc_rust", &|f| {
                let cell = f.heap_alloc(Ty::U64, None, None, AllocOrigin::RustHeap);
                f.dealloc(cell);
            }),
        ),
        (
            "a same-function CMalloc block",
            build("heap_dealloc_libc", &|f| {
                let four = f.iconst(Ty::U64, 4);
                let block = f.heap_alloc(Ty::I64, Some(four), None, AllocOrigin::CMalloc);
                f.dealloc(block);
            }),
        ),
        (
            "a Select of a Rust and a libc allocation",
            build("heap_dealloc_mixed", &|f| {
                let rust = f.heap_alloc(Ty::U64, None, None, AllocOrigin::RustHeap);
                let libc = f.heap_alloc(Ty::U64, None, None, AllocOrigin::CMalloc);
                let zero = f.iconst(Ty::U64, 0);
                let one = f.iconst(Ty::U64, 1);
                let cond = f.icmp(ICmpOp::Ne, Ty::U64, one, zero);
                let either = f.select(Ty::Ptr, cond, rust, libc);
                f.dealloc(either);
            }),
        ),
        (
            "one cell freed twice",
            build("heap_dealloc_double", &|f| {
                let cell = f.heap_alloc(Ty::U64, None, None, AllocOrigin::RustHeap);
                f.dealloc(cell);
                f.dealloc(cell);
            }),
        ),
    ]
}

/// The C driver. On Darwin it defines `malloc`/`free` in the executable (the
/// two-level namespace keeps libSystem on its own allocator) and forwards to
/// the default malloc zone; on Linux the link wraps the module's `malloc` and
/// `free` references (`-Wl,--wrap=malloc,--wrap=free`) and forwards to the
/// real symbols. Counting is armed only around each call into the module.
pub const DRIVER: &str = r#"
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef __APPLE__
#include <malloc/malloc.h>
#define CG_MALLOC malloc
#define CG_FREE free
static void *real_malloc(size_t n) { return malloc_zone_malloc(malloc_default_zone(), n); }
static void *real_memalign(size_t a, size_t n) { return malloc_zone_memalign(malloc_default_zone(), a, n); }
static void real_free(void *p) { malloc_zone_free(malloc_default_zone(), p); }
#else
#define CG_MALLOC __wrap_malloc
#define CG_FREE __wrap_free
extern void *__real_malloc(size_t);
extern void __real_free(void *);
static void *real_malloc(size_t n) { return __real_malloc(n); }
static void *real_memalign(size_t a, size_t n) { void *p = 0; return posix_memalign(&p, a, n) ? 0 : p; }
static void real_free(void *p) { __real_free(p); }
#endif

enum { RUST = 1, LIBC = 2 };
struct live { void *p; size_t size, align; int kind; };
static struct live table[16];
static unsigned live_count, armed;
static unsigned rust_allocs, rust_frees, c_allocs, c_frees, errors;
static size_t alloc_size, alloc_align, free_size, free_align, libc_size;

static void track(void *p, size_t size, size_t align, int kind) {
  if (!p || live_count == 16) { errors++; return; }
  table[live_count].p = p; table[live_count].size = size;
  table[live_count].align = align; table[live_count].kind = kind;
  live_count++;
}
/* Releases only a live block of the same allocator and exact layout, and
   poisons it first: a load the backend moved past the release then cannot
   see the value stored before it, whether or not the allocator overwrites
   freed memory (glibc's tcache leaves most of a small block intact). */
static int untrack(void *p, size_t size, size_t align, int kind) {
  for (unsigned i = 0; i < live_count; i++) {
    if (table[i].p != p) continue;
    if (table[i].kind != kind || (kind == RUST && (table[i].size != size || table[i].align != align))) {
      errors++;
      return 0;
    }
    memset(p, 0xa5, table[i].size);
    table[i] = table[--live_count];
    return 1;
  }
  errors++; /* double free or foreign pointer */
  return 0;
}

void *__rust_alloc(size_t size, size_t align) {
  void *p = real_memalign(align < 16 ? 16 : align, size ? size : 1);
  rust_allocs++; alloc_size = size; alloc_align = align;
  if (align == 0 || (align & (align - 1)) != 0 || ((uintptr_t)p & (align - 1)) != 0) errors++;
  track(p, size, align, RUST);
  return p;
}
void __rust_dealloc(void *p, size_t size, size_t align) {
  rust_frees++; free_size = size; free_align = align;
  if (untrack(p, size, align, RUST)) real_free(p);
}
void *CG_MALLOC(size_t n) {
  void *p = real_malloc(n);
  if (armed) { c_allocs++; libc_size = n; track(p, n, 0, LIBC); }
  return p;
}
void CG_FREE(void *p) {
  if (!armed) { real_free(p); return; }
  c_frees++;
  if (untrack(p, 0, 0, LIBC)) real_free(p);
}

extern uint64_t cg_rust_box(uint64_t), cg_rust_array(uint64_t), cg_rust_overaligned(uint64_t);
extern uint64_t cg_c_malloc(uint64_t), cg_leak(uint64_t), cg_maybe_double_free(uint64_t);
extern uint64_t cg_select_free(uint64_t, uint64_t), cg_join_free(uint64_t, uint64_t);

static unsigned checks, failures;
static void arm(void) {
  rust_allocs = rust_frees = c_allocs = c_frees = errors = 0;
  alloc_size = alloc_align = free_size = free_align = libc_size = 0;
  armed = 1;
}
static void check(const char *what, unsigned line, uint64_t actual, uint64_t expected) {
  checks++;
  if (actual != expected) {
    failures++;
    printf("FAIL %s (line %u): %llu != %llu\n", what, line,
           (unsigned long long)actual, (unsigned long long)expected);
  }
}
#define EQ(actual, expected) check(#actual, __LINE__, (uint64_t)(actual), (uint64_t)(expected))
/* A balanced call: nothing left live, no allocator error, no stray libc use. */
static void balanced(unsigned rust, unsigned libc) {
  EQ(rust_allocs, rust); EQ(rust_frees, rust);
  EQ(c_allocs, libc); EQ(c_frees, libc);
  EQ(errors, 0); EQ(live_count, 0);
}

int main(void) {
  const uint64_t boxes[] = {0, 41, UINT64_C(0xfffffffffffffffe)};
  for (unsigned k = 0; k < 3; k++) {
    arm(); uint64_t r = cg_rust_box(boxes[k]); armed = 0;
    EQ(r, boxes[k] + 1); balanced(1, 0);
    EQ(alloc_size, 8); EQ(alloc_align, 8); EQ(free_size, 8); EQ(free_align, 8);
  }
  const uint64_t lengths[] = {1, 7, 100};
  for (unsigned k = 0; k < 3; k++) {
    uint64_t n = lengths[k];
    arm(); uint64_t r = cg_rust_array(n); armed = 0;
    EQ(r, 3 * n * (n - 1) / 2); balanced(1, 0);
    EQ(alloc_size, 4 * n); EQ(alloc_align, 4); EQ(free_size, 4 * n); EQ(free_align, 4);
  }
  arm(); uint64_t over = cg_rust_overaligned(99); armed = 0;
  EQ(over, 99); balanced(1, 0);
  EQ(alloc_size, 24); EQ(alloc_align, 64); EQ(free_size, 24); EQ(free_align, 64);

  arm(); uint64_t sum = cg_c_malloc(10); armed = 0;
  EQ(sum, 46); balanced(0, 1); EQ(libc_size, 32);

  for (uint64_t c = 0; c < 2; c++) {
    arm(); uint64_t r = cg_select_free(c, 21); armed = 0;
    EQ(r, c ? 21 : 42); balanced(2, 0); EQ(free_size, 8); EQ(free_align, 8);
    arm(); r = cg_join_free(c, 9); armed = 0;
    EQ(r, c ? 9 : 14); balanced(1, 0); EQ(free_size, 8); EQ(free_align, 16);
  }

  /* Negative control: the leak must be visible, then is cleaned up here. */
  arm(); uint64_t leaked = cg_leak(5); armed = 0;
  EQ(rust_allocs, 1); EQ(rust_frees, 0); EQ(errors, 0); EQ(live_count, 1);
  EQ((uintptr_t)table[0].p, leaked);
  EQ(*(uint64_t *)(uintptr_t)leaked, 5);
  if (untrack((void *)(uintptr_t)leaked, 8, 8, RUST)) real_free((void *)(uintptr_t)leaked);
  EQ(live_count, 0);

  /* Negative control: the second release must be observed, not forwarded. */
  arm(); cg_maybe_double_free(0); armed = 0;
  balanced(1, 0);
  arm(); cg_maybe_double_free(1); armed = 0;
  EQ(rust_allocs, 1); EQ(rust_frees, 2); EQ(errors, 1); EQ(live_count, 0);

  if (failures) {
    printf("FAILED %u of %u heap checks\n", failures, checks);
    return 1;
  }
  printf("PASS %u heap checks\n", checks);
  return 0;
}
"#;
