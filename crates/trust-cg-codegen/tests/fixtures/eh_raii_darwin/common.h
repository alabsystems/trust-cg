// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// Shared declarations of the Darwin mixed-codegen exception/RAII campaign
// (tests/e2e_aarch64_eh_raii_darwin.rs, ledger X-DARWIN-P7).
//
// One C++ driver (driver.cpp) and one set of C++ helpers (helpers.cpp) run the
// same two case matrices (the chains and the touch family) over three
// implementations of the `tcg_*` functions: the trust-cg object (AOT, O0-O3,
// linked into the executable or into a dylib of its own), the in-memory
// trust-cg JIT, and the C++-only reference (reference.cpp). Every case prints
// one trace line; the Rust test requires each implementation's lines to equal
// the reference's.
#pragma once

#include <cstdint>

typedef unsigned (*tcg_fn)(unsigned);

// The chain functions, in table order. The Rust test's `CXX_CHAINS` names the
// same functions in the same order; each has a compact-unwind twin `tcg_NAME`
// and a DWARF-fallback twin `tcg_NAME_dyn` (a runtime-sized frame).
#define TCG_CHAINS(X)          \
    X(cleanup)                 \
    X(catch_all)               \
    X(catch_case)              \
    X(catch_int_or_case)       \
    X(catch_case_then_all)     \
    X(guard_catch_int)         \
    X(two_guards)              \
    X(nested_cleanup)          \
    X(plain_mid)               \
    X(catch_over_plain)        \
    X(rethrow)                 \
    X(cxx_mid)                 \
    X(cleanup_inner_throw)     \
    X(empty_cleanup)           \
    X(deep_catch)

#define TCG_CHAIN_INDEX(name) C_##name,
enum { TCG_CHAINS(TCG_CHAIN_INDEX) NCHAINS };
#undef TCG_CHAIN_INDEX

// The thrown types. CaseError has an out-of-line key function (its
// destructor), so helpers.cpp owns a strong, default-visibility typeinfo
// `__ZTI9CaseError` that the CG typed catches bind through the GOT.
struct CaseError {
    explicit CaseError(unsigned payload);
    CaseError(const CaseError &other);
    virtual ~CaseError();
    virtual unsigned tag() const;
    unsigned payload;
};

struct DerivedError : CaseError {
    explicit DerivedError(unsigned payload);
    DerivedError(const DerivedError &other);
    ~DerivedError() override;
    unsigned tag() const override;
    unsigned extra;
};

struct OtherError {
    explicit OtherError(unsigned code);
    OtherError(const OtherError &other);
    ~OtherError();
    unsigned code;
};

// A RAII object that lives in a frame's own storage. The reference declares
// it as an ordinary local; a CG frame gives it a 16-byte stack slot,
// constructs it with `tcg_guard_init` and runs its destructor with
// `tcg_guard_fini` (on the normal path and in its cleanup landing pad). The
// destructor checks the object's address and magic, so a landing pad that
// reaches the slot through a wrongly restored frame is observed.
struct TcgGuard {
    explicit TcgGuard(unsigned id);
    ~TcgGuard();
    TcgGuard(const TcgGuard &) = delete;
    TcgGuard &operator=(const TcgGuard &) = delete;
    unsigned magic;
    unsigned id;
    const TcgGuard *self;
};
static_assert(sizeof(TcgGuard) == 16, "the CG slot is 16 bytes");
static_assert(alignof(TcgGuard) == 8, "the CG slot is 8-aligned");

// The touch family: the Linux campaign's CG frame shape
// (tests/e2e_aarch64_elf_link.rs, UNWIND_PROVIDER/UNWIND_DRIVER) on 64-bit
// inputs. A CG function adds its input to `tcg_words[0]`, reads `&tcg_words[1]`
// from a data slot, calls `tcg_provider` directly and then again through a
// function-pointer slot; the provider updates the word it is handed and
// either call may throw a TouchError. `touch_guarded` also runs a CG-slot
// guard's destructor in a cleanup pad around the direct call and destroys the
// guard before the indirect call, which unwinds through the frame's LSDA with
// no pad. `touch_catch` is a CG catch-all frame over `touch`. Each has a
// compact-unwind twin `tcg_NAME` and a runtime-sized twin `tcg_NAME_dyn`.
typedef uint64_t (*tcg_touch_fn)(uint64_t);

#define TCG_TOUCH_CHAINS(X) \
    X(touch)                \
    X(touch_guarded)        \
    X(touch_catch)

#define TCG_TOUCH_INDEX(name) T_##name,
enum { TCG_TOUCH_CHAINS(TCG_TOUCH_INDEX) NTOUCH };
#undef TCG_TOUCH_INDEX

struct TouchError {
    TouchError(uint64_t payload, unsigned stage);
    TouchError(const TouchError &other);
    ~TouchError();
    uint64_t payload;
    unsigned stage;
};

extern "C" {
// The thrower: the `g_at`-th call in a case throws `g_kind`.
unsigned cxx_leaf(unsigned x);
void tcg_guard_init(TcgGuard *guard, unsigned id);
void tcg_guard_fini(TcgGuard *guard);
// Handlers' bodies: each logs the site and the exception it holds and returns
// `site * 1000 + kind`.
unsigned tcg_on_any(unsigned site);
unsigned tcg_on_case(unsigned site, CaseError *error);
unsigned tcg_on_int(unsigned site, unsigned value);
void tcg_note(unsigned site);
// A C++ frame between CG frames: calls the current implementation's
// `cleanup` chain and rethrows whatever reaches its catch-all.
unsigned cxx_mid_frame(unsigned x);
// Throws and catches its own exception (used from a cleanup that runs while
// another exception is in flight).
void tcg_inner_throw(unsigned site);
// Touches a runtime-sized buffer so the DWARF-fallback frames keep it.
void tcg_scratch(char *buffer, unsigned long length);
// Runs the whole matrix over `fns` (2 * NCHAINS entries: compact twins, then
// DWARF-fallback twins; a null entry is skipped) and writes one line per case
// to `out_path` (stdout when null). Returns the number of cases run.
int tcg_run_matrix(const tcg_fn *fns, const char *out_path);
// Integrity failures the helpers observed (a bad guard, an overflowing log).
int tcg_errors(void);
// The touch family's memory words and provider: the provider's `stage`-th
// call in a case throws when it equals `g_touch_stage`.
extern uint64_t tcg_words[3];
uint64_t tcg_provider(uint64_t x, uint64_t *word);
// Runs the touch matrix over `fns` (2 * NTOUCH entries, compact twins first;
// a null entry is skipped): 64 inputs (eight 64-bit edges, then a fixed
// LCG sequence) and three throw stages (none, the direct call, the indirect
// call), one line per case, to `out_path` (stdout when null).
int tcg_run_touch(const tcg_touch_fn *fns, const char *out_path);
}
