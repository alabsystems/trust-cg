// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// C++ helpers of the Darwin mixed-codegen exception/RAII campaign: the
// thrower, the RAII guard, the handler bodies, the C++ middle frame, the touch
// family's provider and memory words, and the per-case event log. Linked
// unchanged into the trust-cg AOT executables, the C++-only reference
// executable, the provider dylib of the CG-dylib arm and the dylib the JIT arm
// loads.
#include "common.h"

#include <cstdarg>
#include <cstdio>
#include <exception>
#include <new>
#include <string>

// ---------------------------------------------------------------------------
// Per-case state (set by driver.cpp)
// ---------------------------------------------------------------------------

unsigned g_kind = 0;        // 0 none, 1 CaseError, 2 DerivedError, 3 int, 4 OtherError
unsigned g_at = 1;          // which cxx_leaf call of the case throws
unsigned g_leaf_calls = 0;  // cxx_leaf calls so far in the case
unsigned g_family = 0;      // 0 compact-unwind twins, 1 DWARF-fallback twins
const tcg_fn *g_fns = nullptr;
int g_live_objects = 0;     // thrown objects (and copies) not yet destroyed
int g_live_guards = 0;      // TcgGuard objects constructed and not destroyed
int g_errors = 0;
std::string g_log;
unsigned g_touch_stage = 0;     // which tcg_provider call of the case throws (0: none)
unsigned g_provider_calls = 0;  // tcg_provider calls so far in the case
unsigned g_provider_dtors = 0;  // tcg_provider frame guards destroyed in the case

extern "C" {
uint64_t tcg_words[3] = {17, 29, 0xfeedface};
}

static void ev(const char *format, ...) {
    char buffer[96];
    va_list args;
    va_start(args, format);
    int length = std::vsnprintf(buffer, sizeof buffer, format, args);
    va_end(args);
    if (length < 0 || length >= static_cast<int>(sizeof buffer)) {
        ++g_errors;
        return;
    }
    if (!g_log.empty()) g_log += ' ';
    g_log += buffer;
}

static unsigned uncaught() { return static_cast<unsigned>(std::uncaught_exceptions()); }

extern "C" int tcg_errors(void) { return g_errors; }

// ---------------------------------------------------------------------------
// Thrown types
// ---------------------------------------------------------------------------

CaseError::CaseError(unsigned value) : payload(value) { ++g_live_objects; }
CaseError::CaseError(const CaseError &other) : payload(other.payload) { ++g_live_objects; }
CaseError::~CaseError() {
    --g_live_objects;
    ev("x1");
}
unsigned CaseError::tag() const { return 1; }

DerivedError::DerivedError(unsigned value) : CaseError(value), extra(value * 0x9e3779b1u + 0x7f4a7c15u) {}
DerivedError::DerivedError(const DerivedError &other) : CaseError(other), extra(other.extra) {}
DerivedError::~DerivedError() { ev("x2"); }
unsigned DerivedError::tag() const { return 2; }

OtherError::OtherError(unsigned value) : code(value) { ++g_live_objects; }
OtherError::OtherError(const OtherError &other) : code(other.code) { ++g_live_objects; }
OtherError::~OtherError() {
    --g_live_objects;
    ev("x4");
}

TouchError::TouchError(uint64_t value, unsigned at) : payload(value), stage(at) { ++g_live_objects; }
TouchError::TouchError(const TouchError &other) : payload(other.payload), stage(other.stage) {
    ++g_live_objects;
}
TouchError::~TouchError() {
    --g_live_objects;
    ev("x5");
}

struct InnerError {
    explicit InnerError(unsigned value) : site(value) { ++g_live_objects; }
    InnerError(const InnerError &other) : site(other.site) { ++g_live_objects; }
    ~InnerError() { --g_live_objects; }
    unsigned site;
};

// ---------------------------------------------------------------------------
// RAII guard
// ---------------------------------------------------------------------------

static const unsigned GUARD_MAGIC = 0x6a09e667u;
static const unsigned GUARD_DEAD = 0xdeadbeefu;

TcgGuard::TcgGuard(unsigned value) : magic(GUARD_MAGIC), id(value), self(this) {
    ++g_live_guards;
    ev("G%u", id);
}

TcgGuard::~TcgGuard() {
    if (magic != GUARD_MAGIC || self != this) {
        ++g_errors;
        ev("BADGUARD");
        return;
    }
    ev("D%uu%u", id, uncaught());
    magic = GUARD_DEAD;
    self = nullptr;
    --g_live_guards;
}

extern "C" void tcg_guard_init(TcgGuard *guard, unsigned id) { new (guard) TcgGuard(id); }

extern "C" void tcg_guard_fini(TcgGuard *guard) { guard->~TcgGuard(); }

// ---------------------------------------------------------------------------
// Thrower
// ---------------------------------------------------------------------------

namespace {
struct LeafGuard {
    ~LeafGuard() { ev("l%u", uncaught()); }
};
}  // namespace

extern "C" unsigned cxx_leaf(unsigned x) {
    LeafGuard guard;
    unsigned call = ++g_leaf_calls;
    ev("L%u", call);
    if (g_kind != 0 && call == g_at) {
        unsigned payload = x * 2654435761u + call * 40503u + g_kind;
        switch (g_kind) {
        case 1:
            throw CaseError(payload);
        case 2:
            throw DerivedError(payload);
        case 3:
            throw static_cast<int>(payload ^ 0x5a5a5a5au);
        case 4:
            throw OtherError(payload);
        default:
            ++g_errors;
            break;
        }
    }
    return x * 3u + call;
}

// ---------------------------------------------------------------------------
// Handler bodies
// ---------------------------------------------------------------------------

// Classify the exception currently being handled by rethrowing it into this
// frame's own handlers (the caller has begun catching it).
extern "C" unsigned tcg_on_any(unsigned site) {
    unsigned kind = 9, payload = 0;
    try {
        throw;
    } catch (DerivedError &error) {
        kind = 2;
        payload = error.payload ^ error.extra;
    } catch (CaseError &error) {
        kind = 1;
        payload = error.payload;
    } catch (int value) {
        kind = 3;
        payload = static_cast<unsigned>(value);
    } catch (OtherError &error) {
        kind = 4;
        payload = error.code;
    } catch (TouchError &error) {
        kind = 5;
        payload = static_cast<unsigned>(error.payload);
    } catch (...) {
    }
    ev("A%uk%up%x", site, kind, payload);
    return site * 1000u + kind;
}

extern "C" unsigned tcg_on_case(unsigned site, CaseError *error) {
    unsigned tag = error->tag();
    unsigned payload = error->payload;
    if (tag == 2) payload ^= static_cast<DerivedError *>(error)->extra;
    ev("K%ut%up%x", site, tag, payload);
    return site * 1000u + tag;
}

extern "C" unsigned tcg_on_int(unsigned site, unsigned value) {
    ev("I%up%x", site, value);
    return site * 1000u + 3u;
}

extern "C" void tcg_note(unsigned site) { ev("N%uu%u", site, uncaught()); }

// ---------------------------------------------------------------------------
// C++ middle frame and the in-cleanup throw
// ---------------------------------------------------------------------------

namespace {
struct MidGuard {
    ~MidGuard() { ev("m%u", uncaught()); }
};
}  // namespace

extern "C" unsigned cxx_mid_frame(unsigned x) {
    ev("M");
    try {
        MidGuard guard;
        return g_fns[g_family * NCHAINS + C_cleanup](x) + 5u;
    } catch (...) {
        ev("R%u", uncaught());
        throw;
    }
}

extern "C" void tcg_inner_throw(unsigned site) {
    unsigned before = uncaught();
    try {
        throw InnerError(site);
    } catch (InnerError &error) {
        ev("J%uu%uv%u", error.site, before, uncaught());
    }
}

extern "C" void tcg_scratch(char *buffer, unsigned long length) {
    for (unsigned long index = 0; index < length; ++index)
        buffer[index] = static_cast<char>(index ^ length);
}

// ---------------------------------------------------------------------------
// The touch family's provider
// ---------------------------------------------------------------------------

namespace {
struct ProviderGuard {
    ~ProviderGuard() {
        ++g_provider_dtors;
        ev("p%u", uncaught());
    }
};
}  // namespace

// The Linux campaign's provider (e2e_aarch64_elf_link.rs UNWIND_PROVIDER):
// updates the word the CG caller hands it and throws on its `g_touch_stage`-th
// call of the case, with a payload that binds the input and the updated word.
extern "C" uint64_t tcg_provider(uint64_t x, uint64_t *word) {
    ProviderGuard guard;
    unsigned stage = ++g_provider_calls;
    ev("V%u", stage);
    *word += x * UINT64_C(0x100000001b3) + UINT64_C(0x27d4eb2d);
    if (g_touch_stage == stage) throw TouchError(x ^ *word ^ UINT64_C(0xdecafbad12345678), stage);
    return *word ^ (x >> 7);
}
