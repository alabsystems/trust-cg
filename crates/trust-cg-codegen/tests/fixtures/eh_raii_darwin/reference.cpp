// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// The C++-only reference of the Darwin mixed-codegen exception/RAII campaign:
// the `tcg_*` chain and touch functions written as ordinary C++ (RAII locals,
// try/catch, `throw;`, a call through a function-pointer slot). The trust-cg twins in tests/e2e_aarch64_eh_raii_darwin.rs build
// the same control flow from trust-ir `Invoke`/`LandingPad`/`Resume`; the
// test requires both to print identical traces. `_dyn` twins also allocate a
// runtime-sized buffer, as the trust-cg DWARF-fallback twins do; the frame
// shape of the reference is not observable in the trace.
#include "common.h"

#include <alloca.h>

template <bool Dynamic> static void prologue(unsigned x, char *buffer, unsigned long length) {
    (void)x;
    if (Dynamic) tcg_scratch(buffer, length);
}

#define TCG_DYNAMIC_PROLOGUE(D, x)                                                     \
    unsigned long length_ = ((x) & 63u) + 8u;                                          \
    char *buffer_ = D ? static_cast<char *>(__builtin_alloca(length_)) : nullptr;      \
    prologue<D>((x), buffer_, length_)

template <bool D> unsigned same_cleanup(unsigned x);
template <bool D> unsigned same_plain_mid(unsigned x);
template <bool D> unsigned same_nested_cleanup(unsigned x);

template <bool D> static unsigned r_cleanup(unsigned x) {
    TCG_DYNAMIC_PROLOGUE(D, x);
    TcgGuard guard(1);
    return cxx_leaf(x) + 1u;
}

template <bool D> static unsigned r_catch_all(unsigned x) {
    TCG_DYNAMIC_PROLOGUE(D, x);
    try {
        return cxx_leaf(x) + 2u;
    } catch (...) {
        return tcg_on_any(21);
    }
}

template <bool D> static unsigned r_catch_case(unsigned x) {
    TCG_DYNAMIC_PROLOGUE(D, x);
    try {
        return cxx_leaf(x) + 3u;
    } catch (CaseError &error) {
        return tcg_on_case(31, &error);
    }
}

template <bool D> static unsigned r_catch_int_or_case(unsigned x) {
    TCG_DYNAMIC_PROLOGUE(D, x);
    try {
        return cxx_leaf(x) + 4u;
    } catch (int value) {
        return tcg_on_int(41, static_cast<unsigned>(value));
    } catch (CaseError &error) {
        return tcg_on_case(42, &error);
    }
}

template <bool D> static unsigned r_catch_case_then_all(unsigned x) {
    TCG_DYNAMIC_PROLOGUE(D, x);
    try {
        return cxx_leaf(x) + 5u;
    } catch (CaseError &error) {
        return tcg_on_case(51, &error);
    } catch (...) {
        return tcg_on_any(52);
    }
}

template <bool D> static unsigned r_guard_catch_int(unsigned x) {
    TCG_DYNAMIC_PROLOGUE(D, x);
    try {
        TcgGuard guard(6);
        return cxx_leaf(x) + 6u;
    } catch (int value) {
        return tcg_on_int(61, static_cast<unsigned>(value));
    }
}

template <bool D> static unsigned r_two_guards(unsigned x) {
    TCG_DYNAMIC_PROLOGUE(D, x);
    TcgGuard first(71);
    unsigned r1 = cxx_leaf(x);
    TcgGuard second(72);
    unsigned r2 = cxx_leaf(r1);
    return r1 ^ r2;
}

template <bool D> static unsigned r_nested_cleanup(unsigned x) {
    TCG_DYNAMIC_PROLOGUE(D, x);
    TcgGuard guard(8);
    return same_cleanup<D>(x) + 8u;
}

template <bool D> static unsigned r_plain_mid(unsigned x) {
    TCG_DYNAMIC_PROLOGUE(D, x);
    return cxx_leaf(x) + 9u;
}

template <bool D> static unsigned r_catch_over_plain(unsigned x) {
    TCG_DYNAMIC_PROLOGUE(D, x);
    try {
        return same_plain_mid<D>(x) + 10u;
    } catch (...) {
        return tcg_on_any(101);
    }
}

template <bool D> static unsigned r_rethrow(unsigned x) {
    TCG_DYNAMIC_PROLOGUE(D, x);
    try {
        return cxx_leaf(x) + 11u;
    } catch (...) {
        tcg_note(111);
        throw;
    }
}

template <bool D> static unsigned r_cxx_mid(unsigned x) {
    TCG_DYNAMIC_PROLOGUE(D, x);
    TcgGuard guard(12);
    return cxx_mid_frame(x) + 12u;
}

namespace {
struct InnerThrowOnExit {
    ~InnerThrowOnExit() { tcg_inner_throw(13); }
};
}  // namespace

template <bool D> static unsigned r_cleanup_inner_throw(unsigned x) {
    TCG_DYNAMIC_PROLOGUE(D, x);
    InnerThrowOnExit on_exit;
    return cxx_leaf(x) + 13u;
}

template <bool D> static unsigned r_empty_cleanup(unsigned x) {
    TCG_DYNAMIC_PROLOGUE(D, x);
    return cxx_leaf(x) + 14u;
}

template <bool D> static unsigned r_deep_catch(unsigned x) {
    TCG_DYNAMIC_PROLOGUE(D, x);
    try {
        return same_nested_cleanup<D>(x) + 15u;
    } catch (...) {
        return tcg_on_any(151);
    }
}

#define TCG_CHAIN_DEFINE(name)                                                     \
    extern "C" __attribute__((noinline)) unsigned tcg_##name(unsigned x) {        \
        return r_##name<false>(x);                                                 \
    }                                                                              \
    extern "C" __attribute__((noinline)) unsigned tcg_##name##_dyn(unsigned x) {  \
        return r_##name<true>(x);                                                  \
    }
TCG_CHAINS(TCG_CHAIN_DEFINE)
#undef TCG_CHAIN_DEFINE

// ---------------------------------------------------------------------------
// The touch family
// ---------------------------------------------------------------------------

// The trust-cg module's two pointer slots: `&tcg_words[1]` and the provider.
// Volatile, so the reference, like the CG code, reads both at run time and
// makes the second provider call indirectly.
static uint64_t *volatile g_touch_data_slot = &tcg_words[1];
static uint64_t (*volatile g_touch_fn_slot)(uint64_t, uint64_t *) = tcg_provider;

template <bool D> uint64_t same_touch(uint64_t x);

template <bool D> static uint64_t r_touch(uint64_t x) {
    TCG_DYNAMIC_PROLOGUE(D, x);
    tcg_words[0] += x;
    uint64_t *word = g_touch_data_slot;
    uint64_t first = tcg_provider(x, word);
    return g_touch_fn_slot(first, word);
}

template <bool D> static uint64_t r_touch_guarded(uint64_t x) {
    TCG_DYNAMIC_PROLOGUE(D, x);
    tcg_words[0] += x;
    uint64_t *word = g_touch_data_slot;
    uint64_t first;
    {
        TcgGuard guard(31);
        first = tcg_provider(x, word);
    }
    return g_touch_fn_slot(first, word);
}

template <bool D> static uint64_t r_touch_catch(uint64_t x) {
    TCG_DYNAMIC_PROLOGUE(D, x);
    try {
        return same_touch<D>(x) + 32u;
    } catch (...) {
        return tcg_on_any(301);
    }
}

#define TCG_TOUCH_DEFINE(name)                                                     \
    extern "C" __attribute__((noinline)) uint64_t tcg_##name(uint64_t x) {        \
        return r_##name<false>(x);                                                 \
    }                                                                              \
    extern "C" __attribute__((noinline)) uint64_t tcg_##name##_dyn(uint64_t x) {  \
        return r_##name<true>(x);                                                  \
    }
TCG_TOUCH_CHAINS(TCG_TOUCH_DEFINE)
#undef TCG_TOUCH_DEFINE

template <bool D> uint64_t same_touch(uint64_t x) {
    return D ? tcg_touch_dyn(x) : tcg_touch(x);
}

template <bool D> unsigned same_cleanup(unsigned x) {
    return D ? tcg_cleanup_dyn(x) : tcg_cleanup(x);
}
template <bool D> unsigned same_plain_mid(unsigned x) {
    return D ? tcg_plain_mid_dyn(x) : tcg_plain_mid(x);
}
template <bool D> unsigned same_nested_cleanup(unsigned x) {
    return D ? tcg_nested_cleanup_dyn(x) : tcg_nested_cleanup(x);
}
