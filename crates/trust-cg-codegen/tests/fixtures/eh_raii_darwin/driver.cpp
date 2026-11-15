// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// The case matrix of the Darwin mixed-codegen exception/RAII campaign. For
// every chain twin present in the table, every thrown kind (none, CaseError,
// DerivedError, int, OtherError), every throwing call (the second leaf call
// too, for the chain with two) and four inputs, one case calls the chain
// under the driver's own typed C++ handlers and a driver-frame TcgGuard, then
// prints one line: the return value, the catch site and payload, the ordered
// event log (constructions, destructor runs with the in-flight exception
// count, handler entries, exception-object destructions) and the residual
// state (live thrown objects, live guards, uncaught exceptions, a current
// exception), which must all be zero. The touch matrix does the same for the
// touch family over 64-bit inputs and three throw stages, and also prints the
// three memory words and the provider's call and destructor counts.
//
// Every line is flushed as soon as it is written, so a case that crashes the
// process (the likeliest symptom of a bad unwind table) leaves every earlier
// line behind: the crashing case is the one after the last line.
#include "common.h"

#include <cinttypes>
#include <cstdio>
#include <exception>
#include <string>

extern unsigned g_kind, g_at, g_leaf_calls, g_family;
extern unsigned g_touch_stage, g_provider_calls, g_provider_dtors;
extern const tcg_fn *g_fns;
extern int g_live_objects, g_live_guards, g_errors;
extern std::string g_log;

#define TCG_CHAIN_NAME(name) #name,
static const char *const CHAIN_NAMES[NCHAINS] = {TCG_CHAINS(TCG_CHAIN_NAME)};
#undef TCG_CHAIN_NAME

static const unsigned INPUTS[4] = {0u, 7u, 0x7fffffffu, 0x9e3779b9u};

static void run_case(FILE *out, unsigned family, unsigned chain, tcg_fn fn, unsigned kind,
                     unsigned at, unsigned x) {
    g_family = family;
    g_kind = kind;
    g_at = at;
    g_leaf_calls = 0;
    g_log.clear();
    // Each line reports its own case's residue: a leak stays in that line.
    g_live_objects = 0;
    g_live_guards = 0;
    unsigned result = 0, site = 0, payload = 0;
    try {
        TcgGuard top(900);
        result = fn(x);
    } catch (DerivedError &error) {
        site = 902;
        payload = error.payload ^ error.extra;
    } catch (CaseError &error) {
        site = 901;
        payload = error.payload;
    } catch (int value) {
        site = 903;
        payload = static_cast<unsigned>(value);
    } catch (OtherError &error) {
        site = 904;
        payload = error.code;
    } catch (...) {
        site = 909;
    }
    std::fprintf(out,
                 "%s%s k=%u a=%u x=%08x ret=%08x site=%u pay=%08x ev=[%s] live=%d guards=%d "
                 "unc=%d cur=%d\n",
                 CHAIN_NAMES[chain], family ? "_dyn" : "", kind, at, x, result, site, payload,
                 g_log.c_str(), g_live_objects, g_live_guards, std::uncaught_exceptions(),
                 std::current_exception() ? 1 : 0);
    std::fflush(out);
}

extern "C" int tcg_run_matrix(const tcg_fn *fns, const char *out_path) {
    FILE *out = out_path ? std::fopen(out_path, "w") : stdout;
    if (!out) return -1;
    g_fns = fns;
    int cases = 0;
    for (unsigned family = 0; family < 2; ++family) {
        for (unsigned chain = 0; chain < NCHAINS; ++chain) {
            tcg_fn fn = fns[family * NCHAINS + chain];
            if (!fn) continue;
            for (unsigned kind = 0; kind < 5; ++kind) {
                unsigned throwing_calls = (chain == C_two_guards && kind != 0) ? 2 : 1;
                for (unsigned at = 1; at <= throwing_calls; ++at) {
                    for (unsigned input : INPUTS) {
                        run_case(out, family, chain, fn, kind, at, input);
                        ++cases;
                    }
                }
            }
        }
    }
    std::fprintf(out, "cases=%d errors=%d\n", cases, g_errors);
    if (out != stdout) std::fclose(out);
    else std::fflush(out);
    return cases;
}

// ---------------------------------------------------------------------------
// The touch matrix
// ---------------------------------------------------------------------------

#define TCG_TOUCH_NAME(name) #name,
static const char *const TOUCH_NAMES[NTOUCH] = {TCG_TOUCH_CHAINS(TCG_TOUCH_NAME)};
#undef TCG_TOUCH_NAME

// The Linux campaign's inputs: eight 64-bit edges, then its LCG sequence.
static const uint64_t TOUCH_EDGES[8] = {0,
                                        1,
                                        UINT64_MAX,
                                        UINT64_C(0x8000000000000000),
                                        UINT64_C(0x7fffffffffffffff),
                                        UINT64_C(0x100000000),
                                        255,
                                        256};
static const unsigned TOUCH_INPUTS = 64;

static void run_touch_case(FILE *out, unsigned family, unsigned chain, tcg_touch_fn fn,
                           unsigned stage, unsigned index, uint64_t random, uint64_t x) {
    g_touch_stage = stage;
    g_provider_calls = 0;
    g_provider_dtors = 0;
    g_log.clear();
    g_live_objects = 0;
    g_live_guards = 0;
    tcg_words[0] = random;
    tcg_words[1] = ~random;
    tcg_words[2] = UINT64_C(0xfeedfacecafebeef);
    uint64_t result = 0, payload = 0;
    unsigned site = 0, thrown_stage = 0;
    try {
        TcgGuard top(900);
        result = fn(x);
    } catch (TouchError &error) {
        site = 905;
        payload = error.payload;
        thrown_stage = error.stage;
    } catch (...) {
        site = 909;
    }
    std::fprintf(out,
                 "%s%s s=%u i=%u r=%016" PRIx64 " x=%016" PRIx64 " ret=%016" PRIx64
                 " site=%u pay=%016" PRIx64 " st=%u w0=%016" PRIx64 " w1=%016" PRIx64
                 " w2=%016" PRIx64 " calls=%u pd=%u ev=[%s] live=%d guards=%d unc=%d cur=%d\n",
                 TOUCH_NAMES[chain], family ? "_dyn" : "", stage, index, random, x, result, site,
                 payload, thrown_stage, tcg_words[0], tcg_words[1], tcg_words[2],
                 g_provider_calls, g_provider_dtors, g_log.c_str(), g_live_objects,
                 g_live_guards, std::uncaught_exceptions(), std::current_exception() ? 1 : 0);
    std::fflush(out);
}

extern "C" int tcg_run_touch(const tcg_touch_fn *fns, const char *out_path) {
    FILE *out = out_path ? std::fopen(out_path, "w") : stdout;
    if (!out) return -1;
    int cases = 0;
    for (unsigned family = 0; family < 2; ++family) {
        for (unsigned chain = 0; chain < NTOUCH; ++chain) {
            tcg_touch_fn fn = fns[family * NTOUCH + chain];
            if (!fn) continue;
            uint64_t random = UINT64_C(0x3141592653589793);
            for (unsigned index = 0; index < TOUCH_INPUTS; ++index) {
                random = random * UINT64_C(6364136223846793005) + 1;
                uint64_t x = index < 8 ? TOUCH_EDGES[index] : random;
                for (unsigned stage = 0; stage < 3; ++stage) {
                    run_touch_case(out, family, chain, fn, stage, index, random, x);
                    ++cases;
                }
            }
        }
    }
    std::fprintf(out, "cases=%d errors=%d\n", cases, g_errors);
    if (out != stdout) std::fclose(out);
    else std::fflush(out);
    return cases;
}
