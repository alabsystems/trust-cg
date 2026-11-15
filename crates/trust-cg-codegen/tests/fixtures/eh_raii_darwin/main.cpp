// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// Entry point of the executables of the Darwin mixed-codegen exception/RAII
// campaign: the `tcg_*` functions come from the trust-cg object (linked into
// the executable, or into a dylib of its own) or from reference.cpp. The
// trace goes to stdout: the chain matrix, its summary line, then the touch
// matrix and its summary line.
#include "common.h"

#define TCG_CHAIN_DECLARE(name) unsigned tcg_##name(unsigned), tcg_##name##_dyn(unsigned);
#define TCG_TOUCH_DECLARE(name) uint64_t tcg_##name(uint64_t), tcg_##name##_dyn(uint64_t);
extern "C" {
TCG_CHAINS(TCG_CHAIN_DECLARE)
TCG_TOUCH_CHAINS(TCG_TOUCH_DECLARE)
}
#undef TCG_CHAIN_DECLARE
#undef TCG_TOUCH_DECLARE

#define TCG_CHAIN_COMPACT(name) tcg_##name,
#define TCG_CHAIN_DYNAMIC(name) tcg_##name##_dyn,
static const tcg_fn FUNCTIONS[2 * NCHAINS] = {TCG_CHAINS(TCG_CHAIN_COMPACT)
                                                  TCG_CHAINS(TCG_CHAIN_DYNAMIC)};
static const tcg_touch_fn TOUCH_FUNCTIONS[2 * NTOUCH] = {
    TCG_TOUCH_CHAINS(TCG_CHAIN_COMPACT) TCG_TOUCH_CHAINS(TCG_CHAIN_DYNAMIC)};
#undef TCG_CHAIN_COMPACT
#undef TCG_CHAIN_DYNAMIC

int main() {
    int cases = tcg_run_matrix(FUNCTIONS, nullptr);
    int touch_cases = tcg_run_touch(TOUCH_FUNCTIONS, nullptr);
    return cases > 0 && touch_cases > 0 && tcg_errors() == 0 ? 0 : 1;
}
