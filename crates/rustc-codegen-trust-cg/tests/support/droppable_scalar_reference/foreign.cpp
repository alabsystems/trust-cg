// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
#include <cstdint>
#include <unwind.h>
static std::uint64_t drops, destroyed_value;
struct Payload {
    std::uint64_t value;
    ~Payload() { ++drops; destroyed_value = value; }
};
extern "C" void raise_foreign() { throw Payload{91}; }
extern "C" std::uint64_t finish_foreign(void *exception) noexcept {
    _Unwind_DeleteException(static_cast<_Unwind_Exception *>(exception));
    return destroyed_value;
}
extern "C" std::uint64_t foreign_drops() noexcept { return drops; }
