#include <dlfcn.h>
#include <inttypes.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
typedef uint64_t (*Function)(uint64_t);
typedef struct { uintptr_t address; uint64_t a, b; } Triple;
#ifdef OVERRIDE
uint64_t exported_function(uint64_t x) { return x * 23 + 11; }
const uint64_t EXPORTED_DATA = UINT64_C(0xfedcba9876543210);
uintptr_t own_address(void) { return (uintptr_t)&own_address; }
Triple own_triple(uint64_t x) { return (Triple){ (uintptr_t)&own_triple, x + 1, x + 2 }; }
#endif
#ifdef DIRECT
extern uint64_t exported_function(uint64_t);
extern const uint64_t EXPORTED_DATA;
extern Function function_address(void);
extern uint64_t direct_call(uint64_t);
extern uintptr_t own_address(void);
extern Triple own_triple(uint64_t);
extern const uint64_t *data_address(void);
extern uint64_t tls_replace(uint64_t);
extern Function hidden_address(void);
#endif
static void fail(const char *expr, unsigned line) {
    fprintf(stderr, "FAIL %s line=%u\n", expr, line); exit(1);
}
#define CHECK(expr) do { if (!(expr)) fail(#expr, __LINE__); ++checks; } while (0)
typedef struct { Function replace; uint64_t seed; size_t checks; } Thread;
static void *worker(void *raw) {
    Thread *t = raw; size_t checks = 0; uint64_t previous = UINT64_C(0x987654321);
    for (uint64_t i = 0; i < 256; ++i) {
        uint64_t next = t->seed + i * UINT64_C(0x9876543210);
        CHECK(t->replace(next) == previous); previous = next;
    }
    t->checks = checks; return NULL;
}
int main(int argc, char **argv) {
    size_t checks = 0;
#ifdef DIRECT
    (void)argc; (void)argv;
    Function (*address)(void) = function_address;
    Function direct = direct_call;
    uintptr_t (*own)(void) = own_address;
    Triple (*triple)(uint64_t) = own_triple;
    const uint64_t *(*data)(void) = data_address;
    Function replace = tls_replace;
    Function (*hidden)(void) = hidden_address;
    Function expected_function = exported_function;
    const uint64_t *expected_data = &EXPORTED_DATA;
    uintptr_t expected_own = (uintptr_t)&own_address;
    uintptr_t expected_triple = (uintptr_t)&own_triple;
#else
    CHECK(argc == 2);
    void *handle = dlopen(argv[1], RTLD_NOW | RTLD_GLOBAL);
    CHECK(handle != NULL);
    Function (*address)(void) = (Function (*)(void))dlsym(handle, "function_address");
    Function direct = (Function)dlsym(handle, "direct_call");
    uintptr_t (*own)(void) = (uintptr_t (*)(void))dlsym(handle, "own_address");
    Triple (*triple)(uint64_t) = (Triple (*)(uint64_t))dlsym(handle, "own_triple");
    const uint64_t *(*data)(void) = (const uint64_t *(*)(void))dlsym(handle, "data_address");
    Function replace = (Function)dlsym(handle, "tls_replace");
    Function (*hidden)(void) = (Function (*)(void))dlsym(handle, "hidden_address");
    Function expected_function = (Function)dlsym(RTLD_DEFAULT, "exported_function");
    const uint64_t *expected_data = (const uint64_t *)dlsym(RTLD_DEFAULT, "EXPORTED_DATA");
    uintptr_t expected_own = (uintptr_t)dlsym(RTLD_DEFAULT, "own_address");
    uintptr_t expected_triple = (uintptr_t)dlsym(RTLD_DEFAULT, "own_triple");
#endif
    CHECK(address && data && direct && own && triple && replace && hidden);
    CHECK(expected_function && expected_data && expected_own && expected_triple);
    CHECK(address() == expected_function);
    CHECK(data() == expected_data);
    CHECK(own() == expected_own);
#ifdef OVERRIDE
    CHECK(*data() == UINT64_C(0xfedcba9876543210));
#else
    CHECK(*data() == UINT64_C(0x123456789abcdef));
#endif
    for (uint64_t i = 0; i < 1024; ++i) {
        uint64_t x = i * UINT64_C(0x123456789abc);
#ifdef OVERRIDE
        uint64_t expected = x * 23 + 11;
#else
        uint64_t expected = x * 19 + 7;
#endif
        CHECK(address()(x) == expected);
        CHECK(direct(x) == expected);
        Triple t = triple(x);
        CHECK(t.address == expected_triple);
        /* dlsym(handle) selects the library body even when its own symbol's
           canonical address is preempted by the executable. */
        CHECK(t.a == x);
        CHECK(t.b == (x ^ UINT64_C(0xabcdef0123456789)));
        CHECK(hidden()(x) == (((x << 13) | (x >> 51)) ^ UINT64_C(0xaabbccdd)));
    }
    CHECK(replace(17) == UINT64_C(0x987654321));
    pthread_t ids[4]; Thread tasks[4];
    for (size_t i = 0; i < 4; ++i) {
        tasks[i] = (Thread){ replace, i * UINT64_C(0xabcdef), 0 };
        CHECK(pthread_create(&ids[i], NULL, worker, &tasks[i]) == 0);
    }
    for (size_t i = 0; i < 4; ++i) {
        CHECK(pthread_join(ids[i], NULL) == 0); checks += tasks[i].checks;
    }
    CHECK(replace(23) == 17);
#ifndef DIRECT
    CHECK(dlclose(handle) == 0);
#endif
    printf("PASS linux_pic checks=%zu\n", checks);
}
