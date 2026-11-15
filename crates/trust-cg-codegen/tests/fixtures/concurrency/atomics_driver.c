/* Contended multi-thread controls for trust-cg AArch64 atomics.
 *
 * Author: Andrew Yates <andrewyates.name@gmail.com>
 * Copyright 2026 Andrew Yates | License: Apache-2.0
 *
 * Driven by crates/trust-cg-codegen/tests/e2e_aarch64_concurrency.rs, which
 * links it with one CG object and parses its stdout. Every workload runs
 * THREADS threads released together by a barrier, each doing ITERS
 * operations, once through the CG functions ("cg" lane) and once through the
 * compiler's own __atomic builtins ("c11" lane). Each result line is
 *
 *   <lane> <workload> w=<bits> ok=<0|1> final=<hex> [detail]
 *
 * The litmus lines report how many iterations observed a forbidden outcome.
 * They are testing evidence over a finite number of runs on one host, not a
 * memory-model proof. The relaxed lines only report their count: ARMv8
 * permits the weak outcome for the C relaxed controls (plain LDR/STR), whose
 * observations show the harness can see it; the CG relaxed-API lines use CG's
 * relaxed loads and stores, which it currently strengthens to LDAR/STLR.
 */
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define THREADS 8
#define ITERS 16384
#define NM ((uint64_t)THREADS * ITERS)
#define MP_ROUNDS (1u << 20)
#define SB_ROUNDS (1u << 18)
#define SB_RESYNC 256
#define MUTATION_ATTEMPTS 64
#define MUTATION_ITERS 200000

/* ---------------------------------------------------------------- barrier */

typedef struct {
    pthread_mutex_t mutex;
    pthread_cond_t cond;
    unsigned count, waiting, generation;
} barrier_t;

static void barrier_init(barrier_t *b, unsigned count) {
    pthread_mutex_init(&b->mutex, NULL);
    pthread_cond_init(&b->cond, NULL);
    b->count = count;
    b->waiting = 0;
    b->generation = 0;
}

static void barrier_wait(barrier_t *b) {
    pthread_mutex_lock(&b->mutex);
    unsigned generation = b->generation;
    if (++b->waiting == b->count) {
        b->waiting = 0;
        b->generation++;
        pthread_cond_broadcast(&b->cond);
    } else {
        while (generation == b->generation) pthread_cond_wait(&b->cond, &b->mutex);
    }
    pthread_mutex_unlock(&b->mutex);
}

/* -------------------------------------------------------------- CG externs */

#define CG_DECL(T, W)                                                         \
    extern T rmw_add_##W(T *, T);                                             \
    extern T rmw_sub_##W(T *, T);                                             \
    extern T rmw_and_##W(T *, T);                                             \
    extern T rmw_or_##W(T *, T);                                              \
    extern T rmw_xor_##W(T *, T);                                             \
    extern T rmw_xchg_##W(T *, T);                                            \
    extern T rmw_smax_##W(T *, T);                                            \
    extern T rmw_smin_##W(T *, T);                                            \
    extern T rmw_umax_##W(T *, T);                                            \
    extern T rmw_umin_##W(T *, T);                                            \
    extern T cas_##W(T *, T, T);
CG_DECL(int8_t, 8)
CG_DECL(int16_t, 16)
CG_DECL(int32_t, 32)
CG_DECL(int64_t, 64)
extern int64_t load_acquire_64(int64_t *);
extern void store_release_64(int64_t *, int64_t);
extern int64_t load_relaxed_64(int64_t *);
extern void store_relaxed_64(int64_t *, int64_t);
extern int64_t load_seqcst_64(int64_t *);
extern void store_seqcst_64(int64_t *, int64_t);
extern int64_t nonatomic_add_64(int64_t *, int64_t);

/* ------------------------------------------------------ width-generic view */

enum { OP_ADD, OP_SUB, OP_AND, OP_OR, OP_XOR, OP_XCHG, OP_SMAX, OP_SMIN, OP_UMAX, OP_UMIN, OPS };
static const char *const OP_NAMES[OPS] = {"add", "sub", "and", "or", "xor",
                                          "xchg", "smax", "smin", "umax", "umin"};

typedef uint64_t (*rmw_fn)(void *, uint64_t);
typedef uint64_t (*cas_fn)(void *, uint64_t, uint64_t);

#define CG_ADAPT(T, U, W, OP)                                                  \
    static uint64_t cg_##OP##_##W(void *p, uint64_t v) {                       \
        return (U)rmw_##OP##_##W((T *)p, (T)v);                                \
    }
#define CG_ADAPT_ALL(T, U, W)                                                  \
    CG_ADAPT(T, U, W, add) CG_ADAPT(T, U, W, sub) CG_ADAPT(T, U, W, and)      \
    CG_ADAPT(T, U, W, or) CG_ADAPT(T, U, W, xor) CG_ADAPT(T, U, W, xchg)      \
    CG_ADAPT(T, U, W, smax) CG_ADAPT(T, U, W, smin) CG_ADAPT(T, U, W, umax)   \
    CG_ADAPT(T, U, W, umin)                                                    \
    static uint64_t cg_cas_##W(void *p, uint64_t e, uint64_t d) {              \
        return (U)cas_##W((T *)p, (T)e, (T)d);                                 \
    }
CG_ADAPT_ALL(int8_t, uint8_t, 8)
CG_ADAPT_ALL(int16_t, uint16_t, 16)
CG_ADAPT_ALL(int32_t, uint32_t, 32)
CG_ADAPT_ALL(int64_t, uint64_t, 64)

#define C11_SIMPLE(T, U, W, OP, BUILTIN)                                       \
    static uint64_t c11_##OP##_##W(void *p, uint64_t v) {                      \
        return (U)BUILTIN((T *)p, (T)v, __ATOMIC_SEQ_CST);                     \
    }
#define C11_EXTREME(T, U, W, OP, CT, BETTER)                                   \
    static uint64_t c11_##OP##_##W(void *p, uint64_t v) {                      \
        T old = __atomic_load_n((T *)p, __ATOMIC_RELAXED);                     \
        for (;;) {                                                             \
            T next = BETTER((CT)old, (CT)(T)v) ? old : (T)v;                   \
            if (__atomic_compare_exchange_n((T *)p, &old, next, 0,             \
                                            __ATOMIC_SEQ_CST, __ATOMIC_RELAXED)) \
                return (U)old;                                                 \
        }                                                                      \
    }
#define GE(a, b) ((a) >= (b))
#define LE(a, b) ((a) <= (b))
#define C11_ALL(T, U, W)                                                       \
    C11_SIMPLE(T, U, W, add, __atomic_fetch_add)                               \
    C11_SIMPLE(T, U, W, sub, __atomic_fetch_sub)                               \
    C11_SIMPLE(T, U, W, and, __atomic_fetch_and)                               \
    C11_SIMPLE(T, U, W, or, __atomic_fetch_or)                                 \
    C11_SIMPLE(T, U, W, xor, __atomic_fetch_xor)                               \
    C11_SIMPLE(T, U, W, xchg, __atomic_exchange_n)                             \
    C11_EXTREME(T, U, W, smax, T, GE) C11_EXTREME(T, U, W, smin, T, LE)        \
    C11_EXTREME(T, U, W, umax, U, GE) C11_EXTREME(T, U, W, umin, U, LE)        \
    static uint64_t c11_cas_##W(void *p, uint64_t e, uint64_t d) {             \
        T expected = (T)e;                                                     \
        __atomic_compare_exchange_n((T *)p, &expected, (T)d, 0,                \
                                    __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);       \
        return (U)expected;                                                    \
    }
C11_ALL(int8_t, uint8_t, 8)
C11_ALL(int16_t, uint16_t, 16)
C11_ALL(int32_t, uint32_t, 32)
C11_ALL(int64_t, uint64_t, 64)

typedef struct {
    const char *lane;
    unsigned bits;
    rmw_fn rmw[OPS];
    cas_fn cas;
} ops_t;

#define OPS_ROW(LANE, W)                                                       \
    {#LANE, W,                                                                 \
     {LANE##_add_##W, LANE##_sub_##W, LANE##_and_##W, LANE##_or_##W,           \
      LANE##_xor_##W, LANE##_xchg_##W, LANE##_smax_##W, LANE##_smin_##W,       \
      LANE##_umax_##W, LANE##_umin_##W},                                       \
     LANE##_cas_##W}
static const ops_t LANES[] = {
    OPS_ROW(cg, 8), OPS_ROW(cg, 16), OPS_ROW(cg, 32), OPS_ROW(cg, 64),
    OPS_ROW(c11, 8), OPS_ROW(c11, 16), OPS_ROW(c11, 32), OPS_ROW(c11, 64),
};

static uint64_t mask_of(unsigned bits) { return bits == 64 ? ~0ull : (1ull << bits) - 1; }

static uint64_t load_cell(const void *p, unsigned bits) {
    switch (bits) {
    case 8: return *(const volatile uint8_t *)p;
    case 16: return *(const volatile uint16_t *)p;
    case 32: return *(const volatile uint32_t *)p;
    default: return *(const volatile uint64_t *)p;
    }
}

static void store_cell(void *p, unsigned bits, uint64_t v) {
    switch (bits) {
    case 8: *(volatile uint8_t *)p = (uint8_t)v; break;
    case 16: *(volatile uint16_t *)p = (uint16_t)v; break;
    case 32: *(volatile uint32_t *)p = (uint32_t)v; break;
    default: *(volatile uint64_t *)p = v; break;
    }
}

static int64_t sext(uint64_t v, unsigned bits) {
    if (bits == 64) return (int64_t)v;
    uint64_t sign = 1ull << (bits - 1);
    return (int64_t)((v ^ sign) - sign);
}

/* ---------------------------------------------------------- thread harness */

typedef struct job job_t;
typedef void (*body_fn)(job_t *);
struct job {
    const ops_t *ops;
    int op;
    unsigned thread;
    void *cell;
    uint64_t *olds;       /* ITERS entries */
    uint64_t violations;
    uint64_t failures;
    barrier_t *barrier;
    body_fn body;
};

static void *run_job(void *arg) {
    job_t *job = arg;
    barrier_wait(job->barrier);
    job->body(job);
    return NULL;
}

static uint64_t *OLDS;

/* Run `body` on THREADS threads; returns summed violations and failures. */
static void run_threads(const ops_t *ops, int op, void *cell, body_fn body,
                        uint64_t *violations, uint64_t *failures) {
    pthread_t threads[THREADS];
    job_t jobs[THREADS];
    barrier_t barrier;
    barrier_init(&barrier, THREADS);
    for (unsigned t = 0; t < THREADS; t++) {
        jobs[t] = (job_t){ops, op, t, cell, OLDS + (uint64_t)t * ITERS, 0, 0, &barrier, body};
        if (pthread_create(&threads[t], NULL, run_job, &jobs[t]) != 0) exit(80);
    }
    *violations = 0;
    *failures = 0;
    for (unsigned t = 0; t < THREADS; t++) {
        pthread_join(threads[t], NULL);
        *violations += jobs[t].violations;
        *failures += jobs[t].failures;
    }
}

static union {
    uint64_t words[THREADS + 2];
    unsigned char bytes[8 * (THREADS + 2)];
} CELLS;

static void report(const ops_t *ops, const char *workload, int ok, uint64_t final,
                   const char *detail) {
    printf("%s %s w=%u ok=%d final=%llx%s%s\n", ops->lane, workload, ops->bits, ok,
           (unsigned long long)final, detail[0] ? " " : "", detail);
}

/* ---------------------------------------------------------------- workloads */

/* add/sub 1: the old values are a fetch-and-add linearization, so each
 * residue of the counter appears exactly NM / min(NM, 2^w) times. */
static void body_count(job_t *job) {
    rmw_fn f = job->ops->rmw[job->op];
    for (unsigned i = 0; i < ITERS; i++) job->olds[i] = f(job->cell, 1);
}

static void workload_count(const ops_t *ops, int op) {
    uint64_t mask = mask_of(ops->bits), v, fails;
    memset(&CELLS, 0, sizeof CELLS);
    run_threads(ops, op, CELLS.words, body_count, &v, &fails);
    uint64_t span = ops->bits >= 32 ? NM : (mask + 1 < NM ? mask + 1 : NM);
    uint64_t per = NM / span;
    uint32_t *histogram = calloc(span, sizeof *histogram);
    if (!histogram) exit(81);
    int ok = 1;
    for (uint64_t k = 0; k < NM; k++) {
        uint64_t old = OLDS[k];
        uint64_t index = op == OP_ADD ? old : (0 - old) & mask;
        if (index >= span) { ok = 0; continue; }
        histogram[index]++;
    }
    for (uint64_t k = 0; k < span; k++) ok &= histogram[k] == per;
    free(histogram);
    uint64_t final = load_cell(CELLS.words, ops->bits);
    uint64_t want = (op == OP_ADD ? NM : 0 - NM) & mask;
    ok &= final == want;
    report(ops, OP_NAMES[op], ok, final, "");
}

/* Each thread increments its own adjacent cell of the same width: a wider
 * access than the cell would clobber a neighbor. */
static void body_adjacent(job_t *job) {
    rmw_fn f = job->ops->rmw[OP_ADD];
    unsigned char *cell = (unsigned char *)job->cell + job->thread * (job->ops->bits / 8);
    for (unsigned i = 0; i < ITERS; i++) f(cell, 1);
}

static void workload_adjacent(const ops_t *ops) {
    uint64_t v, fails;
    memset(&CELLS, 0, sizeof CELLS);
    run_threads(ops, OP_ADD, CELLS.words, body_adjacent, &v, &fails);
    int ok = 1;
    uint64_t want = ITERS & mask_of(ops->bits);
    for (unsigned t = 0; t < THREADS; t++)
        ok &= load_cell(CELLS.bytes + t * (ops->bits / 8), ops->bits) == want;
    for (unsigned b = THREADS * (ops->bits / 8); b < sizeof CELLS.bytes; b++) ok &= CELLS.bytes[b] == 0;
    report(ops, "adjacent", ok, want, "");
}

/* Thread t owns bit t: OR sets it (it must have been clear), AND clears it
 * (it must have been set). A lost update shows as a wrong own-bit state. */
static void body_or_and(job_t *job) {
    rmw_fn set = job->ops->rmw[OP_OR], clear = job->ops->rmw[OP_AND];
    uint64_t bit = 1ull << job->thread, mask = mask_of(job->ops->bits);
    for (unsigned i = 0; i < ITERS; i++) {
        if (set(job->cell, bit) & bit) job->violations++;
        if (!(clear(job->cell, ~bit & mask) & bit)) job->violations++;
    }
}

static void body_xor(job_t *job) {
    rmw_fn toggle = job->ops->rmw[OP_XOR];
    uint64_t bit = 1ull << job->thread;
    for (unsigned i = 0; i < ITERS; i++)
        if (((toggle(job->cell, bit) & bit) != 0) != (i & 1)) job->violations++;
}

static void workload_bits(const ops_t *ops, int op) {
    uint64_t violations, fails;
    memset(&CELLS, 0, sizeof CELLS);
    run_threads(ops, op, CELLS.words, op == OP_XOR ? body_xor : body_or_and, &violations, &fails);
    uint64_t final = load_cell(CELLS.words, ops->bits);
    char detail[64];
    snprintf(detail, sizeof detail, "violations=%llu", (unsigned long long)violations);
    report(ops, op == OP_XOR ? "xor" : "or_and", violations == 0 && final == 0, final, detail);
}

/* Each thread swaps its token (t + 1) in ITERS times; every token must come
 * back out exactly once per swap-in, except the one left in memory. */
static void body_xchg(job_t *job) {
    rmw_fn swap = job->ops->rmw[OP_XCHG];
    for (unsigned i = 0; i < ITERS; i++) job->olds[i] = swap(job->cell, job->thread + 1);
}

static void workload_xchg(const ops_t *ops) {
    uint64_t v, fails;
    memset(&CELLS, 0, sizeof CELLS);
    run_threads(ops, OP_XCHG, CELLS.words, body_xchg, &v, &fails);
    uint64_t counts[THREADS + 1] = {0};
    int ok = 1;
    for (uint64_t k = 0; k < NM; k++) {
        if (OLDS[k] > THREADS) { ok = 0; continue; }
        counts[OLDS[k]]++;
    }
    uint64_t final = load_cell(CELLS.words, ops->bits);
    ok &= final >= 1 && final <= THREADS && counts[0] == 1;
    for (uint64_t token = 1; token <= THREADS; token++)
        ok &= counts[token] + (final == token) == ITERS;
    report(ops, "xchg", ok, final, "");
}

/* max/min with per-thread monotone operands: memory moves monotonically,
 * so each thread's old values are monotone in that op's signedness and the
 * final value is the extreme operand. */
static uint64_t magnitude(uint64_t k, unsigned bits) {
    uint64_t mask = mask_of(bits), step = mask / (NM - 1);
    if (step == 0) step = 1;
    return k > mask / step ? mask : k * step;
}

static uint64_t extreme_operand(int op, uint64_t k, unsigned bits) {
    uint64_t mask = mask_of(bits), sign = bits == 64 ? 1ull << 63 : 1ull << (bits - 1);
    uint64_t u = magnitude(k, bits);
    switch (op) {
    case OP_UMAX: return u;
    case OP_UMIN: return mask - u;
    case OP_SMAX: return (sign + u) & mask;
    default: return (sign - 1 - u) & mask; /* OP_SMIN */
    }
}

static uint64_t extreme_initial(int op, unsigned bits) {
    uint64_t mask = mask_of(bits), sign = bits == 64 ? 1ull << 63 : 1ull << (bits - 1);
    switch (op) {
    case OP_UMAX: return 0;
    case OP_UMIN: return mask;
    case OP_SMAX: return sign;
    default: return sign - 1;
    }
}

/* <0, 0, >0 comparing a and b in the signedness of `op`. */
static int compare(int op, uint64_t a, uint64_t b, unsigned bits) {
    if (op == OP_SMAX || op == OP_SMIN) {
        int64_t x = sext(a, bits), y = sext(b, bits);
        return (x > y) - (x < y);
    }
    return (a > b) - (a < b);
}

static void body_extreme(job_t *job) {
    rmw_fn f = job->ops->rmw[job->op];
    unsigned bits = job->ops->bits;
    int grow = job->op == OP_SMAX || job->op == OP_UMAX;
    uint64_t previous = extreme_initial(job->op, bits);
    for (unsigned i = 0; i < ITERS; i++) {
        uint64_t operand = extreme_operand(job->op, (uint64_t)i * THREADS + job->thread, bits);
        uint64_t old = f(job->cell, operand);
        int order = compare(job->op, old, previous, bits);
        if (grow ? order < 0 : order > 0) job->violations++;
        previous = old;
    }
}

static void workload_extreme(const ops_t *ops, int op) {
    uint64_t violations, fails;
    memset(&CELLS, 0, sizeof CELLS);
    store_cell(CELLS.words, ops->bits, extreme_initial(op, ops->bits));
    run_threads(ops, op, CELLS.words, body_extreme, &violations, &fails);
    uint64_t final = load_cell(CELLS.words, ops->bits);
    uint64_t want = extreme_operand(op, NM - 1, ops->bits);
    char detail[64];
    snprintf(detail, sizeof detail, "violations=%llu", (unsigned long long)violations);
    report(ops, OP_NAMES[op], violations == 0 && final == want, final, detail);
}

/* A CAS loop counter: every success increments by one. */
static void body_cas(job_t *job) {
    cas_fn cas = job->ops->cas;
    uint64_t mask = mask_of(job->ops->bits), expected = 0;
    for (unsigned done = 0; done < ITERS;) {
        uint64_t old = cas(job->cell, expected, (expected + 1) & mask);
        if (old == expected) {
            done++;
            expected = (expected + 1) & mask;
        } else {
            job->failures++;
            expected = old;
        }
    }
}

static void workload_cas(const ops_t *ops) {
    uint64_t v, failures;
    memset(&CELLS, 0, sizeof CELLS);
    run_threads(ops, 0, CELLS.words, body_cas, &v, &failures);
    uint64_t final = load_cell(CELLS.words, ops->bits);
    char detail[64];
    snprintf(detail, sizeof detail, "failed_attempts=%llu", (unsigned long long)failures);
    report(ops, "cas_loop", final == (NM & mask_of(ops->bits)), final, detail);
}

/* ------------------------------------------------------------------ litmus */

/* A two-thread spin rendezvous that keeps the litmus threads within a few
 * rounds of each other without a kernel call. */
typedef struct {
    unsigned arrived;
    unsigned generation;
} spin_barrier_t;

static void spin_wait(spin_barrier_t *b) {
    unsigned generation = __atomic_load_n(&b->generation, __ATOMIC_ACQUIRE);
    if (__atomic_add_fetch(&b->arrived, 1, __ATOMIC_ACQ_REL) == 2) {
        __atomic_store_n(&b->arrived, 0, __ATOMIC_RELAXED);
        __atomic_store_n(&b->generation, generation + 1, __ATOMIC_RELEASE);
    } else {
        while (__atomic_load_n(&b->generation, __ATOMIC_ACQUIRE) == generation) {}
    }
}

typedef struct {
    int64_t (*load)(int64_t *);
    void (*store)(int64_t *, int64_t);
} access_t;

static int64_t c_load_relaxed(int64_t *p) { return __atomic_load_n(p, __ATOMIC_RELAXED); }
static void c_store_relaxed(int64_t *p, int64_t v) { __atomic_store_n(p, v, __ATOMIC_RELAXED); }

static int64_t MP_DATA, MP_FLAG;
static spin_barrier_t MP_START;

static void *mp_writer(void *arg) {
    const access_t *flag = arg;
    spin_wait(&MP_START);
    for (int64_t r = 1; r <= MP_ROUNDS; r++) {
        c_store_relaxed(&MP_DATA, r);
        flag->store(&MP_FLAG, r);
    }
    return NULL;
}

/* Message passing: data := r (a plain relaxed store) then flag := r; the
 * reader loads flag then data (a plain relaxed load). Observing data < flag
 * is forbidden when the flag store is a release and the flag load an
 * acquire (or both are seq-cst). */
static void litmus_mp(const char *lane, const char *name, const access_t *flag,
                      int assert_forbidden) {
    MP_DATA = 0;
    MP_FLAG = 0;
    memset(&MP_START, 0, sizeof MP_START);
    pthread_t writer;
    if (pthread_create(&writer, NULL, mp_writer, (void *)flag) != 0) exit(82);
    spin_wait(&MP_START);
    uint64_t reads = 0, forbidden = 0, backwards = 0;
    int64_t last = 0, seen;
    do {
        seen = flag->load(&MP_FLAG);
        int64_t data = c_load_relaxed(&MP_DATA);
        reads++;
        if (data < seen) forbidden++;
        if (seen < last) backwards++;
        last = seen;
    } while (seen != MP_ROUNDS);
    pthread_join(writer, NULL);
    printf("%s %s w=64 ok=%d final=%llx rounds=%u reads=%llu forbidden=%llu backwards=%llu\n",
           lane, name, assert_forbidden ? forbidden == 0 && backwards == 0 : 1,
           (unsigned long long)seen, MP_ROUNDS, (unsigned long long)reads,
           (unsigned long long)forbidden, (unsigned long long)backwards);
}

static int64_t SB_X, SB_Y;
static int64_t *SB_SEEN_Y, *SB_SEEN_X;
static spin_barrier_t SB_SYNC;

static void *sb_second(void *arg) {
    const access_t *ops = arg;
    for (int64_t r = 1; r <= SB_ROUNDS; r++) {
        if (r % SB_RESYNC == 1) spin_wait(&SB_SYNC);
        ops->store(&SB_Y, r);
        SB_SEEN_X[r] = ops->load(&SB_X);
    }
    return NULL;
}

/* Perpetual store buffering: round r runs x := r; a[r] := y  ||  y := r;
 * b[r] := x, with x and y only growing. Under sequential consistency
 * a[r] < r && b[r] < r is impossible: if thread 0's load precedes y := r in
 * the total order, thread 1's later load of x follows x := r. */
static void litmus_sb(const char *lane, const char *name, const access_t *ops,
                      int assert_forbidden) {
    SB_X = 0;
    SB_Y = 0;
    memset(&SB_SYNC, 0, sizeof SB_SYNC);
    SB_SEEN_Y = calloc(SB_ROUNDS + 1, sizeof *SB_SEEN_Y);
    SB_SEEN_X = calloc(SB_ROUNDS + 1, sizeof *SB_SEEN_X);
    if (!SB_SEEN_Y || !SB_SEEN_X) exit(86);
    pthread_t second;
    if (pthread_create(&second, NULL, sb_second, (void *)ops) != 0) exit(83);
    for (int64_t r = 1; r <= SB_ROUNDS; r++) {
        if (r % SB_RESYNC == 1) spin_wait(&SB_SYNC);
        ops->store(&SB_X, r);
        SB_SEEN_Y[r] = ops->load(&SB_Y);
    }
    pthread_join(second, NULL);
    uint64_t forbidden = 0;
    for (int64_t r = 1; r <= SB_ROUNDS; r++)
        forbidden += SB_SEEN_Y[r] < r && SB_SEEN_X[r] < r;
    free(SB_SEEN_Y);
    free(SB_SEEN_X);
    printf("%s %s w=64 ok=%d final=%llx rounds=%u forbidden=%llu\n", lane, name,
           assert_forbidden ? forbidden == 0 : 1, (unsigned long long)SB_ROUNDS, SB_ROUNDS,
           (unsigned long long)forbidden);
}

static int64_t LB_X, LB_Y;
static int64_t *LB_SEEN_X, *LB_SEEN_Y;
static spin_barrier_t LB_SYNC;

static void *lb_second(void *arg) {
    const access_t *ops = arg;
    for (int64_t r = 1; r <= SB_ROUNDS; r++) {
        if (r % SB_RESYNC == 1) spin_wait(&LB_SYNC);
        LB_SEEN_Y[r] = ops->load(&LB_Y);
        ops->store(&LB_X, r);
    }
    return NULL;
}

/* Perpetual load buffering: round r runs a[r] := x; y := r  ||  b[r] := y;
 * x := r. With acquire loads and release stores (or seq-cst), a[r] >= r &&
 * b[r] >= r is impossible: each load would have to read a store that its own
 * thread issues only after the other thread's load. */
static void litmus_lb(const char *lane, const char *name, const access_t *ops,
                      int assert_forbidden) {
    LB_X = 0;
    LB_Y = 0;
    memset(&LB_SYNC, 0, sizeof LB_SYNC);
    LB_SEEN_X = calloc(SB_ROUNDS + 1, sizeof *LB_SEEN_X);
    LB_SEEN_Y = calloc(SB_ROUNDS + 1, sizeof *LB_SEEN_Y);
    if (!LB_SEEN_X || !LB_SEEN_Y) exit(87);
    pthread_t second;
    if (pthread_create(&second, NULL, lb_second, (void *)ops) != 0) exit(88);
    for (int64_t r = 1; r <= SB_ROUNDS; r++) {
        if (r % SB_RESYNC == 1) spin_wait(&LB_SYNC);
        LB_SEEN_X[r] = ops->load(&LB_X);
        ops->store(&LB_Y, r);
    }
    pthread_join(second, NULL);
    uint64_t forbidden = 0;
    for (int64_t r = 1; r <= SB_ROUNDS; r++)
        forbidden += LB_SEEN_X[r] >= r && LB_SEEN_Y[r] >= r;
    free(LB_SEEN_X);
    free(LB_SEEN_Y);
    printf("%s %s w=64 ok=%d final=%llx rounds=%u forbidden=%llu\n", lane, name,
           assert_forbidden ? forbidden == 0 : 1, (unsigned long long)SB_ROUNDS, SB_ROUNDS,
           (unsigned long long)forbidden);
}

/* ---------------------------------------------------------------- spinlock */

static int64_t SPIN_LOCK;
/* volatile keeps every critical-section access a real memory access. */
static volatile uint64_t SPIN_COUNTER, SPIN_INSIDE;
static barrier_t SPIN_BARRIER;

/* A CG compare-exchange acquires the lock and a CG store-release frees it;
 * the critical section increments a plain counter and checks that no other
 * thread is inside. */
static void *spin_worker(void *arg) {
    uint64_t *violations = arg;
    barrier_wait(&SPIN_BARRIER);
    for (unsigned i = 0; i < ITERS; i++) {
        while (cas_64(&SPIN_LOCK, 0, 1) != 0) {}
        if (SPIN_INSIDE++ != 0) (*violations)++;
        SPIN_COUNTER++;
        SPIN_INSIDE--;
        store_release_64(&SPIN_LOCK, 0);
    }
    return NULL;
}

static void spinlock_control(void) {
    SPIN_LOCK = 0;
    SPIN_COUNTER = 0;
    SPIN_INSIDE = 0;
    barrier_init(&SPIN_BARRIER, THREADS);
    pthread_t threads[THREADS];
    uint64_t violations[THREADS] = {0};
    for (unsigned t = 0; t < THREADS; t++)
        if (pthread_create(&threads[t], NULL, spin_worker, &violations[t]) != 0) exit(89);
    uint64_t total = 0;
    for (unsigned t = 0; t < THREADS; t++) {
        pthread_join(threads[t], NULL);
        total += violations[t];
    }
    printf("cg spinlock w=64 ok=%d final=%llx violations=%llu\n",
           total == 0 && SPIN_COUNTER == NM && SPIN_LOCK == 0, (unsigned long long)SPIN_COUNTER,
           (unsigned long long)total);
}

/* --------------------------------------------------------- mutation control */

static int64_t MUTATION_COUNTER;
static barrier_t MUTATION_BARRIER;

static void *mutation_worker(void *arg) {
    (void)arg;
    barrier_wait(&MUTATION_BARRIER);
    for (unsigned i = 0; i < MUTATION_ITERS; i++) nonatomic_add_64(&MUTATION_COUNTER, 1);
    return NULL;
}

/* The same counter harness over a NON-atomic CG load/add/store must lose
 * updates, or the harness could not detect a broken RMW. */
static void mutation_control(void) {
    const uint64_t want = (uint64_t)THREADS * MUTATION_ITERS;
    uint64_t attempts = 0, lost = 0;
    while (attempts < MUTATION_ATTEMPTS && lost == 0) {
        attempts++;
        MUTATION_COUNTER = 0;
        barrier_init(&MUTATION_BARRIER, THREADS);
        pthread_t threads[THREADS];
        for (unsigned t = 0; t < THREADS; t++)
            if (pthread_create(&threads[t], NULL, mutation_worker, NULL) != 0) exit(84);
        for (unsigned t = 0; t < THREADS; t++) pthread_join(threads[t], NULL);
        lost = want - (uint64_t)MUTATION_COUNTER;
    }
    printf("cg nonatomic_mutation w=64 ok=%d final=%llx attempts=%llu lost=%llu\n", lost != 0,
           (unsigned long long)(want - lost), (unsigned long long)attempts,
           (unsigned long long)lost);
}

int main(void) {
    OLDS = calloc(NM, sizeof *OLDS);
    if (!OLDS) return 85;
    for (size_t lane = 0; lane < sizeof LANES / sizeof LANES[0]; lane++) {
        const ops_t *ops = &LANES[lane];
        workload_count(ops, OP_ADD);
        workload_count(ops, OP_SUB);
        workload_adjacent(ops);
        workload_bits(ops, OP_OR);
        workload_bits(ops, OP_XOR);
        workload_xchg(ops);
        workload_extreme(ops, OP_SMAX);
        workload_extreme(ops, OP_SMIN);
        workload_extreme(ops, OP_UMAX);
        workload_extreme(ops, OP_UMIN);
        workload_cas(ops);
    }
    static const access_t cg_acquire_release = {load_acquire_64, store_release_64};
    static const access_t cg_seqcst = {load_seqcst_64, store_seqcst_64};
    static const access_t cg_relaxed = {load_relaxed_64, store_relaxed_64};
    static const access_t c_relaxed = {c_load_relaxed, c_store_relaxed};
    litmus_mp("cg", "mp_release_acquire", &cg_acquire_release, 1);
    litmus_mp("cg", "mp_seqcst", &cg_seqcst, 1);
    litmus_mp("cg", "mp_relaxed_api", &cg_relaxed, 0);
    litmus_mp("c11", "mp_relaxed_control", &c_relaxed, 0);
    litmus_sb("cg", "sb_seqcst", &cg_seqcst, 1);
    litmus_sb("cg", "sb_relaxed_api", &cg_relaxed, 0);
    litmus_sb("c11", "sb_relaxed_control", &c_relaxed, 0);
    litmus_lb("cg", "lb_release_acquire", &cg_acquire_release, 1);
    litmus_lb("cg", "lb_seqcst", &cg_seqcst, 1);
    litmus_lb("c11", "lb_relaxed_control", &c_relaxed, 0);
    spinlock_control();
    mutation_control();
    free(OLDS);
    printf("done\n");
    return 0;
}
