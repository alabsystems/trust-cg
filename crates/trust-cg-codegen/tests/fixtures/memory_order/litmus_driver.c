/* Native litmus harness for trust-cg's AArch64 memory-order mapping (L03-P3).
 *
 * Author: Andrew Yates <andrewyates.name@gmail.com>
 * Copyright 2026 Andrew Yates | License: Apache-2.0
 *
 * Driven by crates/trust-cg-codegen/tests/e2e_aarch64_memory_order_litmus.rs,
 * which links it with trust-cg objects whose functions are WHOLE litmus thread
 * bodies (every access and fence of one thread's round, compiled by trust-cg),
 * and parses its stdout. Each result line is
 *
 *   <shape> <variant> lane=<cg|c> expect=<forbidden|allowed|control>
 *       rounds=<n> forbidden=<k> o00=<n> o01=<n> o10=<n> o11=<n>
 *
 * `forbidden` counts rounds that showed the outcome the C11/Rust model
 * forbids for the variant's orderings. `expect=forbidden` lines must report
 * zero; `allowed` lines are orderings under which C11 permits the outcome
 * (reported, never asserted); `control` lines are the C compiler's plain
 * accesses or hand-written replicas of the PRE-L03-P3 selections (inline
 * assembly), which show whether this host produces the weak outcome at all.
 * The `oXY` histogram classifies every round by its two observations (shape
 * specific, see each harness). Testing evidence over finite runs on one
 * host, not a memory-model proof.
 */
#include <pthread.h>
#include <sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MP_ROUNDS (1u << 18)
#define SB_ROUNDS (1u << 18)
#define IRIW_ROUNDS (1u << 16)
#define W2_ROUNDS (1u << 16)
#define RESYNC 256

/* ------------------------------------------------------------ rendezvous */

typedef struct {
    unsigned arrived;
    unsigned generation;
} spin_t;

/* An N-party spin rendezvous that keeps the litmus threads within RESYNC
 * rounds of each other without a kernel call; it yields after a long spin so
 * an oversubscribed host still makes progress. */
static void spin_wait(spin_t *b, unsigned parties) {
    unsigned generation = __atomic_load_n(&b->generation, __ATOMIC_ACQUIRE);
    if (__atomic_add_fetch(&b->arrived, 1, __ATOMIC_ACQ_REL) == parties) {
        __atomic_store_n(&b->arrived, 0, __ATOMIC_RELAXED);
        __atomic_store_n(&b->generation, generation + 1, __ATOMIC_RELEASE);
    } else {
        unsigned spins = 0;
        while (__atomic_load_n(&b->generation, __ATOMIC_ACQUIRE) == generation) {
            if (++spins == 1u << 14) {
                spins = 0;
                sched_yield();
            }
        }
    }
}

static void *xcalloc(size_t n, size_t size) {
    void *p = calloc(n, size);
    if (!p) exit(90);
    return p;
}

/* Two shared 16-byte slots on separate cache lines (128-byte lines on Apple
 * cores). The 64-bit variants use the low half; the 128-bit ones the whole
 * slot. */
typedef struct {
    _Alignas(128) int64_t slot[2];
} line_t;
static line_t X, Y;

static void reset(void) {
    memset(&X, 0, sizeof X);
    memset(&Y, 0, sizeof Y);
}

static void report(const char *shape, const char *variant, const char *lane,
                   const char *expect, unsigned rounds, uint64_t forbidden,
                   const uint64_t o[4]) {
    printf("%s %s lane=%s expect=%s rounds=%u forbidden=%llu o00=%llu o01=%llu o10=%llu "
           "o11=%llu\n",
           shape, variant, lane, expect, rounds, (unsigned long long)forbidden,
           (unsigned long long)o[0], (unsigned long long)o[1], (unsigned long long)o[2],
           (unsigned long long)o[3]);
    fflush(stdout);
}

/* ---------------------------------------------------- CG thread bodies */

/* Message passing: writer `data := r (plain); [order]; flag := r`, reader
 * `f := flag; [order]; *out := data (plain)`, returns f. */
typedef void (*mp_w_t)(int64_t *data, void *flag, int64_t r);
typedef int64_t (*mp_r_t)(void *flag, int64_t *data, int64_t *out);
/* Store buffering: `mine := r; [order]; return other`. */
typedef int64_t (*sb_t)(void *mine, void *other, int64_t r);
/* Load buffering: `v := read_from; [order]; write_to := r; return v`. */
typedef int64_t (*lb_t)(void *read_from, void *write_to, int64_t r);
/* IRIW: writer `p := r`; reader `a := first; [order]; *out := second`. */
typedef void (*iw_t)(void *p, int64_t r);
typedef int64_t (*ir_t)(void *first, void *second, int64_t *out);
/* 2+2W: `first := 1; [order]; second := 2`. */
typedef void (*w2_t)(void *first, void *second);

#define MP(name) \
    extern void mp_##name##_w(int64_t *, void *, int64_t); \
    extern int64_t mp_##name##_r(void *, int64_t *, int64_t *);
MP(relacq)
MP(seqcst)
MP(fence)
MP(fence_acqrel)
MP(fence_seqcst)
MP(rmw)
MP(cas)
MP(wide)
MP(relaxed)
MP(llsc)
extern int64_t sb_seqcst(void *, void *, int64_t);
extern int64_t sb_fence_seqcst(void *, void *, int64_t);
extern int64_t sb_rmw_seqcst(void *, void *, int64_t);
extern int64_t sb_cas_seqcst(void *, void *, int64_t);
extern int64_t sb_wide_seqcst(void *, void *, int64_t);
extern int64_t sb_mixed_narrow(void *, void *, int64_t);
extern int64_t sb_mixed_wide(void *, void *, int64_t);
extern int64_t sb_llsc_seqcst(void *, void *, int64_t);
extern int64_t sb_relacq(void *, void *, int64_t);
extern int64_t sb_fence_release(void *, void *, int64_t);
extern int64_t sb_fence_acqrel(void *, void *, int64_t);
extern int64_t lb_fence_release(void *, void *, int64_t);
extern int64_t lb_fence_acquire(void *, void *, int64_t);
extern int64_t lb_relacq(void *, void *, int64_t);
extern int64_t lb_seqcst(void *, void *, int64_t);
extern int64_t lb_rmw(void *, void *, int64_t);
extern int64_t lb_llsc(void *, void *, int64_t);
extern void iriw_seqcst_w(void *, int64_t);
extern int64_t iriw_seqcst_r(void *, void *, int64_t *);
extern void iriw_fence_w(void *, int64_t);
extern int64_t iriw_fence_r(void *, void *, int64_t *);
extern void iriw_acquire_w(void *, int64_t);
extern int64_t iriw_acquire_r(void *, void *, int64_t *);
extern void w2_seqcst(void *, void *);
extern void w2_fence_seqcst(void *, void *);
extern void w2_release(void *, void *);
extern void w2_fence_release(void *, void *);

/* ------------------------------------------------------- C controls */

static void c_mp_w(int64_t *data, void *flag, int64_t r) {
    __asm__ volatile("str %0, [%1]\n\tstr %0, [%2]" ::"r"(r), "r"(data), "r"(flag) : "memory");
}
static int64_t c_mp_r(void *flag, int64_t *data, int64_t *out) {
    int64_t f, d;
    __asm__ volatile("ldr %0, [%2]\n\tldr %1, [%3]"
                     : "=&r"(f), "=&r"(d)
                     : "r"(flag), "r"(data)
                     : "memory");
    *out = d;
    return f;
}
static int64_t c_sb_plain(void *mine, void *other, int64_t r) {
    int64_t v;
    __asm__ volatile("str %1, [%2]\n\tldr %0, [%3]"
                     : "=&r"(v)
                     : "r"(r), "r"(mine), "r"(other)
                     : "memory");
    return v;
}
/* The PRE-L03-P3 release fence between a store and a load. */
static int64_t c_sb_ishst(void *mine, void *other, int64_t r) {
    int64_t v;
    __asm__ volatile("str %1, [%2]\n\tdmb ishst\n\tldr %0, [%3]"
                     : "=&r"(v)
                     : "r"(r), "r"(mine), "r"(other)
                     : "memory");
    return v;
}
/* The PRE-L03-P3 SeqCst 128-bit pair: the LDAXP/STLXP store loop, then the
 * `ldp; dmb ish` load without its leading barrier. */
static int64_t c_sb_old_wide(void *mine, void *other, int64_t r) {
    int64_t lo, hi, old_lo, old_hi;
    uint32_t status;
    __asm__ volatile("1: ldaxp %0, %1, [%3]\n\t"
                     "stlxp %w2, %4, xzr, [%3]\n\t"
                     "cbnz %w2, 1b"
                     : "=&r"(old_lo), "=&r"(old_hi), "=&r"(status)
                     : "r"(mine), "r"(r)
                     : "memory");
    __asm__ volatile("ldp %0, %1, [%2]\n\tdmb ish" : "=&r"(lo), "=&r"(hi) : "r"(other) : "memory");
    (void)hi;
    return lo;
}
static int64_t c_lb_plain(void *read_from, void *write_to, int64_t r) {
    int64_t v;
    __asm__ volatile("ldr %0, [%2]\n\tstr %1, [%3]"
                     : "=&r"(v)
                     : "r"(r), "r"(read_from), "r"(write_to)
                     : "memory");
    return v;
}
/* The PRE-L03-P3 release fence after a load, and its acquire partner. */
static int64_t c_lb_ishst(void *read_from, void *write_to, int64_t r) {
    int64_t v;
    __asm__ volatile("ldr %0, [%2]\n\tdmb ishst\n\tstr %1, [%3]"
                     : "=&r"(v)
                     : "r"(r), "r"(read_from), "r"(write_to)
                     : "memory");
    return v;
}
static int64_t c_lb_ishld(void *read_from, void *write_to, int64_t r) {
    int64_t v;
    __asm__ volatile("ldr %0, [%2]\n\tdmb ishld\n\tstr %1, [%3]"
                     : "=&r"(v)
                     : "r"(r), "r"(read_from), "r"(write_to)
                     : "memory");
    return v;
}
static void c_iriw_w(void *p, int64_t r) {
    __asm__ volatile("str %0, [%1]" ::"r"(r), "r"(p) : "memory");
}
static int64_t c_iriw_r(void *first, void *second, int64_t *out) {
    int64_t a, b;
    __asm__ volatile("ldr %0, [%2]\n\tldr %1, [%3]"
                     : "=&r"(a), "=&r"(b)
                     : "r"(first), "r"(second)
                     : "memory");
    *out = b;
    return a;
}
static void c_w2(void *first, void *second) {
    __asm__ volatile("str %0, [%2]\n\tstr %1, [%3]" ::"r"((int64_t)1), "r"((int64_t)2),
                     "r"(first), "r"(second)
                     : "memory");
}

/* ------------------------------------------------- message passing */

static spin_t MP_SYNC;
static mp_w_t MP_W;

static void *mp_writer(void *arg) {
    (void)arg;
    for (int64_t r = 1; r <= MP_ROUNDS; r++) {
        if (r % RESYNC == 1) spin_wait(&MP_SYNC, 2);
        MP_W(X.slot, Y.slot, r);
    }
    return NULL;
}

/* Perpetual MP: in round r the writer stores data := r then flag := r; the
 * reader, rendezvousing with the writer every RESYNC rounds so the two always
 * overlap, loads flag then data once per round. Observing data < flag is
 * forbidden when the flag write releases (store-release, release RMW/CAS, or
 * a release fence before it) and the flag read acquires. o00 = flag 0,
 * o01 = data > flag, o10 = forbidden (data < flag), o11 = data == flag. */
static void litmus_mp(const char *variant, const char *lane, const char *expect, mp_w_t w,
                      mp_r_t r) {
    reset();
    memset(&MP_SYNC, 0, sizeof MP_SYNC);
    MP_W = w;
    pthread_t writer;
    if (pthread_create(&writer, NULL, mp_writer, NULL) != 0) exit(81);
    uint64_t o[4] = {0, 0, 0, 0}, forbidden = 0;
    for (int64_t k = 1; k <= MP_ROUNDS; k++) {
        if (k % RESYNC == 1) spin_wait(&MP_SYNC, 2);
        int64_t data;
        int64_t seen = r(Y.slot, X.slot, &data);
        if (seen == 0) o[0]++;
        else if (data > seen) o[1]++;
        else if (data < seen) {
            o[2]++;
            forbidden++;
        } else o[3]++;
    }
    pthread_join(writer, NULL);
    report("mp", variant, lane, expect, MP_ROUNDS, forbidden, o);
}

/* -------------------------------------------------- store buffering */

static spin_t SB_SYNC;
static sb_t SB_SECOND;
static int64_t *SB_SEEN_X;

static void *sb_second(void *arg) {
    (void)arg;
    for (int64_t r = 1; r <= SB_ROUNDS; r++) {
        if (r % RESYNC == 1) spin_wait(&SB_SYNC, 2);
        SB_SEEN_X[r] = SB_SECOND(Y.slot, X.slot, r);
    }
    return NULL;
}

/* Perpetual SB: round r runs x := r; a := y || y := r; b := x. Under SeqCst
 * a < r && b < r is impossible. oXY: X = a saw round r, Y = b saw it. */
static void litmus_sb(const char *variant, const char *lane, const char *expect, sb_t first,
                      sb_t second) {
    reset();
    memset(&SB_SYNC, 0, sizeof SB_SYNC);
    SB_SECOND = second;
    int64_t *seen_y = xcalloc(SB_ROUNDS + 1, sizeof *seen_y);
    SB_SEEN_X = xcalloc(SB_ROUNDS + 1, sizeof *SB_SEEN_X);
    pthread_t thread;
    if (pthread_create(&thread, NULL, sb_second, NULL) != 0) exit(82);
    for (int64_t r = 1; r <= SB_ROUNDS; r++) {
        if (r % RESYNC == 1) spin_wait(&SB_SYNC, 2);
        seen_y[r] = first(X.slot, Y.slot, r);
    }
    pthread_join(thread, NULL);
    uint64_t o[4] = {0, 0, 0, 0}, forbidden = 0;
    for (int64_t r = 1; r <= SB_ROUNDS; r++) {
        int a = seen_y[r] >= r, b = SB_SEEN_X[r] >= r;
        o[a * 2 + b]++;
        forbidden += !a && !b;
    }
    free(seen_y);
    free(SB_SEEN_X);
    report("sb", variant, lane, expect, SB_ROUNDS, forbidden, o);
}

/* --------------------------------------------------- load buffering */

static spin_t LB_SYNC;
static lb_t LB_SECOND;
static int64_t *LB_SEEN_Y;

static void *lb_second(void *arg) {
    (void)arg;
    for (int64_t r = 1; r <= SB_ROUNDS; r++) {
        if (r % RESYNC == 1) spin_wait(&LB_SYNC, 2);
        LB_SEEN_Y[r] = LB_SECOND(Y.slot, X.slot, r);
    }
    return NULL;
}

/* Perpetual LB: round r runs a := x; y := r || b := y; x := r. With the
 * reads ordered before the writes by release/acquire (or SeqCst, or a
 * release fence on one side and an acquire fence on the other),
 * a >= r && b >= r is impossible. oXY: X = a saw round r, Y = b saw it. */
static void litmus_lb(const char *variant, const char *lane, const char *expect, lb_t first,
                      lb_t second) {
    reset();
    memset(&LB_SYNC, 0, sizeof LB_SYNC);
    LB_SECOND = second;
    int64_t *seen_x = xcalloc(SB_ROUNDS + 1, sizeof *seen_x);
    LB_SEEN_Y = xcalloc(SB_ROUNDS + 1, sizeof *LB_SEEN_Y);
    pthread_t thread;
    if (pthread_create(&thread, NULL, lb_second, NULL) != 0) exit(83);
    for (int64_t r = 1; r <= SB_ROUNDS; r++) {
        if (r % RESYNC == 1) spin_wait(&LB_SYNC, 2);
        seen_x[r] = first(X.slot, Y.slot, r);
    }
    pthread_join(thread, NULL);
    uint64_t o[4] = {0, 0, 0, 0}, forbidden = 0;
    for (int64_t r = 1; r <= SB_ROUNDS; r++) {
        int a = seen_x[r] >= r, b = LB_SEEN_Y[r] >= r;
        o[a * 2 + b]++;
        forbidden += a && b;
    }
    free(seen_x);
    free(LB_SEEN_Y);
    report("lb", variant, lane, expect, SB_ROUNDS, forbidden, o);
}

/* --------------------------------------------------------------- IRIW */

static spin_t IRIW_SYNC;
typedef struct {
    int role;
    iw_t w;
    ir_t r;
    int64_t *out;
} iriw_job_t;

static void *iriw_thread(void *arg) {
    iriw_job_t *job = arg;
    for (int64_t k = 1; k <= IRIW_ROUNDS; k++) {
        if (k % RESYNC == 1) spin_wait(&IRIW_SYNC, 4);
        switch (job->role) {
        case 0: job->w(X.slot, k); break;
        case 1: job->w(Y.slot, k); break;
        case 2: job->out[2 * k] = job->r(X.slot, Y.slot, &job->out[2 * k + 1]); break;
        default: job->out[2 * k] = job->r(Y.slot, X.slot, &job->out[2 * k + 1]); break;
        }
    }
    return NULL;
}

/* Perpetual IRIW: two writers store k to x and to y; reader 0 reads x then
 * y, reader 1 reads y then x. For reader rounds k of each, a total order of
 * the four reads forbids "reader 0 saw a newer x than reader 1 AND reader 1
 * saw a newer y than reader 0": a > d && c > b. o00 counts rounds where
 * neither reader saw a newer value than the other, o01/o10 one of them,
 * o11 the forbidden shape. */
static void litmus_iriw(const char *variant, const char *lane, const char *expect, iw_t w,
                        ir_t r) {
    reset();
    memset(&IRIW_SYNC, 0, sizeof IRIW_SYNC);
    int64_t *out0 = xcalloc(2 * (IRIW_ROUNDS + 1), sizeof *out0);
    int64_t *out1 = xcalloc(2 * (IRIW_ROUNDS + 1), sizeof *out1);
    iriw_job_t jobs[4] = {{0, w, r, NULL}, {1, w, r, NULL}, {2, w, r, out0}, {3, w, r, out1}};
    pthread_t threads[4];
    for (int t = 0; t < 4; t++)
        if (pthread_create(&threads[t], NULL, iriw_thread, &jobs[t]) != 0) exit(84);
    for (int t = 0; t < 4; t++) pthread_join(threads[t], NULL);
    uint64_t o[4] = {0, 0, 0, 0}, forbidden = 0;
    for (int64_t k = 1; k <= IRIW_ROUNDS; k++) {
        int64_t a = out0[2 * k], b = out0[2 * k + 1];
        int64_t c = out1[2 * k], d = out1[2 * k + 1];
        int x_newer = a > d, y_newer = c > b;
        o[x_newer * 2 + y_newer]++;
        forbidden += x_newer && y_newer;
    }
    free(out0);
    free(out1);
    report("iriw", variant, lane, expect, IRIW_ROUNDS, forbidden, o);
}

/* --------------------------------------------------------------- 2+2W */

static spin_t W2_SYNC;
static w2_t W2_SECOND;
static int64_t *W2_X, *W2_Y;

static void *w2_second(void *arg) {
    (void)arg;
    for (int64_t r = 0; r < W2_ROUNDS; r++) {
        if (r % RESYNC == 0) spin_wait(&W2_SYNC, 2);
        W2_SECOND(&W2_Y[r * 16], &W2_X[r * 16]);
    }
    return NULL;
}

/* 2+2W over fresh locations per round (one 128-byte line each): thread 0
 * runs x := 1; y := 2, thread 1 runs y := 1; x := 2. Final x == 1 && y == 1
 * is forbidden under SeqCst (and by SeqCst fences between the stores).
 * oXY: X = final x is 2, Y = final y is 2 (o00 is the forbidden shape). */
static void litmus_w2(const char *variant, const char *lane, const char *expect, w2_t f) {
    memset(&W2_SYNC, 0, sizeof W2_SYNC);
    W2_SECOND = f;
    W2_X = xcalloc((size_t)W2_ROUNDS * 16, sizeof *W2_X);
    W2_Y = xcalloc((size_t)W2_ROUNDS * 16, sizeof *W2_Y);
    pthread_t thread;
    if (pthread_create(&thread, NULL, w2_second, NULL) != 0) exit(85);
    for (int64_t r = 0; r < W2_ROUNDS; r++) {
        if (r % RESYNC == 0) spin_wait(&W2_SYNC, 2);
        f(&W2_X[r * 16], &W2_Y[r * 16]);
    }
    pthread_join(thread, NULL);
    uint64_t o[4] = {0, 0, 0, 0}, forbidden = 0, bad = 0;
    for (int64_t r = 0; r < W2_ROUNDS; r++) {
        int64_t x = W2_X[r * 16], y = W2_Y[r * 16];
        if ((x != 1 && x != 2) || (y != 1 && y != 2)) bad++;
        int x2 = x == 2, y2 = y == 2;
        o[x2 * 2 + y2]++;
        forbidden += x == 1 && y == 1;
    }
    free(W2_X);
    free(W2_Y);
    if (bad) exit(86);
    report("2+2w", variant, lane, expect, W2_ROUNDS, forbidden, o);
}

int main(void) {
    litmus_mp("relacq", "cg", "forbidden", mp_relacq_w, mp_relacq_r);
    litmus_mp("seqcst", "cg", "forbidden", mp_seqcst_w, mp_seqcst_r);
    litmus_mp("fence_release_acquire", "cg", "forbidden", mp_fence_w, mp_fence_r);
    litmus_mp("fence_acqrel", "cg", "forbidden", mp_fence_acqrel_w, mp_fence_acqrel_r);
    litmus_mp("fence_seqcst", "cg", "forbidden", mp_fence_seqcst_w, mp_fence_seqcst_r);
    litmus_mp("rmw_release_acquire", "cg", "forbidden", mp_rmw_w, mp_rmw_r);
    litmus_mp("cas_release_failure_acquire", "cg", "forbidden", mp_cas_w, mp_cas_r);
    litmus_mp("wide_release_acquire", "cg", "forbidden", mp_wide_w, mp_wide_r);
    litmus_mp("llsc_release_acquire", "cg", "forbidden", mp_llsc_w, mp_llsc_r);
    litmus_mp("relaxed_api", "cg", "allowed", mp_relaxed_w, mp_relaxed_r);
    litmus_mp("plain", "c", "control", c_mp_w, c_mp_r);

    litmus_sb("seqcst", "cg", "forbidden", sb_seqcst, sb_seqcst);
    litmus_sb("fence_seqcst", "cg", "forbidden", sb_fence_seqcst, sb_fence_seqcst);
    litmus_sb("rmw_seqcst", "cg", "forbidden", sb_rmw_seqcst, sb_rmw_seqcst);
    litmus_sb("cas_seqcst", "cg", "forbidden", sb_cas_seqcst, sb_cas_seqcst);
    litmus_sb("wide_seqcst", "cg", "forbidden", sb_wide_seqcst, sb_wide_seqcst);
    litmus_sb("mixed_seqcst", "cg", "forbidden", sb_mixed_narrow, sb_mixed_wide);
    litmus_sb("llsc_seqcst", "cg", "forbidden", sb_llsc_seqcst, sb_llsc_seqcst);
    litmus_sb("relacq", "cg", "allowed", sb_relacq, sb_relacq);
    litmus_sb("fence_release", "cg", "allowed", sb_fence_release, sb_fence_release);
    litmus_sb("fence_acqrel", "cg", "allowed", sb_fence_acqrel, sb_fence_acqrel);
    litmus_sb("plain", "c", "control", c_sb_plain, c_sb_plain);
    litmus_sb("old_release_fence_ishst", "c", "control", c_sb_ishst, c_sb_ishst);
    litmus_sb("old_wide_seqcst", "c", "control", c_sb_old_wide, c_sb_old_wide);

    litmus_lb("fence_release_acquire", "cg", "forbidden", lb_fence_release, lb_fence_acquire);
    litmus_lb("relacq", "cg", "forbidden", lb_relacq, lb_relacq);
    litmus_lb("seqcst", "cg", "forbidden", lb_seqcst, lb_seqcst);
    litmus_lb("rmw_acquire_release", "cg", "forbidden", lb_rmw, lb_rmw);
    litmus_lb("llsc_acquire_release", "cg", "forbidden", lb_llsc, lb_llsc);
    litmus_lb("plain", "c", "control", c_lb_plain, c_lb_plain);
    litmus_lb("old_release_fence_ishst", "c", "control", c_lb_ishst, c_lb_ishld);

    litmus_iriw("seqcst", "cg", "forbidden", iriw_seqcst_w, iriw_seqcst_r);
    litmus_iriw("fence_seqcst", "cg", "forbidden", iriw_fence_w, iriw_fence_r);
    litmus_iriw("acquire", "cg", "allowed", iriw_acquire_w, iriw_acquire_r);
    litmus_iriw("plain", "c", "control", c_iriw_w, c_iriw_r);

    litmus_w2("seqcst", "cg", "forbidden", w2_seqcst);
    litmus_w2("fence_seqcst", "cg", "forbidden", w2_fence_seqcst);
    litmus_w2("release", "cg", "allowed", w2_release);
    litmus_w2("fence_release", "cg", "allowed", w2_fence_release);
    litmus_w2("plain", "c", "control", c_w2);
    printf("done\n");
    return 0;
}
