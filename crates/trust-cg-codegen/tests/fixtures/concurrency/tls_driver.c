/* Multi-thread thread-local initialization and identity controls for
 * trust-cg AArch64 TLS (Darwin TLV descriptors, ELF local-exec).
 *
 * Author: Andrew Yates <andrewyates.name@gmail.com>
 * Copyright 2026 Andrew Yates | License: Apache-2.0
 *
 * Driven by crates/trust-cg-codegen/tests/e2e_aarch64_concurrency.rs. The CG
 * object defines `cg_tls` (initial value TLS_INIT) and zero-initialized
 * `cg_tls_zero`, and exports their per-thread addresses and a bump. WAVES
 * waves of THREADS threads run after the main thread has mutated its own
 * copy; each wave's threads must see fresh initial values (also after an
 * earlier wave's threads mutated theirs and exited), agree with this C
 * translation unit's own view of the same thread-locals, keep distinct
 * stable addresses while all are alive, and never observe another thread's
 * bumps. One line per wave:
 *
 *   tls wave=<n> ok=<0|1> init=<n> zero=<n> c_view=<n> distinct=<0|1>
 *       isolated=<n> final=<n>
 */
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>

#define THREADS 8
#define WAVES 3
#define ROUNDS 4096
#define TLS_INIT 24301

extern __thread int64_t cg_tls;
extern __thread int64_t cg_tls_zero;
extern int64_t *cg_tls_addr(void);
extern int64_t *cg_tls_zero_addr(void);
extern int64_t cg_tls_bump(int64_t);

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

typedef struct {
    unsigned index;
    int64_t delta;
    int64_t *addr, *zero_addr;
    int64_t init, zero, halfway, final;
    int c_view, stable;
    unsigned isolated;
} slot_t;

static barrier_t BARRIER;
static slot_t SLOTS[THREADS];

static void *worker(void *arg) {
    slot_t *s = arg;
    s->addr = cg_tls_addr();
    s->zero_addr = cg_tls_zero_addr();
    s->init = *s->addr;
    s->zero = *s->zero_addr;
    s->c_view = s->addr == &cg_tls && s->zero_addr == &cg_tls_zero && cg_tls == s->init;
    barrier_wait(&BARRIER); /* every thread initialized, none mutated yet */
    for (unsigned r = 0; r < ROUNDS / 2; r++) cg_tls_bump(s->delta);
    cg_tls_zero += s->delta; /* through the C view */
    s->halfway = *cg_tls_addr();
    barrier_wait(&BARRIER); /* every thread published its halfway value */
    s->isolated = 0;
    for (unsigned t = 0; t < THREADS; t++) {
        const slot_t *other = &SLOTS[t];
        s->isolated += other->halfway == TLS_INIT + other->delta * (ROUNDS / 2);
    }
    for (unsigned r = ROUNDS / 2; r < ROUNDS; r++) cg_tls_bump(s->delta);
    s->final = *cg_tls_addr();
    s->stable = cg_tls_addr() == s->addr && *cg_tls_zero_addr() == s->delta;
    barrier_wait(&BARRIER); /* all alive until every thread finished */
    return NULL;
}

int main(void) {
    int64_t main_init = *cg_tls_addr();
    cg_tls_bump(1000);
    int64_t *main_addr = cg_tls_addr();
    int failures = 0;
    for (unsigned wave = 0; wave < WAVES; wave++) {
        barrier_init(&BARRIER, THREADS);
        pthread_t threads[THREADS];
        for (unsigned t = 0; t < THREADS; t++) {
            SLOTS[t] = (slot_t){.index = t, .delta = (int64_t)(wave * THREADS + t + 1)};
            if (pthread_create(&threads[t], NULL, worker, &SLOTS[t]) != 0) return 80;
        }
        for (unsigned t = 0; t < THREADS; t++) pthread_join(threads[t], NULL);
        unsigned init = 0, zero = 0, c_view = 0, isolated = 0, final = 0, distinct = 1;
        for (unsigned t = 0; t < THREADS; t++) {
            const slot_t *s = &SLOTS[t];
            init += s->init == TLS_INIT;
            zero += s->zero == 0;
            c_view += s->c_view;
            isolated += s->isolated == THREADS;
            final += s->final == TLS_INIT + s->delta * ROUNDS && s->stable;
            distinct &= s->addr != main_addr && s->addr != s->zero_addr;
            for (unsigned u = 0; u < t; u++)
                distinct &= SLOTS[u].addr != s->addr && SLOTS[u].zero_addr != s->zero_addr;
        }
        int ok = init == THREADS && zero == THREADS && c_view == THREADS && distinct &&
                 isolated == THREADS && final == THREADS;
        failures += !ok;
        printf("tls wave=%u ok=%d init=%u zero=%u c_view=%u distinct=%u isolated=%u final=%u\n",
               wave, ok, init, zero, c_view, distinct, isolated, final);
    }
    int main_ok = main_init == TLS_INIT && *cg_tls_addr() == TLS_INIT + 1000 &&
                  cg_tls_addr() == main_addr && &cg_tls == main_addr && cg_tls_zero == 0;
    printf("tls main ok=%d value=%lld\n", main_ok, (long long)*cg_tls_addr());
    return failures || !main_ok ? 3 : 0;
}
