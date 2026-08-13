#if defined(__APPLE__)
#define _DARWIN_C_SOURCE 1
#endif
#define _POSIX_C_SOURCE 200809L

/* tcg_pgo_rt.c - AOT PGO counter dump runtime for trust-cg-ws2-import.
 *
 * Author: Andrew Yates <andrewyates.name@gmail.com>
 * Copyright 2026 Andrew Yates | License: Apache-2.0
 *
 * Link this file into a binary compiled with TCG_PGO_GEN=<base>:
 *
 *   TCG_PGO_GEN=<base> trust-cg-ws2-import --opt-level O2 a.ll a.o
 *   cc -pthread a.o rt/tcg_pgo_rt.c -o bin -lm
 *   TCG_PGO_OUT=<base>.raw ./bin ...
 *
 * The instrumented object DEFINES `__tcg_pgo_counters` (one u64 slot per
 * instrumented basic block, module-wide dense index order matching the
 * `<base>.sites` sidecar) and `__tcg_pgo_nsites` (u64 slot count). At normal
 * process startup the runtime acquires a nonblocking single-writer lock,
 * securely truncates the single-link regular file named by TCG_PGO_OUT, then
 * opens an exclusive temporary file beside it. At normal exit its destructor
 * writes the counter array VERBATIM — nsites raw little-endian u64 values, no
 * header — and atomically renames the complete temporary file over the target.
 * (The host is little-endian AArch64; fwrite of the u64 array is the LE wire
 * format the USE-side reader checks.)
 *
 * Fail-safe properties, mirrored by the compiler's USE-side checks:
 *  - TCG_PGO_OUT unset/empty -> no file written, run is unaffected.
 *  - After the startup constructor runs, an abnormal exit (signal, _Exit,
 *    abort) skips the dump destructor and leaves a zero/short file; the
 *    USE-side length check against the .sites sidecar fails CLOSED. If the
 *    process never reaches constructors, an older file is not touched, so
 *    callers must still manage each .sites/.raw pair as one generation.
 *  - Any requested-output setup, write, close, or rename error terminates the
 *    canary nonzero. A short write leaves the public raw path empty; only a
 *    complete temporary file is installed there.
 *  - A same-path concurrent writer fails before truncating the public target.
 *    Any call to fork after startup marks both parent and child invalid; neither
 *    may publish a profile. Use one non-forking canary process per base name.
 *  - The naked-u64 raw format has no profile identity header. It cannot
 *    authenticate an unrelated same-length raw file; the USE-side documents
 *    and enforces every check the format can actually support.
 *  - Counter increments are plain ldr/add/str (NOT atomic): multi-threaded
 *    canaries may drop racing increments; counts are estimates by contract.
 */

#include <fcntl.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>

#ifndef O_NOFOLLOW
#error "tcg_pgo_rt.c requires O_NOFOLLOW"
#endif

extern uint64_t __tcg_pgo_counters[];
extern const uint64_t __tcg_pgo_nsites;

static FILE *__tcg_pgo_output;
static char *__tcg_pgo_target_path;
static char *__tcg_pgo_temp_path;
static int __tcg_pgo_lock = -1;
static pid_t __tcg_pgo_owner;
static volatile sig_atomic_t __tcg_pgo_fork_observed;

static void __tcg_pgo_fatal(const char *message) {
    fprintf(stderr, "tcg-pgo: %s\n", message);
    _Exit(125);
}

static void __tcg_pgo_release_paths(void) {
    free(__tcg_pgo_target_path);
    free(__tcg_pgo_temp_path);
    __tcg_pgo_target_path = NULL;
    __tcg_pgo_temp_path = NULL;
}

static void __tcg_pgo_mark_fork(void) {
    __tcg_pgo_fork_observed = 1;
}

static void __tcg_pgo_reject_forked_process(void) {
    static const char message[] =
        "tcg-pgo: forked canary process cannot publish a profile\n";
    if (__tcg_pgo_temp_path != NULL) {
        (void)unlink(__tcg_pgo_temp_path);
    }
    (void)write(STDERR_FILENO, message, sizeof(message) - 1);
    _Exit(125);
}

static void __tcg_pgo_set_close_on_exec(int descriptor, const char *what) {
    if (fcntl(descriptor, F_SETFD, FD_CLOEXEC) != 0) {
        __tcg_pgo_fatal(what);
    }
}

__attribute__((constructor)) static void __tcg_pgo_prepare(void) {
    const char *path = getenv("TCG_PGO_OUT");
    if (path == NULL || path[0] == '\0') {
        return;
    }

    size_t path_len = strlen(path);
    /* 12 bytes covers `.tmp.XXXXXX`; 6 covers `.lock`, including NULs. */
    if (path_len > SIZE_MAX - 12) {
        __tcg_pgo_fatal("output path is too long");
    }
    __tcg_pgo_target_path = malloc(path_len + 1);
    __tcg_pgo_temp_path = malloc(path_len + 12);
    char *lock_path = malloc(path_len + 6);
    if (__tcg_pgo_target_path == NULL || __tcg_pgo_temp_path == NULL ||
        lock_path == NULL) {
        free(lock_path);
        __tcg_pgo_release_paths();
        __tcg_pgo_fatal("cannot allocate output paths");
    }
    memcpy(__tcg_pgo_target_path, path, path_len + 1);
    int length = snprintf(__tcg_pgo_temp_path, path_len + 12, "%s.tmp.XXXXXX",
                          path);
    if (length < 0 || (size_t)length >= path_len + 12) {
        free(lock_path);
        __tcg_pgo_release_paths();
        __tcg_pgo_fatal("cannot construct temporary output path");
    }
    length = snprintf(lock_path, path_len + 6, "%s.lock", path);
    if (length < 0 || (size_t)length >= path_len + 6) {
        free(lock_path);
        __tcg_pgo_release_paths();
        __tcg_pgo_fatal("cannot construct writer-lock path");
    }

    __tcg_pgo_lock = open(lock_path, O_RDWR | O_CREAT | O_NOFOLLOW, 0600);
    free(lock_path);
    if (__tcg_pgo_lock < 0) {
        __tcg_pgo_fatal("cannot open writer lock");
    }
    __tcg_pgo_set_close_on_exec(__tcg_pgo_lock,
                                "cannot secure writer lock across exec");
    if (flock(__tcg_pgo_lock, LOCK_EX | LOCK_NB) != 0) {
        __tcg_pgo_fatal("another canary is writing this profile");
    }
    if (pthread_atfork(__tcg_pgo_mark_fork, NULL, NULL) != 0) {
        __tcg_pgo_fatal("cannot install fork-rejection hook");
    }
    __tcg_pgo_owner = getpid();

    int target =
        open(path, O_WRONLY | O_CREAT | O_NOFOLLOW | O_NONBLOCK, 0600);
    if (target < 0) {
        __tcg_pgo_fatal("cannot securely open output path");
    }
    struct stat target_status;
    if (fstat(target, &target_status) != 0) {
        close(target);
        __tcg_pgo_fatal("cannot inspect output path");
    }
    if (!S_ISREG(target_status.st_mode) || target_status.st_nlink != 1) {
        close(target);
        __tcg_pgo_fatal(
            "output path must be a regular file with exactly one link");
    }
    if (ftruncate(target, 0) != 0) {
        close(target);
        __tcg_pgo_fatal("cannot securely truncate output path");
    }
    if (close(target) != 0) {
        __tcg_pgo_fatal("cannot close truncated output path");
    }

    /* Keep only the temporary stream open until the destructor. An abnormal
     * exit leaves the already-truncated public target unable to pass USE. */
    int temporary = mkstemp(__tcg_pgo_temp_path);
    if (temporary < 0) {
        __tcg_pgo_release_paths();
        __tcg_pgo_fatal("cannot create exclusive temporary output path");
    }
    __tcg_pgo_set_close_on_exec(temporary,
                                "cannot secure temporary output across exec");
    __tcg_pgo_output = fdopen(temporary, "wb");
    if (__tcg_pgo_output == NULL) {
        close(temporary);
        remove(__tcg_pgo_temp_path);
        __tcg_pgo_release_paths();
        __tcg_pgo_fatal("cannot open temporary output stream");
    }
}

__attribute__((destructor)) static void __tcg_pgo_dump(void) {
    if (__tcg_pgo_output == NULL) {
        return;
    }
    if (__tcg_pgo_fork_observed || getpid() != __tcg_pgo_owner) {
        __tcg_pgo_reject_forked_process();
    }
    size_t n = (size_t)__tcg_pgo_nsites;
    size_t written =
        fwrite(__tcg_pgo_counters, sizeof(uint64_t), n, __tcg_pgo_output);
    int flush_error = fflush(__tcg_pgo_output);
    int close_error = fclose(__tcg_pgo_output);
    __tcg_pgo_output = NULL;

    if (written != n || flush_error != 0 || close_error != 0) {
        fprintf(stderr, "tcg-pgo: short counter write (%zu of %zu slots)\n",
                written, n);
        remove(__tcg_pgo_temp_path);
        __tcg_pgo_release_paths();
        _Exit(125);
    }
    if (rename(__tcg_pgo_temp_path, __tcg_pgo_target_path) != 0) {
        remove(__tcg_pgo_temp_path);
        __tcg_pgo_release_paths();
        __tcg_pgo_fatal("cannot install completed counter file");
    }
    if (close(__tcg_pgo_lock) != 0) {
        __tcg_pgo_lock = -1;
        __tcg_pgo_release_paths();
        __tcg_pgo_fatal("cannot release writer lock");
    }
    __tcg_pgo_lock = -1;
    __tcg_pgo_release_paths();
}
