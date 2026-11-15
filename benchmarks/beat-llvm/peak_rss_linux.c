/* One command per native process keeps Linux's inherited RSS floor small.
 * Same RUSAGE_CHILDREN per-process maximum as the Python/Darwin wrapper.
 * Compile outside the measurement. No command runs in a shell here.
 */
#define _GNU_SOURCE
#include <errno.h>
#include <limits.h>
#include <math.h>
#include <poll.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#include <fcntl.h>

static double now(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) {
        perror("peak_rss: clock_gettime");
        exit(127);
    }
    return (double)ts.tv_sec + (double)ts.tv_nsec / 1e9;
}

static int record(const char *out, const char *status, int rc, double wall) {
    struct rusage ru;
    if (getrusage(RUSAGE_CHILDREN, &ru) != 0) {
        perror("peak_rss: getrusage");
        return 127;
    }
    FILE *f = fopen(out, "w");
    if (!f) {
        perror("peak_rss: record");
        return 127;
    }
    fprintf(f, "{\"ru_maxrss_raw\":%ld,\"ru_maxrss_unit\":\"KiB\","
               "\"ru_maxrss_bytes\":", ru.ru_maxrss);
    if (ru.ru_maxrss > 0)
        fprintf(f, "%llu", (unsigned long long)ru.ru_maxrss * 1024);
    else
        fputs("null", f);
    fprintf(f, ",\"platform\":\"linux\",\"returncode\":%d,\"status\":\"%s\","
               "\"wall_s\":", rc, status);
    if (strcmp(status, "ok") == 0)
        fprintf(f, "%.6f", wall);
    else
        fputs("null", f);
    fputs("}\n", f);
    if (fclose(f) != 0) {
        perror("peak_rss: close record");
        return 127;
    }
    return rc;
}

int main(int argc, char **argv) {
    const char *out = NULL;
    double timeout = -1;
    int i = 1;
    for (; i < argc; i++) {
        if (strcmp(argv[i], "--") == 0) {
            i++;
            break;
        }
        if (strcmp(argv[i], "--out") == 0 && i + 1 < argc) {
            out = argv[++i];
        } else if (strcmp(argv[i], "--timeout") == 0 && i + 1 < argc) {
            char *end;
            timeout = strtod(argv[++i], &end);
            if (*end || !isfinite(timeout) || timeout < 0) {
                fputs("peak_rss: invalid timeout\n", stderr);
                return 127;
            }
        } else {
            fputs("peak_rss: expected --out FILE [--timeout S] -- CMD\n", stderr);
            return 127;
        }
    }
    if (!out || i >= argc)
        return 127;

    /* An exec-error pipe distinguishes failed exec from a real exit(127).
     * CLOEXEC ensures a successful command cannot leave it open in descendants.
     */
    int errors[2];
    if (pipe2(errors, O_CLOEXEC) != 0) {
        perror("peak_rss: pipe");
        return record(out, "wrapper-failed", 127, 0);
    }
    signal(SIGCHLD, SIG_DFL);
    double start = now();
    pid_t owner = getpid();
    pid_t child = fork();
    if (child < 0) {
        perror("peak_rss: fork");
        close(errors[0]);
        close(errors[1]);
        return record(out, "wrapper-failed", 127, 0);
    }
    if (child == 0) {
        close(errors[0]);
        /* Own group: timeout cleanup includes ordinary child processes, while
         * never sending a signal to the invoking Python process's group.
         */
        if (setpgid(0, 0) != 0 || prctl(PR_SET_PDEATHSIG, SIGKILL) != 0 ||
            getppid() != owner) {
            int failure = errno ? errno : ECHILD;
            (void)!write(errors[1], &failure, sizeof(failure));
            _exit(127);
        }
        execvp(argv[i], argv + i);
        int failure = errno;
        (void)!write(errors[1], &failure, sizeof(failure));
        _exit(127);
    }
    close(errors[1]);
    /* Parent also establishes the group so an immediate deadline cannot race
     * the child's setpgid. An exited or already-execed child is still ours.
     */
    (void)setpgid(child, child);
    const char *status = "ok";
    int rc = 0;
    if (timeout >= 0) {
        int pidfd = (int)syscall(SYS_pidfd_open, child, 0);
        if (pidfd < 0) {
            perror("peak_rss: pidfd_open");
            status = "wrapper-failed";
            rc = 127;
        } else {
            struct pollfd fd = {.fd = pidfd, .events = POLLIN};
            for (;;) {
                double ms = (timeout - (now() - start)) * 1000;
                int wait_ms = ms <= 0 ? 0 : ms >= INT_MAX ? INT_MAX : (int)(ms + 0.999);
                int ready = poll(&fd, 1, wait_ms);
                if (ready > 0 && (fd.revents & POLLIN))
                    break;
                if (ready < 0 && errno == EINTR)
                    continue;
                if (ready == 0 && now() - start < timeout)
                    continue;
                status = ready == 0 ? "timeout" : "wrapper-failed";
                rc = ready == 0 ? 124 : 127;
                break;
            }
            close(pidfd);
        }
        if (rc != 0) {
            (void)kill(-child, SIGKILL);
            (void)kill(child, SIGKILL);
        }
    }
    /* The child stays unreaped until here, so neither its PID nor its owned
     * process-group ID can be reused while the timeout sends a signal.
     */
    int ws;
    pid_t waited;
    do {
        waited = waitpid(child, &ws, 0);
    } while (waited < 0 && errno == EINTR);
    double wall = now() - start;
    int failure = 0;
    ssize_t n;
    do {
        n = read(errors[0], &failure, sizeof(failure));
    } while (n < 0 && errno == EINTR);
    close(errors[0]);
    if (waited != child || n < 0 || (n != 0 && n != sizeof(failure))) {
        status = "wrapper-failed";
        rc = 127;
    } else if (rc == 0 && n == sizeof(failure)) {
        fprintf(stderr, "peak_rss: cannot execute %s: %s\n", argv[i], strerror(failure));
        status = "exec-failed";
        rc = 127;
    } else if (rc == 0 && WIFSIGNALED(ws)) {
        status = "signaled";
        rc = 128 + WTERMSIG(ws);
    } else if (rc == 0 && WIFEXITED(ws)) {
        rc = WEXITSTATUS(ws);
    }
    return record(out, status, rc, wall);
}
