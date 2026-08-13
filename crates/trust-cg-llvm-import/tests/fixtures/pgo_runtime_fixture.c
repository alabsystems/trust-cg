/* Test fixture for rt/tcg_pgo_rt.c.
 *
 * Author: Andrew Yates <andrewyates.name@gmail.com>
 * Copyright 2026 Andrew Yates | License: Apache-2.0
 */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

uint64_t __tcg_pgo_counters[] = {11, 22, 33};
const uint64_t __tcg_pgo_nsites = 3;

int main(int argc, char **argv) {
    if (argc == 2 && strcmp(argv[1], "abort") == 0) {
        abort();
    }
    if (argc == 2 && strcmp(argv[1], "_Exit") == 0) {
        _Exit(17);
    }
    if (argc == 2 && strcmp(argv[1], "sleep") == 0) {
        sleep(2);
    }
    if (argc == 2 && strcmp(argv[1], "fork") == 0) {
        pid_t child = fork();
        if (child < 0) {
            return 18;
        }
        if (child == 0) {
            return 0;
        }
        int status = 0;
        if (waitpid(child, &status, 0) != child) {
            return 19;
        }
    }
    return 0;
}
