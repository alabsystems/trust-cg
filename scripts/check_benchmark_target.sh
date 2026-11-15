#!/usr/bin/env bash
# Read-only prerequisite check shared by the pinned cross-target benchmarks.
# A trustc can name a target-libdir even when that target is not installed.
set -u
if [ "$#" -ne 2 ]; then
    echo "benchmark target: expected RUSTC TARGET" >&2
    exit 2
fi
benchmark_rustc="$1"
benchmark_target="$2"
benchmark_libdir="$("$benchmark_rustc" --print target-libdir --target "$benchmark_target")" || {
    echo "benchmark target: TOOLING: cannot resolve $benchmark_target libraries" >&2
    exit 2
}
shopt -s nullglob
benchmark_std=("$benchmark_libdir"/libstd-*.rlib)
benchmark_core=("$benchmark_libdir"/libcore-*.rlib)
if [ "${#benchmark_std[@]}" -eq 0 ] || [ "${#benchmark_core[@]}" -eq 0 ]; then
    echo "benchmark target: TOOLING: standard libraries missing for $benchmark_target ($benchmark_libdir); no measurement was run" >&2
    exit 2
fi
