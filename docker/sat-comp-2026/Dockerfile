# trust-cg-sat SAT-Competition 2026 reproducible build image.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# Purpose
# -------
# Produce a Linux x86-64 binary of `trust_cg_sat` from a fresh clone of
# the source repository so the SAT-Comp 2026 judging harness can
# reproduce the submission exactly. The host workstation is Apple
# Silicon (AArch64); building inside a `--platform=linux/amd64`
# container under Docker Desktop's QEMU emulation produces the correct
# ELF binary without requiring a separate x86 box.
#
# Inputs (build args)
# -------------------
# * TRUST_CG_REF — git ref of `trust-cg` to build (default: v0.1.0).
#
# trust-cg's lockfile selects the exact public trust-ir revision.
#
# Output
# ------
# Final image stage exposes the binary at `/usr/local/bin/trust_cg_sat`
# (canonical path used by the StarExec wrapper scripts). It is copied unchanged
# from Cargo's release build in the builder stage.

FROM --platform=linux/amd64 ubuntu:24.04 AS builder

ARG TRUST_CG_REF=v0.1.0
ARG RUST_VERSION=1.97.1

ENV DEBIAN_FRONTEND=noninteractive \
    CARGO_HOME=/usr/local/cargo \
    RUSTUP_HOME=/usr/local/rustup \
    PATH=/usr/local/cargo/bin:$PATH

# Base toolchain. `build-essential` gives gcc + make for the vendored
# MicroSAT / drat-trim C sources. `cmake` is present for any future C++
# dependency that pulls it in; today's vendored C sources do not require it.
# `clang` supplies libclang for bindgen and the C compiler used by the SAT host
# build on this image.
RUN apt-get update && apt-get install -y --no-install-recommends \
        ca-certificates \
        curl \
        git \
        build-essential \
        clang \
        cmake \
        pkg-config \
        libssl-dev \
        zlib1g-dev \
    && rm -rf /var/lib/apt/lists/*

# Rustup with the pinned stable toolchain. We do NOT pre-install a
# cross target because this stage already runs as `linux/amd64`, so
# the native target IS `x86_64-unknown-linux-gnu`.
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
        | sh -s -- -y --default-toolchain ${RUST_VERSION} --profile minimal \
    && rustc --version \
    && cargo --version

WORKDIR /build

RUN git clone https://github.com/alabsystems/trust-cg.git /build/trust-cg \
    && (cd /build/trust-cg && git checkout ${TRUST_CG_REF})

# Single canonical build line. The release profile sets `opt-level=3`;
# `cc-rs`'s build script for `trust-cg-sat-host` adds `-O3
# -march=native` on the C side. Note that `-march=native` inside a
# `linux/amd64` emulation layer resolves to whatever the QEMU shim
# exposes (typically Westmere/Nehalem-class on a Mac host); SAT-Comp
# does not pin a microarchitecture, so this is acceptable.
RUN cd /build/trust-cg \
    && cargo build --release --locked --bin trust_cg_sat

# Sanity-check the produced binary actually runs.
RUN /build/trust-cg/target/release/trust_cg_sat --help >/dev/null

# Final image: a thin runtime that just carries the solver binary at
# the StarExec convention path. We use the same Ubuntu base so the
# glibc the binary was linked against is present; nothing else is
# needed at run time.
FROM --platform=linux/amd64 ubuntu:24.04

LABEL org.opencontainers.image.title="trust-cg-sat (SAT-Comp 2026)"
LABEL org.opencontainers.image.authors="Andrew Yates <andrewyates.name@gmail.com>"
LABEL org.opencontainers.image.licenses="Apache-2.0"
LABEL org.opencontainers.image.source="https://github.com/alabsystems/trust-cg"

COPY --from=builder /build/trust-cg/target/release/trust_cg_sat /usr/local/bin/trust_cg_sat
COPY --from=builder /build/trust-cg/starexec_run_default.sh     /solver/starexec_run_default.sh

RUN chmod +x /usr/local/bin/trust_cg_sat /solver/starexec_run_default.sh

WORKDIR /solver
ENTRYPOINT ["/solver/starexec_run_default.sh"]
