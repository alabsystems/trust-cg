# Integrated Linux gates before the twenty-sixth main push — 2026-09-24

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

These gates ran on clean source `89e4306529f1aa1354dfec4ca9bbd75d453c03ea`:
origin/main `0996df987` (the
[gates-26](../2026-09-24-linux-integrated-gates-26/README.md) record) with
L04-P11 merged and a record of its sixth verifier.

## What changed: L04-P11

**Native controls.** The switch and indirect-call controls run on Linux at
O0-O3 with pinned minimums:
- `e2e_aarch64_switch`: 8,685,036 checked calls;
- `e2e_aarch64_indirect_call`: 7,008 checks.

Both are in the floor.

**Per-instruction binding.** In the verifier, each of these binds per
instruction to a decoded-word form or lanewise obligation, and ENC-5 checks
the emitted word:
- register copies (MOV/ORR aliases, typed MOVs, the zero-register forms,
  W<->H FMOV);
- floating-point copies (ORR Vd.16B);
- the 16B NEON AND/ORR/EOR/BIC/NOT.

Each was previously exempted or credited opcode-wide. Every other shape is
refused by name.

**Encoder.** It no longer reads a present non-immediate operand as 0.
`LslRI X0,X1,X2` had encoded as `mov x0,x1` while the verifier credited
it. The verifier refuses register-amount immediate forms and extra ALU
operands.

**Gate ratio.** It moved 174/287 -> 176/287 -> 174/287: the TPREL adds are
no longer credited without a binding.

**Disclosure.** Tests derived from the code pin:
- the 104 credited rows ENC-5 does not decode (88 opcode-wide, 16 per
  instruction, 16 degenerate operand-free bindings);
- ENC-5's 29 named in-arm exits;
- the 117 opcodes whose ignored trailing operand the encoder does not check.

LIMITATIONS.md must name each of these lists exactly.

**Verification.** Six independent verifier rounds. The sixth found the
object code byte-identical before and after the encoder repair:
- 96 targeted programs across 8 configurations;
- 2,868 corpus compiles;
- 478 `--emit-proofs` compiles.

Its latent findings are recorded as open gaps: absent required operands
still encode as 0, and the branch condition, barrier option and `Mrs`
register are masked by the encoder and ENC-5 alike.

**Evidence records.** reports/perf/2026-09-24-linux-l04p11-switch-calls,
-review, -review2, -review3 and -review5.

## Linux regression floor (`records/run34/`)

`scripts/check_linux_aarch64.py` passed all **166 required target families
and 1,042 Rust tests**. The source fingerprint
`2a2ab3832dae42891026e37a793e85c31481452b64b8c788cbe4c28bc9e8babe` was the
same before and after the run. The run took 14:50:54Z to 15:04:29Z. The
highest sampled resident set was 466 MiB, in `e2e_aarch64_link_runtime`.
All four controls were on.

## Library, CLI, native, verifier-gate and branch suites

- **Library tests:** codegen passed 4,204 with 1 ignored, lower 1,902 and
  opt 3,540.
- **CLI, with `TCG_REQUIRE_LLD` and `TCG_REQUIRE_GOLD`:** the binary's tests
  passed 30, `link_options` 37, `output_paths` 8 and
  `trust_ir_binary_container` 4.
- **Native suites, with LLD and gold required and no `SKIP:` line:**
  `aarch64_elf_cfi_differential` 3, `e2e_aarch64_eh_catch` 9,
  `e2e_aarch64_eh_linux` 10, `e2e_aarch64_elf_link` 11,
  `e2e_aarch64_elf_tlsie` 13 and `e2e_aarch64_link_runtime` 34.
- **Verifier gate targets:** `aarch64_value_decode_gate` 5,
  `coverage_gate_tests` 51, `meta_theorems` 8, `proof_gate_strict` 32 and
  `soundness_manifest` 11.
- **L02-P1 lanes:**
  - with LLD and gold required: `aarch64_elf_symbol_binding` 41 and
    `e2e_aarch64_elf_relocation_model` 20;
  - `core_jit_planning` 13, `jit_external_symbol_resolution_policy` 6, and
    the two x86-64 module-batch targets 1 each.
- **The owner's fsym tests:** `fsym_ub_map` 10, `fsym_interpreter_oracle` 4,
  and the CLI's `fsym_flag` 20.

Regression evidence only. It is not complete Linux qualification, proof or
Trust-toolchain authority, or release readiness. Every L01–L14 row remains
OPEN.
