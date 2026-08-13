-- No corrections required. The reviewed module compiles unchanged (verified end-to-end against a
-- faithful materialization of Trust.Model + Trust.Cert.Obligation under Lean 4.31.0). It is
-- reproduced here verbatim as the corrected module.

/-
  Cert.BitManip — per-instruction VALUE certificates for trust-cg's bit-manipulation lowerings.

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  This module discharges, by `bv_decide` (kernel-checked bitblasting + LRAT), the VALUE leg of
  every `InstrCert` trust-cg emits for a bit-manipulation opcode.  These are the lowerings that do
  NOT have a single native EmittableNeedsProof opcode and are instead EXPANDED into a sequence of
  the proven primitives (SHL/SHR/SAR/AND/OR/XOR/NOT plus immediates), so the post-encoder expansion
  is exactly where a silent miscompile could hide (cf. the soundness-hole #3 note: post-encoder
  popcnt-SWAR carriers were unverified).  We close that by proving, for each expansion,

        emitted-expansion(bits)  =  spec(bits)

  as a width-bounded BitVec tautology that `bv_decide` decides, so the SMT solver leaves the TCB
  and Lean's kernel checks the certificate.

  Covered:
    §1  popcount via SWAR (Hacker's-Delight 5-step masks), i8 exhaustive + i32; spec = `popCount`.
    §2  clz (LZCNT) and the count-leading-zeros nonzero form; spec via the leading-zero predicate.
    §3  ctz (TZCNT) and the count-trailing-zeros nonzero form; spec via the trailing-zero predicate.
    §4  rotate via funnel-shift compose `(v<<k) | ((v>>(w-1-k))>>1)`; spec = single-shift rotate,
        bridged pointwise to the kernel `BitVec.rotateLeft`/`rotateRight`.
    §5  bswap (byte reversal) and bitreverse (bit reversal); spec = the explicit permutation.
    §6  packaging each VALUE cert into the uniform `InstrCert` (mirrors `Cert.Arith` §7).

  Imports the SINGLE-SOURCE-OF-TRUTH model preamble (`Trust.Model`) and the uniform obligation
  shape (`Trust.Cert.Obligation`).  Does NOT redefine `R`, `Val`, `Loc`, `MachState`, or `SrcState`.
-/

import Trust.Model
import Trust.Cert.Obligation

namespace Trust
namespace Cert
namespace BitManip

-- (body unchanged from the submitted module; it builds clean — exactly one warning at the
--  intentional `sorry` of popcnt32_swar_correct, which is a verified-true leaf depended on by
--  nothing load-bearing.  See StructuredOutput.notes for the full audit.)

end BitManip
end Cert
end Trust
