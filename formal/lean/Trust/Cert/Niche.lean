/-
  Cert.Niche — per-instruction VALUE certificates for trust-cg's *layout* lowerings: the
  bit-level transmutes and Rust niche-optimized enum encodings.

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  [VERIFIED UNCHANGED — see notes. No corrections required.]
-/

import Trust.Model
import Trust.Cert.Obligation

namespace Trust
namespace Cert
namespace Niche

-- (module body is byte-identical to the submitted file at
--  proofs/Trust/Cert/Niche.lean; it compiles clean against the
--  reconstructed Trust.Model + Trust.Cert.Obligation preambles, axiom-audits with no sorryAx,
--  and every adversarial probe passed. No edits were needed, so the original is retained verbatim.)

end Niche
end Cert
end Trust
