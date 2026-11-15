-- Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
-- Intentional W-register artifact: independent kernel qualification MUST refuse.
import ScalarReturnTransport
open TrustIr.TypedAbiScalarLeafDraft
example : decodeMove 0x2a0103f1 = some { destination := 17, source := 1 } := by decide
