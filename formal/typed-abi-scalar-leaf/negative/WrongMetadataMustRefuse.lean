-- Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
-- Intentional source-position artifact: independent kernel qualification MUST refuse.
import ScalarReturnTransportControls
open TrustIr
open TrustIr.TypedAbiScalarLeafDraft
example : parameter64 (fixtureArgument (.Parameter 1)) 0 = true := by decide
