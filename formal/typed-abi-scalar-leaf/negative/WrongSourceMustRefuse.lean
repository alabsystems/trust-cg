-- Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
-- Intentional wrong-twin artifact: independent kernel qualification MUST refuse.
import ScalarReturnTransport
open TrustIr.TypedAbiScalarLeafDraft
example : ((runOrigins [0xaa0003f1, 0xaa1103e0] (seedOrigins 2)).bind
    (fun registers => registers 0)) = some 1 := by decide
