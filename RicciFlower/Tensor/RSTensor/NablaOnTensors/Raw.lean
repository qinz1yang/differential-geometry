import RicciFlower.Tensor.RSTensor.NablaOnTensors.Smooth

/-!
# Raw and regular tensor covariant derivative APIs

Compatibility wrapper for the raw `nabla*Fun` definitions, bundled `nabla*` wrappers, and
regularity theorems.  Downstream code may continue importing
`RicciFlower.Tensor.RSTensor.NablaOnTensors.Raw`; implementation files should prefer
`RawDefs` or `Regularity` when they only need one layer.
-/
