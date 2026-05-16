# RSTensor Basis Notes

## 2026-05-11 coordinate extraction

Successful:

- Added `continuousLinearMap_homBasis` and `continuousLinearMap_homBasis_repr`
  as the reusable finite-dimensional Hom-coordinate layer.
- Added `tensorRSModel_basis` and `tensorRSModel_basis_repr`; an `(r,s)`
  model coordinate is now explicitly "apply an input `(0,r)` basis tensor,
  then evaluate the output `(0,s)` tensor on basis vectors".
- Added `contMDiffAt_tensorRSModel_of_apply_basis_eval_basis`, moving the
  mixed model smoothness criterion out of `NablaOnTensors.Regularity`.
- Added the fixed-trivialization transition layer:
  `Tensor0SSpace.trivializationAt_apply`,
  `TensorRSSpace.trivializationAt_apply`, and
  `TensorRSSpace.trivializationAt_basis_coord`.
- Added `Tensor0SSpace.constInChart`, the named local `(0,s)` tensor section
  that is constant in a fixed tensor-bundle trivialization.  This is the
  tensor-input analogue of `tangentConstInChart` and is used by the mixed
  regularity frontier.

Remaining:

- This file has no proof frontier. The remaining `nablaRS_reg` gap is now a
  scalar smoothness theorem in `NablaOnTensors.Regularity` after applying the
  transition layer.
