# Monotonicity

## Checked route

`lRedLog` and `lRedJac` are the logarithmic and positive pulled-back reduced
densities relative to the fixed source metric.  Their derivative formulas
combine the L-exponential determinant derivative, the diagonal reduced-length
identity, and the Hamilton--K Laplacian estimate.

The canonical `exists_lRayAdapt` producer now lives in `RayAdapted.lean`.  It
globalizes the strict minimizing ray and constructs one adapted
terminal-orthonormal family on a common open neighborhood.  Thus
`lRedJac_deriv_le0` has no supplied field-family or integrability assumptions.
`lRedJac_anti` then integrates the derivative sign along one ray while deriving
membership in every smaller strict domain from the later minimizing witness.

## Verification and progress

The canonical `RayAdapted` import boundary is verified: its focused check and
named artifact refresh pass, followed by a warning-free focused check of this
module.  No proof placeholders were introduced.  This module was not refreshed
because its public declarations did not change.

- Canonical pointwise reduced-Jacobian monotonicity: **100%**.
- Dedicated strict-ray monotonicity machinery: **100%**.
- The global reduced-volume capstone is completed separately in
  `ReducedVolume.lean`.
