# ApproximatesLinearOn

## Current state

- `ApproximatesLinearOn.fderiv_sub_le` is the canonical fixed-interior-point
  derivative estimate: a differentiable map approximating a continuous linear
  map on a neighborhood has derivative within the same operator-norm error.
- The theorem is scalar-generic and uses only the native
  `ApproximatesLinearOn.lipschitzOnWith` and
  `HasFDerivAt.le_of_lipschitzOn` APIs.
- Focused verification passed without placeholders or warnings, and the phase
  endpoint inverse consumer also passed after migration.

## API boundary

Mathlib's `ApproximatesLinearOn.norm_fderiv_sub_le` is an almost-everywhere
statement designed for measurable sets and boundary points.  It does not
replace this neighborhood/interior-point theorem.  The reusable pointwise
result therefore lives here in the calculus layer rather than in the ODE or
HCG consumer layers.

## HCG accounting

This helper is complete, but it is only a small calculus brick in the shared
Hessian--Neumann producer.  It does not by itself construct either
`CmHessianInput` or `StrictDistInput`; both endpoint producers remain unstated
or unproved at this layer.
