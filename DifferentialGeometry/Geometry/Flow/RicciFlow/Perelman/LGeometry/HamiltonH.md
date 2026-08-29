# HamiltonH

## Purpose

This module isolates the scalar-evolution and Hamilton-`H` algebra used after
the purely spatial trace in `TraceDensity`.  It works in square-root backward
time and keeps the endpoint polynomial, avoiding division by the parameter at
`s = 0`.

## Checked API

- `lHamilton` is Hamilton's backward-time scalar quantity after replacing the
  time derivative by the Ricci-flow scalar evolution equation.
- `lHamilton_eq` recovers the original derivative presentation at a regular
  flow time.
- `lHamSq` is the polynomial realization of `s^4 H` along a regularized path;
  `lHamSq_eq` identifies it with the raw-velocity expression away from no
  endpoint assumption other than the supplied velocity relation.
- `lScalar_path_deriv` proves the scalar-curvature chain rule along an
  arbitrary pointwise differentiable square-root-time path.
- `lTrace_deriv` combines `lIndexInt_trace` with that chain rule.  The
  derivative of `s^3 R` is exactly minus `lHamSq` minus the weighted traced
  index density after its scalar correction.
- `lK` is twice the square-root-time integral of `lHamSq`, and `lK_sq`
  identifies it with the raw backward-time integral weighted by
  `tau * sqrt tau`.

The file passes warning-free focused verification, and its exported module
refresh passes.  The local proof repairs were representation-level: dependent
`mfderiv` equalities had to be transported with `congrArg`/transitivity rather
than rewritten under `fromTangentSpace`, and the real tangent scaling was
handled by the two linear maps separately.

## Downstream status

`lHamSq_int`, `lRayLag_int`, `lRayHam_int`, and `lK_ray_energy` now provide the
smallest stable interval-integrability and energy bridges needed by the
canonical ray.  `TraceIntegral.lTraceInt_eq` and
`HamiltonBound.redLength_lap_K` consume this layer without adding scalar-path
regularity assumptions.  The resulting reduced-Jacobian and reduced-volume
monotonicity endpoints are checked in the downstream modules.
