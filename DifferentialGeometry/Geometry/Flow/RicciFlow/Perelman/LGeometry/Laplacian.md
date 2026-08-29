# Laplacian

## Route

`redLength_lap_le` is the strict-minimizing-region trace of
`redLength_hess_le`.  A supplied adapted family is assumed only with the
scaled-field regularity, chart differentiability, adapted ODE, terminal
orthonormality, and interval-integrability hypotheses consumed by
`redLength_hess_le` and `lIndex_trace`.

The ray regular-time and manifold-differentiability inputs to `lIndex_trace`
are derived internally from strict minimizing membership via
`lMinDomain_down` and `lRegCurve_isReg`; they are not public assumptions.

The proof uses the checked local smoothness of reduced length, identifies the
Laplacian with the metric trace of its Hessian, realizes the supplied terminal
orthonormal family as a basis, applies the Hessian comparison fieldwise, and
then rewrites the finite sum with `lIndex_trace`.  The remaining integral keeps
the finite sum of `lRegIndexInt` and the scalar-curvature contraction.  No
Hamilton `H` or time-Ricci contraction is included at this stage.

## Status

The target theorem is implemented without a placeholder.  Focused verification
passes without warnings after the public `redLength_smooth` export refresh.

## Project status

- `redLength_lap_le`: proved and focused-verified, 100%.
- Dedicated supplied-family Laplacian trace machinery: 100%.
- The later Morgan--Tian `H(X)` and time-Ricci contraction: 0% in this file.
- `redVolume_anti`: 0%.
- Dedicated compact ordinary-flow L-geometry machinery: approximately 99%.
- P2 remains below 1%; the whole Poincare program remains approximately 3--5%.
