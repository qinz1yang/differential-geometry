# MinMaxAction

## Verified interface

Focused verification passes without warnings or placeholders.

- `lRegKinetic_le` is the assumption-minimal algebraic producer.  Given a
  pointwise lower bound `C` for the scalar part of `lRegLag`, integrability of
  the kinetic and full Lagrangian terms, and an action upper bound `A`, it gives
  `integral lRegSpeedSq <= 2 * (A - C * (b - a))`.
- `lRegKinetic_bound` specializes this uniformly on a compact manifold.  It
  assumes only `ScalarSTContOn` for the flow data and that the backward times
  of the interval lie in the carrier; `lScalar_lower` supplies one constant
  valid for every curve.

Both results fully evaluate the moving metric on the velocity before making
scalar inequalities.  No fixed reference metric, gradient/Ricci bound, new
class, or consumer-side compactness assumption enters the algebraic producer.

## Role in the cut route

This action-to-kinetic brick is complete (**100%**) and supplies the `hkin`
input of `lRegInit_bdd`.  It does not itself prove a common action budget for
minimizing rays or the limiting stability of minimizing initial vectors.
Consequently the minimizing-vector compactness endpoint and `lCut_alt` remain
unproved (**0%**), and `redVolume_anti` remains **0%**.  It is one small
producer inside the roughly **92%+** dedicated compact ordinary-flow
L-geometry machinery recorded in the live plan; reused generic infrastructure
is unchanged.
