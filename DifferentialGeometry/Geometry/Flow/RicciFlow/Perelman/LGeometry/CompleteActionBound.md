# CompleteActionBound

## Purpose

`lRegCosts_bdd_rm` supplies the noncompact lower-boundedness input consumed by
`lRegCostC1_le_bdd` and `lCost_le_join_bdd`.  It applies to the exact set of
global fixed-endpoint `C¹` regularized L-action values.

## Route

On a nonnegative square-root-time interval `[a,b]`, the uniform squared
Riemann-curvature bound gives the scalar-potential estimate
`lRegPot_lower_rm`.  For each global `C¹` competitor, regularity of the
backward slab gives integrability of both the full regularized Lagrangian and
its speed-square part.  The speed-square is pointwise nonnegative, so
`lRegKinetic_le` yields the curve-independent lower bound

```text
(-2 b^2 n^2 sqrt(K)) (b-a) <= lRegAction alpha a b.
```

This proves `BddBelow` directly.  It does not assume `CompactSpace M`, the
desired `BddBelow` conclusion, a cost barrier, or a new flow package.  Metric
completeness is deliberately absent because it is not used in this scalar
lower-bound step; complete bounded-curvature consumers can apply the weaker
producer directly.

## Verification

Focused verification passes without warnings or placeholders.  The named
module artifact has also been refreshed successfully for downstream consumers.

## Project position

- `lRegCosts_bdd_rm`: 100% proved, focused green, and exported.
- Dedicated complete-flow action-lower-bound machinery: 100% for this brick.
- The all-point spacetime weak barrier, `exists_redLen_le`,
  `redVolume_late_low`, `smooth_nlc`, P2, and the final Poincare endpoint remain
  0% theorem endpoints.
