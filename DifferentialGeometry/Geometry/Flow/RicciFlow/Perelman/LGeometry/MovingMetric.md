# MovingMetric

## Result

`lInner_deriv_chart` proves the backward-time product rule for a moving
Ricci-flow metric under the same pinned-chart regularity used by the native
fixed-metric compatibility theorem.  `lInner_deriv` supplies the pointwise
`ContMDiffAt` wrapper.  The metric-time contribution is `+2 Ric` because the
forward Ricci-flow equation is composed with `tau ↦ T - tau`.

The proof is scalar throughout.  It forms a jointly differentiable two-variable
chart-Gram pairing, identifies its time slice with `metricDerivAt`, identifies
its curve slice with the existing fixed-metric covariant product rule, and
then differentiates along the diagonal.  This avoids comparing moving bundle
maps or adding a new metric-family interface.

## Verification

Focused verification passed without warnings.  The file contains no
`sorry`, `admit`, or new axioms.

## Next theorem

This producer is now consumed by the focused-green `FirstVariation.lean`.
That file proves the pointwise density derivative, internally justified
differentiation under the integral, the full Morgan--Tian first-variation
formula, and its scalar Euler-residual form without adding a consumer-side
domination assumption.

The later first-variation, criticality equivalence, regularized ODE, and local
existence/uniqueness stages are now focused-green.  No further moving-metric
producer is currently missing for L3.

## Progress

`redVolume_anti` remains **0%**.  Dedicated L-geometry machinery is about
**16--18%**; generic reusable prerequisites are about **60--70%**.  P2 as a
whole remains below **1%**, and the whole Poincare program estimate remains
**3--5%**.
