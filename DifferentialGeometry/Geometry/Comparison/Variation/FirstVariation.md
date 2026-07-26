# FirstVariation.lean

## 2026-06-24

Added `first_variation_geodesic_fixed_end`: for a unit-speed geodesic and a
smooth variation whose final endpoint is fixed, the first variation of arc
length is the negative initial boundary term. This is the reusable moving-start
boundary-term producer needed for the center-of-mass distance-gradient theorem.

The useful proof route was to specialize the existing free-endpoint first
variation formula, kill the final endpoint term by the fixed-end hypothesis,
and kill the integral term by the geodesic equation on the central curve. The
final simplification is sensitive to dependent rewriting through `g.inner`;
rewrite the central-curve derivative before rewriting the base point.

This does not yet prove
`grad (1/2 d(., pt)^2) = - exp_q^{-1}(pt)`. The remaining bridge is to build,
for a moving base curve and fixed endpoint, a smooth family of minimizing
geodesics, prove its arc length agrees locally with the Riemannian distance,
and identify the initial unit velocity with the normalized inverse-exponential
vector. The fixed-base radial-distance/Gauss-lemma API does not provide that
moving-base family by itself.

Verification status: passed. Axiom print for
`first_variation_geodesic_fixed_end` is `[propext, Classical.choice,
Quot.sound]`; no `sorryAx`.

Follow-up in the same layer:

- `dist_deriv_of_length`: if the fixed-endpoint geodesic variation locally
  realizes the distance from its moving initial endpoint to the fixed final
  endpoint by arc length, then the derivative of that distance is the same
  negative boundary term.
- `halfSq_deriv_length`: the corresponding derivative of
  `1/2 * d^2` along such a variation, using the central distance value `L`.

These adapters isolate the exact geometric input that still has to be
constructed for `lbl411`: a smooth local family of length-minimizing geodesics
from a moving base to the fixed point. Verification status: passed. Axiom
prints for both adapters are `[propext, Classical.choice, Quot.sound]`; no
`sorryAx`.

## 2026-07-08 pointwise metric-compatibility wrapper

Added `inner_deriv_at`, the `ContMDiffAt` version of the existing
`metric_compat_hasDerivAt_inner` wrapper.  It still delegates to the same
chart-derivative core theorem; the only change is that callers no longer need a
globally smooth curve when the derivative is used at one time.

Verification passed.  This is infrastructure only: it does not change the
first-variation endpoint theorems and does not prove any new volume-comparison
theorem.
