# CostChartLip

## Verified result

Focused verification passed without warnings or placeholders, and the exported
module was refreshed successfully for downstream consumers.

`lCost_chart_lip` proves, for every positive backward time whose closed slab is
regular and for every canonical-chart center `p`, that

```lean
LocallyLipschitzOn (extChartAt I p).target
  ((fun y : M => lCost S T x y tau) ∘ (extChartAt I p).symm)
```

No connectedness hypothesis is used.  At a reachable coordinate endpoint the
proof obtains a center minimizer, bounds all nearby minimizing initial tangents,
restricts them to a compact closed minimizing/endpoint slice, and replaces a
short terminal ray segment by an affine inverse-chart ramp.  At an unreachable
endpoint it reuses `lCost_zero_lip`, so the local coordinate cost is identically
zero.

## Producer API

- `lCost_le_join_bdd`: on a possibly noncompact manifold, two smooth pieces
  meeting at a node give an honest cost competitor after native `C¹` density,
  assuming explicitly that the global fixed-endpoint `C¹` action values are
  bounded below.  No ambient compactness or time-slab hypothesis is used; the
  native global smoothing step retains the existing Hausdorff assumption.
- `lCost_le_join`: the compact compatibility theorem.  It obtains that lower
  bound from the existing compact direct-method accessor and delegates the
  actual join argument to `lCost_le_join_bdd`.
- `lCost_le_ray_bdd`: on a possibly noncompact manifold, a positive regularized
  ray has cost no larger than its own action whenever the fixed-endpoint action
  class is bounded below. The proof totalizes the ray by the native smooth
  clamp and does not add compactness.
- `lMinVec_local_bdd`: minimizing initial tangents reaching a small coordinate
  neighborhood of one minimizing endpoint have a uniform model norm bound.
- `lRayChart_bound`: a compact regular ray family contained in one chart has a
  uniform linear terminal coordinate-displacement bound; convexity of the ray
  family is not required.
- `lRayChart_tube`: compact terminal chart membership persists on one uniform
  terminal square-root-time interval.
- `lRampAct_eq`: the intrinsic action of an inverse-chart affine ramp equals its
  one-piece `lChartAct`.
- `lCost_ramp_le`: terminal ray replacement gives the quantitative upper cost
  competitor consumed by the main proof.

The arbitrary-duration ramp from `CostChartRamp` is essential: the replacement
duration is the endpoint coordinate distance, while its actual spatial
displacement also includes motion of the truncated original ray.

The noncompact factorization passed focused verification without warnings or
placeholders, and the exported module was refreshed for its immediate
downstream consumer.

## Project position

- `lCost_chart_lip`: 100% proved and focused green.
- `lCost_le_join_bdd`: 100% proved and focused green.
- `lCost_le_ray_bdd`: 100% proved, focused green, and refreshed for its
  complete-flow consumers.
- Dedicated endpoint-Lipschitz machinery: 100% for this stage.
- Downstream cut-multiple nondifferentiability/null assembly: separate consumer;
  it must be checked against this refreshed export.
- `redVolume_anti`: 100% in its own downstream module; it is not reproved here.
- Generic reused manifold/compactness/action infrastructure: already available
  and reused rather than duplicated.
