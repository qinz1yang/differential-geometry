# NormalMetricLocal

## Role

This file is the exact local metric bridge needed to push fenced
normal-coordinate geodesics back to the ambient manifold.

## Current state

- `normalQuarter` uses one quarter of `expRadiusGp`, and
  `normalQuarterImage` is its image open.
- `normalQuarterDiffeo` is the smooth restriction of `framedExpDiffeo`.
- `normalTotal_quarter` states that the restriction of `normalTotal` is exactly
  the cross-model pullback of the ambient restricted metric.
- `normalGeo_map` packages open-subtype locality and pointwise cross-model
  naturality: any locally smooth `normalTotal` geodesic remaining in the
  quarter ball maps under the normal exponential to an ambient geodesic on the
  same open time set.

Focused verification and the framed targeted module build passed; this file
has no local warnings or `sorry`.

## Frontier

`NormalPhaseEndpoint.normal_end_eq_intr` now identifies the pushed trajectory
with the intrinsic geodesic from its initial data.  This file's transport role
is complete on the framed coordinate API; the live frontier is downstream
branch-domain/smallness containment and migration of consumers that still
state the old raw map explicitly.
