# NormalMetricLocal

## Role

This file is the exact local metric bridge needed to push fenced
normal-coordinate geodesics back to the ambient manifold.

## Current state

- `normalQuarter` and `normalQuarterImage` are the source and image opens.
- `normalQuarterDiffeo` is the smooth restricted normal exponential.
- `normalTotal_quarter` states that the restriction of `normalTotal` is exactly
  the cross-model pullback of the ambient restricted metric.
- `normalGeo_map` packages open-subtype locality and pointwise cross-model
  naturality: any locally smooth `normalTotal` geodesic remaining in the
  quarter ball maps under the normal exponential to an ambient geodesic on the
  same open time set.

Focused verification and the targeted module build passed; this file has no
local warnings or `sorry`.

## Frontier

`NormalPhaseEndpoint.normal_end_eq_intr` now identifies the pushed trajectory
with the intrinsic geodesic from its initial data.  This file's transport role
is complete; the live frontier is downstream branch-domain/smallness
containment.
