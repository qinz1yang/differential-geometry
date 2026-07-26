# CurvaturePullback

## `ham3_space_box` route

The canonical lowered Riemann tensor now has a direct universal-cover
naturality theorem, `metricRm_lifted`.  Its proof uses the already verified
chart-Riemann naturality and the canonical coordinate bridge.  It does not
require the older `chartRiemannBasisIdentity` hypotheses carried by
`riemannOp_lifted_natural`.

This is the curvature producer needed to transfer the normalized
curvature-one formula from the compact base to its complete simply connected
universal cover.

`metricRm_lift_one` performs that composition directly: a positive
constant-sectional-curvature metric is scaled by its curvature constant,
lifted, and shown to satisfy the full curvature-one tensor identity on the
cover.  It adds no chart-basis or consumer naturality hypotheses.

`riemannOp_lift_one` further removes the metric lowering, giving the exact
curvature-one operator identity needed by the Jacobi/Cartan route.

## Status

`metricRm_lifted`, `metricRm_lift_one`, and `riemannOp_lift_one` pass focused
verification with no warnings.  The upstream relocation of
`extChartAt_proj_eq` has been refreshed and its temporary duplicate-artifact
seam is closed.

## Progress accounting

- `ham3_space_box` endpoint theorem: 0%.
- Universal-cover curvature normalization producer: 100%.
- Dedicated positive Killing--Hopf machinery overall: approximately 15%.
