# `BoundedCurve.lean`

## Result

`exists_smooth_curve` constructs a globally defined `C∞` curve through any
manifold point with any prescribed tangent vector, while keeping its entire
range inside an arbitrary open neighborhood of that point.

The construction uses the centered extended chart and a bounded sine
parameter.  A coordinate ball contained in the chart image of the requested
neighborhood supplies the amplitude bound, and the extended-chart inverse
derivative identifies the initial velocity intrinsically.

The result now preserves the infinity-order regularity already supplied by
the sine parameter and extended-chart inverse.  This lets covariant
chain-rule consumers use the curve without an artificial finite-order loss.

## Placement and scope

This is a generic comparison/variation producer.  It uses no Riemannian metric,
completeness, compactness, or Ricci-flow assumptions, and it does not expose
chart or tangent-bundle representation details in its statement.

The helper theorem itself and its dedicated machinery are complete (100%).
Downstream `LocalBranch` completion is separate and is not counted as part of
this theorem.

## Verification

Focused verification passed without warnings.  The file contains no
`sorry` or `admit`.
