# ActionDensityGeom

## Result

`exists_c1_of_flat` is the finite geometric assembly producer for strong
L-action density. Given a merely monotone finite subdivision, fixed chart
representatives of the limiting curve, compact chart-target buffers, and
global endpoint-flat `C¹` coordinate approximants, it constructs manifold
curves that:

- are globally `C¹`;
- fix both endpoints;
- remain in the required chart source on every closed piece;
- have exactly the supplied chart coordinates on every closed piece; and
- converge uniformly to the limiting manifold curve on the whole interval.

The result handles repeated nodes directly. The closed-piece identity combines
`flatJoin_eq` away from the left node with a separate node calculation that
propagates endpoint compatibility across repeated nodes. When the subdivision
has no pieces, the endpoint equations force a singleton interval and the
constructed sequence is the constant endpoint curve.

Uniform convergence is not assumed after lifting. On each compact coordinate
buffer, continuity of the inverse extended chart gives uniform continuity;
the coordinate convergence is transported through that inverse and then
assembled over the finite interval cover.

## Placement and verification

The file imports `ChartTimeH1Density` and `ActionFinite`, not `ActionDensity`,
so the analytic density module can import this geometric producer without a
cycle. Focused verification passes without warnings or placeholders.

## Project position

This finite geometric assembly theorem is complete (100%). The final
`lAction_c1_dense` theorem is still not stated or proved here (0%); its remaining
input is the endpoint-flat strong coordinate-density producer and the final
analytic composition with `lAction_chart_lim`. Dedicated minimizer/direct-method
machinery remains roughly 75--82%, dedicated L-geometry roughly 74--78%, P2
below 1%, and the whole Poincare program roughly 3--5%.
