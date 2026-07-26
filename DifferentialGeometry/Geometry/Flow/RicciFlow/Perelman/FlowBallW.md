# FlowBallW

## Status

`flowball_wform` assembles the verified cutoff, normalization, support-entropy,
and scalar-from-Riemann estimates on a genuine curvature-controlled
`FlowMetricBall` at its distinguished time.

`flowball_w_upper` now applies the checked positive-amplitude approximation and
`w_square_form`.  It produces a strictly positive smooth unit-mass amplitude
whose actual `wFunctional` is bounded by the geometric cutoff estimate plus an
arbitrarily small error.

`exists_sel_w_bound` composes this with the checked dyadic selector.  For every
curvature-controlled ball it returns a nested curvature-controlled subball and
a positive unit-mass amplitude whose actual W value is bounded by
`collapseWConst n + log (Vol(B) / radius(B)^n) + δ`.  The constant is independent
of the ball and the selected dyadic depth.  The proof also retains radius
monotonicity and normalized-volume nonincrease for downstream use.

Focused verification passed without warnings.  The curvature-controlled
flow-ball square-form producer, positive-amplitude W upper producer, and
selected-scale W bound are each theorem-level 100%.  The remaining separate
frontier is a flow-uniform W lower bound reaching the initial slice.

## 2026-07-19

Removed the file-private explicit-ball volume-positivity proof.  All three
uses now call the public `VolumeComparison.edist_vol_pos` theorem from
`Geometry/Comparison/Volume/SmallBall`, keeping the general metric-volume fact
below the Perelman layer.

Focused verification is pending the upstream `SmallBall` source check and
artifact refresh; no local Lean diagnostic has been observed yet.

## 2026-07-23 post-merge check

`FlowBallW` now imports `SmallBall` directly for `edist_vol_pos`.  Focused
verification and the module artifact refresh both passed.
