# CurvatureBound

## Status

`scalar_le_of_rm` converts `FlowMetricBall.IsRmControlled` into the scalar
upper bound required by the cutoff W-form estimate, throughout the actual
backward parabolic cylinder.

Focused verification passed without warnings.  The exact invariant route is
`r⁴ |Rm|² ≤ 1`, then square-root monotonicity, then `scalar_abs_le_rm`; no chart
frame or auxiliary curvature assumption is exposed to consumers.
