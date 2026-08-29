# `CovariantDerivativeAlong.lean`

## Result

The connection layer now exposes the pointwise reparameterization rule
`covDerivAlong_comp`, the pointwise fixed-chart identity `covDeriv_chartAt`,
and both directions of chart-coordinate differentiability:
`chartRep_base_diff` and `chartRep_diff_base`.  The older globally smooth
wrappers remain compatibility results and delegate to the pointwise API.

These statements use only scalar derivatives and fully applied tangent
coordinates.  They do not compare connection bundle maps or introduce a new
connection interface.

## Verification and use

Focused verification passed without warnings.  The exported module was
refreshed for its L-geometry consumer.  The square-root acceleration proof,
phase reconstruction, and intrinsic uniqueness theorem consume these results.
