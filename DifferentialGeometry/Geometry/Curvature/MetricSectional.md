# MetricSectional

## Role

This is the geometric adapter from a sectional-numerator identity to the full
canonical lowered Riemann tensor formula.  It is the first producer needed by
the positive Killing--Hopf route for `ham3_space_box`.

## Route

The canonical `metricRm04` realization supplies first-pair skew, last-pair
skew, and first Bianchi.  The sign-adjusted standard-slot tensor is therefore
an algebraic curvature form.  `AlgebraicForm.zero_of_diag` then polarizes the
sectional identity to all four slots.

`riemannOp_of_rm` then removes the final lowering by applying the metric flat
map and using its injectivity.  Consequently a full lowered-curvature formula
now determines the invariant curvature operator without
`chartRiemannBasisIdentity` or any coordinate-frame hypothesis.

No chart selector, local frame, or new consumer assumption is introduced.

## Status

`metricRm_of_sec`, `metricRm_scale_one`, and `riemannOp_of_rm` pass focused
verification, and the targeted module build is GREEN.  This curvature
producer layer is complete for the normalized universal-cover input; the
global Killing--Hopf classification remains a separate frontier.

## Progress accounting

- `ham3_space_box` endpoint theorem: 0% (its proof is still absent).
- Dedicated curvature-normalization machinery for that endpoint: 100%.
- Dedicated positive Killing--Hopf machinery overall: approximately 15%;
  the Cartan/Jacobi transfer and global sphere classification are still the
  dominant missing pieces.
