# Riemannian distance scaling

## State — 2026-07-09

`DistanceScaling.lean` is checked without `sorry`.

- `riemannianEDistOf g` exposes Mathlib's path-length extended distance with
  the Riemannian metric explicit and locally resolves the tangent-norm instance
  diamond in favor of `g`.
- `edistOf_scale` proves `d_(c g) = sqrt(c) d_g` for `c > 0` by expanding the
  path infimum, scaling the metric integrand, pulling the constant through the
  lintegral, and commuting it through both infima.
- `edistBall_scale` proves equality of ball carriers when the metric is scaled
  by `c` and the radius by `sqrt(c)`.

`Perelman.FlowMetricBall.setAt` now uses `riemannianEDistOf` directly, so its
carrier cannot silently fall back to the project's background tangent norm.

## Role in noncollapsing

Together with `Analysis/Integration/Measure/Scaling.lean` and the existing
curvature scaling in `ParabolicRescaling.lean`, this closes the raw geometric
inputs for parabolic kappa-invariance.  `Perelman/ScaleTransfer.lean` consumes
these laws and proves the ball-level and below-scale transfer theorems.

The distance/ball sublane is 100%.  Perelman's analytic no-local-collapsing
producer and `ham3_noncollapse` remain theorem-level 0%; whole HCG machinery
remains about 45%, with HCG endpoints at 0%.

## Metric monotonicity — 2026-07-17

`edistOf_mono` is now checked without `sorry`.  It states that pointwise
quadratic-form domination `g.inner x v v ≤ h.inner x v v` implies
`riemannianEDistOf g x y ≤ riemannianEDistOf h x y`.  The proof stays at the
canonical path-length layer: square root, `ENNReal.ofReal`, and the lintegral
preserve the pointwise order, after which both path infima preserve it.

This helper theorem is complete (100%).  It adds no geometric assumptions or
parallel distance API; it is a small reusable input for downstream metric
comparison arguments.  It does not by itself change the theorem-level status
of the HCG compactness endpoints, which remain 0%.

## Quadratic comparison — 2026-07-23

`edistOf_le_of_quad` and `le_edistOf_of_quad` are focused-green and
sorry-free.  They convert pointwise upper or lower quadratic-form comparison
with factor `c > 0` into the corresponding `sqrt c` comparison of
`riemannianEDistOf`.  Both are short consequences of `edistOf_mono` and
`edistOf_scale`; no second distance construction or completeness hypothesis is
introduced.

This closes the reusable metric-to-distance comparison plumbing (100%).  It is
only supporting infrastructure for the complete-noncompact Shi route:
solution-generated `ShiCutoffData` remains theorem-level 0%, the correct
complete-noncompact Shi theorem remains 0%, its dedicated P4 consumer
machinery remains about 97%, and the whole HCG support machinery remains about
60%.

