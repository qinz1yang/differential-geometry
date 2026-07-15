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

