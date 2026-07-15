# AllTimesBoundsFlow

## 2026-07-13 short-time alignment

The latest HCG progress was checked against the merged short-time-existence
tensor API.  Two order-zero metric-difference evaluations still used the old
underlying `ContinuousMultilinearMap.sub_apply` route.  They now use the public
`Tensor0SBundle.Tensor0SSpace.sub_apply` theorem, preserving the existing
statements and proof structure.  Two local mechanical linter warnings in the
edited file were also removed.

Focused verification passed without warnings.  This is an integration repair,
not new endpoint mathematics: the theorem status and the HCG machinery and
endpoint percentages remain those recorded in `PROJECT_MAP.md`.

## 2026-07-14 bilinear metric-difference bound

Added `metricDiff_abs_le`, the coefficient-one intrinsic Cauchy--Schwarz bound
for an arbitrary bilinear evaluation of the order-zero metric difference.  It
uses a reference-metric orthonormal basis, `abs_apply_le_sqrt_normSq0S`, and the
existing scalar evaluation theorem `metricDiffCovDerivAt_zero_apply`.

Focused verification passed.  This is a reusable metric-norm producer; it does
not itself prove the scalar Galerkin closure or Perelman noncollapsing endpoint.
