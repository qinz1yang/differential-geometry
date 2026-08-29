# `GeneralCurvatureCommutation.lean`

## Pointwise curvature commutation

`cov_commute_at` is verified without warnings.  It proves the two-parameter
covariant-derivative commutator identity at an arbitrary point `(s, t)` from a
single pointwise `C²` hypothesis on the total tangent field.  The corresponding
pointwise `C²` regularity of the base variation is projected from that total
space hypothesis rather than assumed separately.

The proof reuses the fixed-chart `C²` commutator calculation and the pointwise
`covDeriv_chartAt` bridge.  Finite-order locality supplies the nearby slice
germs needed to differentiate the inner covariant derivatives.  No new class,
global smooth-variation hypothesis, or consumer-side wrapper was introduced.

This closes the generic pointwise producer needed by consumers that only use
the commutator at one parameter value.  Global compatibility theorems remain
available for callers that already carry `IsSmoothVariation`.

## Pointwise regularity of `covSnd`

`cov_snd_mdiff_at` is verified without warnings.  A pointwise `C²` total
tangent field at `(s, t)` now produces a pointwise `C¹` total tangent field
after taking the covariant derivative in the second parameter.  The proof
differentiates the fixed-chart formula once and uses finite-order locality only
to identify that formula with the intrinsic covariant derivative near the
basepoint.

The public projections `cov_snd_diff_at` and `cov_snd_fst_at` give the exact
`chartRepAt` differentiability facts in the second and first parameter
directions, respectively.  They are intended for pointwise Jacobi-field
consumers and do not require a global smooth variation.
