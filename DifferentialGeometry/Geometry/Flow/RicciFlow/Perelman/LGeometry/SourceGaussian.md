# SourceGaussian

## Status

Focused verification passes without warnings or placeholders for
`lSrcGram_quad`, `lSrcGauss_eq`, and `lSrcGauss_mass`.

## Route

- `lSrcGram_pd` reuses the canonical positive-definiteness theorem for the
  terminal metric Gram matrix; no second Gram-matrix proof is introduced.
- `lSrcGram_quad` reconstructs a model vector with
  `EuclideanSpace.basisFun.toBasis.sum_repr`, transports the standard basis
  through `chartModelBasis_apply`, and evaluates the Gram quadratic form as
  the intrinsic terminal-metric norm square.
- `lSrcGauss` is the standard source Gaussian written in the exact Euclidean
  coordinates associated with `chartModelBasis`.
- `lSrcGauss_eq` is the thin intrinsic readout: its exponent is the negative
  terminal-metric norm square supplied by `lSrcGram_quad`.
- `lSrcGauss_mass` first pushes `modelHaar` forward by `toEuclidean`, where the
  pushforward is exactly Euclidean volume.  It then uses `gaussSPD_int` for the
  positive-definite source Gram matrix.  The factor `lSrcDensity` cancels the
  inverse square-root determinant, and the remaining power of pi cancels the
  Gaussian integral, giving ENNReal mass one.

The proof stays in ENNReal at the public mass statement and introduces no
unspecified Haar normalization constant.  Real integrals are used only inside
the checked Euclidean Gaussian calculation before conversion back to the
nonnegative integral.

## Project position

This source-normalization brick is complete.  It is dedicated infrastructure
for the small-time reduced-volume limit; it does not by itself prove
`redVolume_zero_lim` or the L-geometry no-local-collapsing endpoint.
