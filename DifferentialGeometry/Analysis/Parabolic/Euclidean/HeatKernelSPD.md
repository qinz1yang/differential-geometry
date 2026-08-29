# Positive-definite Gaussian normalization

`HeatKernelSPD.lean` is the canonical home for Gaussian identities whose
quadratic form is represented by a positive-definite real matrix.  The proof
uses the existing positive square-root equivalence to reduce the quadratic
form to the standard Euclidean norm, then uses Haar-measure scaling by the
determinant and Mathlib's finite-dimensional Gaussian integral.

The source metric need not agree with the ambient Euclidean norm.  The
determinant factor is therefore essential; downstream L-geometry code should
combine this theorem with its source Gram determinant rather than treating the
source density as one.

The exported results are:

- `spdSqrt_det`, identifying the determinant of `spdSqrtEquiv A hA` with
  `Real.sqrt A.det`;
- `gaussSPD_int`, evaluating the integral of
  `exp (-inner x (A x))` as
  `(Real.sqrt A.det)⁻¹ * pi^(card n / 2)`.

Both results use only finite-dimensional Euclidean-space and positive-definite
matrix hypotheses.  Focused verification passed without warnings.
