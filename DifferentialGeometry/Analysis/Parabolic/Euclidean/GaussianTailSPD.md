# GaussianTailSPD

## Role

This module supplies the dimension-uniform Gaussian tail fact needed by the
Perelman source-variable localization.  Its radius is measured in the same
positive-definite quadratic form that defines the Gaussian, so the result is
uniform over all such forms in a fixed finite dimension.

## Route

`gaussSPDTail_eq` applies the canonical positive square-root equivalence of an
SPD matrix.  The quadratic radius becomes the Euclidean norm, while the
Jacobian determinant cancels the square-root determinant in the normalized
density.  Thus every intrinsic SPD tail is exactly the same standard Gaussian
tail.

The standard tail is handled as a finite `withDensity` measure and continuity
from above.  `gaussSPDTail_unif` then chooses one nonnegative radius for a
given positive `ENNReal` threshold and applies the exact equality for every SPD
matrix.  No eigenvalue bound or compact family of matrices is required.

## Status

Focused verification passes without warnings or placeholders, and the named
module artifact has been refreshed.  `gaussSPDTail_eq` and
`gaussSPDTail_unif` are **100%** for their stated interfaces.
