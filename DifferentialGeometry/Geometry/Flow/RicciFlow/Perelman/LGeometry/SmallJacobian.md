# SmallJacobian

## Purpose

This module starts the short-time Jacobian normalization in fixed tangent
coordinates.  The key first-order producer is `lJacCoord_zero_lim`: after
division by `2s`, a regularized L-Jacobi field converges to its prescribed
initial tangent vector in the fixed trivialization at the base point.

The proof uses the native regularized Jacobi equation, its zero value and
initial covariant derivative, and fixed-chart covariance.  It never compares
whole moving bundle maps.

## Verification

The fixed-coordinate producer `lJacCoord_zero_lim`, the normalized Gram limit
`lNormGram_lim`, and the final determinant/density producer
`lExpDen_zero_lim` have passed warning-free focused verification.  The private
scaling lemma carries only the assumptions used by its scalar Gram identity.

## Next frontier

After the module artifact is refreshed, downstream small-time reduced-Jacobian
work can reuse `lExpDen_zero_lim`.  Its proof applies the coordinate limit
entrywise to a fully evaluated moving-metric Gram matrix, then uses determinant
and square-root continuity together with the positive square-root-time scaling.
