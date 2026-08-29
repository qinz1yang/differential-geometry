# `CovariantDerivativeScaling.lean`

## Goal

Expose the constant-metric-scaling naturality needed by the Perelman
L-geometry scaling lane without changing the established along-curve API.

## Result

`covDerivAlong_scale` proves that multiplying a Riemannian metric by a positive
constant does not change the covariant derivative of a vector field along a
curve.  The proof works through the existing fixed-chart definition: the Gram
matrix and its inverse scale oppositely, so the Christoffel contraction and
therefore `covDerivAlong` are unchanged.

## Verification

Focused verification passed without warnings.  The file contains no `sorry`,
`admit`, or new axiom.

This is a generic connection-layer bridge.  It does not implement any
L-geometry scaling theorem itself.  `redVolume_anti` remains 0%; the theorem is
a small reusable prerequisite within the current L3 scaling/naturality stage.
