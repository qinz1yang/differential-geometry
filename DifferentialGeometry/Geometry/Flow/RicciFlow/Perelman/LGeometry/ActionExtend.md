# Endpoint extension of regularized L-curves

## Result

`exists_lRegExtOn` extends a curve satisfying the full intrinsic regularized
L-geodesic triple on `(a, b)` through both endpoints, while agreeing with the
original curve on `[a, b]`.  It returns a positive radius on which the curve
satisfies regular-time membership, manifold differentiability,
differentiability of its moving chart velocity, and the intrinsic acceleration
equation on the open interval `(a-e,b+e)`.  `exists_lRegExt` preserves the old
closed-interval interface as a restriction wrapper.

The theorem uses no compactness, sigma-compactness, or minimizing hypothesis.

## Proof route

The one-sided chart derivatives of the original `C^1` curve prescribe initial
velocities for two local curves supplied by `exists_lRegCurve_at`.  A piecewise
curve uses these local solutions outside `[a, b]` and the original curve on the
closed interval.  Fixed-chart velocity phases are stitched continuously at the
endpoints.  The local radii are also shrunk inside the open preimage of
`D.regular`, so the open certificate does not silently assume time regularity.
Punctured phase derivatives are promoted by
`hasDerivAt_of_punct`; the resulting phase equation reconstructs the intrinsic
acceleration identity.  Curve-germ and fully applied velocity equalities then
transport the interior and exterior triples through `lRegData_congr`.

The native congruence theorem for `covDerivAlong` is imported from the
exponential/Jacobi layer.  No reference-tree code is imported or copied.

## Verification

Focused verification passed without warnings.  The file contains no
`sorry` or `admit`.

## Progress

- `exists_lRegExtOn` and its `exists_lRegExt` wrapper: 100% proved and
  focused-verified.
- Dedicated endpoint-extension machinery: 100% for this brick.
- Generic reused phase, punctured-derivative, and curve-germ infrastructure:
  100% available for this brick.
- `redVolume_anti`: 0%; this theorem does not prove reduced-volume
  monotonicity.
- The full Perelman L-geometry program remains a larger downstream project;
  this endpoint-extension brick is only a small supporting component.
