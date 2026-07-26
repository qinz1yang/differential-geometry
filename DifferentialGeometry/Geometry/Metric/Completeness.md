# Completeness of a smooth Riemannian metric

## Status

The basepoint-free `RiemannianMetricComplete` predicate and its global
uniform-equivalence transfer are implemented in the canonical metric layer.
Focused verification is green and the source is sorry-free.

## Architecture

The predicate records completeness of the `EMetricSpace` induced directly by a
`SmoothRiemannianMetric`; no pointed-manifold data or connectedness hypothesis
is involved.  `of_uniformEquiv` uses only the lower half of the uniform
quadratic comparison to transfer Cauchy convergence.

## Remaining frontier

Compactness of finite-radius closed extended-distance balls is not yet claimed.
The current intrinsic Hopf--Rinow endpoint and its properness consumer both
carry a global `ConnectedSpace M` instance.  The needed canonical missing API is
a point-pair theorem of the form

```lean
hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top
  (hpq : riemannianEDistOf (I := I) g p q ≠ ⊤)
```

The headline proof and its sphere-propagation helpers currently call the global
`riemannianEDist_ne_top`, so this is a missing canonical API theorem rather than
a call-site rewrite.  It is a medium Lean refactor with no new geometric
analysis.  It must be proved before the disconnected closed-ball theorem can be
added honestly.

## Project accounting

- `RiemannianMetricComplete`: theorem 100%, focused-green.
- `RiemannianMetricComplete.of_uniformEquiv`: theorem 100%, focused-green.
- `RiemannianMetricComplete.closedEBall_isCompact`: theorem 0%; its dedicated
  point-pair Hopf--Rinow machinery is 0%.
- Route B-prime complete-Bernstein endpoint: theorem 0%; this milestone is a
  small generic infrastructure brick.
- Unconditional `compactnessSol`: theorem 0%; whole HCG supporting machinery
  remains approximately 60%.
