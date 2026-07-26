# QuadraticBound

## Current status

`ricci_quad_sol` is source-complete and focused GREEN.  It is an
arbitrary-dimensional, pointwise theorem: a bound on the canonical lowered
Riemann norm at one point controls the Ricci quadratic form at that point by
`(finrank E)^2 * sqrt C`.

The theorem reuses the canonical metric-curvature component bound and the
general quadratic-form extension from the unit sphere.  It does not use the
flow equation, a time-domain membership hypothesis, a curvature realization
bridge, HCG data, compactness, or connectedness.

The dedicated theorem is 100% and its exact artifact is current
(`3706/3706`).  This is a supporting algebraic brick only.  The Route B-prime
distance-support theorem remains 0%; its
dedicated producer machinery is about 30%, and the unconditional HCG
compactness theorem remains 0%.

## Consumer migration

`HCGCompactness/MovingShiOpen.lean` now imports this canonical module, uses the
pointwise theorem directly, and deletes its former private duplicate together
with the three imports needed only by that duplicate proof.

The module is also exported by the `Evolution/Ricci.lean` umbrella.  Its import
boundary deliberately avoids `RicciOperatorNormBoundFlow` and
`RmRaisingBridge`, whose reverse dependencies would create an Evolution/HCG
cycle.
