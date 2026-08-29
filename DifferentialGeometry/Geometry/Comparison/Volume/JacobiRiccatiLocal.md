# Pointwise mean Riccati bound

## Role

`mean_riccati_on` is the localized form of the existing mean Riccati
inequality.  It replaces the global `RicciBoundedBelow` hypothesis by the one
Ricci quadratic-form inequality actually used at the current point and tangent
vector.  This is the first comparison brick needed to construct a Calabi
distance upper support from curvature known only on a metric ball.

## Route

The proof reuses the checked derivative identity, curvature-trace identity,
and shape Cauchy--Schwarz estimate from `JacobiRiccati.lean`.  It changes only
the source of the single Ricci inequality; no tensor representation is
unfolded and no global comparison assumption is introduced.

## Verification

Focused verification passed without warnings.

## Next theorem

After this pointwise derivative estimate is green, the next producer is its
along-geodesic interval comparison, which will feed the ball-local Calabi
distance support `dist_calabi_on`.
