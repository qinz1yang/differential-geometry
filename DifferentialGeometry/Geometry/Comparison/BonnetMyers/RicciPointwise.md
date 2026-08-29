# Pointwise Ricci lower bound from Riemann curvature

## Role

`ricciLowerAt_of_rm` is the pointwise projection of the existing global
`ricciLower_of_rm`.  It converts a Riemann-curvature norm bound at one point
into the Ricci quadratic-form lower bound at that same point.  This is exactly
the input required by the localized Jacobi--Riccati chain on a controlled
metric ball.

## Route

The proof uses a metric-orthonormal basis, the checked component bound for the
Ricci contraction, the unit-sphere quadratic estimate, and homogeneity.  No
flow, ball, compactness, or regular-time hypothesis enters this generic
comparison lemma.

## Verification

Focused verification passed without warnings.

## Next theorem

The next adapter derives this pointwise square-root norm hypothesis from
`FlowMetricBall.IsRmControlled` and supplies the resulting Ricci bound along
the selected Calabi-tail geodesic.
