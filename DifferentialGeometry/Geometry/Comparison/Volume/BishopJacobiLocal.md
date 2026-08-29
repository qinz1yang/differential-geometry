# Along-geodesic Jacobi comparison

## Role

`curveMean_le_on` upgrades the pointwise `mean_riccati_on` estimate to the
usual hyperbolic-model mean comparison on an interval, assuming the Ricci
quadratic-form bound only along that curve.  It is the comparison input needed
for radial geodesics that remain inside a controlled metric ball.

## Route

The proof follows the checked `curveMean_le_hyp` argument.  Its derivative and
Riccati inequalities now invoke `mean_riccati_on` at each parameter; the
density-ratio derivative and scalar comparison machinery are reused unchanged.

## Verification

Focused verification passed without warnings after the genuinely consumed
pointwise module was refreshed.

## Next theorem

After verification, specialize this interval theorem to radial Jacobi fields
under a Ricci bound known only on the image of the radial geodesic.  That is the
last comparison step before the local Calabi distance support.
