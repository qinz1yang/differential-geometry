# CostRampBound

## Result

`lRayTail_bound` proves a quantitative terminal-tail estimate for a compact
family of regularized L-rays.  If the compact initial-data set times a closed
square-root-time interval lies in the joint maximal regularized domain, then
one nonnegative constant bounds the absolute action of every terminal segment
by that constant times the segment length.

The proof establishes joint continuity of the fully scalarized regularized
Lagrangian on the maximal ray domain.  Compactness then bounds the Lagrangian,
and the interval-integral norm estimate supplies the linear modulus.  It does
not compare whole moving tangent bundles or introduce a supplied analytic
bound.

`lRayTail_bdd` specializes the compact estimate to a bounded sequence of
initial data by taking the compact closure of its range in the finite-
dimensional model space.

## Verification

Focused verification of the complete file, including the compact-family and
bounded-sequence theorems, passes without warnings or placeholders.

## Frontier

This closes the uniform linear estimate for the action already present on the
terminal part of a bounded minimizing-ray family.  It does not yet construct
the replacement chart ramp connecting a nearby endpoint, so local Lipschitz
continuity of `lCost` remains unproved.  The next producer is the chart-local
terminal replacement with a comparably uniform kinetic bound.

`lCutMulti_null` and `redVolume_anti` remain 0%.
