# Field realization

## Implemented surface

`exists_var_fix_ends` realizes a globally `C^8` tangent field along a curve as
the transverse field of a globally defined smooth variation. If the field
vanishes at the two selected parameter values, the variation fixes those
endpoints for every variation parameter.

The construction takes the compact image of the closed parameter interval in
the tangent bundle, chooses a smooth compactly supported cutoff equal to one
near that image, multiplies the geodesic vector field by the cutoff, and uses
its complete global flow. Projecting the flow gives the variation. Near the
initial tangent data the cutoff is one, so the projected flow derivative is
the prescribed field. A zero initial tangent vector is stationary, which
gives the two fixed endpoints.

This route does not use ordinary or intrinsic exponential-map smoothness and
does not require completeness or a metric-space structure on the manifold.
The current interface asks for a globally `C^8` total-space field; extending a
field given only near the compact interval would require a separate smooth
extension theorem.

## Verification and next use

Focused verification and the targeted module export pass without warnings.
The theorem is ready to combine with `lRegIndex_nonneg_var`. The remaining
transfer must use an honest almost-everywhere interval congruence for the
regularized index density, since equality of fields on a closed interval does
not assert equality of their derivatives at the two endpoints.
