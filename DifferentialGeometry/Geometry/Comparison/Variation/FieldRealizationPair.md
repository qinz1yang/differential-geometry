# Paired field realization

## Purpose

`exists_var_pair` realizes two globally `C^8` tangent fields along the same
curve by two globally smooth variations produced from one compactly supported
geodesic-flow construction. The common flow makes pointwise equality of the
two fields propagate to equality of the corresponding variation curves for
every variation parameter. A zero field value gives a stationary variation
curve, so endpoint-fixing follows directly when either field vanishes there.

The compact cutoff is chosen once around the union of the two compact tangent
images over the unoriented closed interval. No completeness hypothesis on the
manifold and no exponential-map smoothness interface are needed.

## Verification

Focused verification passes without warnings. The reusable pair-realization
surface is complete; downstream L-index work may now obtain two variations
whose slices agree wherever the prescribed tangent fields agree, while zero
values give fixed slices at the outer endpoints.
