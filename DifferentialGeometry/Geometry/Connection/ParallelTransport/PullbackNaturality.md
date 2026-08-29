# `PullbackNaturality.lean`

## Status

Verified warning-free.  This module is the generic weak-regularity layer for
diffeomorphism naturality of vector fields and covariant differentiation along
curves.  It does not introduce a new geometry wrapper or modify the existing
cross-model pullback implementation.

## Public API

- `chartRep_map_diff` transports differentiability of a vector field's fixed
  chart representative under a diffeomorphism.  It assumes only pointwise
  manifold differentiability of the curve and ordinary differentiability of
  the source representative.
- `covAlong_natMDiff` proves naturality of `covDerivAlong` for the native
  same-model pullback metric under the same weak pointwise assumptions.

## Design record

The proof works internally with the existing cross-model pullback metric.  It
splits an arbitrary field along the curve into a smooth ambient extension and a
residual vanishing at the chosen time, proves naturality for the two pieces,
and recombines them by additivity.  The same-model theorem then identifies the
cross-model and native pullback metrics by extensionality of their fiberwise
inner products.

The first verification pass exposed only local integration issues: declaration
ordering, a changed `chartRep_base_diff` interface, and function-equality rewrite
orientation.  Reusing the currently checked smooth-section chart representation
and the existing additive decomposition resolved them.  No mathematical or API
blocker remains, and the final focused verification passed without warnings.

## Project position

The two requested generic bridge declarations are complete (100%), and this
generic weak-regularity sublane is complete (100%).  This file remains
infrastructure only; its L-geometry consumers are now proved in
`Perelman/LGeometry/Naturality.lean`.  Dedicated Perelman L-geometry machinery
is about 30--32%, while reduced-volume monotonicity remains at 0%.
