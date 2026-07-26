# HolderPath

## Status

Focused Lean verification passes without local warnings.  The first check
exposed only a missing `ContDiff` import, an underconstrained finite-sum
argument, and unused section variables; those elaboration issues are repaired
without changing any mathematical statement.

## Producer boundary

`eParC2Half` is the minimal extended gauge used by the selected Schauder
route.  It records uniform spatial jets through order two, spatial
exponent-`1/2` control of the second jet, and time exponent-`1/4` control of
that jet.  `IsParC2Half` separately records genuine differentiability and
time continuity, so the default value of `fderiv` cannot create false
regularity.

`eFinParC2Half` and `InHolderBall` lift this to an arbitrary finite set of
chart/component indices.  Extraction lemmas provide concrete `HolderWith`
constants for the Gaussian cancellation estimates.

This file deliberately does not define a new typeclass, global atlas, or
tensor representation.  The next Ricci-flow-side adapter will instantiate the
finite index with the existing active POU charts and `(0,2)` component pairs.
