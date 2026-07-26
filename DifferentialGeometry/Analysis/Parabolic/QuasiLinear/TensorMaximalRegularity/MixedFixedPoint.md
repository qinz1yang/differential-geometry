# MixedFixedPoint

This file provides the nonlinear maximal-regularity fixed-point cell needed by
the low-regularity Ricci--DeTurck route.  It combines a critical arm
`N2 : H^(a+2) -> H^a` with a subcritical arm `N1 : H^(a+1) -> H^a`.

## Proved

- `mixedMap_dist_le`: the forcing map has contraction modulus
  `L2 * (1 + T) + L1 * (2 * sqrt T)`.
- `mixedMap_contract`: the map is a Banach contraction when that explicit
  modulus is less than one.
- `mixed_strong_exists`: the fixed point produces the expected maximal-
  regularity strong solution and forcing identity.
- `mixed_strong_unique`: two forcing fixed points of the same mixed equation
  agree, as do their Duhamel solution maps.

The map, contraction, existence, and uniqueness chain passed a clean focused
source check and contains no `sorry`, `admit`, or new axiom.  The first proof
attempt exposed only a representation mismatch between `dist` and the norm of
a difference; rewriting both sides explicitly closed it.  A second attempt at
the uniqueness specialization needed the definition of `Function.IsFixedPt`
exposed with `change`; no mathematical hypothesis was altered.

The explicit uniform-horizon cell is also proved and focused green:
`mixedHorizon_pos`, `mixedHorizon_le_one`, and `mixedHorizon_small` choose a
positive horizon depending only on `L2` and `L1` once the genuinely critical
constant satisfies `2 * L2 < 1`.  After the missing
`MaximalRegularity.Synthesis.olean` reappeared, the complete file passed a
clean focused source check.  The temporary failure was only a missing-artifact
obstruction and did not require any theorem or hypothesis change.

## Remaining use-site work

The Ricci--DeTurck remainder still has to be packaged as two globally defined
Nemytskii arms (or as an equivalent closed-ball contraction) whose constants
are supplied by the concrete low-path coefficient jets.  This file does not
assume that packaging and therefore does not move the frontier.

- Mixed fixed-point core: 100%.
- Explicit horizon wrapper: 100%.
- Concrete low-regularity Ricci--DeTurck solver: 0%.
- `ricci_flow_unif_existence`: 0%.
- `ricci_flow_forward_unique`: 0%.
