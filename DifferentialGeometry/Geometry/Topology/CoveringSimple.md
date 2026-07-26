# CoveringSimple

## Role

`IsLocalHomeomorph.surjective_compact` first upgrades a local homeomorphism
from a nonempty compact source to a connected Hausdorff target to a
surjection: its image is nonempty, open, and compact-closed.
`IsLocalHomeomorph.covering_compact` supplies the stronger structural fact
needed by Cartan globalization: a local homeomorphism from a compact Hausdorff
source to a Hausdorff target is automatically a covering map.

`IsCoveringMap.bijective_sc` is the subsequent global topological upgrade
needed after the positive Killing--Hopf route constructs a covering local
isometry between a round sphere and the normalized universal cover.  It proves
bijectivity from connectedness of the total space and simple connectedness plus
local path connectedness of the base.  `homeomorph_sc` packages the same fact
as a homeomorphism.  `diffeomorph_sc` now combines the same bijectivity theorem
with an existing smooth local-diffeomorphism witness, yielding the actual
global `Diffeomorph`; `coe_diffeomorph_sc` records that its underlying map is
unchanged.

The proof is adapted from the corresponding complete argument in
`frenzymath/Poincare-Conjecture`: lift the identity map to a global section and
use uniqueness of lifts to prove the section is also a left inverse.

No Ricci-flow, metric, chart-selector, or classification assumption is added.

## Status

Focused verification is GREEN.  The file is `sorry`-free.

## Progress accounting

- `ham3_space_box` endpoint theorem: 0%.
- This covering-to-global-diffeomorphism topological brick: 100%.
- Dedicated positive Killing--Hopf machinery overall: approximately 43%.
