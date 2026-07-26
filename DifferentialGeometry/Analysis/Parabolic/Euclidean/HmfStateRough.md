# HmfStateRough status

## Source theorem

`hmfStateFlux_sub` is the exact difference split for a genuinely
state-dependent principal coefficient.  `hmfStateFluxWt` proves its weighted
critical estimate:
the gradient arm costs `eps + L R`, and the coefficient-difference arm costs
`L Dp`.  Thus the repair is small through the rough state radius rather than
through a fictitious power of the horizon.

`linCarlOn` proves the needed positive-slab localized coefficient estimate,
and `hmfStateFluxCarl` keeps the two critical Carleson arms separate for two
applications of the linear heat-flux bound.

For actual strong HMF coordinates, the expected full-state chain rule makes
the vertical local-addition derivative cancel between `Phi_t` and the leading
tension term.  In that faithful specialization the principal coefficient is
prescribed and this file is used only with `L = 0`.  The genuinely necessary
state-dependent repair is instead the third quadratic difference arm proved
in `HmfStateQuad.lean`.

The file now imports the canonical rough source classes directly from
`RoughCarleson.lean`; it does not depend on the still-unverified
`HmfRoughMap.lean` layer.

## Verification

Source-complete with no placeholder.  Focused Lean verification is queued
behind the single active Ricci--DeTurck edge-energy build.  Until that check
passes, this is unverified machinery and neither endpoint theorem advances
from 0%.
