# LieSummandLipschitz

## 2026-07-14 family-uniform DeTurck Lie estimate

The file now contains absolute bounds for the DeTurck vector field and its
first coordinate derivative, a reusable algebraic estimate for the chart Lie
summand, and `chartLie_pou_lip`.  The latter gives one family-uniform
`2`-jet Lipschitz constant for the full Lie summand relative to a fixed
background metric, using chart Gram bounds through order two.

Focused and targeted verification passed.  Together with
`chartRicci_pou_lip` this closes the pointwise nonlinear RHS coefficient
estimate.  It does not construct a low-regularity solution or smoothing
interval.

## 2026-07-15 weak-assumption derivative API

The exact first-partial formula `partialDeriv_chartDeTurckVFComp_eq` now uses
the definition by reflexivity instead of the stronger simp lemma.  This
removes unnecessary `SigmaCompactSpace`, `T2Space`, and boundaryless instances
from that formula and the downstream pointwise and compact-family derivative
bounds that genuinely do not use them.  Focused and targeted verification
passed without local warnings.
