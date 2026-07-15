# RHSUniformFamily

## 2026-07-14 family-uniform RHS producer

`chartRHS_pou_lip` combines the already proved family-uniform Ricci and
DeTurck-Lie component estimates.  For a fixed background and a metric family
with uniform ellipticity plus chart Gram bounds through order two, one positive
constant controls the full Ricci--DeTurck RHS difference by
`chartMetricJet2DiffSup` on every active partition-of-unity chart support.

Focused verification passed.  The first placement inside the much larger
`RHSPointwiseLipschitz.lean` hit repeated verification timeouts without Lean
diagnostics, so the pure family-packaging theorem was moved to this narrow
module.  No mathematical route failed.

This closes a coefficient estimate only.  It does not construct a
low-regularity parabolic solution or a uniform existence interval.

## 2026-07-15 uniform absolute RHS bound

`chartRHS_pou_bnd` now combines the explicit absolute Ricci and DeTurck-Lie
bounds with the existing family-uniform inverse-Gram, Christoffel, and first
Christoffel-derivative producers.  From the same metric-equivalence and Gram
order-zero-through-two inputs, it returns one positive constant bounding every
RHS component for every family member on every active POU support.  Focused
and targeted verification passed.

This supplies forcing magnitude as well as the earlier difference modulus.
It does not supply the first RHS jet or an `H^3 -> H^1` mixed tame estimate.
