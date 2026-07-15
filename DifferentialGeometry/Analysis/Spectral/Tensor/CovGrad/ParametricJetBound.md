# ParametricJetBound

## Purpose

This module extracts the generic compact-slab argument that was previously
available only as private consumer-local code.  A jointly smooth family of
fixed-background mixed tensors now has jointly continuous intrinsic fibre norms
for all spatial covariant jets and an order-indexed family of uniform bounds on
one fixed compact time slab.

## Noncollapsing frontier

The slab is quantified before the derivative order.  Consequently one compact
slab can serve every spectral order `n`, while the bound is allowed to depend on
the jet order.  This avoids the invalid route of intersecting countably many
order-dependent time neighborhoods.

This is only the generic compactness producer.  The remaining coefficient
frontier is to prove joint spacetime smoothness, relative to the fixed terminal
metric, for the exact families `scalarFluxCoeff q (G.metric t)` and
`connTraceCoeff q (G.metric t)`, then feed the resulting common jet envelopes
through envelope-driven variants of the passenger-slot and balanced pairing
estimates.  The existing fixed-field pairing theorems hide coefficient constants
behind existential choices and therefore cannot themselves be supremized in
time.

## Verification

Focused verification passed without warnings.
