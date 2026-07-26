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

## Uniform smallness

`joint_jet_small` is now proved in the same low layer.  It assumes joint
spacetime smoothness on `univ ×ˢ S`, `S ∈ 𝓝 t₀`, and `Φ t₀ = 0`, and
concludes eventual uniform-in-space smallness for every jet order `i ≤ p`.
The proof stays scalar throughout: `joint_jet_rfns` gives continuity of the
intrinsic squared fibre norm, a local product patch is extracted at each point,
compactness supplies a finite spatial subcover, and only the finitely many jet
orders are intersected in time.  It does not compare tensor values in different
fibres and does not add a chart-selector hypothesis.

The theorem and its dedicated machinery are both complete (100%).  The first
implementation placed the tensor family, bundle-valued joint-smoothness
hypothesis, and compactness argument in one private patch theorem; elaboration
then timed out at `whnf`.  The successful normal form factors the topology into
the pure scalar private helper `joint_small`, and leaves only the
`joint_jet_rfns` instantiation and zero-jet rewrite in the public theorem.  This
is the reusable performance lesson: scalarize before packaging the compactness
argument, not merely before the final inequality.

## Verification

Focused verification passed without warnings, including the new
uniform-smallness theorem, and the module export passed.
