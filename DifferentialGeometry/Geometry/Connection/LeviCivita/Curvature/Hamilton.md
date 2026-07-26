# Hamilton.lean

## Role

This module owns the static Levi-Civita tensor identity used by the
arbitrary-dimensional Riemann-curvature evolution equation.  It does not own
the time derivative of the metric or curvature, and it makes no Ricci-flow,
compactness, or dimension-specific assumption.

## Status

`hamiltonRm04Id` is implemented and focused-green with no `sorry`, `admit`, or
`axiom`.  It identifies the six canonical second-Ricci derivatives together
with the raw metric-lowering variation as the rough Hessian trace of canonical
`Rm04` plus the explicit quadratic term `hamiltonRmReact`.

The proof is split into reusable geometric steps:

- `canRmRicci` packages the Ricci identity for canonical `nabla^2 Rm04`.
- `canRmHessComm` evaluates one derivative commutator as curvature action.
- `canRicHessSum` reduces the six differentiated-Bianchi terms to the rough
  Hessian trace and five curvature-action contractions.
- Private basis lemmas identify those contractions with the explicit
  arbitrary-dimensional reaction and identify the raw lowering contraction.

The algebra route is structural.  A five-action identity is proved from the
Riemann symmetries and first Bianchi identity, and its sole exchanged double
sum is closed by `Finset.sum_comm`.  No component enumeration over a fixed
dimension is used.

Two final elaboration issues were local and are closed: the lowering proof
needed an explicit change to its local `Ric`/`Rm04` lets plus distribution of a
negative finite sum, and the endpoint needed normalization of `Fin 4` vector
literals after unfolding `hamiltonRmReact`.

## Project accounting

- `hamiltonRm04Id`: 100% implemented, focused-green, and exact-green.  The
  first exact attempt exposed an eta-expansion regression in the separately
  owned upstream `Geometry/Curvature/Realized/Operators.lean`; after its owner
  repaired and refreshed that module, the Hamilton target completed.
- Dedicated static Hamilton machinery in this module: 100%.
- Arbitrary-flow base evolution producer theorem: not yet stated and proved,
  0%.  Its dedicated static and time-variation machinery is about 75% after
  combining this module with the separately owned `Rm04Variation` work.
- `residualStarCosted`: 0%.
- `towerHeatSol`: 0%.
- Unconditional Theorem 3.10: 0%.
- P4 consumer-side machinery remains about 97%; this static identity closes a
  producer brick but does not complete the P4 theorem.

## Next target

Combine `hamiltonRm04Id` with the disjoint time-variation normalization in
`Evolution/Rm04Variation.lean` at the flow evolution layer.  Do not duplicate
either result in this static module.
