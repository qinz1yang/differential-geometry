# GPT Pro consultation: arbitrary-dimensional Hamilton base evolution

> **Resolved 2026-07-22.**  The focused- and exact-green theorem
> `rm04Base_of_solution_any` in
> `Evolution/HamiltonBaseProducer.lean` proves the requested arbitrary-
> dimensional fixed-basis flow identity directly from `IsSolutionOn`.  The
> remainder of this file is retained as the historical consultation record;
> it is no longer the active P4 blocker.

## Repository context

Repository: <https://github.com/liao9yuan/differential-geometry>

Work on the aligned short-time-existence branch
`codex/short-time-existence-align`.  The current local HEAD is
`79cfa7cba5c87ccb471389a80db54593e470ca40`; the earlier remote review used
baseline `3e4767695e3229604d512236a1da039b0bcb77e0`.  Local uncommitted changes
described below may not be visible remotely.

This request concerns the trusted analytic producer for HCG compactness P4.
Do not add HCG assumptions, theorem-equivalent wrappers, a compactness
assumption, or a dimension-three/Weyl-flat route.

## Corrected live state

The direct arbitrary-dimensional architecture is accepted: produce one costed
whole residual and then `TowerHeatBoundOn`; do not force the old fixed-cost,
per-`j` `IteratedRmTowerOn.starBound` contract.

The following local declarations are implemented and focused-green in
`DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/StarSum/ResidualCost.lean`:

- `rmGammaCost`, `rmResidualCost`, and `rmTowerCost`, with nonnegativity;
- `e0Field_cost_any`, proving exact cost `12 * card(Idx)^2` for every finite
  index type;
- `rmBaseReact`, the explicit eight-double-trace quadratic curvature
  expression represented by the existing `e0Field`;
- `e0Field_comp_any`, proving the component realization of `rmBaseReact` in
  every finite orthonormal basis;
- the `Fin 3` specialization agrees with the existing checked recurrence.

`BernsteinShiHigher.lean` also has focused-green
`towerReactionSum_mono` and `TowerHeatBoundOn.mono_cost`.

## Important premise correction

The prior review said that the all-order component time derivative was already
available from `iteratedRmComp_hasDerivWithinAt`.  In the live source that
theorem is conditional: it requires the level-zero `partial_t Rm04` derivative
identity as an input.  It therefore cannot generate the base Hamilton
curvature evolution from `IsSolutionOn`.

Generic infrastructure that does exist:

- `Evolution/Connection/Rm13DerivProducer.lean`:
  `rm13Deriv_of_solution`;
- `Evolution/UhlenbeckBaseProducer.lean`:
  `realizedRmBase_timeDeriv`, whose derivative is still the expanded
  `nabla^2 Ric` plus lowering/metric terms;
- `Evolution/TowerSwapRegularity.lean`: positive-tail derivative and swap
  regularity (currently under `CompactSpace M`);
- generic curvature trace, Bianchi, Ricci-identity, lowering, and metric-trace
  APIs under `Geometry/Curvature` and `Tensor/RSTensor`.

The generic Uhlenbeck cancellation theorem in `Evolution/Uhlenbeck.lean`
still consumes a pre-Uhlenbeck curvature evolution predicate as an input.  It
does not produce that predicate from `IsSolutionOn`.  The existing
`rm04Base_of_sol` solution producer in `UhlenbeckBaseProducer.lean` is a
dimension-three Weyl-flat route.

The successor residual implementation in `Evolution/StarSum/TimeRecursion.lean`
is sorry-free but hardcoded to `Fin 3`.  It should be generalized only after
the arbitrary-dimensional base identity is settled.

## Exact target brick

We need a theorem, owned at the lowest natural Ricci-flow evolution layer,
whose semantic conclusion is the component derivative identity

```text
partial_t Rm04 = roughLap Rm04 + rmBaseReact
```

at a regular time and point, in an arbitrary finite orthonormal basis, for a
general finite-dimensional Ricci-flow solution.  Equivalently, it should
produce the pre-Uhlenbeck
`Riemann04BTensorWithRicciDriftEvolutionInFrameOn` data expected by the generic
Uhlenbeck theorem, with the residual identified with the checked `e0Field` /
`rmBaseReact` realization.

The expected starting point is `realizedRmBase_timeDeriv`; the missing step is
to convert its expanded second covariant derivatives of Ricci, using contracted
second Bianchi and Ricci commutation identities, into the rough Laplacian of
`Rm04` plus the quadratic curvature expression.

## Questions

1. Check `rmBaseReact` / `e0Field` against the repository's curvature sign,
   lowering, metric-trace, and Uhlenbeck conventions.  Is this the correct
   quadratic residual for the pre-Uhlenbeck evolution?
2. What is the shortest mathematically valid route from
   `realizedRmBase_timeDeriv` to the target identity in the current API?
3. Which existing declarations should be reused for the second Bianchi
   identity, Ricci trace, covariant-derivative commutation, lowering, and
   `roughLap` realization?  Distinguish genuine theorems from predicates that
   merely package the desired identity as an input.
4. Give the smallest ordered list of new lemmas, proposed signatures, and
   owning files.  Keep one genuine frontier visible rather than introducing
   several assumption records.
5. If the current API lacks the needed uncontracted/contracted second-Bianchi
   to rough-Laplacian bridge, identify the smallest reusable
   `DifferentialGeometry` lemma that should be added and its natural module.
6. Once the base theorem exists, is generalizing the `Fin 3` successor
   recursion in `TimeRecursion.lean` mechanical?  Identify any hidden
   dimension-three dependencies before recommending that edit.

Please return a feasibility verdict and a file-by-file implementation plan.
Do not claim the arbitrary-dimensional `residualStarCosted` or `towerHeatSol`
theorem complete merely because the cost ledger and component expression are
checked.

## Honest status

- arbitrary-dimensional Hamilton base-evolution theorem: 0%;
- `residualStarCosted`: 0%;
- direct `towerHeatSol`: 0%;
- dedicated direct-tower machinery: about 60-65%;
- complete-noncompact Bernstein theorem: 0%, with about 30-35% dedicated
  machinery;
- unconditional MSM135 Theorem 3.10: 0%; dedicated P4 consumer machinery is
  about 97%.
