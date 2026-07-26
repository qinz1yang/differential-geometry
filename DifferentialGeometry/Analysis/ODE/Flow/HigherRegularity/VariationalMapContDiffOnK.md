# VariationalMapContDiffOnK.lean - Frontier-1 audit correction (2026-06-13)

Step B frontier 1 originally looked like it needed a new fixed-domain theorem for
`hLsp : forall j, ContDiffOn R j (spatialPieceFn Phi) (fixed nesting box)` before
`exists_contDiffOn_flow_Cinfty` could be used.

## Corrected verdict

Do **not** commission a new fixed-domain linear-ODE smoothness theorem yet.  The live tree
already contains the fixed-box Hartman smooth-dependence theorem:

- `IsLocalFlow.contDiffOn_top`
  in `DifferentialGeometry/Analysis/ODE/Flow/HigherRegularity/ContDiffOnTop.lean`;
- `IsLocalFlow.contDiffOn_top_local`
  in `DifferentialGeometry/Analysis/ODE/Flow/HigherRegularity/ContDiffOnTopChartLocal.lean`.

Planner verification: focused read-only Lean check of `ContDiffOnTop.lean` passed, and
`#print axioms` for both the global and local theorem reports only
`[propext, Classical.choice, Quot.sound]`.

## What the audit still usefully pinned

The old finite-order route through `exists_contDiffOn_flow_Cnat` / `flowCkPred_all` and
`exists_isVariationalFlowProjection_of_C` still has order-dependent boxes.  That diagnosis
is useful, but it is not the best next route because the Hartman top-order theorem bypasses
the shrinking-box finite-order extraction.

The nearby APIs checked during the audit:

- `spatialPieceFn_eq_fromAugFlow` and `spatialPieceFn_eq_variationalLinearMapAt`;
- `contDiffOn_fromAugFlow`;
- `IsVariationalFlowProjection` in `VariationalMapContDiffOnK.lean`;
- `exists_isVariationalFlowProjection_of_C` in `VariationalLinearMapSmoothness.lean`;
- `flowCkPred_step` / `augVF`.

## Next real frontier

Wire the existing fixed-box theorem into the chart-phase/geodesic-flow layer:

1. Apply `IsLocalFlow.contDiffOn_top_local` to the chart-phase flow of `chartPhaseVF`
   on the existing nesting box, discharging the local smoothness and orbit containment
   hypotheses for the chart-phase vector field.
2. Package the result as the missing `combined_inf` chart-flow theorem.
3. Use the existing off-zero bridge pattern to prove forward
   `expMap` `ContMDiffAt infinity` / `ContDiffOn R top` on a uniform small ball.

The inverse `normalChartAt`/`expMapDiffeo : PartialDiffeomorph ... infinity` remains a
downstream inverse-function-theorem wiring step after the forward theorem lands.
