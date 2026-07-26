# B1 global stage-map ruling

## Architecture

Preserve `StepB1RawInput` unchanged.  The canonical comparison map is the one
global finite-stage map built from the actual normalized source-stage weights,
the direct source-chart to target-chart points, and the unique global minimizer
of the target-stage center energy.  Source slots are proof indices only.  Do not
glue chart-local limit weights and do not introduce a pointwise chart selector.

For a forward map from stage `k` to stage `l`, the frozen center manifold is the
target stage `l`; the reverse comparison map is used only as an approximate
return map.  The exact reverse map required by `StepB1RawInput` remains
`Function.invFunOn` after local diffeomorphism and global injectivity have been
proved.

The frozen quantifier shape

```text
eventually n, exists N_n, forall a b >= N_n, P n a b
```

does not imply the required all-pairs tail under further reindexing.  The next
center producer must give a common threshold, preferably

```text
exists N, forall n a b >= N, P n a b,
```

before the reference manifold is frozen.

## Checked on 2026-07-15

- `CenterOfMass.centerEnergy_congr`,
  `centerAverage.energy_activeFill`, and
  `centerAverage.uniqueMin_activeFill` make zero-weight replacement
  energy-invariant and preserve the unique global minimizer.
- `StepCStageMap.lean` defines `stageTarget`, `HasUniqueStageCenter`, and
  `stageComparisonMap` without a chart selector; `stageTarget_local` supplies
  the manifold-level local-transition decode under the existing chart-source
  premise.
- `StepCStageComparison.uniqueStage_of_fill` identifies any checked local
  filled center branch with the original global stage energy, and
  `stageCompare_eq_cm` proves that the global map equals its selected center.
- `MetricCompactnessInputs.exists_live_cores` returns fixed compact cores
  `C0 alpha ⊆ interior (C1 alpha) ⊆ C1 alpha ⊆ U alpha` on the existing
  subsequence, and the strict inner-core images cover the frozen source ball.
  `exists_atom_supp_fin`, `HasSuppConvData`, `exists_supp_pts_fin`, and
  `MetricCompactBase.exists_supp_cm_fin` retain those cores on the same master
  subsequence as the support-local center solutions.
- `ContDiffBump.radial` supplies the reusable safety clamp.  `StepCStageFill`
  implements the fixed `6/7` activity bump, fixed `7/8` safety bump,
  old-`InterSlot` finite totalization, actual refined weights/points, and full
  configuration convergence for every pair of reindexings tending to
  infinity.  `stagePtsSub_eq_ne` gives exact raw-target agreement at every
  retained nonzero interacting slot.
- `HasSuppConvData` retains the all-stage two-sided transition smoothness
  already proved by its producer's common finite-pair shift; no new endpoint
  input or second source-chart diagonal is used.

All listed files passed focused verification; the canonical stage-map module
and the canonical energy module also passed exact module refreshes.

## Live analytic status

The analytic route is decomposed at native layers.  Metric-jet to spray
convergence is checked algebraic packaging: `MetricKoszul.metricSpray_conv` and
`normalGeodesicSpray_conv` use a proof-independent inverse Gram expression and
introduce no velocity, stage-stay, or endpoint-radius assumption.

The previously recorded analytic stop points are now implemented in live
source.  `MapCInfConvOnCompacts.ode_solutionAt` derives compact-tube containment
and all parameter-jet convergence from limit-trajectory containment; its proof
uses `ode_c0_on_compact`, smooth solution families, `ode_iterated_any`, and
shift removal, with no stage-family stay assumption and no `sorry`.  The exact
local inverse tails `inv_chart_conv` and `inv_chart_tail`, the intrinsic metric
bridges `cov_comp_tail`, `inv_cov_comp_tail`, `fwd_norm_tail`, and
`inv_norm_tail`, the carrier `preapprox_tail`, and
`MetricCompactBase.exists_b1_raw` likewise have complete proof bodies and do
not assume their conclusions.

The current stop is semantic revalidation after the canonical framed-coordinate
migration.  Several B1 metric and inverse consumers still mention raw
`normalChartAt`, `expMapDiffeo`, or `expMapC2Radius`; their old `.olean` files
predate the framed backend.  Therefore the live proof architecture is complete,
but the framed `exists_b1_raw` chain is not yet checked.  See
`B1_MOVING_ROOT_CONSULT.md` for the answered architecture request; its historic
frontier accounting must be read together with this update.

## Forbidden repairs

- Do not change `StepB1RawInput`.
- Do not add a branch-specific field to `MetricCompactnessInputs`.
- Do not glue local limit weights or select a source chart pointwise.
- Do not impose whole-cage target containment or an endpoint-radius assumption.
- Do not identify the reverse comparison map with the exact inverse.

## Accounting

The canonical map-definition seam, nested-core producer, smooth Route-A
configuration convergence, moving ODE stability, exact-inverse convergence,
intrinsic metric bridges, and raw-input assembly all have complete live proof
bodies (100% source implementation, with no local `sorry` or `admit`).

This is not yet a checked framed endpoint.  The current framed source migration
of the B1 metric/inverse consumer stack is complete (100% source
implementation), while its chain-wide framed verification is still 0% pending;
consequently `MetricCompactBase.exists_b1_raw` must not be reported as
framed-green.  The separately named textbook B1 theorem and all unconditional
compactness endpoints remain theorem-level 0%.  Rounded dedicated Step-B/B1
machinery remains about 95%, Chapter 4 machinery about 87%, and whole-HCG
machinery about 60%.
