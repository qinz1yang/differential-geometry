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

All listed files passed focused verification; the canonical stage-map module
and the canonical energy module also passed exact module refreshes.

## Exact analytic stop point

Actual finite-stage weights already have all-pairs `C^infinity` convergence.
The first target-side mismatch is support-sensitive: the direct target
transition is known to enter the controlled target ball only when its actual
weight is nonzero.  Existing tuple convergence asks for every slot to be smooth
and mapped into its domain on the whole source core.  Pointwise `activeFill`
does not supply that smoothness.  The route therefore needs either a smooth
support filler agreeing with direct targets at every nonzero-weight slot, or a
support-aware averaging/center-equation convergence theorem.

Independently, existing `existsCmExtension` and `cmExt_contDiffOn` handle one
fixed center equation.  They do not provide a common parameter neighborhood or
`C^infinity` convergence for a sequence of moving target-stage equations.  A
compact-graph stability theorem for convergent implicit equations is genuinely
missing, as is its HCG instantiation from normal-coordinate metric convergence
to center-equation convergence on a common tube.

After those two bridges, the remaining large producers are exact-inverse
`C^infinity` convergence and the chart-to-intrinsic
`tensor02CovDerivNormWith` bridge.

## Forbidden repairs

- Do not change `StepB1RawInput`.
- Do not add a branch-specific field to `MetricCompactnessInputs`.
- Do not glue local limit weights or select a source chart pointwise.
- Do not impose whole-cage target containment or an endpoint-radius assumption.
- Do not identify the reverse comparison map with the exact inverse.

## Accounting

The canonical map-definition seam and nested-core producer are each 100%.
The all-pairs stage-map chart-tail theorem, concrete `StepB1RawInput` producer,
and textbook B1 theorem remain 0%.  Rounded dedicated Step-B/B1 machinery stays
about 94%, Chapter 4 machinery about 86%, and whole-HCG machinery about 57%.
All compactness endpoints remain theorem-level 0%.
