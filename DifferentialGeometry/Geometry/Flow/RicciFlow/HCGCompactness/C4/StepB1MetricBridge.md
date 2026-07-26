# StepB1MetricBridge

## Framed migration status (2026-07-18)

The canonical framed-coordinate source migration is complete.  Focused Lean
verification and the exact module refresh both pass against the current framed
Stage-C and H6 dependency chain.

- `HasStageJetData.coeff_tail` now defines its source and target chart readout
  with `NormalCoordinates.framedChartAt`.
- `HasStageJetData.chart_conv` now takes the framed source-chart `MapsTo`
  premise and proves convergence for the framed stage-map readout.
- `HasStageJetData.pb_conv` now uses framed source and target charts throughout.
  Its phase-radius smoothness proof consumes `phaseRadius_exp` at its canonical
  `expRadiusGp / 4` target and enlarges only to `expRadiusGp`, using
  `expRadiusGp_pos`; the obsolete raw `expMapC2Radius` seam is gone.
- `HasStageJetData.pb_jet_tail` now exposes the corresponding framed source
  premise and framed two-stage coefficient family.

No theorem was renamed, no wrapper or new hypothesis was added, and
`normalCoordMetric` remains the already-canonical framed metric.  Source and
diff review also pass.

## Previously verified producer state

Before the canonical framed-coordinate migration, the source-chart coefficient
lane was focused-green.  The mathematical roles of the producers remain:

- `MapCInfConvOnCompacts.pullbackAlong` packages moving evaluation of a
  bilinear-form field, convergence of the derivative of a moving map, and the
  polynomial pullback contraction.
- `pullback_sub_norm` gives the order-zero perturbation estimate used by the
  direct all-pairs comparison.
- `HasStageJetData.coeff_tail` proves, on the retained `C0` core and under the
  honest smaller-source-ball point hypotheses already required by the stage
  jet tail, that the actual target-stage metric pulled back by the actual
  stage chart map is uniformly close to the source-stage normal metric.  It has
  one common rectangular tail in the source and target stage indices.
- `HasStageJetData.chart_conv` converts the retained all-order stage jet tail
  into `MapCInfConvOnCompacts` convergence to `id` along arbitrary cofinal
  source/target stage sequences, assuming eventual source membership on the
  fixed coordinate set.
- `HasStageJetData.pb_conv` combines that chart convergence with the retained
  moving normal metrics.  A compactly nested pair
  `closure V ⊆ W ⊆ interior (C0 alpha)` supplies the honest buffer needed
  to patch the finite prefix and apply the moving pullback theorem.  The actual
  pullback coefficients converge in `C^infinity` on `V` to `gInf alpha`.
- `HasStageJetData.pb_jet_tail` applies the generic bad-sequence extraction to
  obtain one rectangular all-pairs threshold through every requested finite
  derivative order on a compact `K ⊆ V`.

No new `MetricCompactnessInputs` field, endpoint radius assumption, glued
weight family, or chart selector was introduced.  A route through uniform
continuity of nested continuous-linear-map spaces was rejected because it
exposed an unnecessary instance diamond; the checked order-zero proof instead
uses the existing H6 `metricC 1` bound and a segment mean-value estimate.

## Next honest seam

The all-order theorem is conditional only on the local geometric premise it
actually needs: a rectangular tail on which the fixed larger coordinate patch
maps back into the smaller source ball.  The producer-owned intrinsic/source
buffer lane should discharge that premise on the finite local cover.  Once it
does, finite maximization over source charts gives the global compact source
tail.

After that local premise is wired, the remaining metric work is:

1. combine convergence of the pullback coefficients and the source-stage
   coefficients to obtain the finite-order coefficient difference directly;
2. convert those coordinate derivatives into the intrinsic
   `tensor02CovDerivNormWith` bounds on the finite chart cover;
3. repeat the bridge for the exact local inverse, not for the approximate
   reverse stage map.

The first item is local convergence algebra.  The second is the genuine new
chart-to-intrinsic covariant-tensor bridge.  The third depends on the separate
exact-inverse convergence lane.

## Honest accounting

- Live framed `HasStageJetData.coeff_tail`, `chart_conv`, `pb_conv`, and
  `pb_jet_tail`: source migration and current module verification complete
  (100%).
- Arbitrary finite pullback-coefficient jets and their comparison with the
  moving source metric have complete live proof bodies in the downstream
  `cov_comp_tail`, `fwd_norm_tail`, and `inv_norm_tail` chain.  Those theorems
  are not yet framed-revalidated because their consumer files still require
  semantic migration.
- The chart-to-`tensor02CovDerivNormWith` producer and the exact-local-inverse
  route are implemented in live source; they are no longer analytic theorem
  frontiers.  Their current framed chain verification remains pending.
- `MetricCompactBase.exists_b1_raw`: proof body complete with no local
  `sorry`/`admit`; not yet framed-green until the metric/inverse stack is
  migrated and checked.
- Textbook Step B1 theorem: 0%.
- Repository-wide rounded machinery estimates remain the project-map figures:
  about 95% for Step-B/B1, 87% for Chapter 4, and 60% for the whole HCG
  program.  These are infrastructure estimates; the HCG endpoint theorems
  remain 0%.
