# `VolumeTransport.lean` — volume through a metric comparison

Chapter 25 lane (`ch:scn`, `master05b.tex`). Worker W5 for the volume clause of
item 1 of `lem:scn-good-point-buffered-canonical`: the `volume` field of
`CanonicalWitness` (`Chapter25Geometry.lean` L325) and its strict form
`BufferedCanonical.volume_reserve` (`Chapter25Extension.lean` L100).

Namespace `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.Chapter25`.
New file only; no existing file was edited and the module is not yet imported
from any aggregate root.

## What the file establishes

The comparison map `F : PartialDiffeomorph I3 I3 P M ∞` of a
`MetricComparisonOn h g F U times order eps` transports the Riemannian volume of
a compact subset of the model to the Riemannian volume of its image, with the
exact Gram determinant factors in dimension three:

* `(1 - eps) ^ (3/2) * vol_{h s}(K) ≤ vol_{g s}(F '' K)`;
* `vol_{g s}(F '' K) ≤ (1 + eps) ^ (3/2) * vol_{h s}(K)`.

When the source metric enters the comparison as `scaleMetric Q hQ gt` (the
normalization used by `RoundComponent.comparison` and by the rescaled model of
`WindowedModelWitness`), the model reserve `Cm⁻¹ / (R * √R)` becomes a source
reserve `C'⁻¹ / (Q * √Q)` with

    C' = Cm * (R * √R) / √((1 - eps) ^ 3).

For a model normalized to scalar one (`R = 1`, as in
`PointedFlowScalarAtBase model 1`) this is `C' = Cm * (1 - eps) ^ (-3/2)`, which
is exactly the shape of the `volume` field with `C2 := C'`.

## Route actually used

1. `PartialDiffeomorph.toOpensDiffeoCross` (`Topology/Manifold/PartialDiffeomorphOpens.lean`)
   restricts `F` to a genuine cross-model `Diffeomorph` between the open source
   set `U` and its open image `F '' U`, and
   `PartialDiffeomorph.mfderiv_toOpensDiffeoCross` identifies its differential
   with that of `F`. Both are universe- and model-polymorphic, so the source
   manifold `P` and the ambient `M` may live in different universes.
2. `riemannianVolumeMeasure_restrictOpen_apply`
   (`KappaSolutions/OpenRestrictionVolume.lean` L290) identifies the volume of a
   set in the open submanifold with the ambient volume of its image, on both
   sides.
3. `volumeMeasurePreserving_pullbackMetricCross`
   (`KappaSolutions/UpstreamCrossVolumeNaturality.lean` L45) transports the
   ambient volume of `F '' K` to the `Diffeomorph.pullbackMetricCross` volume of
   `K`, through `MeasurePreserving.measure_preimage_emb` with the measurable
   embedding of the subtype diffeomorphism. **This is the recorded earlier
   admission (a `sorry` interface); it is inherited by every volume statement in
   this file.**
4. `Diffeomorph.pullbackMetricCross_inner` plus
   `SmoothRiemannianMetric.restrictOpen_inner` rewrite the pullback metric on the
   open source set into `g.inner (F y) (dF v) (dF v)`, which is exactly what
   `MetricComparisonOn.pullback_eq` and `MetricComparisonOn.equivalence` control.
5. `riemannianVolumeMeasure_le_on` (`KappaSolutions/LocalVolumeOrder.lean` L124)
   is applied twice on the model side, on the measurable set
   `Subtype.val ⁻¹' K` (compact, hence closed, hence Borel), with
   `Module.finrank ℝ ThreeSpace = 3`.
6. `volume_scale_apply` (`Analysis/Integration/Measure/Scaling.lean` L106)
   removes the `scaleMetric Q hQ` normalization, with
   `(ENNReal.ofReal √Q) ^ 3 = ENNReal.ofReal (Q * √Q)`.

## Non-obvious points

* The comparison set `U` of `MetricComparisonOn` is *not* required to be open by
  the structure, and in `WindowedModelWitness` it is a closed ball. The volume
  theorems therefore take a separate **open** `V` with `K ⊆ V ⊆ U` and
  `V ⊆ F.source`. A closed-ball comparison is used through `interior U` or
  through the corresponding open ball; a `Set.univ` comparison
  (`RoundComponent`) can use `V := F.source`.
* Instances for the open subtypes are not available globally and are introduced
  inside the proof:
  `ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace _`,
  `Manifold.locallyCompact_of_finiteDimensional I3`, `IsOpen.locallyCompactSpace`
  and then `SigmaCompactSpace` by instance search. They must not appear in the
  public statements, which is why the subtype measures are confined to proofs.
* The Borel measurable-space instances are the file-local `borel` ones, matching
  the way `riemannianVolumeMeasure` is defined in
  `Analysis/Integration/Measure/Invariance.lean` and used in
  `LocalVolumeOrder.lean` / `OpenRestrictionVolume.lean`. The `Opens` subtype
  variants are declared explicitly because the generic one carries
  `SigmaCompactSpace` in its signature.
* The lane convention `attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup …`
  is deliberately **not** used here: `Chapter25Geometry.lean` elaborates
  `MetricComparisonOn` with the default tangent-space instances, and the
  hypotheses of these theorems must match the structure fields.
* `mul_le_mul_left'` does not exist in this Mathlib pin; `mul_le_mul' le_rfl h`
  is the working monotonicity lemma for `ℝ≥0∞`.
* `positivity` cannot prove `0 ≤ (1 - eps) ^ 3` (odd power, sign from a
  hypothesis); `pow_nonneg h1e.le 3` / `pow_pos h1e 3` are used instead.
* Positivity of the model constants `R`, `Cm` is not needed for the transported
  inequality (both sides degenerate to `0` when they vanish), so those
  hypotheses were dropped; the positivity of the transported constant is the
  separate lemma `volume_reserve_constant_pos`.

## Public declarations

* `MetricComparisonOn.inner_image_bounds`
* `riemannianVolumeMeasure_image_sandwich`
* `MetricComparisonOn.volume_image_ge`
* `MetricComparisonOn.volume_image_le`
* `volume_reserve_constant_pos`
* `volume_reserve_image_of_scaled_comparison`
* `CompactDomain.map_volume_reserve`

Private helpers: `exists_opensDiffeo_of_subset_source`,
`comparison_volume_bounds`, and four file-local Borel instances.

## Verification

Focused check from the repository root, one `lean.exe`:

    LEAN_NUM_THREADS=2 lake env lean \
      DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/VolumeTransport.lean

2026-09-11: empty output, `real 0m32.075s` (run taken in a window with
`tasklist | grep -c -i lean.exe` equal to `0` and ~12.5 GB free physical
memory). No warnings; no `sorry`, `nolint`, `maxHeartbeats`, `maxRecDepth`,
`skipKernelTC` or `set_option backward.*` in the file, and no `show` tactic.

### Axiom audit

`#print axioms` was run on a scratch copy of this file (same imports, the seven
`#print axioms` commands appended before the closing `end`), so no artifact
refresh was needed. Command
`LEAN_NUM_THREADS=2 lake env lean <scratch copy>`, `real 0m34.745s`:

* standard only (`propext`, `Classical.choice`, `Quot.sound`):
  `MetricComparisonOn.inner_image_bounds`, `volume_reserve_constant_pos`;
* standard plus `sorryAx`: `riemannianVolumeMeasure_image_sandwich`,
  `MetricComparisonOn.volume_image_ge`, `MetricComparisonOn.volume_image_le`,
  `volume_reserve_image_of_scaled_comparison`, `CompactDomain.map_volume_reserve`.

A second scratch fixture (`real 0m25.025s`) audited the upstream inputs:
`volumeMeasurePreserving_pullbackMetricCross` is the only one carrying
`sorryAx`. `riemannianVolumeMeasure_le_on`,
`riemannianVolumeMeasure_restrictOpen_apply`, `volume_scale_apply`,
`PartialDiffeomorph.toOpensDiffeoCross`,
`PartialDiffeomorph.mfderiv_toOpensDiffeoCross`,
`Diffeomorph.pullbackMetricCross`, `Diffeomorph.pullbackMetricCross_inner`,
`SmoothRiemannianMetric.restrictOpen` and `CompactDomain.map` are all
standard-only. So the single inherited admission is the cross-model volume
naturality interface.

Host note: on this machine the check aborts at import time with
`failed to read file '….olean'` (a different module each time, toolchain or
project) whenever another large `lean.exe` is running. It is a host glitch, not
a proof failure; the run must be repeated in a window with no competing Lean
process. A retry loop that waits for `tasklist | grep -c -i lean.exe` to reach
`0` and for at least ~7 GB of free physical memory was needed to obtain a clean
run.

## Remaining obligations

* `volumeMeasurePreserving_pullbackMetricCross` is a `sorry` interface; every
  volume statement here is conditional on it. `MetricComparisonOn.inner_image_bounds`
  and `volume_reserve_constant_pos` do not use it.
* This file does not build a `CanonicalWitness`. The consumer still has to
  supply, for the buffered canonical witness: the model volume reserve
  `Cm⁻¹ / (R * √R) ≤ vol_k(model domain)`, the open set `V` between the domain
  and the comparison set inside `F.source`, and the identification of the
  transported constant with the `C2` actually carried by the witness.
* The module is not imported from `DifferentialGeometry.lean` or any lane
  aggregate; it needs a named artifact refresh before a downstream Chapter 25
  file can use it.
