# `AncientKappaFixedCompactness.lean`

`thm:ksol-fixed-kappa-compactness` restated for sequences of genuine ancient
`κ`-solutions, and re-exported through the Chapter 25 convergence interfaces.

## Scope

`KLimThreeDimensionalBounded.exists_fixed_kappa_compactness` takes a sequence
satisfying the internal Harnack-limit package `KLim`
(`def:ksol-Harnack-limit-package`). Downstream consumers (Chapter 25's
`Upstream.fixed_kappa_compactness` slot) present their sequences as
`IsAncientKappaSolution` (`def:red-kappa-solution`). This file bridges the two
with `StandardHarnackLimit.ancientKappaThree_toKLim` and re-exports the limit
data in three shapes.

## Public declarations

| name | content |
| --- | --- |
| `ancientPointedFlowSeq` | `ℕ → PointedFlowData I3 ancientTimeInterval` read as a `PointedFlowSeq` |
| `ancientFlowSequence` | the same sequence read as a Chapter 25 `FlowSequence` with constant interval |
| `ancientFlowSequence_atTime_zero` | the two readings have the same time-zero `PointedRiemannianSeq` (`rfl`) |
| `exists_ancientKappa_fixed_kappa_compactness` | Chapter 23 shape: `PointedCGHMaps`, canonical slice data, mixed comparisons, limit is an `IsAncientKappaSolution` and a `KLim` |
| `exists_ancientKappa_fixed_kappa_convergesOn` | Chapter 25 shape without capture: `PointedRiemannianCGMaps` + `ConvergesOn` |
| `ancientKappa_fixed_kappa_compactness_of_capture` | the exact Chapter 25 slot, conditional on the one missing conversion |

`chapter25_fixed_kappa_compactness_slot` is `private`. It restates the Chapter 25
slot with that file's own anonymous `FlowSequence` literal and derives it from
`ancientKappa_fixed_kappa_compactness_of_capture`, so the compiler certifies that
the export really discharges the slot.

## The one missing conversion

`MetricSourceCapture F` (`Chapter25Convergence.lean`) says that for every
`r > 0`, eventually

```
riemannianBallOf (X.obj (f i)).metric (X.obj (f i)).basepoint r ⊆
  (F.partialDiffeomorph i) '' (F.partialDiffeomorph i).source
```

i.e. fixed-radius balls of the *sources*, centred at their basepoints, are
eventually captured by the images of the exhaustion maps. The Chapter 23
compactness chain (`exists_preliminary_klim_compactness` →
`exists_fixed_kappa_compactness_of_rankOne` → `exists_fixed_kappa_compactness`)
produces `ExhaustsByOpen` on the *limit* side, canonical slice convergence data
and all-order comparisons on compact subsets of the limit. None of these is a
statement about source balls, and capture is not formally derivable from the
abstract data: it needs the metric comparison to be turned into a distance
estimate on the source side plus completeness of the limit. `ConvergesOn` is
derivable and is proved here; capture is not, so it is an explicit hypothesis

```
hcapture : ∀ L f (F : PointedRiemannianCGMaps ((ancientFlowSequence X).atTime 0)
  (L.atTime 0) f), IsAncientKappaSolution kappa L → ConvergesOn F L.S →
    MetricSourceCapture F
```

of `ancientKappa_fixed_kappa_compactness_of_capture` only. Nothing in this file
is a proof placeholder.

## Elaboration note

`PointedCGHMaps.atTime` has `{X : PointedFlowSeq}` implicit and `L :
PointedFlowData X.D`. When the limit is bound with the *reduced* type
`PointedFlowData I3 ancientTimeInterval`, the unification problem
`?X.D =?= ancientTimeInterval` is not solvable and two occurrences of
`Phi.atTime (L := L) t` in one statement acquire different metavariables
(`Type mismatch … MetricSourceData (PointedCGHMaps.atTime ?m.152 t) k` vs
`?m.117`). Passing `(X := ancientPointedFlowSeq X)` explicitly fixes it; the
same holds for the `FlowSequence` reading at time zero. This is worth reusing
whenever a Chapter 23 statement binds the limit at `ancientTimeInterval` rather
than at `X.D`.

## Verification

```
LEAN_NUM_THREADS=2 lake env lean \
  DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/KappaSolutions/AncientKappaFixedCompactness.lean
```

Empty output, exit 0, about 20 s (2026-09-11, artifacts of
`KLimThreeDimensionalBounded` refreshed 00:40).

## Inherited admissions

`#print axioms` reports `propext, sorryAx, Classical.choice, Quot.sound` for the
three theorems and `propext, Classical.choice, Quot.sound` for the two
definitions and the `rfl` lemma. A transitive scan of the proof term of
`ancientKappa_fixed_kappa_compactness_of_capture` (90875 reachable constants)
finds exactly 24 declarations whose own value uses `sorryAx`, all of them the
lane's recorded upstream admissions, all in namespace
`DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions`:

```
ancient_fixed_universal_cover_product_of_null_plane
compact_ricciFlow_volumeVariation_on_regular
complete_forward_flatness
complete_noncompact_three_shrinker_universal_cover_fibres
complete_surface_constant_scalar_round_cover
complete_surface_shrinker_compact_constant_scalar
curvDerivNorm_le_product_real_of_inner_eq
curvDerivNorm_liftedMetric
curvDerivNorm_pullbackMetricCross
existsUnique_meanZero_smooth_poisson
exists_backward_slice_asymptotic_shrinker
exists_local_ancient_flow_compactness
exists_local_pointed_metric_compactness
exists_mixed_curvature_jet_polynomials
hamilton_ancient_trace_harnack_at_terminal
klim_terminal_curvature_trichotomy
metricRm04At_product_real_of_inner_eq
ricciFlow_additive_distance_bound_of_ricci_upper
riemannianVolumeMeasure_product_real_of_inner_eq
scalar_slice_zero_of_nonnegative_slab
universalCover_image_ball_liftedMetric
universalCover_volume_image_le
volumeMeasurePreserving_pullbackMetric
volumeMeasurePreserving_pullbackMetricCross
```

No new admission is introduced here. Besides these, the statements carry two
explicit hypotheses: `hnoEmbedding`, the topological nonembedding obstruction
for the antipodal sphere quotient inherited from
`thm:ksol-three-dimensional-KLim-bounded`, and (for the slot form) `hcapture`.

The scan is reproducible: copy the file outside the tree, append a `run_cmd`
that walks `env.find?` from the endpoint, matching `ConstantInfo.thmInfo v =>
v.value` explicitly — `ConstantInfo.value?` returns `none` for theorems in this
toolchain, which silently yields an empty admission list.

## Not registered

`DifferentialGeometry.lean` is untouched, so no `.olean` exists for this module
yet; downstream files cannot import it until it is registered and refreshed.
