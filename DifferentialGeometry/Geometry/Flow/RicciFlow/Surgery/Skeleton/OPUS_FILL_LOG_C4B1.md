# OPUS_FILL_LOG_C4B1 (DESIGN_C4B bricks M2, M3, G)

## 2026-09-26 entry 1 (start)

Read AGENTS.md (pc3: no header, no module docstring), DESIGN_C4B.md. Scope: M2, M3, G only.
Compile: `LEAN_NUM_THREADS=2 lake env lean` with the lakefile options passed as `-D` (standard
linter set on), axioms by a temporary `#print axioms` appended and removed (script in scratchpad).

## entry 2: G delivered

File `Surgery/Topology/LocalPullScalarGradient.lean` (new).
`Surgery.Topology.abs_mfderiv_metricScalarAt_localPullMetric_scaleMetric_le`, statement verbatim
from DESIGN_C4B §2 G, with `M : Type u`, `N : Type v` independent (only `[T2Space]` on both; no
`SigmaCompactSpace` needed). Compiles clean with the standard linter set. Axioms:
`propext, Classical.choice, Quot.sound`. Deviations: none.

## entry 3: M2 delivered, with one statement change (failure first)

**The §2 M2 statement is false as written** (`U := standardCapWindow D`, the whole window).
`MetricComparisonOn.pullback` is a *global* smooth `Tensor0SField` on `E3` that must equal
`F^* g` on `U`. With `U` the whole open window, `F^* g` need not extend smoothly across the sphere
`‖x‖ = D + 1`: the hypothesis controls only `order` derivatives. Counterexample shape:
`g = (1 + δ·s^(2·order+2)·sin(1/s))·Q_T` on the window, `s = D + 1 − ‖x‖`. Its first `order`
covariant derivatives are `O(δ)` (so the `< e` hypothesis holds for small `δ`), but its derivative
of order `2·order + 3` is unbounded, so no smooth tensor on `E3` restricts to it. Hence no
`MetricComparisonOn` on the whole window exists in general.

**Delivered (nearest correct statement).** File
`Perelman/StandardSolution/StandardWindowComparison.lean` (new), namespace
`DifferentialGeometry.PDE.RicciFlow`:
- `StandardSolution.exists_window_metricComparisonOn`: §2 verbatim except the last line.
  The comparison set is any `U : Set E3` with `closure U ⊆ standardCapWindow D`, in place of
  `standardCapWindow D`.
- `StandardSolution.exists_window_metricComparisonOn_of_lt`: the same, but with the set
  `standardCapWindow D'` for any `D' < D` (an `Opens`, which is the form M4's `U` takes).

Consumer impact (M4★): pass `D' := D − 1` (or any `D' < D` with the M4 ball inside
`standardCapWindow D'`). The M1b placement bound `‖y‖ ≤ ‖z‖ + Λ(L+1) < D + 1` becomes
`< D' + 1`. With `r' := r + Λ(L+1) + 1` and `D > r'`, it holds for `D' = D − 1`, because
`‖y‖ < r + Λ(L+1) < D`. No new hypothesis.
Proof: `D_ref` from `exists_uniform_standard_metric_deriv_norm_reference_bound`,
`e := η / ((D_ref + 1)(order + 1))`. Extend `g` from a neighbourhood of `closure U` to a global
metric `G` (`exists_smooth_metric_agrees_on_neighborhood_of_is_closed`). Then
`MapMetricApproximationOn.ofMetricDerivNorm` gives the approximation, with locality through
`metricDerivNorm_restrictOpen` and `metricDerivNorm_eq_of_metric_eventuallyEq`, and
`MetricComparisonOn.ofMapMetricApproximation` finishes. It uses a private copy of the
`mfderiv (subtypeVal).symm = id` step from `SpatialCanonicalWitnessTransport.subtypeVal_symm_isometry`.
Compile: clean with the standard linter set. Axioms of both: `propext, Classical.choice,
Quot.sound`.

## entry 4: M3 delivered (name change only; deferred merge recorded)

File `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessUniverseTransport.lean` (new, 1132
lines), namespace `FiniteHorn`. Public API (two declarations, both statements match §2 M3 with
`N : Type v` and `M : Type (max u v)`):
- `SpatialCanonicalWitness.pushforwardOfInjectiveULift`
- `SpatialCanonicalWitness.capTubeHasNeckChart.pushforwardOfInjectiveULift`

**Name deviation.** The §2 name `pushforwardOfInjective` is already taken by the committed
same-universe version (`SpatialCanonicalWitnessTransport.lean:1048/1065`), and committed files may
not be touched. The `ULift` suffix is temporary.

**Deferred merge (for the acceptance lane).** Replace sections `Isometry` through `Corollaries`
(lines 277–1078) of `SpatialCanonicalWitnessTransport.lean` in place with the universe-general
versions in this file:
- `N : Type v`, `M : Type (max u v)`;
- the `…Lift`-named private copies become the public originals;
- `SpatialRoundComponent.pushforward` gets its `ULift` model;
- `capCore_/positiveComponent_transport_of_partialDiffeomorph` take the `_lift` bodies.

The old same-universe API is then the special case `v := u`, because `Type (max u u)` is
`Type u`. After that, delete this file and rename `…ULift` back to `pushforwardOfInjective`. The
private copies duplicated here are:
- `IsometricBalls.image_riemannian(Closed)Ball_eq_of_isometric_on_compact_ball`, which is
  `M N : Type u` there and generalizes to `Type*`;
- the four `partialDiffeomorph_*_of_subset_source` from `CanonicalCapTransport.lean`, which are
  `Type u` there;
- the whole transport chain of `SpatialCanonicalWitnessTransport.lean`.

How the universe gap is closed:
- The `CapCore.projective` and `PositiveComponent.projective` models (`Z : Type v`) are replaced by
  `ULift.{u} Z`. This needs `uliftChartedSpace` as a local instance and
  `isManifold_ulift I3 Z` as an explicit `have`; `T2Space`, `CompactSpace` and
  `SigmaCompactSpace` come by instance search. The `ProjectivePresentation` is lifted along `up`,
  with its local-diffeo clause via `Diffeomorph.isLocalDiffeomorph`. The maps are precomposed with
  `(uliftDiffeomorph I3 Z).symm.toPartialDiffeomorph`.
- The round component uses:
  - `Z := ULift R.Z`, whose `ConnectedSpace` comes from `ULift.up_surjective.connectedSpace`;
  - `metric := Diffeomorph.pullbackMetricCross R.metric Φ`. Its scalar-one and
    constant-curvature fields come from `metricScalarAt_localPull` and
    `metricRm04At_localPullMetric`, after identifying the metric with `localPullMetric`;
  - the comparison from a new private `MetricComparisonOn.precompDiffeomorph`: source-side
    precomposition by a diffeomorphism, with the same `eps`, via `pullbackTensor02FieldCross` and
    `tensor02CovDerivNormWith_pullbackTensor02FieldCross`.

Checks:
- Consumer-shape probe (temporary `example`, removed): `N := standardCapWindow D : Type 0` and
  `M : Type w`. Both declarations elaborate and apply; the universe unification works.
- Compile is clean with the standard linter set: no warnings and no diagnostics.
- Axioms of both public declarations: `propext, Classical.choice, Quot.sound`.

## Summary

| Brick | File | Lines | Status | Deviation |
|---|---|---|---|---|
| G | `Surgery/Topology/LocalPullScalarGradient.lean` | 94 | proved, clean | none |
| M2 | `Perelman/StandardSolution/StandardWindowComparison.lean` | 149 | proved, clean | §2 statement false on the whole window; set is `closure U ⊆ window` (plus `_of_lt` for `standardCapWindow D'`, `D' < D`) |
| M3 | `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessUniverseTransport.lean` | 1132 | proved, clean | name `…ULift` (clash); deferred in-place merge |

None of these three files is registered in `DifferentialGeometry.lean`, which the lead owns. There
was no build, no git write, and no committed file was touched.
