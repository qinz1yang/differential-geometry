# Analysis: initial lower bound bricks 24a / 24b (2026-09-26)

Paths relative to `DifferentialGeometry/Geometry/Flow/RicciFlow/`. "Collab" = Ziyang's commits
`286e17a8c..ac2e5266e` (queue entry 23), NOT on this branch; their line numbers are at `ac2e5266e`.

## Interface findings

1. `HistoryReducedVolumeInitialLowerBound` is unprovable as stated: every per-event cap barrier goes
   through `exists_uniform_static_cap_scale_lower_bound` (`Surgery/Topology/GeometricCutoff.lean:614`),
   which needs `p.recenterConstant ≤ c`; the leaf chooses `δmax` before `p₀` and never bounds
   `p₀.recenterConstant`. Fix: add `Λ` as in `CanonicalNeighborhoodsThroughSurgeryStrong`
   (`0 < Λ`, `p₀.recenterConstant ≤ Λ →` beside `δbound ≤ δmax`); propagates to
   `NoncollapsingThroughSurgery` (`CanonicalNeighborhoodInduction.lean:228`),
   `SmallScaleNoncollapsingThroughSurgery`, the C2 assembly, and the consumers at
   `CanonicalNeighborhoodInduction.lean:302`, `CanonicalNeighborhoodsThroughSurgeryStrong.lean:255`.
   (Queue entries 8 / 28.)
2. Collab's all-events theorems (`CapWindowAction.lean:2233` and wrappers 1684, 1768, 1868, 2015,
   2120, 2350, 2438) assume `|∂ₜR| ≤ Cderiv R²` on every stage without a time cutoff; the leaf only
   supplies `DerivativeBoundBefore` on `Ioo a t₀`. Fix: re-thread a strict cutoff `s < t`
   (`HistoryScalarDerivativeBoundBefore`, below); stages after the current one become vacuous.
3. Nothing false: with `Λ`, `c` depends only on `(g₀, B)`; `δmax` may depend on `r₀`; `r₀ ≤ r` only
   gives the pole an `r₀`-controlled ball.
4. `MinimumTime:834/:957` are not barriers (they take regular crossings as hypotheses on a common
   chart `X`; `:957` also needs compact `K`, `μ g ≤ S.metric`, frontier separation, the escape
   inequality `6v² + (4B/3)v⁴ ≤ μ r²`).
5. No `l ≤ 3/2` point through surgeries exists anywhere (dominant cost of 24b).

## Reaching time 0 and birth points

`v = √T` gives `first = 0`, endpoint in stage 0, which has no births: birth endpoints are excluded by
the endpoint time, not by the barrier. Hand-offs at events go through `∃ z : old, z = α_i ∧ oldOutput
z = α_{i+1}` (`AbsoluteContinuity.lean:252`); cap interiors are not in the range of `oldOutput`, so a
curve stopping inside a new cap is not a competitor; the only non-regular hand-offs are `z ∈ ∂old`,
mapped onto a retained cap sphere (`EventCapCapture.lean:46`; collab `MetricCutCapScalarLower.lean:905`,
converse `:544`). So 24a reduces to: a curve at a cap point at its birth time has large action. Birth
endpoints matter only for `v < √T` with `T − v² = time i.succ` (through continuity of `l_min` at
event times; collab 2350 excludes low-cost ones).

## 24a quantitative barrier (≈250–350 lines AFTER entry 23)

Normalization: the `s = √τ` action `∫ ½|α'|² + 2s²R ds` is Perelman's `L`; `l = L/(2√τ)`; the tree
uses an absolute threshold `A` with `v ≤ E`; `T < B` gives `L ≤ Â√T` from `A := Â√B + 1`, `E := √B`.
Scalar floor `3/a₀` with `a₀ = a₀(g₀)` (`HamiltonIveyPinching.lean:666`); stage floor lemma via
`stageInitial_scalarLowerBound_of_history` with `c = a₀/2` (~30 lines).
Existing: branch `CapWindowAction.lean:1067` (discard), `:558`, `:740` (survival); collab `:1537`
(`exists_uniform_canonical_cap_birth_action_lower_bound`), `:1613`
(`exists_uniform_interior_old_nodes_of_action_le`), `:2015` (all crossings regular, uniform `δ₀`),
`:2233` (attained minimizer with regular crossings, floor `3/a₀`; attainment collab `Density.lean:806`).
The barrier is per event; a threshold above `3√τ` with uniform `δ₀` is already proved upstream.

```lean
def HistoryScalarDerivativeBoundBefore {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀)
    (Ctime : ℝ≥0) (qcan t : ℝ) : Prop :=
  ∀ (j : Fin (H.eventCount + 1)) (y : (H.stage j).Carrier),
    ∀ s ∈ Ioo (H.time j) (H.toHistory.stageEndTime j), s < t →
      qcan < metricScalarAt (H.toHistory.stageMetric j s) y →
      |derivWithin (fun z => metricScalarAt (H.toHistory.stageMetric j z) y) (Iic s) s| ≤
        Ctime * metricScalarAt (H.toHistory.stageMetric j s) y ^ 2

theorem exists_uniform_regularMinimizerEndpoint_of_regularizedCost_lt
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ (B A r₀ qcan Λ ρ : ℝ) (Ctime : ℝ≥0), 0 < B → 0 < r₀ → 0 < qcan → 0 < Λ → 0 < ρ →
    ∃ (δ₀ ε₀ R₀ : ℝ) (m₀ : ℕ), 0 < δ₀ ∧ 0 < ε₀ ∧ 0 < R₀ ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ ε₀ → R₀ ≤ p₀.modelRadius → m₀ ≤ p₀.modelOrder →
      p₀.recenterConstant ≤ Λ → δbound ≤ δ₀ → ρbound ≤ ρ →
    ∀ (H : RetainedCoreHistory P₀), InitialIdentification P₀ g₀ H.toHistory →
      H.horizon < B → H.hasCanonicalCutoffRecords p₀ δbound ρbound →
    ∀ (t : Icc (0 : ℝ) H.toHistory.horizon), HistoryScalarDerivativeBoundBefore H Ctime qcan t →
    ∀ (p : (H.toHistory.stageAt t).Carrier), H.toHistory.isParabolicallyRmControlledBall t p r₀ →
    ∀ (first : Fin (H.eventCount + 1)) (hle : first ≤ H.toHistory.activeStage t) (v : ℝ),
      v ≤ Real.sqrt B →
    ∀ q : (H.stage first).Carrier,
      H.toHistory.regularizedCost first (H.toHistory.activeStage t) hle t (3 / a₀) 0 v p q <
        (A : WithTop ℝ) →
      q ∈ H.toHistory.regularMinimizerEndpoints first (H.toHistory.activeStage t) hle t
        (3 / a₀) v p
```

Gaps: G0 collab code (entry 23, at least `b3604787e baadd3cae 5f4118086 d1c4672a1 2425dbcaa
ac24dded4 31059bcb8` + deps); G1 strict cutoff re-threading (80–150); G2 class-to-raw glue (100–150:
record parameters, `a₀` from `InitialIdentification`, `mono_radius`, `stageMetric` =
`incoming.flow.scalar`); G3 stage floor lemma (~30). Re-deriving collab 1537–2233 from the branch's
`:558/:740/:1067` would be 1500+ lines: not recommended.

## 24b positive-volume initial block (≈1200–1850 lines after 24a and entry 23)

```lean
theorem exists_uniform_initial_regular_block
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (B : ℝ) (hB : 0 < B) :
    ∃ a₀ C κ₀ : ℝ, 0 < a₀ ∧ 0 < κ₀ ∧
    ∀ (r₀ qcan Λ ρ : ℝ) (Ctime : ℝ≥0), 0 < r₀ → 0 < qcan → 0 < Λ → 0 < ρ →
    ∃ (δ₀ ε₀ R₀ : ℝ) (m₀ : ℕ), 0 < δ₀ ∧ 0 < ε₀ ∧ 0 < R₀ ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ ε₀ → R₀ ≤ p₀.modelRadius → m₀ ≤ p₀.modelOrder →
      p₀.recenterConstant ≤ Λ → δbound ≤ δ₀ → ρbound ≤ ρ →
    ∀ (H : RetainedCoreHistory P₀), InitialIdentification P₀ g₀ H.toHistory →
      H.horizon < B → H.hasCanonicalCutoffRecords p₀ δbound ρbound →
    ∀ (t : Icc (0 : ℝ) H.toHistory.horizon), 0 < (t : ℝ) →
      HistoryScalarDerivativeBoundBefore H Ctime qcan t →
    ∀ (p : (H.toHistory.stageAt t).Carrier), H.toHistory.isParabolicallyRmControlledBall t p r₀ →
    ∃ U : Set (H.stage 0).Carrier, MeasurableSet U ∧
      ENNReal.ofReal (κ₀ * (t : ℝ) ^ (3 / 2 : ℝ)) ≤
        riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier (H.initialMetric 0) U ∧
      ∀ q ∈ U,
        q ∈ H.toHistory.regularMinimizerEndpoints 0 (H.toHistory.activeStage t)
          (Fin.zero_le _) t (3 / a₀) (Real.sqrt t) p ∧
        H.toHistory.regularizedCost 0 (H.toHistory.activeStage t) (Fin.zero_le _) t (3 / a₀) 0
          (Real.sqrt t) p q ≤ ((2 * C * Real.sqrt t : ℝ) : WithTop ℝ)
```

plus `reducedVolume_ge_of_initial_block` (floor `3/a₀`, `MeasurableSet U`, the volume and block
clauses ⇒ `(4π)^{-3/2} e^{-C} κ₀ ≤ reducedVolume (activeStage t) p t √t`). Constant depends only on
`(g₀, B)`. The block is `U = B_{g₀}(q₀, c₁·min(√t, √θ₀))`: the radius MUST shrink like `√t` (a fixed
radius gives `l ≈ ρ₀²/t`); the task's `l ≤ 3/2 + C` becomes `l ≤ C(g₀, B)`.

- L1 `l_min ≤ 3/2` through surgeries (missing, 700–1100): antitonicity of `2b·m(b) − 6b²` bootstrapped
  by "`m ≤ 3b < A` ⇒ minimizer regular (24a) ⇒ upper support". Pieces: branch `MinimumTime:610`
  (antitone), `:660`, `:546` (upper support near the pole), `HistoryPoleAction:190/233` (seed); collab
  attainment `Density:874`, continuity `TimeContinuity:278`, `EventContinuation:182`,
  `CapWindowAction:2438`, survivor chart `AbsoluteContinuity:2413`. Missing: upper support at an
  interior `b₀` from one regular minimizer and its survivor chart (400–600); global Dini/antitone
  assembly across stage changes (300–500). Template:
  `Perelman/LGeometry/ReducedLength/Minimum/DimensionBound.lean:108`.
- L2 endpoint perturbation in the initial window (missing, 300–450): `θ = min(t, θ₀)` below the first
  singular time (`InitialCurvatureLifespan.lean:31` / `HistoryCurvatureTimeBound.lean:61`), `|Rm| ≤ K`
  on `[0, η]` (`InitialSlabUniformBounds.lean:21`); replace the tail on `[√(t−θ), √t]` by a
  constant-speed `g₀`-path; `cost(q) ≤ cost(q₀) + C'√t` for `d_{g₀}(q, q₀) ≤ ρ₁(t)`; crossings
  unchanged.
- L3 block assembly (200–300): cost `< A` ⇒ endpoint in the set (24a); density
  `≥ e^{-C}(4πt)^{-3/2}` (`regularizedDensity_eq_exp_of_regularizedCost_eq`);
  `reducedVolume_eq_of_scalar_lower_bound_le` with `B₀ = 3/a₀`; `lintegral_mono_set` (no
  measurability of the endpoint set needed); volume from `InitialVolume.lean:55` +
  `riemannianBallOf_volume_eq`.

## Leaf proof from the bricks

Given `B`: `c` from 24b. Given `qcan r₀`: `ρ := 1`, output `δmax = δ₀`, `ρmax = 1`, `εcap = ε₀`,
`Dcap = R₀`, `mcap = m₀`. First clause: shrink the controlled ball to `r₀` (`mono_radius`); derivative
predicate from `EventSlabsDerivative … j.castSucc` + `DerivativeBoundBefore t₀`. Terminal clause: same
on `extendHorizon T` (`hasCanonicalCutoffRecords_extendHorizon`, `T < s ≤ B`). The leaf's canonical,
gradient and pinching hypotheses are unused. Edits: add `Λ`; keep `r₀ ≤ r`; `c` before `qcan r₀`
(already); no explicit `δ ≤ δ₀(B, r₀, A)` class condition needed.
