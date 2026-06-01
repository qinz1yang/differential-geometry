import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartLocalPicardProducer

/-!
## From spatial `C¹`-regularity to the Picard–Lindelöf regularity predicate

The chart-cover assembly that builds the time-indexed diffeomorphism family
(`manifoldFlowFamily_exists` / its regularity-driven wrapper
`manifoldFlowFamily_of_regular`) consumes the clean predicate
`ChartCoordPicardRegular X` — continuity of the uncurried field `(t, x) ↦ X t x`
on `ℝ × M` together with a *per-chart, uniform-in-time* spatial Lipschitz bound
for the chart pushforward `y ↦ X t ((chartAt H α).symm (I.symm y))`.

This file closes the remaining gap: it produces `ChartCoordPicardRegular X` from
the genuine regularity that a parabolic-PDE-driven vector field actually has —
namely

* **continuity in time–space**: `(t, x) ↦ X t x` is continuous on `ℝ × M`; and
* **spatial `C¹` with a jointly-continuous spatial derivative**: for each base
  chart `α`, the chart pushforward `f^α t y := (X t ((chartAt H α).symm (I.symm
  y)) : E)` is Fréchet-differentiable in the space variable `y` on a ball around
  the chart centre, with the *spatial* derivative `Df^α t y : E →L[ℝ] E`
  *jointly continuous* in `(t, y)` on a compact time–space box.

The uniform-in-time Lipschitz constant is extracted by the extreme value theorem:
the jointly-continuous operator-norm `(t, y) ↦ ‖Df^α t y‖` attains a finite
maximum `K` on the compact box `[0, L] × closedBall(centre, r)`, and the
mean-value inequality on the convex ball
(`lipschitzOnWith_of_nnnorm_hasFDerivWithin_le`) then makes `f^α t` uniformly
`K`-Lipschitz on the open ball for *every* `t ∈ [0, L]`.

`chartCoordPicardRegular_of_spatialC1` is the producer. Composed with the
already-proved `chartLocalPicardData_of_regular`
(`ChartLocalPicardProducer.lean`), it yields the per-base-point
`ChartLocalPicardData X α` — and likewise for `-X`, whose chart pushforward has
spatial derivative `-Df^α` with the same joint continuity — directly from the
spatial-`C¹` regularity of `X`, with no bundled ODE-solution data anywhere.
-/

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle Set
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/--
The genuine spatial-`C¹` regularity of a time-dependent vector field, stated
chart-by-chart in model-space coordinates, that suffices to manufacture the
Picard–Lindelöf regularity predicate `ChartCoordPicardRegular X`.

`ChartCoordSpatialC1 X` packages, for each base chart `α : M`:

* a positive time horizon `L` and a positive chart radius `r`;
* the **spatial Fréchet derivative** `Df : ℝ → E → (E →L[ℝ] E)` of the chart
  pushforward `f t y := X t ((chartAt H α).symm (I.symm y))` (a member of `E`
  via the canonical type-synonym defeq `TangentSpace I p = E`);
* `hHasDeriv`: for each time `t ∈ [0, L]` and each point `y` in the closed
  `r`-ball around the chart centre `I ((chartAt H α) α)`, the chart pushforward
  `f t` has `Df t y` as its derivative-within the closed ball at `y`; and
* `hDerCont`: the uncurried spatial derivative `(t, y) ↦ Df t y` is continuous
  on the compact box `[0, L] × closedBall(centre, r)`.

This is purely the regularity of `X`: it never references a flow or an
ODE-solution. For a metric-trace vector field `X t = deTurckVF (g t) g₀` whose
metric family `g` is `C¹` in `(t, x)`, the chart pushforward is `C¹` in `y` (the
DeTurck components are smooth functions of the metric jet, which is `C¹` in `x`),
and the spatial derivative is jointly continuous in `(t, y)` (the metric jet is
continuous in `t`); so this predicate is the natural separable interface a
parabolic Ricci-DeTurck solution supplies. -/
def ChartCoordSpatialC1 (X : ℝ → ∀ x : M, TangentSpace I x) : Prop :=
  ∀ α : M, ∃ (L r : ℝ) (Df : ℝ → E → (E →L[ℝ] E)),
    0 < L ∧ 0 < r ∧
    (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ y ∈ Metric.closedBall (I ((chartAt H α) α)) r,
      HasFDerivWithinAt (fun z : E => (X t ((chartAt H α).symm (I.symm z)) : E))
        (Df t y) (Metric.closedBall (I ((chartAt H α) α)) r) y) ∧
    ContinuousOn (Function.uncurry Df)
      (Set.Icc (0 : ℝ) L ×ˢ Metric.closedBall (I ((chartAt H α) α)) r)

/--
**Per-chart uniform-in-time Lipschitz bound from spatial `C¹`.**

Given the spatial-`C¹` data at a single base chart `α` — a positive horizon `L`,
a positive radius `r`, a spatial derivative `Df` of the chart pushforward on the
closed `r`-ball, and joint continuity of `Df` on the compact box `[0, L] ×
closedBall(centre, r)` — there exist a positive horizon, a positive radius, and a
non-negative constant `K` (the maximum of the operator norm of `Df` over the
compact box) such that, for every `t ∈ [0, L]`, the chart pushforward
`y ↦ X t ((chartAt H α).symm (I.symm y))` is `K`-Lipschitz on the open `r`-ball.

The proof extracts `K = max_{[0,L]×closedBall} ‖Df‖` by the extreme value
theorem (the box is compact and `(t, y) ↦ ‖Df t y‖` is continuous), then applies
the mean-value Lipschitz estimate `lipschitzOnWith_of_nnnorm_hasFDerivWithin_le`
on the convex open `r`-ball with the uniform bound `‖Df t y‖ ≤ K`. -/
theorem exists_uniform_chart_lipschitz_of_spatialC1
    (X : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (L r : ℝ) (Df : ℝ → E → (E →L[ℝ] E))
    (hL : 0 < L) (hr : 0 < r)
    (hHasDeriv : ∀ t ∈ Set.Icc (0 : ℝ) L,
      ∀ y ∈ Metric.closedBall (I ((chartAt H α) α)) r,
        HasFDerivWithinAt
          (fun z : E => (X t ((chartAt H α).symm (I.symm z)) : E))
          (Df t y) (Metric.closedBall (I ((chartAt H α) α)) r) y)
    (hDerCont : ContinuousOn (Function.uncurry Df)
      (Set.Icc (0 : ℝ) L ×ˢ Metric.closedBall (I ((chartAt H α) α)) r)) :
    ∃ Lout K r' : ℝ, 0 < Lout ∧ 0 < r' ∧ 0 ≤ K ∧
      ∀ t ∈ Set.Icc (0 : ℝ) Lout,
        LipschitzOnWith (Real.toNNReal K)
          (fun y : E => (X t ((chartAt H α).symm (I.symm y)) : E))
          (Metric.ball (I ((chartAt H α) α)) r') := by
  set c : E := I ((chartAt H α) α) with hc_def
  set Box : Set (ℝ × E) := Set.Icc (0 : ℝ) L ×ˢ Metric.closedBall c r with hBox
  have hBoxCompact : IsCompact Box := by
    rw [hBox]
    exact (isCompact_Icc).prod (isCompact_closedBall c r)
  have hBoxNonempty : Box.Nonempty := by
    refine ⟨(0, c), ?_⟩
    rw [hBox]
    exact ⟨⟨le_refl 0, hL.le⟩, Metric.mem_closedBall_self hr.le⟩
  have hNormCont : ContinuousOn (fun p : ℝ × E => ‖Function.uncurry Df p‖) Box :=
    hDerCont.norm
  obtain ⟨pmax, hpmaxMem, hpmaxMax⟩ :=
    hBoxCompact.exists_isMaxOn hBoxNonempty hNormCont
  set K : ℝ := ‖Function.uncurry Df pmax‖ with hK_def
  have hK_nonneg : 0 ≤ K := by rw [hK_def]; exact norm_nonneg _
  have hKbound : ∀ t ∈ Set.Icc (0 : ℝ) L, ∀ y ∈ Metric.closedBall c r,
      ‖Df t y‖ ≤ K := by
    intro t ht y hy
    have hmem : (t, y) ∈ Box := by rw [hBox]; exact ⟨ht, hy⟩
    have := hpmaxMax hmem
    simpa [Function.uncurry, hK_def] using this
  refine ⟨L, K, r, hL, hr, hK_nonneg, ?_⟩
  intro t ht
  have hconv : Convex ℝ (Metric.ball c r) := convex_ball c r
  have hKcoe : (Real.toNNReal K : ℝ) = K := Real.coe_toNNReal K hK_nonneg
  have hder_open : ∀ y ∈ Metric.ball c r,
      HasFDerivWithinAt
        (fun z : E => (X t ((chartAt H α).symm (I.symm z)) : E))
        (Df t y) (Metric.ball c r) y := by
    intro y hy
    have hy_closed : y ∈ Metric.closedBall c r :=
      Metric.ball_subset_closedBall hy
    exact (hHasDeriv t ht y hy_closed).mono Metric.ball_subset_closedBall
  have hbound_open : ∀ y ∈ Metric.ball c r,
      ‖Df t y‖₊ ≤ Real.toNNReal K := by
    intro y hy
    have hy_closed : y ∈ Metric.closedBall c r :=
      Metric.ball_subset_closedBall hy
    have hnorm := hKbound t ht y hy_closed
    rw [← NNReal.coe_le_coe, coe_nnnorm, hKcoe]
    exact hnorm
  exact hconv.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le hder_open hbound_open

/--
**Producer: spatial-`C¹` regularity ⇒ Picard–Lindelöf regularity predicate.**

From continuity of the uncurried field `(t, x) ↦ X t x` on `ℝ × M` and the
spatial-`C¹` data `ChartCoordSpatialC1 X` (per-chart spatial Fréchet derivative
with a jointly-continuous spatial derivative), produce the clean Picard–Lindelöf
regularity predicate `ChartCoordPicardRegular X` consumed by the chart-cover
assembly.

The continuity conjunct of `ChartCoordPicardRegular` is exactly `hCont`; the
per-chart spatial-Lipschitz conjunct is supplied, uniformly in time, by
`exists_uniform_chart_lipschitz_of_spatialC1`. -/
theorem chartCoordPicardRegular_of_spatialC1
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hCont : ContinuousOn (Function.uncurry (fun t x => X t x))
      (Set.univ : Set (ℝ × M)))
    (hC1 : ChartCoordSpatialC1 (I := I) X) :
    ChartCoordPicardRegular (I := I) X := by
  refine ⟨hCont, ?_⟩
  intro α
  obtain ⟨L, r, Df, hL, hr, hHasDeriv, hDerCont⟩ := hC1 α
  exact exists_uniform_chart_lipschitz_of_spatialC1 X α L r Df hL hr hHasDeriv
    hDerCont

/--
**The negated field inherits the spatial-`C¹` regularity.**

If `X` is spatial-`C¹` with spatial derivative `Df`, then `-X` is spatial-`C¹`
with spatial derivative `-Df`: the chart pushforward of `-X` is the negation of
the chart pushforward of `X`, whose derivative is `-(Df t y)`, and the uncurried
`(t, y) ↦ -Df t y` is continuous wherever `(t, y) ↦ Df t y` is. -/
theorem chartCoordSpatialC1_neg
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hC1 : ChartCoordSpatialC1 (I := I) X) :
    ChartCoordSpatialC1 (I := I) (fun t x => -(X t x)) := by
  intro α
  obtain ⟨L, r, Df, hL, hr, hHasDeriv, hDerCont⟩ := hC1 α
  refine ⟨L, r, fun t y => -(Df t y), hL, hr, ?_, ?_⟩
  · intro t ht y hy
    have hbase := hHasDeriv t ht y hy
    have hfun :
        (fun z : E => ((-X t ((chartAt H α).symm (I.symm z))) : E))
          = fun z : E => -((X t ((chartAt H α).symm (I.symm z)) : E)) := by
      funext z; rfl
    rw [hfun]
    exact hbase.neg
  · have hfun :
        (Function.uncurry (fun t y => -(Df t y)))
          = fun p : ℝ × E => -(Function.uncurry Df p) := by
      funext p; rfl
    rw [hfun]
    exact hDerCont.neg

/--
**End-to-end producer: spatial-`C¹` regularity ⇒ per-base-point chart-local
Picard data, for `X` and for `-X`.**

From continuity of `(t, x) ↦ X t x` on `ℝ × M` and the spatial-`C¹` data
`ChartCoordSpatialC1 X`, produce both families of per-base-point chart-local
Picard data,

* `∀ α, ChartLocalPicardData X α`, and
* `∀ α, ChartLocalPicardData (fun t x => -(X t x)) α`,

which are exactly the two hypotheses `hper` / `hper_neg` consumed by the global
flow / diffeomorphism-family endpoint on a closed manifold.

The construction routes the spatial-`C¹` regularity through
`chartCoordPicardRegular_of_spatialC1` to obtain `ChartCoordPicardRegular X`
(and, via `chartCoordSpatialC1_neg`, `ChartCoordPicardRegular (-X)` — the
negated field is continuous because negation is continuous), then feeds each
into the previously-proved Picard-data producer `chartLocalPicardData_of_regular`.
The sole ODE-existence input is therefore the genuine spatial-`C¹` regularity of
`X`; no bundled ODE-solution data appears. -/
noncomputable def chartLocalPicardData_of_spatialC1
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hCont : ContinuousOn (Function.uncurry (fun t x => X t x))
      (Set.univ : Set (ℝ × M)))
    (hC1 : ChartCoordSpatialC1 (I := I) X) :
    (∀ α : M, ChartLocalPicardData X α) ×
      (∀ α : M, ChartLocalPicardData (fun t x => -(X t x)) α) := by
  have hReg : ChartCoordPicardRegular (I := I) X :=
    chartCoordPicardRegular_of_spatialC1 X hCont hC1
  have hContNeg :
      ContinuousOn (Function.uncurry (fun t x => -(X t x)))
        (Set.univ : Set (ℝ × M)) := by
    have hfun :
        (Function.uncurry (fun t x => -(X t x)))
          = fun p : ℝ × M => -(Function.uncurry (fun t x => X t x) p) := by
      funext p; rfl
    rw [hfun]
    exact hCont.neg
  have hRegNeg : ChartCoordPicardRegular (I := I) (fun t x => -(X t x)) :=
    chartCoordPicardRegular_of_spatialC1 (fun t x => -(X t x)) hContNeg
      (chartCoordSpatialC1_neg X hC1)
  exact ⟨fun α => chartLocalPicardData_of_regular X hReg α,
    fun α => chartLocalPicardData_of_regular (fun t x => -(X t x)) hRegNeg α⟩

end DifferentialGeometry.PDE.RicciFlow.ODE
