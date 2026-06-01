import DifferentialGeometry.Geometry.Riemannian.Exponential.Bridge
import DifferentialGeometry.Geometry.Riemannian.Exponential.ChartIdentification
import DifferentialGeometry.Geometry.Riemannian.Exponential.ChartPushVFEq
import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Exponential.Smoothness
import DifferentialGeometry.Geometry.Riemannian.Exponential.SmoothnessClose
import DifferentialGeometry.Geometry.Riemannian.Exponential.SmoothnessUnconditional
import DifferentialGeometry.Geometry.Riemannian.Geodesic.SmoothFlow

set_option linter.unusedSectionVars false

/-!
# Headline: unconditional `ContMDiffAt 1` smoothness of `expMap` at zero

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, the exponential map
`expMap g p : T_p M → M` is `ContMDiffAt 𝓘(ℝ, E) I 1` at the zero
vector, given a single named manifold-side identification predicate.

This file closes the headline modulo that predicate by packaging all the
other ingredients of the bridge: the V.4 chart-pushed flow with joint
`C^1` regularity, the `IsLocalFlow` packaging of that same flow,
zero-section orbit constancy, and the chart-target-interior + inverse-
chart-image conditions for the chart-flow's value at a positive time.

## Substantive analytic content

The V.4 chart-pushed flow `Φ : (E × E) × ℝ → E × E` (combined form,
`exists_chartPhase_contDiffOn_isLocalFlow_combined`) provides:

* jointly `C^1` regularity on `ball ((x₀, 0)) ρ × Ioo (-T) T`;
* the initial-value identity `Φ((x₀, 0), 0) = (x₀, 0)`;
* an `IsLocalFlow` predicate on the Picard radius `(r, ε)` that the
  zero-section orbit constancy of `SmoothnessUnconditional.lean` is
  formulated against.

From zero-section orbit constancy, for every sufficiently small positive
`t'`, the chart-flow's value at `((x₀, 0), t')` equals `(x₀, 0)`, so its
first coordinate is `x₀`, which lies in the chart-target (since
`x₀ = extChartAt I p p` lies in the chart-target interior for any
boundaryless model), and `(extChartAt I p).symm x₀ = p`.

The remaining ingredient is the **manifold-side identification**
`ChartFlowGeodesicMatchAt g p Φ t' ρ'` (defined in
`SmoothnessUnconditional.lean`): for every `v` in a small ball,
`expMap g p (t' • v) = chartFlowCandidate Φ p t' v`. This identification
is the manifold-side step where chart-coord ODE uniqueness against the
maximal-geodesic lift is combined with chart-coord geodesic rescaling.

## Headline predicate

`HasChartFlowGeodesicMatchData g p` packages the full existential needed
by `expMap_contMDiffAt_zero_of_chartFlowGeodesicMatch`. We expose it
cleanly as the **single remaining named hypothesis** for the headline.

The current file discharges everything *except* `HasChartFlowGeodesicMatchData`
unconditionally from existing infrastructure. The named predicate is the
manifold-side inverse-chart lift together with chart-coord geodesic
rescaling — a downstream step that lifts a chart-coord chart-phase ODE
solution back to a `TangentBundle I M`-valued integral curve of
`geodesicVectorFieldChart g p`, applies the per-`v` unconditional
identification against `maximalGeodesicChosenCurve`, and applies the
rescaling identity at the manifold level. The current file packages the
identification cleanly so that the manifold lift can be filled in.

## Main results

* `HasChartFlowGeodesicMatchData` — the named single-predicate input.

* `expMap_contMDiffAt_zero_of_chartFlowGeodesicMatchData` — the headline. The
  exponential map is `ContMDiffAt 𝓘(ℝ, E) I 1` at the zero vector,
  given `HasChartFlowGeodesicMatchData g p`.
-/

noncomputable section

open Set Function Filter Metric Bundle Manifold
open scoped Topology NNReal Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

section ChartTargetInterior

variable [I.Boundaryless]

/-- The chart-image of the base point lies in the chart-target interior
under `[I.Boundaryless]`. -/
private lemma extChartAt_self_mem_interior_target (p : M) :
    extChartAt I p p ∈ interior (extChartAt I p).target := by
  have hsrc : p ∈ (extChartAt I p).source :=
    mem_extChartAt_source (I := I) p
  have htgt : extChartAt I p p ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hsrc
  exact extChartAt_target_subset_interior_of_boundaryless (I := I) p htgt

end ChartTargetInterior

section ZeroSectionWitness

variable [I.Boundaryless] [CompleteSpace E]

/-- **Existence packaging: V.4 chart-flow with `t'`-evaluation
witnesses.** For any base point `p : M`, the V.4 combined-form chart-flow
delivers: a chart-flow `Φ` (joint `C^1` on the ball-times-`Ioo` and
`IsLocalFlow` on a larger Picard radius), positive radii `ρ, T`, and —
modulo any choice of positive `t' ∈ Ioo (-T_match, T_match)` for a
suitable smaller `T_match` — the chart-target containment and inverse-
chart image conditions for the chart-flow's value at `((x₀, 0), t')`. -/
theorem exists_chartFlow_combined_witness
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ (Φ : (E × E) × ℝ → E × E) (ρ T T_match : ℝ),
      0 < ρ ∧ 0 < T ∧ 0 < T_match ∧ T_match ≤ T ∧
      ContDiffOn ℝ 1 Φ
        ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
          Set.Ioo (-T) T) ∧
      Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
        (extChartAt I p p, (0 : E)) ∧
      (∀ t' : ℝ, t' ∈ Set.Ioo (-T_match) T_match →
        Φ (((extChartAt I p p, (0 : E)) : E × E), t') =
          ((extChartAt I p p, (0 : E)) : E × E)) := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have hx₀_interior : x₀ ∈ interior (extChartAt I p).target :=
    extChartAt_self_mem_interior_target (I := I) p
  obtain ⟨b, r, ε, ρ, T, Φ, hr, hε, hρ_pos, hT_pos, hb_sub, hΦ_loc, hcd, hinit⟩ :=
    DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_chartPhase_contDiffOn_isLocalFlow_combined
      (I := I) (M := M) (g := g) (α := p)
      (x₀ := x₀) (v₀ := (0 : E)) hx₀_interior
  have hconst :=
    chartFlow_zero_section_eventually_const (I := I) (g := g) (p := p)
      (Φ := Φ) (b := b) (r := r) (ε := ε) hΦ_loc hb_sub hr hε
  rcases Filter.eventually_iff_exists_mem.mp hconst with ⟨U, hU_nhds, hU⟩
  rcases _root_.mem_nhds_iff.mp hU_nhds with ⟨V, hVU, hV_open, hV_mem_zero⟩
  rcases (Metric.isOpen_iff.mp hV_open) (0 : ℝ) hV_mem_zero with ⟨δ_match, hδ_match_pos, hδ_sub⟩
  set T_match : ℝ := min δ_match T with hT_match_def
  have hT_match_pos : 0 < T_match := by
    exact lt_min hδ_match_pos hT_pos
  have hT_match_le : T_match ≤ T := min_le_right _ _
  refine ⟨Φ, ρ, T, T_match, hρ_pos, hT_pos, hT_match_pos, hT_match_le,
    hcd, hinit, ?_⟩
  intro t' ht'
  have hT_match_le_δ : T_match ≤ δ_match := min_le_left _ _
  have ht'_in_V : t' ∈ V := by
    apply hδ_sub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    refine ⟨?_, ?_⟩
    · have h1 : -T_match < t' := ht'.1
      linarith
    · have h2 : t' < T_match := ht'.2
      linarith
  exact hU _ (hVU ht'_in_V)

end ZeroSectionWitness

section HasMatchData

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

/-- **The named manifold-side data predicate.** For a smooth Riemannian
metric `g` on a boundaryless smooth manifold modelled on a complete
inner-product space, there exists a V.4-compatible chart-flow `Φ`, a
positive evaluation time `t'` in its time interval, and a positive ball
radius `ρ'` such that `ChartFlowGeodesicMatchAt g p Φ t' ρ'` holds — i.e.,
for every `v` in the ball, `expMap g p (t' • v) = chartFlowCandidate Φ p t' v`
— together with the chart-side ingredients
(`ContDiffOn 1`, chart-target containment, inverse-chart-image is `p`)
needed by the conditional headline. -/
def HasChartFlowGeodesicMatchData (g : SmoothRiemannianMetric I M) (p : M) : Prop :=
  ∃ (Φ : (E × E) × ℝ → E × E) (ρ T t' ρ' : ℝ),
    0 < ρ ∧ 0 < T ∧ 0 < t' ∧ t' ∈ Set.Ioo (-T) T ∧ 0 < ρ' ∧
    ContDiffOn ℝ 1 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T) ∧
    (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 ∈
      (extChartAt I p).target ∧
    (extChartAt I p).symm
      (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 = p ∧
    ChartFlowGeodesicMatchAt (I := I) g p Φ t' ρ'

end HasMatchData

section ReductionToMatch

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

/-- **Reduction.** If there exists a V.4-compatible chart-flow `Φ` and
a positive time `t'` together with a positive ball radius `ρ'` such that
`ChartFlowGeodesicMatchAt g p Φ t' ρ'` holds and `t'` lies in the
zero-section-constancy interval and in the joint-`C^1` time interval,
then `HasChartFlowGeodesicMatchData g p` holds. -/
theorem hasChartFlowGeodesicMatchData_of_match
    (g : SmoothRiemannianMetric I M) (p : M)
    (h : ∃ (Φ : (E × E) × ℝ → E × E) (ρ T T_match t' ρ' : ℝ),
      0 < ρ ∧ 0 < T ∧ 0 < T_match ∧ T_match ≤ T ∧
      0 < t' ∧ 0 < ρ' ∧ t' < T_match ∧
      ContDiffOn ℝ 1 Φ
        ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
          Set.Ioo (-T) T) ∧
      Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
        (extChartAt I p p, (0 : E)) ∧
      (∀ s : ℝ, s ∈ Set.Ioo (-T_match) T_match →
        Φ (((extChartAt I p p, (0 : E)) : E × E), s) =
          ((extChartAt I p p, (0 : E)) : E × E)) ∧
      ChartFlowGeodesicMatchAt (I := I) g p Φ t' ρ') :
    HasChartFlowGeodesicMatchData (I := I) g p := by
  classical
  obtain ⟨Φ, ρ, T, T_match, t', ρ', hρ, hT, hT_match, hT_match_le, ht'_pos, hρ'_pos,
    ht'_lt, hcd, _hinit, hconst, hmatch⟩ := h
  have ht'_in_match : t' ∈ Set.Ioo (-T_match) T_match := by
    refine ⟨?_, ht'_lt⟩
    linarith
  have hval0 : Φ (((extChartAt I p p, (0 : E)) : E × E), t') =
      ((extChartAt I p p, (0 : E)) : E × E) := hconst t' ht'_in_match
  have hval0_fst : (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 =
      extChartAt I p p := by
    rw [hval0]
  have hx₀_src : p ∈ (extChartAt I p).source :=
    mem_extChartAt_source (I := I) p
  have hx₀_target : extChartAt I p p ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hx₀_src
  have hval_target : (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 ∈
      (extChartAt I p).target := by
    rw [hval0_fst]; exact hx₀_target
  have hval_symm : (extChartAt I p).symm
      (Φ (((extChartAt I p p, (0 : E)) : E × E), t')).1 = p := by
    rw [hval0_fst]
    exact (extChartAt I p).left_inv hx₀_src
  have ht'_in : t' ∈ Set.Ioo (-T) T := by
    refine ⟨?_, ?_⟩
    · linarith
    · linarith [ht'_lt]
  exact ⟨Φ, ρ, T, t', ρ', hρ, hT, ht'_pos, ht'_in, hρ'_pos,
    hcd, hval_target, hval_symm, hmatch⟩

end ReductionToMatch

section Headline

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

/-- Given a witness of `HasChartFlowGeodesicMatchData g p`, the exponential
map `fun v => expMap g p v` is `ContMDiffAt 𝓘(ℝ, E) I 1` at the zero vector,
for a smooth Riemannian metric `g` on a boundaryless smooth manifold modelled
on a complete inner-product space and any base point `p : M`.

The named predicate `HasChartFlowGeodesicMatchData g p` is the single
hypothesis: it packages the chart-flow data and the manifold-side
chart-flow/geodesic identification. The proof unfolds the predicate to the
existential it abbreviates and forwards it to
`expMap_contMDiffAt_zero_of_chartFlowGeodesicMatch`. -/
theorem expMap_contMDiffAt_zero_of_chartFlowGeodesicMatchData
    (g : SmoothRiemannianMetric I M) (p : M)
    (h : HasChartFlowGeodesicMatchData (I := I) g p) :
    ContMDiffAt 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (0 : E) :=
  expMap_contMDiffAt_zero_of_chartFlowGeodesicMatch
    (I := I) (g := g) (p := p) h

end Headline

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
