import DifferentialGeometry.Geometry.Riemannian.Exponential.Bridge
import DifferentialGeometry.Geometry.Riemannian.Exponential.ChartIdentification
import DifferentialGeometry.Geometry.Riemannian.Exponential.ChartPushVFEq
import DifferentialGeometry.Geometry.Riemannian.Exponential.Definition
import DifferentialGeometry.Geometry.Riemannian.Geodesic.SmoothFlow

set_option linter.unusedSectionVars false

/-!
# `C^1` regularity of the chart-pushed geodesic flow in the initial velocity

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete finite-dimensional inner-product space `E`, the
chart-pushed phase-space flow
`Φ : (E × E) × ℝ → E × E` of `Geodesic/SmoothFlow.lean` is jointly `C^1`
on a strict open neighbourhood of `((extChartAt I p p, 0), 0)`. We
extract the `v`-slice smoothness at the zero velocity:

* for any time `t* ∈ Ioo(-T, T)` in the flow's time interval, the map
  `v ↦ Φ((extChartAt I p p, v), t*)` is `C^1` at `v = 0 ∈ E`;
* the manifold-valued candidate
  `chartFlowCandidate Φ p 0 v := (extChartAt I p).symm (Φ((extChartAt I p p, v), 0)).1`
  has its **chart-coordinate form**
  `v ↦ extChartAt I p (chartFlowCandidate Φ p 0 v)`
  `C^1` at `v = 0`; this form is the chart-image of the candidate, and
  the candidate's manifold-side smoothness reads through the base chart.

These two facts are the **substantive analytic content** of the
smoothness of the geodesic flow in the initial velocity at the zero
vector. The full headline
`ContDiffAt ℝ 1 (expMap g p) (0 : T_p M)`
is a consequence of these together with the bridge identification of
the chart-flow candidate with `expMap g p` on a neighbourhood of
`v = 0`. The bridge identification is delivered in
`ChartPushVFEq.lean` (at the eventually-near-`t = 0` level for each
individual `v`) and `Definition.lean` (at the pointwise `v = 0` level
via `expMap_zero`); the full uniform-in-`v` identification requires
additional ingredients (openness of `expDomain g p` at `v = 0`,
geodesic rescaling) which are tracked separately.

## Main results

* `contDiffAt_chartFlow_slice_fst_zero` — the first-coordinate `v`-slice
  of the chart-flow at any time in its time interval is `C^1` at `v = 0`.

* `exists_chartFlow_slice_contDiffAt_zero` — packaged existence of the
  chart-pushed flow with `C^1` `v`-slice smoothness at every time in
  its time interval.

* `chartFlowCandidate` — the manifold-valued candidate map
  `v ↦ (extChartAt I p).symm (Φ((x₀, v), t')).1`.

* `chartFlowCandidate_zero_at_initial` — value of the candidate at
  `v = 0`, `t' = 0` is `p`.

* `extChartAt_symm_comp_chartFlowCandidate_at_zero` — the candidate's
  chart-coordinate form agrees with the chart-flow's first coordinate
  on a neighbourhood of `v = 0` (at `t' = 0`).

* `chartFlowCandidate_chart_contDiffAt_zero_at_origin` — chart-coordinate
  `C^1` smoothness of the candidate at `v = 0` (for `t' = 0`).

* `exists_chartFlowCandidate_chart_contDiffAt_zero` — packaged
  existence of a chart-flow making the chart-coord-form candidate
  `C^1` at `v = 0`, with value `p` at `v = 0`.
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

section ChartCoordSlice

variable [I.Boundaryless] [CompleteSpace E]

/-- The `v`-slice of a jointly-`C^1` chart-flow `Φ` at a fixed time `t*`:
`v ↦ Φ((x₀, v), t*)` is `C^1` at `v = 0`, provided `((x₀, 0), t*)` lies
in the open ball-times-`Ioo` domain on which `Φ` is `C^1`. -/
lemma contDiffAt_chartFlow_slice_zero
    {Φ : (E × E) × ℝ → E × E} {x₀ : E} {ρ T t' : ℝ}
    (hρ : 0 < ρ) (ht' : t' ∈ Set.Ioo (-T) T)
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T)) :
    ContDiffAt ℝ 1 (fun v : E => Φ (((x₀, v) : E × E), t')) (0 : E) := by
  have hpair_cd : ContDiff ℝ 1 (fun v : E => (((x₀, v) : E × E), t')) := by
    have h_const_x₀ : ContDiff ℝ 1 (fun _ : E => x₀) := contDiff_const
    have h_id : ContDiff ℝ 1 (fun v : E => v) := contDiff_id
    have h_pair_E2 : ContDiff ℝ 1 (fun v : E => ((x₀, v) : E × E)) :=
      h_const_x₀.prodMk h_id
    have h_const_t : ContDiff ℝ 1 (fun _ : E => t') := contDiff_const
    exact h_pair_E2.prodMk h_const_t
  have hΦ_cda : ContDiffAt ℝ 1 Φ (((x₀, (0 : E)) : E × E), t') := by
    apply hcd.contDiffAt
    have hopen : IsOpen ((Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T) :=
      Metric.isOpen_ball.prod isOpen_Ioo
    refine hopen.mem_nhds ?_
    exact ⟨Metric.mem_ball_self hρ, ht'⟩
  exact hΦ_cda.comp (0 : E) hpair_cd.contDiffAt

/-- The first-component projection of the chart-flow's `v`-slice is
`C^1` at `v = 0`. -/
lemma contDiffAt_chartFlow_slice_fst_zero
    {Φ : (E × E) × ℝ → E × E} {x₀ : E} {ρ T t' : ℝ}
    (hρ : 0 < ρ) (ht' : t' ∈ Set.Ioo (-T) T)
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((x₀, (0 : E)) : E × E) ρ) ×ˢ Set.Ioo (-T) T)) :
    ContDiffAt ℝ 1 (fun v : E => (Φ (((x₀, v) : E × E), t')).1) (0 : E) := by
  have hslice := contDiffAt_chartFlow_slice_zero (Φ := Φ) (x₀ := x₀)
    (ρ := ρ) (T := T) (t' := t') hρ ht' hcd
  have hfst : ContDiff ℝ 1 (Prod.fst : E × E → E) := contDiff_fst
  exact hfst.contDiffAt.comp (0 : E) hslice

end ChartCoordSlice

section ManifoldCandidate

variable [I.Boundaryless]

/-- The manifold-valued candidate map produced from a chart-flow `Φ`:
`v ↦ (extChartAt I p).symm (Φ((extChartAt I p p, v), t')).1`. -/
def chartFlowCandidate (Φ : (E × E) × ℝ → E × E) (p : M) (t' : ℝ) :
    E → M :=
  fun v => (extChartAt I p).symm (Φ (((extChartAt I p p, v) : E × E), t')).1

@[simp] lemma chartFlowCandidate_apply
    (Φ : (E × E) × ℝ → E × E) (p : M) (t' : ℝ) (v : E) :
    chartFlowCandidate (I := I) Φ p t' v =
      (extChartAt I p).symm (Φ (((extChartAt I p p, v) : E × E), t')).1 := rfl

/-- At `t' = 0` and `v = 0`, the candidate returns `p` when the chart-flow
satisfies its base initial-value identity. -/
lemma chartFlowCandidate_zero_at_initial
    {Φ : (E × E) × ℝ → E × E} {p : M}
    (hinit : Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
      (extChartAt I p p, (0 : E))) :
    chartFlowCandidate (I := I) Φ p 0 (0 : E) = p := by
  unfold chartFlowCandidate
  rw [hinit]
  exact (extChartAt I p).left_inv (mem_extChartAt_source (I := I) p)

end ManifoldCandidate

section CandidateChartCoord

variable [I.Boundaryless] [CompleteSpace E]

/-- **Eventually-near-`v = 0` chart-rewrite of the candidate at `t' = 0`.**
For the chart-pushed flow at base `(x₀, 0)`, the chart-flow at `v = 0`,
`t' = 0` returns `(x₀, 0)`. By continuity of the slice's first
coordinate, the value stays in the chart target on a neighbourhood of
`v = 0`, where the chart-symm-then-chart composition is the identity. -/
lemma extChartAt_symm_comp_chartFlowCandidate_at_zero
    {p : M} {Φ : (E × E) × ℝ → E × E} {ρ T : ℝ}
    (hρ : 0 < ρ) (hT : 0 < T)
    (hinit : Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
      (extChartAt I p p, (0 : E)))
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T)) :
    ∀ᶠ v in 𝓝 (0 : E),
      extChartAt I p (chartFlowCandidate (I := I) Φ p 0 v) =
        (Φ (((extChartAt I p p, v) : E × E), 0)).1 := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have ht0 : (0 : ℝ) ∈ Set.Ioo (-T) T := ⟨by linarith, hT⟩
  have hcd_slice_fst :
      ContDiffAt ℝ 1 (fun v : E => (Φ (((x₀, v) : E × E), (0 : ℝ))).1) (0 : E) :=
    contDiffAt_chartFlow_slice_fst_zero (Φ := Φ) (x₀ := x₀)
      (ρ := ρ) (T := T) (t' := 0) hρ ht0 hcd
  have hcont0 : ContinuousAt
      (fun v : E => (Φ (((x₀, v) : E × E), (0 : ℝ))).1) (0 : E) :=
    hcd_slice_fst.continuousAt
  have hval0 : (Φ (((x₀, (0 : E)) : E × E), (0 : ℝ))).1 = x₀ := by
    rw [hinit]
  have hx₀_src : p ∈ (extChartAt I p).source :=
    mem_extChartAt_source (I := I) p
  have hx₀_target : x₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hx₀_src
  have hx₀_target_open : x₀ ∈ interior (extChartAt I p).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) p hx₀_target
  have htarget_nhds : (extChartAt I p).target ∈ 𝓝 x₀ :=
    mem_nhds_iff.mpr ⟨interior (extChartAt I p).target, interior_subset,
      isOpen_interior, hx₀_target_open⟩
  have htarget_preimage : ∀ᶠ v in 𝓝 (0 : E),
      (Φ (((x₀, v) : E × E), (0 : ℝ))).1 ∈ (extChartAt I p).target := by
    apply hcont0.preimage_mem_nhds
    rw [hval0]; exact htarget_nhds
  filter_upwards [htarget_preimage] with v hv
  simp only [chartFlowCandidate_apply]
  exact (extChartAt I p).right_inv hv

/-- **Chart-coordinate `C^1` smoothness of the candidate at `t' = 0`.**
The chart-coordinate form of the manifold-valued candidate at the time
`t' = 0`, viewed as a function of the initial velocity, is `C^1` at
`v = 0`. -/
lemma chartFlowCandidate_chart_contDiffAt_zero_at_origin
    {p : M} {Φ : (E × E) × ℝ → E × E} {ρ T : ℝ}
    (hρ : 0 < ρ) (hT : 0 < T)
    (hinit : Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
      (extChartAt I p p, (0 : E)))
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T)) :
    ContDiffAt ℝ 1
      (fun v : E => extChartAt I p (chartFlowCandidate (I := I) Φ p 0 v))
      (0 : E) := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have ht0 : (0 : ℝ) ∈ Set.Ioo (-T) T := ⟨by linarith, hT⟩
  have hslice :
      ContDiffAt ℝ 1 (fun v : E => (Φ (((x₀, v) : E × E), (0 : ℝ))).1) (0 : E) :=
    contDiffAt_chartFlow_slice_fst_zero (Φ := Φ) (x₀ := x₀)
      (ρ := ρ) (T := T) (t' := 0) hρ ht0 hcd
  have hev := extChartAt_symm_comp_chartFlowCandidate_at_zero
    (I := I) (p := p) (Φ := Φ) (ρ := ρ) (T := T) hρ hT hinit hcd
  exact hslice.congr_of_eventuallyEq hev

end CandidateChartCoord

section Headline

variable [I.Boundaryless] [CompleteSpace E]

/-- **Headline existence: chart-pushed flow with `v`-slice `C^1`
smoothness.** For any base point `p : M`, the V.4 chart-pushed flow at
`(extChartAt I p p, 0)` delivers a jointly-`C^1` flow `Φ` whose
`v`-slice at every time `t' ∈ Ioo(-T, T)` is `C^1` at `v = 0`. -/
theorem exists_chartFlow_slice_contDiffAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ (ρ T : ℝ) (Φ : (E × E) × ℝ → E × E),
      0 < ρ ∧ 0 < T ∧
      ContDiffOn ℝ 1 Φ
        ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
          Set.Ioo (-T) T) ∧
      Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
        (extChartAt I p p, (0 : E)) ∧
      (∀ (t' : ℝ), t' ∈ Set.Ioo (-T) T →
        ContDiffAt ℝ 1
          (fun v : E => (Φ (((extChartAt I p p, v) : E × E), t')).1)
          (0 : E)) := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have hx₀_src : p ∈ (extChartAt I p).source :=
    mem_extChartAt_source (I := I) p
  have hx₀_target : x₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source hx₀_src
  have hx₀_interior : x₀ ∈ interior (extChartAt I p).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) p hx₀_target
  obtain ⟨_b, ρ, T, Φ, hρ_pos, hT_pos, _hb_sub, hcd, hinit⟩ :=
    DifferentialGeometry.Geometry.Riemannian.Geodesic.exists_chartPhase_contDiffOn_isLocalFlow
      (I := I) (M := M) (g := g) (α := p) (x₀ := x₀) (v₀ := (0 : E)) hx₀_interior
  refine ⟨ρ, T, Φ, hρ_pos, hT_pos, hcd, hinit, ?_⟩
  intro t' ht'
  exact contDiffAt_chartFlow_slice_fst_zero (Φ := Φ) (x₀ := x₀)
    (ρ := ρ) (T := T) (t' := t') hρ_pos ht' hcd

/-- **Headline existence: manifold-valued candidate with chart-coordinate
`C^1` smoothness at `v = 0`.** For any base point `p : M`, there exists a
chart-pushed flow `Φ` such that the manifold-valued candidate's
chart-coordinate form is `C^1` at `v = 0`, and the candidate's value at
`v = 0` is `p`. -/
theorem exists_chartFlowCandidate_chart_contDiffAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ (Φ : (E × E) × ℝ → E × E),
      ContDiffAt ℝ 1
        (fun v : E => extChartAt I p (chartFlowCandidate (I := I) Φ p 0 v))
        (0 : E) ∧
      chartFlowCandidate (I := I) Φ p 0 (0 : E) = p := by
  classical
  obtain ⟨ρ, T, Φ, hρ_pos, hT_pos, hcd, hinit, _⟩ :=
    exists_chartFlow_slice_contDiffAt_zero (I := I) (g := g) (p := p)
  refine ⟨Φ, ?_, ?_⟩
  · exact chartFlowCandidate_chart_contDiffAt_zero_at_origin
      (I := I) (p := p) (Φ := Φ) (ρ := ρ) (T := T) hρ_pos hT_pos hinit hcd
  · exact chartFlowCandidate_zero_at_initial (I := I) (Φ := Φ) (p := p) hinit

/-- **Continuity of the manifold-valued candidate at `v = 0`.** -/
lemma chartFlowCandidate_continuousAt_zero_at_origin
    {p : M} {Φ : (E × E) × ℝ → E × E} {ρ T : ℝ}
    (hρ : 0 < ρ) (hT : 0 < T)
    (hinit : Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
      (extChartAt I p p, (0 : E)))
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T)) :
    ContinuousAt (chartFlowCandidate (I := I) Φ p 0) (0 : E) := by
  classical
  set x₀ : E := extChartAt I p p with hx₀_def
  have ht0 : (0 : ℝ) ∈ Set.Ioo (-T) T := ⟨by linarith, hT⟩
  have hslice :
      ContDiffAt ℝ 1 (fun v : E => (Φ (((x₀, v) : E × E), (0 : ℝ))).1) (0 : E) :=
    contDiffAt_chartFlow_slice_fst_zero (Φ := Φ) (x₀ := x₀)
      (ρ := ρ) (T := T) (t' := 0) hρ ht0 hcd
  have hcont_slice : ContinuousAt
      (fun v : E => (Φ (((x₀, v) : E × E), (0 : ℝ))).1) (0 : E) :=
    hslice.continuousAt
  have hval0 : (Φ (((x₀, (0 : E)) : E × E), (0 : ℝ))).1 = x₀ := by
    rw [hinit]
  have hsymm_cont : ContinuousAt (extChartAt I p).symm x₀ :=
    continuousAt_extChartAt_symm (I := I) p
  have hcont_slice' : ContinuousAt
      (fun v : E => (Φ (((x₀, v) : E × E), (0 : ℝ))).1) (0 : E) := hcont_slice
  have hsymm_at_x₀ : ContinuousAt (fun y : E => (extChartAt I p).symm y) x₀ := hsymm_cont
  have hcomp_step : ContinuousAt
      (fun v : E => (extChartAt I p).symm
        ((fun v' : E => (Φ (((x₀, v') : E × E), (0 : ℝ))).1) v))
      (0 : E) := by
    refine ContinuousAt.comp ?_ hcont_slice'
    show ContinuousAt (extChartAt I p).symm (Φ (((x₀, (0 : E)) : E × E), (0 : ℝ))).1
    rw [hval0]
    exact hsymm_at_x₀
  exact hcomp_step

/-- **Manifold-side `ContMDiffAt 1` smoothness of the candidate at
`v = 0`.** The manifold-valued candidate `chartFlowCandidate Φ p 0 : E → M`
is `ContMDiffAt 𝓘(ℝ, E) I 1` at `v = 0`. -/
lemma chartFlowCandidate_contMDiffAt_zero_at_origin
    {p : M} {Φ : (E × E) × ℝ → E × E} {ρ T : ℝ}
    (hρ : 0 < ρ) (hT : 0 < T)
    (hinit : Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
      (extChartAt I p p, (0 : E)))
    (hcd : ContDiffOn ℝ 1 Φ
      ((Metric.ball ((extChartAt I p p, (0 : E)) : E × E) ρ) ×ˢ
        Set.Ioo (-T) T)) :
    ContMDiffAt 𝓘(ℝ, E) I 1 (chartFlowCandidate (I := I) Φ p 0) (0 : E) := by
  classical
  rw [contMDiffAt_iff]
  refine ⟨?_, ?_⟩
  · exact chartFlowCandidate_continuousAt_zero_at_origin
      (I := I) (p := p) (Φ := Φ) (ρ := ρ) (T := T) hρ hT hinit hcd
  · have hval : chartFlowCandidate (I := I) Φ p 0 (0 : E) = p :=
      chartFlowCandidate_zero_at_initial (I := I) (Φ := Φ) (p := p) hinit
    rw [hval]
    have hchart_cd :
        ContDiffAt ℝ 1
          (fun v : E => extChartAt I p (chartFlowCandidate (I := I) Φ p 0 v))
          (0 : E) :=
      chartFlowCandidate_chart_contDiffAt_zero_at_origin
        (I := I) (p := p) (Φ := Φ) (ρ := ρ) (T := T) hρ hT hinit hcd
    have hsimp_range : (range (𝓘(ℝ, E) : ModelWithCorners ℝ E E)) = Set.univ :=
      ModelWithCorners.range_eq_univ _
    have hsimp_base : (extChartAt (𝓘(ℝ, E) : ModelWithCorners ℝ E E) (0 : E)) (0 : E) =
        (0 : E) := by simp
    rw [hsimp_base, hsimp_range]
    have hsymm_id : ∀ v : E, (extChartAt (𝓘(ℝ, E) : ModelWithCorners ℝ E E) (0 : E)).symm v = v := by
      intro v; simp
    change ContDiffWithinAt ℝ 1
        (extChartAt I p ∘ chartFlowCandidate (I := I) Φ p 0 ∘
          (extChartAt (𝓘(ℝ, E) : ModelWithCorners ℝ E E) (0 : E)).symm)
        Set.univ (0 : E)
    have hgoal_eq :
        (extChartAt I p ∘ chartFlowCandidate (I := I) Φ p 0 ∘
          (extChartAt (𝓘(ℝ, E) : ModelWithCorners ℝ E E) (0 : E)).symm) =
        (fun v : E => extChartAt I p (chartFlowCandidate (I := I) Φ p 0 v)) := by
      ext v; simp [Function.comp]
    rw [hgoal_eq]
    exact hchart_cd.contDiffWithinAt

/-- **Manifold-side existence of a `ContMDiffAt 1` candidate at `v = 0`.**
For any base point `p : M`, there exists a chart-pushed flow `Φ` such
that the manifold-valued candidate `chartFlowCandidate Φ p 0 : E → M` is
`ContMDiffAt 𝓘(ℝ, E) I 1` at `v = 0`, with value `p` at `v = 0`. -/
theorem exists_chartFlowCandidate_contMDiffAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ (Φ : (E × E) × ℝ → E × E),
      ContMDiffAt 𝓘(ℝ, E) I 1 (chartFlowCandidate (I := I) Φ p 0) (0 : E) ∧
      chartFlowCandidate (I := I) Φ p 0 (0 : E) = p := by
  classical
  obtain ⟨ρ, T, Φ, hρ_pos, hT_pos, hcd, hinit, _⟩ :=
    exists_chartFlow_slice_contDiffAt_zero (I := I) (g := g) (p := p)
  refine ⟨Φ, ?_, ?_⟩
  · exact chartFlowCandidate_contMDiffAt_zero_at_origin
      (I := I) (p := p) (Φ := Φ) (ρ := ρ) (T := T) hρ_pos hT_pos hinit hcd
  · exact chartFlowCandidate_zero_at_initial (I := I) (Φ := Φ) (p := p) hinit

end Headline

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
