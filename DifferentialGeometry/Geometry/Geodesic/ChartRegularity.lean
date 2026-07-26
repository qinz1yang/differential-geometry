import DifferentialGeometry.Analysis.ODE.SecondOrderBootstrap
import DifferentialGeometry.Geometry.Geodesic.CrossVFReduction
import DifferentialGeometry.Geometry.Geodesic.SmoothFlow

set_option linter.unusedSectionVars false

/-!
# Chart regularity of geodesics

A curve satisfying the (moving-foot) geodesic equation on an open time window,
continuously and with foot staying in one chart source, has `C^∞` chart reading
there — together with its derivative.  This is the fixed-chart regularity
upgrade behind global-in-time smoothness of geodesics: on any window contained
in a single chart the chart reading solves the autonomous second-order ODE
`u'' = -Γ(u)(u', u')` with `C^∞` coefficients, so the ODE bootstrap
`contDiffOn_ode2_inf` applies.

## Main result

* `chartCurve_contDiffOn` — on an open `O ⊆ ℝ` where `γ` is continuous,
  `γ s ∈ (chartAt H q).source`, and `HasGeodesicEquationAt g γ s` for every
  `s ∈ O`, the chart reading `chartCurve q γ` and its derivative are
  `C^∞` on `O`.

The two fixed-chart ODE inputs are the existing bridges
`hasGeodesicEquationAt_fixedChart_eventually_hasDerivAt` and
`hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity`
(`CrossVFReduction.lean`); the coefficient smoothness is
`chartChristoffelContraction_contDiffOn` (`SmoothFlow.lean`).
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

open DifferentialGeometry.Geometry.Riemannian.AlongCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Chart reading of a geodesic window is `C^∞`.**  If `γ` is continuous on an
open `O ⊆ ℝ`, keeps its foot in `(chartAt H q).source`, and satisfies the
geodesic equation at every `s ∈ O`, then the fixed-chart reading
`chartCurve q γ` and its derivative are `C^∞` on `O`. -/
theorem chartCurve_contDiffOn [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (q : M) {γ : ℝ → M} {O : Set ℝ}
    (hO : IsOpen O) (hγ_cont : ContinuousOn γ O)
    (hsrc : ∀ s ∈ O, γ s ∈ (chartAt H q).source)
    (hgeo : ∀ s ∈ O, HasGeodesicEquationAt (I := I) g γ s) :
    ContDiffOn ℝ ∞ (chartCurve (I := I) q γ) O ∧
      ContDiffOn ℝ ∞ (deriv (chartCurve (I := I) q γ)) O := by
  classical
  set u : ℝ → E := chartCurve (I := I) q γ with hu
  have hcontAt : ∀ s ∈ O, ContinuousAt γ s := fun s hs =>
    (hγ_cont s hs).continuousAt (hO.mem_nhds hs)
  have hy₁ : ∀ s ∈ O, HasDerivAt u (deriv u s) s := fun s hs =>
    (hasGeodesicEquationAt_fixedChart_eventually_hasDerivAt (I := I) g q
      (hcontAt s hs) (hsrc s hs) (hgeo s hs)).self_of_nhds
  have hy₂ : ∀ s ∈ O, HasDerivAt (deriv u)
      ((fun z : E × E =>
          - chartChristoffelContraction (I := I) g q z.2 z.2 z.1)
        (u s, deriv u s)) s := fun s hs =>
    hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity (I := I) g q
      (hcontAt s hs) (hsrc s hs) (hgeo s hs)
  have hmem : ∀ s ∈ O, (u s, deriv u s) ∈
      (interior (extChartAt I q).target) ×ˢ (Set.univ : Set E) := by
    intro s hs
    refine ⟨?_, Set.mem_univ _⟩
    have hsrc' : γ s ∈ (extChartAt I q).source := by
      rw [extChartAt_source]; exact hsrc s hs
    have htgt : extChartAt I q (γ s) ∈ (extChartAt I q).target :=
      (extChartAt I q).map_source hsrc'
    have hus : u s = extChartAt I q (γ s) := by rw [hu, chartCurve_def]
    rw [hus, (isOpen_extChartAt_target (I := I) q).interior_eq]
    exact htgt
  have hF : ContDiffOn ℝ ∞
      (fun z : E × E => - chartChristoffelContraction (I := I) g q z.2 z.2 z.1)
      ((interior (extChartAt I q).target) ×ˢ (Set.univ : Set E)) :=
    (chartChristoffelContraction_contDiffOn (I := I) g q).neg
  exact contDiffOn_ode2_inf hO hF hmem hy₁ hy₂

/-- **`C^∞`-in-time regularity of a moving-foot geodesic (pointwise).**  An
intrinsic moving-foot geodesic `γ` on an open set `s`, continuous on `s`, is
`ContMDiffAt 𝓘(ℝ, ℝ) I ∞` at every `t ∈ s`.  The `C^∞` upgrade of
`isGeodesicOn_contMDiffAt_one`: the chart window around `t` supplies a `C^∞`
chart reading via `chartCurve_contDiffOn`, and the chart round-trip transfers
it to `γ`. -/
theorem isGeodesicOn_contMDiffAt_infty [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hs : IsOpen s) (ht : t ∈ s)
    (hγ : IsGeodesicOn (I := I) g γ s) (hcont : ContinuousOn γ s) :
    ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ t := by
  classical
  set α : M := γ t with hα_def
  set u : ℝ → E := chartCurve (I := I) α γ with hu_def
  have hα_src : α ∈ (chartAt H α).source := mem_chart_source H α
  -- the open chart window around `t`
  set O : Set ℝ := s ∩ γ ⁻¹' (chartAt H α).source with hO_def
  have hO_open : IsOpen O :=
    hcont.isOpen_inter_preimage hs (chartAt H α).open_source
  have htO : t ∈ O := ⟨ht, by rw [Set.mem_preimage, ← hα_def]; exact hα_src⟩
  have hu_cdOn : ContDiffOn ℝ ∞ u O :=
    (chartCurve_contDiffOn (I := I) g α hO_open
      (hcont.mono Set.inter_subset_left) (fun r hr => hr.2)
      (fun r hr => hγ r hr.1)).1
  have hu_cd : ContDiffAt ℝ ∞ u t :=
    hu_cdOn.contDiffAt (hO_open.mem_nhds htO)
  have hu_cmd : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ u t := hu_cd.contMDiffAt
  -- the inverse chart is `C^∞` at `u t`
  have hα_ext_src : α ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hα_src
  have hut_eq : u t = extChartAt I α α := by
    rw [hu_def, chartCurve_def, hα_def]
  have hut_target : u t ∈ (extChartAt I α).target := by
    rw [hut_eq]; exact (extChartAt I α).map_source hα_ext_src
  have htarget_nhds : (extChartAt I α).target ∈ 𝓝 (u t) :=
    (isOpen_extChartAt_target (I := I) α).mem_nhds hut_target
  have hsymm_at : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I α).symm (u t) :=
    (contMDiffWithinAt_extChartAt_symm_target (I := I) α hut_target).contMDiffAt
      htarget_nhds
  have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ ((extChartAt I α).symm ∘ u) t :=
    hsymm_at.comp t hu_cmd
  -- `γ` agrees with the chart round-trip near `t`
  have hcontAt_t : ContinuousAt γ t := hcont.continuousAt (hs.mem_nhds ht)
  have hsrc_nhds : (fun r => γ r) ⁻¹' (chartAt H α).source ∈ 𝓝 t :=
    hcontAt_t.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hα_src)
  have heq : ((extChartAt I α).symm ∘ u) =ᶠ[𝓝 t] γ := by
    filter_upwards [hsrc_nhds] with r hr
    have hr_ext : γ r ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hr
    change (extChartAt I α).symm (u r) = γ r
    rw [hu_def, chartCurve_def]
    exact (extChartAt I α).left_inv hr_ext
  exact hcomp.congr_of_eventuallyEq heq.symm

/-- **`C^∞`-in-time regularity of a moving-foot geodesic (on an open set).**
The `C^∞` upgrade of `isGeodesicOn_contMDiffOn_one`. -/
theorem isGeodesicOn_contMDiffOn_infty [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ}
    (hs : IsOpen s)
    (hγ : IsGeodesicOn (I := I) g γ s) (hcont : ContinuousOn γ s) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ s := fun _t ht =>
  (isGeodesicOn_contMDiffAt_infty (I := I) g hs ht hγ hcont).contMDiffWithinAt

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry
