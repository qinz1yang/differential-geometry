import DifferentialGeometry.Geometry.Geodesic.Flow.VectorField
import DifferentialGeometry.Geometry.Geodesic.Equation.Basic
import DifferentialGeometry.Geometry.Geodesic.Equation.FromIntegralCurve
import DifferentialGeometry.Geometry.Geodesic.Local.Uniqueness
import DifferentialGeometry.Geometry.Geodesic.Equation.ProjectionDerivative
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Chart.Transition
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Mul

open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.AlongCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [NeZero (Module.finrank ℝ E)] in
theorem gc_vf_chart_coincidence
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α α' : M)
    {f : ℝ → TangentBundle I M} {t₀ : ℝ}
    (hα : (f t₀).proj ∈ (chartAt H α).source)
    (hα' : (f t₀).proj ∈ (chartAt H α').source)
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α) t₀) :
    IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g α') t₀ := by
  classical
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hf_contAt : ContinuousAt f t₀ := hf.continuousAt
  have hproj_contAt : ContinuousAt (fun t => (f t).proj) t₀ :=
    hπ_cont.continuousAt.comp hf_contAt
  have hα_nhds : (fun t => (f t).proj) ⁻¹' (chartAt H α).source ∈ 𝓝 t₀ :=
    hproj_contAt.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hα)
  have hα'_nhds : (fun t => (f t).proj) ⁻¹' (chartAt H α').source ∈ 𝓝 t₀ :=
    hproj_contAt.preimage_mem_nhds ((chartAt H α').open_source.mem_nhds hα')
  unfold IsMIntegralCurveAt at hf ⊢
  filter_upwards [hf, hα_nhds, hα'_nhds] with t htD ht_α ht_α'
  have ht_α2 : (f t).proj ∈ (chartAt H α).source := ht_α
  have ht_α'2 : (f t).proj ∈ (chartAt H α').source := ht_α'
  have hvf_eq : geodesicVectorFieldChart (I := I) g α (f t) =
      geodesicVectorFieldChart (I := I) g α' (f t) :=
    geodesicVectorFieldChart_eq_of_proj_mem (I := I) g α α' (p := f t) ht_α2 ht_α'2
  exact hvf_eq ▸ htD

omit [NeZero (Module.finrank ℝ E)] in
theorem gc_cross_vf_projection_uniqueness
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t₀) :
    ∃ f₁ : ℝ → TangentBundle I M,
      (f₁ t₀).proj = γ t₀ ∧
      IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀ ∧
      γ =ᶠ[𝓝 t₀] (fun t => (f₁ t).proj) := by
  classical
  obtain ⟨α, f, hproj, hα_source, hf⟩ := hγ
  have hft₀ : (f t₀).proj = γ t₀ := hproj t₀
  have hγt₀_source : (f t₀).proj ∈ (chartAt H (γ t₀)).source := by
    rw [hft₀]; exact mem_chart_source H (γ t₀)
  obtain ⟨f₁, hf₁_initial, hf₁⟩ :=
    exists_chartCenteredLift_at (I := I) g (γ t₀) ((f t₀).snd : E) t₀
  have hf₁_proj : (f₁ t₀).proj = γ t₀ := by rw [hf₁_initial]
  refine ⟨f₁, hf₁_proj, hf₁, ?_⟩
  have hf_at_γ : IsMIntegralCurveAt f
      (geodesicVectorFieldChart (I := I) g (γ t₀)) t₀ :=
    gc_vf_chart_coincidence (I := I) g α (γ t₀) hα_source hγt₀_source hf
  have h0 : f₁ t₀ = f t₀ := by
    rw [hf₁_initial]
    rw [← hft₀]
  have hfe : f₁ =ᶠ[𝓝 t₀] f := by
    have hsrc₁ : (f₁ t₀).proj ∈ (chartAt H (γ t₀)).source := by
      rw [hf₁_proj]; exact mem_chart_source H (γ t₀)
    exact isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
      (I := I) (g := g) (α := γ t₀) (t₀ := t₀)
      (f₁ := f₁) (f₂ := f) hsrc₁ hf₁ hf_at_γ h0
  filter_upwards [hfe] with t ht
  rw [ht, hproj t]

omit [NeZero (Module.finrank ℝ E)] in
theorem IsGeodesicAt.hasGeodesicEquationAt
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t₀) :
    HasGeodesicEquationAt (I := I) g γ t₀ := by
  obtain ⟨f₁, hf₁_proj_t₀, hf₁, hcross⟩ :=
    gc_cross_vf_projection_uniqueness (I := I) (g := g) (γ := γ) (t₀ := t₀) hγ
  exact IsGeodesicAt.hasGeodesicEquationAt_of_chartCentered_lift_eventuallyEq
    (I := I) (g := g) (γ := γ) (t₀ := t₀) (f₁ := f₁) hf₁ hf₁_proj_t₀ hcross

section MovingFootToFixedChart

variable [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] in
theorem hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity
    (g : SmoothRiemannianMetric I M) (y : M) {γ : ℝ → M} {t : ℝ}
    (hγ_cont : ContinuousAt γ t)
    (hy : γ t ∈ (chartAt H y).source)
    (h : HasGeodesicEquationAt (I := I) g γ t) :
    HasDerivAt (deriv (chartCurve (I := I) y γ))
      (- chartChristoffelContraction (I := I) g y
          (deriv (chartCurve (I := I) y γ) t)
          (deriv (chartCurve (I := I) y γ) t)
          (chartCurve (I := I) y γ t)) t := by
  classical
  set α : M := γ t with hα_def
  set x : E := chartCurve (I := I) α γ t with hx_def
  obtain ⟨v, a, hv0, hev0, ha0, hgeo⟩ := h
  have hwdef : chartLocalCurve (I := I) γ t = chartCurve (I := I) α γ := by
    funext s; rw [chartLocalCurve_def, hα_def, chartCurve_def]
  rw [hwdef] at hv0 hev0 ha0
  have hα_source : γ t ∈ (chartAt H α).source := by
    rw [hα_def]; exact mem_chart_source H (γ t)
  have hx_source : x ∈ chartTransitionSource (I := I) α y :=
    extChartAt_mem_chartTransitionSource (I := I) α y hα_source hy
  have hx_eq : x = extChartAt I (γ t) (γ t) := by rw [hx_def, chartCurve_def, hα_def]
  have hboth_nhds : (fun s => γ s) ⁻¹'
      ((chartAt H α).source ∩ (chartAt H y).source) ∈ 𝓝 t :=
    hγ_cont.preimage_mem_nhds
      (((chartAt H α).open_source.inter (chartAt H y).open_source).mem_nhds ⟨hα_source, hy⟩)
  set u : ℝ → E := chartCurve (I := I) y γ with hu_def
  set w : ℝ → E := chartCurve (I := I) α γ with hw_def
  have hwt : w t = x := by rw [hw_def, hx_def]
  have hcurve_eq : u =ᶠ[𝓝 t]
      (fun s => chartTransitionMap (I := I) α y (w s)) := by
    filter_upwards [hboth_nhds] with s hs
    obtain ⟨hsα, _hsy⟩ := hs
    rw [hu_def, hw_def, chartCurve_def, chartCurve_def]
    exact (chartTransitionMap_apply_extChartAt (I := I) α y hsα).symm
  have hTdiff : ∀ {z : E}, z ∈ chartTransitionSource (I := I) α y →
      DifferentiableAt ℝ (chartTransitionMap (I := I) α y) z :=
    fun hz => chartTransitionMap_differentiableAt (I := I) α y hz
  have hu_hasDerivAt_ev : ∀ᶠ s in 𝓝 t,
      HasDerivAt u (chartTransitionAt (I := I) α y (w s) (deriv w s)) s := by
    filter_upwards [hev0, hboth_nhds, hcurve_eq.eventually_nhds] with s hs hs_both hs_eq
    have hws_source : w s ∈ chartTransitionSource (I := I) α y := by
      rw [hw_def, chartCurve_def]
      exact extChartAt_mem_chartTransitionSource (I := I) α y hs_both.1 hs_both.2
    have hcomp : HasDerivAt
        (fun r => chartTransitionMap (I := I) α y (w r))
        (chartTransitionAt (I := I) α y (w s) (deriv w s)) s := by
      have := (hTdiff hws_source).hasFDerivAt.comp_hasDerivAt s hs
      change HasDerivAt
        (fun r => chartTransitionMap (I := I) α y (w r))
        (chartTransitionAt (I := I) α y (w s) (deriv w s)) s at this
      exact this
    exact hcomp.congr_of_eventuallyEq hs_eq
  have hdw_t : deriv w t = v := hv0.deriv
  have hu_deriv_t : HasDerivAt u (chartTransitionAt (I := I) α y x v) t := by
    have h0 := hu_hasDerivAt_ev.self_of_nhds
    rwa [hwt, hdw_t] at h0
  have hderiv_u_t : deriv u t = chartTransitionAt (I := I) α y x v := hu_deriv_t.deriv
  have hderiv_u_ev : (fun s => deriv u s) =ᶠ[𝓝 t]
      (fun s => chartTransitionAt (I := I) α y (w s) (deriv w s)) := by
    filter_upwards [hu_hasDerivAt_ev] with s hds
    exact hds.deriv
  have hAdiff : DifferentiableAt ℝ
      (fun z => (chartTransitionAt (I := I) α y z : E →L[ℝ] E)) x := by
    have h_open : IsOpen (chartTransitionSource (I := I) α y) :=
      chartTransitionSource_isOpen (I := I) α y
    exact ((chartTransitionAt_smooth (I := I) α y).contDiffAt
      (h_open.mem_nhds hx_source)).differentiableAt (by simp)
  have hAdiff_wt : DifferentiableAt ℝ
      (fun z => (chartTransitionAt (I := I) α y z : E →L[ℝ] E)) (w t) := by
    rw [hwt]; exact hAdiff
  have hcA : HasDerivAt
      (fun s => (chartTransitionAt (I := I) α y (w s) : E →L[ℝ] E))
      ((fderiv ℝ (fun z => chartTransitionAt (I := I) α y z) x) v) t := by
    have hc0 := hAdiff_wt.hasFDerivAt.comp_hasDerivAt t hv0
    rw [hwt] at hc0
    exact hc0
  have hVderiv : HasDerivAt
      (fun s => chartTransitionAt (I := I) α y (w s) (deriv w s))
      (((fderiv ℝ (fun z => chartTransitionAt (I := I) α y z) x) v) v
        + chartTransitionAt (I := I) α y x a) t := by
    have hclm := hcA.clm_apply ha0
    rw [hwt, hdw_t] at hclm
    exact hclm
  have hUderiv : HasDerivAt (deriv u)
      (((fderiv ℝ (fun z => chartTransitionAt (I := I) α y z) x) v) v
        + chartTransitionAt (I := I) α y x a) t :=
    hVderiv.congr_of_eventuallyEq hderiv_u_ev
  have hfoot :
      ((fderiv ℝ (fun z => chartTransitionAt (I := I) α y z) x) v) v =
        chartTransitionAt (I := I) α y x
          (chartTransitionSecondDerivCorrection (I := I) α y v v x) :=
    fderiv_chartTransitionAt_apply_eq_pushCorrection (I := I) α y hx_source v v
  have htransform :
      chartChristoffelContraction (I := I) g α v v x =
        chartTransitionAt (I := I) y α (chartTransitionMap (I := I) α y x)
            (chartChristoffelContraction (I := I) g y
              (chartTransitionAt (I := I) α y x v)
              (chartTransitionAt (I := I) α y x v)
              (chartTransitionMap (I := I) α y x))
          + chartTransitionSecondDerivCorrection (I := I) α y v v x := by
    rw [hx_eq]
    exact chartChristoffelContraction_transform (I := I) g α y hα_source hy v v
  have hu_t : u t = chartTransitionMap (I := I) α y x := by
    have hxα : x = extChartAt I α (γ t) := by rw [hx_def, hw_def, chartCurve_def]
    rw [hu_def, chartCurve_def, hxα]
    exact (chartTransitionMap_apply_extChartAt (I := I) α y hα_source).symm
  have hu'_t : deriv u t = chartTransitionAt (I := I) α y x v := hderiv_u_t
  have hDcollapse :
      ((fderiv ℝ (fun z => chartTransitionAt (I := I) α y z) x) v) v
        + chartTransitionAt (I := I) α y x a
        = - chartChristoffelContraction (I := I) g y
            (deriv u t) (deriv u t) (u t) := by
    have ha_eq : a = - chartChristoffelContraction (I := I) g α v v x := by
      rw [hx_eq]; exact eq_neg_of_add_eq_zero_left hgeo
    rw [hfoot, ha_eq, map_neg, ← sub_eq_add_neg, ← map_sub]
    have hsub :
        chartTransitionSecondDerivCorrection (I := I) α y v v x -
            chartChristoffelContraction (I := I) g α v v x =
          - chartTransitionAt (I := I) y α (chartTransitionMap (I := I) α y x)
              (chartChristoffelContraction (I := I) g y
                (chartTransitionAt (I := I) α y x v)
                (chartTransitionAt (I := I) α y x v)
                (chartTransitionMap (I := I) α y x)) := by
      rw [htransform]; abel
    rw [hsub, map_neg]
    have hinv := chartTransitionAt_reverse_comp (I := I) α y hx_source
    have hid := congrArg (fun L : E →L[ℝ] E => L
        (chartChristoffelContraction (I := I) g y
          (chartTransitionAt (I := I) α y x v)
          (chartTransitionAt (I := I) α y x v)
          (chartTransitionMap (I := I) α y x))) hinv
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hid
    rw [hid, hu_t, hu'_t]
  rw [hDcollapse] at hUderiv
  exact hUderiv

omit [NeZero (Module.finrank ℝ E)] in
theorem hasGeodesicEquationAt_fixedChart_eventually_hasDerivAt
    (g : SmoothRiemannianMetric I M) (y : M) {γ : ℝ → M} {t : ℝ}
    (hγ_cont : ContinuousAt γ t)
    (hy : γ t ∈ (chartAt H y).source)
    (h : HasGeodesicEquationAt (I := I) g γ t) :
    ∀ᶠ s in nhds t,
      HasDerivAt (chartCurve (I := I) y γ) (deriv (chartCurve (I := I) y γ) s) s := by
  classical
  set α : M := γ t with hα_def
  obtain ⟨v, a, hv0, hev0, ha0, hgeo⟩ := h
  have hwdef : chartLocalCurve (I := I) γ t = chartCurve (I := I) α γ := by
    funext s; rw [chartLocalCurve_def, hα_def, chartCurve_def]
  rw [hwdef] at hev0
  have hα_source : γ t ∈ (chartAt H α).source := by
    rw [hα_def]; exact mem_chart_source H (γ t)
  have hboth_nhds : (fun s => γ s) ⁻¹'
      ((chartAt H α).source ∩ (chartAt H y).source) ∈ 𝓝 t :=
    hγ_cont.preimage_mem_nhds
      (((chartAt H α).open_source.inter (chartAt H y).open_source).mem_nhds ⟨hα_source, hy⟩)
  set u : ℝ → E := chartCurve (I := I) y γ with hu_def
  set w : ℝ → E := chartCurve (I := I) α γ with hw_def
  have hcurve_eq : u =ᶠ[𝓝 t]
      (fun s => chartTransitionMap (I := I) α y (w s)) := by
    filter_upwards [hboth_nhds] with s hs
    obtain ⟨hsα, _hsy⟩ := hs
    rw [hu_def, hw_def, chartCurve_def, chartCurve_def]
    exact (chartTransitionMap_apply_extChartAt (I := I) α y hsα).symm
  have hTdiff : ∀ {z : E}, z ∈ chartTransitionSource (I := I) α y →
      DifferentiableAt ℝ (chartTransitionMap (I := I) α y) z :=
    fun hz => chartTransitionMap_differentiableAt (I := I) α y hz
  have hu_hasDerivAt_ev : ∀ᶠ s in 𝓝 t,
      HasDerivAt u (chartTransitionAt (I := I) α y (w s) (deriv w s)) s := by
    filter_upwards [hev0, hboth_nhds, hcurve_eq.eventually_nhds] with s hs hs_both hs_eq
    have hws_source : w s ∈ chartTransitionSource (I := I) α y := by
      rw [hw_def, chartCurve_def]
      exact extChartAt_mem_chartTransitionSource (I := I) α y hs_both.1 hs_both.2
    have hcomp : HasDerivAt
        (fun r => chartTransitionMap (I := I) α y (w r))
        (chartTransitionAt (I := I) α y (w s) (deriv w s)) s := by
      have := (hTdiff hws_source).hasFDerivAt.comp_hasDerivAt s hs
      change HasDerivAt
        (fun r => chartTransitionMap (I := I) α y (w r))
        (chartTransitionAt (I := I) α y (w s) (deriv w s)) s at this
      exact this
    exact hcomp.congr_of_eventuallyEq hs_eq
  filter_upwards [hu_hasDerivAt_ev] with s hs
  rw [hs.deriv]; exact hs

end MovingFootToFixedChart

omit [NeZero (Module.finrank ℝ E)] in
private lemma hasGeodesicEquationAt_comp_sub_const
    {g : SmoothRiemannianMetric I M} {η : ℝ → M} {T t : ℝ}
    (h : HasGeodesicEquationAt (I := I) g η (t - T)) :
    HasGeodesicEquationAt (I := I) g (fun s => η (s - T)) t := by
  obtain ⟨v, a, hv, hev, ha, hgeo⟩ := h
  have hshift : chartLocalCurve (I := I) (fun s => η (s - T)) t =
      fun s => chartLocalCurve (I := I) η (t - T) (s - T) := by funext s; rfl
  refine ⟨v, a, ?_, ?_, ?_, ?_⟩
  · rw [hshift]; exact hv.comp_sub_const t T
  · rw [hshift]
    have hderiv : ∀ s,
        deriv (fun s => chartLocalCurve (I := I) η (t - T) (s - T)) s =
          deriv (chartLocalCurve (I := I) η (t - T)) (s - T) := fun s =>
      deriv_comp_sub_const (chartLocalCurve (I := I) η (t - T)) T s
    have hev' : ∀ᶠ s in nhds t, HasDerivAt
        (chartLocalCurve (I := I) η (t - T))
        (deriv (chartLocalCurve (I := I) η (t - T)) (s - T)) (s - T) :=
      ((continuous_sub_right T).continuousAt).eventually hev
    filter_upwards [hev'] with s hs
    rw [hderiv s]; exact hs.comp_sub_const s T
  · rw [hshift]
    have hd2 : (fun s => deriv
        (fun s => chartLocalCurve (I := I) η (t - T) (s - T)) s) =
        fun s => deriv (chartLocalCurve (I := I) η (t - T)) (s - T) := by
      funext s; exact deriv_comp_sub_const (chartLocalCurve (I := I) η (t - T)) T s
    rw [hd2]; exact ha.comp_sub_const t T
  · exact hgeo

omit [NeZero (Module.finrank ℝ E)] in
theorem isGeodesicOn_glue_at_limit
    (g : SmoothRiemannianMetric I M)
    {γ η : ℝ → M} {T δ : ℝ} (hδ : 0 < δ)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Iio T))
    (hη : IsGeodesicOn (I := I) g η (Set.Ioo (-δ) δ))
    (hmatch : γ =ᶠ[nhdsWithin T (Set.Iio T)] (fun t => η (t - T))) :
    IsGeodesicOn (I := I) g (fun t => if t < T then γ t else η (t - T))
      (Set.Iio (T + δ)) := by
  classical
  set G : ℝ → M := fun t => if t < T then γ t else η (t - T) with hG
  set ηT : ℝ → M := fun s => η (s - T) with hηT
  have hGγ_lt : G =ᶠ[𝓝[<] T] γ :=
    Filter.eventually_of_mem self_mem_nhdsWithin
      (fun t ht => by simp only [hG]; rw [if_pos (mem_Iio.mp ht)])
  have hGηT_ge : G =ᶠ[𝓝[≥] T] ηT :=
    Filter.eventually_of_mem self_mem_nhdsWithin
      (fun t ht => by simp only [hG, hηT]; rw [if_neg (not_lt.mpr (mem_Ici.mp ht))])
  have hGηT_lt : G =ᶠ[𝓝[<] T] ηT := hGγ_lt.trans hmatch
  have hGηT_T : G =ᶠ[𝓝 T] ηT := by
    rw [← nhdsLT_sup_nhdsGE T, Filter.EventuallyEq, eventually_sup]
    exact ⟨hGηT_lt, hGηT_ge⟩
  intro t ht
  rw [mem_Iio] at ht
  rcases lt_trichotomy t T with hlt | heq | hgt
  · have hGγ_t : G =ᶠ[𝓝 t] γ :=
      Filter.eventually_of_mem ((isOpen_Iio).mem_nhds hlt)
        (fun s hs => by simp only [hG]; rw [if_pos (mem_Iio.mp hs)])
    refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := γ) ?_ hGγ_t ?_
    · simp only [hG]; rw [if_pos hlt]
    · exact hγ t (mem_Iio.mpr hlt)
  · subst heq
    have hmem0 : t - t ∈ Set.Ioo (-δ) δ := by
      rw [sub_self]; exact ⟨neg_lt_zero.mpr hδ, hδ⟩
    have hηeq : HasGeodesicEquationAt (I := I) g ηT t :=
      hasGeodesicEquationAt_comp_sub_const (hη (t - t) hmem0)
    refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := ηT) ?_ hGηT_T hηeq
    simp only [hG, hηT]; rw [if_neg (lt_irrefl t)]
  · have hGηT_t : G =ᶠ[𝓝 t] ηT :=
      Filter.eventually_of_mem ((isOpen_Ioi).mem_nhds hgt)
        (fun s hs => by
          simp only [hG, hηT]; rw [if_neg (not_lt.mpr (le_of_lt (mem_Ioi.mp hs)))])
    have hmem : t - T ∈ Set.Ioo (-δ) δ := ⟨by linarith, by linarith⟩
    have hηeq : HasGeodesicEquationAt (I := I) g ηT t :=
      hasGeodesicEquationAt_comp_sub_const (hη (t - T) hmem)
    refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := ηT) ?_ hGηT_t hηeq
    simp only [hG, hηT]; rw [if_neg (not_lt.mpr (le_of_lt hgt))]

omit [NeZero (Module.finrank ℝ E)] in
theorem isGeodesicOn_glue_at_limit_Ioo
    (g : SmoothRiemannianMetric I M)
    {γ η : ℝ → M} {a T δ : ℝ} (hδ : 0 < δ) (haT : a < T)
    (hγ : IsGeodesicOn (I := I) g γ (Set.Ioo a T))
    (hη : IsGeodesicOn (I := I) g η (Set.Ioo (-δ) δ))
    (hmatch : γ =ᶠ[nhdsWithin T (Set.Iio T)] (fun t => η (t - T))) :
    IsGeodesicOn (I := I) g (fun t => if t < T then γ t else η (t - T))
      (Set.Ioo a (T + δ)) := by
  classical
  set G : ℝ → M := fun t => if t < T then γ t else η (t - T) with hG
  set ηT : ℝ → M := fun s => η (s - T) with hηT
  have hGγ_lt : G =ᶠ[𝓝[<] T] γ :=
    Filter.eventually_of_mem self_mem_nhdsWithin
      (fun t ht => by simp only [hG]; rw [if_pos (mem_Iio.mp ht)])
  have hGηT_ge : G =ᶠ[𝓝[≥] T] ηT :=
    Filter.eventually_of_mem self_mem_nhdsWithin
      (fun t ht => by simp only [hG, hηT]; rw [if_neg (not_lt.mpr (mem_Ici.mp ht))])
  have hGηT_lt : G =ᶠ[𝓝[<] T] ηT := hGγ_lt.trans hmatch
  have hGηT_T : G =ᶠ[𝓝 T] ηT := by
    rw [← nhdsLT_sup_nhdsGE T, Filter.EventuallyEq, eventually_sup]
    exact ⟨hGηT_lt, hGηT_ge⟩
  intro t ht
  obtain ⟨ht_lo, ht_hi⟩ := ht
  rcases lt_trichotomy t T with hlt | heq | hgt
  · have hGγ_t : G =ᶠ[𝓝 t] γ :=
      Filter.eventually_of_mem ((isOpen_Iio).mem_nhds hlt)
        (fun s hs => by simp only [hG]; rw [if_pos (mem_Iio.mp hs)])
    refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := γ) ?_ hGγ_t ?_
    · simp only [hG]; rw [if_pos hlt]
    · exact hγ t ⟨ht_lo, hlt⟩
  · subst heq
    have hmem0 : t - t ∈ Set.Ioo (-δ) δ := by
      rw [sub_self]; exact ⟨neg_lt_zero.mpr hδ, hδ⟩
    have hηeq : HasGeodesicEquationAt (I := I) g ηT t :=
      hasGeodesicEquationAt_comp_sub_const (hη (t - t) hmem0)
    refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := ηT) ?_ hGηT_T hηeq
    simp only [hG, hηT]; rw [if_neg (lt_irrefl t)]
  · have hGηT_t : G =ᶠ[𝓝 t] ηT :=
      Filter.eventually_of_mem ((isOpen_Ioi).mem_nhds hgt)
        (fun s hs => by
          simp only [hG, hηT]; rw [if_neg (not_lt.mpr (le_of_lt (mem_Ioi.mp hs)))])
    have hmem : t - T ∈ Set.Ioo (-δ) δ := ⟨by linarith, by linarith⟩
    have hηeq : HasGeodesicEquationAt (I := I) g ηT t :=
      hasGeodesicEquationAt_comp_sub_const (hη (t - T) hmem)
    refine HasGeodesicEquationAt.congr_of_eventuallyEq_at (γ' := ηT) ?_ hGηT_t hηeq
    simp only [hG, hηT]; rw [if_neg (not_lt.mpr (le_of_lt hgt))]

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
