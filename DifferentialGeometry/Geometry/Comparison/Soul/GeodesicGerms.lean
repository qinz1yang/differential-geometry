import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Continuity
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem exists_lift_of_eventually_geodesic_equation
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} (t : ℝ)
    (hγ : ∀ᶠ s in 𝓝 t, HasGeodesicEquationAt (I := I) g γ s)
    (hγ_cont : ∀ᶠ s in 𝓝 t, ContinuousAt γ s) :
    ∃ f : ℝ → TangentBundle I M,
      (f t).proj = γ t ∧
      IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g (γ t)) t ∧
      γ =ᶠ[𝓝 t] (fun s => (f s).proj) := by
  classical
  set y : M := γ t with hy_def
  set v : E := deriv
    (DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) y γ) t
    with hv_def
  obtain ⟨f₁, hf₁_init, hf₁⟩ := exists_chartCenteredLift_at (I := I) g y v t
  have hf₁_proj_t : (f₁ t).proj = y := by rw [hf₁_init]
  refine ⟨f₁, by rw [hf₁_proj_t], by rw [hy_def] at hf₁ ⊢; exact hf₁, ?_⟩
  set w : ℝ → E :=
    DifferentialGeometry.Geometry.Riemannian.AlongCurve.chartCurve (I := I) y γ with hw_def
  set c₁ : ℝ → E × E := fun s => (w s, deriv w s) with hc₁_def
  have hy_src : y ∈ (chartAt H y).source := mem_chart_source H y
  have hγ_src_ev : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H y).source := by
    apply hγ_cont.self_of_nhds.preimage_mem_nhds
    exact (chartAt H y).open_source.mem_nhds (by rw [hy_def]; exact hy_src)
  have hev_first : ∀ᶠ s in 𝓝 t, HasDerivAt w (deriv w s) s :=
    hasGeodesicEquationAt_fixedChart_eventually_hasDerivAt (I := I) g y
      hγ_cont.self_of_nhds (by rw [hy_def]; exact hy_src) hγ.self_of_nhds
  have hev_second : ∀ᶠ s in 𝓝 t,
      HasDerivAt (deriv w)
        (- chartChristoffelContraction (I := I) g y (deriv w s) (deriv w s) (w s)) s := by
    filter_upwards [hγ_src_ev, hγ_cont, hγ] with s hs hsc hsg
    exact hasGeodesicEquationAt_fixedChart_hasDerivAt_velocity (I := I) g y
      hsc hs hsg
  have hc₁_phase : ∀ᶠ s in 𝓝 t,
      HasDerivAt c₁ (chartPhaseVF (I := I) g y (c₁ s)) s ∧
        c₁ s ∈ (interior (extChartAt I y).target) ×ˢ (Set.univ : Set E) := by
    filter_upwards [hev_first, hev_second, hγ_src_ev] with s hf hsd hsrc
    refine ⟨?_, ?_⟩
    · have hpair : HasDerivAt c₁
          ((deriv w s,
            - chartChristoffelContraction (I := I) g y (deriv w s) (deriv w s) (w s))) s :=
        hf.prodMk hsd
      have hrhs : chartPhaseVF (I := I) g y (c₁ s) =
          (deriv w s,
            - chartChristoffelContraction (I := I) g y (deriv w s) (deriv w s) (w s)) := by
        simp only [hc₁_def, chartPhaseVF_apply]
      rw [hrhs]; exact hpair
    · refine ⟨?_, Set.mem_univ _⟩
      have hp_ext_src : γ s ∈ (extChartAt I y).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hsrc
      have hp_target : extChartAt I y (γ s) ∈ (extChartAt I y).target :=
        (extChartAt I y).map_source hp_ext_src
      have : (c₁ s).1 = extChartAt I y (γ s) := by simp [hc₁_def, hw_def]
      rw [this]
      exact
        Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
        (I := I) y hp_target
  set c₂ : ℝ → E × E := chartPushLift (I := I) f₁ t with hc₂_def
  have hπ_cont : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hproj_contAt : ContinuousAt (fun s => (f₁ s).proj) t :=
    hπ_cont.continuousAt.comp hf₁.continuousAt
  have hf_src_ev : ∀ᶠ s in 𝓝 t, (f₁ s).proj ∈ (chartAt H y).source := by
    apply hproj_contAt.preimage_mem_nhds
    rw [hf₁_proj_t]; exact (chartAt H y).open_source.mem_nhds hy_src
  have hc₂_deriv : ∀ᶠ s in 𝓝 t, HasDerivAt (chartPushLift (I := I) f₁ t)
      (chartPushVF (I := I) g y f₁ t s) s := by
    have hf₁' : IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g y) t := hf₁
    exact chartPushLift_eventually_hasDerivAt (I := I) (g := g) (α := y)
      (t₀ := t) (f := f₁) hf₁'
  have hc₂_phase : ∀ᶠ s in 𝓝 t,
      HasDerivAt c₂ (chartPhaseVF (I := I) g y (c₂ s)) s ∧
        c₂ s ∈ (interior (extChartAt I y).target) ×ˢ (Set.univ : Set E) := by
    filter_upwards [hc₂_deriv, hf_src_ev] with s hd hs
    refine ⟨?_, ?_⟩
    · have heq := chartPushVF_eq_chartPhaseVF_at (I := I) g y (f := f₁) (t₀ := t)
        hf₁_proj_t s hs
      rw [heq] at hd; exact hd
    · rw [hc₂_def, chartPushLift_eq_pair (I := I) t s (by rw [hf₁_proj_t]; exact hs)]
      refine ⟨?_, Set.mem_univ _⟩
      rw [hf₁_proj_t]
      have hp_ext_src : (f₁ s).proj ∈ (extChartAt I y).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hs
      have hp_target : extChartAt I y (f₁ s).proj ∈ (extChartAt I y).target :=
        (extChartAt I y).map_source hp_ext_src
      exact
        Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
        (I := I) y hp_target
  have hc₁_t : c₁ t = (extChartAt I y y, v) := by
    have hwt : w t = extChartAt I y y := by simp [hw_def, hy_def]
    have hvt : deriv w t = v := by rw [hv_def, hw_def]
    simp only [hc₁_def, hwt, hvt]
  have hc₂_t : c₂ t = (extChartAt I y y, v) := by
    rw [hc₂_def, chartPushLift_self_pair (I := I) f₁ t, hf₁_proj_t]
    have hfib : chartFiberCoord (I := I) y (f₁ t) = v := by
      rw [show f₁ t = (⟨y, v⟩ : TangentBundle I M) from hf₁_init]
      exact chartFiberCoord_mk_self (I := I) y v
    rw [hfib]
  have hz₀_int : (extChartAt I y y, v) ∈
      (interior (extChartAt I y).target) ×ˢ (Set.univ : Set E) := by
    refine ⟨?_, Set.mem_univ _⟩
    have hp_ext_src : y ∈ (extChartAt I y).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hy_src
    have hp_target : extChartAt I y y ∈ (extChartAt I y).target :=
      (extChartAt I y).map_source hp_ext_src
    exact
      Integral.DivergenceTheorem.extChartAt_target_subset_interior_of_boundaryless
      (I := I) y hp_target
  have hceq : c₁ =ᶠ[𝓝 t] c₂ :=
    chartPhaseVF_orbit_uniqueness_at (I := I) (g := g) (q := y)
      hz₀_int hc₁_t hc₂_t hc₁_phase hc₂_phase
  have hfst : ∀ᶠ s in 𝓝 t, extChartAt I y (γ s) = extChartAt I y (f₁ s).proj := by
    filter_upwards [hceq, hf_src_ev] with s hs hsrc
    have h1 : (c₁ s).1 = extChartAt I y (γ s) := by simp [hc₁_def, hw_def]
    have h2 : (c₂ s).1 = extChartAt I y (f₁ s).proj := by
      rw [hc₂_def, chartPushLift_eq_pair (I := I) t s (by rw [hf₁_proj_t]; exact hsrc)]
      rw [hf₁_proj_t]
    rw [← h1, ← h2, hs]
  filter_upwards [hγ_src_ev, hf_src_ev, hfst] with s hγs hfs heq
  have hγ_es : γ s ∈ (extChartAt I y).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hγs
  have hf_es : (f₁ s).proj ∈ (extChartAt I y).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hfs
  exact (extChartAt I y).injOn hγ_es hf_es heq

theorem isGeodesicAt_of_eventually_hasGeodesicEquationAt
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {t : ℝ}
    (hγ : ∀ᶠ s in 𝓝 t, HasGeodesicEquationAt (I := I) g γ s)
    (hcont : ∀ᶠ s in 𝓝 t, ContinuousAt γ s) :
    IsGeodesicAt (I := I) g γ t := by
  classical
  obtain ⟨f, _, hf, hproj⟩ :=
    exists_lift_of_eventually_geodesic_equation g t hγ hcont
  let F : ℝ → TangentBundle I M := fun s =>
    if (f s).proj = γ s then f s else ⟨γ s, 0⟩
  have hFproj (s : ℝ) : (F s).proj = γ s := by
    dsimp only [F]
    split_ifs with hs
    · exact hs
    · rfl
  have hF : F =ᶠ[𝓝 t] f := by
    filter_upwards [hproj] with s hs
    exact if_pos hs.symm
  refine ⟨γ t, F, hFproj, ?_, ?_⟩
  · rw [hFproj]
    exact mem_chart_source H (γ t)
  · change ∀ᶠ s in 𝓝 t, HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent F s
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (geodesicVectorFieldChart (I := I) g (γ t) (F s)))
    filter_upwards [hf, hF, hF.eventually_nhds] with s hs hFs hFn
    rw [hFs]
    exact hs.congr_of_eventuallyEq hFn

omit [I.Boundaryless] in
private theorem eventually_geodesicAt
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M} {t : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t) :
    ∀ᶠ s in 𝓝 t, IsGeodesicAt (I := I) g γ s := by
  obtain ⟨α, f, hproj, hsrc, hf⟩ := hγ
  have hnear : ∀ᶠ s in 𝓝 t, (f s).proj ∈ (chartAt H α).source :=
    ((FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp hf.continuousAt)
      ((chartAt H α).open_source.mem_nhds hsrc)
  filter_upwards [hnear, hf.eventually_nhds] with s hs hfs
  exact ⟨α, f, hproj, hs, hfs⟩

theorem isGeodesicAt_iff_exists_isGeodesicOn
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    IsGeodesicAt (I := I) g γ t ↔
      ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧ ContinuousOn γ U ∧
        IsGeodesicOn (I := I) g γ U := by
  constructor
  · intro hγ
    obtain ⟨U, hUsub, hU, htU⟩ := mem_nhds_iff.mp (eventually_geodesicAt hγ)
    refine ⟨U, hU, htU, ?_, ?_⟩
    · intro s hs
      exact (hUsub hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hUsub hs).hasGeodesicEquationAt g
  · rintro ⟨U, hU, htU, hcont, hgeo⟩
    apply isGeodesicAt_of_eventually_hasGeodesicEquationAt g
    · filter_upwards [hU.mem_nhds htU] with s hs
      exact hgeo s hs
    · filter_upwards [hU.mem_nhds htU] with s hs
      exact hcont.continuousAt (hU.mem_nhds hs)

theorem exists_smooth_geodesic_neighbourhood_of_isGeodesicAt
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {t : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t) :
    ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ U ∧ IsGeodesicOn (I := I) g γ U := by
  obtain ⟨U, hU, htU, hcont, hgeo⟩ :=
    (isGeodesicAt_iff_exists_isGeodesicOn g γ t).mp hγ
  exact ⟨U, hU, htU, isGeodesicOn_contMDiffOn_infty g hU hgeo hcont, hgeo⟩

theorem isGeodesicAt_congr_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) {γ η : ℝ → M} {t : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t) (heq : η =ᶠ[𝓝 t] γ) :
    IsGeodesicAt (I := I) g η t := by
  have hnear := eventually_geodesicAt hγ
  apply isGeodesicAt_of_eventually_hasGeodesicEquationAt g
  · filter_upwards [hnear, heq.eventually_nhds] with s hs heqs
    exact HasGeodesicEquationAt.congr_of_eventuallyEq_at heqs.self_of_nhds heqs
      (hs.hasGeodesicEquationAt g)
  · filter_upwards [hnear, heq.eventually_nhds] with s hs heqs
    exact hs.continuousAt.congr_of_eventuallyEq heqs

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
theorem exists_contMDiff_curve_eventuallyEq_of_contMDiffOn
    {γ : ℝ → M} {U : Set ℝ} {t : ℝ}
    (hU : IsOpen U) (ht : t ∈ U) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ U) :
    ∃ η : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ η ∧ η =ᶠ[𝓝 t] γ := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ht)
  let χ : ContDiffBump t := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let f : ℝ → ℝ := fun s => t + χ s * (s - t)
  have hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ f :=
    contMDiff_const.add (χ.contDiff.contMDiff.mul (contMDiff_id.sub contMDiff_const))
  have hfU (s : ℝ) : f s ∈ U := by
    by_cases hs : dist s t < r
    · apply hrU
      change dist (t + χ s * (s - t)) t < r
      rw [Real.dist_eq, add_sub_cancel_left, abs_mul, abs_of_nonneg χ.nonneg]
      have hbound : χ s * |s - t| ≤ |s - t| :=
        (mul_le_mul_of_nonneg_right χ.le_one (abs_nonneg _)).trans_eq (one_mul _)
      exact hbound.trans_lt (by simpa only [Real.dist_eq] using hs)
    · have hχ : χ s = 0 := χ.zero_of_le_dist (not_lt.mp hs)
      simpa only [f, hχ, zero_mul, add_zero] using ht
  refine ⟨γ ∘ f, hγ.comp_contMDiff hf hfU, ?_⟩
  filter_upwards [χ.eventuallyEq_one] with s hs
  change γ (t + χ s * (s - t)) = γ s
  rw [show χ s = 1 from hs, one_mul]
  congr 1
  ring

theorem exists_contMDiff_representative_of_isGeodesicAt
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {t : ℝ}
    (hγ : IsGeodesicAt (I := I) g γ t) :
    ∃ η : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ η ∧
      IsGeodesicAt (I := I) g η t ∧ η =ᶠ[𝓝 t] γ := by
  obtain ⟨U, hU, ht, hsmooth, _⟩ :=
    exists_smooth_geodesic_neighbourhood_of_isGeodesicAt g hγ
  obtain ⟨η, hη, heq⟩ := exists_contMDiff_curve_eventuallyEq_of_contMDiffOn hU ht hsmooth
  exact ⟨η, hη, isGeodesicAt_congr_of_eventuallyEq g hγ heq, heq⟩

end DifferentialGeometry.Geometry.Topology

end
