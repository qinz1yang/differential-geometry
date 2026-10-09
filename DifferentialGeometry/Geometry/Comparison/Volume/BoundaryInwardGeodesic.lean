import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryMetricChart
import DifferentialGeometry.Geometry.Metric.Construction.LocalExtension
import DifferentialGeometry.Geometry.Geodesic.Local.Existence
import DifferentialGeometry.Geometry.Geodesic.Equation.ProjectionDerivative
import DifferentialGeometry.Geometry.Geodesic.Flow.CrossVectorFieldReduction
import DifferentialGeometry.Geometry.Boundary.ModelDefiningFunction
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
An actual inward initial velocity enters the original smooth boundary model for positive time.
Local ambient metrics retain the original chart tensor when launching radial geodesics.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E]
  [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [hI : HasSmoothBoundary E H I]

theorem eventually_model_interior_of_inward_derivative (b : hI.boundaryE) (v : E)
    (γ : ℝ → E) (hγ : γ 0 = modelBoundaryParam I b) (hder : HasDerivAt γ v 0)
    (hin : ∃ w : hI.boundaryE, ∃ c : ℝ, 0 < c ∧
      v = fderiv ℝ (modelBoundaryParam I) b w + c • hI.inwardCoordE) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo 0 ε, γ t ∈ interior (range I) := by
  obtain ⟨U, hU, hbU, ρ, hρ, hρzero, hρrange, hρinterior, hρboundary, hdρ⟩ :=
    exists_modelBoundary_definingFunction I b
  obtain ⟨w, c, hc, hvc⟩ := hin
  have hγU : γ 0 ∈ U := hγ.symm ▸ hbU
  have hρdiff : DifferentiableAt ℝ ρ (γ 0) :=
    (hρ.contDiffAt (hU.mem_nhds hγU)).differentiableAt (by simp)
  have hρder : HasDerivAt (ρ ∘ γ) c 0 := by
    convert hρdiff.hasFDerivAt.comp_hasDerivAt 0 hder using 1
    rw [hγ, hvc, hdρ]
  have hslope : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ * ρ (γ t) := by
    have hs := hρder.tendsto_slope_zero_right (isOpen_Ioi.mem_nhds hc)
    change ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < t⁻¹ • ((ρ ∘ γ) (0 + t) - (ρ ∘ γ) 0) at hs
    simpa only [Function.comp_apply, hγ, hρzero, zero_add, sub_zero, smul_eq_mul] using hs
  have hUevent : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ U := by
    have hn : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ U :=
      hder.continuousAt.preimage_mem_nhds (hU.mem_nhds hγU)
    exact hn.filter_mono nhdsWithin_le_nhds
  have henter : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ interior (range I) := by
    filter_upwards [hslope, hUevent, self_mem_nhdsWithin] with t ht htU htpos
    apply (hρinterior (γ t) htU).2
    by_contra hn
    have hnonpos : ρ (γ t) ≤ 0 := le_of_not_gt hn
    exact not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr htpos).le hnonpos) ht
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp henter
  exact ⟨ε, hε, fun t ht => hsub ht⟩

variable {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M]

theorem exists_boundary_inward_ambient_geodesic (g : SmoothRiemannianMetric I M) (p : M)
    (b : hI.boundaryE) (hb : extChartAt I p p = modelBoundaryParam I b) (v : E)
    (hin : ∃ w : hI.boundaryE, ∃ c : ℝ, 0 < c ∧
      v = fderiv ℝ (modelBoundaryParam I) b w + c • hI.inwardCoordE) :
    ∃ G : SmoothRiemannianMetric 𝓘(ℝ, E) E,
      ∃ U : TopologicalSpace.Opens E, extChartAt I p p ∈ U ∧
        (∀ y ∈ (U : Set E) ∩ range I, ∀ z w : E,
          G.inner y z w = metricFlatModelInChart g p y z w) ∧
        ∃ γ : ℝ → E, γ 0 = extChartAt I p p ∧ HasDerivAt γ v 0 ∧
          IsGeodesicAt G γ 0 ∧ ∃ ε : ℝ, 0 < ε ∧
            IsGeodesicOn G γ (Ioo 0 ε) ∧ ∀ t ∈ Ioo 0 ε,
            γ t ∈ (U : Set E) ∩ (I.symm ⁻¹' (chartAt H p).target) ∩ interior (range I) := by
  let ambientAction : ContinuousSMul ℝ E := IsBoundedSMul.continuousSMul
  let ambientComplete : CompleteSpace E := FiniteDimensional.complete ℝ E
  let ambientDimension : NeZero (Module.finrank ℝ E) := by
    have hdim := HasSmoothBoundary.finrank_boundaryE_succ (I := I)
    exact ⟨by omega⟩
  have hp : I.IsBoundaryPoint p := by
    change extChartAt I p p ∈ frontier (range I)
    rw [hb, ← range_modelBoundaryParam I]
    exact mem_range_self b
  obtain ⟨O, hpO, hOtarget, k, hk⟩ := exists_boundaryChart_metric_extension g p hp
  obtain ⟨G, U, hUO, hpU, hG⟩ := exists_model_metric_extension O k ⟨extChartAt I p p, hpO⟩
  have hGoriginal : ∀ y ∈ (U : Set E) ∩ range I, ∀ z w : E,
      G.inner y z w = metricFlatModelInChart g p y z w := by
    intro y hy z w
    rw [hG ⟨y, hy.1⟩ z w]
    exact hk (TopologicalSpace.Opens.inclusion hUO ⟨y, hy.1⟩) hy.2 z w
  obtain ⟨γ, f, hf0, hγproj, hγ0, hf, hgeod⟩ :=
    exists_geodesic_with_initial_velocity_at G (extChartAt I p p) v
  have hγmd : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, E) γ 0 := by
    rw [hγproj]
    exact (contMDiff_proj (IB := 𝓘(ℝ, E)) (n := ∞)
      (TangentSpace 𝓘(ℝ, E))).mdifferentiableAt (by simp) |>.comp 0
        hf.hasMFDerivAt.mdifferentiableAt
  have hvelocity : mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ 0 1 = v := by
    rw [hγproj]
    change mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (fun t => (f t).proj) 0 1 = v
    have hv := hf.mfderiv_proj_one (by rw [hf0]; exact mem_chart_source E _)
    have hfsnd : (f 0).snd = v := by
      rw [hf0]
    exact hv.trans hfsnd
  have hder : HasDerivAt γ v 0 := by
    have hfd : HasFDerivAt γ (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ 0) 0 :=
      hγmd.hasMFDerivAt.hasFDerivAt
    have hd : HasDerivAt γ (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ 0 1) 0 :=
      @HasFDerivAt.hasDerivAt ℝ inferInstance E ambientNorm.toAddCommGroup
        ambientSpace.toModule (inferInstanceAs (TopologicalSpace E)) γ 0 ambientAction
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ 0) hfd
    exact hvelocity ▸ hd
  obtain ⟨ε, hε, henter⟩ := eventually_model_interior_of_inward_derivative b v γ
    (hγ0.trans hb) hder hin
  have htarget : ∀ᶠ t in 𝓝 (0 : ℝ),
      γ t ∈ (U : Set E) ∩ (I.symm ⁻¹' (chartAt H p).target) := by
    apply hder.continuousAt.preimage_mem_nhds
    rw [hγ0]
    exact inter_mem (U.isOpen.mem_nhds hpU)
      (((chartAt H p).open_target.preimage I.continuous_symm).mem_nhds
        (hOtarget (hUO hpU)))
  have hgeoevent : ∀ᶠ t in 𝓝 (0 : ℝ), HasGeodesicEquationAt G γ t := by
    have hfe : ∀ᶠ t in 𝓝 (0 : ℝ),
        IsMIntegralCurveAt f (geodesicVectorFieldChart G (extChartAt I p p)) t :=
      eventually_eventually_nhds.mpr hf
    filter_upwards [hfe] with t ht
    have hgt : IsGeodesicAt G γ t :=
      ⟨extChartAt I p p, f, fun s => by rw [hγproj]; rfl, by simp, ht⟩
    exact hgt.hasGeodesicEquationAt G
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (htarget.and hgeoevent)
  refine ⟨G, U, hpU, hGoriginal, γ, hγ0, hder, hgeod, min ε r, lt_min hε hr, ?_, ?_⟩
  · intro t ht
    apply (hball ?_).2
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
    exact ht.2.trans_le (min_le_right _ _)
  · intro t ht
    refine ⟨(hball ?_).1, henter t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
    exact ht.2.trans_le (min_le_right _ _)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
