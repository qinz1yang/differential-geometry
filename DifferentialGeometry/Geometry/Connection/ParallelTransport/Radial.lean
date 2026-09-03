import DifferentialGeometry.Geometry.Exponential.GaussLemmaPullback
import DifferentialGeometry.Geometry.Exponential.Smoothness.OffZero
import DifferentialGeometry.Analysis.ODE.Flow.GlobalSliceSmoothness
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Endpoint
import DifferentialGeometry.Geometry.Comparison.Variation.CovariantChainRule
import DifferentialGeometry.Geometry.Connection.ParallelTransport.ParallelLocalODE
import DifferentialGeometry.Geometry.Connection.ParallelTransport.MFDerivAlongCurve
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.Connection.LeviCivita.CorrectionContraction
import DifferentialGeometry.Geometry.Connection.ChartFrame.ChartSection
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.CovariantDerivative
import DifferentialGeometry.Geometry.Connection.LeviCivita.LinearExtensionTangent
import Mathlib.Geometry.Manifold.BumpFunction


noncomputable section

open Set Function Filter Metric Bundle Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator

section RadialCurve

omit [NeZero (Module.finrank ℝ E)] in
theorem radialCurve_contMDiffOn_two (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 2
      (fun s : ℝ => (expMap (I := I) g p (s • v) : M))
      {s : ℝ | ‖s • (v : E)‖ < expMapC2Radius (I := I) g p} := by
  rw [ContMDiffOn]
  intro t₀ ht₀
  exact (radialCurve_contMDiffAt2 (I := I) g p (v : E) t₀ ht₀).contMDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem radialCurve_contMDiffOn_two_Icc (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) (hv : ‖(v : E)‖ < expMapC2Radius (I := I) g p) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 2
      (fun s : ℝ => (expMap (I := I) g p (s • v) : M)) (Set.Icc (0 : ℝ) 1) := by
  refine (radialCurve_contMDiffOn_two (I := I) g p v).mono ?_
  intro s hs
  have hs_norm : ‖s • (v : E)‖ ≤ ‖(v : E)‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have habs : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
    exact (mul_le_mul_of_nonneg_right habs (norm_nonneg (v : E))).trans_eq (one_mul _)
  exact lt_of_le_of_lt hs_norm hv

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem radialCurve_zero (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    expMap (I := I) g p ((0 : ℝ) • v) = p := by
  simpa using expMap_zero (I := I) g p

omit [NeZero (Module.finrank ℝ E)] in
theorem radialCurve_velocity (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => (expMap (I := I) g p (s • v) : M)) 0 (1 : ℝ) = v := by
  change mfderiv 𝓘(ℝ, ℝ) I
      (fun u : ℝ => expMap (I := I) g p
        (show TangentSpace I p from u • (v : E))) 0 (1 : ℝ) =
    (show TangentSpace I p from (v : E))
  exact radialCurve_launch_velocity (I := I) g p (v : E)

omit [NeZero (Module.finrank ℝ E)] in
theorem radial_curve_hasGeodesicEquationAt (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) (hv : ‖(v : E)‖ < expMapC2Radius (I := I) g p)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasGeodesicEquationAt (I := I) g (fun s : ℝ => (expMap (I := I) g p (s • v) : M)) t := by
  change HasGeodesicEquationAt (I := I) g
    (fun u : ℝ => expMap (I := I) g p
      (show TangentSpace I p from u • (v : E))) t
  exact radial_geo_at (I := I) g p (v : E) hv t ht

def radialRadius (g : SmoothRiemannianMetric I M) (p : M) : ℝ :=
  expMapC2Radius (I := I) g p / 2

omit [NeZero (Module.finrank ℝ E)] in
lemma radialRadius_pos (g : SmoothRiemannianMetric I M) (p : M) :
    0 < radialRadius (I := I) g p := by
  rw [radialRadius]
  exact div_pos (expMapC2Radius_pos (I := I) g p) (by norm_num)

omit [NeZero (Module.finrank ℝ E)] in
lemma norm_smul_lt_expMapC2Radius_of_lt_radialRadius (g : SmoothRiemannianMetric I M)
    (p : M) {v : TangentSpace I p} (hv : ‖(v : E)‖ < radialRadius (I := I) g p)
    {s : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 2) :
    ‖s • (v : E)‖ < expMapC2Radius (I := I) g p := by
  have hnorm : ‖s • (v : E)‖ ≤ 2 * ‖(v : E)‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have habs : |s| ≤ 2 := by
      rw [abs_le]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact mul_le_mul_of_nonneg_right habs (norm_nonneg (v : E))
  have hlt : 2 * ‖(v : E)‖ < expMapC2Radius (I := I) g p := by
    rw [radialRadius] at hv
    linarith
  exact lt_of_le_of_lt hnorm hlt

omit [NeZero (Module.finrank ℝ E)] in
lemma radialCurve_mem_chartAt_source_of_lt_radialRadius (g : SmoothRiemannianMetric I M)
    (p : M) {v : TangentSpace I p} (hv : ‖(v : E)‖ < radialRadius (I := I) g p)
    {s : ℝ} (hs : s ∈ Set.Icc (-1 : ℝ) 2) :
    expMap (I := I) g p (s • v) ∈ (chartAt H p).source := by
  have hsv : ‖s • (v : E)‖ < expMapC2Radius (I := I) g p :=
    norm_smul_lt_expMapC2Radius_of_lt_radialRadius (I := I) g p hv hs
  have hsrcE : s • (v : E) ∈ (expMapDiffeo (I := I) g p).source :=
    mem_expMapDiffeo_source_of_norm_lt_radius (I := I) g p hsv
  have hmap : expMapDiffeo (I := I) g p (s • (v : E)) ∈ (expMapDiffeo (I := I) g p).target :=
    (expMapDiffeo (I := I) g p).map_source hsrcE
  have hmem : expMap (I := I) g p (s • v) ∈ (expMapDiffeo (I := I) g p).target := by
    rwa [expMapDiffeo_apply_eq (I := I) g p hsrcE] at hmap
  exact exp_target_sub_chart (I := I) g p hmem

omit [NeZero (Module.finrank ℝ E)] in
lemma radialCurve_mem_chartAt_source_of_norm_lt (g : SmoothRiemannianMetric I M) (p : M)
    {v : TangentSpace I p} {s : ℝ}
    (hs : ‖s • (v : E)‖ < expMapC2Radius (I := I) g p) :
    expMap (I := I) g p (s • v) ∈ (chartAt H p).source := by
  have hsrcE : s • (v : E) ∈ (expMapDiffeo (I := I) g p).source :=
    mem_expMapDiffeo_source_of_norm_lt_radius (I := I) g p hs
  have hmap : expMapDiffeo (I := I) g p (s • (v : E)) ∈ (expMapDiffeo (I := I) g p).target :=
    (expMapDiffeo (I := I) g p).map_source hsrcE
  have hmem : expMap (I := I) g p (s • v) ∈ (expMapDiffeo (I := I) g p).target := by
    rwa [expMapDiffeo_apply_eq (I := I) g p hsrcE] at hmap
  exact exp_target_sub_chart (I := I) g p hmem

omit [NeZero (Module.finrank ℝ E)] in
lemma radialCurve_chartCurve_contDiffOn (g : SmoothRiemannianMetric I M) (p : M)
    {v : TangentSpace I p} :
    ContDiffOn ℝ 2 (chartCurve (I := I) p (fun s : ℝ => expMap (I := I) g p (s • v)))
      {s : ℝ | ‖s • (v : E)‖ < expMapC2Radius (I := I) g p} := by
  have h_comp_mdiff : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2
      ((extChartAt I p) ∘ (fun s : ℝ => expMap (I := I) g p (s • v)))
      {s : ℝ | ‖s • (v : E)‖ < expMapC2Radius (I := I) g p} := by
    have hφ : ContMDiffOn I 𝓘(ℝ, E) 2 (extChartAt I p) (chartAt H p).source :=
      (contMDiffOn_extChartAt (I := I) (n := ∞) (x := p)).of_le
        (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    have hmaps : MapsTo (fun s : ℝ => expMap (I := I) g p (s • v))
        {s : ℝ | ‖s • (v : E)‖ < expMapC2Radius (I := I) g p} (chartAt H p).source :=
      fun s hs => radialCurve_mem_chartAt_source_of_norm_lt (I := I) g p hs
    exact hφ.comp (radialCurve_contMDiffOn_two (I := I) g p v) hmaps
  have hfun : (chartCurve (I := I) p (fun s : ℝ => expMap (I := I) g p (s • v))) =
      ((extChartAt I p) ∘ (fun s : ℝ => expMap (I := I) g p (s • v))) := rfl
  rw [hfun]
  exact contMDiffOn_iff_contDiffOn.mp h_comp_mdiff

end RadialCurve

section ParallelTransportOnCurve

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem parallel_chart_overlap_consistency_contMDiffOn [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α β : M) (γ : ℝ → M)
    {s : Set ℝ} (hs_open : IsOpen s)
    (hγ : ContinuousOn γ s)
    (uPrimeα Yα : ℝ → E)
    (hαβ : ∀ t ∈ s, γ t ∈ (chartAt H α).source ∩ (chartAt H β).source)
    (hpar : IsParallelChart (I := I) g α γ uPrimeα Yα s) :
    IsParallelChart (I := I) g β γ
      (fun t => Geodesic.chartTransitionAt (I := I) α β
                  (chartCurve (I := I) α γ t) (uPrimeα t))
      (fun t => Geodesic.chartTransitionAt (I := I) α β
                  (chartCurve (I := I) α γ t) (Yα t))
      s := by
  classical
  set uPrimeβ : ℝ → E := fun t =>
    chartTransitionAt (I := I) α β (chartCurve (I := I) α γ t) (uPrimeα t) with huPrimeβ
  set Yβ : ℝ → E := fun t =>
    chartTransitionAt (I := I) α β (chartCurve (I := I) α γ t) (Yα t) with hYβ
  refine ⟨?_, ?_⟩
  · intro t ht
    set U : Set ℝ := γ ⁻¹' ((chartAt H α).source ∩ (chartAt H β).source) with hU_def
    have hU_open : IsOpen (s ∩ U) :=
      hγ.isOpen_inter_preimage hs_open
        ((chartAt H α).open_source.inter (chartAt H β).open_source)
    have htU : t ∈ s ∩ U := ⟨ht, hαβ t ht⟩
    have hU_nhds : s ∩ U ∈ 𝓝 t := hU_open.mem_nhds htU
    have hcurve_eq : (chartCurve (I := I) β γ) =ᶠ[𝓝 t]
        (fun s => chartTransitionMap (I := I) α β (chartCurve (I := I) α γ s)) := by
      filter_upwards [hU_nhds] with σ hσ
      rw [hU_def] at hσ
      obtain ⟨hσα, _hσβ⟩ := hσ.2
      rw [chartCurve_def, chartCurve_def]
      exact (chartTransitionMap_apply_extChartAt (I := I) α β hσα).symm
    have huα : HasDerivAt (chartCurve (I := I) α γ) (uPrimeα t) t :=
      IsParallelChart.chartCurve_hasDerivAt hpar ht
    have hsrc_t : chartCurve (I := I) α γ t ∈ chartTransitionSource (I := I) α β :=
      extChartAt_mem_chartTransitionSource (I := I) α β (hαβ t ht).1 (hαβ t ht).2
    have hTdiff : DifferentiableAt ℝ (chartTransitionMap (I := I) α β)
        (chartCurve (I := I) α γ t) :=
      chartTransitionMap_differentiableAt (I := I) α β hsrc_t
    have hcomp : HasDerivAt
        (fun s => chartTransitionMap (I := I) α β (chartCurve (I := I) α γ s))
        (chartTransitionAt (I := I) α β (chartCurve (I := I) α γ t) (uPrimeα t)) t := by
      have := hTdiff.hasFDerivAt.comp_hasDerivAt t huα
      convert! this using 1
    exact (hcomp.congr_of_eventuallyEq hcurve_eq)
  · intro t ht
    obtain ⟨htα, htβ⟩ := hαβ t ht
    set x : E := chartCurve (I := I) α γ t with hx_def
    have hsrc_t : x ∈ chartTransitionSource (I := I) α β :=
      extChartAt_mem_chartTransitionSource (I := I) α β htα htβ
    have huα : HasDerivAt (chartCurve (I := I) α γ) (uPrimeα t) t :=
      IsParallelChart.chartCurve_hasDerivAt hpar ht
    have hYαd : HasDerivAt Yα
        (- chartChristoffelContraction (I := I) g α (uPrimeα t) (Yα t) x) t :=
      IsParallelChart.hasDerivAt hpar ht
    have hAdiff : DifferentiableAt ℝ
        (fun z => (chartTransitionAt (I := I) α β z : E →L[ℝ] E)) x := by
      have h_open : IsOpen (chartTransitionSource (I := I) α β) :=
        chartTransitionSource_isOpen (I := I) α β
      exact ((chartTransitionAt_smooth (I := I) α β).contDiffAt
        (h_open.mem_nhds hsrc_t)).differentiableAt (by simp)
    have hcA : HasDerivAt
        (fun s => (chartTransitionAt (I := I) α β (chartCurve (I := I) α γ s) : E →L[ℝ] E))
        ((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (uPrimeα t)) t :=
      hAdiff.hasFDerivAt.comp_hasDerivAt t huα
    have hYβd : HasDerivAt Yβ
        (((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (uPrimeα t)) (Yα t)
          + chartTransitionAt (I := I) α β x
              (- chartChristoffelContraction (I := I) g α (uPrimeα t) (Yα t) x)) t := by
      have := hcA.clm_apply hYαd
      simpa [hYβ, hx_def] using this
    have hfoot :
        ((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (uPrimeα t)) (Yα t) =
          chartTransitionAt (I := I) α β x
            (chartTransitionSecondDerivCorrection (I := I) α β (uPrimeα t) (Yα t) x) :=
      fderiv_chartTransitionAt_apply_eq_pushCorrection (I := I) α β hsrc_t
        (uPrimeα t) (Yα t)
    have hxeq : x = extChartAt I α (γ t) := by rw [hx_def, chartCurve_def]
    have htransform :
        chartChristoffelContraction (I := I) g α (uPrimeα t) (Yα t) x =
          chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β x)
              (chartChristoffelContraction (I := I) g β
                (chartTransitionAt (I := I) α β x (uPrimeα t))
                (chartTransitionAt (I := I) α β x (Yα t))
                (chartTransitionMap (I := I) α β x))
            + chartTransitionSecondDerivCorrection (I := I) α β (uPrimeα t) (Yα t) x := by
      rw [hxeq]
      exact chartChristoffelContraction_transform (I := I) g α β htα htβ
        (uPrimeα t) (Yα t)
    have huβ_eq : chartCurve (I := I) β γ t = chartTransitionMap (I := I) α β x := by
      rw [hx_def, chartCurve_def, chartCurve_def,
        chartTransitionMap_apply_extChartAt (I := I) α β htα]
    have hDcollapse :
        ((fderiv ℝ (fun z => chartTransitionAt (I := I) α β z) x) (uPrimeα t)) (Yα t)
          + chartTransitionAt (I := I) α β x
              (- chartChristoffelContraction (I := I) g α (uPrimeα t) (Yα t) x)
          = - chartChristoffelContraction (I := I) g β
              (uPrimeβ t) (Yβ t) (chartCurve (I := I) β γ t) := by
      rw [hfoot, map_neg, ← sub_eq_add_neg, ← map_sub]
      have hsub :
          chartTransitionSecondDerivCorrection (I := I) α β (uPrimeα t) (Yα t) x -
              chartChristoffelContraction (I := I) g α (uPrimeα t) (Yα t) x =
            - chartTransitionAt (I := I) β α (chartTransitionMap (I := I) α β x)
                (chartChristoffelContraction (I := I) g β
                  (chartTransitionAt (I := I) α β x (uPrimeα t))
                  (chartTransitionAt (I := I) α β x (Yα t))
                  (chartTransitionMap (I := I) α β x)) := by
        rw [htransform]; abel
      rw [hsub, map_neg]
      have hinv := chartTransitionAt_comp_chartTransitionAt' (I := I) α β hsrc_t
      have hid := congrArg (fun L : E →L[ℝ] E => L
          (chartChristoffelContraction (I := I) g β
            (chartTransitionAt (I := I) α β x (uPrimeα t))
            (chartTransitionAt (I := I) α β x (Yα t))
            (chartTransitionMap (I := I) α β x))) hinv
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hid
      rw [hid, huβ_eq]
    have hgoal : HasDerivAt Yβ
        ((fun _ : ℝ => (0 : E)) t -
          chartChristoffelContraction (I := I) g β (uPrimeβ t) (Yβ t)
            (chartCurve (I := I) β γ t)) t := by
      rw [hDcollapse] at hYβd
      simpa using hYβd
    exact hgoal

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem exists_parallel_transport_on_Ioo_contMDiffOn [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (γ : ℝ → M)
    {N : ℕ} (hN : 2 ≤ N) {U : Set ℝ} (hU_open : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I (N : ℕ∞) γ U)
    {a b t₀ : ℝ} (hab : a < b)
    (ht₀ : t₀ ∈ Set.Icc a b)
    (hIcc_sub_U : Set.Icc a b ⊆ U)
    (hsrc : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt H α).source)
    (hα₀ : α = γ t₀)
    (v₀ : TangentSpace I (γ t₀)) :
    ∃ V : ∀ t, TangentSpace I (γ t),
      V t₀ = v₀ ∧
      (∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) ∧
      (∀ t ∈ Set.Ioo a b, covDerivAlong (I := I) g γ V t = 0) ∧
      (∀ t ∈ Set.Icc a b,
        HasDerivWithinAt (chartRepAt (I := I) γ V t₀)
          (- chartChristoffelContraction (I := I) g α
              (deriv (chartCurve (I := I) α γ) t) (chartRepAt (I := I) γ V t₀ t)
              (chartCurve (I := I) α γ t)) (Set.Icc a b) t) := by
  classical
  set uPrime : ℝ → E := fun t => deriv (AlongCurve.chartCurve (I := I) α γ) t with huPrime_def
  have hγ_contOn : ContinuousOn γ (Set.Icc a b) :=
    hγ.continuousOn.mono hIcc_sub_U
  have hcurveCont : ContinuousOn (AlongCurve.chartCurve (I := I) α γ) (Set.Icc a b) := by
    have hφ : ContinuousOn (extChartAt I α) (extChartAt I α).source :=
      continuousOn_extChartAt (I := I) α
    have hmaps : Set.MapsTo γ (Set.Icc a b) (extChartAt I α).source := by
      intro t ht
      rw [extChartAt_source (I := I) α]
      exact hsrc t ht
    exact hφ.comp hγ_contOn hmaps
  set W : Set ℝ := U ∩ γ ⁻¹' (chartAt H α).source with hW_def
  have hW_open : IsOpen W :=
    hγ.continuousOn.isOpen_inter_preimage hU_open (chartAt H α).open_source
  have hIcc_sub_W : Set.Icc a b ⊆ W := fun t ht => ⟨hIcc_sub_U ht, hsrc t ht⟩
  have hUcd : ContDiffOn ℝ (N : ℕ∞) (AlongCurve.chartCurve (I := I) α γ) W := by
    have h_comp_mdiff : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (N : ℕ∞) ((extChartAt I α) ∘ γ) W := by
      have hφ : ContMDiffOn I 𝓘(ℝ, E) (N : ℕ∞) (extChartAt I α) (chartAt H α).source :=
        (contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)).of_le (by exact_mod_cast le_top)
      have hγW : ContMDiffOn 𝓘(ℝ, ℝ) I (N : ℕ∞) γ W := hγ.mono (fun s hs => hs.1)
      have hmaps : MapsTo γ W (chartAt H α).source := fun s hs => hs.2
      exact hφ.comp hγW hmaps
    have hfun : (AlongCurve.chartCurve (I := I) α γ) = ((extChartAt I α) ∘ γ) := rfl
    rw [hfun]; exact contMDiffOn_iff_contDiffOn.mp h_comp_mdiff
  have huPrimeCont : ContinuousOn uPrime (Set.Icc a b) := by
    have hderiv_cd : ContDiffOn ℝ (0 : ℕ∞) (deriv (AlongCurve.chartCurve (I := I) α γ)) W :=
      hUcd.deriv_of_isOpen hW_open (by
        have : (1 : ℕ) ≤ N := le_trans one_le_two hN
        exact_mod_cast this)
    exact (hderiv_cd.continuousOn).mono hIcc_sub_W
  have hγa_src : γ t₀ ∈ (chartAt H α).source := hsrc t₀ ht₀
  set y₀ : E := (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (γ t₀) v₀ with
    hy₀_def
  obtain ⟨Y, hY_deriv, hY_init⟩ :=
    parallel_local_existence_on_Icc (I := I) g α γ uPrime hab.le ht₀
      huPrimeCont hcurveCont hsrc y₀
  set V : ∀ t, TangentSpace I (γ t) := fun s =>
    (trivializationAt E (TangentSpace I) α).symmL ℝ (γ s) (Y s) with hV_def
  have hIccNhds : ∀ t ∈ Set.Ioo a b, Set.Icc a b ∈ 𝓝 t := fun t ht =>
    Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self
  have hcurveDeriv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (AlongCurve.chartCurve (I := I) α γ) (uPrime t) t := by
    intro t ht
    have ht_W : t ∈ W := hIcc_sub_W (Set.mem_Icc_of_Ioo ht)
    have : DifferentiableAt ℝ (AlongCurve.chartCurve (I := I) α γ) t :=
      (hUcd.differentiableOn (by exact_mod_cast (show N ≠ 0 by omega)) t ht_W).differentiableAt
        (hW_open.mem_nhds ht_W)
    exact this.hasDerivAt
  have hY_par_Ioo : IsParallelChart (I := I) g α γ uPrime Y (Set.Ioo a b) := by
    refine ⟨fun t ht => hcurveDeriv t ht, ?_⟩
    intro t ht
    have hd := (hY_deriv t (Set.mem_Icc_of_Ioo ht)).hasDerivAt (hIccNhds t ht)
    simpa using hd
  have hrep_eq : ∀ t ∈ Set.Ioo a b,
      chartRepAt (I := I) γ V t =ᶠ[𝓝 t]
        (fun s => Geodesic.chartTransitionAt (I := I) α (γ t)
          (AlongCurve.chartCurve (I := I) α γ s) (Y s)) := by
    intro t ht
    set W' : Set ℝ := U ∩ γ ⁻¹' ((chartAt H α).source ∩ (chartAt H (γ t)).source) with hW'_def
    have hW'_open : IsOpen W' :=
      hγ.continuousOn.isOpen_inter_preimage hU_open
        ((chartAt H α).open_source.inter (chartAt H (γ t)).open_source)
    have htW' : t ∈ W' := ⟨hIcc_sub_U (Set.mem_Icc_of_Ioo ht),
      ⟨hsrc t (Set.mem_Icc_of_Ioo ht), mem_chart_source H (γ t)⟩⟩
    filter_upwards [hW'_open.mem_nhds htW'] with s hs
    obtain ⟨hsα, hsβ⟩ := hs.2
    rw [chartRepAt_apply, hV_def]
    simp only
    rw [trivialization_coordinateChange_eq_chartTransitionAt (I := I) α (γ t) hsα hsβ (Y s)]
    rw [AlongCurve.chartCurve_def]
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · rw [hV_def]
    simp only
    rw [hY_init, hy₀_def]
    have hbase : γ t₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]; exact hγa_src
    exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hbase v₀
  · intro t ht
    refine (DifferentiableAt.congr_of_eventuallyEq ?_ (hrep_eq t ht))
    set Tαβ : E → (E →L[ℝ] E) := fun x => Geodesic.chartTransitionAt (I := I) α (γ t) x
      with hTαβ_def
    have hsrc_t : AlongCurve.chartCurve (I := I) α γ t ∈
        Geodesic.chartTransitionSource (I := I) α (γ t) :=
      Geodesic.extChartAt_mem_chartTransitionSource (I := I) α (γ t)
        (hsrc t (Set.mem_Icc_of_Ioo ht)) (mem_chart_source H (γ t))
    have hTopen : IsOpen (Geodesic.chartTransitionSource (I := I) α (γ t)) :=
      Geodesic.chartTransitionSource_isOpen (I := I) α (γ t)
    have hTdiff : DifferentiableAt ℝ Tαβ (AlongCurve.chartCurve (I := I) α γ t) :=
      ((Geodesic.chartTransitionAt_smooth (I := I) α (γ t)).contDiffAt
        (hTopen.mem_nhds hsrc_t)).differentiableAt (by simp)
    have hcurve_diff : DifferentiableAt ℝ (AlongCurve.chartCurve (I := I) α γ) t :=
      (hcurveDeriv t ht).differentiableAt
    have hY_diff : DifferentiableAt ℝ Y t :=
      ((hY_deriv t (Set.mem_Icc_of_Ioo ht)).hasDerivAt (hIccNhds t ht)).differentiableAt
    have hTcomp_diff : DifferentiableAt ℝ
        (fun s => (Tαβ (AlongCurve.chartCurve (I := I) α γ s) : E →L[ℝ] E)) t :=
      hTdiff.comp t hcurve_diff
    exact hTcomp_diff.clm_apply hY_diff
  · intro t ht
    rw [covDerivAlong_eq_zero_iff (I := I) g γ V t]
    set o : Set ℝ := Set.Ioo a b ∩ γ ⁻¹' (chartAt H (γ t)).source with ho_def
    have ho_open : IsOpen o := by
      have hUpre : IsOpen (U ∩ γ ⁻¹' (chartAt H (γ t)).source) :=
        hγ.continuousOn.isOpen_inter_preimage hU_open (chartAt H (γ t)).open_source
      have heq : o = (U ∩ γ ⁻¹' (chartAt H (γ t)).source) ∩ Set.Ioo a b := by
        ext s
        simp only [ho_def, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioo]
        constructor <;> intro hs
        · exact ⟨⟨hIcc_sub_U ⟨le_of_lt hs.1.1, le_of_lt hs.1.2⟩, hs.2⟩, hs.1.1, hs.1.2⟩
        · exact ⟨⟨hs.2.1, hs.2.2⟩, hs.1.2⟩
      rw [heq]
      exact hUpre.inter isOpen_Ioo
    have hto : t ∈ o := ⟨ht, mem_chart_source H (γ t)⟩
    have ho_sub : o ⊆ Set.Ioo a b := fun s hs => hs.1
    have hoverlap : ∀ s ∈ o, γ s ∈ (chartAt H α).source ∩ (chartAt H (γ t)).source :=
      fun s hs => ⟨hsrc s (Set.mem_Icc_of_Ioo (ho_sub hs)), hs.2⟩
    have hY_par_o : IsParallelChart (I := I) g α γ uPrime Y o :=
      ⟨fun s hs => hY_par_Ioo.1 s (ho_sub hs), fun s hs => hY_par_Ioo.2 s (ho_sub hs)⟩
    have hpush_par := parallel_chart_overlap_consistency_contMDiffOn
      (I := I) g α (γ t) γ ho_open
      (hγ.continuousOn.mono (fun s hs => hIcc_sub_U (Set.mem_Icc_of_Ioo (ho_sub hs))))
      uPrime Y hoverlap hY_par_o
    set Yβ : ℝ → E := fun s => Geodesic.chartTransitionAt (I := I) α (γ t)
      (AlongCurve.chartCurve (I := I) α γ s) (Y s) with hYβ_def
    have hvel_eq : ∀ s ∈ o,
        deriv (AlongCurve.chartCurve (I := I) (γ t) γ) s =
          Geodesic.chartTransitionAt (I := I) α (γ t)
            (AlongCurve.chartCurve (I := I) α γ s) (uPrime s) := by
      intro s hs
      exact (hpush_par.1 s hs).deriv
    have hpush_par' : IsParallelChart (I := I) g (γ t) γ
        (fun s => deriv (AlongCurve.chartCurve (I := I) (γ t) γ) s) Yβ o := by
      refine ⟨fun s hs => ?_, fun s hs => ?_⟩
      · have h1 := hpush_par.1 s hs
        simp only []
        rw [hvel_eq s hs]; exact h1
      · have h2 := hpush_par.2 s hs
        simp only [hvel_eq s hs]
        exact h2
    have hYβ_zero : chartCovDerivAlong (I := I) g (γ t) γ Yβ t = 0 := by
      have hd := hpush_par'.hasDerivAt hto
      rw [chartCovDerivAlong_def, hd.deriv]
      abel
    have hrep_eqβ : chartRepAt (I := I) γ V t =ᶠ[𝓝 t] Yβ := hrep_eq t ht
    have hgoal : chartCovDerivAlong (I := I) g (γ t) γ (chartRepAt (I := I) γ V t) t =
        chartCovDerivAlong (I := I) g (γ t) γ Yβ t := by
      rw [chartCovDerivAlong_def, chartCovDerivAlong_def]
      rw [hrep_eqβ.deriv_eq, hrep_eqβ.eq_of_nhds]
    rw [hgoal, hYβ_zero]
  · intro t ht
    have hEqOn : Set.EqOn (chartRepAt (I := I) γ V t₀) Y (Set.Icc a b) := by
      intro s hs
      rw [chartRepAt_apply, ← hα₀, hV_def]
      have hmem : γ s ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [TangentBundle.trivializationAt_baseSet]; exact hsrc s hs
      exact (trivializationAt E (TangentSpace I) α).continuousLinearMapAt_symmL
        (R := ℝ) hmem (Y s)
    have hYd := hY_deriv t ht
    have hYd' : HasDerivWithinAt Y
        (- chartChristoffelContraction (I := I) g α (uPrime t)
            (chartRepAt (I := I) γ V t₀ t) (chartCurve (I := I) α γ t))
        (Set.Icc a b) t := by
      rw [← hEqOn ht] at hYd
      exact hYd
    exact hYd'.congr hEqOn (hEqOn ht)

end ParallelTransportOnCurve

section RadialParallelTransport

omit [NeZero (Module.finrank ℝ E)] in
omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem parallelTransport_radial {g : SmoothRiemannianMetric I M} {p : M}
    {v : TangentSpace I p}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) (fun s : ℝ => expMap (I := I) g p (s • v)))
    {L : ℝ} (hL : 0 < L) (η₀ : TangentSpace I p) :
    ∃ η : ∀ s, TangentSpace I (expMap (I := I) g p (s • v)),
      η 0 = η₀ ∧
      (∀ s ∈ Set.Icc (0 : ℝ) L, DifferentiableAt ℝ
        (chartRepAt (I := I) (fun s => expMap (I := I) g p (s • v)) η s) s) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) L,
        covDerivAlong (I := I) g (fun s => expMap (I := I) g p (s • v)) η s = 0) := by
  obtain ⟨V, hV0, hVdiff, hVpar⟩ :=
    exists_parallel_transport_on_Icc (I := I) g (fun s => expMap (I := I) g p (s • v))
      (N := 2) le_rfl hγ hL η₀
  exact ⟨V, hV0, hVdiff, hVpar⟩

omit [NeZero (Module.finrank ℝ E)] in
private lemma rescaleNormLt (g : SmoothRiemannianMetric I M) (p : M) {v : TangentSpace I p}
    (hv : ‖(v : E)‖ < radialRadius (I := I) g p) {c : ℝ} (hc : c ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖(c • v : E)‖ < radialRadius (I := I) g p := by
  have hnorm : ‖(c • v : E)‖ ≤ ‖(v : E)‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have habs : |c| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [hc.1], by linarith [hc.2]⟩
    exact (mul_le_mul_of_nonneg_right habs (norm_nonneg (v : E))).trans_eq (one_mul _)
  exact lt_of_le_of_lt hnorm hv

omit [NeZero (Module.finrank ℝ E)] in
lemma radialCurve_domain_isOpen (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    IsOpen {s : ℝ | ‖s • (v : E)‖ < expMapC2Radius (I := I) g p} :=
  (isOpen_Iio.preimage (continuous_norm.comp (continuous_id.smul continuous_const)))

omit [NeZero (Module.finrank ℝ E)] in
private theorem radialParallelTransportData (g : SmoothRiemannianMetric I M) (p : M)
    {v : TangentSpace I p} (hv : ‖(v : E)‖ < radialRadius (I := I) g p)
    (η₀ : TangentSpace I p) :
    ∃ V : ∀ t, TangentSpace I (expMap (I := I) g p (t • v)),
      V 0 = η₀ ∧
      (∀ t ∈ Set.Ioo (-1 : ℝ) 2, DifferentiableAt ℝ
        (chartRepAt (I := I) (fun s : ℝ => expMap (I := I) g p (s • v)) V t) t) ∧
      (∀ t ∈ Set.Ioo (-1 : ℝ) 2,
        covDerivAlong (I := I) g (fun s : ℝ => expMap (I := I) g p (s • v)) V t = 0) ∧
      (∀ t ∈ Set.Icc (-1 : ℝ) 2,
        HasDerivWithinAt (chartRepAt (I := I) (fun s : ℝ => expMap (I := I) g p (s • v)) V 0)
          (- chartChristoffelContraction (I := I) g p
              (deriv (chartCurve (I := I) p (fun s : ℝ => expMap (I := I) g p (s • v))) t)
              (chartRepAt (I := I) (fun s : ℝ => expMap (I := I) g p (s • v)) V 0 t)
              (chartCurve (I := I) p (fun s : ℝ => expMap (I := I) g p (s • v)) t))
          (Set.Icc (-1 : ℝ) 2) t) :=
  exists_parallel_transport_on_Ioo_contMDiffOn (I := I) g p
    (fun s : ℝ => expMap (I := I) g p (s • v)) (N := 2) le_rfl
    (radialCurve_domain_isOpen (I := I) g p v)
    (radialCurve_contMDiffOn_two (I := I) g p v)
    (by norm_num : (-1 : ℝ) < 2) (t₀ := 0) ⟨by norm_num, by norm_num⟩
    (fun t ht => norm_smul_lt_expMapC2Radius_of_lt_radialRadius (I := I) g p hv ht)
    (fun t ht => radialCurve_mem_chartAt_source_of_lt_radialRadius (I := I) g p hv ht)
    (by simpa using (radialCurve_zero (I := I) g p v).symm) η₀

noncomputable def radialParallelTransportSection (g : SmoothRiemannianMetric I M)
    (p : M) {v : TangentSpace I p} (hv : ‖(v : E)‖ < radialRadius (I := I) g p)
    (η₀ : TangentSpace I p) : ∀ t : ℝ, TangentSpace I (expMap (I := I) g p (t • v)) :=
  Classical.choose (radialParallelTransportData (I := I) g p hv η₀)

omit [NeZero (Module.finrank ℝ E)] in
theorem radialParallelTransportSection_initial (g : SmoothRiemannianMetric I M) (p : M)
    {v : TangentSpace I p} (hv : ‖(v : E)‖ < radialRadius (I := I) g p)
    (η₀ : TangentSpace I p) :
    radialParallelTransportSection (I := I) g p hv η₀ 0 = η₀ :=
  (Classical.choose_spec (radialParallelTransportData (I := I) g p hv η₀)).1

omit [NeZero (Module.finrank ℝ E)] in
theorem radialParallelTransportSection_differentiableAt (g : SmoothRiemannianMetric I M)
    (p : M) {v : TangentSpace I p} (hv : ‖(v : E)‖ < radialRadius (I := I) g p)
    (η₀ : TangentSpace I p) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 2) :
    DifferentiableAt ℝ
      (chartRepAt (I := I) (fun s : ℝ => expMap (I := I) g p (s • v))
        (radialParallelTransportSection (I := I) g p hv η₀) t) t :=
  (Classical.choose_spec (radialParallelTransportData (I := I) g p hv η₀)).2.1 t ht

omit [NeZero (Module.finrank ℝ E)] in
theorem radialParallelTransportSection_covDerivAlong (g : SmoothRiemannianMetric I M)
    (p : M) {v : TangentSpace I p} (hv : ‖(v : E)‖ < radialRadius (I := I) g p)
    (η₀ : TangentSpace I p) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 2) :
    covDerivAlong (I := I) g (fun s : ℝ => expMap (I := I) g p (s • v))
      (radialParallelTransportSection (I := I) g p hv η₀) t = 0 :=
  (Classical.choose_spec (radialParallelTransportData (I := I) g p hv η₀)).2.2.1 t ht

omit [NeZero (Module.finrank ℝ E)] in
theorem radialParallelTransportSection_ode (g : SmoothRiemannianMetric I M) (p : M)
    {v : TangentSpace I p} (hv : ‖(v : E)‖ < radialRadius (I := I) g p)
    (η₀ : TangentSpace I p) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 2) :
    HasDerivWithinAt
      (chartRepAt (I := I) (fun s : ℝ => expMap (I := I) g p (s • v))
        (radialParallelTransportSection (I := I) g p hv η₀) 0)
      (- chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p (fun s : ℝ => expMap (I := I) g p (s • v))) t)
          (chartRepAt (I := I) (fun s : ℝ => expMap (I := I) g p (s • v))
            (radialParallelTransportSection (I := I) g p hv η₀) 0 t)
          (chartCurve (I := I) p (fun s : ℝ => expMap (I := I) g p (s • v)) t))
      (Set.Icc (-1 : ℝ) 2) t :=
  (Classical.choose_spec (radialParallelTransportData (I := I) g p hv η₀)).2.2.2 t ht

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] in
private lemma radial_curve_eq_rescale (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) (c t : ℝ) :
    expMap (I := I) g p (t • (c • v)) = expMap (I := I) g p ((c • t) • v) := by
  congr 1
  rw [smul_smul, smul_eq_mul]
  congr 1
  ring

private lemma smul_mem_Ioo_neg_one_two {c t : ℝ} (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    c • t ∈ Set.Ioo (-1 : ℝ) 2 := by
  constructor
  · by_cases hc0 : 0 ≤ c
    · have hnn : 0 ≤ c • t := mul_nonneg hc0 ht.1
      linarith
    · have hcneg : c ≤ 0 := le_of_not_ge hc0
      calc (-1 : ℝ) < c := hc.1
        _ = c • 1 := by simp
        _ ≤ c • t := by exact mul_le_mul_of_nonpos_left ht.2 hcneg
  · by_cases hc0 : 0 ≤ c
    · have hle : c • t ≤ c • 1 := smul_le_smul_of_nonneg_left ht.2 hc0
      calc c • t ≤ c • 1 := hle
        _ = c := by simp
        _ < 1 := hc.2
        _ < 2 := by norm_num
    · have hneg : c • t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc0) ht.1
      linarith

omit [NeZero (Module.finrank ℝ E)] in
theorem radialParallelTransportSection_rescale (g : SmoothRiemannianMetric I M) (p : M)
    {v : TangentSpace I p} (hv : ‖(v : E)‖ < radialRadius (I := I) g p)
    (η₀ : TangentSpace I p) {c : ℝ} (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    radialParallelTransportSection (I := I) g p (rescaleNormLt (I := I) g p hv hc) η₀ t =
      radialParallelTransportSection (I := I) g p hv η₀ (c • t) := by
  classical
  let γv : ℝ → M := fun s => expMap (I := I) g p (s • v)
  let γcv : ℝ → M := fun s => expMap (I := I) g p (s • (c • v))
  let Pv : ∀ s, TangentSpace I (γv s) := radialParallelTransportSection (I := I) g p hv η₀
  let Pcv : ∀ s, TangentSpace I (γcv s) :=
    radialParallelTransportSection (I := I) g p (rescaleNormLt (I := I) g p hv hc) η₀
  have hγ_eq : ∀ s : ℝ, γcv s = γv (c • s) := by
    intro s
    exact radial_curve_eq_rescale (I := I) g p v c s
  let Yv : ℝ → E := chartRepAt (I := I) γv Pv 0
  let Ycv : ℝ → E := chartRepAt (I := I) γcv Pcv 0
  have hIcc01_sub : Set.Icc (0 : ℝ) 1 ⊆ Set.Icc (-1 : ℝ) 2 := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hYcv_ode : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt Ycv
      (- chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p γcv) τ) (Ycv τ)
          (chartCurve (I := I) p γcv τ)) (Set.Icc (0 : ℝ) 1) τ := by
    intro τ hτ
    have hd := radialParallelTransportSection_ode (I := I) g p
      (rescaleNormLt (I := I) g p hv hc) η₀ (hIcc01_sub hτ)
    exact hd.mono (by intro s hs; exact hIcc01_sub hs)
  have hchart_eq : ∀ s : ℝ, chartCurve (I := I) p γcv s = chartCurve (I := I) p γv (c • s) := by
    intro s
    rw [chartCurve_def, chartCurve_def]
    exact congrArg (extChartAt I p) (hγ_eq s)
  have hfcv_eq : chartCurve (I := I) p γcv = fun s => chartCurve (I := I) p γv (c • s) := by
    funext s
    exact hchart_eq s
  let hUcv : Set ℝ :=
    {s : ℝ | ‖s • ((c • v) : E)‖ < expMapC2Radius (I := I) g p}
  have hUcv_open : IsOpen hUcv := by
    exact radialCurve_domain_isOpen (I := I) g p (c • v)
  have h01_sub_Ucv : Set.Icc (0 : ℝ) 1 ⊆ hUcv := by
    intro s hs
    exact norm_smul_lt_expMapC2Radius_of_lt_radialRadius (I := I) g p
      (rescaleNormLt (I := I) g p hv hc) (hIcc01_sub hs)
  have hcd : ContDiffOn ℝ 1 (chartCurve (I := I) p γcv) hUcv := by
    have h2 := radialCurve_chartCurve_contDiffOn (I := I) g p (v := c • v)
    exact h2.of_le (WithTop.coe_le_coe.2 (by norm_num : (1 : ℕ∞) ≤ (2 : ℕ∞)))
  have hu : ContinuousOn (fun τ : ℝ => deriv (chartCurve (I := I) p γcv) τ) (Set.Icc 0 1) := by
    have hd : ContDiffOn ℝ 0 (deriv (chartCurve (I := I) p γcv)) hUcv :=
      hcd.deriv_of_isOpen hUcv_open (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞))
    exact (hd.continuousOn).mono h01_sub_Ucv
  have hγcv_cont : ContinuousOn γcv hUcv :=
    (radialCurve_contMDiffOn_two (I := I) g p (c • v)).continuousOn
  have hγc : ContinuousOn (chartCurve (I := I) p γcv) (Set.Icc 0 1) := by
    have hφ : ContinuousOn (extChartAt I p) (extChartAt I p).source :=
      continuousOn_extChartAt (I := I) p
    have hmaps : Set.MapsTo γcv (Set.Icc 0 1) (extChartAt I p).source := by
      intro s hs
      rw [extChartAt_source]
      exact radialCurve_mem_chartAt_source_of_lt_radialRadius (I := I) g p
        (rescaleNormLt (I := I) g p hv hc) (hIcc01_sub hs)
    exact hφ.comp (hγcv_cont.mono h01_sub_Ucv) hmaps
  have hsrc01 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, γcv τ ∈ (chartAt H p).source := by
    intro τ hτ
    exact radialCurve_mem_chartAt_source_of_lt_radialRadius (I := I) g p
      (rescaleNormLt (I := I) g p hv hc) (hIcc01_sub hτ)
  have hY2_ode : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt (fun s => Yv (c • s))
      (- chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p γcv) τ) (Yv (c • τ))
          (chartCurve (I := I) p γcv τ)) (Set.Icc (0 : ℝ) 1) τ := by
    intro τ hτ
    have hcτ_gt : (-1 : ℝ) < c • τ := (smul_mem_Ioo_neg_one_two hc hτ).1
    have hcτ_lt : c • τ < 2 := (smul_mem_Ioo_neg_one_two hc hτ).2
    have hcτ_mem : c • τ ∈ Set.Icc (-1 : ℝ) 2 := ⟨hcτ_gt.le, hcτ_lt.le⟩
    let d : E := - chartChristoffelContraction (I := I) g p
        (deriv (chartCurve (I := I) p γv) (c • τ)) (Yv (c • τ))
        (chartCurve (I := I) p γv (c • τ))
    have hd_eq : d = - chartChristoffelContraction (I := I) g p
        (deriv (chartCurve (I := I) p γv) (c • τ)) (Yv (c • τ))
        (chartCurve (I := I) p γv (c • τ)) := rfl
    have hYv_at : HasDerivAt Yv d (c • τ) := by
      have hd2 := radialParallelTransportSection_ode (I := I) g p hv η₀ hcτ_mem
      have hd3 : HasDerivWithinAt Yv d (Set.Icc (-1 : ℝ) 2) (c • τ) := by
        exact hd2
      exact hd3.hasDerivAt (Icc_mem_nhds hcτ_gt hcτ_lt)
    have hinner : HasDerivAt (fun s : ℝ => c • s) c τ := by
      have h := (hasDerivAt_id τ).const_mul c
      simpa [smul_eq_mul] using h
    have hcomp : HasDerivAt (fun s => Yv (c • s)) (c • d) τ := by
      convert! hYv_at.scomp τ hinner using 1
    have hderiv_γ : deriv (chartCurve (I := I) p γcv) τ =
        c • deriv (chartCurve (I := I) p γv) (c • τ) := by
      rw [hfcv_eq]
      simpa using deriv_comp_mul_left c (chartCurve (I := I) p γv) τ
    have hlin : chartChristoffelContraction (I := I) g p
          (c • deriv (chartCurve (I := I) p γv) (c • τ)) (Yv (c • τ))
          (chartCurve (I := I) p γv (c • τ)) =
        c • chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p γv) (c • τ)) (Yv (c • τ))
          (chartCurve (I := I) p γv (c • τ)) :=
      ChartChristoffel.contraction_smul_left c
        (deriv (chartCurve (I := I) p γv) (c • τ)) (Yv (c • τ))
    have hval : - chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p γcv) τ) (Yv (c • τ))
          (chartCurve (I := I) p γcv τ) = c • d := by
      rw [hderiv_γ, hchart_eq τ, hlin]
      rw [hd_eq]
      simp [smul_neg]
    have h2 : HasDerivAt (fun s => Yv (c • s))
        (- chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p γcv) τ) (Yv (c • τ))
          (chartCurve (I := I) p γcv τ)) τ := by
      rw [hval]
      exact hcomp
    exact (h2.hasDerivWithinAt).mono (fun s hs => Set.mem_univ s)
  have hYcv0 : Ycv 0 = (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p η₀ := by
    change (trivializationAt E (TangentSpace I) (γcv 0)).continuousLinearMapAt ℝ (γcv 0)
        (radialParallelTransportSection (I := I) g p (rescaleNormLt (I := I) g p hv hc) η₀ 0) =
      (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p η₀
    rw [radialParallelTransportSection_initial (I := I) g p (rescaleNormLt (I := I) g p hv hc) η₀]
    change (trivializationAt E (TangentSpace I) (expMap (I := I) g p ((0 : ℝ) • (c • v)))).continuousLinearMapAt ℝ
        (expMap (I := I) g p ((0 : ℝ) • (c • v))) η₀ =
      (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p η₀
    rw [radialCurve_zero (I := I) g p (c • v)]
  have hY2_0 : (fun s => Yv (c • s)) 0 = (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p η₀ := by
    change (trivializationAt E (TangentSpace I) (γv 0)).continuousLinearMapAt ℝ (γv (c • 0))
        (radialParallelTransportSection (I := I) g p hv η₀ (c • 0)) =
      (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p η₀
    rw [smul_zero]
    rw [radialParallelTransportSection_initial (I := I) g p hv η₀]
    change (trivializationAt E (TangentSpace I) (expMap (I := I) g p ((0 : ℝ) • v))).continuousLinearMapAt ℝ
        (expMap (I := I) g p ((0 : ℝ) • v)) η₀ =
      (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p η₀
    rw [radialCurve_zero (I := I) g p v]
  have hEq01 : Set.EqOn Ycv (fun s => Yv (c • s)) (Set.Icc (0 : ℝ) 1) :=
    parallel_local_uniqueness_on_Icc (I := I) g p γcv
      (fun τ => deriv (chartCurve (I := I) p γcv) τ) (by norm_num) ⟨le_rfl, by norm_num⟩
      hu hγc hsrc01 hYcv_ode hY2_ode (hYcv0.trans hY2_0.symm)
  have hEq_t : Ycv t = Yv (c • t) := hEq01 ht
  have hchart : chartRepAt (I := I) γcv Pcv 0 t = chartRepAt (I := I) γv Pv 0 (c • t) := by
    change chartRepAt (I := I) γcv Pcv 0 t =
      chartRepAt (I := I) γv Pv 0 (c • t) at hEq_t
    exact hEq_t
  have hmem : γv (c • t) ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    have hct_mem : c • t ∈ Set.Ioo (-1 : ℝ) 2 := smul_mem_Ioo_neg_one_two hc ht
    exact radialCurve_mem_chartAt_source_of_lt_radialRadius (I := I) g p hv
      ⟨hct_mem.1.le, hct_mem.2.le⟩
  have hsec : Pcv t = Pv (c • t) := by
    change (trivializationAt E (TangentSpace I) (γcv 0)).continuousLinearMapAt ℝ (γcv t) (Pcv t) =
      (trivializationAt E (TangentSpace I) (γv 0)).continuousLinearMapAt ℝ (γv (c • t)) (Pv (c • t)) at hchart
    rw [show γcv 0 = p from (radialCurve_zero (I := I) g p (c • v))] at hchart
    rw [show γv 0 = p from (radialCurve_zero (I := I) g p v)] at hchart
    rw [hγ_eq t] at hchart
    have hround_l : (trivializationAt E (TangentSpace I) p).symmL ℝ (γv (c • t))
        ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γv (c • t)) (Pcv t)) =
        Pcv t :=
      (trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hmem (Pcv t)
    have hround_r : (trivializationAt E (TangentSpace I) p).symmL ℝ (γv (c • t))
        ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γv (c • t)) (Pv (c • t))) =
        Pv (c • t) :=
      (trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt (R := ℝ) hmem (Pv (c • t))
    exact hround_l.symm.trans
      ((congrArg ((trivializationAt E (TangentSpace I) p).symmL ℝ (γv (c • t))) hchart).trans
        hround_r)
  change Pcv t = Pv (c • t)
  exact hsec

end RadialParallelTransport


section RadialTransportSection

variable [T2Space M]

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [CompleteSpace E] [T2Space M] [T2Space (TangentBundle I M)] in
private lemma tangentModelSymm_coe_norm (p : M) (v : E) :
    ‖(((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm v : TangentSpace I p) : E)‖ =
      ‖v‖ := by
  rw [tangentSpaceModelContinuousLinearEquiv_symm_apply]
  rfl

noncomputable def radialTransportSection (g : SmoothRiemannianMetric I M) (p : M)
    (η₀ : TangentSpace I p) : ∀ y : M, TangentSpace I y := by
  classical
  exact fun y =>
    if h : y ∈ (normalChartAt (I := I) g p).source ∧
        ‖normalChartAt (I := I) g p y‖ < radialRadius (I := I) g p then
      let v : TangentSpace I p := (tangentSpaceModelContinuousLinearEquiv (I := I) p).symm
        (normalChartAt (I := I) g p y)
      let hv : ‖(v : E)‖ < radialRadius (I := I) g p := by
        rw [tangentModelSymm_coe_norm (I := I)]
        exact h.2
      (tangentSpaceModelContinuousLinearEquiv (I := I) y).symm
        (tangentSpaceModelContinuousLinearEquiv (I := I)
          (expMap (I := I) g p ((1 : ℝ) • v))
          (radialParallelTransportSection g p hv η₀ 1))
    else 0

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
lemma expMap_mem_normalChartAt_source_of_norm_lt_radialRadius (g : SmoothRiemannianMetric I M)
    (p : M) {X : TangentSpace I p} {s : ℝ}
    (hs : ‖s • (X : E)‖ < expMapC2Radius (I := I) g p) :
    expMap (I := I) g p (s • X) ∈ (normalChartAt (I := I) g p).source := by
  have hsrcE : s • (X : E) ∈ (expMapDiffeo (I := I) g p).source :=
    mem_expMapDiffeo_source_of_norm_lt_radius (I := I) g p hs
  have hmap : expMapDiffeo (I := I) g p (s • (X : E)) ∈ (expMapDiffeo (I := I) g p).target :=
    (expMapDiffeo (I := I) g p).map_source hsrcE
  have hmem : expMap (I := I) g p (s • X) ∈ (expMapDiffeo (I := I) g p).target := by
    rwa [expMapDiffeo_apply_eq (I := I) g p hsrcE] at hmap
  rwa [normalChartAt_source_eq (I := I) g p]

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
private lemma radialParallelTransportSection_congr_initial_vector (g : SmoothRiemannianMetric I M)
    (p : M) (η₀ : TangentSpace I p) {a b : TangentSpace I p}
    (ha : ‖(a : E)‖ < radialRadius (I := I) g p) (hb : ‖(b : E)‖ < radialRadius (I := I) g p)
    (hab : a = b) (t : ℝ) :
    radialParallelTransportSection g p ha η₀ t = radialParallelTransportSection g p hb η₀ t := by
  subst b
  rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
theorem radialTransportSection_pullback_eq (g : SmoothRiemannianMetric I M) (p : M)
    (η₀ : TangentSpace I p) {X : TangentSpace I p} (hX : ‖(X : E)‖ < radialRadius (I := I) g p)
    {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1) :
    radialTransportSection g p η₀ (expMap (I := I) g p (s • X)) =
      radialParallelTransportSection g p hX η₀ s := by
  classical
  have hs_norm : ‖s • (X : E)‖ < expMapC2Radius (I := I) g p :=
    norm_smul_lt_expMapC2Radius_of_lt_radialRadius (I := I) g p hX
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hs_norm_radius : ‖s • (X : E)‖ < radialRadius (I := I) g p := by
    have hnorm : ‖s • (X : E)‖ ≤ ‖(X : E)‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have habs : |s| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      exact (mul_le_mul_of_nonneg_right habs (norm_nonneg (X : E))).trans_eq (one_mul _)
    exact lt_of_le_of_lt hnorm hX
  have hv : normalChartAt (I := I) g p (expMap (I := I) g p (s • X)) = (s • X : E) :=
    normalChartAt_expMap_smul (I := I) g p (X : E) s (ball_subset_normalChartAt_target
      (I := I) g p hs_norm)
  have hcond : expMap (I := I) g p (s • X) ∈ (normalChartAt (I := I) g p).source ∧
      ‖normalChartAt (I := I) g p (expMap (I := I) g p (s • X))‖ < radialRadius (I := I) g p := by
    constructor
    · exact expMap_mem_normalChartAt_source_of_norm_lt_radialRadius (I := I) g p hs_norm
    · rw [hv]
      exact hs_norm_radius
  have hcond_model :
      ‖(((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm
        (normalChartAt (I := I) g p (expMap (I := I) g p (s • X))) :
          TangentSpace I p) : E)‖ < radialRadius (I := I) g p := by
    rw [tangentModelSymm_coe_norm (I := I)]
    exact hcond.2
  apply (tangentSpaceModelContinuousLinearEquiv (I := I)
    (expMap (I := I) g p (s • X))).injective
  rw [radialTransportSection, dif_pos hcond]
  dsimp only
  rw [ContinuousLinearEquiv.apply_symm_apply]
  have hEq : radialParallelTransportSection (I := I) g p
      (v := (tangentSpaceModelContinuousLinearEquiv (I := I) p).symm
        (normalChartAt (I := I) g p (expMap (I := I) g p (s • X))))
      hcond_model η₀ 1 =
    radialParallelTransportSection (I := I) g p (v := s • X) hs_norm_radius η₀ 1 := by
    exact radialParallelTransportSection_congr_initial_vector (I := I) g p η₀
      hcond_model
      hs_norm_radius
      (by
        apply (tangentSpaceModelContinuousLinearEquiv (I := I) p).injective
        rw [ContinuousLinearEquiv.apply_symm_apply]
        simpa only [tangentSpaceModelContinuousLinearEquiv_apply] using hv)
      1
  have hscale := radialParallelTransportSection_rescale (I := I) g p hX η₀
    (hc := hs) (t := 1) ⟨by norm_num, le_rfl⟩
  rw [smul_eq_mul, mul_one] at hscale
  simpa only [tangentSpaceModelContinuousLinearEquiv_apply] using
    congrArg (fun z => (z : E)) (hEq.trans hscale)

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
theorem radialTransportSection_center (g : SmoothRiemannianMetric I M) (p : M)
    (η₀ : TangentSpace I p) (X : TangentSpace I p) (hX : ‖(X : E)‖ < radialRadius (I := I) g p) :
    radialTransportSection g p η₀ p = η₀ := by
  have h := radialTransportSection_pullback_eq (I := I) g p η₀ hX (s := 0) ⟨by norm_num, by norm_num⟩
  rw [radialCurve_zero (I := I) g p X] at h
  rw [radialParallelTransportSection_initial (I := I) g p hX η₀] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] in
private theorem radialTransportSection_nabla_center_zero_of_norm_lt
    (g : SmoothRiemannianMetric I M) (p : M)
    (η₀ : TangentSpace I p) {X : TangentSpace I p} (hX : ‖(X : E)‖ < radialRadius (I := I) g p)
    (hη : MDiffAt (T% (radialTransportSection g p η₀)) p) :
    (LeviCivita (I := I) g).toFun (radialTransportSection g p η₀) p X = 0 := by
  classical
  set σ : Π x : M, TangentSpace I x := radialTransportSection (I := I) g p η₀ with hσ
  set γ : ℝ → M := fun s => expMap (I := I) g p (s • X) with hγ
  have hγ0 : γ 0 = p := by
    rw [hγ]
    exact radialCurve_zero (I := I) g p X
  have hvel : mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) = X := by
    rw [hγ]
    exact radialCurve_velocity (I := I) g p X
  have hγ2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ 0 := by
    rw [hγ]
    have h0 : ‖(0 : ℝ) • (X : E)‖ < expMapC2Radius (I := I) g p := by
      rw [zero_smul, norm_zero]
      exact expMapC2Radius_pos (I := I) g p
    exact radialCurve_contMDiffAt2 (I := I) g p (X : E) 0 h0
  have hσ_at : MDiffAt (T% σ) (γ 0) := by
    rw [hγ0]
    simpa [hσ] using hη
  have hagree : (fun s => σ (γ s)) =ᶠ[𝓝 (0 : ℝ)] (fun s => σ (γ s)) := by rfl
  have hpar : covDerivAlong (I := I) g γ (fun s => σ (γ s)) 0 = 0 := by
    have heq : (fun s => σ (γ s)) =ᶠ[𝓝 (0 : ℝ)]
        (radialParallelTransportSection (I := I) g p hX η₀) := by
      have h0 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
      filter_upwards [isOpen_Ioo.mem_nhds h0] with s hs
      have hp := radialTransportSection_pullback_eq (I := I) g p η₀ hX hs
      rw [hσ, hγ]
      exact hp
    rw [covDerivAlong_congr_of_eventuallyEq (I := I) g γ heq]
    exact radialParallelTransportSection_covDerivAlong (I := I) g p hX η₀ ⟨by norm_num, by norm_num⟩
  have hbridge := covDerivAlong_eq_leviCivita_of_eventuallyEq (I := I) g γ 0
    (hγ2.of_le (by norm_num)) hσ_at hagree
  have hmain : (LeviCivita (I := I) g).toFun σ (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) = 0 := by
    rw [← hbridge]
    exact hpar
  have hfinal : (LeviCivita (I := I) g).toFun σ p X = 0 := by
    rw [hvel] at hmain
    rw [hγ0] at hmain
    exact hmain
  exact hfinal

omit [NeZero (Module.finrank ℝ E)] in
theorem radialTransportSection_nabla_center_zero (g : SmoothRiemannianMetric I M) (p : M)
    (η₀ X : TangentSpace I p)
    (hη : MDiffAt (T% (radialTransportSection g p η₀)) p) :
    (LeviCivita (I := I) g).toFun (radialTransportSection g p η₀) p X = 0 := by
  let d : ℝ := radialRadius (I := I) g p / (2 * (‖(X : E)‖ + 1))
  have hd_pos : 0 < d := by
    dsimp [d]
    exact div_pos (radialRadius_pos (I := I) g p) (by positivity)
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hsmall : ‖(d • X : E)‖ < radialRadius (I := I) g p := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd_pos]
    have hden : (‖(X : E)‖ + 1 : ℝ) ≠ 0 := by positivity
    have hd1 : d * (‖(X : E)‖ + 1) = radialRadius (I := I) g p / 2 := by
      dsimp [d]
      field_simp [hden]
    have hlt : d * ‖(X : E)‖ < radialRadius (I := I) g p / 2 := by
      rw [← hd1]
      exact mul_lt_mul_of_pos_left (by linarith) hd_pos
    linarith [radialRadius_pos (I := I) g p]
  have hzero := radialTransportSection_nabla_center_zero_of_norm_lt
    (I := I) g p η₀ hsmall hη
  have hlin : (LeviCivita (I := I) g).toFun
      (radialTransportSection g p η₀) p (d • X) =
      d • (LeviCivita (I := I) g).toFun
        (radialTransportSection g p η₀) p X := by
    exact map_smul _ d X
  have hd_zero : d • (LeviCivita (I := I) g).toFun
      (radialTransportSection g p η₀) p X = 0 := by
    rw [← hlin]
    exact hzero
  exact (smul_eq_zero.mp hd_zero).resolve_left hd_ne

end RadialTransportSection

section SecondOrderFlatness

variable [T2Space M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [CompleteSpace E] [T2Space M] [T2Space (TangentBundle I M)] in
private lemma trivToE_self_eq (x : M) (v : TangentSpace I x) :
    trivToE (I := I) x x v = (v : E) := by
  rw [trivToE]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := x) (b := x) (mem_chart_source H x)]
  exact (tangentBundleCore I M).coordChange_self (achart H x) x (mem_chart_source H x) v

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space M] [T2Space (TangentBundle I M)] in
private lemma chartBasisVecFiber_trivToE (p : M) (a : Fin (Module.finrank ℝ E)) {y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) p).baseSet) :
    trivToE (I := I) p y (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) p a y) = DifferentialGeometry.Tensor.Coordinates.chartModelBasis E a := by
  classical
  rw [trivToE]
  change ((trivializationAt E (TangentSpace I) p).linearMapAt ℝ y)
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) p a y) = DifferentialGeometry.Tensor.Coordinates.chartModelBasis E a
  rw [Trivialization.coe_linearMapAt_of_mem
    (e := trivializationAt E (TangentSpace I) p) (R := ℝ) (b := y) hy]
  exact DifferentialGeometry.Tensor.Coordinates.trivializationAt_chartBasisVec_snd (I := I) p a hy

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space M] [T2Space (TangentBundle I M)] in
private lemma chartBasisVecFiber_self_coe (p : M) (a : Fin (Module.finrank ℝ E)) :
    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) p a p : E) = DifferentialGeometry.Tensor.Coordinates.chartModelBasis E a := by
  rw [← trivToE_self_eq p (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) p a p)]
  exact chartBasisVecFiber_trivToE (I := I) p a
    (by rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H p)

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
theorem radialTransportSection_covDerivAlong_center_zero (g : SmoothRiemannianMetric I M)
    (p : M) {X : TangentSpace I p} (hX : ‖(X : E)‖ < radialRadius (I := I) g p)
    (η₀ : TangentSpace I p) :
    ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      covDerivAlong (I := I) g (fun s : ℝ => expMap (I := I) g p (s • X))
        (fun s : ℝ => radialTransportSection (I := I) g p η₀
          (expMap (I := I) g p (s • X))) t = 0 := by
  intro t ht
  have heq : (fun s : ℝ => radialTransportSection (I := I) g p η₀
        (expMap (I := I) g p (s • X))) =ᶠ[𝓝 t]
      radialParallelTransportSection (I := I) g p hX η₀ := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact radialTransportSection_pullback_eq (I := I) g p η₀ hX hs
  rw [covDerivAlong_congr_of_eventuallyEq (I := I) g
    (fun s : ℝ => expMap (I := I) g p (s • X)) heq]
  exact radialParallelTransportSection_covDerivAlong (I := I) g p hX η₀
    ⟨by linarith [ht.1], by linarith [ht.2]⟩

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
private theorem radialTransportSection_hasDerivAt_chartCurve
    (g : SmoothRiemannianMetric I M) (p : M) {X : TangentSpace I p}
    (hX : ‖(X : E)‖ < radialRadius (I := I) g p) (η₀ : TangentSpace I p)
    {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt
      (fun s : ℝ => trivToE (I := I) p (expMap (I := I) g p (s • X))
        (radialTransportSection (I := I) g p η₀ (expMap (I := I) g p (s • X))))
      (- chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p (fun s : ℝ => expMap (I := I) g p (s • X))) t)
          (trivToE (I := I) p (expMap (I := I) g p (t • X))
            (radialTransportSection (I := I) g p η₀ (expMap (I := I) g p (t • X))))
          (chartCurve (I := I) p (fun s : ℝ => expMap (I := I) g p (s • X)) t))
      t := by
  classical
  set γ : ℝ → M := fun s => expMap (I := I) g p (s • X) with hγ
  set σ : Π y : M, TangentSpace I y := radialTransportSection (I := I) g p η₀ with hσ
  set P : ∀ s, TangentSpace I (γ s) := radialParallelTransportSection (I := I) g p hX η₀ with hP
  have htIcc : t ∈ Set.Icc (-1 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hODE := radialParallelTransportSection_ode (I := I) g p hX η₀ htIcc
  have hODE_at : HasDerivAt (chartRepAt (I := I) γ P 0)
      (- chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p γ) t)
          (chartRepAt (I := I) γ P 0 t)
          (chartCurve (I := I) p γ t)) t :=
    hODE.hasDerivAt (Icc_mem_nhds ht.1 (by linarith [ht.2]))
  have hfun_eq : (fun s : ℝ => trivToE (I := I) p (γ s) (σ (γ s))) =ᶠ[𝓝 t]
      chartRepAt (I := I) γ P 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    rw [chartRepAt_apply]
    rw [show γ 0 = p from by simpa [hγ] using (radialCurve_zero (I := I) g p X)]
    rw [hσ, hP]
    refine congrArg (trivToE (I := I) p (γ s)) ?_
    exact radialTransportSection_pullback_eq (I := I) g p η₀ hX hs
  have hval_eq :
      trivToE (I := I) p (γ t) (σ (γ t)) = chartRepAt (I := I) γ P 0 t := by
    exact hfun_eq.eq_of_nhds
  have hres : HasDerivAt (fun s : ℝ => trivToE (I := I) p (γ s) (σ (γ s)))
      (- chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p γ) t)
          (chartRepAt (I := I) γ P 0 t)
          (chartCurve (I := I) p γ t)) t :=
    hODE_at.congr_of_eventuallyEq hfun_eq
  rw [← hval_eq] at hres
  convert! hres using 1

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
private lemma radialCurve_chartCurve_deriv_zero (g : SmoothRiemannianMetric I M) (p : M)
    (X : TangentSpace I p) :
    deriv (chartCurve (I := I) p (fun s : ℝ => expMap (I := I) g p (s • X))) 0 = (X : E) := by
  classical
  set γ : ℝ → M := fun s => expMap (I := I) g p (s • X) with hγ
  have hγ0 : γ 0 = p := by simpa [hγ] using (radialCurve_zero (I := I) g p X)
  have hvel : mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) = X := by
    rw [hγ]
    exact radialCurve_velocity (I := I) g p X
  have hγ2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ 0 := by
    rw [hγ]
    have h0 : ‖(0 : ℝ) • (X : E)‖ < expMapC2Radius (I := I) g p := by
      rw [zero_smul, norm_zero]
      exact expMapC2Radius_pos (I := I) g p
    exact radialCurve_contMDiffAt2 (I := I) g p (X : E) 0 h0
  have hsrc : γ 0 ∈ (chartAt H p).source := by
    rw [hγ0]
    exact mem_chart_source H p
  have hbridge := chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
    (I := I) (M := M) (hγ2.mdifferentiableAt (by decide)) p hsrc
  have hchart : trivToE (I := I) p (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) =
      deriv (chartCurve (I := I) p γ) 0 := by
    change trivToE (I := I) p (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) =
      deriv (chartCurve (I := I) p γ) 0 at hbridge
    exact hbridge
  rw [hγ]
  rw [← hchart]
  rw [hvel]
  rw [hγ0]
  exact trivToE_self_eq (I := I) p X

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
private theorem radialTransportSection_chartRep_hasDerivAt
    (g : SmoothRiemannianMetric I M) (p : M) {X : TangentSpace I p}
    (hX : ‖(X : E)‖ < radialRadius (I := I) g p) (η₀ : TangentSpace I p)
    {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt
      (fun s : ℝ => chartESectionRepr (I := I) p (radialTransportSection (I := I) g p η₀)
        (expMap (I := I) g p (s • X)))
      (- chartChristoffelContraction (I := I) g p
          (deriv (chartCurve (I := I) p (fun s : ℝ => expMap (I := I) g p (s • X))) t)
          (chartESectionRepr (I := I) p (radialTransportSection (I := I) g p η₀)
            (expMap (I := I) g p (t • X)))
          (chartCurve (I := I) p (fun s : ℝ => expMap (I := I) g p (s • X)) t))
      t := by
  classical
  set γ : ℝ → M := fun s => expMap (I := I) g p (s • X) with hγ
  set σ : Π y : M, TangentSpace I y := radialTransportSection (I := I) g p η₀ with hσ
  have hB1 := radialTransportSection_hasDerivAt_chartCurve (I := I) g p hX η₀ ht
  simpa only [hγ, hσ, chartE_section_repr_eq_trivToE] using hB1

omit [NeZero (Module.finrank ℝ E)] in
private lemma radialTransportSection_chartE_firstOrder
    (g : SmoothRiemannianMetric I M) (p : M) (η₀ : TangentSpace I p)
    (hη : MDiffAt (T% (radialTransportSection (I := I) g p η₀)) p)
    {v : E} :
    fderiv ℝ (chartESectionRepr (I := I) p (radialTransportSection (I := I) g p η₀) ∘
        (extChartAt I p).symm) (extChartAt I p p) v +
      chartChristoffelContraction (I := I) g p v
        (chartESectionRepr (I := I) p (radialTransportSection (I := I) g p η₀) p)
        (extChartAt I p p) = 0 := by
  classical
  set σ : Π y : M, TangentSpace I y := radialTransportSection (I := I) g p η₀ with hσ
  have hmd : MDiffAt (T% σ) p := by simpa [hσ] using hη
  have hconn : (LeviCivita (I := I) g).toFun σ p (trivFromE (I := I) p p v) = 0 := by
    simpa [hσ] using radialTransportSection_nabla_center_zero
      (I := I) g p η₀ (trivFromE (I := I) p p v) hmd
  have hgood : p ∈ chartLeviCivitaGoodSet (I := I) p :=
    self_mem_chartLeviCivitaGoodSet (I := I) p
  have hchart := LeviCivita_chart_apply (I := I) g p hgood hmd (trivFromE (I := I) p p v)
  have hchart2 := chartLeviCivita_apply (I := I) g p σ hgood (trivFromE (I := I) p p v)
  have hbase : p ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H p
  have htriv : trivToE (I := I) p p (trivFromE (I := I) p p v) = v :=
    trivToE_trivFromE (I := I) p hbase v
  have hcorr := correction_eq_contr (I := I) g p p
    (chartESectionRepr (I := I) p σ p) (trivFromE (I := I) p p v)
  have h0 : trivFromE (I := I) p p
      (fderiv ℝ (chartESectionRepr (I := I) p σ ∘ (extChartAt I p).symm) (extChartAt I p p) v +
        chartChristoffelContraction (I := I) g p v
          (chartESectionRepr (I := I) p σ p) (extChartAt I p p)) = 0 := by
    rw [← htriv]
    rw [← hcorr]
    rw [← hchart2, ← hchart]
    exact hconn
  have h0' : fderiv ℝ (chartESectionRepr (I := I) p σ ∘ (extChartAt I p).symm)
        (extChartAt I p p) v +
      chartChristoffelContraction (I := I) g p v
        (chartESectionRepr (I := I) p σ p) (extChartAt I p p) = 0 := by
    have := congrArg (trivToE (I := I) p p) h0
    rw [trivToE_trivFromE (I := I) p hbase
      (fderiv ℝ (chartESectionRepr (I := I) p σ ∘ (extChartAt I p).symm) (extChartAt I p p) v +
        chartChristoffelContraction (I := I) g p v
          (chartESectionRepr (I := I) p σ p) (extChartAt I p p))] at this
    simpa using this
  simpa [hσ] using h0'

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space M] [T2Space (TangentBundle I M)] in
private lemma chartChristoffelContraction_constArg_contDiffOn (g : SmoothRiemannianMetric I M)
    (α : M) (a : E) :
    ContDiffOn ℝ 1
      (fun z : E × E => chartChristoffelContraction (I := I) g α a z.2 z.1)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) := by
  classical
  unfold chartChristoffelContraction
  refine ContDiffOn.sum (fun k _ => ?_)
  have hscalar : ContDiffOn ℝ 1
      (fun z : E × E =>
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j k z.1 *
            chartCoord (E := E) i a * chartCoord (E := E) j z.2)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) := by
    refine ContDiffOn.sum (fun i _ => ?_)
    refine ContDiffOn.sum (fun j _ => ?_)
    have hΓ : ContDiffOn ℝ 1
        (fun z : E × E => chartChristoffel (I := I) g α i j k z.1)
        ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) := by
      have hbase : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α i j k)
          (interior (extChartAt I α).target) :=
        chartChristoffel_contDiffOn_interior (I := I) g α i j k
      have hfst : ContDiff ℝ 1 (Prod.fst : E × E → E) :=
        contDiff_fst.of_le (WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞)))
      have hmapsto : MapsTo (Prod.fst : E × E → E)
          ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E))
          (interior (extChartAt I α).target) := fun _ hp => hp.1
      exact (hbase.of_le (WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞)))).comp hfst.contDiffOn hmapsto
    have hconst : ContDiffOn ℝ 1
        (fun _ : E × E => chartCoord (E := E) i a)
        ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :=
      contDiffOn_const
    have hCLM_j : ContDiff ℝ 1 (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord j).toContinuousLinearMap) :=
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord j).toContinuousLinearMap.contDiff.of_le
        (WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞)))
    have hsnd : ContDiff ℝ 1 (Prod.snd : E × E → E) :=
      contDiff_snd.of_le (WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞)))
    have hcj : ContDiffOn ℝ 1
        (fun z : E × E => chartCoord (E := E) j z.2)
        ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :=
      (hCLM_j.comp hsnd).contDiffOn
    exact (hΓ.mul hconst).mul hcj
  have hconstk : ContDiffOn ℝ 1
      (fun _ : E × E => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E)) :=
    contDiffOn_const
  exact hscalar.smul hconstk

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space M] [T2Space (TangentBundle I M)] in
private lemma deriv_chartContraction_constArg_along (g : SmoothRiemannianMetric I M) (p : M)
    {x s : ℝ → E} {e xu su : E} {x₀ : E}
    (hx₀ : x₀ ∈ interior (extChartAt I p).target)
    (hx₀eq : x 0 = x₀) (hx : HasDerivAt x xu 0) (hs : HasDerivAt s su 0) :
    deriv (fun t : ℝ => chartChristoffelContraction (I := I) g p e (s t) (x t)) 0 =
      (fderiv ℝ (fun y : E => chartChristoffelContraction (I := I) g p e (s 0) y) x₀) xu +
      chartChristoffelContraction (I := I) g p e su x₀ := by
  classical
  set H : E × E → E := fun z => chartChristoffelContraction (I := I) g p e z.2 z.1 with hH
  have hcd : ContDiffOn ℝ 1 H ((interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) := by
    simpa [hH] using chartChristoffelContraction_constArg_contDiffOn (I := I) g p e
  have hmem : (x₀, s 0) ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) :=
    ⟨hx₀, Set.mem_univ _⟩
  have hopen : IsOpen ((interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :=
    isOpen_interior.prod isOpen_univ
  have hdOn : DifferentiableOn ℝ H
      ((interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :=
    hcd.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hHd : HasFDerivAt H (fderiv ℝ H (x₀, s 0)) (x₀, s 0) :=
    ((hdOn (x₀, s 0) hmem).differentiableAt (hopen.mem_nhds hmem)).hasFDerivAt
  let f : ℝ → E × E := fun t => (x t, s t)
  have hxys : HasDerivAt f (xu, su) 0 := by
    simpa [f] using (hx.prodMk hs)
  have hHd' : HasFDerivAt H (fderiv ℝ H (x₀, s 0)) (f 0) := by
    simpa [f, hx₀eq] using hHd
  have hcompF : HasFDerivAt (fun t : ℝ => H (f t))
      ((fderiv ℝ H (x₀, s 0)).comp (ContinuousLinearMap.toSpanSingleton ℝ (xu, su))) 0 :=
    hHd'.comp 0 hxys.hasFDerivAt
  have hcomp : HasDerivAt (fun t : ℝ => H (f t))
      ((fderiv ℝ H (x₀, s 0)) (xu, su)) 0 := by
    simpa using hcompF.hasDerivAt
  have hfun : (fun t : ℝ => chartChristoffelContraction (I := I) g p e (s t) (x t)) =
      fun t : ℝ => H (f t) := by
    funext t
    rfl
  rw [hfun]
  rw [hcomp.deriv]
  have hu : (fderiv ℝ H (x₀, s 0)) (xu, 0) =
      (fderiv ℝ (fun y : E => H (y, s 0)) x₀) xu := by
    have hι : HasFDerivAt (fun y : E => (y, s 0))
        ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E)) x₀ := by
      have h1 : HasFDerivAt (fun y : E => y) (ContinuousLinearMap.id ℝ E) x₀ :=
        (ContinuousLinearMap.id ℝ E).hasFDerivAt
      have h2 : HasFDerivAt (fun _ : E => s 0) (0 : E →L[ℝ] E) x₀ :=
        hasFDerivAt_const (c := s 0) (x := x₀)
      exact h1.prodMk h2
    have hfc : fderiv ℝ (fun y : E => H (y, s 0)) x₀ =
        (fderiv ℝ H (x₀, s 0)).comp (fderiv ℝ (fun y : E => (y, s 0)) x₀) := by
      have h1 : DifferentiableAt ℝ H (x₀, s 0) := hHd.differentiableAt
      have h2 : DifferentiableAt ℝ (fun y : E => (y, s 0)) x₀ := hι.differentiableAt
      rw [← fderiv_comp (x := x₀) h1 h2]
      rfl
    rw [hfc]
    rw [ContinuousLinearMap.comp_apply]
    have hιd : fderiv ℝ (fun y : E => (y, s 0)) x₀ xu = (xu, 0) := by
      simpa using congrArg (fun L : E →L[ℝ] E × E => L xu) hι.fderiv
    rw [hιd]
  have hslice : (fderiv ℝ H (x₀, s 0)) (0, su) =
      fderiv ℝ (fun w : E => H (x₀, w)) (s 0) su := by
    have hι : HasFDerivAt (fun w : E => (x₀, w)) ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) (s 0) := by
      have h1 : HasFDerivAt (fun _ : E => x₀) (0 : E →L[ℝ] E) (s 0) :=
        hasFDerivAt_const (c := x₀) (x := s 0)
      have h2 : HasFDerivAt (fun w : E => w) (ContinuousLinearMap.id ℝ E) (s 0) :=
        (ContinuousLinearMap.id ℝ E).hasFDerivAt
      exact h1.prodMk h2
    have hfc : fderiv ℝ (fun w : E => H (x₀, w)) (s 0) =
        (fderiv ℝ H (x₀, s 0)).comp (fderiv ℝ (fun w : E => (x₀, w)) (s 0)) := by
      have h1 : DifferentiableAt ℝ H (x₀, s 0) := hHd.differentiableAt
      have h2 : DifferentiableAt ℝ (fun w : E => (x₀, w)) (s 0) := hι.differentiableAt
      rw [← fderiv_comp (x := s 0) h1 h2]
      rfl
    rw [hfc]
    rw [ContinuousLinearMap.comp_apply]
    have hιd : fderiv ℝ (fun w : E => (x₀, w)) (s 0) su = (0, su) := by
      simpa using congrArg (fun L : E →L[ℝ] E × E => L su) hι.fderiv
    rw [hιd]
  have hv : (fderiv ℝ H (x₀, s 0)) (0, su) =
      chartChristoffelContraction (I := I) g p e su x₀ := by
    rw [hslice]
    have hlin : (fun w : E => H (x₀, w)) = chartChristoffelContractionRightCLM (I := I) g p e x₀ := by
      funext w
      rfl
    rw [hlin]
    have hld : fderiv ℝ (chartChristoffelContractionRightCLM (I := I) g p e x₀) (s 0) =
        chartChristoffelContractionRightCLM (I := I) g p e x₀ :=
      (chartChristoffelContractionRightCLM (I := I) g p e x₀).hasFDerivAt.fderiv
    rw [hld]
    exact chartChristoffelContractionRightCLM_apply (I := I) g p e x₀ su
  have hsplit : (fderiv ℝ H (x₀, s 0)) (xu, su) =
      (fderiv ℝ H (x₀, s 0)) (xu, 0) + (fderiv ℝ H (x₀, s 0)) (0, su) := by
    have hlin1 : (xu, su) = (xu, 0) + (0, su) := by ext <;> simp
    rw [hlin1]
    exact map_add (fderiv ℝ H (x₀, s 0)) (xu, 0) (0, su)
  rw [hsplit, hu, hv]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space M] [T2Space (TangentBundle I M)] in
private lemma chartChristoffelContraction_full_contDiffOn (g : SmoothRiemannianMetric I M)
    (α : M) :
    ContDiffOn ℝ 1
      (fun z : E × E × E => chartChristoffelContraction (I := I) g α z.2.1 z.2.2 z.1)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) := by
  classical
  have hle : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) :=
    WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞))
  have hfst : ContDiff ℝ 1 (fun z : E × E × E => z.1) :=
    (contDiff_fst (𝕜 := ℝ) (E := E) (F := E × E)).of_le hle
  have hproj21 : ContDiff ℝ 1 (fun z : E × E × E => z.2.1) := by
    have h1 : ContDiff ℝ ∞ (Prod.snd : E × (E × E) → E × E) :=
      contDiff_snd (𝕜 := ℝ) (E := E) (F := E × E)
    have h2 : ContDiff ℝ ∞ (Prod.fst : E × E → E) :=
      contDiff_fst (𝕜 := ℝ) (E := E) (F := E)
    exact (h2.comp h1).of_le hle
  have hproj22 : ContDiff ℝ 1 (fun z : E × E × E => z.2.2) := by
    have h1 : ContDiff ℝ ∞ (Prod.snd : E × (E × E) → E × E) :=
      contDiff_snd (𝕜 := ℝ) (E := E) (F := E × E)
    have h2 : ContDiff ℝ ∞ (Prod.snd : E × E → E) :=
      contDiff_snd (𝕜 := ℝ) (E := E) (F := E)
    exact (h2.comp h1).of_le hle
  unfold chartChristoffelContraction
  refine ContDiffOn.sum (fun k _ => ?_)
  have hscalar : ContDiffOn ℝ 1
      (fun z : E × E × E =>
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j k z.1 *
            chartCoord (E := E) i z.2.1 * chartCoord (E := E) j z.2.2)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) := by
    refine ContDiffOn.sum (fun i _ => ?_)
    refine ContDiffOn.sum (fun j _ => ?_)
    have hΓ : ContDiffOn ℝ 1
        (fun z : E × E × E => chartChristoffel (I := I) g α i j k z.1)
        ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) := by
      have hbase : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α i j k)
          (interior (extChartAt I α).target) :=
        chartChristoffel_contDiffOn_interior (I := I) g α i j k
      have hmapsto : MapsTo (fun z : E × E × E => z.1)
          ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E))
          (interior (extChartAt I α).target) := fun _ hp => hp.1
      exact (hbase.of_le hle).comp hfst.contDiffOn hmapsto
    have hCLM_i : ContDiff ℝ 1 (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord i).toContinuousLinearMap) :=
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord i).toContinuousLinearMap.contDiff.of_le hle
    have hCLM_j : ContDiff ℝ 1 (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord j).toContinuousLinearMap) :=
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord j).toContinuousLinearMap.contDiff.of_le hle
    have hvi : ContDiffOn ℝ 1
        (fun z : E × E × E => chartCoord (E := E) i z.2.1)
        ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) :=
      (hCLM_i.comp hproj21).contDiffOn
    have hwj : ContDiffOn ℝ 1
        (fun z : E × E × E => chartCoord (E := E) j z.2.2)
        ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) :=
      (hCLM_j.comp hproj22).contDiffOn
    exact (hΓ.mul hvi).mul hwj
  have hconstk : ContDiffOn ℝ 1
      (fun _ : E × E × E => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) :=
    contDiffOn_const
  exact hscalar.smul hconstk

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space M] [T2Space (TangentBundle I M)] in
private lemma deriv_chartContraction_full_along (g : SmoothRiemannianMetric I M) (p : M)
    {x u s : ℝ → E} {u0 xu xuu su : E} {x₀ : E}
    (hx₀ : x₀ ∈ interior (extChartAt I p).target)
    (hx₀eq : x 0 = x₀) (hu0 : u 0 = u0)
    (hx : HasDerivAt x xu 0) (hu : HasDerivAt u xuu 0) (hs : HasDerivAt s su 0) :
    deriv (fun t : ℝ => chartChristoffelContraction (I := I) g p (u t) (s t) (x t)) 0 =
      (fderiv ℝ (fun y : E => chartChristoffelContraction (I := I) g p u0 (s 0) y) x₀) xu +
      chartChristoffelContraction (I := I) g p xuu (s 0) x₀ +
      chartChristoffelContraction (I := I) g p u0 su x₀ := by
  classical
  set H : E × E × E → E := fun z => chartChristoffelContraction (I := I) g p z.2.1 z.2.2 z.1 with hH
  set P : E × E × E := (x₀, (u0, s 0)) with hP
  have hcd : ContDiffOn ℝ 1 H
      ((interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) := by
    simpa [hH] using chartChristoffelContraction_full_contDiffOn (I := I) g p
  have hmem : P ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E) := by
    rw [hP]
    exact ⟨hx₀, Set.mem_univ _, Set.mem_univ _⟩
  have hopen : IsOpen ((interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) :=
    isOpen_interior.prod (isOpen_univ.prod isOpen_univ)
  have hdOn : DifferentiableOn ℝ H
      ((interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) :=
    hcd.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hHd : HasFDerivAt H (fderiv ℝ H P) P :=
    ((hdOn P hmem).differentiableAt (hopen.mem_nhds hmem)).hasFDerivAt
  let f : ℝ → E × E × E := fun t => (x t, (u t, s t))
  have hf : HasDerivAt f (xu, (xuu, su)) 0 := by
    simpa [f] using (hx.prodMk (hu.prodMk hs))
  have hHd' : HasFDerivAt H (fderiv ℝ H P) (f 0) := by
    simpa [f, hP, hx₀eq, hu0] using hHd
  have hcompF : HasFDerivAt (fun t : ℝ => H (f t))
      ((fderiv ℝ H P).comp (ContinuousLinearMap.toSpanSingleton ℝ (xu, (xuu, su)))) 0 :=
    hHd'.comp 0 hf.hasFDerivAt
  have hcomp : HasDerivAt (fun t : ℝ => H (f t))
      ((fderiv ℝ H P) (xu, (xuu, su))) 0 := by
    simpa using hcompF.hasDerivAt
  have hfun : (fun t : ℝ => chartChristoffelContraction (I := I) g p (u t) (s t) (x t)) =
      fun t : ℝ => H (f t) := by
    funext t
    rfl
  rw [hfun]
  rw [hcomp.deriv]
  have hs1 : (fderiv ℝ H P) (xu, 0, 0) =
      (fderiv ℝ (fun y : E => H (y, (u0, s 0))) x₀) xu := by
    have hι : HasFDerivAt (fun y : E => (y, (u0, s 0)))
        ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E × E)) x₀ := by
      have h1 : HasFDerivAt (fun y : E => y) (ContinuousLinearMap.id ℝ E) x₀ :=
        (ContinuousLinearMap.id ℝ E).hasFDerivAt
      have h2 : HasFDerivAt (fun _ : E => (u0, s 0)) (0 : E →L[ℝ] E × E) x₀ :=
        hasFDerivAt_const (c := (u0, s 0)) (x := x₀)
      exact h1.prodMk h2
    have hfc : fderiv ℝ (fun y : E => H (y, (u0, s 0))) x₀ =
        (fderiv ℝ H P).comp (fderiv ℝ (fun y : E => (y, (u0, s 0))) x₀) := by
      have h1 : DifferentiableAt ℝ H P := hHd.differentiableAt
      have h2 : DifferentiableAt ℝ (fun y : E => (y, (u0, s 0))) x₀ := hι.differentiableAt
      rw [← fderiv_comp (x := x₀) h1 h2]
      rfl
    rw [hfc]
    rw [ContinuousLinearMap.comp_apply]
    have hιd : fderiv ℝ (fun y : E => (y, (u0, s 0))) x₀ xu = (xu, (0, 0)) := by
      have h := congrArg (fun L : E →L[ℝ] E × (E × E) => L xu) hι.fderiv
      change fderiv ℝ (fun y : E => (y, (u0, s 0))) x₀ xu = (xu, (0, 0)) at h
      exact h
    rw [hιd]
  have hs2slice : (fderiv ℝ H P) (0, xuu, 0) =
      fderiv ℝ (fun v : E => H (x₀, (v, s 0))) u0 xuu := by
    have hι : HasFDerivAt (fun v : E => (x₀, (v, s 0)))
        ((0 : E →L[ℝ] E).prod ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E))) u0 := by
      have h1 : HasFDerivAt (fun _ : E => x₀) (0 : E →L[ℝ] E) u0 :=
        hasFDerivAt_const (c := x₀) (x := u0)
      have h2 : HasFDerivAt (fun v : E => (v, s 0)) ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E)) u0 := by
        have h2a : HasFDerivAt (fun v : E => v) (ContinuousLinearMap.id ℝ E) u0 :=
          (ContinuousLinearMap.id ℝ E).hasFDerivAt
        have h2b : HasFDerivAt (fun _ : E => s 0) (0 : E →L[ℝ] E) u0 :=
          hasFDerivAt_const (c := s 0) (x := u0)
        exact h2a.prodMk h2b
      exact h1.prodMk h2
    have hfc : fderiv ℝ (fun v : E => H (x₀, (v, s 0))) u0 =
        (fderiv ℝ H P).comp (fderiv ℝ (fun v : E => (x₀, (v, s 0))) u0) := by
      have h1 : DifferentiableAt ℝ H P := hHd.differentiableAt
      have h2 : DifferentiableAt ℝ (fun v : E => (x₀, (v, s 0))) u0 := hι.differentiableAt
      rw [← fderiv_comp (x := u0) h1 h2]
      rfl
    rw [hfc]
    rw [ContinuousLinearMap.comp_apply]
    have hιd : fderiv ℝ (fun v : E => (x₀, (v, s 0))) u0 xuu = (0, (xuu, 0)) := by
      simpa using congrArg (fun L : E →L[ℝ] E × (E × E) => L xuu) hι.fderiv
    rw [hιd]
  have hs2 : (fderiv ℝ H P) (0, xuu, 0) =
      chartChristoffelContraction (I := I) g p xuu (s 0) x₀ := by
    rw [hs2slice]
    have hlin : (fun v : E => H (x₀, (v, s 0))) =
        chartChristoffelContractionRightCLM (I := I) g p (s 0) x₀ := by
      funext v
      rw [hH]
      change chartChristoffelContraction (I := I) g p v (s 0) x₀ = _
      rw [chartChristoffelContractionRightCLM_apply]
      exact (chartChristoffelContraction_symm (I := I) g p v (s 0) x₀)
    rw [hlin]
    have hld : fderiv ℝ (chartChristoffelContractionRightCLM (I := I) g p (s 0) x₀) u0 =
        chartChristoffelContractionRightCLM (I := I) g p (s 0) x₀ :=
      (chartChristoffelContractionRightCLM (I := I) g p (s 0) x₀).hasFDerivAt.fderiv
    rw [hld]
    rw [chartChristoffelContractionRightCLM_apply]
    exact (chartChristoffelContraction_symm (I := I) g p xuu (s 0) x₀).symm
  have hs3slice : (fderiv ℝ H P) (0, 0, su) =
      fderiv ℝ (fun w : E => H (x₀, (u0, w))) (s 0) su := by
    have hι : HasFDerivAt (fun w : E => (x₀, (u0, w)))
        ((0 : E →L[ℝ] E).prod ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E))) (s 0) := by
      have h1 : HasFDerivAt (fun _ : E => x₀) (0 : E →L[ℝ] E) (s 0) :=
        hasFDerivAt_const (c := x₀) (x := s 0)
      have h2 : HasFDerivAt (fun w : E => (u0, w)) ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) (s 0) := by
        have h2a : HasFDerivAt (fun _ : E => u0) (0 : E →L[ℝ] E) (s 0) :=
          hasFDerivAt_const (c := u0) (x := s 0)
        have h2b : HasFDerivAt (fun w : E => w) (ContinuousLinearMap.id ℝ E) (s 0) :=
          (ContinuousLinearMap.id ℝ E).hasFDerivAt
        exact h2a.prodMk h2b
      exact h1.prodMk h2
    have hfc : fderiv ℝ (fun w : E => H (x₀, (u0, w))) (s 0) =
        (fderiv ℝ H P).comp (fderiv ℝ (fun w : E => (x₀, (u0, w))) (s 0)) := by
      have h1 : DifferentiableAt ℝ H P := hHd.differentiableAt
      have h2 : DifferentiableAt ℝ (fun w : E => (x₀, (u0, w))) (s 0) := hι.differentiableAt
      rw [← fderiv_comp (x := s 0) h1 h2]
      rfl
    rw [hfc]
    rw [ContinuousLinearMap.comp_apply]
    have hιd : fderiv ℝ (fun w : E => (x₀, (u0, w))) (s 0) su = (0, (0, su)) := by
      simpa using congrArg (fun L : E →L[ℝ] E × (E × E) => L su) hι.fderiv
    rw [hιd]
  have hs3 : (fderiv ℝ H P) (0, 0, su) =
      chartChristoffelContraction (I := I) g p u0 su x₀ := by
    rw [hs3slice]
    have hlin : (fun w : E => H (x₀, (u0, w))) = chartChristoffelContractionRightCLM (I := I) g p u0 x₀ := by
      funext w
      rfl
    rw [hlin]
    have hld : fderiv ℝ (chartChristoffelContractionRightCLM (I := I) g p u0 x₀) (s 0) =
        chartChristoffelContractionRightCLM (I := I) g p u0 x₀ :=
      (chartChristoffelContractionRightCLM (I := I) g p u0 x₀).hasFDerivAt.fderiv
    rw [hld]
    rw [chartChristoffelContractionRightCLM_apply]
  have hsplit : (fderiv ℝ H P) (xu, (xuu, su)) =
      (fderiv ℝ H P) (xu, 0, 0) + (fderiv ℝ H P) (0, xuu, 0) +
        (fderiv ℝ H P) (0, 0, su) := by
    have hsum : (xu, (xuu, su)) = (xu, (0, 0)) + (0, (xuu, 0)) + (0, (0, su)) := by
      simp
    rw [hsum]
    rw [map_add, map_add]
  rw [hsplit, hs1, hs2, hs3]

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
private lemma radialTransportSection_chartE_contDiffOn2 (g : SmoothRiemannianMetric I M) (p : M)
    (η₀ : TangentSpace I p)
    (hη : ContMDiffAt I I.tangent (∞ : WithTop ℕ∞)
      (T% (radialTransportSection (I := I) g p η₀)) p) :
    ∃ U : Set E, U ∈ 𝓝 (extChartAt I p p) ∧
      ContDiffOn ℝ 2
        (chartESectionRepr (I := I) p (radialTransportSection (I := I) g p η₀) ∘
          (extChartAt I p).symm) U := by
  classical
  set σ : Π y : M, TangentSpace I y := radialTransportSection (I := I) g p η₀ with hσ
  have hη2 : ContMDiffAt I I.tangent 2 (T% σ) p := by
    simpa [hσ] using (hη.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))
  have hsrc : p ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H p
  have hchart2 : ContMDiffAt I 𝓘(ℝ, E) 2 (chartESectionRepr (I := I) p σ) p :=
    (contMDiffAt_section_iff_chartE I p σ hsrc).mp hη2
  have hsymmAt : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I p).symm (extChartAt I p p) := by
    have hsrc' : (extChartAt I p p) ∈ (extChartAt I p).target :=
      (extChartAt I p).map_source (by rw [extChartAt_source]; exact mem_chart_source H p)
    have htarget_nhd : (extChartAt I p).target ∈ 𝓝 (extChartAt I p p) :=
      (OpenPartialHomeomorph.isOpen_extend_target (I := I) (f := chartAt H p)).mem_nhds hsrc'
    exact (contMDiffOn_extChartAt_symm (I := I) (n := 2) (x := p)).contMDiffAt htarget_nhd
  have hchart2' : ContMDiffAt I 𝓘(ℝ, E) 2 (chartESectionRepr (I := I) p σ)
      ((extChartAt I p).symm ((extChartAt I p) p)) := by
    simpa [extChartAt_to_inv] using hchart2
  have hcomp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 2
      (chartESectionRepr (I := I) p σ ∘ (extChartAt I p).symm) (extChartAt I p p) :=
    hchart2'.comp (extChartAt I p p) hsymmAt
  have hcdAt : ContDiffAt ℝ 2
      (chartESectionRepr (I := I) p σ ∘ (extChartAt I p).symm) (extChartAt I p p) :=
    (contMDiffAt_iff_contDiffAt.mp hcomp)
  obtain ⟨U, hU, hcdOn⟩ := hcdAt.contDiffOn le_rfl (by simp)
  exact ⟨U, hU, hcdOn⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [T2Space M] in
private lemma deriv_clm_apply_u_zero {L : ℝ → E →L[ℝ] E} {u : ℝ → E} {u' : E}
    (hL : DifferentiableAt ℝ L 0) (hu : HasDerivAt u u' 0) (hu0 : u 0 = 0) :
    deriv (fun t : ℝ => (L t) (u t)) 0 = (L 0) u' := by
  have hLF : HasFDerivAt L (fderiv ℝ L 0) 0 := hL.hasFDerivAt
  have hcompF : HasFDerivAt (fun t : ℝ => (L t) (u t))
      ((L 0).comp (ContinuousLinearMap.toSpanSingleton ℝ u') + (fderiv ℝ L 0).flip (u 0)) 0 :=
    hLF.clm_apply hu.hasFDerivAt
  have hcomp : HasDerivAt (fun t : ℝ => (L t) (u t))
      (((L 0).comp (ContinuousLinearMap.toSpanSingleton ℝ u') + (fderiv ℝ L 0).flip (u 0)) 1) 0 :=
    hcompF.hasDerivAt
  rw [hcomp.deriv]
  rw [hu0]
  simp

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [T2Space M] in
private lemma deriv_fderiv_apply_along {f : E → E} {x : ℝ → E} {e xu : E} {x₀ : E}
    (hx₀ : x 0 = x₀) (hx : HasDerivAt x xu 0)
    (hf : DifferentiableAt ℝ (fun y : E => fderiv ℝ f y) x₀) :
    deriv (fun t : ℝ => fderiv ℝ f (x t) e) 0 =
      (fderiv ℝ (fun y : E => fderiv ℝ f y) x₀) xu e := by
  have hg : HasFDerivAt (fun y : E => fderiv ℝ f y e)
      ((fderiv ℝ (fun y : E => fderiv ℝ f y) x₀).flip e) x₀ := by
    have hc := hf.hasFDerivAt
    have hu : HasFDerivAt (fun _ : E => e) (0 : E →L[ℝ] E) x₀ :=
      hasFDerivAt_const (c := e) (x := x₀)
    simpa using hc.clm_apply hu
  have hg' : HasFDerivAt (fun y : E => fderiv ℝ f y e)
      ((fderiv ℝ (fun y : E => fderiv ℝ f y) x₀).flip e) (x 0) := by
    simpa [hx₀] using hg
  have hd := (hg'.comp 0 hx.hasFDerivAt).hasDerivAt
  have hfun : (fun t : ℝ => fderiv ℝ f (x t) e) =
      (fun y : E => fderiv ℝ f y e) ∘ x := by
    funext t
    rfl
  rw [hfun, hd.deriv]
  simp

omit [NeZero (Module.finrank ℝ E)] in
private lemma radialTransportSection_chartDirSecondDerivAlongRadial_zero
    (g : SmoothRiemannianMetric I M) (p : M) (η₀ : TangentSpace I p)
    {X : TangentSpace I p} (hX : ‖(X : E)‖ < radialRadius (I := I) g p)
    (hη : ContMDiffAt I I.tangent (∞ : WithTop ℕ∞)
      (T% (radialTransportSection (I := I) g p η₀)) p) :
    deriv (fun t : ℝ =>
      (fderiv ℝ (chartESectionRepr (I := I) p (radialTransportSection (I := I) g p η₀) ∘
          (extChartAt I p).symm) (chartCurve (I := I) p (fun s : ℝ => expMap (I := I) g p (s • X)) t))
        (X : E) +
      chartChristoffelContraction (I := I) g p (X : E)
        (chartESectionRepr (I := I) p (radialTransportSection (I := I) g p η₀)
          (expMap (I := I) g p (t • X)))
        (chartCurve (I := I) p (fun s : ℝ => expMap (I := I) g p (s • X)) t)) 0 = 0 := by
  classical
  set σ : Π y : M, TangentSpace I y := radialTransportSection (I := I) g p η₀ with hσ
  set γ : ℝ → M := fun s => expMap (I := I) g p (s • X) with hγ
  set f : E → E := chartESectionRepr (I := I) p σ ∘ (extChartAt I p).symm with hf
  set xcrv : ℝ → E := fun t => chartCurve (I := I) p γ t with hxcrv_def
  set sec : ℝ → E := fun t => f (xcrv t) with hsec_def
  set x₀ : E := xcrv 0 with hx₀_def
  set v : E := (X : E) with hv_def
  have hxcrv0 : xcrv 0 = x₀ := rfl
  have hγ0 : γ 0 = p := by
    rw [hγ]
    exact radialCurve_zero (I := I) g p X
  have hx₀_eq : x₀ = extChartAt I p p := by
    rw [hx₀_def, hxcrv_def]
    change chartCurve (I := I) p γ 0 = extChartAt I p p
    rw [chartCurve_def, hγ0]
  have hx₀_int : x₀ ∈ interior (extChartAt I p).target := by
    rw [hx₀_eq]
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) p
      ((extChartAt I p).map_source (by rw [extChartAt_source]; exact mem_chart_source H p))
  have hxcd : ContDiffOn ℝ 2 xcrv {s : ℝ | ‖s • (X : E)‖ < expMapC2Radius (I := I) g p} := by
    rw [hxcrv_def, hγ]
    exact radialCurve_chartCurve_contDiffOn (I := I) g p (v := X)
  have hdom_nhd : {s : ℝ | ‖s • (X : E)‖ < expMapC2Radius (I := I) g p} ∈ 𝓝 0 := by
    have h0 : ‖(0 : ℝ) • (X : E)‖ < expMapC2Radius (I := I) g p := by
      rw [zero_smul, norm_zero]
      exact expMapC2Radius_pos (I := I) g p
    exact (radialCurve_domain_isOpen (I := I) g p X).mem_nhds h0
  have hxcdAt : ContDiffAt ℝ 2 xcrv 0 := hxcd.contDiffAt hdom_nhd
  have hx' : HasDerivAt xcrv v 0 := by
    have hd : deriv xcrv 0 = v := by
      rw [hxcrv_def, hγ, hv_def]
      exact radialCurve_chartCurve_deriv_zero (I := I) g p X
    have hdx : HasDerivAt xcrv (deriv xcrv 0) 0 :=
      (hxcdAt.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).hasDerivAt
    simpa [hd] using hdx
  have hησ : ContMDiffAt I I.tangent (∞ : WithTop ℕ∞) (T% σ) p := by
    simpa [hσ] using hη
  obtain ⟨U, hU, hfcd⟩ := radialTransportSection_chartE_contDiffOn2 (I := I) g p η₀ hη
  obtain ⟨V, hVU, hV_open, hx₀V⟩ := _root_.mem_nhds_iff.mp hU
  have hfcdV : ContDiffOn ℝ 2 f V := hfcd.mono hVU
  have hfdV : ContDiffOn ℝ 1 (fderiv ℝ f) V :=
    ContDiffOn.fderiv_of_isOpen hfcdV hV_open (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
  have hx₀V' : x₀ ∈ V := by simpa [hx₀_eq] using hx₀V
  have hfdAt : DifferentiableAt ℝ (fun y : E => fderiv ℝ f y) x₀ :=
    (hfdV.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0) x₀ hx₀V').differentiableAt
      (hV_open.mem_nhds hx₀V')
  have hx'' : HasDerivAt (deriv xcrv) (deriv (deriv xcrv) 0) 0 := by
    obtain ⟨xd, ⟨u, hu, hfd⟩, hxd_cd⟩ :=
      (contDiffAt_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 1)).mp hxcdAt
    have hxd_cd1 : ContDiffAt ℝ 1 (fun t : ℝ => (xd t) (1 : ℝ)) 0 :=
      hxd_cd.clm_apply (contDiffAt_const (c := (1 : ℝ)) (x := 0))
    have hderiv_eq : (deriv xcrv) =ᶠ[𝓝 0] (fun t : ℝ => (xd t) (1 : ℝ)) := by
      filter_upwards [hu] with t ht
      have hfdAt_t := hfd t ht
      have hfdr : fderiv ℝ xcrv t = xd t := hfdAt_t.fderiv
      rw [show deriv xcrv t = (fderiv ℝ xcrv t) (1 : ℝ) from rfl]
      rw [hfdr]
    have hderiv_cd : ContDiffAt ℝ 1 (deriv xcrv) 0 :=
      hxd_cd1.congr_of_eventuallyEq hderiv_eq
    exact (hderiv_cd.differentiableAt_one).hasDerivAt
  have hsrc_γ : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, γ t ∈ (extChartAt I p).source := by
    intro t ht
    rw [hγ, extChartAt_source]
    simpa using (radialCurve_mem_chartAt_source_of_lt_radialRadius (I := I) g p hX
      ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hODE : ∀ᶠ t in 𝓝 0,
      HasDerivAt sec (- chartChristoffelContraction (I := I) g p (deriv xcrv t) (sec t) (xcrv t)) t := by
    have h0 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    filter_upwards [isOpen_Ioo.mem_nhds h0] with t ht
    have hODE_t := radialTransportSection_chartRep_hasDerivAt (I := I) g p hX η₀ ht
    have hfun : (fun u : ℝ => chartESectionRepr (I := I) p σ (expMap (I := I) g p (u • X))) =ᶠ[𝓝 t]
        sec := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
      rw [hsec_def]
      rw [hf]
      congr 1
      rw [hxcrv_def]
      change expMap (I := I) g p (u • X) = (extChartAt I p).symm (chartCurve (I := I) p γ u)
      rw [chartCurve_def]
      rw [(extChartAt I p).left_inv (hsrc_γ u hu)]
    have hval : chartESectionRepr (I := I) p σ (expMap (I := I) g p (t • X)) = sec t :=
      hfun.eq_of_nhds
    have hODE_t' : HasDerivAt sec
        (- chartChristoffelContraction (I := I) g p (deriv (chartCurve (I := I) p γ) t)
          (sec t) (chartCurve (I := I) p γ t)) t := by
      have h1 : HasDerivAt sec
          (- chartChristoffelContraction (I := I) g p (deriv (chartCurve (I := I) p γ) t)
            (chartESectionRepr (I := I) p σ (expMap (I := I) g p (t • X)))
            (chartCurve (I := I) p γ t)) t :=
        hODE_t.congr_of_eventuallyEq hfun.symm
      rw [hval] at h1
      exact h1
    rw [hxcrv_def]
    exact hODE_t'
  have hODE_at0 : HasDerivAt sec (- chartChristoffelContraction (I := I) g p v (sec 0) x₀) 0 := by
    have h' := hODE.self_of_nhds
    rw [hx'.deriv] at h'
    simpa [hx₀_def] using h'
  have hs' : deriv sec 0 = - chartChristoffelContraction (I := I) g p v (sec 0) x₀ := hODE_at0.deriv
  have hODE_at0' : HasDerivAt sec (deriv sec 0) 0 := by
    rw [hs']
    exact hODE_at0
  have hL : DifferentiableAt ℝ (fun t : ℝ => fderiv ℝ f (xcrv t)) 0 := by
    have h1 : DifferentiableAt ℝ (fun y : E => fderiv ℝ f y) x₀ := hfdAt
    have h2 : DifferentiableAt ℝ xcrv 0 := hx'.differentiableAt
    have h := h1.comp 0 h2
    change DifferentiableAt ℝ (fun t : ℝ => fderiv ℝ f (xcrv t)) 0 at h
    exact h
  have hAv : DifferentiableAt ℝ (fun t : ℝ => fderiv ℝ f (xcrv t) v) 0 :=
    (hL.clm_apply (differentiableAt_const (x := 0) (c := v)))
  have hA' : deriv (fun t : ℝ => fderiv ℝ f (xcrv t) v) 0 =
      (fderiv ℝ (fun y : E => fderiv ℝ f y) x₀) v v := by
    exact deriv_fderiv_apply_along (f := f) (x := xcrv) (e := v) (xu := v)
      (by rfl) hx' hfdAt
  have hB' : deriv (fun t : ℝ => chartChristoffelContraction (I := I) g p v (sec t) (xcrv t)) 0 =
      (fderiv ℝ (fun y : E => chartChristoffelContraction (I := I) g p v (sec 0) y) x₀) v +
        chartChristoffelContraction (I := I) g p v (deriv sec 0) x₀ := by
    exact deriv_chartContraction_constArg_along (I := I) g p (x := xcrv) (s := sec) (e := v)
      (xu := v) (su := deriv sec 0) hx₀_int (by rfl) hx' hODE_at0'
  let u : ℝ → E := fun t => deriv xcrv t - v
  have hu0 : u 0 = 0 := by
    unfold u
    rw [hx'.deriv]
    simp
  have hu' : HasDerivAt u (deriv (deriv xcrv) 0) 0 := by
    have hsub : HasDerivAt (deriv xcrv - fun _ : ℝ => v) (deriv (deriv xcrv) 0) 0 := by
      simpa [sub_zero] using (hx''.sub (hasDerivAt_const (x := 0) (c := v)))
    exact hsub
  have hM' : deriv (fun t : ℝ => fderiv ℝ f (xcrv t) (u t)) 0 =
      (fderiv ℝ f x₀) (deriv (deriv xcrv) 0) := by
    simpa [u] using deriv_clm_apply_u_zero (L := fun t : ℝ => fderiv ℝ f (xcrv t))
      (u := u) (u' := deriv (deriv xcrv) 0) hL hu' hu0
  have hL' : deriv (fun t : ℝ => chartChristoffelContraction (I := I) g p (u t) (sec t) (xcrv t)) 0 =
      chartChristoffelContraction (I := I) g p (deriv (deriv xcrv) 0) (sec 0) x₀ := by
    have hC := deriv_chartContraction_full_along (I := I) g p (x := xcrv) (u := u) (s := sec)
      (u0 := 0) (xu := v) (xuu := deriv (deriv xcrv) 0) (su := deriv sec 0)
      hx₀_int (by rfl) hu0 hx' hu' hODE_at0'
    have h1 : (fderiv ℝ (fun y : E => chartChristoffelContraction (I := I) g p 0 (sec 0) y) x₀) 0 = 0 := by
      have hfun : (fun y : E => chartChristoffelContraction (I := I) g p 0 (sec 0) y) =
          fun _ : E => (0 : E) := by
        funext y
        rw [chartChristoffelContraction_zero_left]
      rw [hfun]
      simp
    have h3 : chartChristoffelContraction (I := I) g p 0 (deriv sec 0) x₀ = 0 :=
      chartChristoffelContraction_zero_left (I := I) g p (deriv sec 0) x₀
    simpa [h1, h3] using hC
  have hBd : DifferentiableAt ℝ (fun t : ℝ => chartChristoffelContraction (I := I) g p v (sec t) (xcrv t)) 0 := by
    have hcd : ContDiffOn ℝ 1 (fun z : E × E => chartChristoffelContraction (I := I) g p v z.2 z.1)
        ((interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :=
      chartChristoffelContraction_constArg_contDiffOn (I := I) g p v
    have hmem : (x₀, sec 0) ∈ (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) :=
      ⟨hx₀_int, Set.mem_univ _⟩
    have hopen : IsOpen ((interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :=
      isOpen_interior.prod isOpen_univ
    have hdOn : DifferentiableOn ℝ (fun z : E × E => chartChristoffelContraction (I := I) g p v z.2 z.1)
        ((interior (extChartAt I p).target) ×ˢ (Set.univ : Set E)) :=
      hcd.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    have hHd : DifferentiableAt ℝ (fun z : E × E => chartChristoffelContraction (I := I) g p v z.2 z.1)
        (xcrv 0, sec 0) := by
      rw [hxcrv0]
      exact (hdOn (x₀, sec 0) hmem).differentiableAt (hopen.mem_nhds hmem)
    have hxy : DifferentiableAt ℝ (fun t : ℝ => (xcrv t, sec t)) 0 :=
      (hx'.differentiableAt.prodMk (hODE_at0.differentiableAt))
    have hc := hHd.comp 0 hxy
    change DifferentiableAt ℝ
      (fun t : ℝ => chartChristoffelContraction (I := I) g p v (sec t) (xcrv t)) 0 at hc
    exact hc
  have hLd : DifferentiableAt ℝ (fun t : ℝ => chartChristoffelContraction (I := I) g p (u t) (sec t) (xcrv t)) 0 := by
    have hcd : ContDiffOn ℝ 1
        (fun z : E × E × E => chartChristoffelContraction (I := I) g p z.2.1 z.2.2 z.1)
        ((interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) :=
      chartChristoffelContraction_full_contDiffOn (I := I) g p
    have hmem : (x₀, (0, sec 0)) ∈
        (interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E) :=
      ⟨hx₀_int, Set.mem_univ _, Set.mem_univ _⟩
    have hopen : IsOpen
        ((interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) :=
      isOpen_interior.prod (isOpen_univ.prod isOpen_univ)
    have hdOn : DifferentiableOn ℝ
        (fun z : E × E × E => chartChristoffelContraction (I := I) g p z.2.1 z.2.2 z.1)
        ((interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) :=
      hcd.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    have hHd : DifferentiableAt ℝ
        (fun z : E × E × E => chartChristoffelContraction (I := I) g p z.2.1 z.2.2 z.1)
        (xcrv 0, (u 0, sec 0)) := by
      rw [hxcrv0, hu0]
      exact (hdOn (x₀, (0, sec 0)) hmem).differentiableAt (hopen.mem_nhds hmem)
    have hxyu : DifferentiableAt ℝ (fun t : ℝ => (xcrv t, (u t, sec t))) 0 :=
      (hx'.differentiableAt.prodMk (hu'.differentiableAt.prodMk (hODE_at0.differentiableAt)))
    have hc := hHd.comp 0 hxyu
    change DifferentiableAt ℝ
      (fun t : ℝ => chartChristoffelContraction (I := I) g p (u t) (sec t) (xcrv t)) 0 at hc
    exact hc
  have hCsplit : deriv (fun t : ℝ => chartChristoffelContraction (I := I) g p (deriv xcrv t) (sec t) (xcrv t)) 0 =
      deriv (fun t : ℝ => chartChristoffelContraction (I := I) g p v (sec t) (xcrv t)) 0 +
        deriv (fun t : ℝ => chartChristoffelContraction (I := I) g p (u t) (sec t) (xcrv t)) 0 := by
    have hfun : (fun t : ℝ => chartChristoffelContraction (I := I) g p (deriv xcrv t) (sec t) (xcrv t)) =
        (fun t : ℝ => chartChristoffelContraction (I := I) g p v (sec t) (xcrv t)) +
          (fun t : ℝ => chartChristoffelContraction (I := I) g p (u t) (sec t) (xcrv t)) := by
      funext t
      unfold u
      change chartChristoffelContraction (I := I) g p (deriv xcrv t) (sec t) (xcrv t) =
        chartChristoffelContraction (I := I) g p v (sec t) (xcrv t) +
          chartChristoffelContraction (I := I) g p (deriv xcrv t - v) (sec t) (xcrv t)
      rw [show chartChristoffelContraction (I := I) g p (deriv xcrv t) (sec t) (xcrv t) =
        chartChristoffelContraction (I := I) g p (v + (deriv xcrv t - v)) (sec t) (xcrv t) from by
          congr 1
          abel]
      rw [ChartChristoffel.contraction_add_left (I := I) (v₁ := v) (v₂ := deriv xcrv t - v) (w := sec t)]
    rw [hfun]
    exact deriv_add hBd hLd
  have hDsplit : deriv (fun t : ℝ => fderiv ℝ f (xcrv t) (deriv xcrv t)) 0 =
      deriv (fun t : ℝ => fderiv ℝ f (xcrv t) v) 0 +
        deriv (fun t : ℝ => fderiv ℝ f (xcrv t) (u t)) 0 := by
    have hfun : (fun t : ℝ => fderiv ℝ f (xcrv t) (deriv xcrv t)) =
        (fun t : ℝ => fderiv ℝ f (xcrv t) v) + (fun t : ℝ => fderiv ℝ f (xcrv t) (u t)) := by
      funext t
      unfold u
      change (fderiv ℝ f (xcrv t)) (deriv xcrv t) =
        (fderiv ℝ f (xcrv t)) v + (fderiv ℝ f (xcrv t)) (deriv xcrv t - v)
      rw [map_sub]
      abel
    rw [hfun]
    exact deriv_add hAv (hL.clm_apply hu'.differentiableAt)
  have hD : deriv (deriv sec) 0 = deriv (fun t : ℝ => fderiv ℝ f (xcrv t) (deriv xcrv t)) 0 := by
    have hx_in_V_nhd : {t : ℝ | xcrv t ∈ V} ∈ 𝓝 0 := by
      have hcont : ContinuousAt xcrv 0 := hx'.continuousAt
      exact hcont.preimage_mem_nhds (hV_open.mem_nhds hx₀V')
    have h1 : (fun t : ℝ => deriv sec t) =ᶠ[𝓝 0] (fun t : ℝ => fderiv ℝ f (xcrv t) (deriv xcrv t)) := by
      have h0 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
      filter_upwards [isOpen_Ioo.mem_nhds h0, hx_in_V_nhd] with t ht hxtV
      have hderiv_comp : deriv (f ∘ xcrv) t = fderiv ℝ f (xcrv t) (deriv xcrv t) := by
        have hxd : DifferentiableAt ℝ xcrv t := by
          have hs : ‖t • (X : E)‖ < expMapC2Radius (I := I) g p :=
            norm_smul_lt_expMapC2Radius_of_lt_radialRadius (I := I) g p hX
              ⟨by linarith [ht.1], by linarith [ht.2]⟩
          have hdom_t : {s : ℝ | ‖s • (X : E)‖ < expMapC2Radius (I := I) g p} ∈ 𝓝 t :=
            (radialCurve_domain_isOpen (I := I) g p X).mem_nhds hs
          have hx2 : ContDiffAt ℝ 2 xcrv t := hxcd.contDiffAt hdom_t
          exact (hx2.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0))
        have hfd_t : DifferentiableAt ℝ f (xcrv t) :=
          (hfcdV.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0) (xcrv t) hxtV).differentiableAt
            (hV_open.mem_nhds hxtV)
        have hfdF : HasFDerivAt f (fderiv ℝ f (xcrv t)) (xcrv t) := hfd_t.hasFDerivAt
        have hcomp : HasDerivAt (f ∘ xcrv) ((fderiv ℝ f (xcrv t)) (deriv xcrv t)) t := by
          simpa using (hfdF.comp_hasDerivAt t hxd.hasDerivAt)
        exact hcomp.deriv
      have hs_eq : deriv sec t = deriv (f ∘ xcrv) t := by
        rw [hsec_def]
        congr 1
      rw [hs_eq, hderiv_comp]
    exact (h1.deriv_eq)
  have hDneg : deriv (deriv sec) 0 = - deriv (fun t : ℝ => chartChristoffelContraction (I := I) g p (deriv xcrv t) (sec t) (xcrv t)) 0 := by
    have h1 : (fun t : ℝ => deriv sec t) =ᶠ[𝓝 0]
        (fun t : ℝ => - chartChristoffelContraction (I := I) g p (deriv xcrv t) (sec t) (xcrv t)) := by
      filter_upwards [hODE] with t ht
      exact ht.deriv
    have h2 : deriv (deriv sec) 0 = deriv (fun t : ℝ =>
        - chartChristoffelContraction (I := I) g p (deriv xcrv t) (sec t) (xcrv t)) 0 := h1.deriv_eq
    rw [h2]
    rw [show (fun t : ℝ => - chartChristoffelContraction (I := I) g p (deriv xcrv t) (sec t) (xcrv t)) =
        (- fun t : ℝ => chartChristoffelContraction (I := I) g p (deriv xcrv t) (sec t) (xcrv t)) from rfl]
    exact deriv.neg
  have hT : deriv (fun t : ℝ =>
      fderiv ℝ f (xcrv t) v +
        chartChristoffelContraction (I := I) g p v (sec t) (xcrv t)) 0 =
      deriv (fun t : ℝ => fderiv ℝ f (xcrv t) v) 0 +
        deriv (fun t : ℝ => chartChristoffelContraction (I := I) g p v (sec t) (xcrv t)) 0 := by
    have hfun : (fun t : ℝ => fderiv ℝ f (xcrv t) v +
          chartChristoffelContraction (I := I) g p v (sec t) (xcrv t)) =
        (fun t : ℝ => fderiv ℝ f (xcrv t) v) + (fun t : ℝ => chartChristoffelContraction (I := I) g p v (sec t) (xcrv t)) := by
      funext t
      rfl
    rw [hfun]
    exact deriv_add hAv hBd
  have hfirst : fderiv ℝ f x₀ (deriv (deriv xcrv) 0) +
      chartChristoffelContraction (I := I) g p (deriv (deriv xcrv) 0) (sec 0) x₀ = 0 := by
    have hfo := radialTransportSection_chartE_firstOrder (I := I) g p η₀ (hησ.mdifferentiableAt (by decide))
      (v := deriv (deriv xcrv) 0)
    have hs0_eq : sec 0 = chartESectionRepr (I := I) p σ p := by
      rw [hsec_def]
      change f (xcrv 0) = chartESectionRepr (I := I) p σ p
      rw [hf]
      rw [hxcrv0, hx₀_eq]
      change chartESectionRepr (I := I) p σ ((extChartAt I p).symm ((extChartAt I p) p)) =
        chartESectionRepr (I := I) p σ p
      rw [(extChartAt I p).left_inv (by rw [extChartAt_source]; exact mem_chart_source H p)]
    rw [hf]
    simpa [hx₀_eq, hs0_eq, hσ] using hfo
  have hML : deriv (fun t : ℝ => fderiv ℝ f (xcrv t) (u t)) 0 +
      deriv (fun t : ℝ => chartChristoffelContraction (I := I) g p (u t) (sec t) (xcrv t)) 0 = 0 := by
    rw [hM', hL']
    exact hfirst
  have hfinal : deriv (fun t : ℝ =>
      fderiv ℝ f (xcrv t) v +
        chartChristoffelContraction (I := I) g p v (sec t) (xcrv t)) 0 = 0 := by
    have hA : deriv (fun t : ℝ => fderiv ℝ f (xcrv t) v) 0 +
        deriv (fun t : ℝ => fderiv ℝ f (xcrv t) (u t)) 0 = - (deriv (fun t : ℝ => chartChristoffelContraction (I := I) g p v (sec t) (xcrv t)) 0 +
          deriv (fun t : ℝ => chartChristoffelContraction (I := I) g p (u t) (sec t) (xcrv t)) 0) := by
      rw [← hDsplit]
      rw [← hD]
      rw [hDneg]
      rw [hCsplit]
    have hML' : deriv (fun t : ℝ => fderiv ℝ f (xcrv t) (u t)) 0 +
        deriv (fun t : ℝ => chartChristoffelContraction (I := I) g p (u t) (sec t) (xcrv t)) 0 = 0 := hML
    have hsum0 : deriv (fun t : ℝ => fderiv ℝ f (xcrv t) v) 0 +
        deriv (fun t : ℝ => fderiv ℝ f (xcrv t) (u t)) 0 +
        deriv (fun t : ℝ => chartChristoffelContraction (I := I) g p v (sec t) (xcrv t)) 0 +
        deriv (fun t : ℝ => chartChristoffelContraction (I := I) g p (u t) (sec t) (xcrv t)) 0 = 0 := by
      rw [hA]
      abel
    have h1 : (deriv (fun t : ℝ => fderiv ℝ f (xcrv t) v) 0 +
        deriv (fun t : ℝ => chartChristoffelContraction (I := I) g p v (sec t) (xcrv t)) 0) +
        (deriv (fun t : ℝ => fderiv ℝ f (xcrv t) (u t)) 0 +
          deriv (fun t : ℝ => chartChristoffelContraction (I := I) g p (u t) (sec t) (xcrv t)) 0) = 0 := by
      rw [← hsum0]
      ac_rfl
    have h2 : (deriv (fun t : ℝ => fderiv ℝ f (xcrv t) v) 0 +
        deriv (fun t : ℝ => chartChristoffelContraction (I := I) g p v (sec t) (xcrv t)) 0) + 0 = 0 := by
      rwa [hML'] at h1
    have hA'B' : deriv (fun t : ℝ => fderiv ℝ f (xcrv t) v) 0 +
        deriv (fun t : ℝ => chartChristoffelContraction (I := I) g p v (sec t) (xcrv t)) 0 = 0 := by
      exact (add_zero _).symm.trans h2
    rwa [hT]
  have hfun_eq : (fun t : ℝ =>
      (fderiv ℝ (chartESectionRepr (I := I) p σ ∘ (extChartAt I p).symm) (chartCurve (I := I) p γ t))
        (X : E) +
      chartChristoffelContraction (I := I) g p (X : E)
        (chartESectionRepr (I := I) p σ (expMap (I := I) g p (t • X)))
        (chartCurve (I := I) p γ t)) =ᶠ[𝓝 0]
      (fun t : ℝ => fderiv ℝ f (xcrv t) v + chartChristoffelContraction (I := I) g p v (sec t) (xcrv t)) := by
    have h0 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    filter_upwards [isOpen_Ioo.mem_nhds h0] with t ht
    have hsec_eq : chartESectionRepr (I := I) p σ (expMap (I := I) g p (t • X)) = sec t := by
      rw [hsec_def]
      rw [hf]
      congr 1
      rw [hxcrv_def]
      change expMap (I := I) g p (t • X) = (extChartAt I p).symm (chartCurve (I := I) p γ t)
      rw [chartCurve_def]
      rw [(extChartAt I p).left_inv (hsrc_γ t ht)]
    rw [← hf, ← hv_def, hsec_eq]
  have hderiv_eq : deriv (fun t : ℝ =>
      (fderiv ℝ (chartESectionRepr (I := I) p σ ∘ (extChartAt I p).symm) (chartCurve (I := I) p γ t))
        (X : E) +
      chartChristoffelContraction (I := I) g p (X : E)
        (chartESectionRepr (I := I) p σ (expMap (I := I) g p (t • X)))
        (chartCurve (I := I) p γ t)) 0 =
      deriv (fun t : ℝ => fderiv ℝ f (xcrv t) v + chartChristoffelContraction (I := I) g p v (sec t) (xcrv t)) 0 :=
    hfun_eq.deriv_eq
  rwa [hderiv_eq]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
private lemma chartE_covDerivAt (g : SmoothRiemannianMetric I M) (p : M)
    {σ : Π x : M, TangentSpace I x} {y : M}
    (hy : y ∈ chartLeviCivitaGoodSet (I := I) p)
    (hσ : MDiffAt (T% σ) y) (v : TangentSpace I y) :
    trivToE (I := I) p y ((LeviCivita (I := I) g).toFun σ y v) =
      fderiv ℝ (chartESectionRepr (I := I) p σ ∘ (extChartAt I p).symm)
          (extChartAt I p y) (trivToE (I := I) p y v) +
        chartChristoffelContraction (I := I) g p (trivToE (I := I) p y v)
          (chartESectionRepr (I := I) p σ y) (extChartAt I p y) := by
  classical
  have h1 := LeviCivita_chart_apply (I := I) g p hy hσ v
  have h2 := chartLeviCivita_apply (I := I) g p σ hy v
  have hc := correction_eq_contr (I := I) g p y (chartESectionRepr (I := I) p σ y) v
  rw [h1, h2]
  rw [hc]
  rw [trivToE_trivFromE (I := I) p (chartLeviCivitaGoodSet_mem_baseSet (I := I) hy)]

omit [NeZero (Module.finrank ℝ E)] in
theorem radialTransportSection_nabla2_center_zero
    (g : SmoothRiemannianMetric I M) (p : M) (η₀ w : TangentSpace I p)
    (hη : ContMDiffAt I I.tangent (∞ : WithTop ℕ∞)
      (T% (radialTransportSection (I := I) g p η₀)) p) :
    (LeviCivita (I := I) g).toFun
      (fun y : M => (LeviCivita (I := I) g).toFun (radialTransportSection (I := I) g p η₀) y
        (coordExtensionTangent (I := I) p w y)) p w = 0 := by
  classical
  set σ : Π y : M, TangentSpace I y := radialTransportSection (I := I) g p η₀ with hσ
  set W' : Π y : M, TangentSpace I y := fun y =>
    (LeviCivita (I := I) g).toFun σ y (coordExtensionTangent (I := I) p w y) with hW'
  set v₀ : E := tangentCoord (I := I) p w with hv₀
  set c : ℝ := radialRadius (I := I) g p / (2 * (‖(w : E)‖ + 1)) with hc_def
  set X : TangentSpace I p := c • w with hX_def
  set γ : ℝ → M := fun s => expMap (I := I) g p (s • X) with hγ
  set f : E → E := chartESectionRepr (I := I) p σ ∘ (extChartAt I p).symm with hf
  set N : ℝ → E := fun t =>
    (fderiv ℝ f (chartCurve (I := I) p γ t)) v₀ +
      chartChristoffelContraction (I := I) g p v₀ (f (chartCurve (I := I) p γ t))
        (chartCurve (I := I) p γ t) with hN_def
  have hwE : (w : E) = v₀ := by
    rw [hv₀, tangentCoord]
    exact (trivToE_self_eq (I := I) p w).symm
  have hc_pos : 0 < c := by
    unfold c
    exact div_pos (radialRadius_pos (I := I) g p) (by positivity)
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hXE : (X : E) = c • v₀ := by
    rw [← trivToE_self_eq (I := I) p X]
    rw [hX_def]
    rw [map_smul]
    rw [trivToE_self_eq (I := I) p w]
    rw [hwE]
  have hX_norm : ‖(X : E)‖ < radialRadius (I := I) g p := by
    rw [hX_def]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc_pos]
    have hden : (‖(w : E)‖ + 1 : ℝ) ≠ 0 := by positivity
    have hc1 : c * (‖(w : E)‖ + 1) = radialRadius (I := I) g p / 2 := by
      unfold c
      field_simp [hden]
    have hlt : c * ‖(w : E)‖ < radialRadius (I := I) g p / 2 := by
      rw [← hc1]
      exact mul_lt_mul_of_pos_left (by linarith) hc_pos
    have hrad_pos : 0 < radialRadius (I := I) g p := radialRadius_pos (I := I) g p
    linarith
  have hγ0 : γ 0 = p := by simpa [hγ] using (radialCurve_zero (I := I) g p X)
  have hγvel : mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) = X := by
    rw [hγ]
    exact radialCurve_velocity (I := I) g p X
  have hγ2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ 0 := by
    rw [hγ]
    have h0 : ‖(0 : ℝ) • (X : E)‖ < expMapC2Radius (I := I) g p := by
      rw [zero_smul, norm_zero]
      exact expMapC2Radius_pos (I := I) g p
    exact radialCurve_contMDiffAt2 (I := I) g p (X : E) 0 h0
  have hvelE : deriv (chartCurve (I := I) p γ) 0 = (X : E) :=
    radialCurve_chartCurve_deriv_zero (I := I) g p X
  have hvelE' : deriv (chartCurve (I := I) p γ) 0 = c • v₀ := by
    rw [hvelE, hXE]
  have hx₀ : chartCurve (I := I) p γ 0 = extChartAt I p p := by
    rw [chartCurve_def, hγ0]
  have hσmd : MDiffAt (T% σ) p := by
    simpa [hσ] using (hη.mdifferentiableAt (by decide))
  have hησ : ContMDiffAt I I.tangent (∞ : WithTop ℕ∞) (T% σ) p := by
    simpa [hσ] using hη
  have hσ_at2 : ContMDiffAt I I.tangent (2 : WithTop ℕ∞) (T% σ) p :=
    hησ.of_le (by exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
  obtain ⟨u, hu, hσu2⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (by norm_num : (2 : WithTop ℕ∞) ≠ ∞)).mp hσ_at2
  obtain ⟨u₀, hu₀u, hu₀_open, hp₀⟩ := _root_.mem_nhds_iff.mp hu
  let e := trivializationAt E (TangentSpace I) p
  have hpe : p ∈ e.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H p
  let V : Set M := u₀ ∩ e.baseSet
  have hV_open : IsOpen V := hu₀_open.inter e.open_baseSet
  have hpV : p ∈ V := ⟨hp₀, hpe⟩
  have hσV : ContMDiffOn I I.tangent (2 : WithTop ℕ∞) (T% σ) V :=
    hσu2.mono (fun y hy => hu₀u hy.1)
  have hmdW' : MDiffAt (T% W') p := by
    have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (leviCivitaConnectionOfMetric (I := I) g) (1 : WithTop ℕ∞) :=
      leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one (I := I) (M := M) g
    have hcovσ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, (leviCivitaConnectionOfMetric (I := I) g).toFun σ y⟩ :
          TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y))) V := by
      exact (hcov hV_open).contMDiff hσV
    have hDaV : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
        (T% (coordExtensionTangent (I := I) p w)) V := by
      have hbase : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
          (T% (coordExtensionTangent (I := I) p w)) e.baseSet :=
        (coordExtensionTangent_contMDiffOn (I := I) p w).of_le
          (by exact WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞)))
      exact hbase.mono (fun y hy => hy.2)
    have hW'V : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞) (T% W') V := by
      simpa [W', hW', LeviCivita] using (hcovσ.clm_bundle_apply hDaV)
    have hW'at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞) (T% W') p := by
      exact (hW'V p hpV).contMDiffAt (hV_open.mem_nhds hpV)
    exact hW'at.mdifferentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hsrcγ_nhd : γ ⁻¹' (extChartAt I p).source ∈ 𝓝 (0 : ℝ) := by
    have hcont : ContinuousAt γ 0 := hγ2.continuousAt
    have hmem : p ∈ (extChartAt I p).source := by
      rw [extChartAt_source]
      exact mem_chart_source H p
    have hsrc_open : IsOpen (extChartAt I p).source := by
      rw [extChartAt_source]
      exact (chartAt H p).open_source
    exact hcont.preimage_mem_nhds (by simpa [hγ0] using (hsrc_open.mem_nhds hmem))
  have hγu₀_nhd : γ ⁻¹' u₀ ∈ 𝓝 (0 : ℝ) := by
    have hcont : ContinuousAt γ 0 := hγ2.continuousAt
    exact hcont.preimage_mem_nhds (by simpa [hγ0] using (hu₀_open.mem_nhds hp₀))
  have hgood_nhd : γ ⁻¹' (chartLeviCivitaGoodSet (I := I) p) ∈ 𝓝 (0 : ℝ) := by
    have hcont : ContinuousAt γ 0 := hγ2.continuousAt
    exact hcont.preimage_mem_nhds
      (by simpa [hγ0] using
        ((chartLeviCivitaGoodSet_isOpen (I := I) p).mem_nhds (self_mem_chartLeviCivitaGoodSet (I := I) p)))
  have hsec_id : ∀ t : ℝ, t ∈ γ ⁻¹' (extChartAt I p).source →
      chartESectionRepr (I := I) p σ (γ t) = f (chartCurve (I := I) p γ t) := by
    intro t ht
    rw [hf]
    congr 1
    rw [chartCurve_def]
    exact ((extChartAt I p).left_inv ht).symm
  have hcore := radialTransportSection_chartDirSecondDerivAlongRadial_zero (I := I) g p η₀ hX_norm hη
  have hlinN : (fun t : ℝ =>
      (fderiv ℝ (chartESectionRepr (I := I) p (radialTransportSection (I := I) g p η₀) ∘
          (extChartAt I p).symm) (chartCurve (I := I) p (fun s : ℝ => expMap (I := I) g p (s • X)) t))
        (X : E) +
      chartChristoffelContraction (I := I) g p (X : E)
        (chartESectionRepr (I := I) p (radialTransportSection (I := I) g p η₀)
          (expMap (I := I) g p (t • X)))
        (chartCurve (I := I) p (fun s : ℝ => expMap (I := I) g p (s • X)) t)) =ᶠ[𝓝 (0 : ℝ)]
    (fun t : ℝ => c • N t) := by
    have h0 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    filter_upwards [isOpen_Ioo.mem_nhds h0, hsrcγ_nhd] with t ht ht_src
    rw [← hσ, ← hγ, ← hf]
    change (fderiv ℝ f (chartCurve (I := I) p γ t)) (X : E) +
        chartChristoffelContraction (I := I) g p (X : E)
          (chartESectionRepr (I := I) p σ (γ t)) (chartCurve (I := I) p γ t) =
      c • N t
    rw [hsec_id t ht_src]
    rw [hXE]
    rw [map_smul]
    rw [ChartChristoffel.contraction_smul_left c v₀ (f (chartCurve (I := I) p γ t))]
    rw [smul_add]
  have hNderiv0 : deriv N 0 = 0 := by
    have hcs : deriv (fun t : ℝ => c • N t) 0 = c • deriv N 0 := by
      change (fderiv ℝ (c • N) 0) (1 : ℝ) = c • (fderiv ℝ N 0) (1 : ℝ)
      rw [fderiv_const_smul_field (𝕜 := ℝ) (c := c) (f := N)]
      rfl
    have hc0 : c • deriv N 0 = 0 := by
      rw [← hcs]
      rw [hlinN.symm.deriv_eq]
      exact hcore
    exact (smul_eq_zero.mp hc0).resolve_left hc_ne
  have hrep_eq : chartRepAt (I := I) γ (fun s => W' (γ s)) 0 =ᶠ[𝓝 (0 : ℝ)] N := by
    have h0 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    filter_upwards [isOpen_Ioo.mem_nhds h0, hsrcγ_nhd, hγu₀_nhd, hgood_nhd] with s hs hs_src hs_u₀ hs_good
    rw [chartRepAt_apply]
    rw [hγ0]
    rw [hW']
    have hσy : MDiffAt (T% σ) (γ s) := by
      have hγsV : γ s ∈ V := ⟨hs_u₀,
        chartLeviCivitaGoodSet_mem_baseSet (I := I) hs_good⟩
      exact (hσV.contMDiffAt (hV_open.mem_nhds hγsV)).mdifferentiableAt (by norm_num)
    have hchart := chartE_covDerivAt (I := I) g p hs_good hσy
      (coordExtensionTangent (I := I) p w (γ s))
    rw [hchart]
    have hdir : trivToE (I := I) p (γ s)
        (coordExtensionTangent (I := I) p w (γ s)) = v₀ := by
      simpa [hv₀] using chartE_section_repr_coordExtensionTangent_eq
        (I := I) p w (chartLeviCivitaGoodSet_mem_baseSet (I := I) hs_good)
    rw [hdir]
    rw [hsec_id s hs_src]
    rfl
  have hrep_deriv0 : deriv (chartRepAt (I := I) γ (fun s => W' (γ s)) 0) 0 = 0 := by
    rw [hrep_eq.deriv_eq]
    exact hNderiv0
  have hWp : trivToE (I := I) p p (W' p) = 0 := by
    rw [hW']
    have hchartp := chartE_covDerivAt (I := I) g p (self_mem_chartLeviCivitaGoodSet (I := I) p) hσmd
      (coordExtensionTangent (I := I) p w p)
    rw [hchartp]
    have hdir : trivToE (I := I) p p (coordExtensionTangent (I := I) p w p) = v₀ := by
      simpa [hv₀] using chartE_section_repr_coordExtensionTangent_eq
        (I := I) p w (chartLeviCivitaGoodSet_mem_baseSet (I := I)
          (self_mem_chartLeviCivitaGoodSet (I := I) p))
    rw [hdir]
    have hfo := radialTransportSection_chartE_firstOrder (I := I) g p η₀ hσmd (v := v₀)
    rw [← hσ, ← hf] at hfo
    exact hfo
  have hrep0 : chartRepAt (I := I) γ (fun s => W' (γ s)) 0 0 = 0 := by
    rw [chartRepAt_apply]
    rw [hγ0]
    exact hWp
  have hpar : covDerivAlong (I := I) g γ (fun s => W' (γ s)) 0 = 0 := by
    rw [covDerivAlong_def]
    rw [hγ0]
    have hz : chartCovDerivAlong (I := I) g p γ (chartRepAt (I := I) γ (fun s => W' (γ s)) 0) 0 = 0 := by
      rw [chartCovDerivAlong_def]
      rw [hrep_deriv0]
      rw [hrep0]
      rw [hvelE']
      rw [hx₀]
      simp
    change trivFromE (I := I) p p
      (chartCovDerivAlong (I := I) g p γ (chartRepAt (I := I) γ (fun s => W' (γ s)) 0) 0) = 0
    rw [hz]
    exact map_zero (trivFromE (I := I) p p)
  have hbridge := covDerivAlong_eq_leviCivita_of_eventuallyEq (I := I) g γ 0
    (hγ2.of_le (by norm_num)) (by simpa [hγ0] using hmdW') (hV := by rfl)
  have hb : covDerivAlong (I := I) g γ (fun s => W' (γ s)) 0 =
      (LeviCivita (I := I) g).toFun W' p (c • w) := by
    rw [hbridge]
    rw [hγ0]
    have hvel : mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) = c • w := by
      rw [hγvel, hX_def]
    change (LeviCivita (I := I) g).toFun W' p (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) =
      (LeviCivita (I := I) g).toFun W' p (c • w)
    rw [hvel]
  have hmain : (LeviCivita (I := I) g).toFun W' p (c • w) = 0 := by
    rw [← hb]
    exact hpar
  have hlin : (LeviCivita (I := I) g).toFun W' p (c • w) =
      c • (LeviCivita (I := I) g).toFun W' p w := by
    exact map_smul _ c w
  have hc0 : c • (LeviCivita (I := I) g).toFun W' p w = 0 := by
    rw [← hlin]
    exact hmain
  have hW'0 : (LeviCivita (I := I) g).toFun W' p w = 0 :=
    (smul_eq_zero.mp hc0).resolve_left hc_ne
  simpa [hW', hσ, coordExtensionTangent_self] using hW'0


end SecondOrderFlatness

section RadialTransportSectionSmooth

variable [T2Space M]

open DifferentialGeometry.Analysis.ODE.Flow

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [T2Space M] [T2Space (TangentBundle I M)] in
private lemma chartChristoffelContraction_full_contDiffOn_infty (g : SmoothRiemannianMetric I M)
    (α : M) :
    ContDiffOn ℝ ∞
      (fun z : E × E × E => chartChristoffelContraction (I := I) g α z.2.1 z.2.2 z.1)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) := by
  classical
  have hfst : ContDiff ℝ ∞ (fun z : E × E × E => z.1) :=
    contDiff_fst (𝕜 := ℝ) (E := E) (F := E × E)
  have hproj21 : ContDiff ℝ ∞ (fun z : E × E × E => z.2.1) := by
    have h1 : ContDiff ℝ ∞ (Prod.snd : E × (E × E) → E × E) :=
      contDiff_snd (𝕜 := ℝ) (E := E) (F := E × E)
    have h2 : ContDiff ℝ ∞ (Prod.fst : E × E → E) :=
      contDiff_fst (𝕜 := ℝ) (E := E) (F := E)
    exact h2.comp h1
  have hproj22 : ContDiff ℝ ∞ (fun z : E × E × E => z.2.2) := by
    have h1 : ContDiff ℝ ∞ (Prod.snd : E × (E × E) → E × E) :=
      contDiff_snd (𝕜 := ℝ) (E := E) (F := E × E)
    have h2 : ContDiff ℝ ∞ (Prod.snd : E × E → E) :=
      contDiff_snd (𝕜 := ℝ) (E := E) (F := E)
    exact h2.comp h1
  unfold chartChristoffelContraction
  refine ContDiffOn.sum (fun k _ => ?_)
  have hscalar : ContDiffOn ℝ ∞
      (fun z : E × E × E =>
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j k z.1 *
            chartCoord (E := E) i z.2.1 * chartCoord (E := E) j z.2.2)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) := by
    refine ContDiffOn.sum (fun i _ => ?_)
    refine ContDiffOn.sum (fun j _ => ?_)
    have hΓ : ContDiffOn ℝ ∞
        (fun z : E × E × E => chartChristoffel (I := I) g α i j k z.1)
        ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) := by
      have hbase : ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α i j k)
          (interior (extChartAt I α).target) :=
        chartChristoffel_contDiffOn_interior (I := I) g α i j k
      have hmapsto : MapsTo (fun z : E × E × E => z.1)
          ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E))
          (interior (extChartAt I α).target) := fun _ hp => hp.1
      exact hbase.comp hfst.contDiffOn hmapsto
    have hCLM_i : ContDiff ℝ ∞ (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord i).toContinuousLinearMap) :=
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord i).toContinuousLinearMap.contDiff
    have hCLM_j : ContDiff ℝ ∞ (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord j).toContinuousLinearMap) :=
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord j).toContinuousLinearMap.contDiff
    have hvi : ContDiffOn ℝ ∞
        (fun z : E × E × E => chartCoord (E := E) i z.2.1)
        ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) :=
      (hCLM_i.comp hproj21).contDiffOn
    have hwj : ContDiffOn ℝ ∞
        (fun z : E × E × E => chartCoord (E := E) j z.2.2)
        ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) :=
      (hCLM_j.comp hproj22).contDiffOn
    exact (hΓ.mul hvi).mul hwj
  have hconstk : ContDiffOn ℝ ∞
      (fun _ : E × E × E => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)
      ((interior (extChartAt I α).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) :=
    contDiffOn_const
  exact hscalar.smul hconstk

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
private lemma chartCurveDir_contDiffOn (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ expMapC2Radius (I := I) g p / 2 ∧
      ContDiffOn ℝ ∞
        (fun q : ℝ × E =>
          chartCurve (I := I) p
            (fun t : ℝ => expMap (I := I) g p (show TangentSpace I p from t • q.2)) q.1)
        ((Ioo (-1 : ℝ) 1) ×ˢ (ball (0 : E) ρ)) := by
  classical
  obtain ⟨δ, hδ_pos, hδ⟩ := expMap_contMDiffAt_infty_of_norm_lt (I := I) g p
  let ρ : ℝ := min (δ / 2) (expMapC2Radius (I := I) g p / 2)
  have hρ_pos : 0 < ρ := lt_min (half_pos hδ_pos) (half_pos (expMapC2Radius_pos (I := I) g p))
  have hρ_le : ρ ≤ expMapC2Radius (I := I) g p / 2 := min_le_right _ _
  refine ⟨ρ, hρ_pos, hρ_le, ?_⟩
  rw [IsOpen.contDiffOn_iff (isOpen_Ioo.prod isOpen_ball)]
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  have hw : ‖t • x‖ < δ := by
    have hnorm : ‖t • x‖ ≤ ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have habs : |t| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      exact (mul_le_mul_of_nonneg_right habs (norm_nonneg x)).trans_eq (one_mul _)
    have hxρ : ‖x‖ < ρ := by simpa [dist_eq_norm] using (mem_ball.mp hx)
    have hlt : ‖x‖ < δ := lt_of_le_of_lt (le_of_lt hxρ) (by
      have hρ_le : ρ ≤ δ / 2 := min_le_left _ _
      linarith)
    exact lt_of_le_of_lt hnorm hlt
  have hexpAt : ContMDiffAt 𝓘(ℝ, E) I ∞
      (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M)) (t • x) :=
    hδ (t • x) hw
  have hsmul : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E) ∞ (fun q : ℝ × E => q.1 • q.2) (t, x) := by
    have hcd : ContDiff ℝ ∞ (fun q : ℝ × E => q.1 • q.2) := by fun_prop
    exact (contMDiffAt_iff_contDiffAt.mpr hcd.contDiffAt)
  have hcomp1 : ContMDiffAt 𝓘(ℝ, ℝ × E) I ∞
      (fun q : ℝ × E => (expMap (I := I) g p (show TangentSpace I p from q.1 • q.2) : M)) (t, x) :=
    hexpAt.comp (t, x) hsmul
  have hw2 : ‖t • x‖ < expMapC2Radius (I := I) g p := by
    have hnorm : ‖t • x‖ ≤ ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have habs : |t| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      exact (mul_le_mul_of_nonneg_right habs (norm_nonneg x)).trans_eq (one_mul _)
    have hxρ : ‖x‖ < ρ := by simpa [dist_eq_norm] using (mem_ball.mp hx)
    have hlt : ‖x‖ < expMapC2Radius (I := I) g p := lt_of_le_of_lt (le_of_lt hxρ) (by
      have hρ_le : ρ ≤ expMapC2Radius (I := I) g p / 2 := min_le_right _ _
      linarith)
    exact lt_of_le_of_lt hnorm hlt
  have hsrc : expMap (I := I) g p (show TangentSpace I p from t • x) ∈ (chartAt H p).source := by
    exact radialCurve_mem_chartAt_source_of_norm_lt (I := I) g p hw2
  have hext : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I p)
      (expMap (I := I) g p (show TangentSpace I p from t • x)) :=
    contMDiffAt_extChartAt' (I := I) (n := ∞) (x := p) (x' := expMap (I := I) g p (show TangentSpace I p from t • x)) hsrc
  have hfull : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E) ∞
      (fun q : ℝ × E =>
        extChartAt I p (expMap (I := I) g p (show TangentSpace I p from q.1 • q.2))) (t, x) :=
    hext.comp (t, x) hcomp1
  have hfun : (fun q : ℝ × E =>
        chartCurve (I := I) p
          (fun t : ℝ => expMap (I := I) g p (show TangentSpace I p from t • q.2)) q.1) =
      fun q : ℝ × E =>
        extChartAt I p (expMap (I := I) g p (show TangentSpace I p from q.1 • q.2)) := by
    funext q
    rfl
  rw [hfun]
  exact contMDiffAt_iff_contDiffAt.mp hfull

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
private lemma chartCurveDirDeriv_contDiffOn (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ expMapC2Radius (I := I) g p / 2 ∧
      ContDiffOn ℝ ∞
        (fun q : ℝ × E =>
          deriv (chartCurve (I := I) p
            (fun t : ℝ => expMap (I := I) g p (show TangentSpace I p from t • q.2))) q.1)
        ((Ioo (-1 : ℝ) 1) ×ˢ (ball (0 : E) ρ)) := by
  classical
  obtain ⟨ρ, hρ_pos, hρ_le, hF⟩ := chartCurveDir_contDiffOn (I := I) g p
  set U : Set (ℝ × E) := (Ioo (-1 : ℝ) 1) ×ˢ (ball (0 : E) ρ) with hU_def
  have hU_open : IsOpen U := isOpen_Ioo.prod isOpen_ball
  set F : ℝ × E → E := fun q =>
    chartCurve (I := I) p
      (fun t : ℝ => expMap (I := I) g p (show TangentSpace I p from t • q.2)) q.1 with hF_def
  have hF' : ContDiffOn ℝ ∞ F U := by simpa [hF_def] using hF
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ F) U :=
    hF'.fderiv_of_isOpen hU_open (by simp)
  have happ : ContDiffOn ℝ ∞ (fun q : ℝ × E => (fderiv ℝ F q) (1, 0)) U := by
    have hconst : ContDiffOn ℝ ∞ (fun _ : ℝ × E => ((1 : ℝ), (0 : E))) U :=
      contDiffOn_const
    exact hfd.clm_apply hconst
  have hdeq : ∀ q : ℝ × E, q ∈ U →
      deriv (fun s : ℝ => chartCurve (I := I) p
        (fun t : ℝ => expMap (I := I) g p (show TangentSpace I p from t • q.2)) s) q.1 =
      (fderiv ℝ F (q.1, q.2)) (1, 0) := by
    intro q hq
    have hFdiff : DifferentiableAt ℝ F (q.1, q.2) :=
      ((hF' (q.1, q.2) hq).differentiableWithinAt (by decide)).differentiableAt
        (hU_open.mem_nhds hq)
    have hι : DifferentiableAt ℝ (fun s : ℝ => (s, q.2)) q.1 := by
      have h1 : HasFDerivAt (fun s : ℝ => s) (ContinuousLinearMap.id ℝ ℝ) q.1 :=
        (ContinuousLinearMap.id ℝ ℝ).hasFDerivAt
      have h2 : HasFDerivAt (fun _ : ℝ => q.2) (0 : ℝ →L[ℝ] E) q.1 :=
        hasFDerivAt_const (c := q.2) (x := q.1)
      exact (h1.prodMk h2).differentiableAt
    have hchain : fderiv ℝ (fun s : ℝ => F (s, q.2)) q.1 =
        (fderiv ℝ F (q.1, q.2)).comp (fderiv ℝ (fun s : ℝ => (s, q.2)) q.1) := by
      have hfun : (fun s : ℝ => F (s, q.2)) = F ∘ fun s : ℝ => (s, q.2) := rfl
      rw [hfun]
      exact fderiv_comp (x := q.1) hFdiff hι
    have hιd : fderiv ℝ (fun s : ℝ => (s, q.2)) q.1 = ContinuousLinearMap.inl ℝ ℝ E := by
      have h1 : HasFDerivAt (fun s : ℝ => s) (ContinuousLinearMap.id ℝ ℝ) q.1 :=
        (ContinuousLinearMap.id ℝ ℝ).hasFDerivAt
      have h2 : HasFDerivAt (fun _ : ℝ => q.2) (0 : ℝ →L[ℝ] E) q.1 :=
        hasFDerivAt_const (c := q.2) (x := q.1)
      have hιF : HasFDerivAt (fun s : ℝ => (s, q.2))
          ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] E)) q.1 := h1.prodMk h2
      have hval : fderiv ℝ (fun s : ℝ => (s, q.2)) q.1 =
          (ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] E) := hιF.fderiv
      rw [hval]
      rfl
    have hderiv_eq : deriv (fun s : ℝ => F (s, q.2)) q.1 =
        (fderiv ℝ (fun s : ℝ => F (s, q.2)) q.1) (1 : ℝ) := rfl
    rw [hderiv_eq, hchain, hιd]
    simp
  have htarget : ContDiffOn ℝ ∞
      (fun q : ℝ × E =>
        deriv (chartCurve (I := I) p
          (fun t : ℝ => expMap (I := I) g p (show TangentSpace I p from t • q.2))) q.1) U := by
    refine happ.congr ?_
    intro q hq
    exact hdeq q hq
  refine ⟨ρ, hρ_pos, hρ_le, ?_⟩
  simpa [hU_def] using htarget

omit [T2Space M] in
private def radialContractionFun (g : SmoothRiemannianMetric I M) (p : M) : E × E × E → E :=
  fun z => chartChristoffelContraction (I := I) g p z.2.1 z.2.2 z.1

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
private lemma radialTransportODE_contDiffOn (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ expMapC2Radius (I := I) g p / 2 ∧
      ContDiffOn ℝ ∞
        (fun q : ℝ × E × E =>
          - chartChristoffelContraction (I := I) g p
            (deriv (chartCurve (I := I) p
              (fun t : ℝ => expMap (I := I) g p (t • q.2.1))) q.1)
            q.2.2
            (chartCurve (I := I) p
              (fun t : ℝ => expMap (I := I) g p (t • q.2.1)) q.1))
        ((Ioo (-1 : ℝ) 1) ×ˢ (ball (0 : E) ρ) ×ˢ (Set.univ : Set E)) := by
  classical
  obtain ⟨ρ₁, hρ₁_pos, hρ₁_le_c2, h1⟩ := chartCurveDir_contDiffOn (I := I) g p
  obtain ⟨ρ₂, hρ₂_pos, hρ₂_le_c2, h2⟩ := chartCurveDirDeriv_contDiffOn (I := I) g p
  let ρ : ℝ := min ρ₁ ρ₂
  have hρ_pos : 0 < ρ := lt_min hρ₁_pos hρ₂_pos
  have hρ_le_c2 : ρ ≤ expMapC2Radius (I := I) g p / 2 := by
    exact le_trans (min_le_left _ _) hρ₁_le_c2
  have hρ₁_le : ρ ≤ ρ₁ := min_le_left _ _
  have hρ₂_le : ρ ≤ ρ₂ := min_le_right _ _
  set U : Set (ℝ × E × E) := (Ioo (-1 : ℝ) 1) ×ˢ (ball (0 : E) ρ) ×ˢ (Set.univ : Set E) with hU_def
  have hU_open : IsOpen U := isOpen_Ioo.prod (isOpen_ball.prod isOpen_univ)
  have hΓ : ContDiffOn ℝ ∞ (radialContractionFun g p)
      ((interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) := by
    change ContDiffOn ℝ ∞
        (fun z : E × E × E => chartChristoffelContraction (I := I) g p z.2.1 z.2.2 z.1)
        ((interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E))
    exact chartChristoffelContraction_full_contDiffOn_infty (I := I) g p
  set ccrv : (ℝ × E × E) → E := fun q =>
    chartCurve (I := I) p
      (fun t : ℝ => expMap (I := I) g p (t • q.2.1)) q.1 with hccrv_def
  set cdrv : (ℝ × E × E) → E := fun q =>
    deriv (chartCurve (I := I) p
      (fun t : ℝ => expMap (I := I) g p (t • q.2.1))) q.1 with hcdrv_def
  have hπ : ContDiff ℝ ∞ (fun q : ℝ × E × E => (q.1, q.2.1)) := by
    have hfst1 : ContDiff ℝ ∞ (fun q : ℝ × (E × E) => q.1) :=
      contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := E × E)
    have hsnd : ContDiff ℝ ∞ (Prod.snd : ℝ × (E × E) → E × E) :=
      contDiff_snd (𝕜 := ℝ) (E := ℝ) (F := E × E)
    have hfst2 : ContDiff ℝ ∞ (Prod.fst : E × E → E) :=
      contDiff_fst (𝕜 := ℝ) (E := E) (F := E)
    exact hfst1.prodMk (hfst2.comp hsnd)
  have hccrv_on : ContDiffOn ℝ ∞ ccrv U := by
    have h1' : ContDiffOn ℝ ∞
        (fun q : ℝ × E =>
          chartCurve (I := I) p
            (fun t : ℝ => expMap (I := I) g p (show TangentSpace I p from t • q.2)) q.1)
        ((Ioo (-1 : ℝ) 1) ×ˢ (ball (0 : E) ρ)) :=
      h1.mono (Set.prod_mono (le_refl _) (Metric.ball_subset_ball hρ₁_le))
    have hmap : MapsTo (fun q : ℝ × E × E => (q.1, q.2.1)) U
        ((Ioo (-1 : ℝ) 1) ×ˢ (ball (0 : E) ρ)) := by
      intro q hq
      rcases hq with ⟨ht, hx, _⟩
      exact ⟨ht, hx⟩
    exact h1'.comp (hπ.contDiffOn) hmap
  have hcdrv_on : ContDiffOn ℝ ∞ cdrv U := by
    have h2' : ContDiffOn ℝ ∞
        (fun q : ℝ × E =>
          deriv (chartCurve (I := I) p
            (fun t : ℝ => expMap (I := I) g p (show TangentSpace I p from t • q.2))) q.1)
        ((Ioo (-1 : ℝ) 1) ×ˢ (ball (0 : E) ρ)) :=
      h2.mono (Set.prod_mono (le_refl _) (Metric.ball_subset_ball hρ₂_le))
    have hmap : MapsTo (fun q : ℝ × E × E => (q.1, q.2.1)) U
        ((Ioo (-1 : ℝ) 1) ×ˢ (ball (0 : E) ρ)) := by
      intro q hq
      rcases hq with ⟨ht, hx, _⟩
      exact ⟨ht, hx⟩
    exact h2'.comp (hπ.contDiffOn) hmap
  have hw_proj : ContDiffOn ℝ ∞ (fun q : ℝ × E × E => q.2.2) U := by
    have hsnd : ContDiff ℝ ∞ (Prod.snd : ℝ × (E × E) → E × E) :=
      contDiff_snd (𝕜 := ℝ) (E := ℝ) (F := E × E)
    have hsnd2 : ContDiff ℝ ∞ (Prod.snd : E × E → E) :=
      contDiff_snd (𝕜 := ℝ) (E := E) (F := E)
    exact (hsnd2.comp hsnd).contDiffOn
  have hinner : ContDiffOn ℝ ∞ (fun q : ℝ × E × E => (ccrv q, (cdrv q, q.2.2))) U :=
    hccrv_on.prodMk (hcdrv_on.prodMk hw_proj)
  have hsrc_mem : ∀ q : ℝ × E × E, q ∈ U →
      expMap (I := I) g p (q.1 • q.2.1) ∈ (chartAt H p).source := by
    intro q hq
    rcases hq with ⟨ht, hx, _⟩
    have hnorm : ‖q.1 • q.2.1‖ ≤ ‖q.2.1‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have habs : |q.1| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      exact (mul_le_mul_of_nonneg_right habs (norm_nonneg (q.2.1))).trans_eq (one_mul _)
    have hxρ : ‖q.2.1‖ < ρ := by simpa [dist_eq_norm] using (mem_ball.mp hx)
    have hlt : ‖q.1 • q.2.1‖ < expMapC2Radius (I := I) g p := by
      have : ‖q.2.1‖ < expMapC2Radius (I := I) g p := lt_of_le_of_lt (le_of_lt hxρ) (by linarith)
      exact lt_of_le_of_lt hnorm this
    have hlt_one : ‖(1 : ℝ) • (q.1 • q.2.1)‖ < expMapC2Radius (I := I) g p := by
      rw [one_smul]
      exact hlt
    have hsrc_one := radialCurve_mem_chartAt_source_of_norm_lt (I := I) g p
      (s := 1) (v := (q.1 • q.2.1 : TangentSpace I p)) hlt_one
    have harg : (1 : ℝ) • (q.1 • q.2.1 : TangentSpace I p) = q.1 • q.2.1 :=
      one_smul ℝ (q.1 • q.2.1 : TangentSpace I p)
    exact (congrArg (fun z : M => z ∈ (chartAt H p).source)
      (congrArg (expMap (I := I) g p) harg)).mp hsrc_one
  have hmapsto : MapsTo (fun q : ℝ × E × E => (ccrv q, (cdrv q, q.2.2))) U
      ((interior (extChartAt I p).target) ×ˢ (Set.univ : Set E) ×ˢ (Set.univ : Set E)) := by
    intro q hq
    refine ⟨?_, ?_, ?_⟩
    · have hsrc : expMap (I := I) g p (q.1 • q.2.1) ∈ (chartAt H p).source :=
        hsrc_mem q hq
      have hsrc' : expMap (I := I) g p (q.1 • q.2.1) ∈ (extChartAt I p).source := by
        simpa [extChartAt_source] using hsrc
      have htgt : extChartAt I p (expMap (I := I) g p (q.1 • q.2.1)) ∈
          (extChartAt I p).target :=
        (extChartAt I p).map_source hsrc'
      simpa [hccrv_def] using
        (extChartAt_target_subset_interior_of_boundaryless (I := I) p htgt)
    · exact Set.mem_univ _
    · exact Set.mem_univ _
  have hΓc : ContDiffOn ℝ ∞
      (fun q : ℝ × E × E => radialContractionFun g p (ccrv q, (cdrv q, q.2.2))) U := by
    exact hΓ.comp (s := U) (f := fun q : ℝ × E × E => (ccrv q, (cdrv q, q.2.2))) hinner hmapsto
  have hneg : ContDiffOn ℝ ∞
      (fun q : ℝ × E × E => - radialContractionFun g p (ccrv q, (cdrv q, q.2.2))) U :=
    hΓc.neg
  refine ⟨ρ, hρ_pos, hρ_le_c2, ?_⟩
  simpa [hU_def, hccrv_def, hcdrv_def, radialContractionFun] using hneg

omit [T2Space M] in
private noncomputable def radialTransportODEValue (g : SmoothRiemannianMetric I M) (p : M)
    (t : ℝ) (x w : E) : E :=
  - chartChristoffelContraction (I := I) g p
    (deriv (chartCurve (I := I) p
      (fun s : ℝ => expMap (I := I) g p (show TangentSpace I p from s • x))) t) w
    (chartCurve (I := I) p
      (fun s : ℝ => expMap (I := I) g p (show TangentSpace I p from s • x)) t)

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
private lemma radialTransportODEValue_contDiffOn (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ expMapC2Radius (I := I) g p / 2 ∧
      ContDiffOn ℝ ∞
        (fun q : ℝ × E × E => radialTransportODEValue g p q.1 q.2.1 q.2.2)
        ((Ioo (-1 : ℝ) 1) ×ˢ (ball (0 : E) ρ) ×ˢ (Set.univ : Set E)) := by
  obtain ⟨ρ, hρ_pos, hρ_le, hcd⟩ := radialTransportODE_contDiffOn (I := I) g p
  refine ⟨ρ, hρ_pos, hρ_le, ?_⟩
  exact hcd

omit [T2Space M] in
private noncomputable def radialTransportChartRep (g : SmoothRiemannianMetric I M) (p : M)
    (η₀ : TangentSpace I p) (x : E) (t : ℝ) : E :=
  chartESectionRepr (I := I) p (radialTransportSection (I := I) g p η₀)
    (expMap (I := I) g p (show TangentSpace I p from t • x))

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
private theorem radialTransportSection_chartE_value_contDiffOn (g : SmoothRiemannianMetric I M)
    (p : M) (η₀ : TangentSpace I p) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ContDiffOn ℝ ∞ (fun x : E => radialTransportChartRep g p η₀ x 1) (ball (0 : E) ρ) := by
  classical
  set σ : Π y : M, TangentSpace I y := radialTransportSection (I := I) g p η₀ with hσ
  obtain ⟨ρ, hρ_pos, hρ_le_c2, hODE_cd⟩ := radialTransportODE_contDiffOn (I := I) g p
  set J : Set ℝ := Ioo (-1 : ℝ) 1 with hJ_def
  set V : Set (E × E) := ball (0 : E) ρ ×ˢ (Set.univ : Set E) with hV_def
  set v : ℝ → (E × E) → (E × E) := fun t q => (0, radialTransportODEValue g p t q.1 q.2) with hv_def
  have hODE_cd' : ContDiffOn ℝ ∞
      (fun q : ℝ × (E × E) => radialTransportODEValue g p q.1 q.2.1 q.2.2) (J ×ˢ V) := by
    change ContDiffOn ℝ ∞
        (fun q : ℝ × E × E => radialTransportODEValue g p q.1 q.2.1 q.2.2)
        ((Ioo (-1 : ℝ) 1) ×ˢ (ball (0 : E) ρ) ×ˢ (Set.univ : Set E))
    exact hODE_cd
  have hv : ContDiffOn ℝ ∞ (uncurry v) (J ×ˢ V) := by
    have h₁ : ContDiffOn ℝ ∞ (fun q : ℝ × (E × E) => (0 : E)) (J ×ˢ V) :=
      contDiffOn_const
    have h₂ : ContDiffOn ℝ ∞ (fun q : ℝ × (E × E) => radialTransportODEValue g p q.1 q.2.1 q.2.2) (J ×ˢ V) :=
      hODE_cd'
    have hfun : uncurry v =
        fun q : ℝ × (E × E) => (0, radialTransportODEValue g p q.1 q.2.1 q.2.2) := by
      funext q
      rfl
    rw [hfun]
    exact h₁.prodMk h₂
  set a₀ : E → E × E := fun x => (x, chartESectionRepr (I := I) p σ p) with ha₀_def
  have ha₀ : ContDiffOn ℝ ∞ a₀ (ball (0 : E) ρ) := by
    have h₁ : ContDiff ℝ ∞ (fun x : E => x) := contDiff_id
    have h₂ : ContDiff ℝ ∞ (fun _ : E => chartESectionRepr (I := I) p σ p) := contDiff_const
    simpa [a₀] using (h₁.prodMk h₂).contDiffOn
  set γ : E → ℝ → E × E := fun x t => (x, radialTransportChartRep g p η₀ x t) with hγ_def
  have hY_ode : ∀ x ∈ ball (0 : E) ρ, ∀ t ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun s : ℝ => radialTransportChartRep g p η₀ x s)
        (radialTransportODEValue g p t x (radialTransportChartRep g p η₀ x t)) t := by
    intro x hx t ht
    have hX : ‖(show TangentSpace I p from x : E)‖ < radialRadius (I := I) g p := by
      have hxρ : ‖x‖ < ρ := by simpa [dist_eq_norm] using (mem_ball.mp hx)
      have hlt : ‖x‖ < expMapC2Radius (I := I) g p / 2 := lt_of_lt_of_le hxρ hρ_le_c2
      rw [radialRadius]
      exact hlt
    have hraw := radialTransportSection_chartRep_hasDerivAt (I := I) g p hX η₀ ht
    have hcurve :
        (fun s : ℝ => expMap (I := I) g p
          (show TangentSpace I p from s • x)) =
        (fun s : ℝ => expMap (I := I) g p
          (s • (show TangentSpace I p from x))) := by
      funext s
      congr 1
    have hcurve_apply (s : ℝ) := congrFun hcurve s
    unfold radialTransportChartRep radialTransportODEValue
    simpa only [hcurve_apply] using hraw
  have hγ_ode : ∀ x ∈ ball (0 : E) ρ,
      γ x 0 = a₀ x ∧ IsIntegralCurveOn (γ x) v (Set.Icc (0 : ℝ) (1 / 2)) := by
    intro x hx
    constructor
    · have hY0 : radialTransportChartRep g p η₀ x 0 = chartESectionRepr (I := I) p σ p := by
        change chartESectionRepr (I := I) p σ
            (expMap (I := I) g p ((0 : ℝ) • (show TangentSpace I p from x))) =
          chartESectionRepr (I := I) p σ p
        rw [radialCurve_zero (I := I) g p (show TangentSpace I p from x)]
      simp [γ, a₀, hY0]
    · intro t ht
      have htIoo : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hODE_t := hY_ode x hx t htIoo
      have hfst : HasDerivWithinAt (fun s : ℝ => x) (0 : E) (Set.Icc (0 : ℝ) (1 / 2)) t := by
        simpa using (hasDerivAt_const t (c := x)).hasDerivWithinAt
      have hsnd : HasDerivWithinAt (fun s : ℝ => radialTransportChartRep g p η₀ x s)
          (radialTransportODEValue g p t x (radialTransportChartRep g p η₀ x t))
          (Set.Icc (0 : ℝ) (1 / 2)) t :=
        hODE_t.hasDerivWithinAt
      have hprod : HasDerivWithinAt (fun s : ℝ => (x, radialTransportChartRep g p η₀ x s))
          ((0 : E), radialTransportODEValue g p t x (radialTransportChartRep g p η₀ x t))
          (Set.Icc (0 : ℝ) (1 / 2)) t :=
        hfst.prodMk hsnd
      simpa [γ, v, hv_def] using hprod
  have hstay : ∀ x ∈ ball (0 : E) ρ, MapsTo (γ x) (Set.Icc (0 : ℝ) (1 / 2)) V := by
    intro x hx t ht
    exact ⟨hx, Set.mem_univ _⟩
  have hres := ode_slice_right_on (E := E × E) (P := E) (J := J) (V := V) (v := v)
    (hJ := isOpen_Ioo) (hV := isOpen_ball.prod isOpen_univ) (hv := hv)
    (A := ball (0 : E) ρ) (hA := isOpen_ball)
    (a := 0) (b := 1 / 2) (hI := by intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (a₀ := a₀) (ha₀ := ha₀) (γ := γ) (hγ := hγ_ode) (hstay := hstay)
  have hhalf : ContDiffOn ℝ ∞
      (fun x : E => radialTransportChartRep g p η₀ x (1 / 2)) (ball (0 : E) ρ) := by
    have hslice : ContDiffOn ℝ ∞ (fun x : E => γ x (1 / 2)) (ball (0 : E) ρ) :=
      hres (1 / 2) ⟨by norm_num, by norm_num⟩
    have hsnd' : ContDiffOn ℝ ∞ (fun x : E => (γ x (1 / 2)).2) (ball (0 : E) ρ) := hslice.snd
    simpa [hγ_def] using hsnd'
  have hdouble : ContDiff ℝ ∞ (fun x : E => (2 : ℝ) • x) := by fun_prop
  have hdoubleOn : ContDiffOn ℝ ∞ (fun x : E => radialTransportChartRep g p η₀ ((2 : ℝ) • x) (1 / 2))
      (ball (0 : E) (ρ / 2)) := by
    have hmaps : MapsTo (fun x : E => (2 : ℝ) • x) (ball (0 : E) (ρ / 2)) (ball (0 : E) ρ) := by
      intro x hx
      have hxρ : ‖x‖ < ρ / 2 := by simpa [dist_eq_norm] using (mem_ball.mp hx)
      rw [mem_ball, dist_zero_right]
      rw [norm_smul, Real.norm_eq_abs]
      have h2 : |(2 : ℝ)| = 2 := by norm_num
      rw [h2]
      have hnorm : 2 * ‖x‖ < ρ := by linarith
      exact hnorm
    exact hhalf.comp hdouble.contDiffOn hmaps
  have hid : ∀ x : E,
      radialTransportChartRep g p η₀ x 1 = radialTransportChartRep g p η₀ ((2 : ℝ) • x) (1 / 2) := by
    intro x
    set v : TangentSpace I p := show TangentSpace I p from x with hv'
    have hsmul : (1 / 2 : ℝ) • ((2 : ℝ) • v) = (1 : ℝ) • v := by
      rw [smul_smul]
      congr 1
      norm_num
    have hval : expMap (I := I) g p ((1 : ℝ) • v) =
        expMap (I := I) g p ((1 / 2 : ℝ) • ((2 : ℝ) • v)) := by
      rw [hsmul]
    change chartESectionRepr (I := I) p σ (expMap (I := I) g p ((1 : ℝ) • v)) =
      chartESectionRepr (I := I) p σ (expMap (I := I) g p ((1 / 2 : ℝ) • ((2 : ℝ) • v)))
    rw [hval]
  refine ⟨ρ / 2, by positivity, ?_⟩
  have hgoal : ContDiffOn ℝ ∞
      (fun x : E => radialTransportChartRep g p η₀ x 1) (ball (0 : E) (ρ / 2)) := by
    refine hdoubleOn.congr ?_
    intro x hx
    exact hid x
  exact hgoal

omit [T2Space M] in
private noncomputable def expMapE (g : SmoothRiemannianMetric I M) (p : M) (x : E) : M :=
  expMap (I := I) g p x

omit [T2Space M] [NeZero (Module.finrank ℝ E)] in
private lemma chartExpCoord_contDiffAt (g : SmoothRiemannianMetric I M) (p : M) :
    ContDiffAt ℝ ∞
      (fun x : E => extChartAt I p (expMapE g p x)) 0 := by
  classical
  obtain ⟨δ, hδ_pos, hδ⟩ := expMap_contMDiffAt_infty_of_norm_lt (I := I) g p
  have hδ0 : ‖(0 : E)‖ < δ := by simpa using hδ_pos
  have hexp : ContMDiffAt 𝓘(ℝ, E) I ∞ (fun x : E => (expMapE g p x : M)) 0 := by
    simpa [expMapE] using hδ (0 : E) hδ0
  have hsrc : p ∈ (chartAt H p).source := mem_chart_source H p
  have hφ : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I p) p :=
    contMDiffAt_extChartAt' (I := I) (n := ∞) (x := p) (x' := p) hsrc
  have hφAt : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I p) (expMapE g p 0) := by
    convert hφ using 1
    change expMap (I := I) g p (0 : TangentSpace I p) = p
    exact expMap_zero (I := I) g p
  have hcomp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      ((extChartAt I p) ∘ fun x : E => expMapE g p x) 0 :=
    hφAt.comp 0 hexp
  exact contMDiffAt_iff_contDiffAt.mp hcomp

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
private lemma chartExpCoord_fderiv_zero (g : SmoothRiemannianMetric I M) (p : M) :
    fderiv ℝ (fun x : E => extChartAt I p (expMapE g p x)) 0 =
      ContinuousLinearMap.id ℝ E := by
  classical
  set z : E → E := fun x => extChartAt I p (expMapE g p x) with hz
  have hz1 : ContDiffAt ℝ 1 z 0 :=
    (chartExpCoord_contDiffAt (I := I) g p).of_le (by norm_num)
  have hzdiff : DifferentiableAt ℝ z 0 := hz1.differentiableAt_one
  apply ContinuousLinearMap.ext
  intro v
  have hιd : DifferentiableAt ℝ (fun t : ℝ => t • v) 0 := by
    have hL : (fun t : ℝ => t • v) = ContinuousLinearMap.toSpanSingleton ℝ v := by
      funext t
      rfl
    rw [hL]
    exact (ContinuousLinearMap.toSpanSingleton ℝ v).hasFDerivAt.differentiableAt
  have hι1 : (fderiv ℝ (fun t : ℝ => t • v) 0) (1 : ℝ) = v := by
    have hL : (fun t : ℝ => t • v) = ContinuousLinearMap.toSpanSingleton ℝ v := by
      funext t
      rfl
    rw [hL]
    have hfd : fderiv ℝ (ContinuousLinearMap.toSpanSingleton ℝ v) 0 =
        ContinuousLinearMap.toSpanSingleton ℝ v :=
      (ContinuousLinearMap.toSpanSingleton ℝ v).hasFDerivAt.fderiv
    rw [hfd]
    simp
  have hdir : (fderiv ℝ z 0) v = deriv (fun t : ℝ => z (t • v)) 0 := by
    have hdrv : deriv (fun t : ℝ => z (t • v)) 0 =
        (fderiv ℝ (fun t : ℝ => z (t • v)) 0) (1 : ℝ) := rfl
    rw [hdrv]
    have hfun : (fun t : ℝ => z (t • v)) = z ∘ (fun t : ℝ => t • v) := rfl
    rw [hfun]
    have hzAt : DifferentiableAt ℝ z ((fun t : ℝ => t • v) 0) := by simpa using hzdiff
    have hchain := fderiv_comp (x := 0) hzAt hιd
    rw [hchain]
    rw [ContinuousLinearMap.comp_apply]
    rw [hι1]
    rw [zero_smul]
  have hderiv : deriv (fun t : ℝ => z (t • v)) 0 = v := by
    have hzv : (fun t : ℝ => z (t • v)) = chartCurve (I := I) p
        (fun s : ℝ => expMap (I := I) g p (show TangentSpace I p from s • v)) := by
      funext t
      simp [z, expMapE]
    rw [hzv]
    exact radialCurve_chartCurve_deriv_zero (I := I) g p
      (show TangentSpace I p from v)
  rw [hdir]
  exact hderiv

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
private lemma chartExpCoord_hasFDerivAt_zero (g : SmoothRiemannianMetric I M) (p : M) :
    HasFDerivAt (fun x : E => extChartAt I p (expMapE g p x))
      (ContinuousLinearMap.id ℝ E) 0 := by
  classical
  have hz1 : ContDiffAt ℝ 1 (fun x : E => extChartAt I p (expMapE g p x)) 0 :=
    (chartExpCoord_contDiffAt (I := I) g p).of_le (by norm_num)
  have hfd : HasFDerivAt (fun x : E => extChartAt I p (expMapE g p x))
      (fderiv ℝ (fun x : E => extChartAt I p (expMapE g p x)) 0) 0 :=
    hz1.differentiableAt_one.hasFDerivAt
  convert hfd using 1
  exact (chartExpCoord_fderiv_zero (I := I) g p).symm

omit [T2Space M] in
noncomputable def radialTransportSectionDomain (g : SmoothRiemannianMetric I M) (p : M) : Set M :=
  {y : M | y ∈ (normalChartAt (I := I) g p).source ∧
    ‖normalChartAt (I := I) g p y‖ < radialRadius (I := I) g p}

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
lemma radialTransportSectionDomain_isOpen (g : SmoothRiemannianMetric I M) (p : M) :
    IsOpen (radialTransportSectionDomain (I := I) g p) := by
  classical
  unfold radialTransportSectionDomain
  have hcont : ContinuousOn (normalChartAt (I := I) g p) (normalChartAt (I := I) g p).source :=
    (normalChartAt_contMDiffOn (I := I) g p).continuousOn
  have hopen1 : IsOpen ((normalChartAt (I := I) g p).source ∩
      (normalChartAt (I := I) g p) ⁻¹' (ball (0 : E) (radialRadius (I := I) g p))) :=
    hcont.isOpen_inter_preimage (normalChartAt (I := I) g p).open_source isOpen_ball
  convert hopen1 using 1
  ext y
  simp [mem_ball, dist_zero_right]

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
lemma mem_radialTransportSectionDomain_self (g : SmoothRiemannianMetric I M) (p : M) :
    p ∈ radialTransportSectionDomain (I := I) g p := by
  classical
  unfold radialTransportSectionDomain
  refine ⟨normalChartAt_source (I := I) g p, ?_⟩
  rw [normalChartAt_centre (I := I) g p]
  simpa using (radialRadius_pos (I := I) g p)

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
private lemma chartExpCoord_localInverse (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ W : Set E, IsOpen W ∧ extChartAt I p p ∈ W ∧
      ∃ ψ : E → E, ψ (extChartAt I p p) = 0 ∧
        ContDiffOn ℝ ∞ ψ W ∧
        (∀ᶠ x in 𝓝 (0 : E), ψ (extChartAt I p (expMapE g p x)) = x) := by
  classical
  set Φ : E → E := fun x => extChartAt I p (expMapE g p x) with hΦ
  have hΦ0 : Φ 0 = extChartAt I p p := by
    change extChartAt I p (expMap (I := I) g p (0 : TangentSpace I p)) = extChartAt I p p
    rw [expMap_zero]
  have hcd : ContDiffAt ℝ ∞ Φ 0 := by
    simpa [hΦ] using (chartExpCoord_contDiffAt (I := I) g p)
  have hfd : HasFDerivAt Φ (ContinuousLinearMap.id ℝ E) 0 := by
    simpa [hΦ] using (chartExpCoord_hasFDerivAt_zero (I := I) g p)
  let f' : E ≃L[ℝ] E := ContinuousLinearEquiv.refl ℝ E
  have hfd' : HasFDerivAt Φ (f' : E →L[ℝ] E) 0 := by
    simpa [f'] using hfd
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let e : OpenPartialHomeomorph E E := hcd.toOpenPartialHomeomorph Φ hfd' hn
  have he_target : Φ 0 ∈ e.target := hcd.image_mem_toOpenPartialHomeomorph_target hfd' hn
  let ψ : E → E := hcd.localInverse hfd' hn
  have hψ0 : ψ (Φ 0) = 0 := hcd.localInverse_apply_image hfd' hn
  have hleft : ∀ᶠ x in 𝓝 (0 : E), ψ (Φ x) = x := by
    have h := (hcd.hasStrictFDerivAt' hfd' hn).eventually_left_inverse
    change ∀ᶠ x in 𝓝 (0 : E), ψ (Φ x) = x at h
    exact h
  have hψ_cont0 : ContinuousAt ψ (Φ 0) := by
    simpa [ψ] using (hcd.to_localInverse hfd' hn).continuousAt
  have hcd1 : ContDiffAt ℝ 1 Φ 0 := hcd.of_le (by simp)
  obtain ⟨A, ⟨u₀, hu₀, hA_deriv⟩, hA_cd0⟩ :=
    (contDiffAt_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 0)).mp hcd1
  have hA0 : A 0 = ContinuousLinearMap.id ℝ E := by
    have h₁ : HasFDerivAt Φ (A 0) 0 := hA_deriv 0 (mem_of_mem_nhds hu₀)
    have h₂ : HasFDerivAt Φ (ContinuousLinearMap.id ℝ E) 0 := by
      simpa [hΦ] using (chartExpCoord_hasFDerivAt_zero (I := I) g p)
    exact h₁.unique h₂
  have hunit0 : IsUnit (A 0) := by
    rw [hA0]
    exact isUnit_one
  have hA_unit_nhd : {y : E | IsUnit (A y)} ∈ 𝓝 (0 : E) :=
    hA_cd0.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hunit0)
  obtain ⟨δ, hδ_pos, hδ⟩ := expMap_contMDiffAt_infty_of_norm_lt (I := I) g p
  obtain ⟨δ_u, hδu_pos, hδu_ball⟩ := Metric.mem_nhds_iff.mp hu₀
  obtain ⟨δ_A, hδA_pos, hδA_ball⟩ := Metric.mem_nhds_iff.mp hA_unit_nhd
  let ε : ℝ := min δ (min δ_u (min δ_A (expMapC2Radius (I := I) g p)))
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact lt_min hδ_pos (lt_min hδu_pos (lt_min hδA_pos (expMapC2Radius_pos (I := I) g p)))
  have hε_le_δ : ε ≤ δ := min_le_left _ _
  have hε_le_δu : ε ≤ δ_u := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε_le_δA : ε ≤ δ_A := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε_le_c2 : ε ≤ expMapC2Radius (I := I) g p :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hψ_small_nhd : {ξ : E | ‖ψ ξ‖ < ε} ∈ 𝓝 (Φ 0) := by
    have hb : (0 : E) ∈ ball (0 : E) ε := by simpa using hε_pos
    have hpre : ψ ⁻¹' (ball (0 : E) ε) ∈ 𝓝 (Φ 0) :=
      hψ_cont0.preimage_mem_nhds (isOpen_ball.mem_nhds (by simpa [hψ0] using hb))
    convert hpre using 1
    ext ξ
    simp [mem_ball, dist_zero_right]
  have hW_nhd : e.target ∩ {ξ : E | ‖ψ ξ‖ < ε} ∈ 𝓝 (Φ 0) :=
    Filter.inter_mem (e.open_target.mem_nhds he_target) hψ_small_nhd
  obtain ⟨W, hW_sub, hW_open, hW_mem⟩ := _root_.mem_nhds_iff.mp hW_nhd
  have hW_target : W ⊆ e.target := fun ξ hξ => (hW_sub hξ).1
  have hW_small : W ⊆ {ξ : E | ‖ψ ξ‖ < ε} := fun ξ hξ => (hW_sub hξ).2
  have hψ_cdAt : ∀ ξ ∈ W, ContDiffAt ℝ ∞ ψ ξ := by
    intro ξ hξ
    have hξ_target : ξ ∈ e.target := hW_target hξ
    have hξ_small : ‖ψ ξ‖ < ε := hW_small hξ
    set x : E := ψ ξ with hx
    have hx_ε : ‖x‖ < ε := by simpa [hx] using hξ_small
    have hx_δ : ‖x‖ < δ := lt_of_lt_of_le hx_ε hε_le_δ
    have hx_δu : ‖x‖ < δ_u := lt_of_lt_of_le hx_ε hε_le_δu
    have hx_δA : ‖x‖ < δ_A := lt_of_lt_of_le hx_ε hε_le_δA
    have hx_c2 : ‖x‖ < expMapC2Radius (I := I) g p := lt_of_lt_of_le hx_ε hε_le_c2
    have hx_ball_u : x ∈ ball (0 : E) δ_u := by
      rw [mem_ball, dist_zero_right]
      exact hx_δu
    have hx_u₀ : x ∈ u₀ := hδu_ball hx_ball_u
    have hx_ball_A : x ∈ ball (0 : E) δ_A := by
      rw [mem_ball, dist_zero_right]
      exact hx_δA
    have hunit_x : IsUnit (A x) := hδA_ball hx_ball_A
    have hsrc_exp : expMap (I := I) g p (show TangentSpace I p from x) ∈ (chartAt H p).source := by
      have hnorm : ‖(1 : ℝ) • (show TangentSpace I p from x : E)‖ < expMapC2Radius (I := I) g p := by
        change ‖(1 : ℝ) • x‖ < expMapC2Radius (I := I) g p
        rw [one_smul]
        exact hx_c2
      have hsrc_one := radialCurve_mem_chartAt_source_of_norm_lt (I := I) g p
        (v := show TangentSpace I p from x) (s := 1) hnorm
      have harg : (1 : ℝ) • (show TangentSpace I p from x) =
          (show TangentSpace I p from x) := one_smul ℝ _
      exact (congrArg (fun z : M => z ∈ (chartAt H p).source)
        (congrArg (expMap (I := I) g p) harg)).mp hsrc_one
    have hmd_exp : ContMDiffAt 𝓘(ℝ, E) I ∞
        (fun u : E => (expMap (I := I) g p (show TangentSpace I p from u) : M)) x :=
      hδ x hx_δ
    have hφ_exp : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I p)
        (expMap (I := I) g p (show TangentSpace I p from x)) :=
      contMDiffAt_extChartAt' (I := I) (n := ∞) (x := p)
        (x' := expMap (I := I) g p (show TangentSpace I p from x)) hsrc_exp
    have hmd_Φ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
        (fun u : E => extChartAt I p (expMap (I := I) g p (show TangentSpace I p from u))) x :=
      hφ_exp.comp x hmd_exp
    have hcdΦx : ContDiffAt ℝ ∞ Φ x := by
      have hfun : (fun u : E => extChartAt I p (expMap (I := I) g p (show TangentSpace I p from u))) = Φ := by
        funext u
        rw [hΦ]
        rfl
      rw [hfun] at hmd_Φ
      exact contMDiffAt_iff_contDiffAt.mp hmd_Φ
    have hf' : HasFDerivAt Φ (A x) x := hA_deriv x hx_u₀
    obtain ⟨u, hu⟩ := hunit_x
    let L : E ≃L[ℝ] E := ContinuousLinearEquiv.unitsEquiv ℝ E u
    have hL : (L : E →L[ℝ] E) = A x := by
      ext x'
      change ContinuousLinearEquiv.unitsEquiv ℝ E u x' = A x x'
      rw [ContinuousLinearEquiv.unitsEquiv_apply, hu]
    have hf'' : HasFDerivAt Φ (L : E →L[ℝ] E) x := by
      simpa [hL] using hf'
    have hψ_cdξ : ContDiffAt ℝ ∞ ψ ξ := by
      have h := e.contDiffAt_symm (a := ξ) (f₀' := L) hξ_target hf'' hcdΦx
      change ContDiffAt ℝ ∞ ψ ξ at h
      exact h
    exact hψ_cdξ
  have hψ_cdOn : ContDiffOn ℝ ∞ ψ W := (IsOpen.contDiffOn_iff hW_open).2 hψ_cdAt
  refine ⟨W, hW_open, ?_, ψ, ?_, hψ_cdOn, ?_⟩
  · rw [← hΦ0]
    exact hW_mem
  · rw [← hΦ0]
    exact hψ0
  · simpa [hΦ] using hleft

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
private lemma radialTransportSection_chartE_repr_eq (g : SmoothRiemannianMetric I M)
    (p : M) (η₀ : TangentSpace I p) {ψ : E → E} {y : M}
    (hy : y ∈ (normalChartAt (I := I) g p).source)
    (hx : ψ (extChartAt I p y) = normalChartAt (I := I) g p y) :
    chartESectionRepr (I := I) p (radialTransportSection (I := I) g p η₀) y =
      radialTransportChartRep g p η₀ (ψ (extChartAt I p y)) 1 := by
  classical
  set σ : Π y : M, TangentSpace I y := radialTransportSection (I := I) g p η₀ with hσ
  set x : E := normalChartAt (I := I) g p y with hx_def
  have hy_exp : y = expMap (I := I) g p (show TangentSpace I p from (1 : ℝ) • x) := by
    have hsymm : (normalChartAt (I := I) g p).symm x = y := by
      rw [hx_def]
      exact normalChartAt_left_inv (I := I) g p hy
    have htgt : x ∈ (normalChartAt (I := I) g p).symm.source := by
      rw [hx_def]
      have hmap : (normalChartAt (I := I) g p) y ∈ (normalChartAt (I := I) g p).target :=
        (normalChartAt (I := I) g p).map_source hy
      simpa using hmap
    have hexp : (normalChartAt (I := I) g p).symm x =
        expMap (I := I) g p (show TangentSpace I p from x) :=
      normalChartAt_symm_apply (I := I) g p htgt
    rw [← hsymm, hexp]
    simp [one_smul]
  calc
    chartESectionRepr (I := I) p σ y
        = chartESectionRepr (I := I) p σ (expMap (I := I) g p
            (show TangentSpace I p from (1 : ℝ) • x)) := by
      rw [← hy_exp]
    _ = radialTransportChartRep g p η₀ x 1 := rfl
    _ = radialTransportChartRep g p η₀ (ψ (extChartAt I p y)) 1 := by
      rw [← hx]

omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] in
theorem radialTransportSection_contMDiffOn (g : SmoothRiemannianMetric I M) (p : M)
    (η₀ : TangentSpace I p) :
    ∃ U : Set M, U ∈ 𝓝 p ∧ U ⊆ radialTransportSectionDomain (I := I) g p ∧
      ContMDiffOn I I.tangent ∞ (T% (radialTransportSection (I := I) g p η₀)) U := by
  classical
  set σ : Π y : M, TangentSpace I y := radialTransportSection (I := I) g p η₀ with hσ
  set φ : M → E := (extChartAt I p : M → E) with hφ
  set Φ : E → E := fun x => φ (expMapE g p x) with hΦ
  obtain ⟨ρ, hρ_pos, hρ_cd⟩ := radialTransportSection_chartE_value_contDiffOn (I := I) g p η₀
  obtain ⟨W, hW_open, hW_φp, ψ, hψ_φp, hψ_cd, hψ_left⟩ :=
    chartExpCoord_localInverse (I := I) g p
  obtain ⟨A, hA_nhd, hA⟩ := hψ_left.exists_mem
  have hNC_cont : ContinuousAt (normalChartAt (I := I) g p) p := by
    have hsrc_nhd : (normalChartAt (I := I) g p).source ∈ 𝓝 p :=
      (normalChartAt_open_source (I := I) g p).mem_nhds (normalChartAt_source (I := I) g p)
    have hNC_at : ContMDiffAt I 𝓘(ℝ, E) 1 (normalChartAt (I := I) g p) p :=
      (normalChartAt_contMDiffOn (I := I) g p p (normalChartAt_source (I := I) g p)).contMDiffAt
        hsrc_nhd
    exact hNC_at.continuousAt
  have hBρ_p : {y : M | ‖normalChartAt (I := I) g p y‖ < ρ} ∈ 𝓝 p := by
    have hρ_nhd : ball (0 : E) ρ ∈ 𝓝 (normalChartAt (I := I) g p p) := by
      rw [normalChartAt_centre (I := I) g p]
      exact isOpen_ball.mem_nhds (by rw [mem_ball, dist_zero_right]; simpa using hρ_pos)
    have hpre : (normalChartAt (I := I) g p) ⁻¹' (ball (0 : E) ρ) ∈ 𝓝 p :=
      hNC_cont.preimage_mem_nhds hρ_nhd
    convert hpre using 1
    ext y
    simp [mem_ball, dist_zero_right]
  let V : Set M := (chartAt H p).source ∩ φ ⁻¹' W ∩ (normalChartAt (I := I) g p).source ∩
    (normalChartAt (I := I) g p) ⁻¹' A ∩ {y : M | ‖normalChartAt (I := I) g p y‖ < ρ}
  have hpV : p ∈ V := by
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · exact mem_chart_source H p
    · simpa [hφ] using hW_φp
    · exact normalChartAt_source (I := I) g p
    · change normalChartAt (I := I) g p p ∈ A
      rw [normalChartAt_centre (I := I) g p]
      exact mem_of_mem_nhds hA_nhd
    · change ‖normalChartAt (I := I) g p p‖ < ρ
      rw [normalChartAt_centre (I := I) g p]
      simpa using hρ_pos
  have hV_nhd : V ∈ 𝓝 p := by
    have h1 : (chartAt H p).source ∈ 𝓝 p :=
      (chartAt H p).open_source.mem_nhds (mem_chart_source H p)
    have h2 : φ ⁻¹' W ∈ 𝓝 p :=
      (contMDiffAt_extChartAt (I := I) (n := ∞) (x := p)).continuousAt.preimage_mem_nhds
        (hW_open.mem_nhds (by simpa [hφ] using hW_φp))
    have h3 : (normalChartAt (I := I) g p).source ∈ 𝓝 p :=
      (normalChartAt_open_source (I := I) g p).mem_nhds (normalChartAt_source (I := I) g p)
    have h4 : (normalChartAt (I := I) g p) ⁻¹' A ∈ 𝓝 p := by
      have hA_p : A ∈ 𝓝 (normalChartAt (I := I) g p p) := by
        rw [normalChartAt_centre (I := I) g p]
        exact hA_nhd
      exact hNC_cont.preimage_mem_nhds hA_p
    have h5 : {y : M | ‖normalChartAt (I := I) g p y‖ < ρ} ∈ 𝓝 p := hBρ_p
    exact Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem h1 h2) h3) h4) h5
  obtain ⟨U₀, hU₀_sub, hU₀_open, hU₀_mem⟩ := _root_.mem_nhds_iff.mp hV_nhd
  have hident : ∀ y ∈ V,
      ψ (φ y) = normalChartAt (I := I) g p y ∧
        chartESectionRepr (I := I) p σ y = radialTransportChartRep g p η₀ (ψ (φ y)) 1 := by
    intro y hyV
    have hy_nc : y ∈ (normalChartAt (I := I) g p).source := hyV.1.1.2
    have hyA : normalChartAt (I := I) g p y ∈ A := hyV.1.2
    set x : E := normalChartAt (I := I) g p y with hx
    have hxA : x ∈ A := by simpa [hx] using hyA
    have hψΦx : ψ (extChartAt I p (expMapE g p x)) = x := hA x hxA
    have hy_exp : y = expMap (I := I) g p (show TangentSpace I p from (1 : ℝ) • x) := by
      have hsymm : (normalChartAt (I := I) g p).symm x = y := by
        rw [hx]
        exact normalChartAt_left_inv (I := I) g p hy_nc
      have htgt : x ∈ (normalChartAt (I := I) g p).symm.source := by
        rw [hx]
        have hmap : (normalChartAt (I := I) g p) y ∈ (normalChartAt (I := I) g p).target :=
          (normalChartAt (I := I) g p).map_source hy_nc
        simpa using hmap
      have hexp : (normalChartAt (I := I) g p).symm x =
          expMap (I := I) g p (show TangentSpace I p from x) :=
        normalChartAt_symm_apply (I := I) g p htgt
      rw [← hsymm, hexp]
      simp [one_smul]
    have hΦx : Φ x = φ y := by
      have hE : expMapE g p x = expMap (I := I) g p (show TangentSpace I p from (1 : ℝ) • x) := by
        simp [expMapE, one_smul]
      calc
        Φ x = φ (expMapE g p x) := by rw [hΦ]
        _ = φ (expMap (I := I) g p (show TangentSpace I p from (1 : ℝ) • x)) := by rw [hE]
        _ = φ y := by rw [← hy_exp]
    have hx_eq : ψ (φ y) = x := by
      rw [← hΦx]
      change ψ (Φ x) = x at hψΦx
      exact hψΦx
    refine ⟨?_, ?_⟩
    · simpa [hx] using hx_eq
    · exact radialTransportSection_chartE_repr_eq (I := I) g p η₀ hy_nc hx_eq
  let D : Set M := radialTransportSectionDomain (I := I) g p
  let U : Set M := U₀ ∩ D
  refine ⟨U, ?_, ?_, ?_⟩
  · exact Filter.inter_mem (hU₀_open.mem_nhds hU₀_mem)
      ((radialTransportSectionDomain_isOpen (I := I) g p).mem_nhds
        (mem_radialTransportSectionDomain_self (I := I) g p))
  · intro y hy
    exact hy.2
  · intro y hy
    have hy₀ : y ∈ U₀ := hy.1
    have hyV : y ∈ V := hU₀_sub hy₀
    have hy_src : y ∈ (chartAt H p).source := hyV.1.1.1.1
    have hyφW : φ y ∈ W := hyV.1.1.1.2
    have hyBρ : ‖normalChartAt (I := I) g p y‖ < ρ := hyV.2
    set x : E := normalChartAt (I := I) g p y with hx
    have hxρ : ‖x‖ < ρ := by simpa [hx] using hyBρ
    have hx_eq : ψ (φ y) = x := by
      have := (hident y hyV).1
      simpa [hx] using this
    have hR : ContDiffAt ℝ ∞ (fun x' : E => radialTransportChartRep g p η₀ x' 1) (ψ (φ y)) := by
      rw [hx_eq]
      have hx_ball : x ∈ ball (0 : E) ρ := by
        rw [mem_ball, dist_zero_right]
        exact hxρ
      exact hρ_cd.contDiffAt (isOpen_ball.mem_nhds hx_ball)
    have hFφ : ContMDiffAt I 𝓘(ℝ, E) ∞
        (fun y' : M => radialTransportChartRep g p η₀ (ψ (φ y')) 1) y := by
      have hψy : ContDiffAt ℝ ∞ ψ (φ y) :=
        hψ_cd.contDiffAt (hW_open.mem_nhds hyφW)
      have hF : ContDiffAt ℝ ∞ (fun ξ : E => radialTransportChartRep g p η₀ (ψ ξ) 1) (φ y) :=
        hR.comp (φ y) hψy
      have hF_md : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
          (fun ξ : E => radialTransportChartRep g p η₀ (ψ ξ) 1) (φ y) :=
        hF.contMDiffAt
      have hφy : ContMDiffAt I 𝓘(ℝ, E) ∞ φ y :=
        contMDiffAt_extChartAt' (I := I) (n := ∞) (x := p) (x' := y) hy_src
      exact hF_md.comp y hφy
    have hchart_y : ContMDiffAt I 𝓘(ℝ, E) ∞ (chartESectionRepr (I := I) p σ) y := by
      refine hFφ.congr_of_eventuallyEq ?_
      filter_upwards [hU₀_open.mem_nhds hy₀] with y' hy'
      exact (hident y' (hU₀_sub hy')).2
    have hy_base : y ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hy_src
    have hsec : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (T% σ) y :=
      (contMDiffAt_section_iff_chartE I p σ hy_base).mpr hchart_y
    exact hsec.contMDiffWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_localized_radial_transport_sections
    {ι : Type*} [Finite ι]
    (g : SmoothRiemannianMetric I M) (p : M) (v : ι → TangentSpace I p) :
    ∃ (χ : SmoothBumpFunction I p)
      (W : ι → ContMDiffSection I E ∞ (TangentSpace I : M → Type _)),
      tsupport (χ : M → ℝ) ⊆ radialTransportSectionDomain (I := I) g p ∧
      (∀ i y, W i y = χ y • radialTransportSection (I := I) g p (v i) y) ∧
      (∀ᶠ y in 𝓝 p, ∀ i, W i y = radialTransportSection (I := I) g p (v i) y) := by
  classical
  choose U hU_nhds _ hU_smooth using
    fun i : ι => radialTransportSection_contMDiffOn (I := I) g p (v i)
  let D : Set M := radialTransportSectionDomain (I := I) g p
  let V : Set M := interior (D ∩ ⋂ i : ι, U i)
  have hD_nhds : D ∈ 𝓝 p :=
    (radialTransportSectionDomain_isOpen (I := I) g p).mem_nhds
      (mem_radialTransportSectionDomain_self (I := I) g p)
  have hInter_nhds : (⋂ i : ι, U i) ∈ 𝓝 p := Filter.iInter_mem.mpr hU_nhds
  have hpV : p ∈ V :=
    mem_interior_iff_mem_nhds.mpr (Filter.inter_mem hD_nhds hInter_nhds)
  have hV_open : IsOpen V := isOpen_interior
  have hV_nhds : V ∈ 𝓝 p := hV_open.mem_nhds hpV
  obtain ⟨χ, hχ_tsupport⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (c := p) hV_nhds).ex_mem
  let W : ι → ContMDiffSection I E ∞ (TangentSpace I : M → Type _) := fun i =>
    ⟨fun y => χ y • radialTransportSection (I := I) g p (v i) y,
      ContMDiffOn.smul_section_of_tsupport
        χ.contMDiff.contMDiffOn hV_open hχ_tsupport
          ((hU_smooth i).mono (interior_subset.trans
            (inter_subset_right.trans (iInter_subset U i))))⟩
  refine ⟨χ, W, ?_, ?_, ?_⟩
  · exact hχ_tsupport.trans (interior_subset.trans inter_subset_left)
  · intro i y
    rfl
  · filter_upwards [χ.eventuallyEq_one] with y hy i
    change χ y • radialTransportSection (I := I) g p (v i) y = _
    have hy' : χ y = 1 := by simpa using hy
    rw [hy', one_smul]

end RadialTransportSectionSmooth

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
