import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurck.PullbackEvaluationChainRule
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Spectrum.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.Analysis.Spectral.MetricRealization

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem forcing_continuous_interior
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (u₁ : ℝ → TensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
    (N_cont : TensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      TensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
    (hN_cont : Continuous N_cont)
    (hcont : ∀ ε : ℝ, 0 < ε → ContinuousOn u₁ (Set.Icc ε T))
    :
    ∀ ε : ℝ, 0 < ε →
      ContinuousOn (fun s => (N_cont (u₁ s) :
        TensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))) (Set.Icc ε T) := by
  intro ε hε
  exact hN_cont.comp_continuousOn (hcont ε hε)

open MeasureTheory in
theorem permode_sum_hasderivat
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (u₂ : ℝ → TensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (u₁ : ℝ → TensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
    (hderiv_ae : (u.deriv : ℝ → TensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
        =ᵐ[timeMeasure T]
      (fun s => scaleLaplacianFun (I := I) (M := M) (u₂ s) +
        deTurckGeometricN (I := I) g_bg a (u₁ s)))
    (hRHS_cont : ContinuousOn
      (fun s => scaleLaplacianFun (I := I) (M := M) (u₂ s) +
        deTurckGeometricN (I := I) g_bg a (u₁ s)) (Set.Ioo (0 : ℝ) T)) :
    ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun r => (timeH1.toFun u r : TensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)))
        (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
          deTurckGeometricN (I := I) g_bg a (u₁ s)) s := by
  classical
  set RHS : ℝ → TensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) :=
    fun s => scaleLaplacianFun (I := I) (M := M) (u₂ s) +
      deTurckGeometricN (I := I) g_bg a (u₁ s) with hRHS_def
  intro s hs
  obtain ⟨hs0, hsT⟩ := hs
  have hsmem : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs0, hsT⟩
  have hTpos : (0 : ℝ) ≤ T := hs0.le.trans hsT.le
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hTpos⟩
  have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs0.le, hsT.le⟩
  have hderiv_int : IntervalIntegrable (fun r => u.deriv r) volume 0 s :=
    u.intervalIntegrable_deriv h0mem hsIcc
  have hRHS_int : IntervalIntegrable RHS volume 0 s := by
    have hsub : Set.uIoc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans (Set.uIcc_subset_Icc h0mem hsIcc)
    have hae := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hderiv_ae
    exact hderiv_int.congr_ae hae
  have hRHS_at : ContinuousAt RHS s :=
    hRHS_cont.continuousAt (isOpen_Ioo.mem_nhds hsmem)
  have hRHS_meas : StronglyMeasurableAtFilter RHS (𝓝 s) volume :=
    hRHS_cont.stronglyMeasurableAtFilter isOpen_Ioo s hsmem
  have hftc_RHS : HasDerivAt (fun r => ∫ x in (0 : ℝ)..r, RHS x) (RHS s) s :=
    intervalIntegral.integral_hasDerivAt_right hRHS_int hRHS_meas hRHS_at
  have heq : (fun r => ∫ x in (0 : ℝ)..r, u.deriv x)
      =ᶠ[nhds s] fun r => ∫ x in (0 : ℝ)..r, RHS x := by
    filter_upwards [Ioo_mem_nhds hs0 hsT] with r hr
    refine intervalIntegral.integral_congr_ae ?_
    have hrIcc : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le⟩
    have hsub : Set.uIoc (0 : ℝ) r ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans (Set.uIcc_subset_Icc h0mem hrIcc)
    have hae := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hderiv_ae
    rw [ae_restrict_iff' measurableSet_uIoc] at hae
    filter_upwards [hae] with x hx hxmem
    exact hx hxmem
  have hftc_u : HasDerivAt (fun r => ∫ x in (0 : ℝ)..r, u.deriv x) (RHS s) s :=
    hftc_RHS.congr_of_eventuallyEq heq
  have hconst : HasDerivAt
      (fun r => (timeH1.toFun u r : TensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)))
      (RHS s) s := by
    have h := hftc_u.const_add u.init
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with r
    rw [timeH1.toFun_apply]
  exact hconst

end DifferentialGeometry.PDE.RicciFlow
