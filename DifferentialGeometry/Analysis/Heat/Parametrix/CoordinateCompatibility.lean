import DifferentialGeometry.Analysis.Heat.Parametrix.Coefficient
import DifferentialGeometry.Analysis.Integration.RadialIntegralCongruence
import DifferentialGeometry.Geometry.Comparison.Volume.NormalJacobianCompatibility

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch

open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral
open DifferentialGeometry.Analysis.HeatEquation
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem heatParametrixCoefficientInCoordinates_eventuallyEq
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) (hB0 : (0 : E) ∈ B.hom.source) (k : ℕ) :
    heatParametrixCoefficientInCoordinates g B.hom B.inv
        (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) k =ᶠ[𝓝 p]
      heatParametrixCoefficient g p k := by
  let J : E → ℝ := fun v => paramDensity g B.hom v / paramDensity g B.hom 0
  have hJ : J =ᶠ[𝓝 (0 : E)] normalJacobian g p :=
    B.paramDensity_ratio_eventuallyEq_normalJacobian_zero hB0
  have hchart := B.inv_eventuallyEq_normalChartAt_centre hB0
  have hBzero : B.hom 0 = p :=
    (B.eventuallyEq_expMapDiffeo_zero hB0).eq_of_nhds.trans (expMapDiffeo_zero g p)
  have hBp : p ∈ B.dom := by
    change p ∈ B.hom.target
    simpa only [hBzero] using B.hom.map_source hB0
  have hinvzero : B.inv p = 0 := hchart.eq_of_nhds.trans (normalChartAt_centre g p)
  have hinv : Tendsto B.inv (𝓝 p) (𝓝 (0 : E)) := by
    rw [← hinvzero]
    exact (B.inv_contMDiffOn.continuousOn.continuousAt
      (B.hom.open_target.mem_nhds hBp))
  have hforw : Tendsto (B.hom : E → M) (𝓝 (0 : E)) (𝓝 p) := by
    simpa only [ContinuousAt, hBzero] using
      B.hom.contMDiffOn_toFun.continuousOn.continuousAt (B.hom.open_source.mem_nhds hB0)
  have hexp : (B.hom : E → M) =ᶠ[𝓝 (0 : E)]
      fun v => expMap g p ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm v) := by
    filter_upwards [B.eventuallyEq_expMapDiffeo_zero hB0,
      Metric.ball_mem_nhds (0 : E) (expMapC2Radius_pos g p)] with v hv hvr
    rw [hv]
    exact expMapDiffeo_apply_eq g p (mem_expMapDiffeo_source_of_norm_lt_radius g p
      (by simpa using hvr))
  have hw : (fun q => (Real.sqrt (J (B.inv q)))⁻¹) =ᶠ[𝓝 p]
      fun q => (Real.sqrt (normalJacobian g p (normalChartAt g p q)))⁻¹ := by
    filter_upwards [hJ.comp_tendsto hinv, hchart] with q hq hc
    simp only [Function.comp_apply] at hq
    rw [hq, hc]
  let V : Set M := (normalChartAt g p).source ∩
    (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)
  have hV : IsOpen V :=
    (normalChartAt_contMDiffOn g p).continuousOn.isOpen_inter_preimage
      (normalChartAt g p).open_source Metric.isOpen_ball
  have hpV : p ∈ V := by
    refine ⟨normalChartAt_source g p, ?_⟩
    change normalChartAt g p p ∈ Metric.ball (0 : E) (expMapC2Radius g p)
    rw [normalChartAt_centre]
    exact Metric.mem_ball_self (expMapC2Radius_pos g p)
  change heatParametrixCoefficientInCoordinates g B.hom B.inv J k =ᶠ[𝓝 p]
    heatParametrixCoefficient g p k
  induction k with
  | zero => exact hw
  | succ k ih =>
    have hΔ : laplacian (LeviCivita g) g
        (heatParametrixCoefficientInCoordinates g B.hom B.inv J k) =ᶠ[𝓝 p]
        laplacian (LeviCivita g) g (heatParametrixCoefficient g p k) := by
      filter_upwards [ih.eventuallyEq_nhds, hV.mem_nhds hpV] with q hq hqV
      have hold := (contMDiffOn_heatParametrixCoefficient g p k q hqV).contMDiffAt
        (hV.mem_nhds hqV)
      exact laplacian_congr_of_eventuallyEq (LeviCivita g) g
        (hold.congr_of_eventuallyEq hq) hold hq
    have hi : (fun v => Real.sqrt (J v) * laplacian (LeviCivita g) g
        (heatParametrixCoefficientInCoordinates g B.hom B.inv J k) (B.hom v)) =ᶠ[𝓝 (0 : E)]
        fun v => Real.sqrt (normalJacobian g p v) * laplacian (LeviCivita g) g
          (heatParametrixCoefficient g p k)
          (expMap g p ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm v)) := by
      filter_upwards [hJ, hΔ.comp_tendsto hforw, hexp] with v hj hd he
      simp only [Function.comp_apply] at hd
      rw [hj, hd, he]
    have hr := (radialIntegral_eventuallyEq k hi).comp_tendsto hinv
    filter_upwards [hw, hr, hchart] with q hq hqr hqc
    simp only [Function.comp_apply] at hqr
    rw [heatParametrixCoefficientInCoordinates, heatParametrixCoefficient_succ, hq, hqr, hqc]

theorem contMDiffAt_heatParametrixCoefficientInCoordinates_centre
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) (hB0 : (0 : E) ∈ B.hom.source) (k : ℕ) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (heatParametrixCoefficientInCoordinates g B.hom B.inv
        (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) k) p := by
  let V : Set M := (normalChartAt g p).source ∩
    (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)
  have hV : IsOpen V :=
    (normalChartAt_contMDiffOn g p).continuousOn.isOpen_inter_preimage
      (normalChartAt g p).open_source Metric.isOpen_ball
  have hpV : p ∈ V := by
    refine ⟨normalChartAt_source g p, ?_⟩
    change normalChartAt g p p ∈ Metric.ball (0 : E) (expMapC2Radius g p)
    rw [normalChartAt_centre]
    exact Metric.mem_ball_self (expMapC2Radius_pos g p)
  exact ((contMDiffOn_heatParametrixCoefficient g p k p hpV).contMDiffAt
    (hV.mem_nhds hpV)).congr_of_eventuallyEq
      (B.heatParametrixCoefficientInCoordinates_eventuallyEq hB0 k)

theorem heatParametrixCoefficientInCoordinates_eventuallyEq_of_zero_mem
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B₁ B₂ : ExponentialInverseBranch g hEnorm p)
    (hB₁ : (0 : E) ∈ B₁.hom.source) (hB₂ : (0 : E) ∈ B₂.hom.source)
    (k : ℕ) :
    heatParametrixCoefficientInCoordinates g B₁.hom B₁.inv
        (fun v => paramDensity g B₁.hom v / paramDensity g B₁.hom 0) k =ᶠ[𝓝 p]
      heatParametrixCoefficientInCoordinates g B₂.hom B₂.inv
        (fun v => paramDensity g B₂.hom v / paramDensity g B₂.hom 0) k := by
  exact (B₁.heatParametrixCoefficientInCoordinates_eventuallyEq hB₁ k).trans
    (B₂.heatParametrixCoefficientInCoordinates_eventuallyEq hB₂ k).symm

end DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch
