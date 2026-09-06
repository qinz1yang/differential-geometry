import DifferentialGeometry.Analysis.Heat.Parametrix.CoordinateCoefficient
import DifferentialGeometry.Geometry.Comparison.Volume.NormalJacobianLaplacian

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.HeatEquation

open Geometry.Riemannian (expMapC2Radius expMapC2Radius_pos
  expMap_contMDiffAt_infty_of_norm_lt_radius mem_expMapDiffeo_source_of_norm_lt_radius)
open Geometry.Riemannian.VolumeComparison Geometry.Riemannian.NormalCoordinates
open Geometry.Riemannian.Exponential Geometry.Connection Geometry.Operator
open DifferentialGeometry.Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space (TangentBundle I M)]

def heatParametrixCoefficient (g : SmoothRiemannianMetric I M) (p : M) : ℕ → M → ℝ :=
  heatParametrixCoefficientInCoordinates g
    (fun v => expMap g p ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm v))
    (normalChartAt g p) (normalJacobian g p)

@[simp] theorem heatParametrixCoefficient_zero
    (g : SmoothRiemannianMetric I M) (p q : M) :
    heatParametrixCoefficient g p 0 q =
      (Real.sqrt (normalJacobian g p (normalChartAt g p q)))⁻¹ := rfl

theorem heatParametrixCoefficient_succ
    (g : SmoothRiemannianMetric I M) (p : M) (k : ℕ) (q : M) :
    heatParametrixCoefficient g p (k + 1) q =
      (Real.sqrt (normalJacobian g p (normalChartAt g p q)))⁻¹ *
        radialIntegral k (fun v : E => Real.sqrt (normalJacobian g p v) *
          laplacian (LeviCivita g) g (heatParametrixCoefficient g p k)
            (expMap g p ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm v)))
          (normalChartAt g p q) := rfl

theorem heatParametrixCoefficient_zero_centre
    (g : SmoothRiemannianMetric I M) (p : M) : heatParametrixCoefficient g p 0 p = 1 := by
  simp only [heatParametrixCoefficient_zero, normalChartAt_centre, normalJacobian_inv_sqrt_zero]

theorem heatParametrixCoefficient_succ_centre
    (g : SmoothRiemannianMetric I M) (p : M) (k : ℕ) :
    heatParametrixCoefficient g p (k + 1) p =
      laplacian (LeviCivita g) g (heatParametrixCoefficient g p k) p / (k + 1 : ℝ) := by
  rw [heatParametrixCoefficient_succ, normalChartAt_centre, normalJacobian_inv_sqrt_zero,
    one_mul, radialIntegral_zero, normalJacobian_zero, Real.sqrt_one, one_mul, map_zero, expMap_zero]
  simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_comm]

variable [T2Space M]

theorem contMDiffOn_heatParametrixCoefficient
    (g : SmoothRiemannianMetric I M) (p : M) (k : ℕ) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (heatParametrixCoefficient g p k)
      ((normalChartAt g p).source ∩
        (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)) := by
  let U := Metric.ball (0 : E) (expMapC2Radius g p)
  let V := (normalChartAt g p).source ∩ (normalChartAt g p) ⁻¹' U
  have hV : IsOpen V :=
    (normalChartAt_contMDiffOn g p).continuousOn.isOpen_inter_preimage
      (normalChartAt g p).open_source Metric.isOpen_ball
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (normalChartAt g p) V := by
    apply (HCGCompactness.normalChartAt_contMDiffOn_infty g p).mono
    intro q hq
    refine ⟨normalChartAt g p q, hq.2, ?_⟩
    exact (normalChartAt_symm_apply g p ((normalChartAt g p).map_source hq.1)).symm.trans
      ((normalChartAt g p).left_inv hq.1)
  have hexp : ContMDiffOn 𝓘(ℝ, E) I ∞
      (fun v : E => expMap g p ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm v)) U := by
    intro v hv
    exact (expMap_contMDiffAt_infty_of_norm_lt_radius g p (by simpa [U] using hv)).contMDiffWithinAt
  have hexpV : MapsTo (fun v : E => expMap g p ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm v)) U V := by
    intro v hv
    have hsrc := mem_expMapDiffeo_source_of_norm_lt_radius g p (by simpa [U] using hv)
    have heq : expMapDiffeo g p v =
        expMap g p ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm v) :=
      expMapDiffeo_apply_eq g p hsrc
    change expMap g p ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm v) ∈ V
    rw [← heq]
    refine ⟨(expMapDiffeo g p).map_source hsrc, ?_⟩
    have hinv : normalChartAt g p (expMapDiffeo g p v) = v :=
      (expMapDiffeo g p).left_inv hsrc
    change normalChartAt g p (expMapDiffeo g p v) ∈ U
    rw [hinv]
    exact hv
  have hstar : StarConvex ℝ (0 : E) U :=
    (convex_ball (0 : E) (expMapC2Radius g p)).starConvex
      (Metric.mem_ball_self (expMapC2Radius_pos g p))
  exact contMDiffOn_heatParametrixCoefficientInCoordinates g Metric.isOpen_ball hstar hV
    hexp hchart hexpV (fun q hq => hq.2) (contDiffOn_normalJacobian g p)
    (fun v hv => normalJacobian_pos g p (mem_expMapDiffeo_source_of_norm_lt_radius g p
      (by simpa [U] using hv))) k

theorem heatParametrixCoefficient_one_centre
    (g : SmoothRiemannianMetric I M) (p : M) :
    heatParametrixCoefficient g p 1 p = (1 / 6 : ℝ) * Geometry.Curvature.metricScalarAt g p := by
  have h := heatParametrixCoefficient_succ_centre g p 0
  simp only [Nat.cast_zero, zero_add, div_one] at h
  exact h.trans (laplacian_normalJacobian_inv_sqrt_centre g p)

end DifferentialGeometry.Analysis.HeatEquation
