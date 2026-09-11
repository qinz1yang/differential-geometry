import DifferentialGeometry.Geometry.MinimalSurface.Plateau.NonconstantCoefficient
import DifferentialGeometry.Analysis.Integration.Measure.SmoothDensity
import DifferentialGeometry.Geometry.Curvature.DiskRegularizer



noncomputable section

open Set Bundle Manifold DifferentialGeometry MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]




theorem SmoothDiskExtension.exists_curvature_density
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : C(closedDisk, M)} {U : ℂ → M}
    (hu : SmoothDiskExtension (E := E) u U)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U z)
    (hnon : ¬ ∃ c : M, ∀ z : closedDisk, u z = c) :
    ∃ κ : ℂ → ℝ, ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧
      tsupport κ ⊆ Metric.ball (0 : ℂ) 1 ∩
        (diskMapConformalCoefficient g U) ⁻¹' Ioi 0 ∧
      (∀ z, 0 ≤ κ z) ∧ (∫ z, κ z) = 2 * Real.pi := by
  obtain ⟨z, hz, hpos⟩ := hu.exists_pos_coefficient g hconf hnon
  obtain ⟨_, N, hN, hDN, hU⟩ := hu
  have hc := ((contDiffOn_diskMapConformalCoefficient g hN hU).mono
    (Metric.ball_subset_closedBall.trans hDN)).continuousOn
  exact exists_smooth_nonneg_density
    (hc.isOpen_inter_preimage Metric.isOpen_ball isOpen_Ioi) ⟨z, hz, hpos⟩
    (mul_pos (by norm_num) Real.pi_pos)




theorem SmoothDiskExtension.exists_curvature_regularizer
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : C(closedDisk, M)} {U : ℂ → M}
    (hu : SmoothDiskExtension (E := E) u U)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U z)
    (hnon : ¬ ∃ c : M, ∀ z : closedDisk, u z = c) :
    ∃ κ F : ℂ → ℝ, ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧
      tsupport κ ⊆ Metric.ball (0 : ℂ) 1 ∩
        (diskMapConformalCoefficient g U) ⁻¹' Ioi 0 ∧
      (∀ z, 0 ≤ κ z) ∧ (∫ z, κ z) = 2 * Real.pi ∧ ContDiff ℝ ∞ F ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, F =ᶠ[𝓝 z] diskRegularizerPotential κ) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, -Laplacian.laplacian F z = κ z) ∧
      (∀ z : ℂ, ‖z‖ = 1 → fderiv ℝ F z z = -1) := by
  obtain ⟨κ, hκ, hc, hs, hn, hmass⟩ := hu.exists_curvature_density g hconf hnon
  obtain ⟨F, hF, heq, hK, hk⟩ := exists_diskRegularizer_metric hc hκ
    (hs.trans inter_subset_left) hmass
  refine ⟨κ, F, hκ, hc, hs, hn, hmass, hF, heq, ?_, ?_⟩
  · intro z hz
    simpa only [planeGaussianCurvature_mul_areaDensity hF] using hK z hz
  · intro z hz
    have h := hk z hz
    rw [conformalCircleGeodesicCurvature_eq hF hz] at h
    have h' := (mul_eq_zero.mp h).resolve_left (Real.exp_ne_zero _)
    linarith

end DifferentialGeometry.Geometry
