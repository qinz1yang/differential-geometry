import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricCoefficient
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Ball
import Mathlib.Analysis.Normed.Module.Ball.Pointwise



noncomputable section

open Set Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]





theorem SmoothDiskExtension.exists_nonneg_coefficient_extension
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : C(closedDisk, M)} {U : ℂ → M}
    (hu : SmoothDiskExtension (E := E) u U) :
    ∃ A : ℂ → ℝ, ContDiff ℝ ∞ A ∧ HasCompactSupport A ∧ (∀ z, 0 ≤ A z) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        A =ᶠ[𝓝 z] diskMapConformalCoefficient g U := by
  obtain ⟨_, N, hN, hDN, hU⟩ := hu
  obtain ⟨δ, hδ, hδN⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_cthickening_subset_open hN hDN
  rw [cthickening_closedBall hδ.le (by norm_num : (0 : ℝ) ≤ 1)] at hδN
  have hball : Metric.ball (0 : ℂ) (δ + 1) ⊆ N := Metric.ball_subset_closedBall.trans hδN
  exact exists_contDiff_nonneg_compactSupport_eq_near_closedBall (by norm_num)
    (by linarith : (1 : ℝ) < δ + 1)
    ((contDiffOn_diskMapConformalCoefficient g hN hU).mono hball)
    (fun z _ => diskMapConformalCoefficient_nonneg g U z)

end DifferentialGeometry.Geometry
