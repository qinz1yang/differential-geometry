import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricCoefficient
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Geometry.Metric.ZeroDerivative



noncomputable section

open Set Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]





theorem SmoothDiskExtension.exists_pos_coefficient
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : C(closedDisk, M)} {U : ℂ → M}
    (hu : SmoothDiskExtension (E := E) u U)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U z)
    (hnon : ¬ ∃ c : M, ∀ z : closedDisk, u z = c) :
    ∃ z ∈ Metric.ball (0 : ℂ) 1, 0 < diskMapConformalCoefficient g U z := by
  by_contra hpos
  push Not at hpos
  obtain ⟨heq, N, hN, hDN, hU⟩ := hu
  have hder : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z = 0 := by
    intro z hz
    exact (hconf z hz).coefficient_eq_zero_iff.mp
      (le_antisymm (hpos z hz) (diskMapConformalCoefficient_nonneg g U z))
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hconst : EqOn U (fun _ => U 0) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    exact eq_of_mfderiv_eq_zero_on_convex g hN (hU.of_le (by simp))
      (Metric.ball_subset_closedBall.trans hDN) (convex_ball (0 : ℂ) 1) hder hz h0
  have hclosed : EqOn U (fun _ => U 0) (Metric.closedBall (0 : ℂ) 1) :=
    hconst.of_subset_closure (hU.continuousOn.mono hDN) continuousOn_const
      Metric.ball_subset_closedBall (by rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)])
  apply hnon
  exact ⟨U 0, fun z => (heq z).symm.trans (hclosed z.property)⟩

end DifferentialGeometry.Geometry
