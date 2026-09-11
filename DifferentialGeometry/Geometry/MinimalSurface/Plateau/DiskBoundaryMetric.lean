import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskConormal
import DifferentialGeometry.Geometry.Metric.CurveSpeedCalculus
import Mathlib.MeasureTheory.Integral.CircleIntegral



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem contMDiff_diskMapBoundary {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (U ∘ circleMap 0 1) := by
  intro θ
  have hz : circleMap 0 1 θ ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [Metric.mem_closedBall, dist_zero_right]
  exact ((hU _ (hDs hz)).contMDiffAt (hs.mem_nhds (hDs hz))).comp θ
    (contDiff_circleMap 0 1).contMDiff.contMDiffAt

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem mfderiv_diskMapBoundary {U : ℂ → M} {θ : ℝ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (circleMap 0 1 θ)) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (U ∘ circleMap 0 1) θ (1 : ℝ) =
      diskMapPartial U (circleMap 0 1 θ) (Complex.I * circleMap 0 1 θ) := by
  have h := congrArg (fun p : TangentBundle 𝓘(ℝ, E) M => (p.2 : E))
    (tangent_velocity_comp hU (differentiable_circleMap 0 1 θ))
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (U ∘ circleMap 0 1) θ (1 : ℝ) =
    diskMapPartial U (circleMap 0 1 θ) (deriv (circleMap 0 1) θ) at h
  simpa only [deriv_circleMap, mul_comm] using h



theorem riemannianCurveSpeed_diskMapBoundary
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {θ : ℝ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (circleMap 0 1 θ))
    (hconf : DiskMapConformalAt g U (circleMap 0 1 θ)) :
    riemannianCurveSpeed g (U ∘ circleMap 0 1) θ =
      Real.sqrt (diskMapConformalCoefficient g U (circleMap 0 1 θ)) := by
  unfold riemannianCurveSpeed
  erw [mfderiv_diskMapBoundary hU]
  exact hconf.boundary_arclengthDensity (by simp)

end DifferentialGeometry.Geometry
