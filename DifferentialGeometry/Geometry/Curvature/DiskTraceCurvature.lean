import DifferentialGeometry.Geometry.Curvature.DiskBoundary
import DifferentialGeometry.Geometry.Curvature.CurveReparametrization
import Mathlib.Analysis.Calculus.Deriv.Slope



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
theorem deriv_trace_pos_of_coefficient_pos
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {γ : ℝ → M} {φ : ℝ → ℝ} {θ : ℝ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (circleMap 0 1 θ))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ (φ θ))
    (hφ : DifferentiableAt ℝ φ θ) (hm : Monotone φ)
    (htrace : U ∘ circleMap 0 1 = γ ∘ φ)
    (hconf : DiskMapConformalAt g U (circleMap 0 1 θ))
    (ha : 0 < diskMapConformalCoefficient g U (circleMap 0 1 θ)) :
    0 < deriv φ θ := by
  have hspeed : 0 < riemannianCurveSpeed g (U ∘ circleMap 0 1) θ := by
    rw [riemannianCurveSpeed_diskMapBoundary g hU hconf]
    exact Real.sqrt_pos.mpr ha
  by_contra hn
  have hz : deriv φ θ = 0 := le_antisymm (le_of_not_gt hn) hm.deriv_nonneg
  rw [htrace, riemannianCurveSpeed_reparam g hγ hφ, hz, abs_zero, zero_mul] at hspeed
  exact lt_irrefl 0 hspeed




theorem diskMapTraceCurvature_density
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ q ∈ Metric.closedBall 0 1, DiskMapConformalAt g U q)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hm : Monotone φ)
    (htrace : U ∘ circleMap 0 1 = γ ∘ φ)
    (θ : ℝ) (ha : 0 < diskMapConformalCoefficient g U (circleMap 0 1 θ)) :
    let z := circleMap 0 1 θ
    g.inner (U z) (riemannianCurveCurvature g γ (φ θ) : E) (diskMapInwardConormal g U z) *
      Real.sqrt (diskMapConformalCoefficient g U z) =
        1 + fderiv ℝ (diskMapConformalCoefficient g U) z z /
          (2 * diskMapConformalCoefficient g U z) := by
  have hz : circleMap 0 1 θ ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [Metric.mem_closedBall, dist_zero_right]
  have hpos := deriv_trace_pos_of_coefficient_pos g
    (((hU _ (hDs hz)).contMDiffAt (hs.mem_nhds (hDs hz))).mdifferentiableAt (by simp))
    (hγ.mdifferentiable (by simp) _) (hφ.differentiable (by simp) _) hm htrace (hconf _ hz) ha
  have hcurv : (riemannianCurveCurvature g (U ∘ circleMap 0 1) θ : E) =
      riemannianCurveCurvature g γ (φ θ) := by
    rw [htrace]
    exact riemannianCurveCurvature_reparam_pos g hγ hi hφ hpos
  change g.inner _ _ _ * _ = _
  rw [← hcurv]
  exact diskMapBoundaryCurvature_density g hs hU hDs hconf θ ha

end DifferentialGeometry.Geometry
