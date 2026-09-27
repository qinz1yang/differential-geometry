import DifferentialGeometry.Geometry.Curvature.DiskTraceDensity
import DifferentialGeometry.Geometry.Curvature.RegularizedConformalDisk



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]




theorem regularizedDisk_boundaryDensity_eq_trace
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ q ∈ Metric.closedBall 0 1, DiskMapConformalAt g U q)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hm : Monotone φ)
    (htrace : U ∘ circleMap 0 1 = γ ∘ φ)
    {a f : ℂ → ℝ} (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f)
    (han : ∀ z, 0 ≤ a z) (θ : ℝ)
    (haeq : a =ᶠ[𝓝 (circleMap 0 1 θ)] diskMapConformalCoefficient g U)
    (hfν : fderiv ℝ f (circleMap 0 1 θ) (circleMap 0 1 θ) = -1)
    {ε : ℝ} (hε : ε ≠ 0) :
    let z := circleMap 0 1 θ
    conformalCircleGeodesicCurvature (regularizedConformalLogFactor a f ε)
        (contDiff_regularizedConformalLogFactor ha hf han hε) z *
      Real.sqrt ((regularizedConformalMetric a f ha hf han ε hε).inner z
        (Complex.I * z) (Complex.I * z)) =
      regularizedConformalWeight a f ε z * diskMapTraceBoundaryDensity g U γ φ θ := by
  dsimp only
  rw [regularizedConformalMetric_boundaryDensity ha hf han hε (by simp) hfν]
  by_cases hz : a (circleMap 0 1 θ) = 0
  · simp [regularizedConformalWeight, hz]
  · have hap : 0 < diskMapConformalCoefficient g U (circleMap 0 1 θ) := by
      rw [← haeq.eq_of_nhds]
      exact lt_of_le_of_ne (han _) (Ne.symm hz)
    have hb : diskMapTraceBoundaryDensity g U γ φ θ =
        1 + fderiv ℝ (diskMapConformalCoefficient g U) (circleMap 0 1 θ) (circleMap 0 1 θ) /
          (2 * diskMapConformalCoefficient g U (circleMap 0 1 θ)) :=
      diskMapTraceCurvature_density g hs hU hDs hconf hγ hi hφ hm htrace θ hap
    rw [hb, fderiv.log (ha.differentiable (by simp) _) hz]
    simp only [_root_.smul_apply, smul_eq_mul]
    rw [haeq.fderiv_eq, haeq.eq_of_nhds]
    ring

end DifferentialGeometry.Geometry
