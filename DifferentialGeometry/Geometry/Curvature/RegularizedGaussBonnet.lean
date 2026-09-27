import DifferentialGeometry.Geometry.Curvature.RegularizedDiskBoundary
import DifferentialGeometry.Geometry.Curvature.ConformalGaussBonnet



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry MeasureTheory Filter
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]




theorem gaussBonnet_regularizedDisk_trace
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ q ∈ Metric.closedBall 0 1, DiskMapConformalAt g U q)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hm : Monotone φ)
    (htrace : U ∘ circleMap 0 1 = γ ∘ φ)
    {a f : ℂ → ℝ} (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (han : ∀ z, 0 ≤ a z)
    (haeq : ∀ z ∈ Metric.closedBall 0 1, a =ᶠ[𝓝 z] diskMapConformalCoefficient g U)
    (hfν : ∀ z : ℂ, ‖z‖ = 1 → fderiv ℝ f z z = -1)
    {ε : ℝ} (hε : ε ≠ 0) :
    (∫ z in Metric.closedBall (0 : ℂ) 1,
      planeGaussianCurvature (regularizedConformalMetric a f ha hf han ε hε) z *
        tangentTwoJacobian (regularizedConformalMetric a f ha hf han ε hε)
          (x := z) (1 : ℂ) Complex.I) +
    (∫ θ in -Real.pi..Real.pi, regularizedConformalWeight a f ε (circleMap 0 1 θ) *
      diskMapTraceBoundaryDensity g U γ φ θ) = 2 * Real.pi := by
  have hgb := gaussBonnet_conformalDisk (contDiff_regularizedConformalLogFactor ha hf han hε)
  have hcircle (θ : ℝ) : Complex.polarCoord.symm (1, θ) = circleMap 0 1 θ := by
    simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
  simp_rw [hcircle] at hgb
  convert hgb using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  erw [hcircle θ]
  exact (regularizedDisk_boundaryDensity_eq_trace g hs hU hDs hconf hγ hi hφ hm htrace
    ha hf han θ (haeq _ (by simp [Metric.mem_closedBall, dist_zero_right]))
    (hfν _ (by simp)) hε).symm

end DifferentialGeometry.Geometry
