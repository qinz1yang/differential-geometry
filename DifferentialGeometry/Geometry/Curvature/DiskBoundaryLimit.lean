import DifferentialGeometry.Geometry.Curvature.DiskTraceDensity
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Regularization.Vanishing



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry MeasureTheory Filter
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]




theorem tendsto_intervalIntegral_diskMapTraceBoundaryDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ q ∈ Metric.closedBall 0 1, DiskMapConformalAt g U q)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (htrace : U ∘ circleMap 0 1 = γ ∘ φ)
    {a f : ℂ → ℝ} (ha : Measurable a) (hf : Measurable f) (han : ∀ z, 0 ≤ a z)
    (haeq : ∀ z ∈ Metric.closedBall 0 1, a z = diskMapConformalCoefficient g U z) (l r : ℝ) :
    Tendsto (fun ε : ℝ => ∫ θ in l..r,
      regularizedConformalWeight a f ε (circleMap 0 1 θ) * diskMapTraceBoundaryDensity g U γ φ θ)
      (𝓝 0) (𝓝 (∫ θ in l..r, diskMapTraceBoundaryDensity g U γ φ θ)) := by
  have hzero (θ : ℝ) (hz : a (circleMap 0 1 θ) = 0) :
      diskMapTraceBoundaryDensity g U γ φ θ = 0 := by
    apply diskMapTraceBoundaryDensity_eq_zero
    rw [← haeq _ (by simp [Metric.mem_closedBall, dist_zero_right])]
    exact hz
  have hB := intervalIntegrable_diskMapTraceBoundaryDensity g hs hU hDs hconf hγ hi hφ htrace l r
  have hlim (ν : Measure ℝ) (hb : Integrable (diskMapTraceBoundaryDensity g U γ φ) ν) :=
    tendsto_integral_regularizedConformalWeight_comp_of_zero (measurable_circleMap 0 1) ha hf
      (Eventually.of_forall (fun θ => han _)) hb (Eventually.of_forall hzero)
  exact (hlim _ hB.1).sub (hlim _ hB.2)

end DifferentialGeometry.Geometry
