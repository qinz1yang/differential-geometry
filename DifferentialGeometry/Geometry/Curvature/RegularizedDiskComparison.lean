import DifferentialGeometry.Geometry.Curvature.DiskGauss
import DifferentialGeometry.Geometry.Curvature.RegularizedConformalDisk



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter InnerProductSpace
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem regularizedConformalMetric_eq_pullback_add
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {z : ℂ}
    (hconf : DiskMapConformalAt g U z)
    {a f : ℂ → ℝ} (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (han : ∀ z, 0 ≤ a z)
    {ε : ℝ} (hε : ε ≠ 0) (heq : a z = diskMapConformalCoefficient g U z) (v w : ℂ) :
    (regularizedConformalMetric a f ha hf han ε hε).inner z v w =
      g.inner (U z) (diskMapPartial U z v) (diskMapPartial U z w) +
        ε ^ 2 * (conformalEuclideanMetric f hf).inner z v w := by
  rw [regularizedConformalMetric_inner, hconf.inner_partials, conformalEuclideanMetric_inner]
  unfold regularizedConformalCoefficient
  rw [heq]
  ring





theorem regularizedDisk_curvatureDensity_le_sectional
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hconf : ∀ q ∈ s, DiskMapConformalAt g U q)
    (hharm : ∀ q ∈ s, diskMapTension g U q = 0)
    {a f : ℂ → ℝ} (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (han : ∀ z, 0 ≤ a z)
    {ε : ℝ} (hε : ε ≠ 0) {z : ℂ} (hz : z ∈ s)
    (heq : a =ᶠ[𝓝 z] diskMapConformalCoefficient g U) :
    planeGaussianCurvature (regularizedConformalMetric a f ha hf han ε hε) z *
        tangentTwoJacobian (regularizedConformalMetric a f ha hf han ε hε)
          (x := z) (1 : ℂ) Complex.I ≤
      regularizedConformalWeight a f ε z *
        (sectionalCurvature g (U z) (diskMapPartial U z 1) (diskMapPartial U z Complex.I) *
          diskMapConformalCoefficient g U z) +
      (1 - regularizedConformalWeight a f ε z) * (-Laplacian.laplacian f z) := by
  apply (regularizedConformalMetric_curvatureDensity_le ha hf han hε z).trans
  refine add_le_add ?_ le_rfl
  by_cases hzero : a z = 0
  · have hw : regularizedConformalWeight a f ε z = 0 := by
      simp [regularizedConformalWeight, hzero]
    rw [if_pos hzero, hw, zero_mul]
  · rw [if_neg hzero]
    apply mul_le_mul_of_nonneg_left _ (regularizedConformalWeight_mem_Icc (han z) hε).1
    have hpos : 0 < diskMapConformalCoefficient g U z := by
      rw [← heq.eq_of_nhds]
      exact lt_of_le_of_ne (han z) (Ne.symm hzero)
    have hlog : (fun q => Real.log (a q)) =ᶠ[𝓝 z]
        (fun q => Real.log (diskMapConformalCoefficient g U q)) := heq.fun_comp Real.log
    rw [(laplacian_congr_nhds hlog).eq_of_nhds]
    exact diskMap_curvature_density_le_sectional g hs hU hconf hharm hz hpos

end DifferentialGeometry.Geometry
