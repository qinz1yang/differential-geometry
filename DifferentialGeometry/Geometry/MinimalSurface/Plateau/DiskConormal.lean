import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricCoefficient



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry InnerProductSpace
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



def diskMapInwardConormal (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z : ℂ) : TangentSpace 𝓘(ℝ, E) (U z) :=
  -(Real.sqrt (diskMapConformalCoefficient g U z))⁻¹ • diskMapPartial U z z


theorem DiskMapConformalAt.boundary_arclengthDensity
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (hc : DiskMapConformalAt g U z) (hz : ‖z‖ = 1) :
    Real.sqrt (g.inner (U z) (diskMapPartial U z (Complex.I * z))
      (diskMapPartial U z (Complex.I * z))) =
      Real.sqrt (diskMapConformalCoefficient g U z) := by
  rw [hc.inner_partials, real_inner_self_eq_norm_sq, norm_mul, Complex.norm_I, hz]
  simp


theorem diskMapInwardConormal_eq_zero
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (hz : diskMapConformalCoefficient g U z = 0) : diskMapInwardConormal g U z = 0 := by
  simp [diskMapInwardConormal, hz]


theorem DiskMapConformalAt.inwardConormal_unit
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (hc : DiskMapConformalAt g U z) (hz : ‖z‖ = 1)
    (ha : 0 < diskMapConformalCoefficient g U z) :
    g.inner (U z) (diskMapInwardConormal g U z) (diskMapInwardConormal g U z) = 1 := by
  unfold diskMapInwardConormal
  simp only [map_smul, smul_apply, smul_eq_mul, hc.inner_partials,
    real_inner_self_eq_norm_sq, hz, one_pow, mul_one]
  have hs := Real.sq_sqrt ha.le
  have hn := ne_of_gt (Real.sqrt_pos.mpr ha)
  field_simp [hn, hs]
  exact hs.symm



theorem DiskMapConformalAt.inwardConormal_orthogonal
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (hc : DiskMapConformalAt g U z) :
    g.inner (U z) (diskMapPartial U z (Complex.I * z)) (diskMapInwardConormal g U z) = 0 := by
  unfold diskMapInwardConormal
  simp only [map_smul, smul_eq_mul, hc.inner_partials]
  have horth : inner ℝ (Complex.I * z) z = 0 := by
    simp [Complex.inner, Complex.mul_re, Complex.mul_im, mul_comm]
  rw [horth]
  ring




theorem DiskMapConformalAt.inwardConormal_flux
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (hc : DiskMapConformalAt g U z) (V : TangentSpace 𝓘(ℝ, E) (U z)) :
    g.inner (U z) V (diskMapInwardConormal g U z) *
      Real.sqrt (diskMapConformalCoefficient g U z) =
      -g.inner (U z) V (diskMapPartial U z z) := by
  by_cases ha : diskMapConformalCoefficient g U z = 0
  · have hd := hc.coefficient_eq_zero_iff.mp ha
    simp only [diskMapInwardConormal_eq_zero ha, map_zero, zero_mul, diskMapPartial, hd]
    change 0 = -g.inner (U z) V 0
    simp
  · have hp := lt_of_le_of_ne (diskMapConformalCoefficient_nonneg g U z) (Ne.symm ha)
    have hn := ne_of_gt (Real.sqrt_pos.mpr hp)
    unfold diskMapInwardConormal
    simp only [map_smul, smul_eq_mul]
    field_simp

end DifferentialGeometry.Geometry
