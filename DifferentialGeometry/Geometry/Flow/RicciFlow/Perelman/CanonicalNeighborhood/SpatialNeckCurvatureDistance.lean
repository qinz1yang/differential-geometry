import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckChart
import Mathlib.Topology.MetricSpace.Completion

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [MetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x : M}

theorem SpatialNeck.scalar_distance_lower_bound (nk : SpatialNeck g eps x)
    (hsmall : eps ≤ 1 / 4323) (q : UniformSpace.Completion M)
    {c : ℝ}
    (hquant : c ^ 2 ≤ metricScalarAt g x * dist q (x : UniformSpace.Completion M) ^ 2)
    {y : M} (hy : y ∈ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹))
    (hnear : dist x y ≤ c / (2 * Real.sqrt (metricScalarAt g x))) :
    (1 - 4323 * eps) * c ^ 2 / 4 ≤
      metricScalarAt g y * dist q (y : UniformSpace.Completion M) ^ 2 := by
  have hc : 0 ≤ c := by
    have h := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2)
      (Real.sqrt_pos.mpr nk.Q_pos))).mp (dist_nonneg.trans hnear)
    simpa only [zero_mul] using h
  have hroot : c ≤ Real.sqrt (metricScalarAt g x) * dist q (x : UniformSpace.Completion M) := by
    apply (sq_le_sq₀ hc (mul_nonneg (Real.sqrt_nonneg _) dist_nonneg)).mp
    rw [mul_pow, Real.sq_sqrt nk.Q_pos.le]
    exact hquant
  have hnear' : dist x y ≤ dist q (x : UniformSpace.Completion M) / 2 := by
    apply hnear.trans
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.sqrt_pos.mpr nk.Q_pos))).mpr
    linarith only [hroot]
  have htriangle := dist_triangle q (y : UniformSpace.Completion M) (x : UniformSpace.Completion M)
  rw [UniformSpace.Completion.dist_eq, dist_comm y x] at htriangle
  have hdist : dist q (x : UniformSpace.Completion M) / 2 ≤
      dist q (y : UniformSpace.Completion M) := by linarith only [htriangle, hnear']
  have hfactor : 0 ≤ 1 - 4323 * eps := by linarith only [hsmall]
  have hlow := (nk.scalar_bounds_on_image_window hy).1
  have hnonneg : 0 ≤ metricScalarAt g y :=
    (mul_nonneg hfactor nk.Q_pos.le).trans hlow
  calc
    (1 - 4323 * eps) * c ^ 2 / 4 ≤
        ((1 - 4323 * eps) * metricScalarAt g x) *
          (dist q (x : UniformSpace.Completion M) / 2) ^ 2 := by
      nlinarith only [mul_le_mul_of_nonneg_left hquant hfactor]
    _ ≤ metricScalarAt g y * dist q (y : UniformSpace.Completion M) ^ 2 :=
      mul_le_mul hlow (pow_le_pow_left₀ (div_nonneg dist_nonneg (by norm_num)) hdist 2)
        (sq_nonneg _) hnonneg

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
