import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import DifferentialGeometry.Topology.MetricSpace.GeodesicSeparator
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

theorem SpatialNeck.central_sphere_dist_lt_endpoint_sum (nk : SpatialNeck g eps x)
    (hmetric : ∀ y z : M, edist y z = riemannianEDistOf g y z)
    (q : UniformSpace.Completion M)
    (hquant : 196 < metricScalarAt g x * dist q (x : UniformSpace.Completion M) ^ 2)
    {y z : M} (hy : y ∈ nk.map '' (univ ×ˢ {(0 : ℝ)}))
    (hz : z ∈ nk.map '' (univ ×ˢ {(0 : ℝ)})) :
    dist (y : UniformSpace.Completion M) (z : UniformSpace.Completion M) <
      dist (y : UniformSpace.Completion M) q + dist q (z : UniformSpace.Completion M) := by
  have hQ := Real.sqrt_pos.mpr nk.Q_pos
  have hroot : 14 < Real.sqrt (metricScalarAt g x) * dist q (x : UniformSpace.Completion M) := by
    apply (sq_lt_sq₀ (by norm_num) (mul_nonneg hQ.le dist_nonneg)).mp
    rw [mul_pow, Real.sq_sqrt nk.Q_pos.le]
    norm_num only [show (14 : ℝ) ^ 2 = 196 by norm_num]
    exact hquant
  have hfar : 2 * (7 / Real.sqrt (metricScalarAt g x)) < dist (x : UniformSpace.Completion M) q := by
    rw [dist_comm, ← mul_div_assoc]
    apply (div_lt_iff₀ hQ).mpr
    linarith only [hroot]
  have hball (w : M) (hw : w ∈ nk.map '' (univ ×ˢ {(0 : ℝ)})) :
      (w : UniformSpace.Completion M) ∈ Metric.closedBall (x : UniformSpace.Completion M)
        (7 / Real.sqrt (metricScalarAt g x)) := by
    have hb := nk.central_sphere_subset_closedBall hw
    change riemannianEDistOf g x w ≤ ENNReal.ofReal (7 / Real.sqrt (metricScalarAt g x)) at hb
    rw [← hmetric, edist_dist] at hb
    rw [Metric.mem_closedBall, UniformSpace.Completion.dist_eq, dist_comm]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
  exact Metric.dist_lt_dist_add_dist_of_mem_closedBall (hball y hy) (hball z hz) hfar


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
