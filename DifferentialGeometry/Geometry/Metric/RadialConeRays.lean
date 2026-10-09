import DifferentialGeometry.Geometry.Metric.RadialConeIdentities

set_option autoImplicit false

noncomputable section
open scoped NNReal

namespace GC.MetricGeometry

variable {X : Type*} [MetricSpace X]

namespace RadialConeData

variable {p : X} (H : RadialConeData p)

noncomputable def unitRay (x : X) (t : ℝ≥0) : X := H.map (t / nndist p x) x

theorem unitRay_zero (x : X) : H.unitRay x 0 = p := by
  simp only [unitRay, zero_div, H.map_zero]

theorem unitRay_through {x : X} (hx : x ≠ p) : H.unitRay x (nndist p x) = x := by
  have hn : nndist p x ≠ 0 := by simpa only [ne_eq, nndist_eq_zero] using hx.symm
  simp only [unitRay, div_self hn, H.map_one]

theorem unitRay_isometry {x : X} (hx : x ≠ p) : Isometry (H.unitRay x) := by
  have hr : dist p x ≠ 0 := dist_ne_zero.mpr hx.symm
  apply Isometry.of_dist_eq
  intro s t
  change dist (H.map (s / nndist p x) x) (H.map (t / nndist p x) x) = |(s : ℝ) - t|
  rw [H.same_ray_dist]
  simp only [NNReal.coe_div, coe_nndist]
  rw [← sub_div, abs_div, abs_of_nonneg dist_nonneg, div_mul_cancel₀ _ hr]

theorem eq_map_of_radial_distances (t : ℝ≥0) (x z : X)
    (hz : dist p z = (t : ℝ) * dist p x)
    (hzx : dist z x = (1 - (t : ℝ)) * dist p x) : z = H.map t x := by
  have hh := H.dist_sq 1 t z x
  rw [H.map_one] at hh
  norm_num only [NNReal.coe_one, one_pow, one_mul] at hh
  unfold radialConeKernel at hh
  rw [hz, hzx] at hh
  have he : dist z (H.map t x) ^ 2 = 0 := by rw [hh]; ring
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg (x := z) (y := H.map t x)]


theorem eq_map_of_radial_distances_abs (t : ℝ≥0) (x z : X)
    (hz : dist p z = (t : ℝ) * dist p x)
    (hzx : dist z x = |1 - (t : ℝ)| * dist p x) : z = H.map t x := by
  have hh := H.dist_sq 1 t z x
  rw [H.map_one] at hh
  norm_num only [NNReal.coe_one, one_pow, one_mul] at hh
  unfold radialConeKernel at hh
  rw [hz, hzx] at hh
  simp only [mul_pow, sq_abs] at hh
  have he : dist z (H.map t x) ^ 2 = 0 := by rw [hh]; ring
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg (x := z) (y := H.map t x)]

theorem unitRay_dist_apex {x : X} (hx : x ≠ p) (t : ℝ≥0) :
    dist p (H.unitRay x t) = (t : ℝ) := by
  conv_lhs => arg 1; rw [← H.unitRay_zero x]
  rw [(H.unitRay_isometry hx).dist_eq]
  change |(0 : ℝ) - t| = (t : ℝ)
  rw [zero_sub, abs_neg, abs_of_nonneg t.coe_nonneg]

theorem unitRay_unique {x : X} (hx : x ≠ p) (γ : ℝ≥0 → X)
    (hγ : Isometry γ) (hzero : γ 0 = p) (hthrough : γ (nndist p x) = x) :
    γ = H.unitRay x := by
  funext t
  have hr : dist p x ≠ 0 := dist_ne_zero.mpr hx.symm
  apply H.eq_map_of_radial_distances_abs
  · conv_lhs => rw [← hzero]
    rw [hγ.dist_eq]
    change |(0 : ℝ) - t| = ((t / nndist p x : ℝ≥0) : ℝ) * dist p x
    simp only [zero_sub, abs_neg, abs_of_nonneg t.coe_nonneg, NNReal.coe_div, coe_nndist]
    exact (div_mul_cancel₀ _ hr).symm
  · conv_lhs => rw [← hthrough]
    rw [hγ.dist_eq]
    change |(t : ℝ) - dist p x| =
      |1 - ((t / nndist p x : ℝ≥0) : ℝ)| * dist p x
    simp only [NNReal.coe_div, coe_nndist]
    calc
      |(t : ℝ) - dist p x| = |dist p x - t| := abs_sub_comm _ _
      _ = |(1 - (t : ℝ) / dist p x) * dist p x| := by
        rw [sub_mul, one_mul, div_mul_cancel₀ _ hr]
      _ = |1 - (t : ℝ) / dist p x| * dist p x := by
        rw [abs_mul, abs_of_nonneg dist_nonneg]


end RadialConeData
end GC.MetricGeometry
