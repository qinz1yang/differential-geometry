import DifferentialGeometry.Geometry.Metric.RadialConeData

set_option autoImplicit false

noncomputable section
open scoped NNReal

namespace GC.MetricGeometry

variable {X : Type*} [MetricSpace X]

namespace RadialConeData

variable {p : X} (H : RadialConeData p)

theorem dist_apex (t : ℝ≥0) (x : X) : dist p (H.map t x) = (t : ℝ) * dist p x := by
  have hh := H.dist_sq 0 t p x
  rw [H.map_zero] at hh
  norm_num only [NNReal.coe_zero, zero_pow, zero_mul, zero_add, sub_zero] at hh
  apply (sq_eq_sq₀ dist_nonneg (mul_nonneg t.coe_nonneg dist_nonneg)).mp
  simpa only [mul_pow] using hh

theorem map_apex (t : ℝ≥0) : H.map t p = p := by
  have hh := H.dist_apex t p
  rw [dist_self, mul_zero] at hh
  exact (dist_eq_zero.mp hh).symm

theorem same_ray_dist (s t : ℝ≥0) (x : X) :
    dist (H.map s x) (H.map t x) = |(s : ℝ) - t| * dist p x := by
  apply (sq_eq_sq₀ dist_nonneg (mul_nonneg (abs_nonneg _) dist_nonneg)).mp
  rw [H.dist_sq, radialConeKernel_self, mul_pow, sq_abs]
  ring

theorem similarity (t : ℝ≥0) (x y : X) :
    dist (H.map t x) (H.map t y) = (t : ℝ) * dist x y := by
  apply (sq_eq_sq₀ dist_nonneg (mul_nonneg t.coe_nonneg dist_nonneg)).mp
  rw [H.dist_sq, mul_pow]
  unfold radialConeKernel
  ring

theorem kernel_map_left (t : ℝ≥0) (x y : X) :
    radialConeKernel p (H.map t x) y = (t : ℝ) * radialConeKernel p x y := by
  have hh := H.dist_sq t 1 x y
  rw [H.map_one] at hh
  norm_num only [NNReal.coe_one, one_pow, one_mul, mul_one] at hh
  unfold radialConeKernel at hh ⊢
  rw [H.dist_apex]
  nlinarith

theorem kernel_map_right (t : ℝ≥0) (x y : X) :
    radialConeKernel p x (H.map t y) = (t : ℝ) * radialConeKernel p x y := by
  rw [radialConeKernel_comm p x, H.kernel_map_left, radialConeKernel_comm p y]

theorem map_mul (s t : ℝ≥0) (x : X) : H.map s (H.map t x) = H.map (s * t) x := by
  have hh := H.dist_sq s (s * t) (H.map t x) x
  rw [H.dist_apex, H.kernel_map_left, radialConeKernel_self] at hh
  simp only [NNReal.coe_mul] at hh
  have hz : dist (H.map s (H.map t x)) (H.map (s * t) x) ^ 2 = 0 := by
    rw [hh]
    ring
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg (x := H.map s (H.map t x)) (y := H.map (s * t) x)]

theorem map_inv_map {t : ℝ≥0} (ht : t ≠ 0) (x : X) : H.map t⁻¹ (H.map t x) = x := by
  rw [H.map_mul, inv_mul_cancel₀ ht, H.map_one]

theorem map_map_inv {t : ℝ≥0} (ht : t ≠ 0) (x : X) : H.map t (H.map t⁻¹ x) = x := by
  rw [H.map_mul, mul_inv_cancel₀ ht, H.map_one]

theorem map_surjective {t : ℝ≥0} (ht : t ≠ 0) : Function.Surjective (H.map t) :=
  fun x => ⟨H.map t⁻¹ x, H.map_map_inv ht x⟩

theorem map_injective {t : ℝ≥0} (ht : t ≠ 0) : Function.Injective (H.map t) := by
  intro x y hxy
  have hh := congrArg (H.map t⁻¹) hxy
  simpa only [H.map_inv_map ht] using hh


end RadialConeData
end GC.MetricGeometry
