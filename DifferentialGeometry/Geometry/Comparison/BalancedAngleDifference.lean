import DifferentialGeometry.Geometry.Comparison.AngleReversal

set_option autoImplicit false

open Real Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem abs_comparisonAngleNegCurvature_sub_le_of_balanced_coordinates
    {x y z u : X} {a A ε : ℝ} (ha : 0 < a) (hzu : dist z u ∈ Icc a A)
    (hs : 0 < dist z x) (hs1 : dist z x ≤ 1) (hsa : dist z x ≤ a / 2)
    (hbalance : dist z x = dist z y) (hε : 0 ≤ ε)
    (hcoord : |dist x u - dist y u| ≤ ε * dist x y) :
    |comparisonAngleNegCurvature 1 (dist z u) (dist z x) (dist u x) -
      comparisonAngleNegCurvature 1 (dist z u) (dist z y) (dist u y)| ≤
      Real.pi * sqrt (ε + (4 * cosh (A + 1) / sinh a) * dist z x) := by
  let α := comparisonAngleNegCurvature 1 (dist z u) (dist z x) (dist u x)
  let α' := comparisonAngleNegCurvature 1 (dist z u) (dist z y) (dist u y)
  let K := 4 * cosh (A + 1) / sinh a
  have hx := abs_dist_sub_add_cos_comparisonAngleNegCurvature_one_le z x u ha hzu.1 hzu.2 hs hs1 hsa
  have hy := abs_dist_sub_add_cos_comparisonAngleNegCurvature_one_le z y u ha hzu.1 hzu.2
    (by rwa [← hbalance]) (by rwa [← hbalance]) (by rwa [← hbalance])
  have hx' : |dist x u - dist z u + dist z x * cos α| ≤ K * (dist z x) ^ 2 := by
    simpa only [α, K, dist_comm u x] using hx
  have hy' : |dist y u - dist z u + dist z x * cos α'| ≤ K * (dist z x) ^ 2 := by
    simpa only [α', K, dist_comm u y, hbalance] using hy
  have htri : dist x y ≤ 2 * dist z x := by
    have h := dist_triangle x z y
    rw [dist_comm x z, ← hbalance] at h
    linarith
  have he := mul_le_mul_of_nonneg_left htri hε
  have hcos : |cos α - cos α'| ≤ 2 * (ε + K * dist z x) := by
    apply abs_le.mpr
    constructor
    · apply (mul_le_mul_iff_left₀ hs).mp
      nlinarith [(abs_le.mp hx').1, (abs_le.mp hy').2, (abs_le.mp hcoord).2]
    · apply (mul_le_mul_iff_left₀ hs).mp
      nlinarith [(abs_le.mp hx').2, (abs_le.mp hy').1, (abs_le.mp hcoord).1]
  exact abs_sub_le_pi_mul_sqrt_of_abs_cos_sub_le
    (comparisonAngleNegCurvature_mem_Icc _ _ _ _)
    (comparisonAngleNegCurvature_mem_Icc _ _ _ _) hcos

end DifferentialGeometry.Geometry.Comparison.Toponogov
