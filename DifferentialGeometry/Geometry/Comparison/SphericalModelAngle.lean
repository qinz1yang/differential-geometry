import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngle

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

noncomputable def sphericalComparisonAngle (a b c : ℝ) : ℝ :=
  Real.arccos ((Real.cos c - Real.cos a * Real.cos b) / (Real.sin a * Real.sin b))

theorem sphericalComparisonAngle_mem_Icc (a b c : ℝ) :
    sphericalComparisonAngle a b c ∈ Icc 0 Real.pi :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

theorem sphericalComparisonAngle_comm (a b c : ℝ) :
    sphericalComparisonAngle a b c = sphericalComparisonAngle b a c := by
  simp only [sphericalComparisonAngle, mul_comm]

theorem spherical_comparison_cosine_mem_Icc {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hlower : |a - b| ≤ c) (hupper : c ≤ a + b)
    (hperimeter : a + b + c < 2 * Real.pi) :
    (Real.cos c - Real.cos a * Real.cos b) / (Real.sin a * Real.sin b) ∈
      Icc (-1) 1 := by
  have hc : 0 ≤ c := (abs_nonneg _).trans hlower
  have hab := abs_le.mp hlower
  have haπ : a < Real.pi := by linarith [hab.2]
  have hbπ : b < Real.pi := by linarith [hab.1]
  have hcπ : c < Real.pi := by linarith
  have hden : 0 < Real.sin a * Real.sin b :=
    mul_pos (Real.sin_pos_of_pos_of_lt_pi ha haπ) (Real.sin_pos_of_pos_of_lt_pi hb hbπ)
  have hup : Real.cos c ≤ Real.cos (a - b) := by
    simpa only [Real.cos_abs] using
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (a - b)) hcπ.le hlower
  have hlo : Real.cos (a + b) ≤ Real.cos c := by
    by_cases hsum : a + b ≤ Real.pi
    · exact Real.cos_le_cos_of_nonneg_of_le_pi hc hsum hupper
    · have href : c ≤ 2 * Real.pi - (a + b) := by linarith
      have hrefπ : 2 * Real.pi - (a + b) ≤ Real.pi := by linarith
      simpa only [Real.cos_two_pi_sub] using
        Real.cos_le_cos_of_nonneg_of_le_pi hc hrefπ href
  rw [Real.cos_sub] at hup
  rw [Real.cos_add] at hlo
  constructor
  · rw [le_div_iff₀ hden]
    linarith
  · rw [div_le_iff₀ hden]
    linarith

theorem cos_sphericalComparisonAngle {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hlower : |a - b| ≤ c) (hupper : c ≤ a + b)
    (hperimeter : a + b + c < 2 * Real.pi) :
    Real.cos (sphericalComparisonAngle a b c) =
      (Real.cos c - Real.cos a * Real.cos b) / (Real.sin a * Real.sin b) := by
  have h := spherical_comparison_cosine_mem_Icc ha hb hlower hupper hperimeter
  exact Real.cos_arccos h.1 h.2

theorem spherical_comparison_cosine_eq_secant_quotient {a b c : ℝ}
    (hca : Real.cos a ≠ 0) (hcb : Real.cos b ≠ 0)
    (hsa : Real.sin a ≠ 0) (hsb : Real.sin b ≠ 0) :
    (Real.tan a ^ 2 + Real.tan b ^ 2 -
      ((Real.cos a)⁻¹ ^ 2 + (Real.cos b)⁻¹ ^ 2 -
        2 * (Real.cos a)⁻¹ * (Real.cos b)⁻¹ * Real.cos c)) /
        (2 * Real.tan a * Real.tan b) =
      (Real.cos c - Real.cos a * Real.cos b) / (Real.sin a * Real.sin b) := by
  have ht (x : ℝ) (hx : Real.cos x ≠ 0) :
      Real.tan x ^ 2 = (Real.cos x)⁻¹ ^ 2 - 1 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [ht a hca, ht b hcb, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
  field_simp
  ring

end DifferentialGeometry.Geometry.Comparison.Toponogov
