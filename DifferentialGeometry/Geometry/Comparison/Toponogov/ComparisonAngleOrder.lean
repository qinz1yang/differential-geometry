import DifferentialGeometry.Geometry.Comparison.Toponogov.MetricComparisonAngle

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.Toponogov

theorem comparisonAngle_le_of_sq_le_cos {a b c θ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hc : c ^ 2 ≤ a ^ 2 + b ^ 2 - 2 * a * b * Real.cos θ) :
    comparisonAngle a b c ≤ θ := by
  rw [comparisonAngle, ← Real.arccos_cos hθ₀ hθπ]
  apply Real.arccos_le_arccos
  unfold comparisonCosine
  rw [le_div_iff₀ (by positivity : 0 < 2 * a * b)]
  nlinarith

theorem sq_le_cos_of_comparisonAngle_le {a b c θ : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hca : |a - b| ≤ c) (hac : c ≤ a + b)
    (hθπ : θ ≤ Real.pi) (hangle : comparisonAngle a b c ≤ θ) :
    c ^ 2 ≤ a ^ 2 + b ^ 2 - 2 * a * b * Real.cos θ := by
  have hcos : Real.cos θ ≤ Real.cos (comparisonAngle a b c) :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (comparisonAngle_mem_Icc a b c).1 hθπ hangle
  rw [cos_comparisonAngle ha hb hca hac] at hcos
  unfold comparisonCosine at hcos
  have hab : 0 < 2 * a * b := by positivity
  rw [le_div_iff₀ hab] at hcos
  nlinarith

theorem comparisonAngle_mono_third {a b c₁ c₂ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc₁ : 0 ≤ c₁) (hc₁₂ : c₁ ≤ c₂) :
    comparisonAngle a b c₁ ≤ comparisonAngle a b c₂ := by
  unfold comparisonAngle
  apply Real.arccos_le_arccos
  unfold comparisonCosine
  rw [div_le_div_iff_of_pos_right (by positivity : 0 < 2 * a * b)]
  nlinarith

theorem comparisonAngle_le_iff_sq_le_cos {a b c θ : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hca : |a - b| ≤ c) (hac : c ≤ a + b)
    (hθ₀ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    comparisonAngle a b c ≤ θ ↔
      c ^ 2 ≤ a ^ 2 + b ^ 2 - 2 * a * b * Real.cos θ := by
  constructor
  · exact sq_le_cos_of_comparisonAngle_le ha hb hca hac hθπ
  · exact comparisonAngle_le_of_sq_le_cos ha hb hθ₀ hθπ

end DifferentialGeometry.Toponogov
