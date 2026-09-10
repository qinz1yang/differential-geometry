import DifferentialGeometry.Geometry.Comparison.Toponogov.MetricComparisonAngle

namespace Poincare.Toponogov

theorem smallAngle_quadratic_loss {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (_hC : 0 ≤ C)
    (hreverse : |A - B| ≤ C) (htriangle : C ≤ A + B)
    (hangle : comparisonAngle A B C ≤ Real.pi / 3) :
    C ^ 2 ≤ A ^ 2 + B ^ 2 - A * B := by
  have hangle_nonneg : 0 ≤ comparisonAngle A B C :=
    (comparisonAngle_mem_Icc A B C).1
  have hpi_third_le_pi : Real.pi / 3 ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have hcos : Real.cos (Real.pi / 3) ≤ Real.cos (comparisonAngle A B C) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hangle_nonneg hpi_third_le_pi hangle
  rw [Real.cos_pi_div_three, cos_comparisonAngle hA hB hreverse htriangle,
    comparisonCosine] at hcos
  have hden : 0 < 2 * A * B := by positivity
  rw [le_div_iff₀ hden] at hcos
  nlinarith

theorem smallAngle_linear_loss {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 ≤ C)
    (hreverse : |A - B| ≤ C) (htriangle : C ≤ A + B)
    (hangle : comparisonAngle A B C ≤ Real.pi / 3) (hlarge : 2 * B ≤ A) :
    C ≤ A - B / 4 := by
  have hquadratic : C ^ 2 ≤ A ^ 2 + B ^ 2 - A * B :=
    smallAngle_quadratic_loss hA hB hC hreverse htriangle hangle
  have htarget_nonneg : 0 ≤ A - B / 4 := by linarith
  have hproduct : 0 ≤ (A - 2 * B) * B :=
    mul_nonneg (sub_nonneg.mpr hlarge) hB.le
  have htarget_sq : A ^ 2 + B ^ 2 - A * B ≤ (A - B / 4) ^ 2 := by
    nlinarith [sq_nonneg B]
  exact (sq_le_sq₀ hC htarget_nonneg).mp (hquadratic.trans htarget_sq)

section Regression


example : comparisonAngle 1 1 1 = Real.pi / 3 := by
  rw [comparisonAngle]
  norm_num [comparisonCosine]
  rw [← Real.cos_pi_div_three, Real.arccos_cos]
  · positivity
  · nlinarith [Real.pi_pos]


example : (1 : ℝ) ≤ 2 - 1 / 4 := by
  apply smallAngle_linear_loss (A := 2) (B := 1) (C := 1)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · have hzero : comparisonAngle (2 : ℝ) 1 1 = 0 := by
      convert comparisonAngle_abs_sub (a := (2 : ℝ)) (b := 1) (by norm_num) (by norm_num)
      norm_num
    rw [hzero]
    nlinarith [Real.pi_pos]
  · norm_num

end Regression

end Poincare.Toponogov
