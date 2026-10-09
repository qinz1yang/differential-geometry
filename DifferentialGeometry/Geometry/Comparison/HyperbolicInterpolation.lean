import DifferentialGeometry.Analysis.ODE.HyperbolicMidpoint
import DifferentialGeometry.Geometry.Comparison.ModelAngle

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open DifferentialGeometry.Analysis.ODE

theorem comparisonAngleNegCurvature_le_of_cosh_interpolate {κ a A b c C : ℝ}
    (hκ : 0 < κ) (ha : 0 < a) (haA : a ≤ A) (hb : 0 < b)
    (h : hyperbolicInterpolate (Real.sqrt κ) A (Real.cosh (Real.sqrt κ * b))
      (Real.cosh (Real.sqrt κ * C)) a ≤ Real.cosh (Real.sqrt κ * c)) :
    comparisonAngleNegCurvature κ A b C ≤ comparisonAngleNegCurvature κ a b c := by
  have hk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hA : 0 < A := ha.trans_le haA
  have hsa : 0 < Real.sinh (Real.sqrt κ * a) := Real.sinh_pos_iff.mpr (mul_pos hk ha)
  have hsA : 0 < Real.sinh (Real.sqrt κ * A) := Real.sinh_pos_iff.mpr (mul_pos hk hA)
  have hsb : 0 < Real.sinh (Real.sqrt κ * b) := Real.sinh_pos_iff.mpr (mul_pos hk hb)
  rw [hyperbolicInterpolate_eq_cosh hk hA] at h
  have hmul := mul_le_mul_of_nonneg_right h hsA.le
  field_simp at hmul
  have hquotient :
      (Real.cosh (Real.sqrt κ * a) * Real.cosh (Real.sqrt κ * b) - Real.cosh (Real.sqrt κ * c)) /
        Real.sinh (Real.sqrt κ * a) ≤
      (Real.cosh (Real.sqrt κ * A) * Real.cosh (Real.sqrt κ * b) - Real.cosh (Real.sqrt κ * C)) /
        Real.sinh (Real.sqrt κ * A) := by
    rw [div_le_div_iff₀ hsa hsA]
    nlinarith
  have hcosine := div_le_div_of_nonneg_right hquotient hsb.le
  simp only [div_div] at hcosine
  simp only [comparisonAngleNegCurvature, ite_eq_right hκ.ne']
  exact Real.arccos_le_arccos hcosine

end DifferentialGeometry.Geometry.Comparison.Toponogov
