import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace DifferentialGeometry.Analysis

theorem eq_or_eq_neg_of_unit_of_mem_span
    {R E : Type*} [CommRing R] [NoZeroDivisors R] [AddCommGroup E] [Module R E]
    (B : E →ₗ[R] E →ₗ[R] R) (v w : E)
    (hv : B v v = 1) (hw : B w w = 1) (hline : v ∈ Submodule.span R {w}) :
    v = w ∨ v = -w := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hline
  have hnorm := hv
  simp only [← hc, map_smul, LinearMap.smul_apply, hw, smul_eq_mul, mul_one] at hnorm
  rcases mul_self_eq_one_iff.mp hnorm with h | h
  · exact Or.inl (by simpa only [h, one_smul] using hc.symm)
  · exact Or.inr (by simpa only [h, neg_one_smul] using hc.symm)

theorem eq_of_unit_of_mem_span_of_positive_functional
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (ℓ : E →ₗ[ℝ] ℝ) (v w : E)
    (hv : B v v = 1) (hw : B w w = 1) (hline : v ∈ Submodule.span ℝ {w})
    (hvpos : 0 < ℓ v) (hwpos : 0 < ℓ w) : v = w := by
  rcases eq_or_eq_neg_of_unit_of_mem_span B v w hv hw hline with h | h
  · exact h
  · rw [h, map_neg] at hvpos
    linarith

end DifferentialGeometry.Analysis
