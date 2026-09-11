import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace DifferentialGeometry.Analysis

theorem eq_of_unit_of_mem_span_of_positive_functional
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (ℓ : E →ₗ[ℝ] ℝ) (v w : E)
    (hv : B v v = 1) (hw : B w w = 1) (hline : v ∈ Submodule.span ℝ {w})
    (hvpos : 0 < ℓ v) (hwpos : 0 < ℓ w) : v = w := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hline
  have hnorm := hv
  simp only [← hc, map_smul, LinearMap.smul_apply, hw] at hnorm
  change c * (c * 1) = 1 at hnorm
  have hpos := hvpos
  rw [← hc, map_smul] at hpos
  change 0 < c * ℓ w at hpos
  have hcpos : 0 < c := (mul_pos_iff_of_pos_right hwpos).mp hpos
  have hc1 : c = 1 := by nlinarith only [hnorm, hcpos]
  simpa only [hc1, one_smul] using hc.symm

end DifferentialGeometry.Analysis
