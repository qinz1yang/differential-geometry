import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

section

namespace Real

theorem sqrt_regularized_gram_sub_le
    {a b c δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ^ 2 ≤ a * b) (hδ : 0 ≤ δ) :
    0 ≤ Real.sqrt ((a + δ) * (b + δ) - c ^ 2) - Real.sqrt (a * b - c ^ 2) ∧
      Real.sqrt ((a + δ) * (b + δ) - c ^ 2) - Real.sqrt (a * b - c ^ 2) ≤
        Real.sqrt (δ * (a + b) + δ ^ 2) := by
  have hbase : 0 ≤ a * b - c ^ 2 := sub_nonneg.mpr hc
  have herr : 0 ≤ δ * (a + b) + δ ^ 2 := by positivity
  have heq : (a + δ) * (b + δ) - c ^ 2 = (a * b - c ^ 2) + (δ * (a + b) + δ ^ 2) := by ring
  rw [heq]
  refine ⟨sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith)), ?_⟩
  have hsq : Real.sqrt ((a * b - c ^ 2) + (δ * (a + b) + δ ^ 2)) ≤
      Real.sqrt (a * b - c ^ 2) + Real.sqrt (δ * (a + b) + δ ^ 2) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
    nlinarith [Real.sq_sqrt hbase, Real.sq_sqrt herr,
      mul_nonneg (Real.sqrt_nonneg (a * b - c ^ 2)) (Real.sqrt_nonneg (δ * (a + b) + δ ^ 2))]
  linarith

theorem sqrt_regularized_gram_sub_le_of_trace_le
    {a b c δ C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ^ 2 ≤ a * b)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hC : a + b ≤ C) :
    |Real.sqrt ((a + δ) * (b + δ) - c ^ 2) - Real.sqrt (a * b - c ^ 2)| ≤
      Real.sqrt δ * Real.sqrt (C + 1) := by
  have hh := sqrt_regularized_gram_sub_le ha hb hc hδ
  rw [abs_of_nonneg hh.1]
  apply hh.2.trans
  rw [← Real.sqrt_mul hδ]
  apply Real.sqrt_le_sqrt
  have hmul := mul_le_mul_of_nonneg_left hC hδ
  have hsq : δ ^ 2 ≤ δ := by nlinarith
  nlinarith

end Real

end
