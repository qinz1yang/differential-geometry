import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem norm_sum_smul_sub_le_of_nonzero_close
    {E ι : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Finset ι) (w : ι → ℝ) (a : ι → E) (p : E) (δ : ℝ)
    (hw0 : ∀ i ∈ S, 0 ≤ w i) (hw1 : ∑ i ∈ S, w i = 1)
    (hclose : ∀ i ∈ S, w i ≠ 0 → ‖a i - p‖ ≤ δ) :
    ‖(∑ i ∈ S, w i • a i) - p‖ ≤ δ := by
  have he : (∑ i ∈ S, w i • a i) - p = ∑ i ∈ S, w i • (a i - p) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw1, one_smul]
  rw [he]
  calc
    _ ≤ ∑ i ∈ S, ‖w i • (a i - p)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, w i * δ := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hz : w i = 0
      · simp only [hz, zero_smul, norm_zero, zero_mul, le_refl]
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 i hi)]
        exact mul_le_mul_of_nonneg_left (hclose i hi hz) (hw0 i hi)
    _ = δ := by rw [← Finset.sum_mul, hw1, one_mul]
