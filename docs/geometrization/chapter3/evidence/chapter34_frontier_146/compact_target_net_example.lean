
namespace GC146ExportReview

theorem expanding_open_interval_net :
    ∃ T : Finset (Ioo (0 : ℝ) 1), T.card ≤ 2 ∧
      ∀ a : Ioo (0 : ℝ) 1, ∃ b ∈ T, dist a b < 3 := by
  let Φ : Ioo (0 : ℝ) 1 → Icc (0 : ℝ) 2 := fun a =>
    ⟨2 * a.val, by constructor <;> linarith [a.property.1, a.property.2]⟩
  let z : Icc (0 : ℝ) 2 := ⟨0, by constructor <;> norm_num⟩
  let w : Icc (0 : ℝ) 2 := ⟨2, by constructor <;> norm_num⟩
  let S : Finset (Icc (0 : ℝ) 2) := {z, w}
  apply compact_comparison_target_net (η := 3) Φ ?_ (by norm_num) 2 S ?_ ?_
  · intro a b
    change |a.val - b.val| ≤ |2 * a.val - 2 * b.val|
    rw [show 2 * a.val - 2 * b.val = 2 * (a.val - b.val) by ring, abs_mul]
    norm_num
    linarith [abs_nonneg (a.val - b.val)]
  · exact (Finset.card_insert_le z {w}).trans (by simp)
  · intro k
    by_cases hk : k.val ≤ 1
    · refine ⟨z, by simp [S], ?_⟩
      change |k.val - 0| ≤ (3 : ℝ) / 3
      simpa only [sub_zero, abs_of_nonneg k.property.1, div_self (by norm_num : (3 : ℝ) ≠ 0)] using hk
    · refine ⟨w, by simp [S], ?_⟩
      change |k.val - 2| ≤ (3 : ℝ) / 3
      rw [abs_of_nonpos (by linarith [k.property.2])]
      norm_num
      linarith

end GC146ExportReview
