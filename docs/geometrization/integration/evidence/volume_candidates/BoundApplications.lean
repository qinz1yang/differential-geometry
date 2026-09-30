import DifferentialGeometry.Analysis.Order.EventualTestBounds

set_option autoImplicit false

open Set Filter

example : ∃ A : ℕ → ℝ, (∀ w, 0 < A w) ∧ ∀ w : ℕ, (w : ℝ) ≤ A w := by
  have hfinite (n : ℕ) : ∃ D : ℝ, ∀ _ : Unit, (n : ℝ) ≤ D := ⟨n, fun _ => le_rfl⟩
  have htail (w : ℕ) (_ : w ∈ (univ : Set ℕ)) :
      ∃ B : ℝ, ∀ᶠ n : ℕ in atTop, ∀ _ : Unit, n ≤ w → (n : ℝ) ≤ B := by
    refine ⟨0, eventually_atTop.mpr ⟨w + 1, ?_⟩⟩
    intro n hn _ h
    exact (Nat.not_succ_le_self w (hn.trans h)).elim
  obtain ⟨A, hA, _, ht⟩ := exists_positive_test_bound_of_pointwise_eventual_bounds
    (I := fun _ => Unit) univ (fun n _ => (n : ℝ)) (fun w n _ => n ≤ w) hfinite htail
  exact ⟨A, hA, fun w => ht w (mem_univ _) w () le_rfl⟩

example : ∃ A : ℝ → ℝ, (∀ w, 0 < A w) ∧ ∀ w, A w = 1 := by
  obtain ⟨A, hA, hout, _⟩ := exists_positive_test_bound_of_pointwise_eventual_bounds
    (I := fun _ => Unit) (∅ : Set ℝ) (fun n _ => (n : ℝ)) (fun _ _ _ => True)
    (fun n => ⟨n, fun _ => le_rfl⟩) (fun _ h => False.elim h)
  exact ⟨A, hA, fun w => hout w (by simp)⟩
