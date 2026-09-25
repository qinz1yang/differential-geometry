import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open scoped Topology

namespace Filter

theorem exists_eventually_of_monotone_of_subsequence
    (P : ℕ → ℕ → Prop) (hmono : ∀ i, Monotone (P i))
    (hsub : ∀ f : ℕ → ℕ, StrictMono f → ∃ m, ∃ᶠ i in atTop, P (f i) m) :
    ∃ m, ∀ᶠ i in atTop, P i m := by
  by_contra hnot
  have hbad (m : ℕ) : ∃ᶠ i in atTop, ¬ P i m :=
    not_eventually.mp fun h => hnot ⟨m, h⟩
  obtain ⟨f, hf, hfail⟩ := extraction_forall_of_frequently hbad
  obtain ⟨m, hm⟩ := hsub f hf
  obtain ⟨i, hPi, hmi⟩ := (hm.and_eventually (eventually_ge_atTop m)).exists
  exact hfail i (hmono (f i) hmi hPi)

theorem exists_pos_eventually_of_antitone_of_subsequence
    (P : ℕ → ℝ → Prop)
    (hmono : ∀ i ε δ, 0 < ε → ε ≤ δ → P i δ → P i ε)
    (hsub : ∀ f : ℕ → ℕ, StrictMono f →
      ∃ δ : ℝ, 0 < δ ∧ ∃ g : ℕ → ℕ, StrictMono g ∧ ∀ i, P (f (g i)) δ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in atTop, P i δ := by
  let width : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hpos (n : ℕ) : 0 < width n := by dsimp [width]; positivity
  have hwidth : Antitone width := by
    intro m n hmn
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hlimit : Tendsto width atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨m, hm⟩ := exists_eventually_of_monotone_of_subsequence
    (fun i n => P i (width n)) (fun i m n hmn => hmono i _ _ (hpos n) (hwidth hmn)) (by
      intro f hf
      obtain ⟨δ, hδ, g, hg, hgood⟩ := hsub f hf
      obtain ⟨m, hm⟩ := (hlimit.eventually (Iio_mem_nhds hδ)).exists
      refine ⟨m, frequently_atTop.2 fun N => ⟨g N, hg.id_le N, ?_⟩⟩
      exact hmono (f (g N)) _ _ (hpos m) hm.le (hgood N))
  exact ⟨width m, hpos m, hm⟩

end Filter
