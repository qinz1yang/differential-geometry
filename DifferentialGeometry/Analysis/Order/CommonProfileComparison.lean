import DifferentialGeometry.Analysis.Order.CommonProfileDecay

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace GC.GeneralFlow

theorem exists_decaying_commonProfile_sq_mul_lt
    {b : ℕ → ℝ} (hb : ∀ n, 0 < b n)
    {r : ℝ → ℝ} (hr : ∀ t, 0 ≤ t → 0 < r t)
    (hranti : AntitoneOn r (Ici 0)) :
    ∃ δ : ℝ → ℝ,
      (∀ t, 0 < δ t) ∧ Antitone δ ∧ (∀ t, δ t < 1) ∧
      Tendsto δ atTop (𝓝 0) ∧
      (∀ (n : ℕ) (t : ℝ), (n : ℝ) ≤ t →
        δ t < b n ∧ δ t < b (n + 1)) ∧
      ∀ u : ℝ, 0 ≤ u → δ u ^ 2 * r u < r (2 * u) / (u + 1) := by
  have hr₀ : 0 < r 0 := hr 0 le_rfl
  let a : ℕ → ℝ := fun n => min (b n) (r (2 * (n : ℝ)) / (((n : ℝ) + 1) * r 0))
  have ha : ∀ n, 0 < a n := by
    intro n
    exact lt_min (hb n) (div_pos (hr _ (by positivity)) (by positivity))
  obtain ⟨δ, hδpos, hδanti, hδlt, hδlim, hbudget⟩ := exists_decaying_commonProfile ha
  refine ⟨δ, hδpos, hδanti, hδlt, hδlim, ?_, ?_⟩
  · intro n t ht
    obtain ⟨h₀, h₁⟩ := hbudget n t ht
    exact ⟨h₀.trans_le (min_le_left _ _), h₁.trans_le (min_le_left _ _)⟩
  · intro u hu
    let n : ℕ := ⌊u⌋₊
    let N : ℕ := n + 1
    have hnu : (n : ℝ) ≤ u := Nat.floor_le hu
    have huN : u < (N : ℝ) := by
      simpa only [N, n, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one u
    have hδnext : δ u < r (2 * (N : ℝ)) / (((N : ℝ) + 1) * r 0) :=
      ((hbudget n u hnu).2).trans_le (min_le_right _ _)
    have hδsq : δ u ^ 2 ≤ δ u := by
      simpa only [pow_two, mul_one] using
        mul_le_mul_of_nonneg_left (hδlt u).le (hδpos u).le
    have hru : r u ≤ r 0 := hranti (show (0 : ℝ) ∈ Ici 0 from le_refl (0 : ℝ)) hu hu
    have h2u : 0 ≤ 2 * u := by positivity
    have h2N : 0 ≤ 2 * (N : ℝ) := by positivity
    have hcompare : r (2 * (N : ℝ)) ≤ r (2 * u) :=
      hranti h2u h2N (mul_le_mul_of_nonneg_left huN.le (by norm_num))
    calc
      δ u ^ 2 * r u ≤ δ u ^ 2 * r 0 :=
        mul_le_mul_of_nonneg_left hru (sq_nonneg _)
      _ ≤ δ u * r 0 := mul_le_mul_of_nonneg_right hδsq hr₀.le
      _ < (r (2 * (N : ℝ)) / (((N : ℝ) + 1) * r 0)) * r 0 :=
        mul_lt_mul_of_pos_right hδnext hr₀
      _ = r (2 * (N : ℝ)) / ((N : ℝ) + 1) := by
        rw [div_mul_eq_div_div, div_mul_cancel₀ _ hr₀.ne']
      _ ≤ r (2 * u) / ((N : ℝ) + 1) :=
        div_le_div_of_nonneg_right hcompare (by positivity)
      _ ≤ r (2 * u) / (u + 1) :=
        div_le_div_of_nonneg_left (hr _ h2u).le (by positivity)
          (add_le_add huN.le (le_refl (1 : ℝ)))

end GC.GeneralFlow
