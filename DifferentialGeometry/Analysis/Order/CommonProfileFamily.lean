import DifferentialGeometry.Analysis.Order.CommonProfileComparison

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace GC.GeneralFlow

theorem prefixBudget_mono {b c : ℕ → ℝ} (hbc : ∀ n, b n ≤ c n) (n : ℕ) :
    prefixBudget b n ≤ prefixBudget c n := by
  induction n with
  | zero =>
    exact min_le_min (le_refl _) (div_le_div_of_nonneg_right (hbc 0) (by norm_num))
  | succ n ih =>
    exact min_le_min ih (div_le_div_of_nonneg_right (hbc (n + 1)) (by norm_num))

theorem commonProfile_mono {b c : ℕ → ℝ} (hbc : ∀ n, b n ≤ c n) (t : ℝ) :
    commonProfile b t ≤ commonProfile c t :=
  prefixBudget_mono hbc _

theorem exists_antitone_family_minorant {d : ℕ → ℝ → ℝ}
    (hdpos : ∀ n t, 0 ≤ t → 0 < d n t)
    (hdanti : ∀ n, AntitoneOn (d n) (Ici 0)) :
    ∃ α : ℝ → ℝ → ℝ,
      (∀ A t, 0 ≤ t → 0 < α A t) ∧
      (∀ A, AntitoneOn (α A) (Ici 0)) ∧
      (∀ t, Antitone (fun A => α A t)) ∧
      ∀ A t, 0 ≤ t → α A t < d ⌈A⌉₊ t := by
  refine ⟨fun A t => commonProfile (fun n => d n t) A, ?_, ?_, ?_, ?_⟩
  · intro A t ht
    exact commonProfile_pos (fun n => hdpos n t ht) A
  · intro A s hs t ht hst
    exact commonProfile_mono (fun n => hdanti n hs ht hst) A
  · intro t
    exact commonProfile_antitone _
  · intro A t ht
    exact commonProfile_lt_budget (fun n => hdpos n t ht) A ⌈A⌉₊
      (Nat.ceil_le_floor_add_one A)

theorem exists_decaying_commonProfile_sq_mul_lt_and_diagonal
    {b : ℕ → ℝ} (hb : ∀ n, 0 < b n)
    {r : ℝ → ℝ} (hr : ∀ t, 0 ≤ t → 0 < r t)
    (hranti : AntitoneOn r (Ici 0))
    {α : ℝ → ℝ → ℝ} (hαpos : ∀ A t, 0 < A → 0 ≤ t → 0 < α A t)
    (hαtime : ∀ A, 0 < A → AntitoneOn (α A) (Ici 0))
    (hαscale : ∀ t, 0 ≤ t → AntitoneOn (fun A => α A t) (Ioi 0)) :
    ∃ δ : ℝ → ℝ,
      (∀ t, 0 < δ t) ∧ Antitone δ ∧ (∀ t, δ t < 1) ∧
      Tendsto δ atTop (𝓝 0) ∧
      (∀ (n : ℕ) (t : ℝ), (n : ℝ) ≤ t →
        δ t < b n ∧ δ t < b (n + 1)) ∧
      (∀ u : ℝ, 0 ≤ u → δ u ^ 2 * r u < r (2 * u) / (u + 1)) ∧
      ∀ t : ℝ, 0 < t → δ t < α (2 * t) (2 * t) := by
  let a : ℕ → ℝ := fun n =>
    min (b n) (α (2 * ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1)))
  have ha : ∀ n, 0 < a n := by
    intro n
    exact lt_min (hb n) (hαpos _ _ (by positivity) (by positivity))
  obtain ⟨δ, hδpos, hδanti, hδlt, hδlim, hbudget, hsq⟩ :=
    exists_decaying_commonProfile_sq_mul_lt ha hr hranti
  refine ⟨δ, hδpos, hδanti, hδlt, hδlim, ?_, hsq, ?_⟩
  · intro n t ht
    obtain ⟨h₀, h₁⟩ := hbudget n t ht
    exact ⟨h₀.trans_le (min_le_left _ _), h₁.trans_le (min_le_left _ _)⟩
  · intro t ht
    have hsample : δ t <
        α (2 * ((⌊t⌋₊ : ℝ) + 1)) (2 * ((⌊t⌋₊ : ℝ) + 1)) :=
      ((hbudget ⌊t⌋₊ t (Nat.floor_le ht.le)).1).trans_le (min_le_right _ _)
    have hcompare : 2 * t ≤ 2 * ((⌊t⌋₊ : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one t).le (by norm_num)
    have h2t : 0 < 2 * t := mul_pos (by norm_num) ht
    have hsamplepos : 0 < 2 * ((⌊t⌋₊ : ℝ) + 1) := by positivity
    have hscale :
        α (2 * ((⌊t⌋₊ : ℝ) + 1)) (2 * ((⌊t⌋₊ : ℝ) + 1)) ≤
          α (2 * t) (2 * ((⌊t⌋₊ : ℝ) + 1)) :=
      hαscale _ hsamplepos.le h2t hsamplepos hcompare
    have htime : α (2 * t) (2 * ((⌊t⌋₊ : ℝ) + 1)) ≤ α (2 * t) (2 * t) :=
      hαtime _ h2t h2t.le hsamplepos.le hcompare
    exact hsample.trans_le (hscale.trans htime)

end GC.GeneralFlow
