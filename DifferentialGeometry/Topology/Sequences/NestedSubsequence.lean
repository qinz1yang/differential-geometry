import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Rat.Encodable
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false

open Filter

namespace DifferentialGeometry

private theorem exists_strictMono_eq_comp_of_forall_ge {f g : ℕ → ℕ} (hf : StrictMono f)
    (hg : StrictMono g) {k : ℕ} (h : ∀ i, k ≤ i → ∃ m, i ≤ m ∧ g i = f m) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∀ i, k ≤ i → g i = f (ρ i) := by
  classical
  choose m hm heq using h
  let ρ : ℕ → ℕ := fun i => if hi : k ≤ i then m i hi else i
  have hρ : ∀ i (hi : k ≤ i), ρ i = m i hi := fun i hi => dite_eq_left hi
  refine ⟨ρ, strictMono_nat_of_lt_succ fun i => ?_, fun i hi => by rw [hρ i hi]; exact heq i hi⟩
  by_cases hi : k ≤ i
  · have hi' : k ≤ i + 1 := hi.trans (Nat.le_succ i)
    rw [hρ i hi, hρ (i + 1) hi']
    apply hf.lt_iff_lt.mp
    rw [← heq i hi, ← heq (i + 1) hi']
    exact hg (Nat.lt_succ_self i)
  · have hlt : ρ i = i := dite_eq_right hi
    rw [hlt]
    by_cases hi' : k ≤ i + 1
    · rw [hρ (i + 1) hi']
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (hm (i + 1) hi')
    · have : ρ (i + 1) = i + 1 := dite_eq_right hi'
      rw [this]
      exact Nat.lt_succ_self i

theorem exists_strictMono_forall_of_subseq_property (E : (ℕ → ℕ) → ℝ → Prop)
    (hdown : ∀ σ T T', 0 < T' → T' ≤ T → E σ T → E σ T')
    (hsub : ∀ σ ψ T, StrictMono ψ → E σ T → E (σ ∘ ψ) T)
    (htail : ∀ σ σ' T, (∀ᶠ i in atTop, σ i = σ' i) → E σ T → E σ' T) (σ₀ : ℕ → ℕ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ χ : ℕ → ℕ, StrictMono χ → ∀ T T' : ℝ, 0 < T' → T' < T →
      E (σ₀ ∘ ψ ∘ χ) T → E (σ₀ ∘ ψ) T' := by
  classical
  obtain ⟨q, hq⟩ := exists_surjective_nat ℚ
  let step : {f : ℕ → ℕ // StrictMono f} → ℕ → {f : ℕ → ℕ // StrictMono f} := fun Φ k =>
    if h : ∃ χ : ℕ → ℕ, StrictMono χ ∧ E (σ₀ ∘ Φ.1 ∘ χ) (q k) then
      ⟨Φ.1 ∘ Classical.choose h, Φ.2.comp (Classical.choose_spec h).1⟩
    else Φ
  let Φ : ℕ → {f : ℕ → ℕ // StrictMono f} := fun k =>
    Nat.rec ⟨id, strictMono_id⟩ (fun k Φk => step Φk k) k
  have hΦsucc : ∀ k, Φ (k + 1) = step (Φ k) k := fun k => rfl
  have hstep : ∀ k, ∃ χ : ℕ → ℕ, StrictMono χ ∧ (Φ (k + 1)).1 = (Φ k).1 ∘ χ := by
    intro k
    rw [hΦsucc]
    by_cases h : ∃ χ : ℕ → ℕ, StrictMono χ ∧ E (σ₀ ∘ (Φ k).1 ∘ χ) (q k)
    · refine ⟨Classical.choose h, (Classical.choose_spec h).1, ?_⟩
      simp only [step, dite_eq_left h]
    · refine ⟨id, strictMono_id, ?_⟩
      simp only [step, dite_eq_right h]
      rfl
  have hchosen : ∀ k, (∃ χ : ℕ → ℕ, StrictMono χ ∧ E (σ₀ ∘ (Φ k).1 ∘ χ) (q k)) →
      E (σ₀ ∘ (Φ (k + 1)).1) (q k) := by
    intro k h
    rw [hΦsucc]
    simp only [step, dite_eq_left h]
    exact (Classical.choose_spec h).2
  have hle : ∀ k m, k ≤ m → ∃ χ : ℕ → ℕ, StrictMono χ ∧ (Φ m).1 = (Φ k).1 ∘ χ := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => exact ⟨id, strictMono_id, rfl⟩
    | succ m _ ih =>
      obtain ⟨χ, hχ, hm⟩ := ih
      obtain ⟨χ', hχ', hm'⟩ := hstep m
      exact ⟨χ ∘ χ', hχ.comp hχ', by rw [hm', hm]; rfl⟩
  let ψ : ℕ → ℕ := fun i => (Φ i).1 i
  have hψ : StrictMono ψ := by
    refine strictMono_nat_of_lt_succ fun i => ?_
    obtain ⟨χ, hχ, hi⟩ := hstep i
    change (Φ i).1 i < (Φ (i + 1)).1 (i + 1)
    rw [hi]
    exact (Φ i).2 (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hχ.le_apply)
  have htailΦ : ∀ k, ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∀ i, k ≤ i → ψ i = (Φ k).1 (ρ i) := by
    intro k
    refine exists_strictMono_eq_comp_of_forall_ge (Φ k).2 hψ fun i hki => ?_
    obtain ⟨χ, hχ, hi⟩ := hle k i hki
    exact ⟨χ i, hχ.le_apply, by change (Φ i).1 i = _; rw [hi]; rfl⟩
  refine ⟨ψ, hψ, fun χ hχ T T' hT' hTT' hE => ?_⟩
  obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn hTT'
  obtain ⟨k, rfl⟩ := hq r
  have hr₀ : (0 : ℝ) < q k := hT'.trans hr₁
  obtain ⟨ρ, hρ, hψρ⟩ := htailΦ k
  have hEk : E (σ₀ ∘ (Φ k).1 ∘ (ρ ∘ χ)) (q k) := by
    refine htail _ _ _ ?_ (hdown _ _ _ hr₀ hr₂.le hE)
    filter_upwards [eventually_ge_atTop k] with i hi
    simp only [Function.comp_apply]
    rw [hψρ (χ i) (hi.trans hχ.le_apply)]
  have hEk' := hchosen k ⟨ρ ∘ χ, hρ.comp hχ, hEk⟩
  obtain ⟨ρ', hρ', hψρ'⟩ := htailΦ (k + 1)
  have hEψ : E (σ₀ ∘ ψ) (q k) := by
    refine htail _ _ _ ?_ (hsub _ _ _ hρ' hEk')
    filter_upwards [eventually_ge_atTop (k + 1)] with i hi
    simp only [Function.comp_apply]
    rw [hψρ' i hi]
  exact hdown _ _ _ hT' hr₁.le hEψ

theorem exists_strictMono_maximal_depth (E : (ℕ → ℕ) → ℝ → Prop)
    (hdown : ∀ σ T T', 0 < T' → T' ≤ T → E σ T → E σ T')
    (hsub : ∀ σ ψ T, StrictMono ψ → E σ T → E (σ ∘ ψ) T)
    (htail : ∀ σ σ' T, (∀ᶠ i in atTop, σ i = σ' i) → E σ T → E σ' T) (σ₀ : ℕ → ℕ)
    (hbase : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ T₀ : ℝ, 0 < T₀ ∧ E (σ₀ ∘ ψ) T₀) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ((∀ T : ℝ, 0 < T → E (σ₀ ∘ ψ) T) ∨
        ∃ Tstar : ℝ, 0 < Tstar ∧ (∀ T : ℝ, 0 < T → T < Tstar → E (σ₀ ∘ ψ) T) ∧
          ∀ χ : ℕ → ℕ, StrictMono χ → ∀ T : ℝ, Tstar < T → ¬ E (σ₀ ∘ ψ ∘ χ) T) := by
  obtain ⟨ψ₀, hψ₀, T₀, hT₀, hE₀⟩ := hbase
  obtain ⟨ψ₁, hψ₁, hmax⟩ :=
    exists_strictMono_forall_of_subseq_property E hdown hsub htail (σ₀ ∘ ψ₀)
  have hE₁ : E (σ₀ ∘ (ψ₀ ∘ ψ₁)) T₀ := hsub (σ₀ ∘ ψ₀) ψ₁ T₀ hψ₁ hE₀
  refine ⟨ψ₀ ∘ ψ₁, hψ₀.comp hψ₁, ?_⟩
  let S : Set ℝ := {T | 0 < T ∧ E (σ₀ ∘ (ψ₀ ∘ ψ₁)) T}
  have hT₀S : T₀ ∈ S := ⟨hT₀, hE₁⟩
  by_cases hbdd : BddAbove S
  · right
    have hle : T₀ ≤ sSup S := le_csSup hbdd hT₀S
    refine ⟨sSup S, hT₀.trans_le hle, fun T hT hTs => ?_, fun χ hχ T hT hE => ?_⟩
    · obtain ⟨T'', hT''S, hTT''⟩ := exists_lt_of_lt_csSup ⟨T₀, hT₀S⟩ hTs
      exact hdown _ _ _ hT hTT''.le hT''S.2
    · obtain ⟨T', hT's, hT'T⟩ := exists_between hT
      have hT'pos : 0 < T' := (hT₀.trans_le hle).trans hT's
      have hE' : E (σ₀ ∘ (ψ₀ ∘ ψ₁)) T' := hmax χ hχ T T' hT'pos hT'T hE
      exact absurd (le_csSup hbdd ⟨hT'pos, hE'⟩) (not_le.mpr hT's)
  · left
    intro T hT
    rw [not_bddAbove_iff] at hbdd
    obtain ⟨T'', hT''S, hTT''⟩ := hbdd T
    exact hdown _ _ _ hT hTT''.le hT''S.2

end DifferentialGeometry
