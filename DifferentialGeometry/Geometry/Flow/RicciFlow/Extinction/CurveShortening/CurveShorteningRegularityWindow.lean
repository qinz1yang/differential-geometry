import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Set

def CurveShorteningRegularityWindow (a b : ℝ) : Prop :=
  ∀ (T : ℝ), a < T → T ≤ b → ∀ J : Set ℝ, (J = Ico a T ∨ J = Icc a T) →
    ∀ tstar ∈ Ico a T, ∀ d : ℝ, 0 ≤ d → tstar + d ∈ J →
      Icc (tstar + d / 2) (tstar + d) ⊆ J

namespace CurveShorteningRegularityWindow

theorem window_subset {a b T tstar d : ℝ} {J : Set ℝ}
    (hW : CurveShorteningRegularityWindow a b) (hT : a < T) (hTb : T ≤ b)
    (hJ : J = Ico a T ∨ J = Icc a T) (htstar : tstar ∈ Ico a T)
    (hd : 0 ≤ d) (hend : tstar + d ∈ J) :
    Icc (tstar + d / 2) (tstar + d) ⊆ J :=
  hW T hT hTb J hJ tstar htstar d hd hend

theorem of_mem_endpoint (a b : ℝ) : CurveShorteningRegularityWindow a b := by
  intro T hT hTb J hJ tstar htstar d hd hend t ht
  have h1 : a ≤ t := le_trans htstar.1 (le_trans (by linarith : tstar ≤ tstar + d / 2) ht.1)
  have h2 : t ≤ tstar + d := ht.2
  rcases hJ with h | h
  · rw [h] at hend ⊢
    exact ⟨h1, lt_of_le_of_lt h2 hend.2⟩
  · rw [h] at hend ⊢
    exact ⟨h1, le_trans h2 hend.2⟩

theorem window_subset_delta {a b T tstar δ r : ℝ} {J : Set ℝ}
    (hW : CurveShorteningRegularityWindow a b) (hT : a < T) (hTb : T ≤ b)
    (hJ : J = Ico a T ∨ J = Icc a T) (htstar : tstar ∈ Ico a T)
    (hδ : 0 < δ) (hr : 0 < r) (hfit : tstar + δ * r ^ 2 ∈ J) :
    Icc (tstar + δ * r ^ 2 / 2) (tstar + δ * r ^ 2) ⊆ J :=
  hW.window_subset hT hTb hJ htstar (by positivity) hfit

theorem Ico_subset_Icc {a T : ℝ} : Ico a T ⊆ Icc a T := fun _ ht => ⟨ht.1, ht.2.le⟩

theorem Ico_subset_Ico {a T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : Ico a T₁ ⊆ Ico a T₂ :=
  fun _ ht => ⟨ht.1, lt_of_lt_of_le ht.2 h⟩

theorem Ico_subset_Icc_of_le {a T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : Ico a T₁ ⊆ Icc a T₂ :=
  fun _ ht => ⟨ht.1, le_trans ht.2.le h⟩

theorem mem_J_of_mem_Ico {a T : ℝ} {J : Set ℝ} (hJ : J = Ico a T ∨ J = Icc a T)
    {tstar : ℝ} (ht : tstar ∈ Ico a T) : tstar ∈ J := by
  rcases hJ with h | h
  · rw [h]; exact ht
  · rw [h]; exact ⟨ht.1, ht.2.le⟩

theorem lt_and_le_of_mem_window {tstar d t : ℝ} (hd : 0 < d)
    (ht : t ∈ Icc (tstar + d / 2) (tstar + d)) : tstar < t ∧ t ≤ tstar + d :=
  ⟨lt_of_lt_of_le (by linarith) ht.1, ht.2⟩

theorem Ioc_eq_Ioc_union_Icc {tstar d : ℝ} (hd : 0 < d) :
    Ioc tstar (tstar + d) = Ioc tstar (tstar + d / 2) ∪ Icc (tstar + d / 2) (tstar + d) := by
  ext t
  constructor
  · intro ht
    by_cases h : t ≤ tstar + d / 2
    · exact Or.inl ⟨ht.1, h⟩
    · exact Or.inr ⟨(not_le.mp h).le, ht.2⟩
  · intro ht
    rcases ht with ht | ht
    · exact ⟨ht.1, le_trans ht.2 (by linarith)⟩
    · exact ⟨lt_of_lt_of_le (by linarith) ht.1, ht.2⟩

theorem forall_mem_Ioc_iff {tstar d : ℝ} (hd : 0 < d) (P : ℝ → Prop) :
    (∀ t ∈ Ioc tstar (tstar + d), P t) ↔
      (∀ t ∈ Ioc tstar (tstar + d / 2), P t) ∧
        (∀ t ∈ Icc (tstar + d / 2) (tstar + d), P t) := by
  rw [Ioc_eq_Ioc_union_Icc hd]
  constructor
  · intro h
    exact ⟨fun t ht => h t (Or.inl ht), fun t ht => h t (Or.inr ht)⟩
  · rintro ⟨h1, h2⟩ t ht
    rcases ht with ht | ht
    · exact h1 t ht
    · exact h2 t ht

theorem iff_forall_mem_of_subset {tstar d : ℝ} {J : Set ℝ} (P : ℝ → Prop)
    (hsub : Ioc tstar (tstar + d) ⊆ J) :
    (∀ t ∈ J, tstar < t → t ≤ tstar + d → P t) ↔ (∀ t ∈ Ioc tstar (tstar + d), P t) := by
  constructor
  · intro h t ht
    exact h t (hsub ht) ht.1 ht.2
  · intro h t _ h1 h2
    exact h t ⟨h1, h2⟩

theorem Ioc_subset_iff_mem_endpoint {a T : ℝ} {J : Set ℝ} (hJ : J = Ico a T ∨ J = Icc a T)
    {tstar : ℝ} (ht : tstar ∈ Ico a T) {d : ℝ} (hd : 0 ≤ d) :
    Ioc tstar (tstar + d) ⊆ J ↔ tstar + d ∈ J := by
  constructor
  · intro hsub
    rcases eq_or_lt_of_le hd with h0 | hpos
    · rw [← h0, add_zero]
      exact mem_J_of_mem_Ico hJ ht
    · exact hsub ⟨by linarith, le_refl _⟩
  · intro hend
    rcases hJ with h | h
    · rw [h] at hend ⊢
      intro hx hmem
      exact ⟨le_trans ht.1 hmem.1.le, lt_of_le_of_lt hmem.2 hend.2⟩
    · rw [h] at hend ⊢
      intro hx hmem
      exact ⟨le_trans ht.1 hmem.1.le, le_trans hmem.2 hend.2⟩

theorem forall_mem_of_window_of_inner {tstar d : ℝ} {J : Set ℝ} (P : ℝ → Prop)
    (hinner : ∀ t ∈ Ioc tstar (tstar + d / 2), P t)
    (hwindow : ∀ t ∈ Icc (tstar + d / 2) (tstar + d), P t) :
    ∀ t ∈ J, tstar < t → t ≤ tstar + d → P t := by
  intro t _ h1 h2
  by_cases h : t ≤ tstar + d / 2
  · exact hinner t ⟨h1, h⟩
  · exact hwindow t ⟨(not_le.mp h).le, h2⟩

theorem window_of_forall_mem {a b T tstar d : ℝ} {J : Set ℝ}
    (hW : CurveShorteningRegularityWindow a b) (hT : a < T) (hTb : T ≤ b)
    (hJ : J = Ico a T ∨ J = Icc a T) (htstar : tstar ∈ Ico a T) (hd : 0 < d)
    (hend : tstar + d ∈ J) (P : ℝ → Prop)
    (h : ∀ t ∈ J, tstar < t → t ≤ tstar + d → P t) :
    ∀ t ∈ Icc (tstar + d / 2) (tstar + d), P t := by
  intro t ht
  obtain ⟨h1, h2⟩ := lt_and_le_of_mem_window hd ht
  exact h t (hW.window_subset hT hTb hJ htstar hd.le hend ht) h1 h2

theorem forall_mem_of_zero_window {J : Set ℝ} (P : ℝ → Prop) (tstar : ℝ) :
    ∀ t ∈ J, tstar < t → t ≤ tstar + 0 → P t := by
  intro t _ h1 h2
  rw [add_zero] at h2
  exact absurd h2 (not_le.mpr h1)

theorem not_window_subset_of_overflow :
    ¬ (Icc ((3 : ℝ) / 4) ((5 : ℝ) / 4) ⊆ Ico (0 : ℝ) (1 / 2)) := by
  intro h
  have hmem : (5 : ℝ) / 4 ∈ Ico (0 : ℝ) (1 / 2) := h (by norm_num [Set.mem_Icc])
  norm_num [Set.mem_Ico] at hmem

theorem witness_Icc :
    (1 / 2 : ℝ) ∈ Ico (0 : ℝ) 1 ∧
      Icc ((1 / 2 : ℝ) + (1 / 2) * (1 / 4 : ℝ) ^ 2 / 2)
        ((1 / 2 : ℝ) + (1 / 2) * (1 / 4 : ℝ) ^ 2) ⊆ Icc (0 : ℝ) 1 ∧
      (33 / 64 : ℝ) ∈ Icc (0 : ℝ) 1 ∧
      (1 / 2 : ℝ) < 33 / 64 ∧ (33 / 64 : ℝ) ≤ 1 / 2 + (1 / 2) * (1 / 4 : ℝ) ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [Set.mem_Ico]
  · intro t ht
    simp only [Set.mem_Icc] at ht ⊢
    norm_num at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  · norm_num [Set.mem_Icc]
  · norm_num
  · norm_num

theorem witness_Ico :
    (1 / 2 : ℝ) ∈ Ico (0 : ℝ) 1 ∧
      Icc ((1 / 2 : ℝ) + (1 / 2) * (1 / 2 : ℝ) ^ 2 / 2)
        ((1 / 2 : ℝ) + (1 / 2) * (1 / 2 : ℝ) ^ 2) ⊆ Ico (0 : ℝ) 1 ∧
      (9 / 16 : ℝ) ∈ Ico (0 : ℝ) 1 ∧
      (1 / 2 : ℝ) < 9 / 16 ∧ (9 / 16 : ℝ) ≤ 1 / 2 + (1 / 2) * (1 / 2 : ℝ) ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [Set.mem_Ico]
  · intro t ht
    simp only [Set.mem_Ico] at ⊢
    simp only [Set.mem_Icc] at ht
    norm_num at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  · norm_num [Set.mem_Ico]
  · norm_num
  · norm_num

end CurveShorteningRegularityWindow

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
