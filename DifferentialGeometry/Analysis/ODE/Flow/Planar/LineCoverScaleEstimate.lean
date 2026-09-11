import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section
open Set

namespace DifferentialGeometry.Analysis

private theorem scaled_error_lt (A E r Q R η : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hr : 0 ≤ r) (hr' : r ≤ 1 / 2) (hQ : 0 < Q) (hR : 0 < R)
    (hη : (Real.sqrt Q)⁻¹ ≤ η) (hQR : Q ≤ 4 * R) (hsmall : 24 * A * E < 1) :
    4 * ((A / η) * (1 + r)) * (E / Real.sqrt R) < 1 - r := by
  have hq := Real.sqrt_pos.mpr hQ
  have hroot : Real.sqrt Q ≤ 2 * Real.sqrt R := by
    calc
      _ ≤ Real.sqrt (4 * R) := Real.sqrt_le_sqrt hQR
      _ = _ := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hηpos : 0 < η := (inv_pos.mpr hq).trans_le hη
  have hηmul : 1 ≤ η * Real.sqrt Q :=
    (div_le_iff₀ hq).mp (by simpa only [one_div] using hη)
  have hdiv : A / η ≤ A * (2 * Real.sqrt R) := by
    apply (le_trans ?_ (mul_le_mul_of_nonneg_left hroot hA))
    apply (div_le_iff₀ hηpos).mpr
    nlinarith only [hηmul, hA]
  have h1r : 0 ≤ 1 + r := by linarith only [hr]
  have hquot : 0 ≤ E / Real.sqrt R := div_nonneg hE (Real.sqrt_nonneg _)
  calc
    _ ≤ 4 * ((A * (2 * Real.sqrt R)) * (1 + r)) * (E / Real.sqrt R) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdiv h1r) (by norm_num)) hquot
    _ = 8 * A * (1 + r) * E := by
      field_simp
      ring
    _ ≤ 12 * A * E := by nlinarith only [mul_nonneg hA hE, hr']
    _ < 1 / 2 := by linarith only [hsmall]
    _ ≤ 1 - r := by linarith only [hr']

theorem exists_overlap_error_bound_of_line_cover
    {n : ℕ} {X : Type*} (K : Fin (n + 1) → Set X)
    (hline : ∀ x i, x ∈ K i → ∀ j, x ∈ K j → i.val ≤ j.val + 1)
    (Q η : Fin (n + 1) → ℝ) (hQ : ∀ i, 0 < Q i)
    (hη : ∀ i, (Real.sqrt (Q i))⁻¹ ≤ η i)
    (e : Fin n → ℝ) (A E r : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hr : 0 ≤ r) (hr' : r ≤ 1 / 2) (hsmall : 24 * A * E < 1)
    (hratio : ∀ j : Fin n, |Q j.castSucc / Q j.succ - 1| ≤ 1 / 2)
    (he : ∀ j : Fin n, ∀ x ∈ K j.castSucc, x ∈ K j.succ → e j ≤ E / Real.sqrt (Q j.castSucc)) :
    ∃ Δ : X → ℝ, (∀ x, 0 ≤ Δ x) ∧
      (∀ j : Fin n, ∀ x ∈ K j.castSucc, x ∈ K j.succ → e j ≤ Δ x) ∧
      ∀ x i, x ∈ K i → 4 * ((A / η i) * (1 + r)) * Δ x < 1 - r := by
  classical
  let P (x : X) (j : Fin n) : Prop := x ∈ K j.castSucc ∧ x ∈ K j.succ
  have hedge {x : X} {j k : Fin n} (hj : P x j) (hk : P x k) : j = k := by
    have h₁ := hline x j.succ hj.2 k.castSucc hk.1
    have h₂ := hline x k.succ hk.2 j.castSucc hj.1
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castSucc] at h₁ h₂
    omega
  let Δ : X → ℝ := fun x ↦ if h : ∃ j, P x j then E / Real.sqrt (Q h.choose.castSucc) else 0
  refine ⟨Δ, ?_, ?_, ?_⟩
  · intro x
    dsimp only [Δ]
    split_ifs
    · exact div_nonneg hE (Real.sqrt_nonneg _)
    · exact le_rfl
  · intro j x hx hy
    have hj : P x j := ⟨hx, hy⟩
    have h : ∃ k, P x k := ⟨j, hj⟩
    have heq : h.choose = j := hedge h.choose_spec hj
    dsimp only [Δ]
    rw [dif_pos h, heq]
    exact he j x hx hy
  · intro x i hi
    dsimp only [Δ]
    split_ifs with h
    · let j := h.choose
      have hj : P x j := h.choose_spec
      have h₁ := hline x j.succ hj.2 i hi
      have h₂ := hline x i hi j.castSucc hj.1
      have hwhich : i = j.castSucc ∨ i = j.succ := by
        simp only [Fin.val_succ, Fin.val_castSucc] at h₁ h₂
        have hv : i.val = j.val ∨ i.val = j.val + 1 := by omega
        rcases hv with hv | hv
        · exact Or.inl (Fin.ext hv)
        · exact Or.inr (Fin.ext hv)
      apply scaled_error_lt A E r (Q i) (Q j.castSucc) (η i) hA hE hr hr' (hQ i)
        (hQ j.castSucc) (hη i) _ hsmall
      rcases hwhich with rfl | rfl
      · linarith only [hQ j.castSucc]
      · have hlo : (1 : ℝ) / 2 ≤ Q j.castSucc / Q j.succ := by
          have hh := (abs_le.mp (hratio j)).1
          linarith only [hh]
        have hh := (le_div_iff₀ (hQ j.succ)).mp hlo
        linarith only [hh, hQ j.castSucc]
    · simp only [mul_zero]
      linarith only [hr']

theorem exists_overlap_error_bound_of_line_cover_with_margin
    {n : ℕ} {X : Type*} (m : ℝ) (hm : 0 < m) (K : Fin (n + 1) → Set X)
    (hline : ∀ x i, x ∈ K i → ∀ j, x ∈ K j → i.val ≤ j.val + 1)
    (Q η : Fin (n + 1) → ℝ) (hQ : ∀ i, 0 < Q i)
    (hη : ∀ i, m * (Real.sqrt (Q i))⁻¹ ≤ η i)
    (e : Fin n → ℝ) (A E r : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hr : 0 ≤ r) (hr' : r ≤ 1 / 2) (hsmall : 24 * A * E < m)
    (hratio : ∀ j : Fin n, |Q j.castSucc / Q j.succ - 1| ≤ 1 / 2)
    (he : ∀ j : Fin n, ∀ x ∈ K j.castSucc, x ∈ K j.succ → e j ≤ E / Real.sqrt (Q j.castSucc)) :
    ∃ Δ : X → ℝ, (∀ x, 0 ≤ Δ x) ∧
      (∀ j : Fin n, ∀ x ∈ K j.castSucc, x ∈ K j.succ → e j ≤ Δ x) ∧
      ∀ x i, x ∈ K i → 4 * ((A / η i) * (1 + r)) * Δ x < 1 - r := by
  have hwidth (i) : (Real.sqrt (Q i))⁻¹ ≤ η i / m :=
    (le_div_iff₀ hm).mpr (by simpa only [mul_comm] using hη i)
  have hsmall' : 24 * (A / m) * E < 1 := by
    have h : (24 * A * E) / m < 1 := (div_lt_one hm).mpr hsmall
    convert h using 1
    ring
  obtain ⟨Δ, hΔ, heΔ, hb⟩ := exists_overlap_error_bound_of_line_cover K hline Q
    (fun i ↦ η i / m) hQ hwidth e (A / m) E r (div_nonneg hA hm.le) hE hr hr'
    hsmall' hratio he
  refine ⟨Δ, hΔ, heΔ, ?_⟩
  intro x i hi
  simpa only [div_div_div_cancel_right₀ hm.ne'] using hb x i hi

end DifferentialGeometry.Analysis
