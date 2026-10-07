import Mathlib

/-!
# CH12-S94 G2 (a): the numeric constants of `hsub86N_S94` (pure real arithmetic)

`hsub86N_consts_S94`: given `A, rbar, C > 0`, `1 ≤ C2`, `0 ≤ ct` and the thresholds `T₀, B`, the constants
`A' = A + rbar²`, `Cb = ct + 1`, `Q = 32 C2 A'`, `κ₀ = 1/(10(Q+1))`, `K = C Q κ₀²/4`, `Λs = √(18K)+1`,
`τs`, `τ₁ = 1/(64 Cb A')`, `τ₂ = τs κ₀²/4`, `C₁`, `T` with all positivity / order facts used downstream.
(Kept in its own theorem: a single declaration with the big `hev` binder plus these facts exceeds
200000 heartbeats.)
-/

set_option autoImplicit false

namespace GC.LongTime.Ch12

theorem hsub86N_consts_S94 {A rbar C C2 ct T₀ B : ℝ} (hA1 : 1 ≤ A) (hrbar : 0 < rbar) (hCpos : 0 < C)
    (hC2 : 1 ≤ C2) (hct : 0 ≤ ct) (hT₀ : 0 < T₀) :
    ∃ A' Cb Q κ₀ K Λs τs τ₁ τ₂ C₁ T : ℝ,
      A' = A + rbar ^ 2 ∧ A < A' ∧ 1 ≤ A' ∧ Cb = ct + 1 ∧ 0 < Cb ∧ ct ≤ Cb ∧
      Q = 32 * C2 * A' ∧ 0 < Q ∧ κ₀ = 1 / (10 * (Q + 1)) ∧ 0 < κ₀ ∧
      K = C * Q * κ₀ ^ 2 / 4 ∧ 0 < K ∧ 1 ≤ Λs ∧ 2 * (9 * K) < Λs ^ 2 ∧
      0 < τs ∧ Real.exp (9 * K * τs) < 2 ∧ τ₁ = 1 / (64 * Cb * A') ∧ 0 < τ₁ ∧
      τ₂ = τs * κ₀ ^ 2 / 4 ∧ 0 < τ₂ ∧ τ₂ ≤ τ₁ ∧
      1 ≤ C₁ ∧ 8 * A' + 1 ≤ C₁ ∧ 2 * Λs / κ₀ ≤ C₁ ∧
      T₀ ≤ T ∧ 2 * (B + 1) ≤ T ∧ 2 * (τ₁ + τ₂) * rbar ^ 2 ≤ T ∧ 0 < T := by
  have hA0 : 0 < A := by linarith
  obtain ⟨A', hA'def⟩ : ∃ A' : ℝ, A' = A + rbar ^ 2 := ⟨_, rfl⟩
  have hA'1 : 1 ≤ A' := by nlinarith [sq_nonneg rbar]
  obtain ⟨Cb, hCbdef⟩ : ∃ Cb : ℝ, Cb = ct + 1 := ⟨_, rfl⟩
  have hCb : 0 < Cb := by rw [hCbdef]; positivity
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = 32 * C2 * A' := ⟨_, rfl⟩
  have hQ : 0 < Q := by rw [hQdef]; positivity
  obtain ⟨κ₀, hκdef⟩ : ∃ κ₀ : ℝ, κ₀ = 1 / (10 * (Q + 1)) := ⟨_, rfl⟩
  have hκ : 0 < κ₀ := by rw [hκdef]; positivity
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = C * Q * κ₀ ^ 2 / 4 := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hKdef]; positivity
  obtain ⟨Λs, hΛsdef⟩ : ∃ Λs : ℝ, Λs = Real.sqrt (18 * K) + 1 := ⟨_, rfl⟩
  have hΛs1 : 1 ≤ Λs := by rw [hΛsdef]; linarith [Real.sqrt_nonneg (18 * K)]
  have hΛsK : 2 * (9 * K) < Λs ^ 2 := by
    have h := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 18 * K)
    rw [hΛsdef]; nlinarith [Real.sqrt_nonneg (18 * K)]
  obtain ⟨τs, hτsdef⟩ : ∃ τs : ℝ, τs = min (Real.log 2 / (18 * K + 1)) (4 / (64 * Cb * A' * κ₀ ^ 2)) :=
    ⟨_, rfl⟩
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hτs : 0 < τs := by rw [hτsdef]; exact lt_min (by positivity) (by positivity)
  have hτs1 : τs ≤ Real.log 2 / (18 * K + 1) := hτsdef ▸ min_le_left _ _
  have hτs2 : τs ≤ 4 / (64 * Cb * A' * κ₀ ^ 2) := hτsdef ▸ min_le_right _ _
  have hexp : Real.exp (9 * K * τs) < 2 := by
    have h1 := (le_div_iff₀ (by positivity : 0 < 18 * K + 1)).mp hτs1
    have hkt : 0 < K * τs := mul_pos hK hτs
    have : 9 * K * τs < Real.log 2 := by nlinarith
    exact (Real.exp_lt_exp.mpr this).trans_eq (Real.exp_log (by norm_num))
  obtain ⟨τ₁, hτ₁def⟩ : ∃ τ₁ : ℝ, τ₁ = 1 / (64 * Cb * A') := ⟨_, rfl⟩
  have hτ₁ : 0 < τ₁ := by rw [hτ₁def]; positivity
  obtain ⟨τ₂, hτ₂def⟩ : ∃ τ₂ : ℝ, τ₂ = τs * κ₀ ^ 2 / 4 := ⟨_, rfl⟩
  have hτ₂ : 0 < τ₂ := by rw [hτ₂def]; positivity
  have hτ₂le : τ₂ ≤ τ₁ := by
    rw [hτ₂def, hτ₁def]
    have h := mul_le_mul_of_nonneg_right hτs2 (by positivity : 0 ≤ κ₀ ^ 2 / 4)
    calc τs * κ₀ ^ 2 / 4 = τs * (κ₀ ^ 2 / 4) := by ring
      _ ≤ 4 / (64 * Cb * A' * κ₀ ^ 2) * (κ₀ ^ 2 / 4) := h
      _ = 1 / (64 * Cb * A') := by field_simp
  obtain ⟨C₁, hC₁def⟩ : ∃ C₁ : ℝ, C₁ = max (2 * Λs / κ₀) (8 * A' + 1) := ⟨_, rfl⟩
  have hC₁1 : 1 ≤ C₁ := by rw [hC₁def]; exact le_max_of_le_right (by linarith)
  have hC₁A : 8 * A' + 1 ≤ C₁ := hC₁def ▸ le_max_right _ _
  have hC₁Λ : 2 * Λs / κ₀ ≤ C₁ := hC₁def ▸ le_max_left _ _
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = max (max T₀ (2 * (B + 1))) (2 * (τ₁ + τ₂) * rbar ^ 2) + 1 := ⟨_, rfl⟩
  have hTT₀ : T₀ ≤ T := by rw [hTdef]; linarith [le_max_left (max T₀ (2 * (B + 1))) (2 * (τ₁ + τ₂) * rbar ^ 2), le_max_left T₀ (2 * (B + 1))]
  have hTB : 2 * (B + 1) ≤ T := by rw [hTdef]; linarith [le_max_left (max T₀ (2 * (B + 1))) (2 * (τ₁ + τ₂) * rbar ^ 2), le_max_right T₀ (2 * (B + 1))]
  have hTL : 2 * (τ₁ + τ₂) * rbar ^ 2 ≤ T := by rw [hTdef]; linarith [le_max_right (max T₀ (2 * (B + 1))) (2 * (τ₁ + τ₂) * rbar ^ 2)]
  have hT : 0 < T := by rw [hTdef]; linarith [le_max_left (max T₀ (2 * (B + 1))) (2 * (τ₁ + τ₂) * rbar ^ 2), le_max_left T₀ (2 * (B + 1))]
  have hAA' : A < A' := by rw [hA'def]; nlinarith [sq_pos_of_pos hrbar]
  have hCbC : ct ≤ Cb := by rw [hCbdef]; linarith
  exact ⟨A', Cb, Q, κ₀, K, Λs, τs, τ₁, τ₂, C₁, T, hA'def, hAA', hA'1, hCbdef, hCb, hCbC, hQdef, hQ, hκdef, hκ,
    hKdef, hK, hΛs1, hΛsK, hτs, hexp, hτ₁def, hτ₁, hτ₂def, hτ₂, hτ₂le, hC₁1, hC₁A, hC₁Λ, hTT₀, hTB, hTL, hT⟩

end GC.LongTime.Ch12
