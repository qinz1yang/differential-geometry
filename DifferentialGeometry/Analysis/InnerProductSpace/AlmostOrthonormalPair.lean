import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Almost orthonormal pairs (LFR06, the Gram-matrix estimate)

Blueprint 207A, LFR06 (`thm:collapse-rank-two-adapted-existence`, A:25225–25320), the "one additional
estimate": two gradients `wⱼ` within `ε` of unit vectors `uⱼ` with `|⟪u₁, u₂⟫| ≤ δ` give a linear map
`v ↦ (⟪w₁, v⟫, ⟪w₂, v⟫)` of norm at most `√(1 + δ) + √2 ε` (instead of the crude `√2`), surjective
onto `ℝ²` when `δ + 4ε < 1`.

* `inner_sq_add_inner_sq_le_of_unit`: Bessel's inequality `⟪u₁,v⟫² + ⟪u₂,v⟫² ≤ (1 + δ)‖v‖²`.
* `almostOrthonormal_pair_bounds`: the norm bound and the surjectivity (Cramer's rule on the Gram
  matrix, whose determinant is positive).
-/

set_option autoImplicit false

open scoped RealInnerProductSpace

namespace DifferentialGeometry.Analysis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Bessel's inequality for two almost orthogonal unit vectors. -/
theorem inner_sq_add_inner_sq_le_of_unit {u₁ u₂ : V} (hu₁ : ‖u₁‖ = 1) (hu₂ : ‖u₂‖ = 1) {δ : ℝ}
    (hδ : |⟪u₁, u₂⟫| ≤ δ) (v : V) :
    ⟪u₁, v⟫ ^ 2 + ⟪u₂, v⟫ ^ 2 ≤ (1 + δ) * ‖v‖ ^ 2 := by
  set p := ⟪u₁, v⟫
  set r := ⟪u₂, v⟫
  set z : V := p • u₁ + r • u₂
  have hz : ⟪z, v⟫ = p ^ 2 + r ^ 2 := by
    simp only [z, inner_add_left, inner_smul_left, RCLike.conj_to_real, p, r]
    ring
  have hzz : ‖z‖ ^ 2 ≤ (1 + δ) * (p ^ 2 + r ^ 2) := by
    rw [← real_inner_self_eq_norm_sq]
    have h11 : ⟪u₁, u₁⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu₁, one_pow]
    have h22 : ⟪u₂, u₂⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu₂, one_pow]
    have hexp : ⟪z, z⟫ = p ^ 2 + r ^ 2 + 2 * p * r * ⟪u₁, u₂⟫ := by
      simp only [z, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
        RCLike.conj_to_real, h11, h22, real_inner_comm u₂ u₁]
      ring
    rw [hexp]
    have h2pr : |2 * p * r| ≤ p ^ 2 + r ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (p + r), sq_nonneg (p - r)]
    have : 2 * p * r * ⟪u₁, u₂⟫ ≤ δ * (p ^ 2 + r ^ 2) := by
      calc 2 * p * r * ⟪u₁, u₂⟫ ≤ |2 * p * r * ⟪u₁, u₂⟫| := le_abs_self _
        _ = |2 * p * r| * |⟪u₁, u₂⟫| := abs_mul _ _
        _ ≤ (p ^ 2 + r ^ 2) * δ :=
          mul_le_mul h2pr hδ (abs_nonneg _) (by positivity)
        _ = δ * (p ^ 2 + r ^ 2) := by ring
    linarith
  have hcs : p ^ 2 + r ^ 2 ≤ ‖z‖ * ‖v‖ := hz ▸ real_inner_le_norm z v
  have hS : 0 ≤ p ^ 2 + r ^ 2 := by positivity
  have hδ0 : 0 ≤ 1 + δ := by linarith [abs_nonneg ⟪u₁, u₂⟫]
  -- (p²+r²)² ≤ ‖z‖²‖v‖² ≤ (1+δ)(p²+r²)‖v‖²
  have hsq : (p ^ 2 + r ^ 2) ^ 2 ≤ (1 + δ) * (p ^ 2 + r ^ 2) * ‖v‖ ^ 2 := by
    have h1 : (p ^ 2 + r ^ 2) ^ 2 ≤ (‖z‖ * ‖v‖) ^ 2 := pow_le_pow_left₀ hS hcs 2
    rw [mul_pow] at h1
    nlinarith [sq_nonneg ‖v‖]
  rcases hS.lt_or_eq with hpos | hzero
  · nlinarith
  · rw [← hzero]
    positivity


/-- Perturbations of an almost orthonormal pair: if `‖wⱼ − uⱼ‖ ≤ ε` for unit `u₁, u₂` with
`|⟪u₁, u₂⟫| ≤ δ`, then `v ↦ (⟪w₁, v⟫, ⟪w₂, v⟫)` has norm at most `√(1 + δ) + √2 ε`, and it is
surjective onto `ℝ²` as soon as `δ + 4ε < 1`. -/
theorem almostOrthonormal_pair_bounds {u₁ u₂ w₁ w₂ : V} (hu₁ : ‖u₁‖ = 1) (hu₂ : ‖u₂‖ = 1)
    {ε δ : ℝ} (hε : 0 ≤ ε) (h₁ : ‖w₁ - u₁‖ ≤ ε) (h₂ : ‖w₂ - u₂‖ ≤ ε) (hδ : |⟪u₁, u₂⟫| ≤ δ) :
    (∀ v : V, ⟪w₁, v⟫ ^ 2 + ⟪w₂, v⟫ ^ 2 ≤ ((Real.sqrt (1 + δ) + Real.sqrt 2 * ε) * ‖v‖) ^ 2) ∧
      (δ + 4 * ε < 1 → ∀ s₁ s₂ : ℝ, ∃ v : V, ⟪w₁, v⟫ = s₁ ∧ ⟪w₂, v⟫ = s₂) := by
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hδ
  constructor
  · intro v
    set a₁ := ⟪u₁, v⟫
    set a₂ := ⟪u₂, v⟫
    set b₁ := ⟪w₁ - u₁, v⟫
    set b₂ := ⟪w₂ - u₂, v⟫
    have hw₁ : ⟪w₁, v⟫ = a₁ + b₁ := by simp [a₁, b₁, inner_sub_left]
    have hw₂ : ⟪w₂, v⟫ = a₂ + b₂ := by simp [a₂, b₂, inner_sub_left]
    have hb₁ : |b₁| ≤ ε * ‖v‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right h₁ (norm_nonneg _))
    have hb₂ : |b₂| ≤ ε * ‖v‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right h₂ (norm_nonneg _))
    have ha : a₁ ^ 2 + a₂ ^ 2 ≤ (1 + δ) * ‖v‖ ^ 2 := inner_sq_add_inner_sq_le_of_unit hu₁ hu₂ hδ v
    have hb : b₁ ^ 2 + b₂ ^ 2 ≤ (Real.sqrt 2 * ε * ‖v‖) ^ 2 := by
      have e1 : b₁ ^ 2 ≤ (ε * ‖v‖) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb₁ 2
      have e2 : b₂ ^ 2 ≤ (ε * ‖v‖) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb₂ 2
      have : (Real.sqrt 2 * ε * ‖v‖) ^ 2 = 2 * (ε * ‖v‖) ^ 2 := by
        rw [mul_assoc, mul_pow, Real.sq_sqrt (by norm_num)]
      rw [this]
      linarith
    set A := Real.sqrt (1 + δ) * ‖v‖
    set B := Real.sqrt 2 * ε * ‖v‖
    have hA0 : 0 ≤ A := by positivity
    have hB0 : 0 ≤ B := by positivity
    have hA : a₁ ^ 2 + a₂ ^ 2 ≤ A ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]
      exact ha
    have hcs : a₁ * b₁ + a₂ * b₂ ≤ A * B := by
      have h1 : (a₁ * b₁ + a₂ * b₂) ^ 2 ≤ (a₁ ^ 2 + a₂ ^ 2) * (b₁ ^ 2 + b₂ ^ 2) := by
        nlinarith [sq_nonneg (a₁ * b₂ - a₂ * b₁)]
      have h2 : (a₁ ^ 2 + a₂ ^ 2) * (b₁ ^ 2 + b₂ ^ 2) ≤ (A * B) ^ 2 := by
        rw [mul_pow]
        exact mul_le_mul hA hb (by positivity) (by positivity)
      have h3 := h1.trans h2
      exact abs_le_of_sq_le_sq' h3 (by positivity) |>.2
    rw [hw₁, hw₂, show (Real.sqrt (1 + δ) + Real.sqrt 2 * ε) * ‖v‖ = A + B by ring]
    nlinarith
  · intro hsmall s₁ s₂
    have hε4 : ε < 1 / 4 := by linarith
    have hn₁ : 1 - ε ≤ ‖w₁‖ := by
      have := norm_sub_norm_le u₁ (u₁ - w₁)
      rw [sub_sub_cancel, norm_sub_rev] at this
      linarith
    have hn₂ : 1 - ε ≤ ‖w₂‖ := by
      have := norm_sub_norm_le u₂ (u₂ - w₂)
      rw [sub_sub_cancel, norm_sub_rev] at this
      linarith
    have hC : |⟪w₁, w₂⟫| ≤ δ + 2 * ε + ε ^ 2 := by
      have hsplit : ⟪w₁, w₂⟫ = ⟪u₁, u₂⟫ + ⟪w₁ - u₁, u₂⟫ + ⟪u₁, w₂ - u₂⟫ + ⟪w₁ - u₁, w₂ - u₂⟫ := by
        simp only [inner_sub_left, inner_sub_right]
        ring
      rw [hsplit]
      have t1 : |⟪w₁ - u₁, u₂⟫| ≤ ε := by
        have := abs_real_inner_le_norm (w₁ - u₁) u₂
        rw [hu₂, mul_one] at this; linarith
      have t2 : |⟪u₁, w₂ - u₂⟫| ≤ ε := by
        have := abs_real_inner_le_norm u₁ (w₂ - u₂)
        rw [hu₁, one_mul] at this; linarith
      have t3 : |⟪w₁ - u₁, w₂ - u₂⟫| ≤ ε ^ 2 := by
        have := abs_real_inner_le_norm (w₁ - u₁) (w₂ - u₂)
        nlinarith [norm_nonneg (w₁ - u₁), norm_nonneg (w₂ - u₂)]
      calc _ ≤ |⟪u₁, u₂⟫ + ⟪w₁ - u₁, u₂⟫ + ⟪u₁, w₂ - u₂⟫| + |⟪w₁ - u₁, w₂ - u₂⟫| := abs_add_le _ _
        _ ≤ |⟪u₁, u₂⟫ + ⟪w₁ - u₁, u₂⟫| + |⟪u₁, w₂ - u₂⟫| + |⟪w₁ - u₁, w₂ - u₂⟫| := by
          gcongr; exact abs_add_le _ _
        _ ≤ |⟪u₁, u₂⟫| + |⟪w₁ - u₁, u₂⟫| + |⟪u₁, w₂ - u₂⟫| + |⟪w₁ - u₁, w₂ - u₂⟫| := by
          gcongr; exact abs_add_le _ _
        _ ≤ δ + ε + ε + ε ^ 2 := by gcongr
        _ = δ + 2 * ε + ε ^ 2 := by ring
    have hA : (1 - ε) ^ 2 ≤ ⟪w₁, w₁⟫ := by
      rw [real_inner_self_eq_norm_sq]; exact pow_le_pow_left₀ (by linarith) hn₁ 2
    have hB : (1 - ε) ^ 2 ≤ ⟪w₂, w₂⟫ := by
      rw [real_inner_self_eq_norm_sq]; exact pow_le_pow_left₀ (by linarith) hn₂ 2
    set A := ⟪w₁, w₁⟫
    set B := ⟪w₂, w₂⟫
    set C := ⟪w₁, w₂⟫
    have hCl : |C| < (1 - ε) ^ 2 := by nlinarith
    have hD : 0 < A * B - C ^ 2 := by
      have hC2 : C ^ 2 < ((1 - ε) ^ 2) ^ 2 := by
        rw [← sq_abs]; exact pow_lt_pow_left₀ hCl (abs_nonneg _) (by norm_num)
      have hAB : ((1 - ε) ^ 2) ^ 2 ≤ A * B := by
        rw [sq]; exact mul_le_mul hA hB (by positivity) ((sq_nonneg _).trans hA)
      linarith
    set D := A * B - C ^ 2
    refine ⟨((s₁ * B - s₂ * C) / D) • w₁ + ((s₂ * A - s₁ * C) / D) • w₂, ?_, ?_⟩
    · simp only [inner_add_right, inner_smul_right]
      rw [real_inner_comm w₁ w₁]
      field_simp
      simp only [D, A, B, C]
      ring
    · simp only [inner_add_right, inner_smul_right]
      rw [real_inner_comm w₁ w₂]
      field_simp
      simp only [D, A, B, C]
      ring

end DifferentialGeometry.Analysis
