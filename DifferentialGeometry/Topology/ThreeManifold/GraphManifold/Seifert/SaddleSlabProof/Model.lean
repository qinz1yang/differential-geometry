import DifferentialGeometry.Topology.Morse.Strip.Foundations.ModelField

/-!
# Algebra of the planar saddle

Lane RG03c. On `MorseModel 2` put `saddleQ y = (y₁² - y₀²) / 2` (the index-one normal form
minus its value) and `saddleK y = y₀ y₁`. The descending model field `modelField 1 r` of the
gradient-like strips is `θ (y₀, -y₁)` with `θ = |y|⁻²` off the small ball, so along its integral
curves `saddleK` is constant and `saddleQ` decreases at unit speed. `(y₀² + y₁²)² =
4 (saddleQ² + saddleK²)`, and a point is determined by `saddleQ`, `saddleK` and the sign of one
nonzero coordinate (`eq_of_saddle_zero`, `eq_of_saddle_one`). `footPt ε σ t = (σ √(2ε + t²), t)`
parametrises the branch `σ y₀ > 0` of the level `saddleQ = -ε`.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negIdx posIdx)

namespace GC.Seifert.SaddleSlabProof

def saddleQ (y : MorseModel 2) : ℝ := (y 1 ^ 2 - y 0 ^ 2) / 2

def saddleK (y : MorseModel 2) : ℝ := y 0 * y 1

theorem morseNorm_sq_two (y : MorseModel 2) : morseNorm 2 y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
  have h := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin 2))
  simpa [Fin.sum_univ_two] using h

theorem morseNormalForm_eq_saddleQ {k : ℕ} (hk : k ≤ 2) (hk1 : k = 1) (c : ℝ)
    (y : MorseModel 2) : morseNormalForm hk c y = c + saddleQ y := by
  subst hk1
  simp [morseNormalForm, negIdx, posIdx, saddleQ]
  ring

theorem normSq_sq_eq (y : MorseModel 2) :
    (y 0 ^ 2 + y 1 ^ 2) ^ 2 = 4 * (saddleQ y ^ 2 + saddleK y ^ 2) := by
  unfold saddleQ saddleK
  ring

theorem two_abs_saddleQ_le (y : MorseModel 2) : 2 * |saddleQ y| ≤ y 0 ^ 2 + y 1 ^ 2 := by
  unfold saddleQ
  have h0 := sq_nonneg (y 0)
  have h1 := sq_nonneg (y 1)
  rcases abs_cases ((y 1 ^ 2 - y 0 ^ 2) / 2) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith

theorem two_abs_saddleK_le (y : MorseModel 2) : 2 * |saddleK y| ≤ y 0 ^ 2 + y 1 ^ 2 := by
  unfold saddleK
  rcases abs_cases (y 0 * y 1) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
    nlinarith [sq_nonneg (y 0 - y 1), sq_nonneg (y 0 + y 1)]

theorem normSq_le_two_mul (y : MorseModel 2) :
    y 0 ^ 2 + y 1 ^ 2 ≤ 2 * (|saddleQ y| + |saddleK y|) := by
  have h := normSq_sq_eq y
  have hq := abs_nonneg (saddleQ y)
  have hk := abs_nonneg (saddleK y)
  have hn : 0 ≤ y 0 ^ 2 + y 1 ^ 2 := by positivity
  have hsq : (y 0 ^ 2 + y 1 ^ 2) ^ 2 ≤ (2 * (|saddleQ y| + |saddleK y|)) ^ 2 := by
    rw [h]
    nlinarith [sq_abs (saddleQ y), sq_abs (saddleK y), mul_nonneg hq hk]
  exact (sq_le_sq₀ hn (by positivity)).1 hsq

theorem eq_of_saddle_zero {y z : MorseModel 2} (hq : saddleQ y = saddleQ z)
    (hk : saddleK y = saddleK z) (h : 0 < y 0 * z 0) : y = z := by
  unfold saddleQ at hq
  unfold saddleK at hk
  have hq' : y 1 ^ 2 - y 0 ^ 2 = z 1 ^ 2 - z 0 ^ 2 := by linarith
  have hk2 : y 0 ^ 2 * y 1 ^ 2 = z 0 ^ 2 * z 1 ^ 2 := by
    rw [← mul_pow, ← mul_pow, hk]
  have hprod : (y 0 ^ 2 - z 0 ^ 2) * (y 0 ^ 2 + z 1 ^ 2) = 0 := by
    linear_combination hk2 - y 0 ^ 2 * hq'
  have hy0 : y 0 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact lt_irrefl 0 h
  have hpos : 0 < y 0 ^ 2 + z 1 ^ 2 := by positivity
  have hsq : y 0 ^ 2 = z 0 ^ 2 := by
    have := (mul_eq_zero.mp hprod).resolve_right hpos.ne'
    linarith
  have h0 : y 0 = z 0 := by
    have hsum : 0 < (y 0 + z 0) ^ 2 := by nlinarith [sq_nonneg (y 0), sq_nonneg (z 0)]
    have hd : (y 0 - z 0) * (y 0 + z 0) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hd with hd | hd
    · linarith
    · rw [hd] at hsum
      norm_num at hsum
  have h1 : y 1 = z 1 := by
    rw [← h0] at hk
    exact mul_left_cancel₀ hy0 hk
  ext i
  fin_cases i
  · exact h0
  · exact h1

theorem eq_of_saddle_one {y z : MorseModel 2} (hq : saddleQ y = saddleQ z)
    (hk : saddleK y = saddleK z) (h : 0 < y 1 * z 1) : y = z := by
  unfold saddleQ at hq
  unfold saddleK at hk
  have hq' : y 1 ^ 2 - y 0 ^ 2 = z 1 ^ 2 - z 0 ^ 2 := by linarith
  have hk2 : y 0 ^ 2 * y 1 ^ 2 = z 0 ^ 2 * z 1 ^ 2 := by
    rw [← mul_pow, ← mul_pow, hk]
  have hprod : (y 1 ^ 2 - z 1 ^ 2) * (y 1 ^ 2 + z 0 ^ 2) = 0 := by
    linear_combination hk2 + y 1 ^ 2 * hq'
  have hy1 : y 1 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact lt_irrefl 0 h
  have hpos : 0 < y 1 ^ 2 + z 0 ^ 2 := by positivity
  have hsq : y 1 ^ 2 = z 1 ^ 2 := by
    have := (mul_eq_zero.mp hprod).resolve_right hpos.ne'
    linarith
  have h1 : y 1 = z 1 := by
    have hsum : 0 < (y 1 + z 1) ^ 2 := by nlinarith [sq_nonneg (y 1), sq_nonneg (z 1)]
    have hd : (y 1 - z 1) * (y 1 + z 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hd with hd | hd
    · linarith
    · rw [hd] at hsum
      norm_num at hsum
  have h0 : y 0 = z 0 := by
    rw [← h1, mul_comm (y 0), mul_comm (z 0)] at hk
    exact mul_left_cancel₀ hy1 hk
  ext i
  fin_cases i
  · exact h0
  · exact h1

theorem modelField_one_apply_zero (r : ℝ) (y : MorseModel 2) :
    ModelField.modelField 1 r y 0 = ModelField.theta r y * y 0 := by
  simp [ModelField.modelField, ModelField.modelDesc]

theorem modelField_one_apply_one (r : ℝ) (y : MorseModel 2) :
    ModelField.modelField 1 r y 1 = -(ModelField.theta r y * y 1) := by
  simp [ModelField.modelField, ModelField.modelDesc]

theorem hasDerivAt_saddleK_curve {z : ℝ → MorseModel 2} {r t : ℝ}
    (hz : HasDerivAt z (ModelField.modelField 1 r (z t)) t) :
    HasDerivAt (fun s => saddleK (z s)) 0 t := by
  have h0 := (hasDerivAt_pi.mp hz) 0
  have h1 := (hasDerivAt_pi.mp hz) 1
  rw [modelField_one_apply_zero] at h0
  rw [modelField_one_apply_one] at h1
  have h := h0.mul h1
  convert h using 1
  · funext s
    simp [saddleK]
  · ring

theorem hasDerivAt_saddleQ_curve {z : ℝ → MorseModel 2} {r t : ℝ}
    (hz : HasDerivAt z (ModelField.modelField 1 r (z t)) t) :
    HasDerivAt (fun s => saddleQ (z s))
      (-(ModelField.theta r (z t) * (z t 0 ^ 2 + z t 1 ^ 2))) t := by
  have h0 := (hasDerivAt_pi.mp hz) 0
  have h1 := (hasDerivAt_pi.mp hz) 1
  rw [modelField_one_apply_zero] at h0
  rw [modelField_one_apply_one] at h1
  have h := ((h1.pow 2).sub (h0.pow 2)).div_const 2
  convert h using 1
  · funext s
    simp [saddleQ]
  · push_cast
    ring

theorem theta_mul_normSq {r : ℝ} (hr : 0 < r) {y : MorseModel 2} (hy : r / 2 ≤ morseNorm 2 y) :
    ModelField.theta r y * (y 0 ^ 2 + y 1 ^ 2) = 1 := by
  rw [← morseNorm_sq_two]
  exact ModelField.theta_mul_sq hr hy

def footPt (ε σ t : ℝ) : MorseModel 2 := ![σ * Real.sqrt (2 * ε + t ^ 2), t]

theorem saddleQ_footPt {ε σ : ℝ} (hε : 0 ≤ ε) (hσ : σ ^ 2 = 1) (t : ℝ) :
    saddleQ (footPt ε σ t) = -ε := by
  have h := Real.sq_sqrt (show 0 ≤ 2 * ε + t ^ 2 by positivity)
  simp only [saddleQ, footPt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [mul_pow, h, hσ]
  ring

theorem saddleK_footPt (ε σ t : ℝ) :
    saddleK (footPt ε σ t) = σ * t * Real.sqrt (2 * ε + t ^ 2) := by
  simp only [saddleK, footPt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

theorem footPt_zero (ε σ t : ℝ) : footPt ε σ t 0 = σ * Real.sqrt (2 * ε + t ^ 2) := rfl

theorem footPt_one (ε σ t : ℝ) : footPt ε σ t 1 = t := rfl

end GC.Seifert.SaddleSlabProof
