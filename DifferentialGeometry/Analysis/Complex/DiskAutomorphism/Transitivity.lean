import DifferentialGeometry.Analysis.Complex.DiskAutomorphism.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section

open scoped ComplexConjugate

namespace Complex

private theorem norm_cayley_disk_parameter_lt_one {p α β : ℂ}
    (hp : ‖p‖ = 1) (hβα : ‖β‖ < ‖α‖) :
    ‖-p * conj β / conj α‖ < 1 := by
  have hα : 0 < ‖α‖ := lt_of_le_of_lt (norm_nonneg β) hβα
  simpa only [norm_div, norm_mul, norm_neg, norm_conj, hp, one_mul] using
    (div_lt_one hα).mpr hβα

private theorem norm_cayley_disk_rotation {p q α : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hα : α ≠ 0) :
    ‖q * conj α / (p * α)‖ = 1 := by
  simp only [norm_div, norm_mul, norm_conj, hq, hp, one_mul]
  exact div_self (norm_ne_zero_iff.mpr hα)

theorem diskMoebius_eq_of_cayley_coefficients {p q α β z : ℂ}
    (hp : ‖p‖ = 1) (hα : α ≠ 0) :
    (q * conj α / (p * α)) * diskMoebius (-p * conj β / conj α) z =
      q * (conj α * z + conj β * p) / (α * p + β * z) := by
  have hp₀ : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hp]; exact one_ne_zero)
  have hαc : conj α ≠ 0 := norm_ne_zero_iff.mp (by
    rw [norm_conj]
    exact norm_ne_zero_iff.mpr hα)
  have hpconj : conj p = p⁻¹ := by
    rw [Complex.inv_def, normSq_eq_norm_sq, hp]
    simp
  have hd : 1 - conj (-p * conj β / conj α) * z =
      (α * p + β * z) / (α * p) := by
    simp only [map_div₀, map_mul, map_neg, conj_conj, hpconj]
    field_simp [hp₀, hα]
    ring
  rw [diskMoebius, hd]
  field_simp [hp₀, hα, hαc]
  ring

theorem diskMoebius_cayley_affine_parameters (p q : ℂ) (l m : ℝ)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hl : 0 < l) :
    let α : ℂ := (l + 1 : ℝ) - I * (m : ℂ)
    let β : ℂ := (l - 1 : ℝ) + I * (m : ℂ)
    let a : ℂ := -p * conj β / conj α
    let η : ℂ := q * conj α / (p * α)
    ‖a‖ < 1 ∧ ‖η‖ = 1 ∧
      (∀ z : ℂ,
        η * diskMoebius a z = q * (conj α * z + conj β * p) / (α * p + β * z)) ∧
      η * diskMoebius a p = q := by
  let α : ℂ := (l + 1 : ℝ) - I * (m : ℂ)
  let β : ℂ := (l - 1 : ℝ) + I * (m : ℂ)
  let a : ℂ := -p * conj β / conj α
  let η : ℂ := q * conj α / (p * α)
  change ‖a‖ < 1 ∧ ‖η‖ = 1 ∧
    (∀ z : ℂ,
      η * diskMoebius a z = q * (conj α * z + conj β * p) / (α * p + β * z)) ∧
    η * diskMoebius a p = q
  have hdiff : normSq α - normSq β = 4 * l := by
    dsimp only [α, β]
    simp only [normSq_apply, sub_re, sub_im, add_re, add_im, mul_re, mul_im,
      ofReal_re, ofReal_im, I_re, I_im]
    ring
  have hβα : ‖β‖ < ‖α‖ := by
    rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at hdiff
    nlinarith [norm_nonneg α, norm_nonneg β]
  have hα : α ≠ 0 := norm_ne_zero_iff.mp
    (ne_of_gt (lt_of_le_of_lt (norm_nonneg β) hβα))
  have hp₀ : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hp]; exact one_ne_zero)
  have hab : α + β = ((2 * l : ℝ) : ℂ) := by
    dsimp only [α, β]
    simp only [ofReal_add, ofReal_sub, ofReal_mul, ofReal_one, ofReal_ofNat]
    ring
  have hden : α * p + β * p ≠ 0 := by
    rw [← add_mul, hab]
    exact mul_ne_zero (ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) hl.ne')) hp₀
  refine ⟨norm_cayley_disk_parameter_lt_one hp hβα,
    norm_cayley_disk_rotation hp hq hα, ?_, ?_⟩
  · intro z
    exact diskMoebius_eq_of_cayley_coefficients hp hα
  · have hc : conj α + conj β = α + β := by
      calc
        conj α + conj β = conj (α + β) := (map_add _ _ _).symm
        _ = ((2 * l : ℝ) : ℂ) := by simp only [hab, conj_ofReal]
        _ = α + β := hab.symm
    calc
      η * diskMoebius a p =
          q * (conj α * p + conj β * p) / (α * p + β * p) :=
        diskMoebius_eq_of_cayley_coefficients hp hα
      _ = q := by
        simp only [← add_mul, hc]
        exact mul_div_cancel_right₀ q (by simpa only [add_mul] using hden)

end Complex

end

noncomputable section

namespace Real

theorem strictMonoOn_neg_cos_div_sin :
    StrictMonoOn (fun u : ℝ => -cos u / sin u) (Set.Ioo 0 Real.pi) := by
  intro u hu v hv huv
  have hsu : 0 < sin u := sin_pos_of_pos_of_lt_pi hu.1 hu.2
  have hsv : 0 < sin v := sin_pos_of_pos_of_lt_pi hv.1 hv.2
  have hsin : 0 < sin (v - u) :=
    sin_pos_of_pos_of_lt_pi (sub_pos.mpr huv) (by linarith [hu.1, hv.2])
  rw [sin_sub] at hsin
  apply (div_lt_div_iff₀ hsu hsv).mpr
  nlinarith

theorem strictMonoOn_neg_cot_pi :
    StrictMonoOn (fun t : ℝ => -cos (Real.pi * t) / sin (Real.pi * t)) (Set.Ioo 0 1) := by
  intro s hs t ht hst
  apply strictMonoOn_neg_cos_div_sin
  · exact ⟨mul_pos pi_pos hs.1, by nlinarith [pi_pos, hs.2]⟩
  · exact ⟨mul_pos pi_pos ht.1, by nlinarith [pi_pos, ht.2]⟩
  · exact mul_lt_mul_of_pos_left hst pi_pos

end Real

namespace Complex

theorem exp_two_mul_I_eq_neg_cot_fraction {u : ℝ} (hu : Real.sin u ≠ 0) :
    exp (((2 * u : ℝ) : ℂ) * I) =
      (((-Real.cos u / Real.sin u : ℝ) : ℂ) - I) /
        (((-Real.cos u / Real.sin u : ℝ) : ℂ) + I) := by
  let x : ℝ := -Real.cos u / Real.sin u
  have hs : (Real.sin u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu
  have hminus : (x : ℂ) - I = -exp ((u : ℂ) * I) / (Real.sin u : ℂ) := by
    rw [exp_ofReal_mul_I]
    dsimp only [x]
    simp only [ofReal_div, ofReal_neg]
    field_simp [hs]
    ring
  have hplus : (x : ℂ) + I =
      -exp (((-u : ℝ) : ℂ) * I) / (Real.sin u : ℂ) := by
    rw [exp_ofReal_mul_I]
    dsimp only [x]
    simp only [Real.cos_neg, Real.sin_neg, ofReal_div, ofReal_neg]
    field_simp [hs]
    ring
  change exp (((2 * u : ℝ) : ℂ) * I) = ((x : ℂ) - I) / ((x : ℂ) + I)
  rw [hminus, hplus, div_div_div_cancel_right₀ hs, neg_div_neg_eq, ← exp_sub]
  congr 1
  simp only [ofReal_mul, ofReal_ofNat, ofReal_neg]
  ring

theorem exp_two_pi_mul_I_eq_neg_cot_fraction {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    exp (((2 * Real.pi * t : ℝ) : ℂ) * I) =
      (((-Real.cos (Real.pi * t) / Real.sin (Real.pi * t) : ℝ) : ℂ) - I) /
        (((-Real.cos (Real.pi * t) / Real.sin (Real.pi * t) : ℝ) : ℂ) + I) := by
  have hs : Real.sin (Real.pi * t) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht.1)
      (by nlinarith [Real.pi_pos, ht.2])).ne'
  simpa only [mul_assoc] using exp_two_mul_I_eq_neg_cot_fraction hs

end Complex

end

noncomputable section

open Set
open scoped ComplexConjugate

namespace Complex

private theorem cayley_fraction_apply (p q : ℂ) (l m x : ℝ)
    (hp : ‖p‖ = 1) (hl : 0 < l) :
    let α : ℂ := (l + 1 : ℝ) - I * (m : ℂ)
    let β : ℂ := (l - 1 : ℝ) + I * (m : ℂ)
    (q * conj α / (p * α)) *
      diskMoebius (-p * conj β / conj α) (p * ((x : ℂ) - I) / ((x : ℂ) + I)) =
      q * (((l * x + m : ℝ) : ℂ) - I) / (((l * x + m : ℝ) : ℂ) + I) := by
  let α : ℂ := (l + 1 : ℝ) - I * (m : ℂ)
  let β : ℂ := (l - 1 : ℝ) + I * (m : ℂ)
  have ha : α ≠ 0 := by
    intro h
    have hh := congrArg re h
    simp [α] at hh
    linarith
  have hx : (x : ℂ) + I ≠ 0 := by
    intro h
    have hh := congrArg im h
    norm_num at hh
  have hp0 : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hp]; exact one_ne_zero)
  change (q * conj α / (p * α)) *
      diskMoebius (-p * conj β / conj α) (p * ((x : ℂ) - I) / ((x : ℂ) + I)) = _
  rw [diskMoebius_eq_of_cayley_coefficients hp ha]
  have hn : conj α * (p * ((x : ℂ) - I) / ((x : ℂ) + I)) + conj β * p =
      2 * p * (((l * x + m : ℝ) : ℂ) - I) / ((x : ℂ) + I) := by
    dsimp [α, β]
    push_cast
    simp only [map_sub, map_add, map_mul, conj_ofReal, conj_I, map_one]
    field_simp [hx]
    ring_nf
    simp [I_sq]
  have hd : α * p + β * (p * ((x : ℂ) - I) / ((x : ℂ) + I)) =
      2 * p * (((l * x + m : ℝ) : ℂ) + I) / ((x : ℂ) + I) := by
    dsimp [α, β]
    push_cast
    field_simp [hx]
    ring_nf
    simp [I_sq]
  rw [hn, hd, ← mul_div_assoc, div_div_div_cancel_right₀ hx]
  rw [show q * (2 * p * (((l * x + m : ℝ) : ℂ) - I)) =
    (2 * p) * (q * (((l * x + m : ℝ) : ℂ) - I)) by ring]
  exact mul_div_mul_left _ _ (mul_ne_zero (by norm_num) hp0)

theorem exists_diskMoebius_cayley_triple
    (p q : ℂ) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (x₁ x₂ y₁ y₂ : ℝ) (hx : x₁ < x₂) (hy : y₁ < y₂) :
    ∃ a η : ℂ, ‖a‖ < 1 ∧ ‖η‖ = 1 ∧ η * diskMoebius a p = q ∧
      η * diskMoebius a (p * ((x₁ : ℂ) - I) / ((x₁ : ℂ) + I)) =
        q * ((y₁ : ℂ) - I) / ((y₁ : ℂ) + I) ∧
      η * diskMoebius a (p * ((x₂ : ℂ) - I) / ((x₂ : ℂ) + I)) =
        q * ((y₂ : ℂ) - I) / ((y₂ : ℂ) + I) := by
  let l : ℝ := (y₂ - y₁) / (x₂ - x₁)
  let m : ℝ := y₁ - l * x₁
  have hl : 0 < l := div_pos (sub_pos.mpr hy) (sub_pos.mpr hx)
  have h1 : l * x₁ + m = y₁ := by dsimp [m]; ring
  have h2 : l * x₂ + m = y₂ := by
    dsimp [m, l]
    field_simp [ne_of_gt (sub_pos.mpr hx)]
    ring
  let α : ℂ := (l + 1 : ℝ) - I * (m : ℂ)
  let β : ℂ := (l - 1 : ℝ) + I * (m : ℂ)
  let a : ℂ := -p * conj β / conj α
  let η : ℂ := q * conj α / (p * α)
  obtain ⟨ha, hη, _, h0⟩ := diskMoebius_cayley_affine_parameters p q l m hp hq hl
  refine ⟨a, η, ha, hη, h0, ?_, ?_⟩
  · simpa only [h1] using cayley_fraction_apply p q l m x₁ hp hl
  · simpa only [h2] using cayley_fraction_apply p q l m x₂ hp hl

end Complex

end

noncomputable section

open Set
open scoped ComplexConjugate

namespace Complex

private theorem exp_eq_cayley_fraction_of_lt {s t : ℝ} (hst : s < t) (ht : t < s + 1) :
    exp ((2 * Real.pi * t : ℝ) * I) =
      exp ((2 * Real.pi * s : ℝ) * I) *
        (((-Real.cos (Real.pi * (t - s)) / Real.sin (Real.pi * (t - s)) : ℝ) : ℂ) - I) /
        (((-Real.cos (Real.pi * (t - s)) / Real.sin (Real.pi * (t - s)) : ℝ) : ℂ) + I) := by
  have h : exp ((2 * Real.pi * t : ℝ) * I) =
      exp ((2 * Real.pi * s : ℝ) * I) * exp ((2 * Real.pi * (t - s) : ℝ) * I) := by
    rw [← exp_add]
    congr 1
    push_cast
    ring
  rw [h, exp_two_pi_mul_I_eq_neg_cot_fraction ⟨sub_pos.mpr hst, by linarith⟩,
    mul_div_assoc]

theorem exists_diskMoebius_map_cyclic_triples
    (s₀ s₁ s₂ t₀ t₁ t₂ : ℝ)
    (hs₁ : s₀ < s₁) (hs₂ : s₁ < s₂) (hs₃ : s₂ < s₀ + 1)
    (ht₁ : t₀ < t₁) (ht₂ : t₁ < t₂) (ht₃ : t₂ < t₀ + 1) :
    ∃ a η : ℂ, ‖a‖ < 1 ∧ ‖η‖ = 1 ∧
      η * diskMoebius a (exp ((2 * Real.pi * s₀ : ℝ) * I)) =
        exp ((2 * Real.pi * t₀ : ℝ) * I) ∧
      η * diskMoebius a (exp ((2 * Real.pi * s₁ : ℝ) * I)) =
        exp ((2 * Real.pi * t₁ : ℝ) * I) ∧
      η * diskMoebius a (exp ((2 * Real.pi * s₂ : ℝ) * I)) =
        exp ((2 * Real.pi * t₂ : ℝ) * I) := by
  let x (t : ℝ) := -Real.cos (Real.pi * t) / Real.sin (Real.pi * t)
  have hsx : x (s₁ - s₀) < x (s₂ - s₀) :=
    Real.strictMonoOn_neg_cot_pi ⟨sub_pos.mpr hs₁, by linarith⟩
      ⟨by linarith, by linarith⟩ (by linarith)
  have hty : x (t₁ - t₀) < x (t₂ - t₀) :=
    Real.strictMonoOn_neg_cot_pi ⟨sub_pos.mpr ht₁, by linarith⟩
      ⟨by linarith, by linarith⟩ (by linarith)
  obtain ⟨a, η, ha, hη, h0, h1, h2⟩ := exists_diskMoebius_cayley_triple
    (exp ((2 * Real.pi * s₀ : ℝ) * I)) (exp ((2 * Real.pi * t₀ : ℝ) * I))
    (norm_exp_ofReal_mul_I _) (norm_exp_ofReal_mul_I _)
    (x (s₁ - s₀)) (x (s₂ - s₀)) (x (t₁ - t₀)) (x (t₂ - t₀)) hsx hty
  refine ⟨a, η, ha, hη, h0, ?_, ?_⟩
  · rw [exp_eq_cayley_fraction_of_lt hs₁ (hs₂.trans hs₃),
      exp_eq_cayley_fraction_of_lt ht₁ (ht₂.trans ht₃)]
    exact h1
  · rw [exp_eq_cayley_fraction_of_lt (hs₁.trans hs₂) hs₃,
      exp_eq_cayley_fraction_of_lt (ht₁.trans ht₂) ht₃]
    exact h2

end Complex

end
