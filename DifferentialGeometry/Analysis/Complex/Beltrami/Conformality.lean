import DifferentialGeometry.Analysis.Complex.Beltrami.Coefficient
import Mathlib.Tactic.LinearCombination
import DifferentialGeometry.Analysis.Complex.Beltrami.LinearParts

section

noncomputable section
open scoped ComplexConjugate

namespace DifferentialGeometry.Analysis

theorem normSq_add_beltrami_mul_conj
    {a b c : ℝ} (ha : 0 < a) (hdet : 0 < a * b - c ^ 2) (z : ℂ) :
    (a + b + 2 * Real.sqrt (a * b - c ^ 2)) / 4 *
        Complex.normSq (z + beltramiCoefficient a b c * conj z) =
      a * z.re ^ 2 + 2 * c * z.re * z.im + b * z.im ^ 2 := by
  have hb : 0 < b := by nlinarith [sq_nonneg c]
  let d := Real.sqrt (a * b - c ^ 2)
  have hd : 0 < d := Real.sqrt_pos.mpr hdet
  have hd2 : d ^ 2 = a * b - c ^ 2 := Real.sq_sqrt hdet.le
  have hs : a + b + 2 * d ≠ 0 := (by positivity : 0 < a + b + 2 * d).ne'
  change (a + b + 2 * d) / 4 *
    Complex.normSq (z + (((a - b : ℝ) + (2 * c : ℝ) * Complex.I) /
      (a + b + 2 * d : ℝ)) * conj z) = _
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  field_simp
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Analysis

theorem beltrami_eq_iff_metric_columns
    {a b c : ℝ} (ha : 0 < a) (hdet : 0 < a * b - c ^ 2) (u v : ℂ) :
    u + Complex.I * v = beltramiCoefficient a b c * (u - Complex.I * v) ↔
      v = ((c : ℂ) + Real.sqrt (a * b - c ^ 2) * Complex.I) / a * u := by
  have hb : 0 < b := by nlinarith [sq_nonneg c]
  let d := Real.sqrt (a * b - c ^ 2)
  let μ := beltramiCoefficient a b c
  let η : ℂ := ((c : ℂ) + d * Complex.I) / a
  have hd : 0 < d := Real.sqrt_pos.mpr hdet
  have hd2 : d ^ 2 = a * b - c ^ 2 := Real.sq_sqrt hdet.le
  have hs : a + b + 2 * d ≠ 0 := (by positivity : 0 < a + b + 2 * d).ne'
  have hμ : (1 - μ) + Complex.I * (1 + μ) * η = 0 := by
    apply Complex.ext <;>
      simp only [μ, beltramiCoefficient, η, d, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
        Complex.zero_re, Complex.zero_im]
    all_goals
      dsimp only [d] at hs hd2
      field_simp
      nlinarith
  have hne : 1 + μ ≠ 0 := by
    intro hh
    have heq : μ = -1 := eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hh)
    have hn := norm_beltramiCoefficient_lt_one ha hdet
    change ‖μ‖ < 1 at hn
    rw [heq, norm_neg, norm_one] at hn
    exact (lt_irrefl _ hn)
  have hid : u + Complex.I * v - μ * (u - Complex.I * v) =
      (Complex.I * (1 + μ)) * (v - η * u) := by
    linear_combination u * hμ
  change u + Complex.I * v = μ * (u - Complex.I * v) ↔ v = η * u
  rw [← sub_eq_zero, hid, mul_eq_zero,
    or_iff_right (mul_ne_zero Complex.I_ne_zero hne), sub_eq_zero]

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open scoped ComplexConjugate

namespace DifferentialGeometry.Analysis

theorem metric_columns_iff_oriented_conformal_gram
    {a b c : ℝ} (ha : 0 < a) (hdet : 0 < a * b - c ^ 2) (u v : ℂ) :
    v = ((c : ℂ) + Real.sqrt (a * b - c ^ 2) * Complex.I) / a * u ↔
      ∃ lam : ℝ, 0 ≤ lam ∧ Complex.normSq u = lam * a ∧ Complex.normSq v = lam * b ∧
        (conj u * v).re = lam * c ∧ 0 ≤ (conj u * v).im := by
  let d := Real.sqrt (a * b - c ^ 2)
  have hd : 0 < d := Real.sqrt_pos.mpr hdet
  have hd2 : d ^ 2 = a * b - c ^ 2 := Real.sq_sqrt hdet.le
  have ha0 : a ≠ 0 := ha.ne'
  have hn : Complex.normSq (((c : ℂ) + d * Complex.I) / a) = b / a := by
    rw [Complex.normSq_div, Complex.normSq_add_mul_I, Complex.normSq_ofReal]
    field_simp
    nlinarith
  constructor
  · intro hv
    refine ⟨Complex.normSq u / a, div_nonneg (Complex.normSq_nonneg u) ha.le, ?_, ?_, ?_, ?_⟩
    · field_simp
    · rw [hv, Complex.normSq_mul, hn]
      ring
    · rw [hv]
      have heq : conj u * (((c : ℂ) + d * Complex.I) / a * u) =
          ((Complex.normSq u : ℝ) : ℂ) * (((c : ℂ) + d * Complex.I) / a) := by
        rw [Complex.normSq_eq_conj_mul_self]
        ring
      rw [heq]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofReal_re,
        Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero]
      ring
    · rw [hv]
      have heq : conj u * (((c : ℂ) + d * Complex.I) / a * u) =
          ((Complex.normSq u : ℝ) : ℂ) * (((c : ℂ) + d * Complex.I) / a) := by
        rw [Complex.normSq_eq_conj_mul_self]
        ring
      rw [heq]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofReal_im,
        Complex.add_im, Complex.I_im, mul_one, zero_mul, add_zero, zero_add]
      exact mul_nonneg (Complex.normSq_nonneg u) (div_nonneg hd.le ha.le)
  · rintro ⟨lam, hlam, hu, hv, hreal, him⟩
    have hsq : (conj u * v).im ^ 2 = (lam * d) ^ 2 := by
      have hnorm := Complex.normSq_mul (conj u) v
      rw [Complex.normSq_conj, hu, hv, Complex.normSq_apply, hreal] at hnorm
      nlinarith
    have himag : (conj u * v).im = lam * d := (sq_eq_sq₀ him (mul_nonneg hlam hd.le)).mp hsq
    have hpair : conj u * v = (lam : ℂ) * ((c : ℂ) + d * Complex.I) := by
      apply Complex.ext
      · simpa using hreal
      · simpa using himag
    by_cases hu0 : u = 0
    · subst u
      have hlam0 : lam = 0 := (mul_eq_zero.mp (by simpa using hu.symm)).resolve_right ha0
      have hv0 : v = 0 := Complex.normSq_eq_zero.mp (by rw [hv, hlam0, zero_mul])
      rw [hv0, mul_zero]
    · apply mul_left_cancel₀ ((map_ne_zero (starRingEnd ℂ)).mpr hu0)
      rw [hpair]
      have hn : conj u * u = (lam : ℂ) * a := by
        rw [← Complex.normSq_eq_conj_mul_self, hu, Complex.ofReal_mul]
      change (lam : ℂ) * ((c : ℂ) + d * Complex.I) =
        conj u * (((c : ℂ) + d * Complex.I) / a * u)
      calc
        _ = ((c : ℂ) + d * Complex.I) / a * ((lam : ℂ) * a) := by
          field_simp [Complex.ofReal_ne_zero.mpr ha0]
        _ = ((c : ℂ) + d * Complex.I) / a * (conj u * u) := by rw [hn]
        _ = _ := by ring

theorem beltrami_eq_iff_oriented_conformal_gram
    {a b c : ℝ} (ha : 0 < a) (hdet : 0 < a * b - c ^ 2)
    (L : ℂ →L[ℝ] ℂ) :
    complexAntilinearPart L = beltramiCoefficient a b c * complexLinearPart L ↔
      ∃ lam : ℝ, 0 ≤ lam ∧ Complex.normSq (L 1) = lam * a ∧
        Complex.normSq (L Complex.I) = lam * b ∧ (conj (L 1) * L Complex.I).re = lam * c ∧
          0 ≤ (conj (L 1) * L Complex.I).im := by
  have heq : complexAntilinearPart L = beltramiCoefficient a b c * complexLinearPart L ↔
      L 1 + Complex.I * L Complex.I =
        beltramiCoefficient a b c * (L 1 - Complex.I * L Complex.I) := by
    rw [complexAntilinearPart, complexLinearPart, ← mul_div_assoc]
    exact div_left_inj' (by norm_num : (2 : ℂ) ≠ 0)
  rw [heq, beltrami_eq_iff_metric_columns ha hdet]
  exact metric_columns_iff_oriented_conformal_gram ha hdet (L 1) (L Complex.I)

theorem beltrami_eq_iff_positive_conformal_gram
    {a b c : ℝ} (ha : 0 < a) (hdet : 0 < a * b - c ^ 2)
    (L : ℂ →L[ℝ] ℂ) (hL : L ≠ 0) :
    complexAntilinearPart L = beltramiCoefficient a b c * complexLinearPart L ↔
      ∃ lam : ℝ, 0 < lam ∧ Complex.normSq (L 1) = lam * a ∧
        Complex.normSq (L Complex.I) = lam * b ∧ (conj (L 1) * L Complex.I).re = lam * c ∧
          0 < (conj (L 1) * L Complex.I).im := by
  constructor
  · intro h
    obtain ⟨lam, hlam, h1, hI, hc, hi⟩ :=
      (beltrami_eq_iff_oriented_conformal_gram ha hdet L).mp h
    have hlam0 : lam ≠ 0 := by
      intro hz
      have hL1 : L 1 = 0 := Complex.normSq_eq_zero.mp (by rw [h1, hz, zero_mul])
      have hLI : L Complex.I = 0 := Complex.normSq_eq_zero.mp (by rw [hI, hz, zero_mul])
      apply hL
      ext z
      have he := apply_eq_complexLinearPart_mul_add_complexAntilinearPart_mul_conj L z
      simpa only [complexLinearPart, complexAntilinearPart, hL1, hLI, mul_zero,
        add_zero, sub_zero, zero_div, zero_add, zero_mul, zero_apply] using he
    have hp : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hlam0)
    have hnorm := Complex.normSq_mul (conj (L 1)) (L Complex.I)
    rw [Complex.normSq_conj, h1, hI, Complex.normSq_apply, hc] at hnorm
    have hj : 0 < (conj (L 1) * L Complex.I).im := by
      have hpos : 0 < lam ^ 2 * (a * b - c ^ 2) := mul_pos (sq_pos_of_pos hp) hdet
      nlinarith
    exact ⟨lam, hp, h1, hI, hc, hj⟩
  · rintro ⟨lam, hlam, h1, hI, hc, hi⟩
    exact (beltrami_eq_iff_oriented_conformal_gram ha hdet L).mpr
      ⟨lam, hlam.le, h1, hI, hc, hi.le⟩

end DifferentialGeometry.Analysis

end

end
