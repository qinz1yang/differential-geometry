import DifferentialGeometry.Analysis.Convex.HyperbolicSine
import DifferentialGeometry.Geometry.Comparison.ModelAngle

set_option autoImplicit false

open Set Real

namespace Real

private theorem cosh_sub_one_half (x : ℝ) : cosh x - 1 = 2 * sinh (x / 2) ^ 2 := by
  have h := cosh_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  nlinarith [cosh_sq_sub_sinh_sq (x / 2)]

private theorem hyperbolic_side_half_identity (r s C : ℝ) :
    cosh r * cosh s - sinh r * sinh s * C - 1 =
      2 * sinh ((r - s) / 2) ^ 2 + sinh r * sinh s * (1 - C) := by
  have h := cosh_sub_one_half (r - s)
  rw [cosh_sub] at h
  nlinarith

private theorem radial_side_lower_of_cosine_laws_ordered {r s c d D t C : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hsr : s ≤ r) (hrD : r ≤ D)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hD : 0 < D) (ht : t ∈ Icc 0 1) (hC : C ≤ 1)
    (hcLaw : cosh c = cosh r * cosh s - sinh r * sinh s * C)
    (hdLaw : cosh (t * r) * cosh (t * s) - sinh (t * r) * sinh (t * s) * C ≤ cosh d) :
    (t * D / sinh D) * c ≤ d := by
  let Λ := t * D / sinh D
  have hsD : 0 < sinh D := sinh_pos_iff.mpr hD
  have hΛ : 0 ≤ Λ := div_nonneg (mul_nonneg ht.1 hD.le) hsD.le
  have hΛ1 : Λ ≤ 1 := by
    apply (div_le_one hsD).mpr
    exact (mul_le_of_le_one_left hD.le ht.2).trans (self_le_sinh_iff.mpr hD.le)
  have hdiff : 0 ≤ (r - s) / 2 := by linarith
  have hdiffD : (r - s) / 2 ≤ D := by linarith
  have hdr := mul_sinh_le_sinh_mul_of_le ht.1 hr hD hrD
  have hds := mul_sinh_le_sinh_mul_of_le ht.1 hs hD (hsr.trans hrD)
  have hdd := mul_sinh_le_sinh_mul_of_le ht.1 hdiff hD hdiffD
  have hsinhR : 0 ≤ sinh (t * r) := sinh_nonneg_iff.mpr (mul_nonneg ht.1 hr)
  have hsinhS : 0 ≤ sinh (t * s) := sinh_nonneg_iff.mpr (mul_nonneg ht.1 hs)
  have hsinhDiff : 0 ≤ sinh (t * ((r - s) / 2)) := sinh_nonneg_iff.mpr (mul_nonneg ht.1 hdiff)
  have hprod := mul_le_mul hdr hds (mul_nonneg hΛ (sinh_nonneg_iff.mpr hs)) hsinhR
  have hprodC := mul_le_mul_of_nonneg_right hprod (sub_nonneg.mpr hC)
  have hdiffSq := pow_le_pow_left₀ (mul_nonneg hΛ (sinh_nonneg_iff.mpr hdiff)) hdd 2
  have hbase := hyperbolic_side_half_identity r s C
  rw [← hcLaw] at hbase
  have hsmall := hyperbolic_side_half_identity (t * r) (t * s) C
  rw [show (t * r - t * s) / 2 = t * ((r - s) / 2) by ring] at hsmall
  have hcosh : Λ ^ 2 * (cosh c - 1) ≤ cosh d - 1 := by
    have hid : Λ ^ 2 * (cosh c - 1) =
        2 * (Λ * sinh ((r - s) / 2)) ^ 2 +
          ((Λ * sinh r) * (Λ * sinh s)) * (1 - C) := by rw [hbase]; ring
    rw [hid]
    nlinarith
  have hhalf := sinh_mul_le_mul_sinh ⟨hΛ, hΛ1⟩ (show 0 ≤ c / 2 by positivity)
  have hsquare := pow_le_pow_left₀
    (sinh_nonneg_iff.mpr (mul_nonneg hΛ (show 0 ≤ c / 2 by positivity))) hhalf 2
  have hscaled : cosh (Λ * c) ≤ cosh d := by
    have h1 := cosh_sub_one_half (Λ * c)
    have h2 := cosh_sub_one_half c
    rw [show Λ * c / 2 = Λ * (c / 2) by ring] at h1
    nlinarith
  simpa only [abs_of_nonneg (mul_nonneg hΛ hc), abs_of_nonneg hd] using cosh_le_cosh.mp hscaled

theorem radial_side_lower_of_cosine_laws {r s c d D t C : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrD : r ≤ D) (hsD : s ≤ D)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hD : 0 < D) (ht : t ∈ Icc 0 1) (hC : C ≤ 1)
    (hcLaw : cosh c = cosh r * cosh s - sinh r * sinh s * C)
    (hdLaw : cosh (t * r) * cosh (t * s) - sinh (t * r) * sinh (t * s) * C ≤ cosh d) :
    (t * D / sinh D) * c ≤ d := by
  rcases le_total s r with hsr | hrs
  · exact radial_side_lower_of_cosine_laws_ordered hr hs hsr hrD hc hd hD ht hC hcLaw hdLaw
  · apply radial_side_lower_of_cosine_laws_ordered hs hr hrs hsD hc hd hD ht hC
    · simpa only [mul_comm (cosh s) (cosh r), mul_comm (sinh s) (sinh r)] using hcLaw
    · simpa only [mul_comm (cosh (t * s)) (cosh (t * r)),
        mul_comm (sinh (t * s)) (sinh (t * r))] using hdLaw

end Real
