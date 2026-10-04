import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! GAF06 (master207B, B:6008) whole-preimage localization along the global segment, and the
numerical steps of GAF07 (B:6049): no extra base points, the first inclusion, and the level bound.

The data are the original block map `F` (FC01: block `(R ζ η, R ζ)`, zero extension), the adjusted
map `E`, the vector/marker projections `u, v` of one retained block, the cutoff `ζ`, the coordinate
`η` and the scale `ρ`. The inputs are GAF02's (AM0) on the segment, CFS26's (AS) and (AE). -/

set_option autoImplicit false
open Set

namespace GC.MetricGeometry

variable {M H V : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem norm_apply_sub_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (A : H →L[ℝ] W) (hA : ‖A‖ ≤ 1) (a b : H) : ‖A a - A b‖ ≤ ‖a - b‖ := by
  rw [← map_sub]
  exact (A.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hA)

theorem norm_segment_sub_le (x y : H) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    ‖((1 - τ) • x + τ • y) - x‖ ≤ ‖y - x‖ := by
  have h : ((1 - τ) • x + τ • y) - x = τ • (y - x) := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hτ.2

/-- GAF06: a point of the segment `H_τ = (1-τ)F + τE` with marker above `.9R` and ratio at most
`4ℓ` comes from a source point with positive original cutoff and `|η| < 4.01 ℓ`. -/
theorem norm_coordinate_lt_of_ratio_on_segment
    (F E : M → H) (u : H →L[ℝ] V) (v : H →L[ℝ] ℝ) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (ζ ρ : M → ℝ) (η : M → V) {R ℓ c₃ : ℝ} (hR : 0 < R) (hℓ : 1 ≤ ℓ)
    (hc₃ : c₃ < 1 / 1000)
    (hblock : ∀ p, u (F p) = (R * ζ p) • η p ∧ v (F p) = R * ζ p)
    (hζ : ∀ p, 0 ≤ ζ p)
    (hzero : ∀ p, ∀ τ ∈ Icc (0 : ℝ) 1, ζ p = 0 → |v ((1 - τ) • F p + τ • E p)| ≤ R / 32)
    (hscale : ∀ p, 0 < ζ p → 3 * R / 4 ≤ ρ p ∧ ρ p ≤ 5 * R / 4)
    (herr : ∀ p, ‖E p - F p‖ < c₃ * ρ p) :
    ∀ p, ∀ τ ∈ Icc (0 : ℝ) 1,
      9 / 10 * R < v ((1 - τ) • F p + τ • E p) →
      ‖u ((1 - τ) • F p + τ • E p)‖ ≤ 4 * ℓ * v ((1 - τ) • F p + τ • E p) →
      0 < ζ p ∧ ‖η p‖ < 401 / 100 * ℓ := by
  intro p τ hτ hmark hratio
  set X := (1 - τ) • F p + τ • E p with hX
  have hζpos : 0 < ζ p := by
    rcases (hζ p).lt_or_eq with h | h
    · exact h
    · have h32 := hzero p τ hτ h.symm
      linarith [le_abs_self (v X)]
  obtain ⟨hρ1, hρ2⟩ := hscale p hζpos
  have he : ‖X - F p‖ < R / 800 := by
    have h1 := norm_segment_sub_le (F p) (E p) hτ
    have h2 := herr p
    have hc₃pos : 0 < c₃ := by
      by_contra hneg
      have : c₃ * ρ p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hneg) (by linarith)
      linarith [norm_nonneg (E p - F p)]
    have h3 : c₃ * ρ p ≤ c₃ * (5 * R / 4) := mul_le_mul_of_nonneg_left hρ2 hc₃pos.le
    nlinarith
  obtain ⟨hbu, hbv⟩ := hblock p
  have hvdiff : |v X - R * ζ p| ≤ ‖X - F p‖ := by
    have := norm_apply_sub_le v hv X (F p)
    rwa [hbv, Real.norm_eq_abs] at this
  have hudiff : ‖u X - (R * ζ p) • η p‖ ≤ ‖X - F p‖ := by
    have := norm_apply_sub_le u hu X (F p)
    rwa [hbu] at this
  set e := ‖X - F p‖
  have hA : 719 / 800 * R < R * ζ p := by
    linarith [(abs_le.mp hvdiff).2]
  have hRζ : 0 < R * ζ p := by linarith
  have hnormη : R * ζ p * ‖η p‖ ≤ ‖u X‖ + e := by
    have := norm_sub_norm_le ((R * ζ p) • η p) (u X)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hRζ, norm_sub_rev] at this
    linarith
  have hvX : v X ≤ R * ζ p + e := by linarith [(abs_le.mp hvdiff).2]
  have hℓ0 : 0 ≤ 4 * ℓ := by linarith
  have hkey : R * ζ p * ‖η p‖ ≤ 4 * ℓ * (R * ζ p) + (4 * ℓ + 1) * e := by
    nlinarith [mul_le_mul_of_nonneg_left hvX hℓ0]
  refine ⟨hζpos, ?_⟩
  by_contra hge
  have hge' : 401 / 100 * ℓ ≤ ‖η p‖ := le_of_not_gt hge
  have h1 := mul_le_mul_of_nonneg_left hge' hRζ.le
  have h2 : 0 < ℓ * (R * ζ p - 719 / 800 * R) := mul_pos (by linarith) (by linarith)
  have h3 : 0 < (4 * ℓ + 1) * (R / 800 - e) := mul_pos (by linarith) (by linarith)
  nlinarith

/-- GAF07, no extra base points: an adjusted point with marker above `.9R` has marker below
`(1 + 1/800) R`, and the ratio threshold `4ℓ` puts its vector in the `5.5 ℓ R` ball. -/
theorem marker_lt_and_norm_lt_of_marker_gt
    (F E : M → H) (u : H →L[ℝ] V) (v : H →L[ℝ] ℝ) (hv : ‖v‖ ≤ 1)
    (ζ ρ : M → ℝ) (η : M → V) {R ℓ c₃ : ℝ} (hR : 0 < R) (hℓ : 1 ≤ ℓ)
    (hc₃ : c₃ < 1 / 1000)
    (hblock : ∀ p, u (F p) = (R * ζ p) • η p ∧ v (F p) = R * ζ p)
    (hζ : ∀ p, 0 ≤ ζ p) (hζ1 : ∀ p, ζ p ≤ 1)
    (hzero : ∀ p, ζ p = 0 → |v (E p)| ≤ R / 32)
    (hscale : ∀ p, 0 < ζ p → 3 * R / 4 ≤ ρ p ∧ ρ p ≤ 5 * R / 4)
    (herr : ∀ p, ‖E p - F p‖ < c₃ * ρ p) :
    ∀ p, 9 / 10 * R < v (E p) →
      v (E p) < (1 + 1 / 800) * R ∧
      (‖u (E p)‖ < 4 * ℓ * v (E p) → ‖u (E p)‖ < 11 / 2 * ℓ * R) := by
  intro p hmark
  have hζpos : 0 < ζ p := by
    rcases (hζ p).lt_or_eq with h | h
    · exact h
    · have h32 := hzero p h.symm
      linarith [le_abs_self (v (E p))]
  obtain ⟨hρ1, hρ2⟩ := hscale p hζpos
  have hc₃pos : 0 < c₃ := by
    by_contra hneg
    have : c₃ * ρ p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hneg) (by linarith)
    linarith [norm_nonneg (E p - F p), herr p]
  have he : ‖E p - F p‖ < R / 800 := by
    have h3 : c₃ * ρ p ≤ c₃ * (5 * R / 4) := mul_le_mul_of_nonneg_left hρ2 hc₃pos.le
    nlinarith [herr p]
  have hvdiff : |v (E p) - R * ζ p| ≤ ‖E p - F p‖ := by
    have := norm_apply_sub_le v hv (E p) (F p)
    rwa [(hblock p).2, Real.norm_eq_abs] at this
  have hRζ : R * ζ p ≤ R := by nlinarith [hζ1 p]
  have hvlt : v (E p) < (1 + 1 / 800) * R := by linarith [(abs_le.mp hvdiff).2]
  refine ⟨hvlt, fun hrat => ?_⟩
  have h4 : 4 * ℓ * v (E p) ≤ 4 * ℓ * ((1 + 1 / 800) * R) :=
    mul_le_mul_of_nonneg_left hvlt.le (by linarith)
  nlinarith

/-- GAF07, first inclusion: at a full-marker source point with `|η| ≤ 3.5 ℓ` whose adjusted image
has exact marker `R` (GAF05), the adjusted ratio is below `4ℓ`. -/
theorem norm_lt_four_mul_of_full_marker
    (F E : M → H) (u : H →L[ℝ] V) (hu : ‖u‖ ≤ 1)
    (ζ ρ : M → ℝ) (η : M → V) {R ℓ c₃ : ℝ} (hR : 0 < R) (hℓ : 1 ≤ ℓ)
    (hc₃ : c₃ < 1 / 1000)
    (hblock : ∀ p, u (F p) = (R * ζ p) • η p)
    (hscale : ∀ p, 0 < ζ p → 3 * R / 4 ≤ ρ p ∧ ρ p ≤ 5 * R / 4)
    (herr : ∀ p, ‖E p - F p‖ < c₃ * ρ p) :
    ∀ p, ζ p = 1 → ‖η p‖ ≤ 7 / 2 * ℓ → ‖u (E p)‖ < 4 * ℓ * R := by
  intro p hζ1 hη
  obtain ⟨hρ1, hρ2⟩ := hscale p (by rw [hζ1]; norm_num)
  have hc₃pos : 0 < c₃ := by
    by_contra hneg
    have : c₃ * ρ p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hneg) (by linarith)
    linarith [norm_nonneg (E p - F p), herr p]
  have he : ‖E p - F p‖ < R / 800 := by
    have h3 : c₃ * ρ p ≤ c₃ * (5 * R / 4) := mul_le_mul_of_nonneg_left hρ2 hc₃pos.le
    nlinarith [herr p]
  have hudiff : ‖u (E p) - u (F p)‖ ≤ ‖E p - F p‖ := norm_apply_sub_le u hu (E p) (F p)
  have huF : ‖u (F p)‖ ≤ 7 / 2 * ℓ * R := by
    rw [hblock p, hζ1, mul_one, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    nlinarith
  nlinarith [norm_sub_norm_le (u (E p)) (u (F p))]

/-- GAF07, level bound for the straight-line family `h_τ = (1-τ) η + τ g`. -/
theorem norm_lt_of_level_of_straight_line {a η g : V} {τ ℓ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hℓ : 1 ≤ ℓ) (ha : ‖a‖ < 4 * ℓ) (hg : ‖g - η‖ < 1 / 800)
    (hlevel : (1 - τ) • η + τ • g = a) : ‖η‖ < 401 / 100 * ℓ := by
  have hsplit : η = a - τ • (g - η) := by
    rw [← hlevel, smul_sub, sub_smul, one_smul]
    abel
  have hτg : ‖τ • (g - η)‖ ≤ ‖g - η‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hτ.2
  have := norm_sub_le a (τ • (g - η))
  rw [← hsplit] at this
  linarith

end GC.MetricGeometry
