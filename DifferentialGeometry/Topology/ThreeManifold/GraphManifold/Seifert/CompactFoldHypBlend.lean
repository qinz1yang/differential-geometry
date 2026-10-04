import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypValid

/-!
# Canonical sums and the outer blend of the hyperbolic fold

Lane CF-H, tier 3 (design
`docs/geometrization/handoffs/20261004-design-cf-compact-triangle-fold.md`, §4, the blend weight
`ν` "with no layout input", curvature `-1`). The canonical coordinates take the values
`∓τⱼ` at the vertices (`canon_one_zero`, `canon_two_zero`, …, from `canonForm a (a ⊕ b) = b`,
`canonForm_oplus`), and the sum over the two vertices of a wall is nonnegative on the whole
triangle (`canon_one_add_two_nonneg`, `canon_zero_add_two_nonneg`, `canon_zero_add_one_nonneg`:
the bracket factorisation off the vertices, the explicit values at them). The angle about
`v₃ = 0` lies in `[0, θ₃]` on the triangle (`discAngle_mem`, from `discAngle_mem_sector`).

Consequently the argument `blendThree` of the outer weight `ν` is at least `w` on the corner
region `{canon 0 ≤ -e}` and at most `-w` on `{canon 1 ≤ -e}` as soon as `δ ≤ e`
(`blendThree_ge_of_cornerOne`, `blendThree_le_of_cornerTwo`): on the boundaries of the two inner
corner regions the outer corner is exactly the bridge `bridgeOne` resp. `bridgeZero`, by the
triangle inequality alone.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace HypFold

theorem canonForm_oplus {a b : ℝ} (ha1 : a < 1) (ha0 : -1 < a) (hab : 0 < 1 + a * b) :
    canonForm a (oplus a b) = b := by
  have h1 : 1 - a ^ 2 ≠ 0 := by nlinarith
  rw [canonForm, oplus]
  have e1 : (a + b) / (1 + a * b) - a = b * (1 - a ^ 2) / (1 + a * b) := by
    field_simp
    ring
  have e2 : 1 - (a + b) / (1 + a * b) * a = (1 - a ^ 2) / (1 + a * b) := by
    field_simp
    ring
  rw [e1, e2, div_div_div_cancel_right₀ hab.ne', mul_div_assoc, div_self h1, mul_one]

theorem discAngle_mem_sector {θ : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ Real.pi / 2) {w : ℂ} (hw : w ≠ 0)
    (h1 : 0 ≤ w.im) (h2 : (exp (-((θ : ℂ) * I)) * w).im ≤ 0) :
    0 ≤ discAngle w ∧ discAngle w ≤ θ := by
  have hre : 0 ≤ w.re := re_nonneg_of_sector hθ hθ' h1 h2
  have hpos : 0 < ‖w‖ + w.re := norm_add_re_pos_of_re hw hre
  have hm := halfArg_mem ‖w‖ w.re w.im
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hp := halfArg_polar_self hw hpos
  set φ := discAngle w with hφ
  have hwim : w.im = ‖w‖ * Real.sin φ := by
    conv_lhs => rw [hp]
    rw [im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hwre : w.re = ‖w‖ * Real.cos φ := by
    conv_lhs => rw [hp]
    rw [re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hm' : φ ∈ Set.Ioo (-Real.pi) Real.pi := hm
  have hsin : 0 ≤ Real.sin φ := by
    rw [hwim] at h1
    by_contra hc
    push Not at hc
    have := mul_neg_of_pos_of_neg hn hc
    linarith
  have hφ0 : 0 ≤ φ := by
    by_contra hc
    push Not at hc
    have := Real.sin_neg_of_neg_of_neg_pi_lt hc hm'.1
    linarith
  refine ⟨hφ0, ?_⟩
  have h2' : (exp (-((θ : ℂ) * I)) * w).im = ‖w‖ * Real.sin (φ - θ) := by
    rw [exp_neg_ofReal_mul_I_eq]
    simp only [mul_im, sub_re, sub_im, ofReal_re, ofReal_im, mul_re, I_re, I_im]
    rw [hwim, hwre, Real.sin_sub]
    ring
  rw [h2'] at h2
  have hs : Real.sin (φ - θ) ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos hn hc
    linarith
  by_contra hc
  push Not at hc
  have hlt : φ - θ < Real.pi := by linarith [hm'.2]
  have := Real.sin_pos_of_pos_of_lt_pi (by linarith) hlt
  linarith

variable {σ : CompactShape}

section Hyp

variable (h : σ.curv = .hyperbolic)
include h

theorem canon_one_zero : canon σ 1 0 = tauThree σ := by
  change canonForm (tauTwo σ) ‖mob σ.vertexTwo 0‖ = _
  rw [mob_zero_right, norm_neg, norm_vertexTwo h, ← oplus_tauTwo_tauThree h]
  exact canonForm_oplus tauTwo_lt_one (by linarith [tauTwo_pos h])
    (by nlinarith [tauTwo_pos h, tauThree_pos h])

omit h in
theorem canon_two_zero : canon σ 2 0 = -tauThree σ := by
  change canonForm (tauThree σ) ‖(0 : ℂ)‖ = _
  rw [norm_zero, canonForm]
  simp

theorem canon_zero_zero : canon σ 0 0 = tauThree σ := by
  change canonForm (tauOne σ) ‖mob σ.vertexOne 0‖ = _
  rw [mob_zero_right, norm_neg, norm_vertexOne h, ← oplus_tauOne_tauThree h]
  exact canonForm_oplus tauOne_lt_one (by linarith [tauOne_pos h])
    (by nlinarith [tauOne_pos h, tauThree_pos h])

theorem canon_two_vertexTwo : canon σ 2 σ.vertexTwo = tauTwo σ := by
  change canonForm (tauThree σ) ‖σ.vertexTwo‖ = _
  rw [norm_vertexTwo h, ← oplus_tauTwo_tauThree h, oplus_comm]
  exact canonForm_oplus tauThree_lt_one (by linarith [tauThree_pos h])
    (by nlinarith [tauTwo_pos h, tauThree_pos h])

omit h in
theorem canon_one_vertexTwo : canon σ 1 σ.vertexTwo = -tauTwo σ := by
  change canonForm (tauTwo σ) ‖mob σ.vertexTwo σ.vertexTwo‖ = _
  rw [mob_self, norm_zero, canonForm]
  simp

theorem canon_two_vertexOne : canon σ 2 σ.vertexOne = tauOne σ := by
  change canonForm (tauThree σ) ‖σ.vertexOne‖ = _
  rw [norm_vertexOne h, ← oplus_tauOne_tauThree h, oplus_comm]
  exact canonForm_oplus tauThree_lt_one (by linarith [tauThree_pos h])
    (by nlinarith [tauOne_pos h, tauThree_pos h])

omit h in
theorem canon_zero_vertexOne : canon σ 0 σ.vertexOne = -tauOne σ := by
  change canonForm (tauOne σ) ‖mob σ.vertexOne σ.vertexOne‖ = _
  rw [mob_self, norm_zero, canonForm]
  simp

theorem canon_one_vertexOne : canon σ 1 σ.vertexOne = tauOne σ := by
  change canonForm (tauTwo σ) ‖mob σ.vertexTwo σ.vertexOne‖ = _
  have hn : ‖mob σ.vertexTwo σ.vertexOne‖ = sideOneTwo σ := by
    rw [← norm_rotTwo h, rotTwo_vertexOne h, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sideOneTwo_pos h)]
  rw [hn, ← oplus_tauOne_tauTwo h, oplus_comm]
  exact canonForm_oplus tauTwo_lt_one (by linarith [tauTwo_pos h])
    (by nlinarith [tauOne_pos h, tauTwo_pos h])

theorem canon_zero_vertexTwo : canon σ 0 σ.vertexTwo = tauTwo σ := by
  change canonForm (tauOne σ) ‖mob σ.vertexOne σ.vertexTwo‖ = _
  have hn : ‖mob σ.vertexOne σ.vertexTwo‖ = sideOneTwo σ := by
    rw [← norm_rotOne h, rotOne_vertexTwo h, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sideOneTwo_pos h), Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [hn, ← oplus_tauOne_tauTwo h]
  exact canonForm_oplus tauOne_lt_one (by linarith [tauOne_pos h])
    (by nlinarith [tauOne_pos h, tauTwo_pos h])

theorem canon_one_add_two_nonneg {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ canon σ 1 z + canon σ 2 z := by
  by_cases h0 : z = 0
  · subst h0
    rw [canon_one_zero h, canon_two_zero]
    simp
  by_cases h2 : z = σ.vertexTwo
  · subst h2
    rw [canon_one_vertexTwo, canon_two_vertexTwo h]
    simp
  have hd := mem_domZeroThree h hz h0 h2
  rw [canon_add_canon_zero_three h hd]
  exact mul_nonneg (sq_nonneg _) (cofZeroThree_pos h hd).le

theorem canon_zero_add_two_nonneg {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ canon σ 0 z + canon σ 2 z := by
  by_cases h0 : z = 0
  · subst h0
    rw [canon_zero_zero h, canon_two_zero]
    simp
  by_cases h1 : z = σ.vertexOne
  · subst h1
    rw [canon_zero_vertexOne, canon_two_vertexOne h]
    simp
  have hd := mem_domOneThree h hz h0 h1
  rw [canon_add_canon_one_three h hd]
  exact mul_nonneg (sq_nonneg _) (cofOneThree_pos h hd).le

theorem canon_zero_add_one_nonneg {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ canon σ 0 z + canon σ 1 z := by
  by_cases h1 : z = σ.vertexOne
  · subst h1
    rw [canon_zero_vertexOne, canon_one_vertexOne h]
    simp
  by_cases h2 : z = σ.vertexTwo
  · subst h2
    rw [canon_zero_vertexTwo h, canon_one_vertexTwo]
    simp
  have hd := mem_domOneTwo h hz h1 h2
  rw [canon_add_canon_side_two h hd]
  exact mul_nonneg (sq_nonneg _) (cofTwo_pos h hd).le

omit h in
theorem discAngle_mem {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) :
    0 ≤ discAngle z ∧ discAngle z ≤ σ.θ₃ :=
  discAngle_mem_sector (θ₃_pos σ) (θ₃_le σ) h0 (sector_three hz).1 (sector_three hz).2

theorem blendThree_ge_of_cornerOne {w δ e : ℝ} (hw : 0 < w) (hδ : 0 < δ) (he : δ ≤ e)
    {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (hc : canon σ 0 z ≤ -e) :
    w ≤ blendThree σ w δ z := by
  have hs := canon_zero_add_one_nonneg h hz
  have hd := discAngle_mem hz h0
  have hθ := θ₃_pos σ
  have h1 : -1 ≤ 2 * discAngle z / σ.θ₃ - 1 := by
    have : 0 ≤ 2 * discAngle z / σ.θ₃ := div_nonneg (by linarith [hd.1]) hθ.le
    linarith
  have h2 : 2 * w ≤ w / δ * (canon σ 1 z - canon σ 0 z) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    nlinarith
  unfold blendThree
  nlinarith

theorem blendThree_le_of_cornerTwo {w δ e : ℝ} (hw : 0 < w) (hδ : 0 < δ) (he : δ ≤ e)
    {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (hc : canon σ 1 z ≤ -e) :
    blendThree σ w δ z ≤ -w := by
  have hs := canon_zero_add_one_nonneg h hz
  have hd := discAngle_mem hz h0
  have hθ := θ₃_pos σ
  have h1 : 2 * discAngle z / σ.θ₃ - 1 ≤ 1 := by
    have : 2 * discAngle z / σ.θ₃ ≤ 2 := by
      rw [div_le_iff₀ hθ]
      linarith
    linarith
  have h2 : w / δ * (canon σ 1 z - canon σ 0 z) ≤ -(2 * w) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ]
    nlinarith
  unfold blendThree
  nlinarith

end Hyp

end HypFold

end GC.Seifert
