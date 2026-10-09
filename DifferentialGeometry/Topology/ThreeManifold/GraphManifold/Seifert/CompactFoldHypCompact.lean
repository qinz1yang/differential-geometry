import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypCornerWalls
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldGenericShape

/-!
# Compactness of the hyperbolic compact triangle

Lane CF-H, tier 3 (design
`docs/geometrization/handoffs/20261004-design-cf-compact-triangle-fold.md`, §6, curvature `-1`).
In the Klein coordinate `klein z = 2z/(1 + |z|²)` the side function of wall 2 is
`(1 + |z|²)/2` times an affine function of `klein z` (`wallSide_two_klein`), and those of walls
0, 1 are positive multiples of linear ones, so the triangle is a Euclidean triangle in the Klein
coordinate with vertices `0`, `klein v₂`, `klein v₁`. Writing a point as a convex combination of
the vertices (`bary_bound_aux`) bounds `‖klein z‖` by the larger of `‖klein vⱼ‖`; since
`r ↦ 2r/(1 + r²)` is increasing on `[0, 1]` (`frac_mono`, `le_of_klein_le`) this gives
`‖z‖ ≤ max (‖v₁‖, ‖v₂‖) < 1` on the triangle (`norm_le_of_mem`). Hence the triangle is the
intersection of a closed ball inside the disc with three closed half-planes
(`triangle_eq_closed`) and is compact (`isCompact_triangle`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set
open scoped ComplexConjugate

namespace GC.Seifert

namespace HypFold

def klein (z : ℂ) : ℂ := (2 / (1 + normSq z) : ℝ) * z

theorem klein_re (z : ℂ) : (klein z).re = 2 / (1 + normSq z) * z.re := by
  rw [klein, Complex.re_ofReal_mul]

theorem klein_im (z : ℂ) : (klein z).im = 2 / (1 + normSq z) * z.im := by
  rw [klein, Complex.im_ofReal_mul]

theorem norm_klein (z : ℂ) : ‖klein z‖ = 2 * ‖z‖ / (1 + ‖z‖ ^ 2) := by
  have h : 0 < 1 + normSq z := by linarith [Complex.normSq_nonneg z]
  rw [klein, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    Complex.normSq_eq_norm_sq]
  ring

theorem le_of_klein_le {r M : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (hM1 : M < 1)
    (h : 2 * r / (1 + r ^ 2) ≤ 2 * M / (1 + M ^ 2)) : r ≤ M := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at h
  by_contra hc
  push Not at hc
  have : 0 < (r - M) * (1 - r * M) := mul_pos (by linarith) (by nlinarith)
  nlinarith

theorem frac_mono {t M : ℝ} (ht : 0 ≤ t) (htM : t ≤ M) (hM1 : M ≤ 1) :
    2 * t / (1 + t ^ 2) ≤ 2 * M / (1 + M ^ 2) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ (M - t) * (1 - t * M) := mul_nonneg (by linarith) (by nlinarith)
  nlinarith

theorem bary_bound_aux {X Y s c t₂ s₂ c₂ m₁ m₂ : ℝ} (hs : 0 < s) (hc1 : c ≤ 1)
    (hcs : s ^ 2 + c ^ 2 = 1) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (ht₂ : 0 < t₂) (hs₂ : 0 < s₂)
    (hm₂t : m₂ * (1 + t₂ ^ 2) = 2 * t₂) (hy : 0 ≤ Y) (hw : 0 ≤ s * X - c * Y)
    (hA : 0 ≤ 2 * t₂ * s₂ - (1 + t₂ ^ 2) * s₂ * X - (1 - t₂ ^ 2) * c₂ * Y)
    (hA1 : 2 * t₂ * s₂ - (1 + t₂ ^ 2) * s₂ * (m₁ * c) - (1 - t₂ ^ 2) * c₂ * (m₁ * s) = 0) :
    X ^ 2 + Y ^ 2 ≤ max m₁ m₂ ^ 2 := by
  set a := Y / s with ha
  set b := (s * X - c * Y) / s with hb
  have ha0 : 0 ≤ a := div_nonneg hy hs.le
  have hb0 : 0 ≤ b := div_nonneg hw hs.le
  have hX : X = a * c + b := by
    rw [ha, hb]; field_simp; ring
  have hY : Y = a * s := by rw [ha]; field_simp
  have hcoef : (1 - t₂ ^ 2) * c₂ * s = (2 * t₂ * s₂ - (1 + t₂ ^ 2) * s₂ * (m₁ * c)) / m₁ := by
    rw [eq_div_iff hm₁.ne']
    linear_combination -hA1
  have hsum : 2 * t₂ * s₂ * (1 - a / m₁ - b / m₂) =
      2 * t₂ * s₂ - (1 + t₂ ^ 2) * s₂ * X - (1 - t₂ ^ 2) * c₂ * Y := by
    rw [hX, hY]
    have e1 : (1 - t₂ ^ 2) * c₂ * (a * s) = a * ((1 - t₂ ^ 2) * c₂ * s) := by ring
    rw [e1, hcoef]
    have e2 : (1 + t₂ ^ 2) = 2 * t₂ / m₂ := by rw [eq_div_iff hm₂.ne']; linarith
    rw [e2]
    field_simp
    ring
  have hl : a / m₁ + b / m₂ ≤ 1 := by
    have h0 : 0 < 2 * t₂ * s₂ := by positivity
    have : 0 ≤ 2 * t₂ * s₂ * (1 - a / m₁ - b / m₂) := by rw [hsum]; exact hA
    have := (mul_nonneg_iff_of_pos_left h0).1 this
    linarith
  set M := max m₁ m₂
  have hM1 : m₁ ≤ M := le_max_left _ _
  have hM2 : m₂ ≤ M := le_max_right _ _
  have hab : a + b ≤ M := by
    have e : a + b = a / m₁ * m₁ + b / m₂ * m₂ := by field_simp
    have h1 : a / m₁ * m₁ ≤ a / m₁ * M := mul_le_mul_of_nonneg_left hM1 (by positivity)
    have h2 : b / m₂ * m₂ ≤ b / m₂ * M := mul_le_mul_of_nonneg_left hM2 (by positivity)
    have hM0 : 0 ≤ M := le_trans hm₁.le hM1
    nlinarith
  rw [hX, hY]
  have : (a * c + b) ^ 2 + (a * s) ^ 2 ≤ (a + b) ^ 2 := by
    have e : (a * c + b) ^ 2 + (a * s) ^ 2 = a ^ 2 * (s ^ 2 + c ^ 2) + 2 * a * b * c + b ^ 2 := by
      ring
    rw [e, hcs]
    nlinarith [mul_nonneg (mul_nonneg ha0 hb0) (sub_nonneg.2 hc1)]
  have hab0 : 0 ≤ a + b := by positivity
  nlinarith

variable {σ : CompactShape}

section Hyp

variable (h : σ.curv = .hyperbolic)
include h

theorem wallSide_two_klein (z : ℂ) : σ.wallSide 2 z = (1 + normSq z) / 2 *
    (2 * sideTwoThree σ * Real.sin σ.θ₂ - (1 + sideTwoThree σ ^ 2) * Real.sin σ.θ₂ *
      (klein z).re - (1 - sideTwoThree σ ^ 2) * Real.cos σ.θ₂ * (klein z).im) := by
  have hp : (1 + normSq z) ≠ 0 := by linarith [Complex.normSq_nonneg z]
  rw [wallSide_two_apply h, klein_re, klein_im]
  field_simp

theorem norm_le_of_mem {z : ℂ} (hz : z ∈ σ.triangle) :
    ‖z‖ ≤ max (sideOneThree σ) (sideTwoThree σ) := by
  have hz1 := norm_lt_one_of_mem h hz
  have t10 := sideOneThree_pos h
  have t11 := sideOneThree_lt_one h
  have t20 := sideTwoThree_pos h
  have t21 := sideTwoThree_lt_one h
  have hs := sin_pos_of_le (θ₃_pos σ) (θ₃_le σ)
  have hs2 := sin_pos_of_le (θ₂_pos σ) (θ₂_le σ)
  have hc := cos_nonneg_of_le (θ₃_pos σ) (θ₃_le σ)
  have hcs := Real.sin_sq_add_cos_sq σ.θ₃
  have hw2 := hz.2 2
  rw [wallSide_two_klein h] at hw2
  have hv := wallSide_two_vertexOne h
  rw [wallSide_two_klein h] at hv
  have hv1re : σ.vertexOne.re = sideOneThree σ * Real.cos σ.θ₃ := by
    rw [vertexOne_eq, exp_ofReal_mul_I_eq]
    simp only [mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have hv1im : σ.vertexOne.im = sideOneThree σ * Real.sin σ.θ₃ := by
    rw [vertexOne_eq, exp_ofReal_mul_I_eq]
    simp only [mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have hnv1 : normSq σ.vertexOne = sideOneThree σ ^ 2 := by
    rw [normSq_apply, hv1re, hv1im]; nlinarith
  rw [klein_re, klein_im, hv1re, hv1im, hnv1] at hv
  have hq1 : 0 < (1 + sideOneThree σ ^ 2) / 2 := by positivity
  have hA1 := (mul_eq_zero.1 hv).resolve_left hq1.ne'
  have hqz : 0 < (1 + normSq z) / 2 := by linarith [Complex.normSq_nonneg z]
  have hA := (mul_nonneg_iff_of_pos_left hqz).1 hw2
  have hy : 0 ≤ (klein z).im := by
    rw [klein_im]
    have : 0 ≤ z.im := hz.2 0
    have := Complex.normSq_nonneg z
    positivity
  have hw1 : 0 ≤ Real.sin σ.θ₃ * (klein z).re - Real.cos σ.θ₃ * (klein z).im := by
    have := hz.2 1
    rw [wallSide_one_apply] at this
    rw [klein_re, klein_im]
    have hk : 0 ≤ 2 / (1 + normSq z) := by have := Complex.normSq_nonneg z; positivity
    nlinarith
  have hm₁ : 0 < 2 / (1 + sideOneThree σ ^ 2) * sideOneThree σ := by positivity
  have hm₂ : 0 < 2 * sideTwoThree σ / (1 + sideTwoThree σ ^ 2) := by positivity
  have hm₂t : 2 * sideTwoThree σ / (1 + sideTwoThree σ ^ 2) * (1 + sideTwoThree σ ^ 2) =
      2 * sideTwoThree σ := by field_simp
  have hb := bary_bound_aux (X := (klein z).re) (Y := (klein z).im) (m₁ := 2 /
    (1 + sideOneThree σ ^ 2) * sideOneThree σ) hs (Real.cos_le_one _) hcs hm₁ hm₂ t20 hs2 hm₂t
    hy hw1 hA
    (by linear_combination hA1)
  have hK : ‖klein z‖ ^ 2 = (klein z).re ^ 2 + (klein z).im ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]; ring
  have hM : max (2 / (1 + sideOneThree σ ^ 2) * sideOneThree σ)
      (2 * sideTwoThree σ / (1 + sideTwoThree σ ^ 2)) ≤
      2 * max (sideOneThree σ) (sideTwoThree σ) /
        (1 + max (sideOneThree σ) (sideTwoThree σ) ^ 2) := by
    apply max_le
    · rw [show 2 / (1 + sideOneThree σ ^ 2) * sideOneThree σ =
          2 * sideOneThree σ / (1 + sideOneThree σ ^ 2) by ring]
      exact frac_mono t10.le (le_max_left _ _) (max_le t11.le t21.le)
    · exact frac_mono t20.le (le_max_right _ _) (max_le t11.le t21.le)
  have hKn : ‖klein z‖ ≤ 2 * max (sideOneThree σ) (sideTwoThree σ) /
      (1 + max (sideOneThree σ) (sideTwoThree σ) ^ 2) := by
    have hm0 : 0 ≤ max (2 / (1 + sideOneThree σ ^ 2) * sideOneThree σ)
        (2 * sideTwoThree σ / (1 + sideTwoThree σ ^ 2)) := le_trans hm₁.le (le_max_left _ _)
    have : ‖klein z‖ ≤ max (2 / (1 + sideOneThree σ ^ 2) * sideOneThree σ)
        (2 * sideTwoThree σ / (1 + sideTwoThree σ ^ 2)) := by
      rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hm0 two_ne_zero, hK]
      exact hb
    linarith
  rw [norm_klein] at hKn
  exact le_of_klein_le (norm_nonneg z) hz1 (max_lt t11 t21) hKn

theorem triangle_eq_closed : σ.triangle =
    Metric.closedBall 0 (max (sideOneThree σ) (sideTwoThree σ)) ∩
      {z | ∀ i, 0 ≤ σ.wallSide i z} := by
  ext z
  constructor
  · intro hz
    exact ⟨by simpa using norm_le_of_mem h hz, hz.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [CompactShape.plane_hyp h]
    have : ‖z‖ ≤ max (sideOneThree σ) (sideTwoThree σ) := by simpa using h1
    simpa using lt_of_le_of_lt this (max_lt (sideOneThree_lt_one h) (sideTwoThree_lt_one h))

theorem isCompact_triangle : IsCompact σ.triangle := by
  rw [triangle_eq_closed h]
  refine (isCompact_closedBall _ _).inter_right ?_
  have : {z : ℂ | ∀ i, 0 ≤ σ.wallSide i z} = ⋂ i, {z | 0 ≤ σ.wallSide i z} := by
    ext z
    simp
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (σ.continuous_wallSide i)

end Hyp

end HypFold

end GC.Seifert
