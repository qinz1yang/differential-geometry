import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidCorners

/-!
# The layout of the flat compact fold: incircle core and junction certificates

Lane CF, tier 3, curvature `0` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §5, as corrected by review 23 §6: shape-dependent
parameters). The triangle has circumdiameter one, sides `sin θₖ`, inradius
`inradius = sin θ₁ sin θ₂ sin θ₃ / (sin θ₁ + sin θ₂ + sin θ₃)` and incentre
`incenter = (sin θ₁ v₁ + sin θ₂ v₂)/(∑ sin θᵢ)`, at side-distance `inradius` from the three walls
(`wallSide_incenter`). In the coordinate `rotTwo` (wall 2 on the real axis, `v₂ ↦ 0`,
`v₁ ↦ sin θ₃`) the incentre is `radTwo + i·inradius` (`rotTwo_incenter`). The canonical radii are at
least the inradius (`inradius_le_radOne`, from `rⱼ sin θⱼ = ρ (1 + cos θⱼ)`, the law of cosines)
and shorter than the altitudes (`radOne_lt_altitude`). All layout parameters are proportional to
`ρ`: lens half-width `lensWidth = ρ/16`, switch top `switchTop = ρ/8`, corner shrink
`cornerShrink = ρ/64`, core radius `coreRadius = ρ - ρ/32`, margin `coreMargin = ρ/128`.

The junction certificates (review 23 §6.1): the whole lens arc `{wallSide 2 = β} ∩ T` outside the
two corner discs `{dⱼ < rⱼ - δ}` (`lensArc_mem_core`) and the switch windows
`{dⱼ = rⱼ - δ, β ≤ wallSide 2 ≤ β'} ∩ T` (`switchWindowOne_mem_core`, `switchWindowTwo_mem_core`)
lie in the core disc of radius `coreRadius - coreMargin` about the incentre. The proof is exact:
in the `rotTwo` coordinate the tangential offset of these points from the tangency point is at most
`δ + y²/(ρ - δ)` at height `y` (`gap_bound`), using only `rⱼ ≥ ρ`. A regression records why the
design's `ρ = 1` normalisation failed (review 23 §4.4): for `(2,3,6)` the ratio `radThree/ρ` is
`2 + √3` (`shape236_radThree_div_inradius`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem gap_bound {r v δ β ρ : ℝ} (hr : ρ ≤ r) (hδρ : δ < ρ) (hvr : v ≤ r)
    (hd : (r - δ) ^ 2 ≤ (r - v) ^ 2 + β ^ 2) : v ≤ δ + β ^ 2 / (ρ - δ) := by
  have hρδ : 0 < ρ - δ := by linarith
  by_contra h
  have h := not_le.1 h
  have hβ : 0 ≤ β ^ 2 / (ρ - δ) := by positivity
  have hvδ : δ < v := by linarith
  have key : (v - δ) * (2 * r - v - δ) ≤ β ^ 2 := by nlinarith
  have h2 : (v - δ) * (ρ - δ) ≤ (v - δ) * (2 * r - v - δ) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 : v - δ ≤ β ^ 2 / (ρ - δ) := by
    rw [le_div_iff₀ hρδ]
    linarith
  linarith

namespace EuclidShape

variable (σ : EuclidShape)

def sinSum : ℝ := Real.sin σ.θ₁ + Real.sin σ.θ₂ + Real.sin σ.θ₃

def inradius : ℝ := Real.sin σ.θ₁ * Real.sin σ.θ₂ * Real.sin σ.θ₃ / σ.sinSum

def incenter : ℂ :=
  ((Real.sin σ.θ₁ / σ.sinSum : ℝ) : ℂ) * σ.vertexOne +
    ((Real.sin σ.θ₂ / σ.sinSum : ℝ) : ℂ) * σ.vertexTwo

theorem sinSum_pos : 0 < σ.sinSum := by
  have := σ.sin_θ₁_pos
  have := σ.sin_θ₂_pos
  have := σ.sin_θ₃_pos
  unfold sinSum
  positivity

theorem inradius_pos : 0 < σ.inradius := by
  have := σ.sin_θ₁_pos
  have := σ.sin_θ₂_pos
  have := σ.sin_θ₃_pos
  have := σ.sinSum_pos
  unfold inradius
  positivity

theorem cos_θ₁_eq : Real.cos σ.θ₁ = Real.sin σ.θ₂ * Real.sin σ.θ₃ -
    Real.cos σ.θ₂ * Real.cos σ.θ₃ := by
  rw [show σ.θ₁ = Real.pi - (σ.θ₂ + σ.θ₃) by linarith [σ.θ_sum], Real.cos_pi_sub,
    Real.cos_add]
  ring

theorem cos_θ₂_eq : Real.cos σ.θ₂ = Real.sin σ.θ₁ * Real.sin σ.θ₃ -
    Real.cos σ.θ₁ * Real.cos σ.θ₃ := by
  rw [show σ.θ₂ = Real.pi - (σ.θ₁ + σ.θ₃) by linarith [σ.θ_sum], Real.cos_pi_sub,
    Real.cos_add]
  ring

theorem cos_θ₃_eq : Real.cos σ.θ₃ = Real.sin σ.θ₁ * Real.sin σ.θ₂ -
    Real.cos σ.θ₁ * Real.cos σ.θ₂ := by
  rw [show σ.θ₃ = Real.pi - (σ.θ₁ + σ.θ₂) by linarith [σ.θ_sum], Real.cos_pi_sub,
    Real.cos_add]
  ring

theorem lawOfCosines_one : Real.sin σ.θ₂ ^ 2 + Real.sin σ.θ₃ ^ 2 - Real.sin σ.θ₁ ^ 2 =
    2 * Real.sin σ.θ₂ * Real.sin σ.θ₃ * Real.cos σ.θ₁ := by
  rw [σ.sin_θ₁_eq, σ.cos_θ₁_eq]
  have h2 := Real.sin_sq_add_cos_sq σ.θ₂
  have h3 := Real.sin_sq_add_cos_sq σ.θ₃
  linear_combination (-(Real.sin σ.θ₂ ^ 2)) * h3 - Real.sin σ.θ₃ ^ 2 * h2


theorem inradius_le_radOne : σ.inradius ≤ σ.radOne := by
  have hS := σ.sinSum_pos
  have hL := σ.lawOfCosines_one
  have h1 := Real.sin_le_one σ.θ₁
  have hc := σ.cos_θ₁_nonneg
  have h2 := σ.sin_θ₂_pos
  have h3 := σ.sin_θ₃_pos
  have key : 2 * (Real.sin σ.θ₁ * Real.sin σ.θ₂ * Real.sin σ.θ₃) ≤
      (Real.sin σ.θ₂ + Real.sin σ.θ₃ - Real.sin σ.θ₁) * σ.sinSum := by
    unfold sinSum
    nlinarith [mul_pos h2 h3]
  rw [inradius, radOne, div_le_iff₀ hS]
  linarith

theorem lawOfCosines_two : Real.sin σ.θ₁ ^ 2 + Real.sin σ.θ₃ ^ 2 - Real.sin σ.θ₂ ^ 2 =
    2 * Real.sin σ.θ₁ * Real.sin σ.θ₃ * Real.cos σ.θ₂ := by
  rw [σ.sin_θ₂_eq, σ.cos_θ₂_eq]
  have h1 := Real.sin_sq_add_cos_sq σ.θ₁
  have h3 := Real.sin_sq_add_cos_sq σ.θ₃
  linear_combination (-(Real.sin σ.θ₁ ^ 2)) * h3 - Real.sin σ.θ₃ ^ 2 * h1

theorem lawOfCosines_three : Real.sin σ.θ₁ ^ 2 + Real.sin σ.θ₂ ^ 2 - Real.sin σ.θ₃ ^ 2 =
    2 * Real.sin σ.θ₁ * Real.sin σ.θ₂ * Real.cos σ.θ₃ := by
  rw [σ.sin_θ₃_eq, σ.cos_θ₃_eq]
  have h1 := Real.sin_sq_add_cos_sq σ.θ₁
  have h2 := Real.sin_sq_add_cos_sq σ.θ₂
  linear_combination (-(Real.sin σ.θ₁ ^ 2)) * h2 - Real.sin σ.θ₂ ^ 2 * h1

theorem inradius_le_radTwo : σ.inradius ≤ σ.radTwo := by
  have hS := σ.sinSum_pos
  have hL := σ.lawOfCosines_two
  have h2 := Real.sin_le_one σ.θ₂
  have hc := σ.cos_θ₂_nonneg
  have h1 := σ.sin_θ₁_pos
  have h3 := σ.sin_θ₃_pos
  have key : 2 * (Real.sin σ.θ₁ * Real.sin σ.θ₂ * Real.sin σ.θ₃) ≤
      (Real.sin σ.θ₃ + Real.sin σ.θ₁ - Real.sin σ.θ₂) * σ.sinSum := by
    unfold sinSum
    nlinarith [mul_pos h1 h3]
  rw [inradius, radTwo, div_le_iff₀ hS]
  linarith

theorem inradius_le_radThree : σ.inradius ≤ σ.radThree := by
  have hS := σ.sinSum_pos
  have hL := σ.lawOfCosines_three
  have h3 := Real.sin_le_one σ.θ₃
  have hc := σ.cos_θ₃_nonneg
  have h1 := σ.sin_θ₁_pos
  have h2 := σ.sin_θ₂_pos
  have key : 2 * (Real.sin σ.θ₁ * Real.sin σ.θ₂ * Real.sin σ.θ₃) ≤
      (Real.sin σ.θ₁ + Real.sin σ.θ₂ - Real.sin σ.θ₃) * σ.sinSum := by
    unfold sinSum
    nlinarith [mul_pos h1 h2]
  rw [inradius, radThree, div_le_iff₀ hS]
  linarith

theorem one_le_sin_add_cos {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ Real.pi / 2) :
    1 ≤ Real.sin θ + Real.cos θ := by
  have hs := EuclidShape.sin_pos_aux h0 h1
  have hc := EuclidShape.cos_nonneg_aux h0 h1
  have hp := Real.sin_sq_add_cos_sq θ
  nlinarith [mul_nonneg hs.le hc]

theorem radOne_lt_altitude : σ.radOne < Real.sin σ.θ₂ * Real.sin σ.θ₃ := by
  have he := σ.sin_θ₁_eq
  have a2 := one_le_sin_add_cos σ.θ₂_pos σ.θ₂_le
  have a3 := one_le_sin_add_cos σ.θ₃_pos σ.θ₃_le
  have h1 := σ.sin_θ₁_pos
  have h2 := σ.sin_θ₂_pos
  have h3 := σ.sin_θ₃_pos
  have hc2 := σ.cos_θ₂_nonneg
  have hc3 := σ.cos_θ₃_nonneg
  have hstrict : 0 < Real.cos σ.θ₂ ∨ 0 < Real.cos σ.θ₃ := by
    by_contra hc
    push Not at hc
    have e2 : Real.cos σ.θ₂ = 0 := le_antisymm hc.1 hc2
    have e3 : Real.cos σ.θ₃ = 0 := le_antisymm hc.2 hc3
    rw [e2, e3] at he
    linarith
  rw [radOne, he]
  rcases hstrict with h | h
  · have : 1 < Real.sin σ.θ₂ + Real.cos σ.θ₂ := by
      have hp := Real.sin_sq_add_cos_sq σ.θ₂
      nlinarith [mul_pos h2 h]
    nlinarith [mul_pos h3 (by linarith : 0 < Real.sin σ.θ₂ + Real.cos σ.θ₂ - 1),
      mul_nonneg h2.le (by linarith : 0 ≤ Real.sin σ.θ₃ + Real.cos σ.θ₃ - 1)]
  · have : 1 < Real.sin σ.θ₃ + Real.cos σ.θ₃ := by
      have hp := Real.sin_sq_add_cos_sq σ.θ₃
      nlinarith [mul_pos h3 h]
    nlinarith [mul_pos h2 (by linarith : 0 < Real.sin σ.θ₃ + Real.cos σ.θ₃ - 1),
      mul_nonneg h3.le (by linarith : 0 ≤ Real.sin σ.θ₂ + Real.cos σ.θ₂ - 1)]

theorem radTwo_lt_altitude : σ.radTwo < Real.sin σ.θ₁ * Real.sin σ.θ₃ := by
  have he := σ.sin_θ₂_eq
  have a1 := one_le_sin_add_cos σ.θ₁_pos σ.θ₁_le
  have a3 := one_le_sin_add_cos σ.θ₃_pos σ.θ₃_le
  have h1 := σ.sin_θ₁_pos
  have h2 := σ.sin_θ₂_pos
  have h3 := σ.sin_θ₃_pos
  have hc1 := σ.cos_θ₁_nonneg
  have hc3 := σ.cos_θ₃_nonneg
  have hstrict : 0 < Real.cos σ.θ₁ ∨ 0 < Real.cos σ.θ₃ := by
    by_contra hc
    push Not at hc
    have e1 : Real.cos σ.θ₁ = 0 := le_antisymm hc.1 hc1
    have e3 : Real.cos σ.θ₃ = 0 := le_antisymm hc.2 hc3
    rw [e1, e3] at he
    linarith
  rw [radTwo, he]
  rcases hstrict with h | h
  · have : 1 < Real.sin σ.θ₁ + Real.cos σ.θ₁ := by
      have hp := Real.sin_sq_add_cos_sq σ.θ₁
      nlinarith [mul_pos h1 h]
    nlinarith [mul_pos h3 (by linarith : 0 < Real.sin σ.θ₁ + Real.cos σ.θ₁ - 1),
      mul_nonneg h1.le (by linarith : 0 ≤ Real.sin σ.θ₃ + Real.cos σ.θ₃ - 1)]
  · have : 1 < Real.sin σ.θ₃ + Real.cos σ.θ₃ := by
      have hp := Real.sin_sq_add_cos_sq σ.θ₃
      nlinarith [mul_pos h3 h]
    nlinarith [mul_pos h1 (by linarith : 0 < Real.sin σ.θ₃ + Real.cos σ.θ₃ - 1),
      mul_nonneg h3.le (by linarith : 0 ≤ Real.sin σ.θ₁ + Real.cos σ.θ₁ - 1)]

theorem two_inradius_lt_altitudeThree : 2 * σ.inradius < Real.sin σ.θ₁ * Real.sin σ.θ₂ := by
  have hS := σ.sinSum_pos
  have he := σ.sin_θ₃_eq
  have h1 := σ.sin_θ₁_pos
  have h2 := σ.sin_θ₂_pos
  have hc1 := cos_lt_one_aux σ.θ₁_pos σ.θ₁_le
  have hc2 := Real.cos_le_one σ.θ₂
  have hlt : Real.sin σ.θ₃ < Real.sin σ.θ₁ + Real.sin σ.θ₂ := by
    rw [he]
    nlinarith [mul_pos h2 (by linarith : 0 < 1 - Real.cos σ.θ₁), mul_nonneg h1.le
      (by linarith : 0 ≤ 1 - Real.cos σ.θ₂)]
  rw [inradius, mul_div_assoc', div_lt_iff₀ hS]
  unfold sinSum
  nlinarith [mul_pos h1 h2]

theorem inradius_lt_half : σ.inradius < 1 / 2 := by
  have h := σ.two_inradius_lt_altitudeThree
  have := Real.sin_le_one σ.θ₁
  have := Real.sin_le_one σ.θ₂
  have := σ.sin_θ₁_pos
  have := σ.sin_θ₂_pos
  nlinarith

theorem incenter_re : σ.incenter.re = (Real.sin σ.θ₁ * (Real.sin σ.θ₂ * Real.cos σ.θ₃) +
    Real.sin σ.θ₂ * Real.sin σ.θ₁) / σ.sinSum := by
  simp only [incenter, add_re, re_ofReal_mul, σ.vertexOne_re', σ.vertexTwo_re']
  ring

theorem incenter_im : σ.incenter.im =
    Real.sin σ.θ₁ * (Real.sin σ.θ₂ * Real.sin σ.θ₃) / σ.sinSum := by
  simp only [incenter, add_im, im_ofReal_mul, σ.vertexOne_im', σ.vertexTwo_im', mul_zero,
    add_zero]
  ring

theorem wallSide_zero_incenter : σ.wallSide 0 σ.incenter = σ.inradius := by
  rw [wallSide_zero_apply, incenter_im, inradius]
  ring

theorem wallSide_one_incenter : σ.wallSide 1 σ.incenter = σ.inradius := by
  have hS := σ.sinSum_pos.ne'
  rw [wallSide_one_apply, incenter_re, incenter_im, inradius]
  field_simp
  ring

theorem wallSide_two_incenter : σ.wallSide 2 σ.incenter = σ.inradius := by
  have hS := σ.sinSum_pos.ne'
  have he := σ.sin_θ₁_eq
  rw [wallSide_two_apply, incenter_re, incenter_im, inradius]
  field_simp
  unfold sinSum
  rw [he]
  ring

theorem rotTwo_re_eq (z : ℂ) : (σ.rotTwo z).re = -(Real.cos σ.θ₂ * z.re) +
    Real.cos σ.θ₂ * Real.sin σ.θ₁ + Real.sin σ.θ₂ * z.im := by
  simp only [rotTwo, neg_re, mul_re, sub_re, sub_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, σ.vertexTwo_re', σ.vertexTwo_im']
  ring

theorem rotTwo_incenter_re : (σ.rotTwo σ.incenter).re = σ.radTwo := by
  have hS := σ.sinSum_pos.ne'
  have h2 := Real.sin_sq_add_cos_sq σ.θ₂
  have h3 := Real.sin_sq_add_cos_sq σ.θ₃
  have key : 2 * (-(Real.cos σ.θ₂) * (Real.sin σ.θ₁ * Real.sin σ.θ₂ * Real.cos σ.θ₃ +
      Real.sin σ.θ₂ * Real.sin σ.θ₁) + Real.cos σ.θ₂ * Real.sin σ.θ₁ * σ.sinSum +
      Real.sin σ.θ₂ * (Real.sin σ.θ₁ * Real.sin σ.θ₂ * Real.sin σ.θ₃)) =
      (Real.sin σ.θ₃ + Real.sin σ.θ₁ - Real.sin σ.θ₂) * σ.sinSum := by
    unfold sinSum
    rw [σ.sin_θ₁_eq]
    linear_combination (2 * Real.cos σ.θ₂ * Real.sin σ.θ₃ ^ 2 - Real.cos σ.θ₃ ^ 2 +
      2 * Real.cos σ.θ₃ * Real.sin σ.θ₂ * Real.sin σ.θ₃ + 1) * h2 +
      (Real.cos σ.θ₂ ^ 2 - 1) * h3
  rw [rotTwo_re_eq, incenter_re, incenter_im, radTwo]
  field_simp
  linear_combination key

theorem rotTwo_incenter : σ.rotTwo σ.incenter = (σ.radTwo : ℂ) + (σ.inradius : ℂ) * I := by
  apply Complex.ext
  · rw [rotTwo_incenter_re]
    simp
  · change σ.wallSide 2 σ.incenter = _
    rw [wallSide_two_incenter]
    simp

theorem norm_sub_eq_rotTwo (z w : ℂ) : ‖z - w‖ = ‖σ.rotTwo z - σ.rotTwo w‖ := by
  rw [rotTwo, rotTwo, neg_sub_neg, ← mul_sub, norm_mul, norm_exp_mul_I, one_mul, norm_sub_rev]
  congr 1
  ring

def lensWidth : ℝ := σ.inradius / 16

def switchTop : ℝ := σ.inradius / 8

def cornerShrink : ℝ := σ.inradius / 64

def coreRadius : ℝ := σ.inradius - σ.inradius / 32

def coreMargin : ℝ := σ.inradius / 128

theorem norm_sq_sub_incenter (z : ℂ) : ‖z - σ.incenter‖ ^ 2 =
    ((σ.rotTwo z).re - σ.radTwo) ^ 2 + (σ.wallSide 2 z - σ.inradius) ^ 2 := by
  rw [σ.norm_sub_eq_rotTwo, rotTwo_incenter, EuclidShape.normSq_eq_sq_norm]
  simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, sub_im, add_im, mul_im]
  change _ = _ + ((σ.rotTwo z).im - σ.inradius) ^ 2
  ring

theorem norm_sq_sub_vertexTwo (z : ℂ) : ‖z - σ.vertexTwo‖ ^ 2 =
    (σ.rotTwo z).re ^ 2 + σ.wallSide 2 z ^ 2 := by
  rw [← σ.norm_rotTwo, EuclidShape.normSq_eq_sq_norm]
  rfl

theorem norm_sq_sub_vertexOne (z : ℂ) : ‖z - σ.vertexOne‖ ^ 2 =
    (Real.sin σ.θ₃ - (σ.rotTwo z).re) ^ 2 + σ.wallSide 2 z ^ 2 := by
  rw [σ.norm_sub_vertexOne_eq_rotTwo, EuclidShape.normSq_eq_sq_norm]
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, zero_sub, neg_sq]
  rfl

theorem radOne_add_radTwo' : σ.radOne + σ.radTwo = Real.sin σ.θ₃ := σ.radOne_add_radTwo

theorem tangential_bound {z : ℂ} (hz : z ∈ σ.triangle) {y : ℝ} (hy : σ.wallSide 2 z = y)
    (h1 : σ.radOne - σ.cornerShrink ≤ ‖z - σ.vertexOne‖)
    (h2 : σ.radTwo - σ.cornerShrink ≤ ‖z - σ.vertexTwo‖) :
    ((σ.rotTwo z).re - σ.radTwo) ^ 2 ≤
      (σ.cornerShrink + y ^ 2 / (σ.inradius - σ.cornerShrink)) ^ 2 := by
  have hρ := σ.inradius_pos
  have hr1 := σ.inradius_le_radOne
  have hr2 := σ.inradius_le_radTwo
  have hδρ : σ.cornerShrink < σ.inradius := by unfold cornerShrink; linarith
  have hδ0 : 0 ≤ σ.cornerShrink := by unfold cornerShrink; positivity
  obtain ⟨hX0, hX1⟩ := σ.re_rotTwo_mem hz
  have hs := σ.radOne_add_radTwo
  have hB : 0 ≤ σ.cornerShrink + y ^ 2 / (σ.inradius - σ.cornerShrink) := by
    have : 0 ≤ y ^ 2 / (σ.inradius - σ.cornerShrink) := div_nonneg (sq_nonneg _) (by linarith)
    linarith
  rcases le_total (σ.rotTwo z).re σ.radTwo with hu | hu
  · have hd : (σ.radTwo - σ.cornerShrink) ^ 2 ≤
        (σ.radTwo - (σ.radTwo - (σ.rotTwo z).re)) ^ 2 + y ^ 2 := by
      have := σ.norm_sq_sub_vertexTwo z
      rw [hy] at this
      have hnn : 0 ≤ σ.radTwo - σ.cornerShrink := by linarith
      have := pow_le_pow_left₀ hnn h2 2
      nlinarith
    have hv := gap_bound hr2 hδρ (by linarith) hd
    have hv0 : 0 ≤ σ.radTwo - (σ.rotTwo z).re := by linarith
    nlinarith
  · have hd : (σ.radOne - σ.cornerShrink) ^ 2 ≤
        (σ.radOne - ((σ.rotTwo z).re - σ.radTwo)) ^ 2 + y ^ 2 := by
      have := σ.norm_sq_sub_vertexOne z
      rw [hy] at this
      have hnn : 0 ≤ σ.radOne - σ.cornerShrink := by linarith
      have := pow_le_pow_left₀ hnn h1 2
      have e : σ.radOne - ((σ.rotTwo z).re - σ.radTwo) = Real.sin σ.θ₃ - (σ.rotTwo z).re := by
        linarith
      rw [e]
      nlinarith
    have hv := gap_bound hr1 hδρ (by linarith) hd
    have hv0 : 0 ≤ (σ.rotTwo z).re - σ.radTwo := by linarith
    nlinarith

theorem lensArc_mem_core {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 2 z = σ.lensWidth)
    (h1 : σ.radOne - σ.cornerShrink ≤ ‖z - σ.vertexOne‖)
    (h2 : σ.radTwo - σ.cornerShrink ≤ ‖z - σ.vertexTwo‖) :
    ‖z - σ.incenter‖ < σ.coreRadius - σ.coreMargin := by
  have hρ := σ.inradius_pos
  have ht := σ.tangential_bound hz hw h1 h2
  have hsq := σ.norm_sq_sub_incenter z
  rw [hw] at hsq
  have hc : 0 < σ.coreRadius - σ.coreMargin := by unfold coreRadius coreMargin; linarith
  have e : σ.cornerShrink + σ.lensWidth ^ 2 / (σ.inradius - σ.cornerShrink) =
      σ.inradius * (1 / 64 + 1 / 252) := by
    unfold cornerShrink lensWidth
    field_simp
    ring
  rw [e] at ht
  have key : ‖z - σ.incenter‖ ^ 2 < (σ.coreRadius - σ.coreMargin) ^ 2 := by
    rw [hsq]
    unfold lensWidth coreRadius coreMargin
    nlinarith [mul_pos hρ hρ]
  exact lt_of_pow_lt_pow_left₀ 2 hc.le key

theorem switchWindow_mem_core {z : ℂ} (hz : z ∈ σ.triangle)
    (hlo : σ.lensWidth ≤ σ.wallSide 2 z) (hhi : σ.wallSide 2 z ≤ σ.switchTop)
    (h1 : σ.radOne - σ.cornerShrink ≤ ‖z - σ.vertexOne‖)
    (h2 : σ.radTwo - σ.cornerShrink ≤ ‖z - σ.vertexTwo‖) :
    ‖z - σ.incenter‖ < σ.coreRadius - σ.coreMargin := by
  have hρ := σ.inradius_pos
  have ht := σ.tangential_bound hz rfl h1 h2
  have hsq := σ.norm_sq_sub_incenter z
  have hc : 0 < σ.coreRadius - σ.coreMargin := by unfold coreRadius coreMargin; linarith
  have hy0 : 0 ≤ σ.wallSide 2 z := le_trans (by unfold lensWidth; positivity) hlo
  have hyb : σ.wallSide 2 z ^ 2 ≤ σ.switchTop ^ 2 := pow_le_pow_left₀ hy0 hhi 2
  have hδρ : 0 < σ.inradius - σ.cornerShrink := by unfold cornerShrink; linarith
  have hB : σ.cornerShrink + σ.wallSide 2 z ^ 2 / (σ.inradius - σ.cornerShrink) ≤
      σ.inradius * (1 / 64 + 1 / 63) := by
    have : σ.wallSide 2 z ^ 2 / (σ.inradius - σ.cornerShrink) ≤
        σ.switchTop ^ 2 / (σ.inradius - σ.cornerShrink) :=
      div_le_div_of_nonneg_right hyb hδρ.le
    have e : σ.cornerShrink + σ.switchTop ^ 2 / (σ.inradius - σ.cornerShrink) =
        σ.inradius * (1 / 64 + 1 / 63) := by
      unfold cornerShrink switchTop
      field_simp
      ring
    linarith
  have hB0 : 0 ≤ σ.cornerShrink + σ.wallSide 2 z ^ 2 / (σ.inradius - σ.cornerShrink) :=
    add_nonneg (by unfold cornerShrink; positivity) (div_nonneg (sq_nonneg _) hδρ.le)
  have ht' : ((σ.rotTwo z).re - σ.radTwo) ^ 2 ≤ (σ.inradius * (1 / 64 + 1 / 63)) ^ 2 :=
    le_trans ht (pow_le_pow_left₀ hB0 hB 2)
  have hy1 : (σ.wallSide 2 z - σ.inradius) ^ 2 ≤ (σ.inradius - σ.lensWidth) ^ 2 := by
    have : σ.wallSide 2 z ≤ σ.inradius := le_trans hhi (by unfold switchTop; linarith)
    nlinarith
  have key : ‖z - σ.incenter‖ ^ 2 < (σ.coreRadius - σ.coreMargin) ^ 2 := by
    rw [hsq]
    unfold lensWidth coreRadius coreMargin at *
    nlinarith [mul_pos hρ hρ]
  exact lt_of_pow_lt_pow_left₀ 2 hc.le key


theorem shape236_θ₁ : shape236.θ₁ = Real.pi / 2 := by
  simp [θ₁, shape236]

theorem shape236_θ₂ : shape236.θ₂ = Real.pi / 3 := by
  simp [θ₂, shape236]

theorem shape236_θ₃ : shape236.θ₃ = Real.pi / 6 := by
  simp [θ₃, shape236]

theorem shape236_radThree_div_inradius :
    shape236.radThree / shape236.inradius = 2 + Real.sqrt 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  simp only [radThree, inradius, sinSum, shape236_θ₁, shape236_θ₂, shape236_θ₃,
    Real.sin_pi_div_two, Real.sin_pi_div_three, Real.sin_pi_div_six]
  field_simp
  nlinarith [h3]

theorem shape236_design_profile_violation :
    1 < shape236.radThree / shape236.inradius / 2 := by
  rw [shape236_radThree_div_inradius]
  have : 1 < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

end EuclidShape

end GC.Seifert
