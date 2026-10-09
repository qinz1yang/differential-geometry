import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldTriangle

/-!
# The Fermi chart of the circle wall

Lane A4, layout (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, errata after
review 15). The Möbius map `fermiChart z = k (z - e₁)/(e₂ - z)`, with `e₁, e₂ = c ∓ 1/4` the feet of
the circle wall and `k = 4 √K/(1 + cos θ₁)`, is an isometry of the upper half-plane sending the
circle wall to the imaginary axis, the triangle to the left half-plane, the cone vertex `v₁` to
`i/√t₁` and `v₂` to `i √t₂`, with the uniform parameters
`t₁ = (1 - cos θ₁)/(1 + cos θ₂)`, `t₂ = (1 - cos θ₂)/(1 + cos θ₁)` (`t₂ = 0` for a cusp).
In the chart `ζ = X + iY` the Fermi coordinates `(s, n)` of the wall are `|ζ| = e^s` and
`sinh n = -X/Y`, and `-X/Y = 2 w(z)/Im z` with `w` the side function of the circle wall
(`neg_re_div_im_fermiChart`, the `σ₂`-odd wall function of review 15).

Every region of the layout is a Euclidean disc or half-plane in the chart:
* the virtual heights satisfy `√K η₁ (1 + t₁|ζ|²) = Y (η₁² + Im v₁²)`
  (`sqrt_constK_mul_coneHeight_one`), `√K η₂ (|ζ|² + t₂) = Y (η₂² + Im v₂²)` for a second cone
  (`sqrt_constK_mul_coneHeight_two`) and `√K |ζ|² = Y η₀` for the cusp `0`
  (`sqrt_constK_mul_normSq_fermiChart`); so the cone disc `η₁ < √K/λ` is
  `1 + t₁|ζ|² < (1/λ + λ t₁) Y` whenever `λ² t₁ < 1` (`coneHeight_one_lt_iff`, likewise
  `coneHeight_two_lt_iff`, `cuspZeroHeight_lt_iff`);
* the triangle lies in `t₁|ζ|² ≤ 1` and `t₂ ≤ |ζ|²` (`tOne_mul_normSq_fermiChart_le`,
  `tTwo_le_normSq_fermiChart`): the sectors of angle `≤ π/2` at the two vertices;
* the side functions of the walls `x = W` and `x = 0` are positive multiples of
  `wallOneChart ζ = (1 + cos θ₂) + 2k cos θ₁ X - (1 - cos θ₁)|ζ|²` and
  `wallZeroChart ζ = (1 + cos θ₂)|ζ|² + 2k cos θ₂ X - k²(1 - cos θ₂)`
  (`wallOneChart_fermiChart`, `wallZeroChart_fermiChart`).
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate

namespace GC.Seifert

namespace ConeShape

variable (σ : ConeShape)

def chartScale : ℝ := 4 * Real.sqrt σ.constK / (1 + Real.cos σ.θ₁)

def tOne : ℝ := (1 - Real.cos σ.θ₁) / (1 + Real.cos σ.θ₂)

def tTwo : ℝ := (1 - Real.cos σ.θ₂) / (1 + Real.cos σ.θ₁)

def leftFoot : ℝ := σ.centre - 1 / 4

def rightFoot : ℝ := σ.centre + 1 / 4

def fermiChart (z : ℂ) : ℂ := (σ.chartScale : ℂ) * (z - σ.leftFoot) / (σ.rightFoot - z)

def wallOneChart (ζ : ℂ) : ℝ :=
  (1 + Real.cos σ.θ₂) + 2 * σ.chartScale * Real.cos σ.θ₁ * ζ.re -
    (1 - Real.cos σ.θ₁) * normSq ζ

def wallZeroChart (ζ : ℂ) : ℝ :=
  (1 + Real.cos σ.θ₂) * normSq ζ + 2 * σ.chartScale * Real.cos σ.θ₂ * ζ.re -
    σ.chartScale ^ 2 * (1 - Real.cos σ.θ₂)

theorem one_add_cos_θ₁_pos : 0 < 1 + Real.cos σ.θ₁ := by
  linarith [σ.cos_θ₁_nonneg]

theorem one_add_cos_θ₂_pos : 0 < 1 + Real.cos σ.θ₂ := by
  linarith [σ.cos_θ₂_nonneg]

theorem cos_θ₁_lt_one : Real.cos σ.θ₁ < 1 := by
  have := σ.sin_θ₁_pos
  have h := Real.sin_sq_add_cos_sq σ.θ₁
  have hc : Real.cos σ.θ₁ ≤ 1 := Real.cos_le_one _
  by_contra hh
  have h1 : Real.cos σ.θ₁ = 1 := le_antisymm hc (not_lt.1 hh)
  rw [h1] at h
  nlinarith

theorem cos_θ₂_le_one : Real.cos σ.θ₂ ≤ 1 := Real.cos_le_one _

theorem sqrt_constK_pos : 0 < Real.sqrt σ.constK := Real.sqrt_pos.2 σ.constK_pos

theorem chartScale_pos : 0 < σ.chartScale := by
  have := σ.sqrt_constK_pos
  have := σ.one_add_cos_θ₁_pos
  unfold chartScale
  positivity

theorem sqrt_constK_eq : Real.sqrt σ.constK = σ.chartScale * (1 + Real.cos σ.θ₁) / 4 := by
  have := σ.one_add_cos_θ₁_pos
  unfold chartScale
  field_simp

theorem chartScale_sq_mul :
    σ.chartScale ^ 2 * (1 + Real.cos σ.θ₁) = 1 + Real.cos σ.θ₂ := by
  have h1 := σ.one_add_cos_θ₁_pos
  have hK : Real.sqrt σ.constK ^ 2 = σ.constK := Real.sq_sqrt σ.constK_pos.le
  unfold chartScale
  rw [div_pow, mul_pow, hK, constK]
  field_simp
  ring

theorem tOne_mul_chartScale_sq :
    σ.tOne * σ.chartScale ^ 2 = (1 - Real.cos σ.θ₁) / (1 + Real.cos σ.θ₁) := by
  have h1 := σ.one_add_cos_θ₁_pos
  have h2 := σ.one_add_cos_θ₂_pos
  have e := σ.chartScale_sq_mul
  have e' : σ.chartScale ^ 2 = (1 + Real.cos σ.θ₂) / (1 + Real.cos σ.θ₁) := by
    field_simp
    linarith
  rw [tOne, e']
  field_simp

theorem tTwo_eq_chartScale_sq :
    σ.tTwo * (1 + Real.cos σ.θ₂) = σ.chartScale ^ 2 * (1 - Real.cos σ.θ₂) := by
  have h1 := σ.one_add_cos_θ₁_pos
  have e := σ.chartScale_sq_mul
  have e' : σ.chartScale ^ 2 = (1 + Real.cos σ.θ₂) / (1 + Real.cos σ.θ₁) := by
    field_simp
    linarith
  rw [tTwo, e']
  field_simp

theorem tOne_pos : 0 < σ.tOne := by
  have := σ.cos_θ₁_lt_one
  have := σ.one_add_cos_θ₂_pos
  unfold tOne
  apply div_pos <;> linarith

theorem tTwo_nonneg : 0 ≤ σ.tTwo := by
  have := σ.cos_θ₂_le_one
  have := σ.one_add_cos_θ₁_pos
  unfold tTwo
  apply div_nonneg <;> linarith

theorem vertexOne_im_sq : σ.vertexOne.im ^ 2 = σ.tOne * σ.constK := by
  have h2 := σ.one_add_cos_θ₂_pos
  have hs : Real.sin σ.θ₁ ^ 2 = 1 - Real.cos σ.θ₁ ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq σ.θ₁]
  rw [vertexOne_im, tOne, constK, div_pow, hs]
  field_simp
  ring

theorem vertexTwo_im_sq : σ.vertexTwo.im ^ 2 = σ.tTwo * σ.constK := by
  have h1 := σ.one_add_cos_θ₁_pos
  have hs : Real.sin σ.θ₂ ^ 2 = 1 - Real.cos σ.θ₂ ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq σ.θ₂]
  rw [vertexTwo_im, tTwo, constK, div_pow, hs]
  field_simp
  ring

theorem rightFoot_sub_ne {z : ℂ} (hz : 0 < z.im) : (σ.rightFoot : ℂ) - z ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem normSq_sub_rightFoot_pos {z : ℂ} (hz : 0 < z.im) : 0 < normSq (z - σ.rightFoot) := by
  apply normSq_pos.2
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem fermiChart_re (z : ℂ) :
    (σ.fermiChart z).re =
      -(σ.chartScale * σ.wallSide 2 z / normSq (z - σ.rightFoot)) := by
  have hn : normSq ((σ.rightFoot : ℂ) - z) = normSq (z - σ.rightFoot) := by
    rw [← Complex.normSq_neg, neg_sub]
  rw [fermiChart, div_re, hn]
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, sub_re, sub_im, zero_mul, sub_zero]
  rw [σ.wallSide_two_eq]
  simp only [normSq_apply, sub_re, sub_im, ofReal_re, ofReal_im, leftFoot, rightFoot]
  rcases eq_or_ne ((z.re - (σ.centre + 1 / 4)) * (z.re - (σ.centre + 1 / 4)) +
    (z.im - 0) * (z.im - 0)) 0 with h | h
  · rw [h]
    simp
  · field_simp
    ring

theorem fermiChart_im (z : ℂ) :
    (σ.fermiChart z).im = σ.chartScale * z.im / (2 * normSq (z - σ.rightFoot)) := by
  have hn : normSq ((σ.rightFoot : ℂ) - z) = normSq (z - σ.rightFoot) := by
    rw [← Complex.normSq_neg, neg_sub]
  rw [fermiChart, div_im, hn]
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, sub_re, sub_im, zero_mul, sub_zero]
  simp only [leftFoot, rightFoot]
  rcases eq_or_ne (normSq (z - ((σ.centre + 1 / 4 : ℝ) : ℂ))) 0 with h | h
  · rw [h]
    simp
  · field_simp
    ring

theorem fermiChart_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (σ.fermiChart z).im := by
  rw [fermiChart_im]
  have := σ.chartScale_pos
  have := σ.normSq_sub_rightFoot_pos hz
  positivity

theorem normSq_fermiChart (z : ℂ) :
    normSq (σ.fermiChart z) =
      σ.chartScale ^ 2 * normSq (z - σ.leftFoot) / normSq (z - σ.rightFoot) := by
  have hn : normSq ((σ.rightFoot : ℂ) - z) = normSq (z - σ.rightFoot) := by
    rw [← Complex.normSq_neg, neg_sub]
  rw [fermiChart, map_div₀, map_mul, hn, normSq_ofReal]
  ring

theorem neg_re_div_im_fermiChart {z : ℂ} (hz : 0 < z.im) :
    -(σ.fermiChart z).re / (σ.fermiChart z).im = 2 * σ.wallSide 2 z / z.im := by
  have h1 := σ.normSq_sub_rightFoot_pos hz
  have h2 := σ.chartScale_pos
  rw [fermiChart_re, fermiChart_im, neg_neg]
  field_simp

theorem sides_identity_one (z : ℂ) :
    (1 + Real.cos σ.θ₁) * normSq (z - σ.rightFoot) -
        (1 - Real.cos σ.θ₁) * normSq (z - σ.leftFoot) =
      2 * Real.cos σ.θ₁ * σ.wallSide 2 z + σ.wallSide 1 z := by
  simp only [normSq_apply, sub_re, sub_im, ofReal_re, ofReal_im, leftFoot, rightFoot, wallSide,
    width, centre]
  ring

theorem sides_identity_two (z : ℂ) :
    (1 + Real.cos σ.θ₂) * normSq (z - σ.leftFoot) -
        (1 - Real.cos σ.θ₂) * normSq (z - σ.rightFoot) =
      2 * Real.cos σ.θ₂ * σ.wallSide 2 z + σ.wallSide 0 z := by
  simp only [normSq_apply, sub_re, sub_im, ofReal_re, ofReal_im, leftFoot, rightFoot, wallSide,
    centre]
  ring

theorem tOne_mul_normSq_fermiChart_le {z : ℂ} (hz : z ∈ σ.triangle) :
    σ.tOne * normSq (σ.fermiChart z) ≤ 1 := by
  have hE := σ.normSq_sub_rightFoot_pos hz.1
  have h1 := σ.one_add_cos_θ₁_pos
  have hid := σ.sides_identity_one z
  have hw2 := hz.2 2
  have hw1 := hz.2 1
  have hc := σ.cos_θ₁_nonneg
  rw [normSq_fermiChart, ← mul_div_assoc, ← mul_assoc, tOne_mul_chartScale_sq,
    div_le_one hE, div_mul_eq_mul_div, div_le_iff₀ h1]
  nlinarith [mul_nonneg hc hw2]

theorem tTwo_le_normSq_fermiChart {z : ℂ} (hz : z ∈ σ.triangle) :
    σ.tTwo ≤ normSq (σ.fermiChart z) := by
  have hE := σ.normSq_sub_rightFoot_pos hz.1
  have h2 := σ.one_add_cos_θ₂_pos
  have hid := σ.sides_identity_two z
  have hw2 := hz.2 2
  have hw0 := hz.2 0
  have hc := σ.cos_θ₂_nonneg
  have e := σ.tTwo_eq_chartScale_sq
  rw [normSq_fermiChart, le_div_iff₀ hE]
  have key : σ.tTwo * normSq (z - σ.rightFoot) * (1 + Real.cos σ.θ₂) ≤
      σ.chartScale ^ 2 * normSq (z - σ.leftFoot) * (1 + Real.cos σ.θ₂) := by
    have hk := σ.chartScale_pos
    have : σ.tTwo * normSq (z - σ.rightFoot) * (1 + Real.cos σ.θ₂) =
        σ.chartScale ^ 2 * ((1 - Real.cos σ.θ₂) * normSq (z - σ.rightFoot)) := by
      rw [mul_right_comm, e]
      ring
    rw [this, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [mul_nonneg hc hw2]
  exact le_of_mul_le_mul_right key h2

theorem wallOneChart_fermiChart {z : ℂ} (hz : 0 < z.im) :
    σ.wallOneChart (σ.fermiChart z) =
      σ.chartScale ^ 2 * σ.wallSide 1 z / normSq (z - σ.rightFoot) := by
  have hE := σ.normSq_sub_rightFoot_pos hz
  have e := σ.chartScale_sq_mul
  have hid := σ.sides_identity_one z
  rw [wallOneChart, fermiChart_re, normSq_fermiChart, eq_div_iff hE.ne']
  field_simp
  rw [← e]
  linear_combination (σ.chartScale ^ 2) * hid

theorem wallZeroChart_fermiChart {z : ℂ} (hz : 0 < z.im) :
    σ.wallZeroChart (σ.fermiChart z) =
      σ.chartScale ^ 2 * σ.wallSide 0 z / normSq (z - σ.rightFoot) := by
  have hE := σ.normSq_sub_rightFoot_pos hz
  have hid := σ.sides_identity_two z
  rw [wallZeroChart, fermiChart_re, normSq_fermiChart, eq_div_iff hE.ne']
  field_simp
  linear_combination (σ.chartScale ^ 2) * hid

theorem chart_sum_one (z : ℂ) :
    (1 + Real.cos σ.θ₁) * normSq (z - σ.rightFoot) +
        (1 - Real.cos σ.θ₁) * normSq (z - σ.leftFoot) =
      normSq (z - σ.vertexOne) + normSq (z - conj σ.vertexOne) := by
  have hs := Real.sin_sq_add_cos_sq σ.θ₁
  simp only [normSq_apply, sub_re, sub_im, conj_re, conj_im, ofReal_re, ofReal_im, leftFoot,
    rightFoot, vertexOne_re, vertexOne_im, width, centre]
  linear_combination (-1 / 8 : ℝ) * hs

theorem chart_sum_two (z : ℂ) :
    (1 + Real.cos σ.θ₂) * normSq (z - σ.leftFoot) +
        (1 - Real.cos σ.θ₂) * normSq (z - σ.rightFoot) =
      normSq (z - σ.vertexTwo) + normSq (z - conj σ.vertexTwo) := by
  have hs := Real.sin_sq_add_cos_sq σ.θ₂
  simp only [normSq_apply, sub_re, sub_im, conj_re, conj_im, ofReal_re, ofReal_im, leftFoot,
    rightFoot, vertexTwo_re, vertexTwo_im, centre]
  linear_combination (-1 / 8 : ℝ) * hs

theorem chart_identity_one {z : ℂ} (hz : 0 < z.im) :
    2 * Real.sqrt σ.constK * z.im * (1 + σ.tOne * normSq (σ.fermiChart z)) =
      (σ.fermiChart z).im * (normSq (z - σ.vertexOne) + normSq (z - conj σ.vertexOne)) := by
  have hE := σ.normSq_sub_rightFoot_pos hz
  have h1 := σ.one_add_cos_θ₁_pos
  have hsum := σ.chart_sum_one z
  have ht := σ.tOne_mul_chartScale_sq
  have ht' : σ.tOne * σ.chartScale ^ 2 * (1 + Real.cos σ.θ₁) = 1 - Real.cos σ.θ₁ := by
    rw [ht]
    field_simp
  rw [normSq_fermiChart, fermiChart_im, σ.sqrt_constK_eq, ← hsum]
  field_simp
  linear_combination (4 * σ.chartScale * normSq (z - σ.leftFoot)) * ht'

theorem chart_identity_two {z : ℂ} (hz : 0 < z.im) :
    2 * Real.sqrt σ.constK * z.im * (normSq (σ.fermiChart z) + σ.tTwo) =
      (σ.fermiChart z).im * (normSq (z - σ.vertexTwo) + normSq (z - conj σ.vertexTwo)) := by
  have hE := σ.normSq_sub_rightFoot_pos hz
  have h1 := σ.one_add_cos_θ₁_pos
  have hsum := σ.chart_sum_two z
  have hk := σ.chartScale_sq_mul
  have ht : σ.tTwo * (1 + Real.cos σ.θ₁) = 1 - Real.cos σ.θ₂ := by
    rw [tTwo]
    field_simp
  rw [normSq_fermiChart, fermiChart_im, σ.sqrt_constK_eq, ← hsum, ← hk, ← ht]
  field_simp
  ring

theorem height_chart_aux {r y a Np Nm : ℝ} (hr : r < 1) (h1 : r ^ 2 * Np = Nm)
    (h2 : Np = Nm + 4 * y * a) :
    a * (1 + r) / (1 - r) * (Nm + Np) =
      2 * y * ((a * (1 + r) / (1 - r)) ^ 2 + a ^ 2) := by
  have h0 : (1 - r) ≠ 0 := by linarith
  subst h1
  field_simp
  linear_combination (a * (1 + r ^ 2)) * h2

theorem coneHeight_chart {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) :
    coneHeight v z * (normSq (z - v) + normSq (z - conj v)) =
      2 * z.im * (coneHeight v z ^ 2 + v.im ^ 2) := by
  have hr1 := norm_coneDisc_lt_one hv hz
  have hNp := normSq_sub_conj_pos hv hz
  have h1 : ‖coneDisc v z‖ ^ 2 * normSq (z - conj v) = normSq (z - v) := by
    rw [Complex.sq_norm, normSq_coneDisc]
    field_simp
  have h2 := normSq_sub_conj_eq v z
  exact height_chart_aux hr1 h1 h2

theorem coneHeight_ge {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) : v.im ≤ coneHeight v z := by
  have hr1 := norm_coneDisc_lt_one hv hz
  have hr0 := norm_nonneg (coneDisc v z)
  rw [coneHeight, le_div_iff₀ (by linarith)]
  nlinarith

theorem sqrt_constK_mul_coneHeight_one {z : ℂ} (hz : 0 < z.im) :
    Real.sqrt σ.constK * coneHeight σ.vertexOne z * (1 + σ.tOne * normSq (σ.fermiChart z)) =
      (σ.fermiChart z).im * (coneHeight σ.vertexOne z ^ 2 + σ.vertexOne.im ^ 2) := by
  have hA := σ.chart_identity_one hz
  have hB := coneHeight_chart σ.vertexOne_im_pos hz
  have hy := hz
  have h2 : 2 * z.im ≠ 0 := by positivity
  apply mul_left_cancel₀ h2
  linear_combination coneHeight σ.vertexOne z * hA + (σ.fermiChart z).im * hB

theorem sqrt_constK_mul_coneHeight_two (hθ : 0 < σ.θ₂) {z : ℂ} (hz : 0 < z.im) :
    Real.sqrt σ.constK * coneHeight σ.vertexTwo z * (normSq (σ.fermiChart z) + σ.tTwo) =
      (σ.fermiChart z).im * (coneHeight σ.vertexTwo z ^ 2 + σ.vertexTwo.im ^ 2) := by
  have hv : 0 < σ.vertexTwo.im := by
    rw [vertexTwo_im]
    have := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [σ.θ₂_le, Real.pi_pos])
    positivity
  have hA := σ.chart_identity_two hz
  have hB := coneHeight_chart hv hz
  have h2 : 2 * z.im ≠ 0 := by positivity
  apply mul_left_cancel₀ h2
  linear_combination coneHeight σ.vertexTwo z * hA + (σ.fermiChart z).im * hB

theorem sqrt_constK_mul_normSq_fermiChart (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im) :
    Real.sqrt σ.constK * normSq (σ.fermiChart z) = (σ.fermiChart z).im * cuspZeroHeight z := by
  have hA := σ.chart_identity_two hz
  have ht : σ.tTwo = 0 := by simp [tTwo, hθ]
  have hv : σ.vertexTwo = 0 := σ.cusp_vertexTwo hθ
  rw [ht, hv, add_zero, map_zero, sub_zero, ← two_mul] at hA
  rw [cuspZeroHeight]
  field_simp
  linear_combination hA / 2

theorem lt_iff_of_height_identity {K η y Y t lam N : ℝ} (hK : 0 < K) (hη : 0 < η) (hY : 0 < Y)
    (hlam : 0 < lam) (hy : y ^ 2 = t * K) (hy0 : 0 < y) (hyη : y ≤ η) (ht : 0 ≤ t)
    (hlamt : lam ^ 2 * t < 1)
    (hid : Real.sqrt K * η * N = Y * (η ^ 2 + y ^ 2)) :
    η < Real.sqrt K / lam ↔ N < (1 / lam + lam * t) * Y := by
  have hs := Real.sqrt_pos.2 hK
  have hss : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
  have hlow : lam * t * Real.sqrt K < η := by
    have h1 : (lam * t * Real.sqrt K) ^ 2 < y ^ 2 := by
      rw [hy, mul_pow, mul_pow, hss]
      have : 0 < t * K := by
        rcases ht.lt_or_eq with h | h
        · positivity
        · rw [← h] at hy
          nlinarith
      nlinarith
    have h2 : lam * t * Real.sqrt K < y := by
      by_contra hc
      have hc' : y ≤ lam * t * Real.sqrt K := not_lt.1 hc
      nlinarith
    linarith
  have key : Real.sqrt K * η * (N - (1 / lam + lam * t) * Y) =
      Y * (η - Real.sqrt K / lam) * (η - lam * t * Real.sqrt K) := by
    rw [mul_sub, hid, hy]
    field_simp
    linear_combination (-(t * lam)) * hss
  constructor
  · intro h
    have : Real.sqrt K * η * (N - (1 / lam + lam * t) * Y) < 0 := by
      rw [key]
      apply mul_neg_of_neg_of_pos _ (by linarith)
      exact mul_neg_of_pos_of_neg hY (by linarith)
    have hp : 0 < Real.sqrt K * η := by positivity
    by_contra hc
    have : 0 ≤ Real.sqrt K * η * (N - (1 / lam + lam * t) * Y) :=
      mul_nonneg hp.le (by linarith [not_lt.1 hc])
    linarith
  · intro h
    have hp : 0 < Real.sqrt K * η := by positivity
    have hneg : Real.sqrt K * η * (N - (1 / lam + lam * t) * Y) < 0 :=
      mul_neg_of_pos_of_neg hp (by linarith)
    rw [key] at hneg
    by_contra hc
    have : 0 ≤ Y * (η - Real.sqrt K / lam) * (η - lam * t * Real.sqrt K) := by
      apply mul_nonneg (mul_nonneg hY.le (by linarith [not_lt.1 hc])) (by linarith)
    linarith

theorem coneHeight_one_lt_iff {lam : ℝ} (hlam : 0 < lam) (hlamt : lam ^ 2 * σ.tOne < 1) {z : ℂ}
    (hz : 0 < z.im) :
    coneHeight σ.vertexOne z < Real.sqrt σ.constK / lam ↔
      1 + σ.tOne * normSq (σ.fermiChart z) < (1 / lam + lam * σ.tOne) * (σ.fermiChart z).im :=
  lt_iff_of_height_identity σ.constK_pos (coneHeight_pos σ.vertexOne_im_pos hz)
    (σ.fermiChart_im_pos hz) hlam σ.vertexOne_im_sq σ.vertexOne_im_pos
    (coneHeight_ge σ.vertexOne_im_pos hz) σ.tOne_pos.le hlamt (σ.sqrt_constK_mul_coneHeight_one hz)

theorem coneHeight_two_lt_iff (hθ : 0 < σ.θ₂) {lam : ℝ} (hlam : 0 < lam)
    (hlamt : lam ^ 2 * σ.tTwo < 1) {z : ℂ} (hz : 0 < z.im) :
    coneHeight σ.vertexTwo z < Real.sqrt σ.constK / lam ↔
      normSq (σ.fermiChart z) + σ.tTwo < (1 / lam + lam * σ.tTwo) * (σ.fermiChart z).im := by
  have hv : 0 < σ.vertexTwo.im := by
    rw [vertexTwo_im]
    have := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [σ.θ₂_le, Real.pi_pos])
    positivity
  exact lt_iff_of_height_identity σ.constK_pos (coneHeight_pos hv hz)
    (σ.fermiChart_im_pos hz) hlam σ.vertexTwo_im_sq hv (coneHeight_ge hv hz) σ.tTwo_nonneg hlamt
    (σ.sqrt_constK_mul_coneHeight_two hθ hz)

theorem cuspZeroHeight_lt_iff (hθ : σ.θ₂ = 0) {lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 0 < z.im) :
    cuspZeroHeight z < Real.sqrt σ.constK / lam ↔
      normSq (σ.fermiChart z) < 1 / lam * (σ.fermiChart z).im := by
  have hid := σ.sqrt_constK_mul_normSq_fermiChart hθ hz
  have hs := σ.sqrt_constK_pos
  have hY := σ.fermiChart_im_pos hz
  rw [lt_div_iff₀ hlam, one_div, inv_mul_eq_div, lt_div_iff₀ hlam]
  constructor
  · intro h
    have h' : √σ.constK * (normSq (σ.fermiChart z) * lam) < √σ.constK * (σ.fermiChart z).im :=
      calc √σ.constK * (normSq (σ.fermiChart z) * lam)
          = (σ.fermiChart z).im * (cuspZeroHeight z * lam) := by rw [← mul_assoc, hid]; ring
        _ < (σ.fermiChart z).im * √σ.constK := mul_lt_mul_of_pos_left h hY
        _ = √σ.constK * (σ.fermiChart z).im := mul_comm _ _
    exact lt_of_mul_lt_mul_left h' hs.le
  · intro h
    have h' : (σ.fermiChart z).im * (cuspZeroHeight z * lam) < (σ.fermiChart z).im * √σ.constK :=
      calc (σ.fermiChart z).im * (cuspZeroHeight z * lam)
          = √σ.constK * (normSq (σ.fermiChart z) * lam) := by rw [← mul_assoc, ← hid, mul_assoc]
        _ < √σ.constK * (σ.fermiChart z).im := mul_lt_mul_of_pos_left h hs
        _ = (σ.fermiChart z).im * √σ.constK := mul_comm _ _
    exact lt_of_mul_lt_mul_left h' hY.le

end ConeShape

end GC.Seifert
