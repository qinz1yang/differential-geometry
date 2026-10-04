import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldDisc
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldProfile

/-!
# The triangles of the cone fold

Lane A4, tier 1 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §2).
A `ConeShape` is a pair of angles `θ₁ ∈ (0, π/2]`, `θ₂ ∈ [0, π/2]` with `θ₁ + θ₂ < π`; for the
orders of the filled block, `θ₁ = π/p₁` and `θ₂ = π/p₂` (`θ₂ = 0` for a free port, i.e. a cusp).
With `W = (cos θ₁ + cos θ₂)/4` and `c = cos θ₂ / 4` the triangle is
`{0 ≤ x ≤ W, |z - c| ≥ 1/4}` in the upper half-plane, with walls `x = 0`, `x = W` and the circle
`|z - c| = 1/4`, vertices `v₁ = W + i sin θ₁/4 = c + e^{iθ₁}/4` (angle `θ₁`),
`v₂ = i sin θ₂/4 = c + e^{i(π - θ₂)}/4` (angle `θ₂`; the cusp `0` when `θ₂ = 0`) and the cusp `∞`.
The case `θ₁ = θ₂ = 0` excluded, `θ₁ = π/p, θ₂ = 0` is the `(p, ⊤, ⊤)` shape and
`(θ₁, θ₂) → (0, 0)` would be K16f's ideal triangle.

The wall reflections `refl i` are involutions of the upper half-plane fixing their walls and
reversing the side functions `wallSide i`. In the disc coordinate at `v₁` the reflection in
`x = W` is `ω ↦ ω̄` and the reflection in the circle is `ω ↦ e^{2iθ₁} ω̄`; at `v₂` the reflection in
`x = 0` is `ω ↦ ω̄` and the circle gives `e^{2i(π - θ₂)}`. The side functions are, up to positive
factors, the imaginary parts of the disc coordinate and of its rotation by `e^{-iθ₁}`.
The constant `constK = (1 + cos θ₁)(1 + cos θ₂)/16` is the product of the virtual heights on the
circle wall: `|v₁|²` for the cusp (`constK_eq_normSq`), and `Im v₁ Im v₂ (1 + t)/(1 - t)` with
`t = cos((θ₁+θ₂)/2)/cos((θ₁-θ₂)/2) = |coneDisc v₁ v₂|` for two cones (`constK_eq_cones`,
`coneDisc_vertexOne_vertexTwo`).
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate

namespace GC.Seifert

structure ConeShape where
  θ₁ : ℝ
  θ₂ : ℝ
  θ₁_pos : 0 < θ₁
  θ₁_le : θ₁ ≤ Real.pi / 2
  θ₂_nonneg : 0 ≤ θ₂
  θ₂_le : θ₂ ≤ Real.pi / 2
  sum_lt : θ₁ + θ₂ < Real.pi

namespace ConeShape

variable (σ : ConeShape)

def width : ℝ := (Real.cos σ.θ₁ + Real.cos σ.θ₂) / 4

def centre : ℝ := Real.cos σ.θ₂ / 4

def vertexOne : ℂ := ⟨σ.width, Real.sin σ.θ₁ / 4⟩

def vertexTwo : ℂ := ⟨0, Real.sin σ.θ₂ / 4⟩

def constK : ℝ := (1 + Real.cos σ.θ₁) * (1 + Real.cos σ.θ₂) / 16

def wallSide : Fin 3 → ℂ → ℝ
  | 0 => fun z => z.re
  | 1 => fun z => σ.width - z.re
  | 2 => fun z => (z.re - σ.centre) ^ 2 + z.im ^ 2 - 1 / 16

def triangle : Set ℂ := {z | 0 < z.im ∧ ∀ i, 0 ≤ σ.wallSide i z}

def refl : Fin 3 → ℂ → ℂ
  | 0 => fun z => -conj z
  | 1 => fun z => 2 * (σ.width : ℂ) - conj z
  | 2 => fun z => (σ.centre : ℂ) + 1 / 16 / (conj z - σ.centre)

theorem cos_θ₁_nonneg : 0 ≤ Real.cos σ.θ₁ :=
  Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [σ.θ₁_pos, Real.pi_pos]) σ.θ₁_le

theorem cos_θ₂_nonneg : 0 ≤ Real.cos σ.θ₂ :=
  Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [σ.θ₂_nonneg, Real.pi_pos]) σ.θ₂_le

theorem sin_θ₁_pos : 0 < Real.sin σ.θ₁ :=
  Real.sin_pos_of_pos_of_lt_pi σ.θ₁_pos (by linarith [σ.θ₁_le, Real.pi_pos])

theorem sin_θ₂_nonneg : 0 ≤ Real.sin σ.θ₂ :=
  Real.sin_nonneg_of_nonneg_of_le_pi σ.θ₂_nonneg (by linarith [σ.θ₂_le, Real.pi_pos])

theorem cos_add_cos_pos : 0 < Real.cos σ.θ₁ + Real.cos σ.θ₂ := by
  rw [Real.cos_add_cos]
  have h1 : 0 < Real.cos ((σ.θ₁ + σ.θ₂) / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [σ.θ₁_pos, σ.θ₂_nonneg, σ.sum_lt]
  have h2 : 0 < Real.cos ((σ.θ₁ - σ.θ₂) / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [σ.θ₁_pos, σ.θ₁_le, σ.θ₂_nonneg, σ.θ₂_le]
  positivity

theorem width_pos : 0 < σ.width := by
  have := σ.cos_add_cos_pos
  unfold width
  positivity

theorem constK_pos : 0 < σ.constK := by
  have := σ.cos_θ₁_nonneg
  have := σ.cos_θ₂_nonneg
  unfold constK
  positivity

theorem vertexOne_re : σ.vertexOne.re = σ.width := rfl

theorem vertexOne_im : σ.vertexOne.im = Real.sin σ.θ₁ / 4 := rfl

theorem vertexTwo_re : σ.vertexTwo.re = 0 := rfl

theorem vertexTwo_im : σ.vertexTwo.im = Real.sin σ.θ₂ / 4 := rfl

theorem vertexOne_im_pos : 0 < σ.vertexOne.im := by
  have := σ.sin_θ₁_pos
  rw [vertexOne_im]
  positivity

theorem exp_mul_I_eq (θ : ℝ) : exp ((θ : ℂ) * I) = ⟨Real.cos θ, Real.sin θ⟩ := by
  apply Complex.ext
  · simp [Complex.exp_ofReal_mul_I_re]
  · simp [Complex.exp_ofReal_mul_I_im]

theorem vertexOne_eq : σ.vertexOne = (σ.centre : ℂ) + exp ((σ.θ₁ : ℂ) * I) / 4 := by
  apply Complex.ext
  · simp only [vertexOne, add_re, ofReal_re, div_ofNat_re, Complex.exp_ofReal_mul_I_re]
    unfold width centre
    ring
  · simp [vertexOne, Complex.exp_ofReal_mul_I_im]

theorem vertexTwo_eq :
    σ.vertexTwo = (σ.centre : ℂ) + exp (((Real.pi - σ.θ₂ : ℝ) : ℂ) * I) / 4 := by
  apply Complex.ext
  · simp only [vertexTwo, centre, add_re, ofReal_re, div_ofNat_re, Complex.exp_ofReal_mul_I_re,
      Real.cos_pi_sub]
    ring
  · simp only [vertexTwo, add_im, ofReal_im, div_ofNat_im, Complex.exp_ofReal_mul_I_im,
      Real.sin_pi_sub]
    ring

theorem refl_one_eq (z : ℂ) : σ.refl 1 z = 2 * (σ.vertexOne.re : ℂ) - conj z := rfl

theorem refl_zero_eq (z : ℂ) : σ.refl 0 z = 2 * (σ.vertexTwo.re : ℂ) - conj z := by
  simp [refl, vertexTwo_re]

theorem coneDisc_vertexOne_refl_one (z : ℂ) :
    coneDisc σ.vertexOne (σ.refl 1 z) = conj (coneDisc σ.vertexOne z) := by
  rw [refl_one_eq, coneDisc_vertical]

theorem coneDisc_vertexTwo_refl_zero (z : ℂ) :
    coneDisc σ.vertexTwo (σ.refl 0 z) = conj (coneDisc σ.vertexTwo z) := by
  rw [refl_zero_eq, coneDisc_vertical]

theorem coneDisc_vertexOne_refl_two {z : ℂ} (hz : z ≠ σ.centre) :
    coneDisc σ.vertexOne (σ.refl 2 z) =
      exp (2 * σ.θ₁ * I) * conj (coneDisc σ.vertexOne z) := by
  rw [vertexOne_eq]
  exact coneDisc_circle hz

theorem coneDisc_vertexTwo_refl_two {z : ℂ} (hz : z ≠ σ.centre) :
    coneDisc σ.vertexTwo (σ.refl 2 z) =
      exp (2 * ((Real.pi - σ.θ₂ : ℝ) : ℂ) * I) * conj (coneDisc σ.vertexTwo z) := by
  rw [vertexTwo_eq]
  exact coneDisc_circle hz

theorem im_coneDisc_vertexOne_mul (z : ℂ) :
    (coneDisc σ.vertexOne z).im * normSq (z - conj σ.vertexOne) =
      2 * σ.vertexOne.im * σ.wallSide 1 z := by
  rw [im_coneDisc_mul]
  rfl

theorem im_coneDisc_vertexTwo_mul (z : ℂ) :
    (coneDisc σ.vertexTwo z).im * normSq (z - conj σ.vertexTwo) =
      -(2 * σ.vertexTwo.im * σ.wallSide 0 z) := by
  rw [im_coneDisc_mul, vertexTwo_re]
  simp [wallSide]

theorem im_rot_coneDisc_vertexOne_mul (z : ℂ) :
    (exp (-(σ.θ₁ * I)) * coneDisc σ.vertexOne z).im * normSq (z - conj σ.vertexOne) =
      -(Real.sin σ.θ₁ * σ.wallSide 2 z) := by
  rw [vertexOne_eq, im_rot_coneDisc_mul]
  simp [wallSide]

theorem im_rot_coneDisc_vertexTwo_mul (z : ℂ) :
    (exp (-(((Real.pi - σ.θ₂ : ℝ) : ℂ) * I)) * coneDisc σ.vertexTwo z).im *
        normSq (z - conj σ.vertexTwo) =
      -(Real.sin σ.θ₂ * σ.wallSide 2 z) := by
  rw [vertexTwo_eq, im_rot_coneDisc_mul, Real.sin_pi_sub]
  simp [wallSide]

theorem centre_ne {z : ℂ} (hz : 0 < z.im) : z - σ.centre ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem conj_centre_ne {z : ℂ} (hz : 0 < z.im) : conj z - σ.centre ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem refl_two_sub (z : ℂ) : σ.refl 2 z - σ.centre = 1 / 16 / (conj z - σ.centre) := by
  simp [refl]

theorem refl_two_im {z : ℂ} (hz : 0 < z.im) :
    (σ.refl 2 z).im = z.im / (16 * normSq (z - σ.centre)) := by
  have h1 := σ.conj_centre_ne hz
  have hc : normSq (conj z - σ.centre) = normSq (z - σ.centre) := by
    rw [show conj z - σ.centre = conj (z - σ.centre) by simp, Complex.normSq_conj]
  have hn : normSq (z - σ.centre) ≠ 0 := normSq_eq_zero.not.2 (σ.centre_ne hz)
  have e : (σ.refl 2 z).im = (σ.refl 2 z - σ.centre).im := by simp
  rw [e, refl_two_sub, div_im, hc]
  simp
  field_simp

theorem refl_im_pos {z : ℂ} (hz : 0 < z.im) (i : Fin 3) : 0 < (σ.refl i z).im := by
  fin_cases i
  · simpa [refl] using hz
  · simpa [refl] using hz
  · change 0 < (σ.refl 2 z).im
    rw [σ.refl_two_im hz]
    have := normSq_pos.2 (σ.centre_ne hz)
    positivity

theorem refl_refl {z : ℂ} (hz : 0 < z.im) (i : Fin 3) : σ.refl i (σ.refl i z) = z := by
  fin_cases i
  · simp [refl]
  · simp [refl, map_ofNat]
  · change σ.refl 2 (σ.refl 2 z) = z
    have h2 := σ.centre_ne hz
    have e : σ.refl 2 (σ.refl 2 z) - σ.centre = z - σ.centre := by
      rw [refl_two_sub, show conj (σ.refl 2 z) - σ.centre = conj (σ.refl 2 z - σ.centre) by simp,
        refl_two_sub, map_div₀, map_div₀, map_sub, Complex.conj_conj, Complex.conj_ofReal]
      simp only [map_one, map_ofNat]
      field_simp
    exact sub_left_injective e

theorem wallSide_two_eq (z : ℂ) : σ.wallSide 2 z = normSq (z - σ.centre) - 1 / 16 := by
  simp [wallSide, normSq_apply]
  ring

theorem refl_of_wallSide_eq_zero {z : ℂ} (hz : 0 < z.im) {i : Fin 3}
    (hw : σ.wallSide i z = 0) : σ.refl i z = z := by
  fin_cases i
  · apply Complex.ext <;> simp_all [refl, wallSide]
  · apply Complex.ext
    · simp only [wallSide] at hw
      simp [refl]
      linarith
    · simp [refl]
  · change σ.refl 2 z = z
    have hw' : normSq (z - σ.centre) = 1 / 16 := by
      have := σ.wallSide_two_eq z
      simp only [Fin.reduceFinMk] at hw
      linarith
    have h1 := σ.conj_centre_ne hz
    have key : (1 / 16 : ℂ) = (conj z - σ.centre) * (z - σ.centre) := by
      rw [show conj z - σ.centre = conj (z - σ.centre) by simp, mul_comm, Complex.mul_conj, hw']
      norm_num
    have e : σ.refl 2 z - σ.centre = z - σ.centre := by
      rw [refl_two_sub, key, mul_div_cancel_left₀ _ h1]
    exact sub_left_injective e

theorem wallSide_refl_zero (z : ℂ) : σ.wallSide 0 (σ.refl 0 z) = -σ.wallSide 0 z := by
  simp [wallSide, refl]

theorem wallSide_refl_one (z : ℂ) : σ.wallSide 1 (σ.refl 1 z) = -σ.wallSide 1 z := by
  simp [wallSide, refl]
  ring

theorem wallSide_refl_two {z : ℂ} (hz : 0 < z.im) :
    σ.wallSide 2 (σ.refl 2 z) = -σ.wallSide 2 z / (16 * normSq (z - σ.centre)) := by
  have hc : normSq (conj z - σ.centre) = normSq (z - σ.centre) := by
    rw [show conj z - σ.centre = conj (z - σ.centre) by simp, Complex.normSq_conj]
  have hn : normSq (z - σ.centre) ≠ 0 := normSq_eq_zero.not.2 (σ.centre_ne hz)
  rw [wallSide_two_eq, wallSide_two_eq, refl_two_sub, map_div₀, hc]
  simp
  field_simp

theorem cusp_centre (h : σ.θ₂ = 0) : σ.centre = 1 / 4 := by
  simp [centre, h]

theorem cusp_vertexTwo (h : σ.θ₂ = 0) : σ.vertexTwo = 0 := by
  apply Complex.ext <;> simp [vertexTwo, h]

theorem constK_eq_normSq (h : σ.θ₂ = 0) : σ.constK = normSq σ.vertexOne := by
  rw [normSq_apply, vertexOne_re, vertexOne_im, width, constK, h, Real.cos_zero]
  have hs := Real.sin_sq_add_cos_sq σ.θ₁
  linear_combination (-1 / 16) * hs

theorem constK_eq_width (h : σ.θ₂ = 0) : σ.constK = σ.width / 2 := by
  rw [width, constK, h, Real.cos_zero]
  ring

theorem conj_div_vertexOne (h : σ.θ₂ = 0) :
    conj σ.vertexOne / σ.vertexOne = exp (-(σ.θ₁ * I)) := by
  have hv : σ.vertexOne ≠ 0 := fun h' => by
    have := σ.vertexOne_im_pos
    rw [h'] at this
    simp at this
  rw [div_eq_iff hv, vertexOne_eq, cusp_centre σ h, map_add, map_div₀, ← Complex.exp_conj,
    Complex.conj_ofReal, map_ofNat]
  rw [show conj ((σ.θ₁ : ℂ) * I) = -((σ.θ₁ : ℂ) * I) by simp, mul_add, mul_div_assoc',
    ← Complex.exp_add]
  push_cast
  simp only [neg_add_cancel, Complex.exp_zero]
  ring

theorem cos_half_diff_pos : 0 < Real.cos ((σ.θ₁ - σ.θ₂) / 2) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [σ.θ₁_pos, σ.θ₁_le, σ.θ₂_nonneg, σ.θ₂_le]

theorem cos_half_sum_pos : 0 < Real.cos ((σ.θ₁ + σ.θ₂) / 2) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [σ.θ₁_pos, σ.θ₂_nonneg, σ.sum_lt]

theorem ofReal_cos_eq_exp (x : ℝ) :
    (Real.cos x : ℂ) = (exp (x * I) + (exp (x * I))⁻¹) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos, ← Complex.exp_neg]
  congr 3
  ring

theorem coneDisc_vertexOne_vertexTwo (h : 0 < σ.θ₂) :
    coneDisc σ.vertexOne σ.vertexTwo =
      ((Real.cos ((σ.θ₁ + σ.θ₂) / 2) / Real.cos ((σ.θ₁ - σ.θ₂) / 2) : ℝ) : ℂ) *
        exp (σ.θ₁ * I) := by
  set E := exp (((σ.θ₁ / 2 : ℝ) : ℂ) * I) with hE
  set F := exp (((σ.θ₂ / 2 : ℝ) : ℂ) * I) with hF
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  have hF0 : F ≠ 0 := Complex.exp_ne_zero _
  have h1 : exp ((σ.θ₁ : ℂ) * I) = E * E := by
    rw [hE, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : exp (((Real.pi - σ.θ₂ : ℝ) : ℂ) * I) = -(F * F)⁻¹ := by
    rw [hF, ← Complex.exp_add, ← Complex.exp_neg, show ((Real.pi - σ.θ₂ : ℝ) : ℂ) * I =
      Real.pi * I + -(((σ.θ₂ / 2 : ℝ) : ℂ) * I + ((σ.θ₂ / 2 : ℝ) : ℂ) * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have h3 : conj (exp ((σ.θ₁ : ℂ) * I)) = (E * E)⁻¹ := by
    rw [← Complex.exp_conj, show conj ((σ.θ₁ : ℂ) * I) = -((σ.θ₁ : ℂ) * I) by simp,
      Complex.exp_neg, h1]
  have hEF : exp ((((σ.θ₁ + σ.θ₂) / 2 : ℝ) : ℂ) * I) = E * F := by
    rw [hE, hF, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hEF' : exp ((((σ.θ₁ - σ.θ₂) / 2 : ℝ) : ℂ) * I) = E * F⁻¹ := by
    rw [hE, hF, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hp : (Real.cos ((σ.θ₁ + σ.θ₂) / 2) : ℂ) = (E * F + (E * F)⁻¹) / 2 := by
    rw [ofReal_cos_eq_exp, hEF]
  have hm : (Real.cos ((σ.θ₁ - σ.θ₂) / 2) : ℂ) = (E * F⁻¹ + (E * F⁻¹)⁻¹) / 2 := by
    rw [ofReal_cos_eq_exp, hEF']
  have hm0 : (E * F⁻¹ + (E * F⁻¹)⁻¹) / 2 ≠ 0 := by
    rw [← hm]
    exact Complex.ofReal_ne_zero.2 σ.cos_half_diff_pos.ne'
  have hd : σ.vertexTwo - conj σ.vertexOne ≠ 0 :=
    sub_conj_ne_zero σ.vertexOne_im_pos (by
      rw [vertexTwo_im]
      have := Real.sin_pos_of_pos_of_lt_pi h (by linarith [σ.θ₂_le, Real.pi_pos])
      positivity)
  rw [coneDisc, div_eq_iff hd, Complex.ofReal_div]
  rw [vertexTwo_eq, vertexOne_eq, map_add, Complex.conj_ofReal, map_div₀, map_ofNat, h3, h2, h1]
  rw [hp, hm, div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hm0]
  field_simp
  ring

theorem constK_eq_cones (h : 0 < σ.θ₂) :
    σ.constK = σ.vertexOne.im * σ.vertexTwo.im *
      (1 + Real.cos ((σ.θ₁ + σ.θ₂) / 2) / Real.cos ((σ.θ₁ - σ.θ₂) / 2)) /
      (1 - Real.cos ((σ.θ₁ + σ.θ₂) / 2) / Real.cos ((σ.θ₁ - σ.θ₂) / 2)) := by
  have hm := σ.cos_half_diff_pos
  have hsa : 0 < Real.sin (σ.θ₁ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [σ.θ₁_pos]) (by linarith [σ.θ₁_le, Real.pi_pos])
  have hsb : 0 < Real.sin (σ.θ₂ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [σ.θ₂_le, Real.pi_pos])
  have e1 : σ.θ₁ = 2 * (σ.θ₁ / 2) := by ring
  have e2 : σ.θ₂ = 2 * (σ.θ₂ / 2) := by ring
  have hp : Real.cos ((σ.θ₁ + σ.θ₂) / 2) = Real.cos (σ.θ₁ / 2) * Real.cos (σ.θ₂ / 2) -
      Real.sin (σ.θ₁ / 2) * Real.sin (σ.θ₂ / 2) := by
    rw [← Real.cos_add]
    congr 1
    ring
  have hq : Real.cos ((σ.θ₁ - σ.θ₂) / 2) = Real.cos (σ.θ₁ / 2) * Real.cos (σ.θ₂ / 2) +
      Real.sin (σ.θ₁ / 2) * Real.sin (σ.θ₂ / 2) := by
    rw [← Real.cos_sub]
    congr 1
    ring
  have hdiff : Real.cos ((σ.θ₁ - σ.θ₂) / 2) - Real.cos ((σ.θ₁ + σ.θ₂) / 2) ≠ 0 := by
    rw [hp, hq]
    have : 0 < Real.sin (σ.θ₁ / 2) * Real.sin (σ.θ₂ / 2) := by positivity
    linarith
  have hc1 : Real.cos σ.θ₁ = 2 * Real.cos (σ.θ₁ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul, ← e1]
  have hc2 : Real.cos σ.θ₂ = 2 * Real.cos (σ.θ₂ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul, ← e2]
  have hs1 : Real.sin σ.θ₁ = 2 * Real.sin (σ.θ₁ / 2) * Real.cos (σ.θ₁ / 2) := by
    rw [← Real.sin_two_mul, ← e1]
  have hs2 : Real.sin σ.θ₂ = 2 * Real.sin (σ.θ₂ / 2) * Real.cos (σ.θ₂ / 2) := by
    rw [← Real.sin_two_mul, ← e2]
  rw [constK, vertexOne_im, vertexTwo_im, one_add_div hm.ne', one_sub_div hm.ne']
  field_simp
  rw [hp, hq, hc1, hc2, hs1, hs2]
  ring

end ConeShape

end GC.Seifert
