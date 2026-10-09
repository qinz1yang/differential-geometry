import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases

/-!
# The flat triangles of the compact fold

Lane CF, tier 1, curvature `0` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §1–2). A `EuclidShape` is a triple of cone orders
`pᵢ ≥ 2` with `∑ 1/pᵢ = 1`, i.e. `(2,3,6)`, `(2,4,4)`, `(3,3,3)` in some order
(`orders_mem`; the instances `shape236`, `shape244`, `shape333`); the angles are `θᵢ = π/pᵢ`.
The triangle has the vertex `v₃ = 0` (the cone on the outer hole), `v₂ = sin θ₁` on
the positive real axis and `v₁ = sin θ₂ e^{iθ₃}`, so its sides have lengths `sin θₖ` opposite to
`vₖ` (law of sines with circumdiameter one) and `v₂ - v₁ = sin θ₃ e^{-iθ₂}`. Wall `0` is
`[v₃, v₂]`, wall `1` is `[v₃, v₁]`, wall `2` is `[v₁, v₂]`; the side functions `wallSide i` are
nonnegative on the triangle, vanish on the lines of the walls and are reversed by the reflections
`refl i` (`z̄`, `e^{2iθ₃} z̄`, `v₂ + e^{-2iθ₂} conj (z - v₂)`), which are isometric involutions
fixing the two vertices of their wall.

The rotated disc coordinates `rotOne`, `rotTwo`, `rotThree` put the vertex at `0`, the first wall
of the sector (`1`, `2`, `0` respectively) on the positive axis and the second at angle `θⱼ`; in
them the two reflections through the vertex are `ω ↦ ω̄` and `ω ↦ e^{2iθⱼ} ω̄`. Consequently the
branched apex models `3/2 + rotOne^{p₁}/2`, `-3/2 + rotTwo^{p₂}/2` and the outer germ
`compactOuterGerm p₃ z = -(7/2 - ‖z‖^{p₃}/2) (z̄/‖z‖)^{p₃}` satisfy the wall identities
`f ∘ refl = conj ∘ f`. Barycentric coordinates (`eq_bary`, `bary_sum`) bound the triangle:
it lies in the unit disc, at distance at most `1` from each vertex, and the cofactors of the
segment identities are positive on it off the two vertices of their wall.

The canonical radii `radOne`, `radTwo`, `radThree` are the tangent lengths of the incircle
(`radᵢ + radⱼ = |vᵢ vⱼ|`), and `canon j z = ‖z - vⱼ‖ - radⱼ`. On wall `ij` one has
`canon i + canon j = 0`, and everywhere `canon i + canon j = Y² Q` (`segment_identity`) with `Y`
the side function of that wall and an explicit cofactor `Q`, positive off the two rays beyond the
vertices (`canon_add_canon_zero_three`, `canon_add_canon_one_three`, `canon_add_canon_one_two`).
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate

namespace GC.Seifert

def compactOuterGerm (p : ℕ) (z : ℂ) : ℂ :=
  -(((7 / 2 - ‖z‖ ^ p / 2 : ℝ) : ℂ) * (conj z / ‖z‖) ^ p)

theorem compactOuterGerm_conj (p : ℕ) (z : ℂ) :
    compactOuterGerm p (conj z) = conj (compactOuterGerm p z) := by
  simp only [compactOuterGerm, Complex.norm_conj, Complex.conj_conj, map_neg, map_mul,
    Complex.conj_ofReal, map_pow, map_div₀]

structure EuclidShape where
  p₁ : ℕ
  p₂ : ℕ
  p₃ : ℕ
  two_le_p₁ : 2 ≤ p₁
  two_le_p₂ : 2 ≤ p₂
  two_le_p₃ : 2 ≤ p₃
  sum_inv : (1 / p₁ + 1 / p₂ + 1 / p₃ : ℝ) = 1

namespace EuclidShape

variable (σ : EuclidShape)

def θ₁ : ℝ := Real.pi / σ.p₁

def θ₂ : ℝ := Real.pi / σ.p₂

def θ₃ : ℝ := Real.pi / σ.p₃

theorem p_pos_aux {p : ℕ} (hp : 2 ≤ p) : (2 : ℝ) ≤ p := by exact_mod_cast hp

theorem θ_pos_aux {p : ℕ} (hp : 2 ≤ p) : 0 < Real.pi / p := by
  have := p_pos_aux hp
  have := Real.pi_pos
  positivity

theorem θ_le_aux {p : ℕ} (hp : 2 ≤ p) : Real.pi / p ≤ Real.pi / 2 := by
  have := p_pos_aux hp
  exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) this

theorem θ₁_pos : 0 < σ.θ₁ := θ_pos_aux σ.two_le_p₁

theorem θ₂_pos : 0 < σ.θ₂ := θ_pos_aux σ.two_le_p₂

theorem θ₃_pos : 0 < σ.θ₃ := θ_pos_aux σ.two_le_p₃

theorem θ₁_le : σ.θ₁ ≤ Real.pi / 2 := θ_le_aux σ.two_le_p₁

theorem θ₂_le : σ.θ₂ ≤ Real.pi / 2 := θ_le_aux σ.two_le_p₂

theorem θ₃_le : σ.θ₃ ≤ Real.pi / 2 := θ_le_aux σ.two_le_p₃

theorem θ_sum : σ.θ₁ + σ.θ₂ + σ.θ₃ = Real.pi := by
  have h := σ.sum_inv
  unfold θ₁ θ₂ θ₃
  have : Real.pi / σ.p₁ + Real.pi / σ.p₂ + Real.pi / σ.p₃ =
      Real.pi * (1 / σ.p₁ + 1 / σ.p₂ + 1 / σ.p₃) := by ring
  rw [this, h, mul_one]

theorem θ₁_mul : σ.θ₁ * σ.p₁ = Real.pi := by
  have := p_pos_aux σ.two_le_p₁
  unfold θ₁
  field_simp

theorem θ₂_mul : σ.θ₂ * σ.p₂ = Real.pi := by
  have := p_pos_aux σ.two_le_p₂
  unfold θ₂
  field_simp

theorem θ₃_mul : σ.θ₃ * σ.p₃ = Real.pi := by
  have := p_pos_aux σ.two_le_p₃
  unfold θ₃
  field_simp

theorem sin_pos_aux {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ Real.pi / 2) : 0 < Real.sin θ :=
  Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])

theorem cos_nonneg_aux {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ Real.pi / 2) : 0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h1

theorem cos_lt_one_aux {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ Real.pi / 2) : Real.cos θ < 1 := by
  have hs := sin_pos_aux h0 h1
  have hc := Real.sin_sq_add_cos_sq θ
  have hc1 := Real.cos_le_one θ
  rcases hc1.lt_or_eq with h | h
  · exact h
  · rw [h] at hc
    nlinarith

theorem sin_θ₁_pos : 0 < Real.sin σ.θ₁ := sin_pos_aux σ.θ₁_pos σ.θ₁_le

theorem sin_θ₂_pos : 0 < Real.sin σ.θ₂ := sin_pos_aux σ.θ₂_pos σ.θ₂_le

theorem sin_θ₃_pos : 0 < Real.sin σ.θ₃ := sin_pos_aux σ.θ₃_pos σ.θ₃_le

theorem cos_θ₁_nonneg : 0 ≤ Real.cos σ.θ₁ := cos_nonneg_aux σ.θ₁_pos σ.θ₁_le

theorem cos_θ₂_nonneg : 0 ≤ Real.cos σ.θ₂ := cos_nonneg_aux σ.θ₂_pos σ.θ₂_le

theorem cos_θ₃_nonneg : 0 ≤ Real.cos σ.θ₃ := cos_nonneg_aux σ.θ₃_pos σ.θ₃_le

theorem sin_θ₁_eq : Real.sin σ.θ₁ = Real.sin σ.θ₂ * Real.cos σ.θ₃ +
    Real.cos σ.θ₂ * Real.sin σ.θ₃ := by
  rw [← Real.sin_add, show σ.θ₁ = Real.pi - (σ.θ₂ + σ.θ₃) by linarith [σ.θ_sum],
    Real.sin_pi_sub]

theorem sin_θ₂_eq : Real.sin σ.θ₂ = Real.sin σ.θ₁ * Real.cos σ.θ₃ +
    Real.cos σ.θ₁ * Real.sin σ.θ₃ := by
  rw [← Real.sin_add, show σ.θ₂ = Real.pi - (σ.θ₁ + σ.θ₃) by linarith [σ.θ_sum],
    Real.sin_pi_sub]

theorem sin_θ₃_eq : Real.sin σ.θ₃ = Real.sin σ.θ₁ * Real.cos σ.θ₂ +
    Real.cos σ.θ₁ * Real.sin σ.θ₂ := by
  rw [← Real.sin_add, show σ.θ₃ = Real.pi - (σ.θ₁ + σ.θ₂) by linarith [σ.θ_sum],
    Real.sin_pi_sub]

def vertexOne : ℂ := (Real.sin σ.θ₂ : ℂ) * exp (σ.θ₃ * I)

def vertexTwo : ℂ := (Real.sin σ.θ₁ : ℂ)

def radOne : ℝ := (Real.sin σ.θ₃ + Real.sin σ.θ₂ - Real.sin σ.θ₁) / 2

def radTwo : ℝ := (Real.sin σ.θ₃ + Real.sin σ.θ₁ - Real.sin σ.θ₂) / 2

def radThree : ℝ := (Real.sin σ.θ₁ + Real.sin σ.θ₂ - Real.sin σ.θ₃) / 2

theorem radOne_pos : 0 < σ.radOne := by
  have h := σ.sin_θ₁_eq
  have := cos_lt_one_aux σ.θ₂_pos σ.θ₂_le
  have := cos_lt_one_aux σ.θ₃_pos σ.θ₃_le
  have := σ.sin_θ₂_pos
  have := σ.sin_θ₃_pos
  unfold radOne
  nlinarith

theorem radTwo_pos : 0 < σ.radTwo := by
  have h := σ.sin_θ₂_eq
  have := cos_lt_one_aux σ.θ₁_pos σ.θ₁_le
  have := cos_lt_one_aux σ.θ₃_pos σ.θ₃_le
  have := σ.sin_θ₁_pos
  have := σ.sin_θ₃_pos
  unfold radTwo
  nlinarith

theorem radThree_pos : 0 < σ.radThree := by
  have h := σ.sin_θ₃_eq
  have := cos_lt_one_aux σ.θ₁_pos σ.θ₁_le
  have := cos_lt_one_aux σ.θ₂_pos σ.θ₂_le
  have := σ.sin_θ₁_pos
  have := σ.sin_θ₂_pos
  unfold radThree
  nlinarith

theorem radOne_add_radTwo : σ.radOne + σ.radTwo = Real.sin σ.θ₃ := by
  unfold radOne radTwo
  ring

theorem radOne_add_radThree : σ.radOne + σ.radThree = Real.sin σ.θ₂ := by
  unfold radOne radThree
  ring

theorem radTwo_add_radThree : σ.radTwo + σ.radThree = Real.sin σ.θ₁ := by
  unfold radTwo radThree
  ring

theorem norm_exp_mul_I (θ : ℝ) : ‖exp (θ * I)‖ = 1 := norm_exp_ofReal_mul_I θ

theorem conj_exp_mul_I (θ : ℝ) : conj (exp (θ * I)) = exp (-(θ * I)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem exp_mul_I_mul_exp_neg (θ : ℝ) : exp (θ * I) * exp (-(θ * I)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem vertexTwo_sub_vertexOne :
    σ.vertexTwo - σ.vertexOne = (Real.sin σ.θ₃ : ℂ) * exp (-((σ.θ₂ : ℂ) * I)) := by
  have h := σ.sin_θ₁_eq
  apply Complex.ext
  · simp only [vertexTwo, vertexOne, sub_re, ofReal_re, mul_re, ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]
    rw [show -((σ.θ₂ : ℂ) * I) = ((-σ.θ₂ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    linarith
  · simp only [vertexTwo, vertexOne, sub_im, ofReal_im, mul_im, ofReal_re,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, add_zero, zero_sub]
    rw [show -((σ.θ₂ : ℂ) * I) = ((-σ.θ₂ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_ofReal_mul_I_im, Real.sin_neg]
    ring

theorem norm_vertexOne : ‖σ.vertexOne‖ = Real.sin σ.θ₂ := by
  rw [vertexOne, norm_mul, norm_exp_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos σ.sin_θ₂_pos]

theorem norm_vertexTwo : ‖σ.vertexTwo‖ = Real.sin σ.θ₁ := by
  rw [vertexTwo, Complex.norm_real, Real.norm_eq_abs, abs_of_pos σ.sin_θ₁_pos]

theorem norm_vertexOne_sub_vertexTwo : ‖σ.vertexOne - σ.vertexTwo‖ = Real.sin σ.θ₃ := by
  rw [← norm_neg, neg_sub, vertexTwo_sub_vertexOne, norm_mul,
    show -((σ.θ₂ : ℂ) * I) = ((-σ.θ₂ : ℝ) : ℂ) * I by push_cast; ring, norm_exp_mul_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos σ.sin_θ₃_pos]


def rotOne (z : ℂ) : ℂ := -(exp (-((σ.θ₃ : ℂ) * I)) * (z - σ.vertexOne))

def rotTwo (z : ℂ) : ℂ := -(exp ((σ.θ₂ : ℂ) * I) * (z - σ.vertexTwo))

def wallSide : Fin 3 → ℂ → ℝ
  | 0 => fun z => z.im
  | 1 => fun z => (exp ((σ.θ₃ : ℂ) * I) * conj z).im
  | 2 => fun z => (σ.rotTwo z).im

def triangle : Set ℂ := {z | ∀ i, 0 ≤ σ.wallSide i z}

def refl : Fin 3 → ℂ → ℂ
  | 0 => fun z => conj z
  | 1 => fun z => exp (2 * (σ.θ₃ : ℂ) * I) * conj z
  | 2 => fun z => σ.vertexTwo + exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (z - σ.vertexTwo)

theorem exp_two_mul_conj (θ : ℝ) (w : ℂ) :
    conj (exp (2 * (θ : ℂ) * I) * conj w) = exp (-(2 * (θ : ℂ) * I)) * w := by
  rw [map_mul, Complex.conj_conj, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem exp_neg_mul_exp (a : ℂ) (w : ℂ) : exp (-a) * (exp a * w) = w := by
  rw [← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

theorem conj_vertexTwo : conj σ.vertexTwo = σ.vertexTwo := by
  rw [vertexTwo, Complex.conj_ofReal]

theorem conj_vertexOne : conj σ.vertexOne = exp (-(2 * (σ.θ₃ : ℂ) * I)) * σ.vertexOne := by
  rw [vertexOne, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, mul_left_comm,
    ← Complex.exp_add]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem refl_refl (i : Fin 3) (z : ℂ) : σ.refl i (σ.refl i z) = z := by
  fin_cases i
  · simp [refl]
  · change exp (2 * (σ.θ₃ : ℂ) * I) * conj (exp (2 * (σ.θ₃ : ℂ) * I) * conj z) = z
    rw [exp_two_mul_conj, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
      one_mul]
  · change σ.vertexTwo + exp (-(2 * (σ.θ₂ : ℂ) * I)) *
      conj (σ.vertexTwo + exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (z - σ.vertexTwo) - σ.vertexTwo) = z
    rw [add_sub_cancel_left, map_mul, Complex.conj_conj, ← Complex.exp_conj, ← mul_assoc,
      ← Complex.exp_add]
    have : -(2 * (σ.θ₂ : ℂ) * I) + conj (-(2 * (σ.θ₂ : ℂ) * I)) = 0 := by
      simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
      ring
    rw [this, Complex.exp_zero, one_mul]
    ring

theorem rotTwo_refl_two (z : ℂ) : σ.rotTwo (σ.refl 2 z) = conj (σ.rotTwo z) := by
  change -(exp ((σ.θ₂ : ℂ) * I) * (σ.vertexTwo + exp (-(2 * (σ.θ₂ : ℂ) * I)) *
    conj (z - σ.vertexTwo) - σ.vertexTwo)) = conj (-(exp ((σ.θ₂ : ℂ) * I) * (z - σ.vertexTwo)))
  rw [add_sub_cancel_left, map_neg, map_mul, ← Complex.exp_conj, ← mul_assoc, ← Complex.exp_add]
  congr 3
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem rotTwo_refl_zero (z : ℂ) :
    σ.rotTwo (σ.refl 0 z) = exp (2 * (σ.θ₂ : ℂ) * I) * conj (σ.rotTwo z) := by
  change -(exp ((σ.θ₂ : ℂ) * I) * (conj z - σ.vertexTwo)) =
    exp (2 * (σ.θ₂ : ℂ) * I) * conj (-(exp ((σ.θ₂ : ℂ) * I) * (z - σ.vertexTwo)))
  rw [map_neg, map_mul, map_sub, σ.conj_vertexTwo, ← Complex.exp_conj, mul_neg, ← mul_assoc,
    ← Complex.exp_add]
  congr 3
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem rotOne_refl_one (z : ℂ) : σ.rotOne (σ.refl 1 z) = conj (σ.rotOne z) := by
  change -(exp (-((σ.θ₃ : ℂ) * I)) * (exp (2 * (σ.θ₃ : ℂ) * I) * conj z - σ.vertexOne)) =
    conj (-(exp (-((σ.θ₃ : ℂ) * I)) * (z - σ.vertexOne)))
  have hv : σ.vertexOne = exp (2 * (σ.θ₃ : ℂ) * I) * conj σ.vertexOne := by
    rw [σ.conj_vertexOne, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
      one_mul]
  rw [map_neg, map_mul, map_sub, ← Complex.exp_conj]
  conv_lhs => rw [hv, ← mul_sub, ← mul_assoc, ← Complex.exp_add]
  congr 3
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem rotOne_refl_two (z : ℂ) :
    σ.rotOne (σ.refl 2 z) = exp (2 * (σ.θ₁ : ℂ) * I) * conj (σ.rotOne z) := by
  have hm := σ.vertexTwo_sub_vertexOne
  have hsum := σ.θ_sum
  have key : σ.refl 2 z - σ.vertexOne = exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (z - σ.vertexOne) := by
    change σ.vertexTwo + exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (z - σ.vertexTwo) - σ.vertexOne = _
    have e1 : z - σ.vertexTwo = (z - σ.vertexOne) - (σ.vertexTwo - σ.vertexOne) := by ring
    rw [e1, map_sub, hm, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    have e2 : exp (-(2 * (σ.θ₂ : ℂ) * I)) * (((Real.sin σ.θ₃ : ℝ) : ℂ) *
        exp (conj (-((σ.θ₂ : ℂ) * I)))) = ((Real.sin σ.θ₃ : ℝ) : ℂ) * exp (-((σ.θ₂ : ℂ) * I)) := by
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    linear_combination hm - e2
  change -(exp (-((σ.θ₃ : ℂ) * I)) * (σ.refl 2 z - σ.vertexOne)) =
    exp (2 * (σ.θ₁ : ℂ) * I) * conj (-(exp (-((σ.θ₃ : ℂ) * I)) * (z - σ.vertexOne)))
  rw [key, map_neg, map_mul, ← Complex.exp_conj, mul_neg, ← mul_assoc, ← mul_assoc,
    ← Complex.exp_add, ← Complex.exp_add]
  have e3 : -((σ.θ₃ : ℂ) * I) + -(2 * (σ.θ₂ : ℂ) * I) =
      2 * (σ.θ₁ : ℂ) * I + conj (-((σ.θ₃ : ℂ) * I)) + -(2 * (Real.pi : ℂ) * I) := by
    simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
    have : (σ.θ₁ : ℂ) = Real.pi - σ.θ₂ - σ.θ₃ := by
      rw [show σ.θ₁ = Real.pi - σ.θ₂ - σ.θ₃ by linarith]
      push_cast
      ring
    rw [this]
    ring
  rw [e3, Complex.exp_add (2 * (σ.θ₁ : ℂ) * I + _), Complex.exp_neg, Complex.exp_two_pi_mul_I,
    inv_one, mul_one]


theorem im_conj_mul (a w : ℂ) : (conj a * conj w).im = -(a * w).im := by
  rw [← map_mul, Complex.conj_im]

theorem wallSide_refl (i : Fin 3) (z : ℂ) : σ.wallSide i (σ.refl i z) = -σ.wallSide i z := by
  fin_cases i
  · simp [wallSide, refl]
  · change (exp ((σ.θ₃ : ℂ) * I) * conj (exp (2 * (σ.θ₃ : ℂ) * I) * conj z)).im =
      -(exp ((σ.θ₃ : ℂ) * I) * conj z).im
    rw [exp_two_mul_conj, ← mul_assoc, ← Complex.exp_add,
      show (σ.θ₃ : ℂ) * I + -(2 * (σ.θ₃ : ℂ) * I) = conj ((σ.θ₃ : ℂ) * I) by
        simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring,
      Complex.exp_conj, ← Complex.conj_conj z, ← map_mul, Complex.conj_im, Complex.conj_conj]
  · change (σ.rotTwo (σ.refl 2 z)).im = -(σ.rotTwo z).im
    rw [rotTwo_refl_two, Complex.conj_im]

theorem rotTwo_injective : Function.Injective σ.rotTwo := by
  intro a b h
  have h' : exp ((σ.θ₂ : ℂ) * I) * (a - σ.vertexTwo) = exp ((σ.θ₂ : ℂ) * I) * (b - σ.vertexTwo) :=
    neg_injective h
  have := mul_left_cancel₀ (Complex.exp_ne_zero _) h'
  exact sub_left_injective this

theorem refl_of_wallSide_eq_zero {i : Fin 3} {z : ℂ} (hw : σ.wallSide i z = 0) :
    σ.refl i z = z := by
  fin_cases i
  · change conj z = z
    exact Complex.conj_eq_iff_im.2 hw
  · change exp (2 * (σ.θ₃ : ℂ) * I) * conj z = z
    change (exp ((σ.θ₃ : ℂ) * I) * conj z).im = 0 at hw
    have hr := Complex.conj_eq_iff_im.2 hw
    rw [map_mul, Complex.conj_conj, ← Complex.exp_conj] at hr
    have e : exp (2 * (σ.θ₃ : ℂ) * I) = exp ((σ.θ₃ : ℂ) * I) * exp ((σ.θ₃ : ℂ) * I) := by
      rw [← Complex.exp_add]
      ring_nf
    rw [e, mul_assoc, ← hr, ← mul_assoc, ← Complex.exp_add,
      show (σ.θ₃ : ℂ) * I + conj ((σ.θ₃ : ℂ) * I) = 0 by
        simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring,
      Complex.exp_zero, one_mul]
  · apply σ.rotTwo_injective
    change (σ.rotTwo z).im = 0 at hw
    change σ.rotTwo (σ.refl 2 z) = σ.rotTwo z
    rw [rotTwo_refl_two]
    exact Complex.conj_eq_iff_im.2 hw

theorem rotTwo_eq_rotOne (z : ℂ) :
    σ.rotTwo z = -(exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z) + (Real.sin σ.θ₃ : ℂ) := by
  have hm := σ.vertexTwo_sub_vertexOne
  have hs := σ.θ_sum
  have e : exp (-((σ.θ₁ : ℂ) * I)) * exp (-((σ.θ₃ : ℂ) * I)) =
      -exp ((σ.θ₂ : ℂ) * I) := by
    rw [← Complex.exp_add, show -((σ.θ₁ : ℂ) * I) + -((σ.θ₃ : ℂ) * I) =
      (σ.θ₂ : ℂ) * I + -(Real.pi * I) by
        rw [show σ.θ₁ = Real.pi - σ.θ₂ - σ.θ₃ by linarith]; push_cast; ring,
      Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
    ring
  have e2 : exp ((σ.θ₂ : ℂ) * I) * exp (-((σ.θ₂ : ℂ) * I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  unfold rotTwo rotOne
  have : z - σ.vertexTwo = (z - σ.vertexOne) - (σ.vertexTwo - σ.vertexOne) := by ring
  rw [this, hm]
  linear_combination -(z - σ.vertexOne) * e + (Real.sin σ.θ₃ : ℂ) * e2

theorem wallSide_one_eq_im_rotOne (z : ℂ) : σ.wallSide 1 z = (σ.rotOne z).im := by
  have hv : exp (-((σ.θ₃ : ℂ) * I)) * σ.vertexOne = (Real.sin σ.θ₂ : ℂ) := by
    rw [vertexOne, mul_left_comm, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  change (exp ((σ.θ₃ : ℂ) * I) * conj z).im = _
  rw [rotOne, mul_sub, hv, show -((σ.θ₃ : ℂ) * I) = ((-σ.θ₃ : ℝ) : ℂ) * I by push_cast; ring]
  simp only [neg_im, sub_im, mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    conj_re, conj_im, ofReal_im, Real.cos_neg, Real.sin_neg]
  ring


theorem wallSide_two_eq_rotOne (z : ℂ) :
    σ.wallSide 2 z = -(exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).im := by
  change (σ.rotTwo z).im = _
  rw [rotTwo_eq_rotOne, add_im, ofReal_im, add_zero, neg_im]

theorem wallSide_zero_eq_rotTwo (z : ℂ) :
    σ.wallSide 0 z = -(exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).im := by
  change z.im = _
  rw [rotTwo, mul_neg, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul,
    neg_im, neg_neg, sub_im, vertexTwo, ofReal_im, sub_zero]

theorem wallSide_one_eq_rotThree (z : ℂ) :
    σ.wallSide 1 z = -(exp (-((σ.θ₃ : ℂ) * I)) * z).im := by
  rw [wallSide_one_eq_im_rotOne, rotOne, mul_sub, neg_sub, sub_im, vertexOne, mul_left_comm,
    ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one, ofReal_im, zero_sub]

theorem norm_refl_sub (i : Fin 3) (z w : ℂ) (hw : σ.wallSide i w = 0) :
    ‖σ.refl i z - w‖ = ‖z - w‖ := by
  have hfix := σ.refl_of_wallSide_eq_zero hw
  fin_cases i
  · change ‖conj z - w‖ = _
    change conj w = w at hfix
    rw [← hfix, ← map_sub, Complex.norm_conj, hfix]
  · change exp (2 * (σ.θ₃ : ℂ) * I) * conj w = w at hfix
    change ‖exp (2 * (σ.θ₃ : ℂ) * I) * conj z - w‖ = _
    conv_lhs => rw [← hfix, ← mul_sub, ← map_sub, norm_mul, Complex.norm_conj]
    rw [show 2 * (σ.θ₃ : ℂ) * I = ((2 * σ.θ₃ : ℝ) : ℂ) * I by push_cast; ring, norm_exp_mul_I,
      one_mul]
  · change σ.vertexTwo + exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (w - σ.vertexTwo) = w at hfix
    change ‖σ.vertexTwo + exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (z - σ.vertexTwo) - w‖ = _
    conv_lhs => rw [← hfix]
    rw [add_sub_add_left_eq_sub, ← mul_sub, ← map_sub, norm_mul, Complex.norm_conj,
      show -(2 * (σ.θ₂ : ℂ) * I) = ((-(2 * σ.θ₂) : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_mul_I, one_mul]
    congr 1
    ring

theorem wallSide_zero_vertexTwo : σ.wallSide 0 σ.vertexTwo = 0 := by
  simp [wallSide, vertexTwo]

theorem wallSide_zero_zero : σ.wallSide 0 0 = 0 := by
  simp [wallSide]

theorem wallSide_one_zero : σ.wallSide 1 0 = 0 := by
  simp [wallSide]

theorem rotOne_vertexOne : σ.rotOne σ.vertexOne = 0 := by
  simp [rotOne]

theorem rotTwo_vertexTwo : σ.rotTwo σ.vertexTwo = 0 := by
  simp [rotTwo]

theorem rotTwo_vertexOne : σ.rotTwo σ.vertexOne = (Real.sin σ.θ₃ : ℂ) := by
  rw [rotTwo_eq_rotOne, rotOne_vertexOne, mul_zero, neg_zero, zero_add]

theorem wallSide_one_vertexOne : σ.wallSide 1 σ.vertexOne = 0 := by
  rw [wallSide_one_eq_im_rotOne, rotOne_vertexOne, zero_im]

theorem wallSide_two_vertexOne : σ.wallSide 2 σ.vertexOne = 0 := by
  change (σ.rotTwo σ.vertexOne).im = 0
  rw [rotTwo_vertexOne, ofReal_im]

theorem wallSide_two_vertexTwo : σ.wallSide 2 σ.vertexTwo = 0 := by
  change (σ.rotTwo σ.vertexTwo).im = 0
  rw [rotTwo_vertexTwo, zero_im]

theorem exp_pow_eq_one {θ : ℝ} {p : ℕ} (h : θ * p = Real.pi) :
    exp (2 * (θ : ℂ) * I) ^ p = 1 := by
  rw [← Complex.exp_nat_mul, show (p : ℂ) * (2 * (θ : ℂ) * I) = 2 * ((θ * p : ℝ) : ℂ) * I by
    push_cast; ring, h, Complex.exp_two_pi_mul_I]

def apexOne (z : ℂ) : ℂ := 3 / 2 + σ.rotOne z ^ σ.p₁ / 2

def apexTwo (z : ℂ) : ℂ := -(3 / 2) + σ.rotTwo z ^ σ.p₂ / 2

theorem apexOne_refl_one (z : ℂ) : σ.apexOne (σ.refl 1 z) = conj (σ.apexOne z) := by
  simp only [apexOne, rotOne_refl_one, map_add, map_div₀, map_pow, map_ofNat]

theorem apexOne_refl_two (z : ℂ) : σ.apexOne (σ.refl 2 z) = conj (σ.apexOne z) := by
  simp only [apexOne, rotOne_refl_two, mul_pow, exp_pow_eq_one σ.θ₁_mul, one_mul, map_add,
    map_div₀, map_pow, map_ofNat]

theorem apexTwo_refl_two (z : ℂ) : σ.apexTwo (σ.refl 2 z) = conj (σ.apexTwo z) := by
  simp only [apexTwo, rotTwo_refl_two, map_add, map_div₀, map_pow, map_ofNat, map_neg]

theorem apexTwo_refl_zero (z : ℂ) : σ.apexTwo (σ.refl 0 z) = conj (σ.apexTwo z) := by
  simp only [apexTwo, rotTwo_refl_zero, mul_pow, exp_pow_eq_one σ.θ₂_mul, one_mul, map_add,
    map_div₀, map_pow, map_ofNat, map_neg]

theorem outerGerm_refl_zero (z : ℂ) :
    compactOuterGerm σ.p₃ (σ.refl 0 z) = conj (compactOuterGerm σ.p₃ z) :=
  compactOuterGerm_conj σ.p₃ z

theorem outerGerm_refl_one (z : ℂ) :
    compactOuterGerm σ.p₃ (σ.refl 1 z) = conj (compactOuterGerm σ.p₃ z) := by
  have hn : ‖σ.refl 1 z‖ = ‖z‖ := by
    have := σ.norm_refl_sub 1 z 0 σ.wallSide_one_zero
    simpa using this
  rw [compactOuterGerm, hn, ← compactOuterGerm_conj]
  change -(((7 / 2 - ‖z‖ ^ σ.p₃ / 2 : ℝ) : ℂ) * (conj (exp (2 * (σ.θ₃ : ℂ) * I) * conj z) /
    ‖z‖) ^ σ.p₃) = compactOuterGerm σ.p₃ (conj z)
  rw [exp_two_mul_conj, mul_div_assoc, mul_pow, show exp (-(2 * (σ.θ₃ : ℂ) * I)) ^ σ.p₃ = 1 by
    rw [show -(2 * (σ.θ₃ : ℂ) * I) = 2 * ((-σ.θ₃ : ℝ) : ℂ) * I by push_cast; ring,
      ← Complex.exp_nat_mul, show (σ.p₃ : ℂ) * (2 * ((-σ.θ₃ : ℝ) : ℂ) * I) =
      -(2 * ((σ.θ₃ * σ.p₃ : ℝ) : ℂ) * I) by push_cast; ring, σ.θ₃_mul, Complex.exp_neg,
      Complex.exp_two_pi_mul_I, inv_one], one_mul, compactOuterGerm, Complex.norm_conj,
    Complex.conj_conj]

def canon : Fin 3 → ℂ → ℝ
  | 0 => fun z => ‖z - σ.vertexOne‖ - σ.radOne
  | 1 => fun z => ‖z - σ.vertexTwo‖ - σ.radTwo
  | 2 => fun z => ‖z‖ - σ.radThree

theorem segment_identity {r μ ℓ X Y : ℝ} (hr : r ^ 2 = X ^ 2 + Y ^ 2)
    (hμ : μ ^ 2 = (X - ℓ) ^ 2 + Y ^ 2) (h1 : 0 < r + X) (h2 : 0 < μ + (ℓ - X)) :
    r + μ - ℓ = Y ^ 2 * (1 / (r + X) + 1 / (μ + (ℓ - X))) := by
  have e1 : r - X = Y ^ 2 / (r + X) := by
    rw [eq_div_iff h1.ne']
    nlinarith
  have e2 : μ - (ℓ - X) = Y ^ 2 / (μ + (ℓ - X)) := by
    rw [eq_div_iff h2.ne']
    nlinarith
  have : r + μ - ℓ = (r - X) + (μ - (ℓ - X)) := by ring
  rw [this, e1, e2]
  ring

theorem normSq_eq_sq_norm (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

def cofZeroThree (z : ℂ) : ℝ :=
  1 / (‖z‖ + z.re) + 1 / (‖z - σ.vertexTwo‖ + (Real.sin σ.θ₁ - z.re))

def cofOneThree (z : ℂ) : ℝ :=
  1 / (‖z‖ + (exp (-((σ.θ₃ : ℂ) * I)) * z).re) +
    1 / (‖z - σ.vertexOne‖ + (Real.sin σ.θ₂ - (exp (-((σ.θ₃ : ℂ) * I)) * z).re))

def cofOneTwo (z : ℂ) : ℝ :=
  1 / (‖z - σ.vertexTwo‖ + (σ.rotTwo z).re) +
    1 / (‖z - σ.vertexOne‖ + (Real.sin σ.θ₃ - (σ.rotTwo z).re))

theorem canon_add_canon_zero_three {z : ℂ} (h1 : 0 < ‖z‖ + z.re)
    (h2 : 0 < ‖z - σ.vertexTwo‖ + (Real.sin σ.θ₁ - z.re)) :
    σ.canon 1 z + σ.canon 2 z = σ.wallSide 0 z ^ 2 * σ.cofZeroThree z := by
  have hs := σ.radTwo_add_radThree
  have e : σ.canon 1 z + σ.canon 2 z = ‖z‖ + ‖z - σ.vertexTwo‖ - Real.sin σ.θ₁ := by
    change ‖z - σ.vertexTwo‖ - σ.radTwo + (‖z‖ - σ.radThree) = _
    linarith
  rw [e, cofZeroThree]
  refine segment_identity (normSq_eq_sq_norm z) ?_ h1 h2
  rw [normSq_eq_sq_norm, sub_re, sub_im, vertexTwo, ofReal_re, ofReal_im, sub_zero]
  rfl

theorem canon_add_canon_one_three {z : ℂ} (h1 : 0 < ‖z‖ + (exp (-((σ.θ₃ : ℂ) * I)) * z).re)
    (h2 : 0 < ‖z - σ.vertexOne‖ + (Real.sin σ.θ₂ - (exp (-((σ.θ₃ : ℂ) * I)) * z).re)) :
    σ.canon 0 z + σ.canon 2 z = σ.wallSide 1 z ^ 2 * σ.cofOneThree z := by
  have hs := σ.radOne_add_radThree
  set ζ := exp (-((σ.θ₃ : ℂ) * I)) * z with hζ
  have hu : ‖exp (-((σ.θ₃ : ℂ) * I))‖ = 1 := by
    rw [show -((σ.θ₃ : ℂ) * I) = ((-σ.θ₃ : ℝ) : ℂ) * I by push_cast; ring, norm_exp_mul_I]
  have hnz : ‖ζ‖ = ‖z‖ := by rw [hζ, norm_mul, hu, one_mul]
  have hv : exp (-((σ.θ₃ : ℂ) * I)) * σ.vertexOne = (Real.sin σ.θ₂ : ℂ) := by
    rw [vertexOne, mul_left_comm, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  have hnv : ‖ζ - (Real.sin σ.θ₂ : ℂ)‖ = ‖z - σ.vertexOne‖ := by
    rw [hζ, ← hv, ← mul_sub, norm_mul, hu, one_mul]
  have e : σ.canon 0 z + σ.canon 2 z = ‖z‖ + ‖z - σ.vertexOne‖ - Real.sin σ.θ₂ := by
    change ‖z - σ.vertexOne‖ - σ.radOne + (‖z‖ - σ.radThree) = _
    linarith
  have hw : σ.wallSide 1 z ^ 2 = ζ.im ^ 2 := by
    rw [wallSide_one_eq_rotThree, neg_sq]
  rw [e, cofOneThree, hw]
  refine segment_identity ?_ ?_ h1 h2
  · rw [← hnz, normSq_eq_sq_norm]
  · rw [← hnv, normSq_eq_sq_norm, sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]

theorem canon_add_canon_one_two {z : ℂ} (h1 : 0 < ‖z - σ.vertexTwo‖ + (σ.rotTwo z).re)
    (h2 : 0 < ‖z - σ.vertexOne‖ + (Real.sin σ.θ₃ - (σ.rotTwo z).re)) :
    σ.canon 0 z + σ.canon 1 z = σ.wallSide 2 z ^ 2 * σ.cofOneTwo z := by
  have hs := σ.radOne_add_radTwo
  have hu : ‖exp ((σ.θ₂ : ℂ) * I)‖ = 1 := norm_exp_mul_I _
  have hn2 : ‖σ.rotTwo z‖ = ‖z - σ.vertexTwo‖ := by rw [rotTwo, norm_neg, norm_mul, hu, one_mul]
  have hn1 : ‖σ.rotTwo z - (Real.sin σ.θ₃ : ℂ)‖ = ‖z - σ.vertexOne‖ := by
    have : σ.rotTwo z - (Real.sin σ.θ₃ : ℂ) = -(exp ((σ.θ₂ : ℂ) * I) * (z - σ.vertexOne)) := by
      have h := σ.rotTwo_eq_rotOne z
      have hm := σ.vertexTwo_sub_vertexOne
      rw [rotTwo, show z - σ.vertexTwo = (z - σ.vertexOne) - (σ.vertexTwo - σ.vertexOne) by ring,
        hm, mul_sub, mul_left_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
      ring
    rw [this, norm_neg, norm_mul, hu, one_mul]
  have e : σ.canon 0 z + σ.canon 1 z = ‖z - σ.vertexTwo‖ + ‖z - σ.vertexOne‖ - Real.sin σ.θ₃ := by
    change ‖z - σ.vertexOne‖ - σ.radOne + (‖z - σ.vertexTwo‖ - σ.radTwo) = _
    linarith
  rw [e, cofOneTwo]
  refine segment_identity ?_ ?_ h1 h2
  · rw [← hn2, normSq_eq_sq_norm]
    rfl
  · rw [← hn1, normSq_eq_sq_norm, sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]
    rfl


theorem wallSide_zero_apply (z : ℂ) : σ.wallSide 0 z = z.im := rfl

theorem wallSide_one_apply (z : ℂ) :
    σ.wallSide 1 z = Real.sin σ.θ₃ * z.re - Real.cos σ.θ₃ * z.im := by
  change (exp ((σ.θ₃ : ℂ) * I) * conj z).im = _
  simp only [mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, conj_re, conj_im]
  ring

theorem wallSide_two_apply (z : ℂ) : σ.wallSide 2 z =
    Real.sin σ.θ₁ * Real.sin σ.θ₂ - Real.sin σ.θ₂ * z.re - Real.cos σ.θ₂ * z.im := by
  change (σ.rotTwo z).im = _
  simp only [rotTwo, neg_im, mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    sub_re, sub_im, vertexTwo, ofReal_re, ofReal_im]
  ring

def baryOne (z : ℂ) : ℝ := σ.wallSide 0 z / (Real.sin σ.θ₂ * Real.sin σ.θ₃)

def baryTwo (z : ℂ) : ℝ := σ.wallSide 1 z / (Real.sin σ.θ₁ * Real.sin σ.θ₃)

def baryThree (z : ℂ) : ℝ := σ.wallSide 2 z / (Real.sin σ.θ₁ * Real.sin σ.θ₂)

theorem bary_sum (z : ℂ) : σ.baryOne z + σ.baryTwo z + σ.baryThree z = 1 := by
  have h1 := σ.sin_θ₁_pos
  have h2 := σ.sin_θ₂_pos
  have h3 := σ.sin_θ₃_pos
  have he := σ.sin_θ₁_eq
  rw [baryOne, baryTwo, baryThree, wallSide_zero_apply, wallSide_one_apply, wallSide_two_apply]
  field_simp
  linear_combination z.im * he

theorem eq_bary (z : ℂ) :
    z = (σ.baryTwo z : ℂ) * σ.vertexTwo + (σ.baryOne z : ℂ) * σ.vertexOne := by
  have h1 := σ.sin_θ₁_pos
  have h2 := σ.sin_θ₂_pos
  have h3 := σ.sin_θ₃_pos
  apply Complex.ext
  · simp only [add_re, mul_re, ofReal_re, ofReal_im, vertexTwo, vertexOne,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, mul_im]
    rw [baryOne, baryTwo, wallSide_zero_apply, wallSide_one_apply]
    field_simp
    ring
  · simp only [add_im, mul_im, ofReal_re, ofReal_im, vertexTwo, vertexOne,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, add_zero, mul_re,
      zero_add, mul_zero, sub_zero]
    rw [baryOne, wallSide_zero_apply]
    field_simp

theorem bary_nonneg {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ σ.baryOne z ∧ 0 ≤ σ.baryTwo z ∧ 0 ≤ σ.baryThree z := by
  have h1 := σ.sin_θ₁_pos
  have h2 := σ.sin_θ₂_pos
  have h3 := σ.sin_θ₃_pos
  refine ⟨div_nonneg (hz 0) (by positivity), div_nonneg (hz 1) (by positivity),
    div_nonneg (hz 2) (by positivity)⟩

theorem sin_le_one_aux (θ : ℝ) : Real.sin θ ≤ 1 := Real.sin_le_one θ

theorem norm_le_one_of_mem {z : ℂ} (hz : z ∈ σ.triangle) : ‖z‖ ≤ 1 := by
  obtain ⟨b1, b2, b3⟩ := σ.bary_nonneg hz
  have hs := σ.bary_sum z
  rw [σ.eq_bary z]
  calc ‖(σ.baryTwo z : ℂ) * σ.vertexTwo + (σ.baryOne z : ℂ) * σ.vertexOne‖
      ≤ ‖(σ.baryTwo z : ℂ) * σ.vertexTwo‖ + ‖(σ.baryOne z : ℂ) * σ.vertexOne‖ := norm_add_le _ _
    _ = σ.baryTwo z * Real.sin σ.θ₁ + σ.baryOne z * Real.sin σ.θ₂ := by
        rw [norm_mul, norm_mul, norm_vertexOne, norm_vertexTwo, Complex.norm_real,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg b1,
          abs_of_nonneg b2]
    _ ≤ 1 := by
        nlinarith [sin_le_one_aux σ.θ₁, sin_le_one_aux σ.θ₂]

theorem sub_vertexOne_eq_bary (z : ℂ) : z - σ.vertexOne =
    (σ.baryTwo z : ℂ) * (σ.vertexTwo - σ.vertexOne) + (σ.baryThree z : ℂ) * (0 - σ.vertexOne) := by
  have hs := σ.bary_sum z
  have hs' : (σ.baryThree z : ℂ) = 1 - σ.baryOne z - σ.baryTwo z := by
    rw [show σ.baryThree z = 1 - σ.baryOne z - σ.baryTwo z by linarith]
    push_cast
    ring
  conv_lhs => rw [σ.eq_bary z]
  rw [hs']
  ring

theorem sub_vertexTwo_eq_bary (z : ℂ) : z - σ.vertexTwo =
    (σ.baryOne z : ℂ) * (σ.vertexOne - σ.vertexTwo) + (σ.baryThree z : ℂ) * (0 - σ.vertexTwo) := by
  have hs := σ.bary_sum z
  have hs' : (σ.baryThree z : ℂ) = 1 - σ.baryOne z - σ.baryTwo z := by
    rw [show σ.baryThree z = 1 - σ.baryOne z - σ.baryTwo z by linarith]
    push_cast
    ring
  conv_lhs => rw [σ.eq_bary z]
  rw [hs']
  ring

theorem norm_sub_vertexOne_le {z : ℂ} (hz : z ∈ σ.triangle) : ‖z - σ.vertexOne‖ ≤ 1 := by
  obtain ⟨b1, b2, b3⟩ := σ.bary_nonneg hz
  have hs := σ.bary_sum z
  rw [σ.sub_vertexOne_eq_bary z]
  calc _ ≤ ‖(σ.baryTwo z : ℂ) * (σ.vertexTwo - σ.vertexOne)‖ +
        ‖(σ.baryThree z : ℂ) * (0 - σ.vertexOne)‖ := norm_add_le _ _
    _ = σ.baryTwo z * Real.sin σ.θ₃ + σ.baryThree z * Real.sin σ.θ₂ := by
        rw [norm_mul, norm_mul, ← norm_neg (σ.vertexTwo - σ.vertexOne), neg_sub,
          norm_vertexOne_sub_vertexTwo, zero_sub, norm_neg, norm_vertexOne, Complex.norm_real,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg b2,
          abs_of_nonneg b3]
    _ ≤ 1 := by nlinarith [sin_le_one_aux σ.θ₃, sin_le_one_aux σ.θ₂]

theorem norm_sub_vertexTwo_le {z : ℂ} (hz : z ∈ σ.triangle) : ‖z - σ.vertexTwo‖ ≤ 1 := by
  obtain ⟨b1, b2, b3⟩ := σ.bary_nonneg hz
  have hs := σ.bary_sum z
  rw [σ.sub_vertexTwo_eq_bary z]
  calc _ ≤ ‖(σ.baryOne z : ℂ) * (σ.vertexOne - σ.vertexTwo)‖ +
        ‖(σ.baryThree z : ℂ) * (0 - σ.vertexTwo)‖ := norm_add_le _ _
    _ = σ.baryOne z * Real.sin σ.θ₃ + σ.baryThree z * Real.sin σ.θ₁ := by
        rw [norm_mul, norm_mul, norm_vertexOne_sub_vertexTwo, zero_sub, norm_neg, norm_vertexTwo,
          Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg b1, abs_of_nonneg b3]
    _ ≤ 1 := by nlinarith [sin_le_one_aux σ.θ₃, sin_le_one_aux σ.θ₁]

theorem re_mem {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ z.re ∧ z.re ≤ Real.sin σ.θ₁ := by
  obtain ⟨b1, b2, b3⟩ := σ.bary_nonneg hz
  have hs := σ.bary_sum z
  have he := σ.sin_θ₁_eq
  have hc := cos_nonneg_aux σ.θ₂_pos σ.θ₂_le
  have hz' : z.re =
      σ.baryTwo z * Real.sin σ.θ₁ + σ.baryOne z * (Real.sin σ.θ₂ * Real.cos σ.θ₃) := by
    conv_lhs => rw [σ.eq_bary z]
    simp only [add_re, mul_re, ofReal_re, ofReal_im, vertexTwo, vertexOne,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]
  have h1 := σ.sin_θ₁_pos
  have h2 := σ.sin_θ₂_pos
  have h3 := σ.sin_θ₃_pos
  have hc3 := σ.cos_θ₃_nonneg
  have k1 := mul_nonneg b2 h1.le
  have k2 := mul_nonneg b1 (mul_nonneg h2.le hc3)
  have k3 := mul_nonneg b1 (mul_nonneg hc h3.le)
  have k4 := mul_nonneg b3 h1.le
  constructor
  · rw [hz']
    linarith
  · rw [hz']
    nlinarith


theorem re_rotThree_mem {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ (exp (-((σ.θ₃ : ℂ) * I)) * z).re ∧
      (exp (-((σ.θ₃ : ℂ) * I)) * z).re ≤ Real.sin σ.θ₂ := by
  obtain ⟨b1, b2, b3⟩ := σ.bary_nonneg hz
  have hs := σ.bary_sum z
  have he := σ.sin_θ₂_eq
  have h1 := σ.sin_θ₁_pos
  have h2 := σ.sin_θ₂_pos
  have h3 := σ.sin_θ₃_pos
  have hc1 := σ.cos_θ₁_nonneg
  have hc3 := σ.cos_θ₃_nonneg
  have hz' : (exp (-((σ.θ₃ : ℂ) * I)) * z).re =
      σ.baryTwo z * (Real.sin σ.θ₁ * Real.cos σ.θ₃) + σ.baryOne z * Real.sin σ.θ₂ := by
    conv_lhs => rw [σ.eq_bary z]
    rw [mul_add, mul_left_comm, mul_left_comm _ _ σ.vertexOne, vertexOne, mul_left_comm _ _
      (exp ((σ.θ₃ : ℂ) * I)), ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one,
      show -((σ.θ₃ : ℂ) * I) = ((-σ.θ₃ : ℝ) : ℂ) * I by push_cast; ring]
    simp only [add_re, mul_re, ofReal_re, ofReal_im, vertexTwo, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg, mul_zero, sub_zero, zero_mul]
    ring
  have k1 := mul_nonneg b2 (mul_nonneg h1.le hc3)
  have k2 := mul_nonneg b1 h2.le
  have k3 := mul_nonneg b2 (mul_nonneg hc1 h3.le)
  have k4 := mul_nonneg b3 h2.le
  constructor
  · rw [hz']
    linarith
  · rw [hz']
    nlinarith

theorem re_rotTwo_mem {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ (σ.rotTwo z).re ∧ (σ.rotTwo z).re ≤ Real.sin σ.θ₃ := by
  obtain ⟨b1, b2, b3⟩ := σ.bary_nonneg hz
  have hs := σ.bary_sum z
  have he := σ.sin_θ₃_eq
  have h1 := σ.sin_θ₁_pos
  have h2 := σ.sin_θ₂_pos
  have h3 := σ.sin_θ₃_pos
  have hc1 := σ.cos_θ₁_nonneg
  have hc2 := σ.cos_θ₂_nonneg
  have hm := σ.vertexTwo_sub_vertexOne
  have hz' : (σ.rotTwo z).re =
      σ.baryOne z * Real.sin σ.θ₃ + σ.baryThree z * (Real.sin σ.θ₁ * Real.cos σ.θ₂) := by
    have e : σ.rotTwo z = (σ.baryOne z : ℂ) * (Real.sin σ.θ₃ : ℂ) +
        (σ.baryThree z : ℂ) * (exp ((σ.θ₂ : ℂ) * I) * σ.vertexTwo) := by
      rw [rotTwo, σ.sub_vertexTwo_eq_bary z, ← neg_sub σ.vertexTwo σ.vertexOne, hm]
      have e2 : exp ((σ.θ₂ : ℂ) * I) * exp (-((σ.θ₂ : ℂ) * I)) = 1 := by
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      linear_combination (σ.baryOne z : ℂ) * (Real.sin σ.θ₃ : ℂ) * e2
    rw [e]
    simp only [add_re, mul_re, ofReal_re, ofReal_im, vertexTwo, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, mul_zero, sub_zero, zero_mul, mul_im]
    ring
  have k1 := mul_nonneg b1 h3.le
  have k2 := mul_nonneg b3 (mul_nonneg h1.le hc2)
  have k3 := mul_nonneg b3 (mul_nonneg hc1 h2.le)
  have k4 := mul_nonneg b2 h3.le
  constructor
  · rw [hz']
    linarith
  · rw [hz']
    nlinarith

theorem pos_aux {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b := by linarith

theorem cof_pos_zero_three_left {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) :
    0 < ‖z‖ + z.re := pos_aux (norm_pos_iff.2 h0) (σ.re_mem hz).1

theorem cof_pos_zero_three_right {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ σ.vertexTwo) :
    0 < ‖z - σ.vertexTwo‖ + (Real.sin σ.θ₁ - z.re) :=
  pos_aux (norm_pos_iff.2 (sub_ne_zero.2 h0)) (by linarith [(σ.re_mem hz).2])

theorem cof_pos_one_three_left {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) :
    0 < ‖z‖ + (exp (-((σ.θ₃ : ℂ) * I)) * z).re :=
  pos_aux (norm_pos_iff.2 h0) (σ.re_rotThree_mem hz).1

theorem cof_pos_one_three_right {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ σ.vertexOne) :
    0 < ‖z - σ.vertexOne‖ + (Real.sin σ.θ₂ - (exp (-((σ.θ₃ : ℂ) * I)) * z).re) :=
  pos_aux (norm_pos_iff.2 (sub_ne_zero.2 h0)) (by linarith [(σ.re_rotThree_mem hz).2])

theorem cof_pos_one_two_left {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ σ.vertexTwo) :
    0 < ‖z - σ.vertexTwo‖ + (σ.rotTwo z).re :=
  pos_aux (norm_pos_iff.2 (sub_ne_zero.2 h0)) (σ.re_rotTwo_mem hz).1

theorem cof_pos_one_two_right {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ σ.vertexOne) :
    0 < ‖z - σ.vertexOne‖ + (Real.sin σ.θ₃ - (σ.rotTwo z).re) :=
  pos_aux (norm_pos_iff.2 (sub_ne_zero.2 h0)) (by linarith [(σ.re_rotTwo_mem hz).2])

theorem zero_mem_triangle : (0 : ℂ) ∈ σ.triangle := by
  intro i
  fin_cases i
  · exact σ.wallSide_zero_zero.ge
  · exact σ.wallSide_one_zero.ge
  · change 0 ≤ σ.wallSide 2 0
    rw [wallSide_two_apply]
    simp only [zero_re, zero_im, mul_zero, sub_zero]
    exact (mul_pos σ.sin_θ₁_pos σ.sin_θ₂_pos).le

theorem vertexOne_mem_triangle : σ.vertexOne ∈ σ.triangle := by
  intro i
  fin_cases i
  · change 0 ≤ σ.vertexOne.im
    simp only [vertexOne, mul_im, ofReal_re, ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]
    exact (mul_pos σ.sin_θ₂_pos σ.sin_θ₃_pos).le
  · exact σ.wallSide_one_vertexOne.ge
  · exact σ.wallSide_two_vertexOne.ge

theorem vertexTwo_mem_triangle : σ.vertexTwo ∈ σ.triangle := by
  intro i
  fin_cases i
  · exact σ.wallSide_zero_vertexTwo.ge
  · change 0 ≤ σ.wallSide 1 σ.vertexTwo
    rw [wallSide_one_apply]
    simp only [vertexTwo, ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact (mul_pos σ.sin_θ₃_pos σ.sin_θ₁_pos).le
  · exact σ.wallSide_two_vertexTwo.ge


def shape236 : EuclidShape where
  p₁ := 2
  p₂ := 3
  p₃ := 6
  two_le_p₁ := le_rfl
  two_le_p₂ := by norm_num
  two_le_p₃ := by norm_num
  sum_inv := by norm_num

def shape244 : EuclidShape where
  p₁ := 2
  p₂ := 4
  p₃ := 4
  two_le_p₁ := le_rfl
  two_le_p₂ := by norm_num
  two_le_p₃ := by norm_num
  sum_inv := by norm_num

def shape333 : EuclidShape where
  p₁ := 3
  p₂ := 3
  p₃ := 3
  two_le_p₁ := by norm_num
  two_le_p₂ := by norm_num
  two_le_p₃ := by norm_num
  sum_inv := by norm_num

theorem orders_nat_eq : σ.p₂ * σ.p₃ + σ.p₁ * σ.p₃ + σ.p₁ * σ.p₂ = σ.p₁ * σ.p₂ * σ.p₃ := by
  have h := σ.sum_inv
  have h1 : (σ.p₁ : ℝ) ≠ 0 := by have := σ.two_le_p₁; positivity
  have h2 : (σ.p₂ : ℝ) ≠ 0 := by have := σ.two_le_p₂; positivity
  have h3 : (σ.p₃ : ℝ) ≠ 0 := by have := σ.two_le_p₃; positivity
  have hr : ((σ.p₂ * σ.p₃ + σ.p₁ * σ.p₃ + σ.p₁ * σ.p₂ : ℕ) : ℝ) =
      ((σ.p₁ * σ.p₂ * σ.p₃ : ℕ) : ℝ) := by
    push_cast
    field_simp at h
    linarith
  exact_mod_cast hr

theorem order_le_six {a b c : ℕ} (hb : 2 ≤ b) (hc : 2 ≤ c)
    (e : b * c + a * c + a * b = a * b * c) : a ≤ 6 := by
  by_contra h
  have h7 : 7 ≤ a := by omega
  rcases Nat.lt_or_ge b 3 with hb3 | hb3
  · have hb2 : b = 2 := by omega
    subst hb2
    rcases Nat.lt_or_ge c 3 with hc3 | hc3
    · have : c = 2 := by omega
      subst this
      omega
    · nlinarith
  · rcases Nat.lt_or_ge c 3 with hc3 | hc3
    · have : c = 2 := by omega
      subst this
      nlinarith
    · nlinarith [Nat.mul_le_mul_right (a * c) hb3, Nat.mul_le_mul_right (a * b) hc3,
        Nat.mul_le_mul_right (b * c) h7, Nat.mul_le_mul hb3 hc3]

theorem orders_mem :
    (σ.p₁, σ.p₂, σ.p₃) ∈ ({(2, 3, 6), (2, 6, 3), (3, 2, 6), (3, 6, 2), (6, 2, 3), (6, 3, 2),
      (2, 4, 4), (4, 2, 4), (4, 4, 2), (3, 3, 3)} : Finset (ℕ × ℕ × ℕ)) := by
  have e := σ.orders_nat_eq
  have h1 := σ.two_le_p₁
  have h2 := σ.two_le_p₂
  have h3 := σ.two_le_p₃
  have b1 : σ.p₁ ≤ 6 := order_le_six h2 h3 e
  have b2 : σ.p₂ ≤ 6 := order_le_six h1 h3 (by linarith [e])
  have b3 : σ.p₃ ≤ 6 := order_le_six h1 h2 (by linarith [e])
  generalize σ.p₁ = a at *
  generalize σ.p₂ = b at *
  generalize σ.p₃ = c at *
  interval_cases a <;> interval_cases b <;> interval_cases c <;> simp_all

end EuclidShape

end GC.Seifert
