import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypTrig

/-!
# The hyperbolic compact triangle: vertices, rotated coordinates, walls

Lane CF-H, tier 1 (design
`docs/geometrization/handoffs/20261004-design-cf-compact-triangle-fold.md`,
§2, curvature `-1`, with the errata of review 23). For a `CompactShape` of curvature
`hyperbolic` the angles satisfy `θᵢ ∈ (0, π/2]`, `pᵢ θᵢ = π`, `θ₁ + θ₂ + θ₃ < π`, and the side
tangents of the spec are the `hTan` of `CompactFoldHypTrig`, in `(0, 1)`:
`sideOneThree = ‖v₁‖`, `sideTwoThree = v₂` and `sideOneTwo = tanh (ℓ₁₂/2)`.

The placement identity gives the rotated disc coordinates of the vertices: `rotTwo v₁ = sideOneTwo`
(wall 2 leaves `v₂` along the positive axis, `rotTwo_vertexOne`), `rotOne v₂ = sideOneTwo e^{iθ₁}`
(`rotOne_vertexTwo`), `rotOne 0 = sideOneThree`, `rotTwo 0 = sideTwoThree e^{iθ₂}`; the two rotated
coordinates differ by a disc automorphism, `rotOne = -e^{iθ₁} mob sideOneTwo ∘ rotTwo` on the disc
(`rotOne_eq_mob_rotTwo`), with the unimodular constant `1 - v₂ v₁ = -e^{i(θ₁+θ₂+θ₃)} (1 - v̄₁ v₂)`
read off from the two placements (`one_sub_mul_vertex_eq`).

Each side function is, up to an explicit positive factor on the disc, the imaginary part of a
rotated coordinate (`wallSide_one_eq_rotOne`, `wallSide_zero_eq_rotTwo`, `wallSide_two_eq_rotOne`),
so on the triangle every rotated coordinate lies in its closed sector `[0, θⱼ]`
(`sector_three`, `sector_one`, `sector_two`), and in particular has nonnegative real part.
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate

namespace GC.Seifert

namespace HypFold

variable (σ : CompactShape)

theorem p_pos_aux {p : ℕ} (hp : 2 ≤ p) : (0 : ℝ) < p := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  linarith

theorem θ_pos_aux {p : ℕ} (hp : 2 ≤ p) : 0 < Real.pi / p := div_pos Real.pi_pos (p_pos_aux hp)

theorem θ_le_aux {p : ℕ} (hp : 2 ≤ p) : Real.pi / p ≤ Real.pi / 2 := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) this

theorem θ₁_pos : 0 < σ.θ₁ := θ_pos_aux σ.two_le_p₁

theorem θ₂_pos : 0 < σ.θ₂ := θ_pos_aux σ.two_le_p₂

theorem θ₃_pos : 0 < σ.θ₃ := θ_pos_aux σ.two_le_p₃

theorem θ₁_le : σ.θ₁ ≤ Real.pi / 2 := θ_le_aux σ.two_le_p₁

theorem θ₂_le : σ.θ₂ ≤ Real.pi / 2 := θ_le_aux σ.two_le_p₂

theorem θ₃_le : σ.θ₃ ≤ Real.pi / 2 := θ_le_aux σ.two_le_p₃

theorem θ₁_mul : σ.θ₁ * σ.p₁ = Real.pi := by
  rw [CompactShape.θ₁, div_mul_cancel₀ _ (p_pos_aux σ.two_le_p₁).ne']

theorem θ₂_mul : σ.θ₂ * σ.p₂ = Real.pi := by
  rw [CompactShape.θ₂, div_mul_cancel₀ _ (p_pos_aux σ.two_le_p₂).ne']

theorem θ₃_mul : σ.θ₃ * σ.p₃ = Real.pi := by
  rw [CompactShape.θ₃, div_mul_cancel₀ _ (p_pos_aux σ.two_le_p₃).ne']

theorem exp_mul_exp_neg (x : ℝ) : exp ((x : ℂ) * I) * exp (-((x : ℂ) * I)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

variable {σ}

theorem sum_inv_lt (h : σ.curv = .hyperbolic) : (1 / σ.p₁ + 1 / σ.p₂ + 1 / σ.p₃ : ℝ) < 1 := by
  rcases σ.angle_cond with ⟨-, hs⟩ | ⟨h', -⟩ | ⟨h', -⟩
  · exact hs
  · rw [h] at h'
    exact absurd h' (by decide)
  · rw [h] at h'
    exact absurd h' (by decide)

theorem θ_sum_lt (h : σ.curv = .hyperbolic) : σ.θ₁ + σ.θ₂ + σ.θ₃ < Real.pi := by
  have hs := sum_inv_lt h
  have e : σ.θ₁ + σ.θ₂ + σ.θ₃ = Real.pi * (1 / σ.p₁ + 1 / σ.p₂ + 1 / σ.p₃) := by
    simp only [CompactShape.θ₁, CompactShape.θ₂, CompactShape.θ₃]
    ring
  rw [e]
  nlinarith [Real.pi_pos]

theorem sideTan_hyp (h : σ.curv = .hyperbolic) (a b c : ℝ) :
    σ.sideTan a b c = Real.sqrt ((CompactShape.sideCos a b c - 1) /
      (CompactShape.sideCos a b c + 1)) := by
  unfold CompactShape.sideTan
  rw [h]

variable (σ)

def sideOneThree : ℝ := σ.sideTan σ.θ₁ σ.θ₃ σ.θ₂

def sideTwoThree : ℝ := σ.sideTan σ.θ₂ σ.θ₃ σ.θ₁

def sideOneTwo : ℝ := σ.sideTan σ.θ₁ σ.θ₂ σ.θ₃

variable {σ}

section Hyp

variable (h : σ.curv = .hyperbolic)
include h

theorem sideOneThree_eq : sideOneThree σ = hTan σ.θ₁ σ.θ₃ σ.θ₂ := by
  rw [sideOneThree, sideTan_hyp h]
  exact sqrt_sideCos_eq (θ₁_pos σ) (θ₁_le σ) (θ₃_pos σ) (θ₃_le σ) (θ₂_pos σ) (θ₂_le σ)
    (by linarith [θ_sum_lt h])

theorem sideTwoThree_eq : sideTwoThree σ = hTan σ.θ₂ σ.θ₃ σ.θ₁ := by
  rw [sideTwoThree, sideTan_hyp h]
  exact sqrt_sideCos_eq (θ₂_pos σ) (θ₂_le σ) (θ₃_pos σ) (θ₃_le σ) (θ₁_pos σ) (θ₁_le σ)
    (by linarith [θ_sum_lt h])

theorem sideOneTwo_eq : sideOneTwo σ = hTan σ.θ₁ σ.θ₂ σ.θ₃ := by
  rw [sideOneTwo, sideTan_hyp h]
  exact sqrt_sideCos_eq (θ₁_pos σ) (θ₁_le σ) (θ₂_pos σ) (θ₂_le σ) (θ₃_pos σ) (θ₃_le σ)
    (θ_sum_lt h)

theorem sideOneThree_pos : 0 < sideOneThree σ := by
  rw [sideOneThree_eq h]
  exact hTan_pos (θ₁_pos σ) (θ₁_le σ) (θ₃_pos σ) (θ₃_le σ) (θ₂_pos σ) (θ₂_le σ)
    (by linarith [θ_sum_lt h])

theorem sideTwoThree_pos : 0 < sideTwoThree σ := by
  rw [sideTwoThree_eq h]
  exact hTan_pos (θ₂_pos σ) (θ₂_le σ) (θ₃_pos σ) (θ₃_le σ) (θ₁_pos σ) (θ₁_le σ)
    (by linarith [θ_sum_lt h])

theorem sideOneTwo_pos : 0 < sideOneTwo σ := by
  rw [sideOneTwo_eq h]
  exact hTan_pos (θ₁_pos σ) (θ₁_le σ) (θ₂_pos σ) (θ₂_le σ) (θ₃_pos σ) (θ₃_le σ) (θ_sum_lt h)

theorem sideOneThree_lt_one : sideOneThree σ < 1 := by
  rw [sideOneThree_eq h]
  exact hTan_lt_one (θ₁_pos σ) (θ₁_le σ) (θ₃_pos σ) (θ₃_le σ) (θ₂_pos σ) (θ₂_le σ)
    (by linarith [θ_sum_lt h])

theorem sideTwoThree_lt_one : sideTwoThree σ < 1 := by
  rw [sideTwoThree_eq h]
  exact hTan_lt_one (θ₂_pos σ) (θ₂_le σ) (θ₃_pos σ) (θ₃_le σ) (θ₁_pos σ) (θ₁_le σ)
    (by linarith [θ_sum_lt h])

theorem sideOneTwo_lt_one : sideOneTwo σ < 1 := by
  rw [sideOneTwo_eq h]
  exact hTan_lt_one (θ₁_pos σ) (θ₁_le σ) (θ₂_pos σ) (θ₂_le σ) (θ₃_pos σ) (θ₃_le σ)
    (θ_sum_lt h)

theorem oplus_three : sideOneTwo σ < oplus (sideOneThree σ) (sideTwoThree σ) := by
  rw [sideOneTwo_eq h, sideOneThree_eq h, sideTwoThree_eq h]
  exact hTan_lt_oplus (θ₁_pos σ) (θ₁_le σ) (θ₂_pos σ) (θ₂_le σ) (θ₃_pos σ) (θ₃_le σ)
    (θ_sum_lt h)

theorem oplus_one : sideTwoThree σ < oplus (sideOneTwo σ) (sideOneThree σ) := by
  rw [sideOneTwo_eq h, sideOneThree_eq h, sideTwoThree_eq h,
    show hTan σ.θ₁ σ.θ₂ σ.θ₃ = hTan σ.θ₂ σ.θ₁ σ.θ₃ from (hTan_swap _ _ _).symm,
    show hTan σ.θ₁ σ.θ₃ σ.θ₂ = hTan σ.θ₃ σ.θ₁ σ.θ₂ from (hTan_swap _ _ _).symm]
  exact hTan_lt_oplus (θ₂_pos σ) (θ₂_le σ) (θ₃_pos σ) (θ₃_le σ) (θ₁_pos σ) (θ₁_le σ)
    (by linarith [θ_sum_lt h])

theorem oplus_two : sideOneThree σ < oplus (sideOneTwo σ) (sideTwoThree σ) := by
  rw [sideOneTwo_eq h, sideOneThree_eq h, sideTwoThree_eq h,
    show hTan σ.θ₂ σ.θ₃ σ.θ₁ = hTan σ.θ₃ σ.θ₂ σ.θ₁ from (hTan_swap _ _ _).symm]
  exact hTan_lt_oplus (θ₁_pos σ) (θ₁_le σ) (θ₃_pos σ) (θ₃_le σ) (θ₂_pos σ) (θ₂_le σ)
    (by linarith [θ_sum_lt h])

omit h in
theorem vertexOne_eq : σ.vertexOne = (sideOneThree σ : ℂ) * exp ((σ.θ₃ : ℂ) * I) := rfl

omit h in
theorem vertexTwo_eq : σ.vertexTwo = (sideTwoThree σ : ℂ) := rfl

omit h in
theorem conj_vertexTwo : conj σ.vertexTwo = σ.vertexTwo := by
  rw [vertexTwo_eq, Complex.conj_ofReal]

theorem norm_vertexOne : ‖σ.vertexOne‖ = sideOneThree σ := by
  rw [vertexOne_eq, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (sideOneThree_pos h)]

theorem norm_vertexTwo : ‖σ.vertexTwo‖ = sideTwoThree σ := by
  rw [vertexTwo_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sideTwoThree_pos h)]

theorem norm_vertexOne_lt_one : ‖σ.vertexOne‖ < 1 := by
  rw [norm_vertexOne h]
  exact sideOneThree_lt_one h

theorem norm_vertexTwo_lt_one : ‖σ.vertexTwo‖ < 1 := by
  rw [norm_vertexTwo h]
  exact sideTwoThree_lt_one h

theorem placement_two :
    σ.vertexOne - σ.vertexTwo = -((sideOneTwo σ : ℂ) * exp (-((σ.θ₂ : ℂ) * I))) *
      (1 - σ.vertexTwo * σ.vertexOne) := by
  have hp := hTan_placement (θ₂_pos σ) (θ₂_le σ) (θ₁_pos σ) (θ₁_le σ) (θ₃_pos σ) (θ₃_le σ)
    (by linarith [θ_sum_lt h])
  rw [hTan_swap σ.θ₁ σ.θ₂, ← sideOneThree_eq h, ← sideTwoThree_eq h, ← sideOneTwo_eq h] at hp
  rw [vertexOne_eq, vertexTwo_eq]
  exact hp

theorem placement_one :
    σ.vertexTwo - σ.vertexOne = -((sideOneTwo σ : ℂ) * exp (((σ.θ₁ + σ.θ₃ : ℝ) : ℂ) * I)) *
      (1 - conj σ.vertexOne * σ.vertexTwo) := by
  have hp := hTan_placement (θ₁_pos σ) (θ₁_le σ) (θ₂_pos σ) (θ₂_le σ) (θ₃_pos σ) (θ₃_le σ)
    (θ_sum_lt h)
  rw [← sideOneThree_eq h, ← sideTwoThree_eq h, ← sideOneTwo_eq h] at hp
  have hc := congrArg (fun w => exp ((σ.θ₃ : ℂ) * I) * conj w) hp
  simp only [map_sub, map_mul, map_neg, map_one, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.conj_I, map_neg] at hc
  rw [vertexOne_eq, vertexTwo_eq, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  have e1 : exp ((σ.θ₃ : ℂ) * I) * exp ((σ.θ₃ : ℂ) * -I) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    exact Complex.exp_zero
  have e2 : exp ((σ.θ₃ : ℂ) * I) * exp (-(-((σ.θ₁ : ℂ) * I))) =
      exp (((σ.θ₁ + σ.θ₃ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc (sideTwoThree σ : ℂ) - (sideOneThree σ : ℂ) * exp ((σ.θ₃ : ℂ) * I)
      = exp ((σ.θ₃ : ℂ) * I) * ((sideTwoThree σ : ℂ) * exp ((σ.θ₃ : ℂ) * -I) -
          (sideOneThree σ : ℂ)) := by
        rw [mul_sub, mul_left_comm, e1, mul_one, mul_comm]
    _ = -((sideOneTwo σ : ℂ) * exp (((σ.θ₁ + σ.θ₃ : ℝ) : ℂ) * I)) *
          (1 - (sideOneThree σ : ℂ) * exp ((σ.θ₃ : ℂ) * -I) * (sideTwoThree σ : ℂ)) := by
        rw [hc, ← e2]
        ring_nf

theorem one_sub_vertexTwo_mul_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : 1 - σ.vertexTwo * z ≠ 0 := by
  have := one_sub_conj_mul_ne_zero (norm_vertexTwo_lt_one h) hz
  rwa [conj_vertexTwo] at this

theorem one_sub_conj_vertexOne_mul_ne_zero {z : ℂ} (hz : ‖z‖ < 1) :
    1 - conj σ.vertexOne * z ≠ 0 :=
  one_sub_conj_mul_ne_zero (norm_vertexOne_lt_one h) hz

theorem disc_vertexTwo_vertexOne :
    σ.disc σ.vertexTwo σ.vertexOne = -((sideOneTwo σ : ℂ) * exp (-((σ.θ₂ : ℂ) * I))) := by
  have hne := one_sub_vertexTwo_mul_ne_zero h (norm_vertexOne_lt_one h)
  rw [CompactShape.disc_eq_mob h, mob, conj_vertexTwo, div_eq_iff hne, placement_two h]

theorem disc_vertexOne_vertexTwo :
    σ.disc σ.vertexOne σ.vertexTwo = -((sideOneTwo σ : ℂ) * exp (((σ.θ₁ + σ.θ₃ : ℝ) : ℂ) * I)) := by
  have hne := one_sub_conj_vertexOne_mul_ne_zero h (norm_vertexTwo_lt_one h)
  rw [CompactShape.disc_eq_mob h, mob, div_eq_iff hne, placement_one h]

theorem rotTwo_vertexOne : σ.rotTwo σ.vertexOne = (sideOneTwo σ : ℂ) := by
  rw [CompactShape.rotTwo, disc_vertexTwo_vertexOne h]
  simp only [mul_neg, neg_neg]
  rw [mul_left_comm, exp_mul_exp_neg, mul_one]

theorem rotOne_vertexTwo : σ.rotOne σ.vertexTwo = (sideOneTwo σ : ℂ) * exp ((σ.θ₁ : ℂ) * I) := by
  rw [CompactShape.rotOne, disc_vertexOne_vertexTwo h]
  simp only [mul_neg, neg_neg]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

omit h in
theorem rotOne_zero_eq : σ.rotOne 0 = (sideOneThree σ : ℂ) := by
  rw [CompactShape.rotOne, CompactShape.disc, vertexOne_eq]
  simp only [zero_sub, mul_zero, sub_zero, div_one, mul_neg, neg_neg]
  rw [mul_left_comm, mul_comm (exp _), exp_mul_exp_neg, mul_one]

omit h in
theorem rotTwo_zero_eq : σ.rotTwo 0 = (sideTwoThree σ : ℂ) * exp ((σ.θ₂ : ℂ) * I) := by
  rw [CompactShape.rotTwo, CompactShape.disc, vertexTwo_eq]
  simp only [zero_sub, mul_zero, sub_zero, div_one, mul_neg, neg_neg]
  ring

theorem one_sub_mul_vertex_eq :
    1 - σ.vertexTwo * σ.vertexOne =
      -exp (((σ.θ₁ + σ.θ₂ + σ.θ₃ : ℝ) : ℂ) * I) * (1 - conj σ.vertexOne * σ.vertexTwo) := by
  have h2 := placement_two h
  have h1 := placement_one h
  have ht : (sideOneTwo σ : ℂ) ≠ 0 := by exact_mod_cast (sideOneTwo_pos h).ne'
  have hsum : (sideOneTwo σ : ℂ) * (exp (-((σ.θ₂ : ℂ) * I)) * (1 - σ.vertexTwo * σ.vertexOne) +
      exp (((σ.θ₁ + σ.θ₃ : ℝ) : ℂ) * I) * (1 - conj σ.vertexOne * σ.vertexTwo)) = 0 := by
    linear_combination h2 + h1
  have hs := (mul_eq_zero.1 hsum).resolve_left ht
  have e : exp (((σ.θ₁ + σ.θ₂ + σ.θ₃ : ℝ) : ℂ) * I) =
      exp ((σ.θ₂ : ℂ) * I) * exp (((σ.θ₁ + σ.θ₃ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e]
  linear_combination exp ((σ.θ₂ : ℂ) * I) * hs -
    (1 - σ.vertexTwo * σ.vertexOne) * exp_mul_exp_neg σ.θ₂

theorem rotTwo_eq_mul_mob (z : ℂ) : σ.rotTwo z = -exp ((σ.θ₂ : ℂ) * I) * mob σ.vertexTwo z := by
  rw [CompactShape.rotTwo, CompactShape.disc_eq_mob h, neg_mul]

theorem rotOne_eq_mul_mob (z : ℂ) :
    σ.rotOne z = -exp (-((σ.θ₃ : ℂ) * I)) * mob σ.vertexOne z := by
  rw [CompactShape.rotOne, CompactShape.disc_eq_mob h, neg_mul]

omit h in
theorem norm_neg_exp (x : ℝ) : ‖-exp ((x : ℂ) * I)‖ = 1 := by
  rw [norm_neg, Complex.norm_exp_ofReal_mul_I]

omit h in
theorem norm_neg_exp_neg (x : ℝ) : ‖-exp (-((x : ℂ) * I))‖ = 1 := by
  rw [norm_neg, show -((x : ℂ) * I) = ((-x : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem normSq_vertexTwo_ne_one : normSq σ.vertexTwo ≠ 1 := by
  have h1 := normSq_lt_one_of_norm_lt (norm_vertexTwo_lt_one h)
  exact h1.ne

theorem normSq_vertexOne_ne_one : normSq σ.vertexOne ≠ 1 := by
  have h1 := normSq_lt_one_of_norm_lt (norm_vertexOne_lt_one h)
  exact h1.ne

theorem rotOne_eq_mob_rotTwo {z : ℂ} (hz : ‖z‖ < 1) :
    σ.rotOne z = -exp ((σ.θ₁ : ℂ) * I) * mob (sideOneTwo σ) (σ.rotTwo z) := by
  have ht : -exp ((σ.θ₂ : ℂ) * I) * mob σ.vertexTwo σ.vertexOne = (sideOneTwo σ : ℂ) := by
    rw [← rotTwo_eq_mul_mob h, rotTwo_vertexOne h]
  have h1 := one_sub_conj_mul_ne_zero (norm_vertexTwo_lt_one h) (norm_vertexOne_lt_one h)
  have h2 := one_sub_conj_mul_ne_zero (norm_vertexTwo_lt_one h) hz
  have h3 := one_sub_conj_mul_ne_zero (norm_vertexOne_lt_one h) hz
  have hm := mob_mob_mob (normSq_vertexTwo_ne_one h) h1 h2 h3
  rw [rotTwo_eq_mul_mob h, ← ht, mob_mul_mul (norm_neg_exp σ.θ₂), hm, rotOne_eq_mul_mob h,
    conj_vertexTwo]
  have hk := one_sub_mul_vertex_eq h
  have h1' : 1 - σ.vertexTwo * σ.vertexOne ≠ 0 := by rwa [conj_vertexTwo] at h1
  have e : exp (((σ.θ₁ + σ.θ₂ + σ.θ₃ : ℝ) : ℂ) * I) =
      exp ((σ.θ₁ : ℂ) * I) * exp ((σ.θ₂ : ℂ) * I) * exp ((σ.θ₃ : ℂ) * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e] at hk
  have e3 := exp_mul_exp_neg σ.θ₃
  rw [show -exp ((σ.θ₁ : ℂ) * I) * (-exp ((σ.θ₂ : ℂ) * I) * (mob σ.vertexOne z *
      ((1 - σ.vertexTwo * conj σ.vertexOne) / (1 - σ.vertexTwo * σ.vertexOne)))) =
      exp ((σ.θ₁ : ℂ) * I) * exp ((σ.θ₂ : ℂ) * I) * (1 - σ.vertexTwo * conj σ.vertexOne) *
        mob σ.vertexOne z / (1 - σ.vertexTwo * σ.vertexOne) by ring, eq_div_iff h1']
  linear_combination (-(exp (-((σ.θ₃ : ℂ) * I)) * mob σ.vertexOne z)) * hk +
    (exp ((σ.θ₁ : ℂ) * I) * exp ((σ.θ₂ : ℂ) * I) * (1 - σ.vertexTwo * conj σ.vertexOne) *
      mob σ.vertexOne z) * e3

omit h in
theorem im_mob_ofReal (t : ℝ) (W : ℂ) :
    (mob (t : ℂ) W).im * normSq (1 - (t : ℂ) * W) = (1 - t ^ 2) * W.im := by
  have e := im_mob_mul_normSq (t : ℂ) W
  rw [Complex.conj_ofReal] at e
  rw [e]
  simp only [mul_im, mul_re, sub_re, sub_im, ofReal_re, ofReal_im, conj_re, conj_im, one_re,
    one_im, map_sub, map_one, map_mul, Complex.conj_ofReal]
  ring

omit h in
omit h in
theorem wallSide_one_eq_neg_im (z : ℂ) :
    σ.wallSide 1 z = -(exp (-((σ.θ₃ : ℂ) * I)) * z).im := by
  change (exp ((σ.θ₃ : ℂ) * I) * conj z).im = _
  rw [exp_neg_ofReal_mul_I_eq, exp_ofReal_mul_I_eq]
  simp only [mul_im, add_re, add_im, sub_re, sub_im, ofReal_re, ofReal_im, mul_re, I_re, I_im,
    conj_re, conj_im]
  ring

omit h in
theorem wallSide_one_apply (z : ℂ) :
    σ.wallSide 1 z = Real.sin σ.θ₃ * z.re - Real.cos σ.θ₃ * z.im := by
  change (exp ((σ.θ₃ : ℂ) * I) * conj z).im = _
  rw [exp_ofReal_mul_I_eq]
  simp only [mul_im, add_re, add_im, ofReal_re, ofReal_im, mul_re, I_re, I_im, conj_re, conj_im]
  ring

theorem wallSide_two_apply (z : ℂ) : σ.wallSide 2 z =
    sideTwoThree σ * Real.sin σ.θ₂ * (1 + normSq z) -
      (1 + sideTwoThree σ ^ 2) * Real.sin σ.θ₂ * z.re -
      (1 - sideTwoThree σ ^ 2) * Real.cos σ.θ₂ * z.im := by
  change (-(exp ((σ.θ₂ : ℂ) * I) * ((z - σ.vertexTwo) *
    conj (1 - σ.eps * conj σ.vertexTwo * z)))).im = _
  rw [CompactShape.eps_hyp h, exp_ofReal_mul_I_eq, vertexTwo_eq]
  simp only [neg_im, mul_im, mul_re, add_re, add_im, sub_re, sub_im, ofReal_re, ofReal_im,
    I_re, I_im, conj_re, conj_im, one_re, one_im, map_sub, map_one, map_mul,
    Complex.conj_ofReal, normSq_apply]
  ring

theorem rotOne_im_mul_normSq {z : ℂ} (hz : ‖z‖ < 1) :
    (σ.rotOne z).im * normSq (1 - conj σ.vertexOne * z) =
      (1 - sideOneThree σ ^ 2) * σ.wallSide 1 z := by
  have hD := one_sub_conj_vertexOne_mul_ne_zero h hz
  have e : σ.rotOne z * (normSq (1 - conj σ.vertexOne * z) : ℂ) =
      -(exp (-((σ.θ₃ : ℂ) * I)) * ((z - σ.vertexOne) * conj (1 - conj σ.vertexOne * z))) := by
    rw [rotOne_eq_mul_mob h, mul_assoc, mob_mul_normSq hD]
    ring
  have him := congrArg Complex.im e
  rw [Complex.mul_im, ofReal_re, ofReal_im, mul_zero, zero_add] at him
  rw [him, wallSide_one_apply, vertexOne_eq, exp_neg_ofReal_mul_I_eq, exp_ofReal_mul_I_eq]
  simp only [neg_im, mul_im, mul_re, sub_re, sub_im, ofReal_re, ofReal_im, I_re, I_im, add_re,
    add_im, conj_re, conj_im, map_sub, map_one, map_mul, Complex.conj_ofReal, one_re, one_im,
    map_add, Complex.conj_I, neg_re, neg_im]
  have hcs := Real.sin_sq_add_cos_sq σ.θ₃
  linear_combination (-(sideOneThree σ ^ 2) * (Real.sin σ.θ₃ * z.re - Real.cos σ.θ₃ * z.im)) *
    hcs

theorem exp_neg_mul_rotTwo (z : ℂ) :
    exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z = -mob σ.vertexTwo z := by
  rw [rotTwo_eq_mul_mob h, neg_mul, mul_neg, ← mul_assoc, mul_comm (exp _), exp_mul_exp_neg,
    one_mul]

theorem exp_neg_mul_rotOne {z : ℂ} (hz : ‖z‖ < 1) :
    exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z = -mob (sideOneTwo σ) (σ.rotTwo z) := by
  rw [rotOne_eq_mob_rotTwo h hz, neg_mul, mul_neg, ← mul_assoc, mul_comm (exp _),
    exp_mul_exp_neg, one_mul]

theorem rotTwo_rot_im_mul_normSq (z : ℂ) :
    (exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).im * normSq (1 - σ.vertexTwo * z) =
      -((1 - sideTwoThree σ ^ 2) * σ.wallSide 0 z) := by
  have e := im_mob_mul_normSq σ.vertexTwo z
  rw [conj_vertexTwo] at e
  rw [exp_neg_mul_rotTwo h, neg_im, neg_mul, e, vertexTwo_eq]
  change -((z - (sideTwoThree σ : ℂ)) * conj (1 - (sideTwoThree σ : ℂ) * z)).im =
    -((1 - sideTwoThree σ ^ 2) * z.im)
  simp only [mul_im, mul_re, sub_re, sub_im, ofReal_re, ofReal_im, conj_re, conj_im, one_re,
    one_im, map_sub, map_one, map_mul, Complex.conj_ofReal]
  ring

theorem wallSide_two_eq_rotTwo (z : ℂ) :
    σ.wallSide 2 z = (σ.rotTwo z).im * normSq (1 - σ.vertexTwo * z) := by
  rw [σ.wallSide_two_eq, CompactShape.eps_hyp h, conj_vertexTwo, Complex.ofReal_one, one_mul]

theorem rotOne_rot_im_mul_normSq {z : ℂ} (hz : ‖z‖ < 1) :
    (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).im *
        normSq (1 - (sideOneTwo σ : ℂ) * σ.rotTwo z) =
      -((1 - sideOneTwo σ ^ 2) * (σ.rotTwo z).im) := by
  rw [exp_neg_mul_rotOne h hz, neg_im, neg_mul, im_mob_ofReal]

omit h in
theorem normSq_pos_of_ne {w : ℂ} (hw : w ≠ 0) : 0 < normSq w := normSq_pos.2 hw

theorem norm_lt_one_of_mem {z : ℂ} (hz : z ∈ σ.triangle) : ‖z‖ < 1 := by
  have h1 := hz.1
  rw [CompactShape.plane_hyp h] at h1
  simpa using h1

theorem norm_rotTwo_lt_one {z : ℂ} (hz : ‖z‖ < 1) : ‖σ.rotTwo z‖ < 1 := by
  rw [rotTwo_eq_mul_mob h, norm_mul, norm_neg_exp, one_mul]
  exact norm_mob_lt_one (norm_vertexTwo_lt_one h) hz

theorem norm_rotOne_lt_one {z : ℂ} (hz : ‖z‖ < 1) : ‖σ.rotOne z‖ < 1 := by
  rw [rotOne_eq_mul_mob h, norm_mul, norm_neg_exp_neg, one_mul]
  exact norm_mob_lt_one (norm_vertexOne_lt_one h) hz

theorem norm_rotTwo (z : ℂ) : ‖σ.rotTwo z‖ = ‖mob σ.vertexTwo z‖ := by
  rw [rotTwo_eq_mul_mob h, norm_mul, norm_neg_exp, one_mul]

theorem norm_rotOne (z : ℂ) : ‖σ.rotOne z‖ = ‖mob σ.vertexOne z‖ := by
  rw [rotOne_eq_mul_mob h, norm_mul, norm_neg_exp_neg, one_mul]

omit h in
theorem re_nonneg_of_sector {θ : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ Real.pi / 2) {W : ℂ}
    (h1 : 0 ≤ W.im) (h2 : (exp (-((θ : ℂ) * I)) * W).im ≤ 0) : 0 ≤ W.re := by
  rw [exp_neg_ofReal_mul_I_eq] at h2
  simp only [mul_im, sub_re, sub_im, ofReal_re, ofReal_im, mul_re, I_re, I_im] at h2
  have hs := sin_pos_of_le hθ hθ'
  have hc := cos_nonneg_of_le hθ hθ'
  nlinarith

omit h in
theorem sector_three {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ z.im ∧ (exp (-((σ.θ₃ : ℂ) * I)) * z).im ≤ 0 := by
  refine ⟨hz.2 0, ?_⟩
  have := hz.2 1
  rw [wallSide_one_eq_neg_im] at this
  linarith

theorem sector_two {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ (σ.rotTwo z).im ∧ (exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).im ≤ 0 := by
  have hz1 := norm_lt_one_of_mem h hz
  have hp := normSq_pos_of_ne (one_sub_vertexTwo_mul_ne_zero h hz1)
  have ht1 := sideTwoThree_lt_one h
  have ht0 := sideTwoThree_pos h
  constructor
  · have h2 := hz.2 2
    rw [wallSide_two_eq_rotTwo h] at h2
    exact nonneg_of_mul_nonneg_left h2 hp
  · have h0 := hz.2 0
    have e := rotTwo_rot_im_mul_normSq h z
    have : 0 ≤ (1 - sideTwoThree σ ^ 2) * σ.wallSide 0 z := by
      apply mul_nonneg _ h0
      nlinarith
    by_contra hc
    push Not at hc
    have := mul_pos hc hp
    linarith

theorem sector_one {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ (σ.rotOne z).im ∧ (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).im ≤ 0 := by
  have hz1 := norm_lt_one_of_mem h hz
  constructor
  · have hp := normSq_pos_of_ne (one_sub_conj_vertexOne_mul_ne_zero h hz1)
    have e := rotOne_im_mul_normSq h hz1
    have h1 := hz.2 1
    have ht1 := sideOneThree_lt_one h
    have ht0 := sideOneThree_pos h
    have : 0 ≤ (1 - sideOneThree σ ^ 2) * σ.wallSide 1 z := by
      apply mul_nonneg _ h1
      nlinarith
    rw [← e] at this
    exact nonneg_of_mul_nonneg_left this hp
  · have hW := (sector_two h hz).1
    have e := rotOne_rot_im_mul_normSq h hz1
    have ht1 := sideOneTwo_lt_one h
    have ht0 := sideOneTwo_pos h
    have hne : 1 - (sideOneTwo σ : ℂ) * σ.rotTwo z ≠ 0 := by
      have := one_sub_conj_mul_ne_zero (a := (sideOneTwo σ : ℂ))
        (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; exact ht1)
        (norm_rotTwo_lt_one h hz1)
      rwa [Complex.conj_ofReal] at this
    have hp := normSq_pos_of_ne hne
    have : 0 ≤ (1 - sideOneTwo σ ^ 2) * (σ.rotTwo z).im := by
      apply mul_nonneg _ hW
      nlinarith
    by_contra hc
    push Not at hc
    have := mul_pos hc hp
    linarith

end Hyp

end HypFold

end GC.Seifert
