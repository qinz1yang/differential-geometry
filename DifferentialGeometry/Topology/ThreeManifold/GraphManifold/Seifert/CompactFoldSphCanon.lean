import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphTriangle

/-!
# Canonical radii and the profile functions of the spherical compact fold

Lane CF-S, tier 1, curvature `+4` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §2). In the stereographic chart the half-distance
tangent `tan (d(a, b)/2)` is `‖sphMoeb a b‖`, and it satisfies the strict triangle inequality
`‖sphMoeb a b‖ < ‖a‖ ⊕ ‖b‖` with `x ⊕ y = (x + y)/(1 - x y)` unless the two directions are opposite
(`norm_sphMoeb_lt_oplus`). Applied at the three vertices it gives the strict triangle inequalities
of the half sides `aᵢⱼ = arctan tᵢⱼ ∈ (0, π/4]`, so the half canonical radii
`sphHalfRad j = (aⱼᵢ + aⱼₖ - aᵢₖ)/2` lie in `(0, π/4)` and their tangents `sphTau j ∈ (0, 1)`
satisfy `τᵢ ⊕ τⱼ = tᵢⱼ` (`sphTau_oplus_*`).

The profile functions are `sphCanon j = (ϖⱼ - τⱼ)/(1 + ϖⱼ τⱼ) = tan ((dⱼ - rⱼ)/2)` with
`ϖⱼ = sphDist j` the chordal distance to the vertex (`‖rotOne‖`, `‖rotTwo‖`, `‖z‖`). They lie in
`(-1, 1)` on the triangle (`sphCanon_mem`). The sum of two of them factorises as
`(1 - τᵢτⱼ) β / ((1 + ϖᵢτᵢ)(1 + ϖⱼτⱼ))` with `β = ϖᵢ + ϖⱼ - tᵢⱼ (1 - ϖᵢ ϖⱼ)` (`canon_add_aux_sph`),
and in the rotated disc coordinate `ζ` at `vᵢ` with `vⱼ` at `t = tᵢⱼ > 0` one has
`β = (Im ζ)² · sphPairQ t ζ` (`pair_identity_sph`), with an explicit cofactor positive off the two
vertices of the wall (`pairQ_pos_sph`). The three instances are `sphCanon_add_zero` (wall 0, `ζ =
z`),
`sphCanon_add_one` (wall 1, `ζ = e^{-iθ₃} z`) and `sphCanon_add_two` (wall 2, `ζ = rotTwo z`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set
open scoped ComplexConjugate

namespace GC.Seifert

theorem conj_mul_re_eq_sph (a b : ℂ) : (conj a * b).re = a.re * b.re + a.im * b.im := by
  simp only [mul_re, conj_re, conj_im]
  ring

theorem sq_norm_sub_eq_sph (a b : ℂ) :
    ‖b - a‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * (conj a * b).re := by
  rw [CompactShape.sq_norm_eq_sph, CompactShape.sq_norm_eq_sph a, CompactShape.sq_norm_eq_sph b,
    conj_mul_re_eq_sph]
  simp only [sub_re, sub_im]
  ring

theorem sq_norm_one_add_eq_sph (a b : ℂ) :
    ‖1 + conj a * b‖ ^ 2 = 1 + ‖a‖ ^ 2 * ‖b‖ ^ 2 + 2 * (conj a * b).re := by
  rw [CompactShape.sq_norm_eq_sph, CompactShape.sq_norm_eq_sph a, CompactShape.sq_norm_eq_sph b,
    conj_mul_re_eq_sph]
  simp only [add_re, add_im, one_re, one_im, mul_re, mul_im, conj_re, conj_im]
  ring

theorem norm_one_add_conj_mul_pos_sph {a b : ℂ} (hab : ‖a‖ * ‖b‖ < 1)
    (hc : -(‖a‖ * ‖b‖) < (conj a * b).re) : 0 < ‖1 + conj a * b‖ := by
  have h2 := sq_norm_one_add_eq_sph a b
  have hsq : 0 < ‖1 + conj a * b‖ ^ 2 := by
    rw [h2]
    nlinarith [mul_nonneg (norm_nonneg a) (norm_nonneg b)]
  by_contra h
  push Not at h
  have := le_antisymm h (norm_nonneg _)
  rw [this] at hsq
  norm_num at hsq

theorem norm_sphMoeb_lt_oplus {a b : ℂ} (hab : ‖a‖ * ‖b‖ < 1)
    (hc : -(‖a‖ * ‖b‖) < (conj a * b).re) :
    ‖sphMoeb a b‖ < (‖a‖ + ‖b‖) / (1 - ‖a‖ * ‖b‖) := by
  have hD := norm_one_add_conj_mul_pos_sph hab hc
  have h1 := sq_norm_sub_eq_sph a b
  have h2 := sq_norm_one_add_eq_sph a b
  rw [sphMoeb, norm_div, div_lt_div_iff₀ hD (by linarith)]
  have hl : 0 ≤ ‖b - a‖ * (1 - ‖a‖ * ‖b‖) := mul_nonneg (norm_nonneg _) (by linarith)
  have hr : 0 ≤ (‖a‖ + ‖b‖) * ‖1 + conj a * b‖ :=
    mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  refine (pow_lt_pow_iff_left₀ hl hr two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, h1, h2]
  set A := ‖a‖
  set B := ‖b‖
  set c := (conj a * b).re
  have key : (A + B) ^ 2 * (1 + A ^ 2 * B ^ 2 + 2 * c) -
      (A ^ 2 + B ^ 2 - 2 * c) * (1 - A * B) ^ 2 =
      2 * ((A + B) ^ 2 + (1 - A * B) ^ 2) * (c + A * B) := by ring
  have hpos : 0 < 2 * ((A + B) ^ 2 + (1 - A * B) ^ 2) * (c + A * B) := by
    have : 0 < (1 - A * B) ^ 2 := by nlinarith
    have : 0 < c + A * B := by linarith
    positivity
  linarith

theorem arctan_lt_add_of_sph {x y z : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hy1 : y ≤ 1)
    (hz1 : z ≤ 1) (h : x * y < 1 → z < (x + y) / (1 - x * y)) :
    Real.arctan z < Real.arctan x + Real.arctan y := by
  by_cases hxy : x * y < 1
  · rw [Real.arctan_add hxy]
    exact Real.arctan_strictMono (h hxy)
  · push Not at hxy
    have hx' : x = 1 := by nlinarith
    have hy' : y = 1 := by nlinarith
    have hz : Real.arctan z ≤ Real.arctan 1 := Real.arctan_le_arctan_iff.2 hz1
    rw [hx', hy', Real.arctan_one]
    rw [Real.arctan_one] at hz
    linarith [Real.pi_pos]

theorem arctan_mem_sph {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) :
    0 < Real.arctan t ∧ Real.arctan t ≤ Real.pi / 4 := by
  refine ⟨Real.arctan_pos.2 h0, ?_⟩
  rw [← Real.arctan_one]
  exact Real.arctan_le_arctan_iff.2 h1

theorem canon_add_aux_sph {ϖ μ τ₁ τ₂ t : ℝ} (ht : τ₁ + τ₂ = t * (1 - τ₁ * τ₂))
    (h1 : 1 + ϖ * τ₁ ≠ 0) (h2 : 1 + μ * τ₂ ≠ 0) :
    (ϖ - τ₁) / (1 + ϖ * τ₁) + (μ - τ₂) / (1 + μ * τ₂) =
      (1 - τ₁ * τ₂) * (ϖ + μ - t * (1 - ϖ * μ)) / ((1 + ϖ * τ₁) * (1 + μ * τ₂)) := by
  rw [div_add_div _ _ h1 h2]
  congr 1
  linear_combination (-(1 - ϖ * μ)) * ht

def sphPairNum (t : ℝ) (ζ : ℂ) : ℝ :=
  (1 + t * ζ.re) * ‖sphMoeb t ζ‖ + t - ζ.re

def sphPairQ (t : ℝ) (ζ : ℂ) : ℝ :=
  (1 + t * ‖sphMoeb t ζ‖) / (‖ζ‖ + ζ.re) +
    (1 + t ^ 2) * (1 + 2 * t * ζ.re - t ^ 2) / (Complex.normSq (1 + t * ζ) * sphPairNum t ζ)

theorem normSq_one_add_real_sph (t : ℝ) (ζ : ℂ) :
    Complex.normSq (1 + t * ζ) = (1 + t * ζ.re) ^ 2 + t ^ 2 * ζ.im ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [add_re, add_im, one_re, one_im, mul_re, mul_im, ofReal_re, ofReal_im, zero_mul,
    sub_zero, add_zero, zero_add]
  ring

theorem sq_norm_sphMoeb_real (t : ℝ) (ζ : ℂ) (h : 0 < 1 + t * ζ.re) :
    ‖sphMoeb t ζ‖ ^ 2 * ((1 + t * ζ.re) ^ 2 + t ^ 2 * ζ.im ^ 2) =
      (ζ.re - t) ^ 2 + ζ.im ^ 2 := by
  have hD : 0 < (1 + t * ζ.re) ^ 2 + t ^ 2 * ζ.im ^ 2 := by positivity
  rw [sphMoeb, Complex.conj_ofReal, norm_div, div_pow, Complex.sq_norm, Complex.sq_norm,
    normSq_one_add_real_sph, div_mul_cancel₀ _ hD.ne', Complex.normSq_apply]
  simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]
  ring

theorem pair_identity_sph {t : ℝ} {ζ : ℂ} (h1 : 0 < ‖ζ‖ + ζ.re) (h2 : 0 < 1 + t * ζ.re)
    (h3 : 0 < sphPairNum t ζ) :
    ‖ζ‖ + ‖sphMoeb t ζ‖ - t * (1 - ‖ζ‖ * ‖sphMoeb t ζ‖) = ζ.im ^ 2 * sphPairQ t ζ := by
  set ϖ := ‖ζ‖ with hϖdef
  set μ := ‖sphMoeb t ζ‖ with hμdef
  set X := ζ.re
  set Y := ζ.im
  have hϖ : ϖ ^ 2 = X ^ 2 + Y ^ 2 := CompactShape.sq_norm_eq_sph ζ
  have hμ := sq_norm_sphMoeb_real t ζ h2
  rw [← hμdef] at hμ
  set D := (1 + t * X) ^ 2 + t ^ 2 * Y ^ 2 with hD
  have hDpos : 0 < D := by positivity
  set P := sphPairNum t ζ with hP
  have hP' : P = (1 + t * X) * μ + t - X := rfl
  have key : (ϖ + μ - t * (1 - ϖ * μ)) * ((ϖ + X) * (D * P)) =
      Y ^ 2 * ((1 + t * μ) * (D * P) + (ϖ + X) * ((1 + t ^ 2) * (1 + 2 * t * X - t ^ 2))) := by
    rw [hP']
    linear_combination (1 + t * μ) * D * ((1 + t * X) * μ + t - X) * hϖ +
      (ϖ + X) * (1 + t * X) ^ 2 * hμ
  rw [sphPairQ, ← hϖdef, ← hμdef, normSq_one_add_real_sph, ← hD, ← hP,
    div_add_div _ _ h1.ne' (mul_ne_zero hDpos.ne' h3.ne'), mul_div_assoc',
    eq_div_iff (mul_ne_zero h1.ne' (mul_ne_zero hDpos.ne' h3.ne'))]
  linear_combination key

theorem pairQ_pos_sph {t : ℝ} {ζ : ℂ} (ht : 0 < t) (h1 : 0 < ‖ζ‖ + ζ.re) (h2 : 0 < 1 + t * ζ.re)
    (h3 : 0 < sphPairNum t ζ) (h4 : 0 ≤ 1 + 2 * t * ζ.re - t ^ 2) : 0 < sphPairQ t ζ := by
  have hN : 0 < Complex.normSq (1 + t * ζ) := by
    rw [normSq_one_add_real_sph]
    positivity
  unfold sphPairQ
  have := norm_nonneg (sphMoeb (t : ℂ) ζ)
  have hA : 0 < (1 + t * ‖sphMoeb (t : ℂ) ζ‖) / (‖ζ‖ + ζ.re) := by positivity
  have hB : 0 ≤ (1 + t ^ 2) * (1 + 2 * t * ζ.re - t ^ 2) /
      (Complex.normSq (1 + t * ζ) * sphPairNum t ζ) := by positivity
  linarith

theorem pair_wall_sph {t : ℝ} {ζ : ℂ} (ht : 0 < t) (hY : ζ.im = 0) (hX0 : 0 ≤ ζ.re)
    (hXt : ζ.re ≤ t) :
    ‖ζ‖ + ‖sphMoeb t ζ‖ - t * (1 - ‖ζ‖ * ‖sphMoeb t ζ‖) = 0 := by
  have hζ : ζ = (ζ.re : ℂ) := by
    apply Complex.ext <;> simp [hY]
  set X := ζ.re
  have h1 : 0 < 1 + t * X := by positivity
  have hn : ‖ζ‖ = X := by rw [hζ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX0]
  have hm : ‖sphMoeb t ζ‖ = (t - X) / (1 + t * X) := by
    rw [hζ, sphMoeb, Complex.conj_ofReal]
    have e : ((X : ℂ) - t) / (1 + t * X) = (((X - t) / (1 + t * X) : ℝ) : ℂ) := by push_cast; rfl
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (by linarith) h1.le)]
    ring
  rw [hn, hm]
  field_simp
  ring


theorem tan_oplus_aux_sph {x y t : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) (hy0 : 0 < y)
    (hy : y < Real.pi / 4) (hxy : x + y = Real.arctan t) :
    Real.tan x + Real.tan y = t * (1 - Real.tan x * Real.tan y) := by
  have hpi := Real.pi_pos
  have htx : Real.tan x < 1 := by
    rw [← Real.tan_pi_div_four]
    exact Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) (by linarith) hx
  have hty : Real.tan y < 1 := by
    rw [← Real.tan_pi_div_four]
    exact Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) (by linarith) hy
  have hx' := Real.tan_pos_of_pos_of_lt_pi_div_two hx0 (by linarith)
  have hy' := Real.tan_pos_of_pos_of_lt_pi_div_two hy0 (by linarith)
  have hlt : Real.tan x * Real.tan y < 1 := by nlinarith
  have e : Real.arctan ((Real.tan x + Real.tan y) / (1 - Real.tan x * Real.tan y)) =
      Real.arctan t := by
    rw [← Real.arctan_add hlt, Real.arctan_tan (by linarith) (by linarith),
      Real.arctan_tan (by linarith) (by linarith), hxy]
  have e' := Real.arctan_injective e
  rw [div_eq_iff (by linarith)] at e'
  exact e'


theorem sphMoeb_ofReal (t x : ℝ) : sphMoeb t x = (((x - t) / (1 + t * x) : ℝ) : ℂ) := by
  rw [sphMoeb, Complex.conj_ofReal]
  push_cast
  ring

theorem eq_ofReal_re_of_im_sph {ζ : ℂ} (hY : ζ.im = 0) : ζ = (ζ.re : ℂ) := by
  apply Complex.ext <;> simp [hY]

theorem pairNum_pos_sph {t : ℝ} {ζ : ℂ} (ht : 0 < t) (hX : 0 ≤ ζ.re) (hne : ζ ≠ t)
    (hwall : ζ.im = 0 → ζ.re ≤ t) : 0 < sphPairNum t ζ := by
  have h2 : 0 < 1 + t * ζ.re := by positivity
  have hμ := sq_norm_sphMoeb_real t ζ h2
  have hμ0 := norm_nonneg (sphMoeb (t : ℂ) ζ)
  unfold sphPairNum
  by_cases hXt : ζ.re ≤ t
  · have hpos : 0 < ‖sphMoeb (t : ℂ) ζ‖ := by
      rw [norm_pos_iff]
      intro h0
      rw [h0, norm_zero] at hμ
      have hzero : (ζ.re - t) ^ 2 + ζ.im ^ 2 = 0 := by rw [← hμ]; ring
      have hre : ζ.re = t := by nlinarith
      have him : ζ.im = 0 := by nlinarith
      exact hne (Complex.ext (by simp [hre]) (by simp [him]))
    have := mul_pos h2 hpos
    linarith
  · push Not at hXt
    have hY : ζ.im ≠ 0 := fun h => absurd (hwall h) (not_le.2 hXt)
    have hY2 : 0 < ζ.im ^ 2 := by positivity
    by_contra hc
    push Not at hc
    have hle : (1 + t * ζ.re) * ‖sphMoeb (t : ℂ) ζ‖ ≤ ζ.re - t := by linarith
    have hsq : ((1 + t * ζ.re) * ‖sphMoeb (t : ℂ) ζ‖) ^ 2 ≤ (ζ.re - t) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hle 2
    have hD : 0 < (1 + t * ζ.re) ^ 2 + t ^ 2 * ζ.im ^ 2 := by positivity
    have key : (1 + t * ζ.re) ^ 2 * ((ζ.re - t) ^ 2 + ζ.im ^ 2) ≤
        (ζ.re - t) ^ 2 * ((1 + t * ζ.re) ^ 2 + t ^ 2 * ζ.im ^ 2) := by
      rw [← hμ]
      have := mul_le_mul_of_nonneg_right hsq hD.le
      linarith [this]
    have hfac : 0 < (1 + 2 * t * ζ.re - t ^ 2) * (1 + t ^ 2) := by
      have : 0 < 1 + 2 * t * ζ.re - t ^ 2 := by nlinarith
      positivity
    nlinarith [mul_pos hY2 hfac]

theorem pair_conditions_sph {t : ℝ} {ζ : ℂ} (ht : 0 < t) (ht1 : t ≤ 1) (hX : 0 ≤ ζ.re)
    (h0 : ζ ≠ 0) (hne : ζ ≠ t) (hwall : ζ.im = 0 → ζ.re ≤ t) :
    0 < ‖ζ‖ + ζ.re ∧ 0 < 1 + t * ζ.re ∧ 0 < sphPairNum t ζ ∧ 0 < sphPairQ t ζ := by
  have h1 : 0 < ‖ζ‖ + ζ.re := by
    have := norm_pos_iff.2 h0
    linarith
  have h2 : 0 < 1 + t * ζ.re := by positivity
  have h3 := pairNum_pos_sph ht hX hne hwall
  refine ⟨h1, h2, h3, pairQ_pos_sph ht h1 h2 h3 ?_⟩
  nlinarith [mul_nonneg ht.le hX]

namespace CompactShape

variable {σ : CompactShape}

def sphHalfRad (σ : CompactShape) : Fin 3 → ℝ
  | 0 => (Real.arctan σ.sphTOneTwo + Real.arctan σ.sphTOneThree - Real.arctan σ.sphTTwoThree) / 2
  | 1 => (Real.arctan σ.sphTOneTwo + Real.arctan σ.sphTTwoThree - Real.arctan σ.sphTOneThree) / 2
  | 2 => (Real.arctan σ.sphTOneThree + Real.arctan σ.sphTTwoThree - Real.arctan σ.sphTOneTwo) / 2

def sphTau (σ : CompactShape) (j : Fin 3) : ℝ := Real.tan (σ.sphHalfRad j)

def sphDist (σ : CompactShape) : Fin 3 → ℂ → ℝ
  | 0 => fun z => ‖σ.rotOne z‖
  | 1 => fun z => ‖σ.rotTwo z‖
  | 2 => fun z => ‖z‖

def sphCanon (σ : CompactShape) (j : Fin 3) (z : ℂ) : ℝ :=
  (σ.sphDist j z - σ.sphTau j) / (1 + σ.sphDist j z * σ.sphTau j)

theorem sphDist_nonneg (j : Fin 3) (z : ℂ) : 0 ≤ σ.sphDist j z := by
  fin_cases j <;> exact norm_nonneg _

theorem wallSide_one_eq_neg_im_sph (z : ℂ) :
    σ.wallSide 1 z = -(exp (-((σ.θ₃ : ℂ) * I)) * z).im := by
  change (exp ((σ.θ₃ : ℂ) * I) * conj z).im = _
  have : exp ((σ.θ₃ : ℂ) * I) * conj z = conj (exp (-((σ.θ₃ : ℂ) * I)) * z) := by
    rw [map_mul, conj_exp_neg_sph]
  rw [this, Complex.conj_im]

theorem norm_exp_neg_mul_sph (z : ℂ) : ‖exp (-((σ.θ₃ : ℂ) * I)) * z‖ = ‖z‖ := by
  rw [norm_mul, exp_neg_ofReal_mul_I_sph, norm_exp_mul_I_sph', one_mul]

theorem sphCanon_congr {j : Fin 3} {z w : ℂ} (h : σ.sphDist j w = σ.sphDist j z) :
    σ.sphCanon j w = σ.sphCanon j z := by
  rw [sphCanon, sphCanon, h]

theorem sphCanon_refl_zero_two (z : ℂ) : σ.sphCanon 2 (σ.refl 0 z) = σ.sphCanon 2 z :=
  sphCanon_congr (norm_refl_zero_sph z)

theorem sphCanon_refl_one_two (z : ℂ) : σ.sphCanon 2 (σ.refl 1 z) = σ.sphCanon 2 z :=
  sphCanon_congr (norm_refl_one_sph z)

section Spherical

variable (hs : σ.curv = .spherical)
include hs

theorem rotOne_eq_neg_sphMoeb (z : ℂ) :
    σ.rotOne z = -sphMoeb σ.sphTOneThree (exp (-((σ.θ₃ : ℂ) * I)) * z) := by
  set w := exp (-((σ.θ₃ : ℂ) * I)) * z with hw
  have hu : conj (exp ((σ.θ₃ : ℂ) * I)) * exp ((σ.θ₃ : ℂ) * I) = 1 := conj_exp_mul_exp_sph σ.θ₃
  have hz : z = exp ((σ.θ₃ : ℂ) * I) * w := by
    rw [hw, ← mul_assoc, exp_mul_exp_neg_sph, one_mul]
  rw [rotOne_eq_mul_sph hs, vertexOne_eq_sph]
  conv_lhs => rw [hz, mul_comm (σ.sphTOneThree : ℂ), sphMoeb_mul_unit hu]
  have := exp_mul_exp_neg_sph σ.θ₃
  linear_combination (-sphMoeb (σ.sphTOneThree : ℂ) w) * this

theorem tOneTwo_eq_norm_sph : σ.sphTOneTwo = ‖sphMoeb σ.vertexTwo σ.vertexOne‖ := by
  rw [← norm_rotTwo_sph hs, rotTwo_vertexOne_sph hs, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (tOneTwo_pos_sph hs)]

theorem tOneThree_eq_norm_sph : σ.sphTOneThree = ‖sphMoeb (σ.rotTwo 0) (σ.rotTwo σ.vertexOne)‖ := by
  have hu : conj (-exp ((σ.θ₂ : ℂ) * I)) * -exp ((σ.θ₂ : ℂ) * I) = 1 := conj_neg_exp_mul_sph σ.θ₂
  have h1 : 1 + conj σ.vertexTwo * σ.vertexOne ≠ 0 := by
    rw [conj_vertexTwo_sph]
    exact one_add_vertexTwo_mul_vertexOne_ne_sph hs
  rw [rotTwo_eq_mul_sph hs, rotTwo_eq_mul_sph hs, norm_sphMoeb_mul_unit hu,
    norm_sphMoeb_comp (a := σ.vertexTwo) (b := 0) (z := σ.vertexOne) h1 (by simp) (by simp),
    sphMoeb_zero, norm_vertexOne_sph hs]

theorem tTwoThree_eq_norm_sph : σ.sphTTwoThree = ‖sphMoeb (σ.rotOne 0) (σ.rotOne σ.vertexTwo)‖ := by
  have hu : conj (-exp (((-σ.θ₃ : ℝ) : ℂ) * I)) * -exp (((-σ.θ₃ : ℝ) : ℂ) * I) = 1 :=
    conj_neg_exp_mul_sph (-σ.θ₃)
  have h1 := one_add_conj_vertexOne_mul_vertexTwo_ne_sph hs
  rw [rotOne_eq_mul_sph hs, rotOne_eq_mul_sph hs, exp_neg_ofReal_mul_I_sph, norm_sphMoeb_mul_unit
      hu,
    norm_sphMoeb_comp (a := σ.vertexOne) (b := 0) (z := σ.vertexTwo) h1 (by simp) (by simp),
    sphMoeb_zero, norm_vertexTwo_sph hs]

theorem tri_three_sph :
    Real.arctan σ.sphTOneTwo < Real.arctan σ.sphTTwoThree + Real.arctan σ.sphTOneThree := by
  refine arctan_lt_add_of_sph (tTwoThree_pos_sph hs) (tTwoThree_le_one_sph hs) (tOneThree_le_one_sph
      hs)
    (tOneTwo_le_one_sph hs) fun h => ?_
  have hre : (conj σ.vertexTwo * σ.vertexOne).re =
      σ.sphTTwoThree * σ.sphTOneThree * Real.cos σ.θ₃ := by
    rw [conj_vertexTwo_sph, vertexTwo_eq_sph, vertexOne_eq_sph]
    simp only [mul_re, ofReal_re, ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, mul_im, add_zero]
    ring
  have := norm_sphMoeb_lt_oplus (a := σ.vertexTwo) (b := σ.vertexOne)
    (by rwa [norm_vertexTwo_sph hs, norm_vertexOne_sph hs])
    (by
      rw [norm_vertexTwo_sph hs, norm_vertexOne_sph hs, hre]
      have := mul_pos (tTwoThree_pos_sph hs) (tOneThree_pos_sph hs)
      have := mul_nonneg this.le σ.cos_θ₃_nonneg_sph
      linarith)
  rwa [norm_vertexTwo_sph hs, norm_vertexOne_sph hs, ← tOneTwo_eq_norm_sph hs] at this

theorem tri_two_sph :
    Real.arctan σ.sphTOneThree < Real.arctan σ.sphTTwoThree + Real.arctan σ.sphTOneTwo := by
  refine arctan_lt_add_of_sph (tTwoThree_pos_sph hs) (tTwoThree_le_one_sph hs) (tOneTwo_le_one_sph
      hs)
    (tOneThree_le_one_sph hs) fun h => ?_
  have ha : ‖σ.rotTwo 0‖ = σ.sphTTwoThree := by
    rw [rotTwo_zero_sph hs, norm_mul, norm_exp_mul_I_sph', mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (tTwoThree_pos_sph hs)]
  have hb : ‖σ.rotTwo σ.vertexOne‖ = σ.sphTOneTwo := by
    rw [rotTwo_vertexOne_sph hs, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (tOneTwo_pos_sph
        hs)]
  have hre : (conj (σ.rotTwo 0) * σ.rotTwo σ.vertexOne).re =
      σ.sphTTwoThree * σ.sphTOneTwo * Real.cos σ.θ₂ := by
    rw [rotTwo_zero_sph hs, rotTwo_vertexOne_sph hs, map_mul, Complex.conj_ofReal,
      conj_exp_ofReal_mul_I_sph, exp_neg_ofReal_mul_I_sph]
    simp only [mul_re, ofReal_re, ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, mul_im, add_zero, Real.cos_neg]
    ring
  have := norm_sphMoeb_lt_oplus (a := σ.rotTwo 0) (b := σ.rotTwo σ.vertexOne)
    (by rwa [ha, hb])
    (by
      rw [ha, hb, hre]
      have := mul_pos (tTwoThree_pos_sph hs) (tOneTwo_pos_sph hs)
      have := mul_nonneg this.le σ.cos_θ₂_nonneg_sph
      linarith)
  rwa [ha, hb, ← tOneThree_eq_norm_sph hs] at this

theorem tri_one_sph :
    Real.arctan σ.sphTTwoThree < Real.arctan σ.sphTOneThree + Real.arctan σ.sphTOneTwo := by
  refine arctan_lt_add_of_sph (tOneThree_pos_sph hs) (tOneThree_le_one_sph hs) (tOneTwo_le_one_sph
      hs)
    (tTwoThree_le_one_sph hs) fun h => ?_
  have ha : ‖σ.rotOne 0‖ = σ.sphTOneThree := by
    rw [rotOne_zero_sph hs, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (tOneThree_pos_sph hs)]
  have hb : ‖σ.rotOne σ.vertexTwo‖ = σ.sphTOneTwo := by
    rw [rotOne_vertexTwo_sph hs, norm_mul, norm_exp_mul_I_sph', mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (tOneTwo_pos_sph hs)]
  have hre : (conj (σ.rotOne 0) * σ.rotOne σ.vertexTwo).re =
      σ.sphTOneThree * σ.sphTOneTwo * Real.cos σ.θ₁ := by
    rw [rotOne_zero_sph hs, rotOne_vertexTwo_sph hs, Complex.conj_ofReal]
    simp only [mul_re, ofReal_re, ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, mul_im, add_zero]
    ring
  have := norm_sphMoeb_lt_oplus (a := σ.rotOne 0) (b := σ.rotOne σ.vertexTwo)
    (by rwa [ha, hb])
    (by
      rw [ha, hb, hre]
      have := mul_pos (tOneThree_pos_sph hs) (tOneTwo_pos_sph hs)
      have := mul_nonneg this.le σ.cos_θ₁_nonneg_sph
      linarith)
  rwa [ha, hb, ← tTwoThree_eq_norm_sph hs] at this

theorem sphHalfRad_pos (j : Fin 3) : 0 < σ.sphHalfRad j := by
  have := tri_one_sph hs
  have := tri_two_sph hs
  have := tri_three_sph hs
  fin_cases j <;> simp only [sphHalfRad] <;> linarith

theorem sphHalfRad_lt (j : Fin 3) : σ.sphHalfRad j < Real.pi / 4 := by
  obtain ⟨a1, a1'⟩ := arctan_mem_sph (tOneTwo_pos_sph hs) (tOneTwo_le_one_sph hs)
  obtain ⟨a2, a2'⟩ := arctan_mem_sph (tOneThree_pos_sph hs) (tOneThree_le_one_sph hs)
  obtain ⟨a3, a3'⟩ := arctan_mem_sph (tTwoThree_pos_sph hs) (tTwoThree_le_one_sph hs)
  fin_cases j <;> simp only [sphHalfRad] <;> linarith

theorem sphTau_pos (j : Fin 3) : 0 < σ.sphTau j :=
  Real.tan_pos_of_pos_of_lt_pi_div_two (sphHalfRad_pos hs j)
    (by linarith [sphHalfRad_lt hs j, Real.pi_pos])

theorem sphTau_lt_one (j : Fin 3) : σ.sphTau j < 1 := by
  rw [sphTau, ← Real.tan_pi_div_four]
  exact Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith [sphHalfRad_pos hs j, Real.pi_pos])
    (by linarith [Real.pi_pos]) (sphHalfRad_lt hs j)

theorem sphTau_oplus_onetwo :
    σ.sphTau 0 + σ.sphTau 1 = σ.sphTOneTwo * (1 - σ.sphTau 0 * σ.sphTau 1) :=
  tan_oplus_aux_sph (sphHalfRad_pos hs 0) (sphHalfRad_lt hs 0) (sphHalfRad_pos hs 1)
    (sphHalfRad_lt hs 1) (by simp only [sphHalfRad]; ring)

theorem sphTau_oplus_onethree :
    σ.sphTau 0 + σ.sphTau 2 = σ.sphTOneThree * (1 - σ.sphTau 0 * σ.sphTau 2) :=
  tan_oplus_aux_sph (sphHalfRad_pos hs 0) (sphHalfRad_lt hs 0) (sphHalfRad_pos hs 2)
    (sphHalfRad_lt hs 2) (by simp only [sphHalfRad]; ring)

theorem sphTau_oplus_twothree :
    σ.sphTau 1 + σ.sphTau 2 = σ.sphTTwoThree * (1 - σ.sphTau 1 * σ.sphTau 2) :=
  tan_oplus_aux_sph (sphHalfRad_pos hs 1) (sphHalfRad_lt hs 1) (sphHalfRad_pos hs 2)
    (sphHalfRad_lt hs 2) (by simp only [sphHalfRad]; ring)

theorem sphTau_mul_lt_one (i j : Fin 3) : σ.sphTau i * σ.sphTau j < 1 := by
  have := sphTau_pos hs i
  have := sphTau_lt_one hs i
  have := sphTau_pos hs j
  have := sphTau_lt_one hs j
  nlinarith

theorem one_add_sphDist_mul_pos (j : Fin 3) (z : ℂ) : 0 < 1 + σ.sphDist j z * σ.sphTau j := by
  have := mul_nonneg (σ.sphDist_nonneg j z) (sphTau_pos hs j).le
  linarith

theorem neg_one_lt_sphCanon (j : Fin 3) (z : ℂ) : -1 < σ.sphCanon j z := by
  have hd := one_add_sphDist_mul_pos hs j z
  have h0 := σ.sphDist_nonneg j z
  have ht := sphTau_lt_one hs j
  rw [sphCanon, lt_div_iff₀ hd]
  nlinarith

theorem sphCanon_lt_one {j : Fin 3} {z : ℂ} (h : σ.sphDist j z ≤ 1) : σ.sphCanon j z < 1 := by
  have hd := one_add_sphDist_mul_pos hs j z
  have h0 := σ.sphDist_nonneg j z
  have ht := sphTau_pos hs j
  rw [sphCanon, div_lt_one hd]
  nlinarith

theorem sphDist_le_one_of_mem (j : Fin 3) {z : ℂ} (hz : z ∈ σ.triangle) :
    σ.sphDist j z ≤ 1 := by
  fin_cases j
  · exact norm_rotOne_le_one_sph hs hz
  · exact norm_rotTwo_le_one_sph hs hz
  · exact norm_le_one_of_mem_sph hs hz

theorem sphCanon_mem (j : Fin 3) {z : ℂ} (hz : z ∈ σ.triangle) :
    -1 < σ.sphCanon j z ∧ σ.sphCanon j z < 1 :=
  ⟨neg_one_lt_sphCanon hs j z, sphCanon_lt_one hs (sphDist_le_one_of_mem hs j hz)⟩

theorem sphCanon_add_zero {z : ℂ} (h1 : 0 < ‖z‖ + z.re) (h2 : 0 < 1 + σ.sphTTwoThree * z.re)
    (h3 : 0 < sphPairNum σ.sphTTwoThree z) :
    σ.sphCanon 2 z + σ.sphCanon 1 z = (1 - σ.sphTau 2 * σ.sphTau 1) *
      (σ.wallSide 0 z ^ 2 * sphPairQ σ.sphTTwoThree z) /
        ((1 + σ.sphDist 2 z * σ.sphTau 2) * (1 + σ.sphDist 1 z * σ.sphTau 1)) := by
  have hd1 : σ.sphDist 1 z = ‖sphMoeb σ.sphTTwoThree z‖ := by
    change ‖σ.rotTwo z‖ = _
    rw [norm_rotTwo_sph hs, vertexTwo_eq_sph]
  have hd2 : σ.sphDist 2 z = ‖z‖ := rfl
  rw [sphCanon, sphCanon, canon_add_aux_sph (t := σ.sphTTwoThree)
    (by linear_combination sphTau_oplus_twothree hs)
    (one_add_sphDist_mul_pos hs 2 z).ne' (one_add_sphDist_mul_pos hs 1 z).ne', hd1, hd2,
    pair_identity_sph h1 h2 h3, wallSide_zero_apply_sph]

theorem sphCanon_add_one {z : ℂ} (h1 : 0 < ‖z‖ + (exp (-((σ.θ₃ : ℂ) * I)) * z).re)
    (h2 : 0 < 1 + σ.sphTOneThree * (exp (-((σ.θ₃ : ℂ) * I)) * z).re)
    (h3 : 0 < sphPairNum σ.sphTOneThree (exp (-((σ.θ₃ : ℂ) * I)) * z)) :
    σ.sphCanon 2 z + σ.sphCanon 0 z = (1 - σ.sphTau 2 * σ.sphTau 0) *
      (σ.wallSide 1 z ^ 2 * sphPairQ σ.sphTOneThree (exp (-((σ.θ₃ : ℂ) * I)) * z)) /
        ((1 + σ.sphDist 2 z * σ.sphTau 2) * (1 + σ.sphDist 0 z * σ.sphTau 0)) := by
  have hd0 : σ.sphDist 0 z = ‖sphMoeb σ.sphTOneThree (exp (-((σ.θ₃ : ℂ) * I)) * z)‖ := by
    change ‖σ.rotOne z‖ = _
    rw [rotOne_eq_neg_sphMoeb hs, norm_neg]
  have hd2 : σ.sphDist 2 z = ‖exp (-((σ.θ₃ : ℂ) * I)) * z‖ := (norm_exp_neg_mul_sph z).symm
  have hw : σ.wallSide 1 z ^ 2 = (exp (-((σ.θ₃ : ℂ) * I)) * z).im ^ 2 := by
    rw [wallSide_one_eq_neg_im_sph]
    ring
  rw [← norm_exp_neg_mul_sph z] at h1
  rw [sphCanon, sphCanon, canon_add_aux_sph (t := σ.sphTOneThree)
    (by linear_combination sphTau_oplus_onethree hs)
    (one_add_sphDist_mul_pos hs 2 z).ne' (one_add_sphDist_mul_pos hs 0 z).ne', hd0, hd2,
    pair_identity_sph h1 h2 h3, hw]

theorem norm_rotOne_eq_sphMoeb_rotTwo {z : ℂ} (h1 : 1 + conj σ.vertexOne * z ≠ 0)
    (h2 : 1 + conj σ.vertexTwo * z ≠ 0) :
    ‖σ.rotOne z‖ = ‖sphMoeb σ.sphTOneTwo (σ.rotTwo z)‖ := by
  rw [rotOne_eq_rotTwo_sph hs h1 h2, norm_neg, norm_mul, norm_exp_mul_I_sph', one_mul]

theorem sphCanon_add_two {z : ℂ} (h1 : 1 + conj σ.vertexOne * z ≠ 0)
    (h2 : 1 + conj σ.vertexTwo * z ≠ 0) (h3 : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re)
    (h4 : 0 < 1 + σ.sphTOneTwo * (σ.rotTwo z).re) (h5 : 0 < sphPairNum σ.sphTOneTwo (σ.rotTwo z)) :
    σ.sphCanon 1 z + σ.sphCanon 0 z = (1 - σ.sphTau 1 * σ.sphTau 0) *
      ((σ.rotTwo z).im ^ 2 * sphPairQ σ.sphTOneTwo (σ.rotTwo z)) /
        ((1 + σ.sphDist 1 z * σ.sphTau 1) * (1 + σ.sphDist 0 z * σ.sphTau 0)) := by
  have hd0 : σ.sphDist 0 z = ‖sphMoeb σ.sphTOneTwo (σ.rotTwo z)‖ :=
    norm_rotOne_eq_sphMoeb_rotTwo hs h1 h2
  have hd1 : σ.sphDist 1 z = ‖σ.rotTwo z‖ := rfl
  rw [sphCanon, sphCanon, canon_add_aux_sph (t := σ.sphTOneTwo)
    (by linear_combination sphTau_oplus_onetwo hs)
    (one_add_sphDist_mul_pos hs 1 z).ne' (one_add_sphDist_mul_pos hs 0 z).ne', hd0, hd1,
    pair_identity_sph h3 h4 h5]


theorem re_le_of_wall_zero_sph {z : ℂ} (hz : z ∈ σ.triangle) (hY : z.im = 0) :
    z.re ≤ σ.sphTTwoThree := by
  have hs2 := (sector_two_sph hs hz).1
  rw [rotTwo_apply_sph hs, vertexTwo_eq_sph, eq_ofReal_re_of_im_sph hY] at hs2
  have e : -(exp ((σ.θ₂ : ℂ) * I) * ((z.re : ℂ) - σ.sphTTwoThree) / (1 + σ.sphTTwoThree * z.re)) =
      -(exp ((σ.θ₂ : ℂ) * I) * (((z.re - σ.sphTTwoThree) / (1 + σ.sphTTwoThree * z.re) : ℝ) : ℂ)) :=
          by
    push_cast
    ring
  rw [e, neg_im, mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, ofReal_re,
    ofReal_im, mul_zero, zero_add] at hs2
  have hpos : 0 < 1 + σ.sphTTwoThree * z.re := by
    have := mul_nonneg (tTwoThree_pos_sph hs).le (re_nonneg_of_mem_sph hs hz)
    linarith
  have hsin := σ.sin_θ₂_pos_sph
  have : (z.re - σ.sphTTwoThree) / (1 + σ.sphTTwoThree * z.re) ≤ 0 := by
    by_contra h
    push Not at h
    nlinarith [mul_pos hsin h]
  rw [div_nonpos_iff] at this
  rcases this with ⟨-, h⟩ | ⟨h, -⟩
  · linarith
  · linarith

theorem conditions_zero_sph {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (h2 : z ≠ σ.vertexTwo) :
    0 < ‖z‖ + z.re ∧ 0 < 1 + σ.sphTTwoThree * z.re ∧ 0 < sphPairNum σ.sphTTwoThree z ∧
      0 < sphPairQ σ.sphTTwoThree z := by
  refine pair_conditions_sph (tTwoThree_pos_sph hs) (tTwoThree_le_one_sph hs) (re_nonneg_of_mem_sph
      hs hz) h0
    (by rwa [← vertexTwo_eq_sph]) fun hY => re_le_of_wall_zero_sph hs hz hY

theorem re_exp_neg_mul_nonneg_sph {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ (exp (-((σ.θ₃ : ℂ) * I)) * z).re := by
  rw [exp_neg_ofReal_mul_I_sph]
  simp only [mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg,
    Real.sin_neg]
  have := re_nonneg_of_mem_sph hs hz
  have := im_nonneg_of_mem_sph hs hz
  have := σ.cos_θ₃_nonneg_sph
  have := σ.sin_θ₃_pos_sph
  nlinarith

theorem re_le_of_wall_one_sph {z : ℂ} (hz : z ∈ σ.triangle)
    (hY : (exp (-((σ.θ₃ : ℂ) * I)) * z).im = 0) :
    (exp (-((σ.θ₃ : ℂ) * I)) * z).re ≤ σ.sphTOneThree := by
  have hr := re_rotOne_nonneg_sph hs hz
  rw [rotOne_eq_neg_sphMoeb hs, eq_ofReal_re_of_im_sph hY, sphMoeb_ofReal, neg_re, ofReal_re] at hr
  have hpos : 0 < 1 + σ.sphTOneThree * (exp (-((σ.θ₃ : ℂ) * I)) * z).re := by
    have := mul_nonneg (tOneThree_pos_sph hs).le (re_exp_neg_mul_nonneg_sph hs hz)
    linarith
  have : ((exp (-((σ.θ₃ : ℂ) * I)) * z).re - σ.sphTOneThree) /
      (1 + σ.sphTOneThree * (exp (-((σ.θ₃ : ℂ) * I)) * z).re) ≤ 0 := by linarith
  rw [div_nonpos_iff] at this
  rcases this with ⟨-, h⟩ | ⟨h, -⟩
  · linarith
  · linarith

theorem conditions_one_sph {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (h1 : z ≠ σ.vertexOne) :
    0 < ‖z‖ + (exp (-((σ.θ₃ : ℂ) * I)) * z).re ∧
      0 < 1 + σ.sphTOneThree * (exp (-((σ.θ₃ : ℂ) * I)) * z).re ∧
      0 < sphPairNum σ.sphTOneThree (exp (-((σ.θ₃ : ℂ) * I)) * z) ∧
      0 < sphPairQ σ.sphTOneThree (exp (-((σ.θ₃ : ℂ) * I)) * z) := by
  have hne0 : exp (-((σ.θ₃ : ℂ) * I)) * z ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) h0
  have hnet : exp (-((σ.θ₃ : ℂ) * I)) * z ≠ σ.sphTOneThree := by
    intro h
    apply h1
    rw [vertexOne_eq_sph, ← h]
    have := exp_mul_exp_neg_sph σ.θ₃
    linear_combination (-z) * this
  rw [← norm_exp_neg_mul_sph z]
  exact pair_conditions_sph (tOneThree_pos_sph hs) (tOneThree_le_one_sph hs)
    (re_exp_neg_mul_nonneg_sph hs hz) hne0 hnet fun hY => re_le_of_wall_one_sph hs hz hY

theorem rotTwo_ne_zero_sph {z : ℂ} (hz : 1 + σ.vertexTwo * z ≠ 0) (h2 : z ≠ σ.vertexTwo) :
    σ.rotTwo z ≠ 0 := by
  rw [rotTwo_eq_mul_sph hs]
  refine mul_ne_zero (neg_ne_zero.2 (Complex.exp_ne_zero _)) (div_ne_zero (sub_ne_zero.2 h2) ?_)
  rwa [conj_vertexTwo_sph]

theorem rotTwo_ne_tOneTwo_sph {z : ℂ} (hz : 1 + σ.vertexTwo * z ≠ 0) (h1 : z ≠ σ.vertexOne) :
    σ.rotTwo z ≠ σ.sphTOneTwo := by
  intro h
  apply h1
  rw [← rotTwo_vertexOne_sph hs, rotTwo_eq_mul_sph hs, rotTwo_eq_mul_sph hs] at h
  have h' := mul_left_cancel₀ (neg_ne_zero.2 (Complex.exp_ne_zero _)) h
  have e1 := sphMoebInv_sphMoeb (a := σ.vertexTwo) (z := z) (by rwa [conj_vertexTwo_sph])
  have e2 := sphMoebInv_sphMoeb (a := σ.vertexTwo) (z := σ.vertexOne)
    (by rw [conj_vertexTwo_sph]; exact one_add_vertexTwo_mul_vertexOne_ne_sph hs)
  rw [← e1, ← e2, h']

theorem re_le_of_wall_two_sph {z : ℂ} (hz : z ∈ σ.triangle) (hY : (σ.rotTwo z).im = 0) :
    (σ.rotTwo z).re ≤ σ.sphTOneTwo := by
  have hc1 := one_add_conj_vertexOne_ne_sph hs hz
  have hc2 : 1 + conj σ.vertexTwo * z ≠ 0 := by
    rw [conj_vertexTwo_sph]
    exact one_add_vertexTwo_ne_sph hs hz
  have hr := (sector_one_sph hs hz).1
  rw [rotOne_eq_rotTwo_sph hs hc1 hc2, eq_ofReal_re_of_im_sph hY, sphMoeb_ofReal, neg_im, mul_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, ofReal_re, ofReal_im, mul_zero,
    zero_add] at hr
  have hpos : 0 < 1 + σ.sphTOneTwo * (σ.rotTwo z).re := by
    have := mul_nonneg (tOneTwo_pos_sph hs).le (re_rotTwo_nonneg_sph hs hz)
    linarith
  have hsin := σ.sin_θ₁_pos_sph
  have : ((σ.rotTwo z).re - σ.sphTOneTwo) / (1 + σ.sphTOneTwo * (σ.rotTwo z).re) ≤ 0 := by
    by_contra h
    push Not at h
    nlinarith [mul_pos hsin h]
  rw [div_nonpos_iff] at this
  rcases this with ⟨-, h⟩ | ⟨h, -⟩
  · linarith
  · linarith

theorem conditions_two_sph {z : ℂ} (hz : z ∈ σ.triangle) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) :
    0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re ∧ 0 < 1 + σ.sphTOneTwo * (σ.rotTwo z).re ∧
      0 < sphPairNum σ.sphTOneTwo (σ.rotTwo z) ∧ 0 < sphPairQ σ.sphTOneTwo (σ.rotTwo z) := by
  have hz2 := one_add_vertexTwo_ne_sph hs hz
  exact pair_conditions_sph (tOneTwo_pos_sph hs) (tOneTwo_le_one_sph hs) (re_rotTwo_nonneg_sph hs
      hz)
    (rotTwo_ne_zero_sph hs hz2 h2) (rotTwo_ne_tOneTwo_sph hs hz2 h1) fun hY => re_le_of_wall_two_sph
        hs hz hY


theorem sphCanon_add_zero_wall {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 0 z = 0) :
    σ.sphCanon 2 z + σ.sphCanon 1 z = 0 := by
  have hd1 : σ.sphDist 1 z = ‖sphMoeb σ.sphTTwoThree z‖ := by
    change ‖σ.rotTwo z‖ = _
    rw [norm_rotTwo_sph hs, vertexTwo_eq_sph]
  have hd2 : σ.sphDist 2 z = ‖z‖ := rfl
  rw [sphCanon, sphCanon, canon_add_aux_sph (t := σ.sphTTwoThree)
    (by linear_combination sphTau_oplus_twothree hs)
    (one_add_sphDist_mul_pos hs 2 z).ne' (one_add_sphDist_mul_pos hs 1 z).ne', hd1, hd2,
    pair_wall_sph (tTwoThree_pos_sph hs) hw (re_nonneg_of_mem_sph hs hz) (re_le_of_wall_zero_sph hs
        hz hw)]
  simp

theorem sphCanon_add_one_wall {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 1 z = 0) :
    σ.sphCanon 2 z + σ.sphCanon 0 z = 0 := by
  have hY : (exp (-((σ.θ₃ : ℂ) * I)) * z).im = 0 := by
    rw [wallSide_one_eq_neg_im_sph] at hw
    linarith
  have hd0 : σ.sphDist 0 z = ‖sphMoeb σ.sphTOneThree (exp (-((σ.θ₃ : ℂ) * I)) * z)‖ := by
    change ‖σ.rotOne z‖ = _
    rw [rotOne_eq_neg_sphMoeb hs, norm_neg]
  have hd2 : σ.sphDist 2 z = ‖exp (-((σ.θ₃ : ℂ) * I)) * z‖ := (norm_exp_neg_mul_sph z).symm
  rw [sphCanon, sphCanon, canon_add_aux_sph (t := σ.sphTOneThree)
    (by linear_combination sphTau_oplus_onethree hs)
    (one_add_sphDist_mul_pos hs 2 z).ne' (one_add_sphDist_mul_pos hs 0 z).ne', hd0, hd2,
    pair_wall_sph (tOneThree_pos_sph hs) hY (re_exp_neg_mul_nonneg_sph hs hz) (re_le_of_wall_one_sph
        hs hz hY)]
  simp

theorem sphCanon_add_two_wall {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 2 z = 0) :
    σ.sphCanon 1 z + σ.sphCanon 0 z = 0 := by
  have hz2 := one_add_vertexTwo_ne_sph hs hz
  have hY : (σ.rotTwo z).im = 0 := by
    rw [wallSide_two_eq_sph hs] at hw
    exact (mul_eq_zero.1 hw).resolve_right (Complex.normSq_pos.2 hz2).ne'
  have hc2 : 1 + conj σ.vertexTwo * z ≠ 0 := by rwa [conj_vertexTwo_sph]
  have hd0 : σ.sphDist 0 z = ‖sphMoeb σ.sphTOneTwo (σ.rotTwo z)‖ :=
    norm_rotOne_eq_sphMoeb_rotTwo hs (one_add_conj_vertexOne_ne_sph hs hz) hc2
  have hd1 : σ.sphDist 1 z = ‖σ.rotTwo z‖ := rfl
  rw [sphCanon, sphCanon, canon_add_aux_sph (t := σ.sphTOneTwo)
    (by linear_combination sphTau_oplus_onetwo hs)
    (one_add_sphDist_mul_pos hs 1 z).ne' (one_add_sphDist_mul_pos hs 0 z).ne', hd0, hd1,
    pair_wall_sph (tOneTwo_pos_sph hs) hY (re_rotTwo_nonneg_sph hs hz) (re_le_of_wall_two_sph hs hz
        hY)]
  simp

theorem sphCanon_refl_zero_one (z : ℂ) : σ.sphCanon 1 (σ.refl 0 z) = σ.sphCanon 1 z := by
  refine sphCanon_congr ?_
  change ‖σ.rotTwo (σ.refl 0 z)‖ = ‖σ.rotTwo z‖
  rw [norm_rotTwo_sph hs, norm_rotTwo_sph hs, norm_sphMoeb_vertexTwo_refl_zero]

theorem sphCanon_refl_one_zero (z : ℂ) : σ.sphCanon 0 (σ.refl 1 z) = σ.sphCanon 0 z := by
  refine sphCanon_congr ?_
  change ‖σ.rotOne (σ.refl 1 z)‖ = ‖σ.rotOne z‖
  rw [norm_rotOne_sph hs, norm_rotOne_sph hs, norm_sphMoeb_vertexOne_refl_one]

theorem sphCanon_refl_two_one {z : ℂ} (hz : z ∈ σ.reflChart 2) :
    σ.sphCanon 1 (σ.refl 2 z) = σ.sphCanon 1 z := by
  refine sphCanon_congr ?_
  change ‖σ.rotTwo (σ.refl 2 z)‖ = ‖σ.rotTwo z‖
  rw [norm_rotTwo_sph hs, norm_rotTwo_sph hs, norm_sphMoeb_vertexTwo_refl_two hs hz]

theorem sphCanon_refl_two_zero {z : ℂ} (hz : z ∈ σ.reflChart 2)
    (h1 : 1 + conj σ.vertexOne * z ≠ 0) : σ.sphCanon 0 (σ.refl 2 z) = σ.sphCanon 0 z := by
  refine sphCanon_congr ?_
  change ‖σ.rotOne (σ.refl 2 z)‖ = ‖σ.rotOne z‖
  rw [norm_rotOne_sph hs, norm_rotOne_sph hs, norm_sphMoeb_vertexOne_refl_two hs hz h1]

end Spherical

end CompactShape

end GC.Seifert
