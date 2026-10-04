import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldOneConeAssembly

/-!
# The image of the triangle under the assembled cone fold

Lane A4b2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §6, "separation
is structural"). On the triangle `T` of a one-cone shape every branch of `foldE p` has an
explicit image region:
* on `R₂ = {η₀ < h}`: `‖E - 3/2‖ = G(η₀) < G(h)` (`foldE_image_zero`);
* on `R₁ = {η₁ < h}`: `‖E + 3/2‖ = coneRadial η₁ < G(h)` (`foldE_image_cone`);
* on the lens: `‖E - 3/2‖ = G(η₀) ≥ G(h)`, `‖E + 3/2‖ = G(η₁) ≥ G(h)`, `‖E‖ < 2`
  (`foldE_image_lens`);
* elsewhere: `‖E‖ = outerProfile y > 2`, `‖E ∓ 3/2‖ ≥ G(h)` (`foldE_image_inf`; for `y ≤ Y₁` the
  angle of `E` lies between those of the wall-0 and wall-1 bridges, and `|R e^{iA} ∓ 3/2|` is
  monotone in `A ∈ [0, π]`; above `Y₁` the outer profile exceeds `3/2 + G(Y₁)`).
In all cases `Im E ≥ 0` (the angles lie in `[0, π]`), `‖E‖ < 3` and `‖E - 3/2‖ > 1/2`
(`foldE_mem_target`). Since `G(h) < 3/2` the four regions are pairwise disjoint.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem halfArg_mem_Ico {S R J : ℝ} (hJ : 0 ≤ J) (hSR : 0 < S + R) :
    0 ≤ halfArg S R J ∧ halfArg S R J < Real.pi := by
  unfold halfArg
  have h1 : 0 ≤ J / (S + R) := div_nonneg hJ hSR.le
  have h2 := Real.arctan_lt_pi_div_two (J / (S + R))
  have h3 : 0 ≤ Real.arctan (J / (S + R)) := Real.arctan_nonneg.2 h1
  constructor <;> linarith

theorem negHalfArg_mem_Ioc {S R J : ℝ} (hJ : 0 ≤ J) (hSR : 0 < S - R) :
    0 < negHalfArg S R J ∧ negHalfArg S R J ≤ Real.pi := by
  unfold negHalfArg
  have h1 : 0 ≤ J / (S - R) := div_nonneg hJ hSR.le
  have h2 := Real.arctan_lt_pi_div_two (J / (S - R))
  have h3 : 0 ≤ Real.arctan (J / (S - R)) := Real.arctan_nonneg.2 h1
  constructor <;> linarith

theorem twoCircle_im_nonneg {a b A B w P : ℝ} (hw : 0 ≤ w) : 0 ≤ (twoCircle a b A B w P).im := by
  simp only [twoCircle, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one,
    zero_add]
  have := Real.sqrt_nonneg P
  positivity

theorem norm_ofReal_mul_exp (S θ : ℝ) (hS : 0 ≤ S) : ‖(S : ℂ) * exp ((θ : ℂ) * I)‖ = S := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hS]

theorem im_ofReal_mul_exp_nonneg {S θ : ℝ} (hS : 0 ≤ S) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi) :
    0 ≤ ((S : ℂ) * exp ((θ : ℂ) * I)).im := by
  rw [im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  exact mul_nonneg hS (Real.sin_nonneg_of_nonneg_of_le_pi h0 h1)

theorem normSq_polar_sub (R c θ : ℝ) :
    ‖(R : ℂ) * exp ((θ : ℂ) * I) - c‖ ^ 2 = R ^ 2 - 2 * c * R * Real.cos θ + c ^ 2 := by
  rw [Complex.sq_norm, normSq_apply]
  simp only [sub_re, sub_im, re_ofReal_mul, im_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, ofReal_re, ofReal_im, sub_zero]
  have := Real.sin_sq_add_cos_sq θ
  linear_combination R ^ 2 * this

namespace ConeShape

variable (σ : ConeShape)

/-! ### Angle ranges on the triangle -/

theorem bridgeZero_im_nonneg {z : ℂ} (hx : 0 ≤ z.re) : 0 ≤ (σ.bridgeZero z).im :=
  twoCircle_im_nonneg hx

theorem bridgeOne_im_nonneg {z : ℂ} (hw : 0 ≤ σ.wallOne z) : 0 ≤ (σ.bridgeOne z).im :=
  twoCircle_im_nonneg hw

theorem bridgeTwo_im_nonneg {z : ℂ} (hw : 0 ≤ σ.wallTwo z) : 0 ≤ (σ.bridgeTwo z).im :=
  twoCircle_im_nonneg hw

theorem angleZeroHole_mem {z : ℂ} (hz : 0 < z.im) (hx : 0 ≤ z.re) :
    0 ≤ σ.angleZeroHole z ∧ σ.angleZeroHole z < Real.pi :=
  halfArg_mem_Ico (σ.bridgeZero_im_nonneg hx) (σ.three_halves_hole_pos hz)

theorem angleTwoHole_mem (hθ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.domTwo) (hw : 0 ≤ σ.wallTwo z) :
    0 < σ.angleTwoHole z ∧ σ.angleTwoHole z ≤ Real.pi :=
  negHalfArg_mem_Ioc (σ.bridgeTwo_im_nonneg hw) (σ.bridgeTwo_hole_pos hθ hz)

theorem angleHole_mem (hθ : σ.θ₂ = 0) (a b : ℝ) {z : ℂ} (hz : z ∈ σ.domTwo) (hx : 0 ≤ z.re)
    (hw : 0 ≤ σ.wallTwo z) : 0 ≤ σ.angleHole a b z ∧ σ.angleHole a b z ≤ Real.pi := by
  have h1 := σ.angleZeroHole_mem hz.1 hx
  have h2 := σ.angleTwoHole_mem hθ hz hw
  have hw0 := coneStep_nonneg a b (horoX z)
  have hw1 := coneStep_le_one a b (horoX z)
  unfold angleHole
  constructor <;> nlinarith

theorem angleOneCone_mem {z : ℂ} (hz : z ∈ σ.domOne) (hw : 0 ≤ σ.wallOne z) :
    0 < σ.angleOneCone z ∧ σ.angleOneCone z ≤ Real.pi := by
  have hp := σ.bridgeOne_cone_pos hz
  rw [sub_neg_eq_add] at hp
  exact negHalfArg_mem_Ioc (σ.bridgeOne_im_nonneg hw) hp

theorem angleTwoCone_mem (hθ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.domTwo) (hw : 0 ≤ σ.wallTwo z) :
    0 ≤ σ.angleTwoCone z ∧ σ.angleTwoCone z < Real.pi := by
  have hp := σ.bridgeTwo_cone_pos hθ hz
  rw [sub_neg_eq_add] at hp
  exact halfArg_mem_Ico (σ.bridgeTwo_im_nonneg hw) hp

theorem angleCone_mem (hθ : σ.θ₂ = 0) {p : ℕ} (hp : σ.θ₁ * p = Real.pi) (a b φa φb : ℝ) {z : ℂ}
    (hz1 : z ∈ σ.domOne) (hz2 : z ∈ σ.domTwo) (hw1 : 0 ≤ σ.wallOne z) (hw2 : 0 ≤ σ.wallTwo z)
    (hφ : 0 ≤ discAngle (σ.discOne z) ∧ discAngle (σ.discOne z) ≤ σ.θ₁) :
    0 ≤ σ.angleCone p a b φa φb z ∧ σ.angleCone p a b φa φb z ≤ Real.pi := by
  have h1 := σ.angleOneCone_mem hz1 hw1
  have h2 := σ.angleTwoCone_mem hθ hz2 hw2
  have hl0 := coneStep_nonneg φa φb (discAngle (σ.discOne z))
  have hl1 := coneStep_le_one φa φb (discAngle (σ.discOne z))
  have ht0 := coneStep_nonneg a b (σ.etaOne z)
  have ht1 := coneStep_le_one a b (σ.etaOne z)
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have ha0 : 0 ≤ Real.pi - p * discAngle (σ.discOne z) := by
    have : (p : ℝ) * discAngle (σ.discOne z) ≤ p * σ.θ₁ := mul_le_mul_of_nonneg_left hφ.2 hp0
    linarith [mul_comm σ.θ₁ (p : ℝ)]
  have ha1 : Real.pi - p * discAngle (σ.discOne z) ≤ Real.pi := by
    have := mul_nonneg hp0 hφ.1
    linarith
  have hB : 0 ≤ σ.angleConeBlend φa φb z ∧ σ.angleConeBlend φa φb z ≤ Real.pi := by
    unfold angleConeBlend coneLambda
    constructor <;> nlinarith
  unfold angleCone
  constructor <;> nlinarith

theorem angleInfW_mem {ν : ℂ → ℝ} {z : ℂ} (hz : z ∈ σ.domOne) (hx : 0 ≤ z.re)
    (hw : 0 ≤ σ.wallOne z) (h0 : 0 ≤ ν z) (h1 : ν z ≤ 1) :
    0 ≤ σ.angleZeroInf z ∧ σ.angleZeroInf z ≤ σ.angleInfW ν z ∧
      σ.angleInfW ν z ≤ σ.angleOneInf z ∧ σ.angleOneInf z ≤ Real.pi := by
  have ha := σ.angleZeroInf_nonneg hz.1 hx
  have hb := σ.angleOneInf_le_pi hz hw
  have hm1 := σ.angleZeroInf_mem hz.1
  have hm2 := σ.angleOneInf_mem hz
  have hab : σ.angleZeroInf z ≤ σ.angleOneInf z := by linarith [hm1.2, hm2.1]
  unfold angleInfW
  refine ⟨ha, ?_, ?_, hb⟩ <;> nlinarith

/-! ### The branches of `foldE` on the triangle -/

section Branches

variable (hθ : σ.θ₂ = 0) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)

theorem foldE_of_zero {p : ℕ} {z : ℂ} (h0 : cuspZeroHeight z < σ.foldH) :
    σ.foldE p z = σ.cornerZero σ.foldA₀ σ.foldB₀ z := by
  simp only [foldE, h0, ↓reduceIte]

include hθ h₁ in
theorem foldE_of_cone {p : ℕ} (hp : 1 ≤ p) {z : ℂ} (hz : z ∈ σ.triangle)
    (h1 : σ.etaOne z < σ.foldH) :
    σ.foldE p z = σ.cornerCone p σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB z := by
  have h₂ := σ.adm_two_of_cusp hθ
  have h0 := σ.foldH_lt_cuspZeroHeight_of_etaOne_le hθ hz.1 h1.le
  by_cases ha : σ.etaOne z < σ.foldA₁
  · simp only [foldE, not_lt.2 h0.le, ha, ↓reduceIte]
    have hpos : z = σ.vertexOne ∨ z ∈ σ.domOne := by
      by_cases hzv : z = σ.vertexOne
      · exact Or.inl hzv
      · exact Or.inr (σ.mem_domOne_of_mem_triangle hz hzv)
    exact (σ.cornerCone_eq_apex hp (σ.foldA₁_lt_foldB₁ h₁ h₂) hz.1 hpos ha.le).symm
  · simp only [foldE, not_lt.2 h0.le, ha, h1, ↓reduceIte]

include hθ h₁ in
theorem foldE_of_lens {p : ℕ} {z : ℂ} (h0 : σ.foldH ≤ cuspZeroHeight z)
    (h1 : σ.foldH ≤ σ.etaOne z) (hL : |σ.sinhN z| < 1 / 10) : σ.foldE p z = σ.bridgeTwo z := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hAH : σ.foldA₁ < σ.foldH :=
    lt_trans (σ.foldA₁_lt_foldB₁ h₁ h₂) (σ.foldB₁_lt_foldH h₁ h₂)
  simp only [foldE, not_lt.2 h0, not_lt.2 (le_trans hAH.le h1), not_lt.2 h1, hL, ↓reduceIte]

include hθ h₁ in
theorem foldE_of_inf {p : ℕ} {z : ℂ} (h0 : σ.foldH ≤ cuspZeroHeight z)
    (h1 : σ.foldH ≤ σ.etaOne z) (hL : 1 / 10 ≤ |σ.sinhN z|) :
    σ.foldE p z = σ.cornerInfW σ.blendWeight σ.foldY₁ σ.foldY₂ z := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hAH : σ.foldA₁ < σ.foldH :=
    lt_trans (σ.foldA₁_lt_foldB₁ h₁ h₂) (σ.foldB₁_lt_foldH h₁ h₂)
  simp only [foldE, not_lt.2 h0, not_lt.2 (le_trans hAH.le h1), not_lt.2 h1, not_lt.2 hL,
    ↓reduceIte]

/-! ### Image regions -/

theorem coneProfile_foldH_lt : coneProfile σ.constK σ.foldH < 3 / 2 := by
  have := (coneProfile_lt_three_halves_iff σ.constK_pos σ.foldH_pos.le).2 σ.foldH_lt_sqrt
  exact this

theorem half_lt_coneProfile_foldH : 1 / 2 < coneProfile σ.constK σ.foldH :=
  half_lt_coneProfile σ.constK_pos σ.foldH_pos.ne'

include hθ h₁ in
theorem foldE_image_zero {p : ℕ} {z : ℂ} (hz : z ∈ σ.triangle)
    (h0 : cuspZeroHeight z < σ.foldH) :
    ‖σ.foldE p z - 3 / 2‖ = coneProfile σ.constK (cuspZeroHeight z) ∧
      coneProfile σ.constK (cuspZeroHeight z) < coneProfile σ.constK σ.foldH ∧
      0 ≤ (σ.foldE p z).im := by
  have hzv := σ.ne_vertexOne_of_cuspZeroHeight_le hθ h₁ h0.le
  have hz2 := σ.mem_domTwo_of_mem_triangle hz hzv
  have hA := σ.angleHole_mem hθ σ.foldA₀ σ.foldB₀ hz2 (σ.re_nonneg_of_triangle hz)
    (σ.wallTwo_nonneg_of_mem_triangle hz)
  have hG := σ.holeModulus_pos z
  rw [σ.foldE_of_zero h0]
  refine ⟨?_, (coneProfile_lt_iff σ.constK_pos (cuspZeroHeight_pos hz.1).le
    σ.foldH_pos.le).2 h0, ?_⟩
  · rw [cornerZero, add_sub_cancel_left, norm_ofReal_mul_exp _ _ hG.le]
  · rw [cornerZero, add_im, show (3 / 2 : ℂ).im = 0 by norm_num, zero_add]
    exact im_ofReal_mul_exp_nonneg hG.le hA.1 hA.2

theorem coneRadial_lt_foldH {p : ℕ} (hp : 1 ≤ p) {η : ℝ} (hη : σ.vertexOne.im ≤ η)
    (hηh : η < σ.foldH) :
    0 ≤ coneRadial p σ.foldA₁ σ.foldB₁ σ.vertexOne.im σ.constK η ∧
      coneRadial p σ.foldA₁ σ.foldB₁ σ.vertexOne.im σ.constK η < coneProfile σ.constK σ.foldH := by
  have hv := σ.vertexOne_im_pos
  have hη0 : 0 < η := by linarith
  have hϖ0 : 0 ≤ (η - σ.vertexOne.im) / (η + σ.vertexOne.im) := div_nonneg (by linarith)
    (by linarith)
  have hϖ1 : (η - σ.vertexOne.im) / (η + σ.vertexOne.im) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  have hpow : ((η - σ.vertexOne.im) / (η + σ.vertexOne.im)) ^ p < 1 :=
    pow_lt_one₀ hϖ0 hϖ1 (by omega)
  have hpow0 : 0 ≤ ((η - σ.vertexOne.im) / (η + σ.vertexOne.im)) ^ p := pow_nonneg hϖ0 p
  have hGh := σ.half_lt_coneProfile_foldH
  have hGη : coneProfile σ.constK η < coneProfile σ.constK σ.foldH :=
    (coneProfile_lt_iff σ.constK_pos hη0.le σ.foldH_pos.le).2 hηh
  have hG0 := half_le_coneProfile σ.constK_pos η
  have ht0 := coneStep_nonneg σ.foldA₁ σ.foldB₁ η
  have ht1 := coneStep_le_one σ.foldA₁ σ.foldB₁ η
  unfold coneRadial
  constructor
  · have : 0 ≤ (1 - coneStep σ.foldA₁ σ.foldB₁ η) *
        ((η - σ.vertexOne.im) / (η + σ.vertexOne.im)) ^ p := mul_nonneg (by linarith) hpow0
    nlinarith
  · nlinarith

include hθ h₁ in
theorem foldE_image_cone {p : ℕ} (hp : 1 ≤ p) (hpθ : σ.θ₁ * p = Real.pi) {z : ℂ}
    (hz : z ∈ σ.triangle) (h1 : σ.etaOne z < σ.foldH) :
    ‖σ.foldE p z + 3 / 2‖ = coneRadial p σ.foldA₁ σ.foldB₁ σ.vertexOne.im σ.constK (σ.etaOne z) ∧
      ‖σ.foldE p z + 3 / 2‖ < coneProfile σ.constK σ.foldH ∧ 0 ≤ (σ.foldE p z).im := by
  have hge : σ.vertexOne.im ≤ σ.etaOne z := coneHeight_ge σ.vertexOne_im_pos hz.1
  obtain ⟨hS0, hS1⟩ := σ.coneRadial_lt_foldH hp hge h1
  have hnorm : ‖σ.foldE p z + 3 / 2‖ =
      coneRadial p σ.foldA₁ σ.foldB₁ σ.vertexOne.im σ.constK (σ.etaOne z) := by
    rw [σ.foldE_of_cone hθ h₁ hp hz h1, cornerCone, neg_add_cancel_comm,
      norm_ofReal_mul_exp _ _ hS0]
  refine ⟨hnorm, hnorm ▸ hS1, ?_⟩
  rw [σ.foldE_of_cone hθ h₁ hp hz h1, cornerCone, add_im]
  by_cases hzv : z = σ.vertexOne
  · subst hzv
    have : coneRadial p σ.foldA₁ σ.foldB₁ σ.vertexOne.im σ.constK (σ.etaOne σ.vertexOne) = 0 := by
      rw [σ.etaOne_vertexOne]
      unfold coneRadial
      have h₂ := σ.adm_two_of_cusp hθ
      rw [coneStep_eq_zero (σ.foldA₁_lt_foldB₁ h₁ h₂) (σ.vertexOne_im_lt_foldA₁ h₁ h₂).le]
      simp [zero_pow (by omega : p ≠ 0)]
    rw [this]
    simp
  · have hz1 := σ.mem_domOne_of_mem_triangle hz hzv
    have hz2 := σ.mem_domTwo_of_mem_triangle hz hzv
    have hA := σ.angleCone_mem hθ hpθ σ.foldA₁ σ.foldB₁ σ.foldPhiA σ.foldPhiB hz1 hz2
      (σ.wallOne_nonneg_of_mem_triangle hz) (σ.wallTwo_nonneg_of_mem_triangle hz)
      (σ.discAngle_mem_of_mem_triangle hz hzv)
    rw [show (-(3 / 2 : ℂ)).im = 0 by norm_num, zero_add]
    exact im_ofReal_mul_exp_nonneg hS0 hA.1 hA.2

include hθ h₁ in
theorem foldE_image_lens {p : ℕ} {z : ℂ} (hz : z ∈ σ.triangle)
    (h0 : σ.foldH ≤ cuspZeroHeight z) (h1 : σ.foldH ≤ σ.etaOne z) (hL : |σ.sinhN z| < 1 / 10) :
    ‖σ.foldE p z - 3 / 2‖ = coneProfile σ.constK (cuspZeroHeight z) ∧
      ‖σ.foldE p z + 3 / 2‖ = coneProfile σ.constK (σ.etaOne z) ∧
      coneProfile σ.constK σ.foldH ≤ coneProfile σ.constK (cuspZeroHeight z) ∧
      coneProfile σ.constK σ.foldH ≤ coneProfile σ.constK (σ.etaOne z) ∧
      ‖σ.foldE p z‖ < 2 ∧ 0 ≤ (σ.foldE p z).im := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hAH : σ.foldA₁ < σ.foldH :=
    lt_trans (σ.foldA₁_lt_foldB₁ h₁ h₂) (σ.foldB₁_lt_foldH h₁ h₂)
  have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (le_trans hAH.le h1)
  have hz2 := σ.mem_domTwo_of_mem_triangle hz hzv
  have hH := σ.foldH_pos
  rw [σ.foldE_of_lens hθ h₁ h0 h1 hL]
  exact ⟨σ.norm_bridgeTwo_sub hθ hz2, σ.norm_bridgeTwo_add hθ hz2,
    (coneProfile_le_iff σ.constK_pos hH.le (by linarith)).2 h0,
    (coneProfile_le_iff σ.constK_pos hH.le (by linarith)).2 h1,
    σ.norm_bridgeTwo_lt_two hθ hz2, σ.bridgeTwo_im_nonneg (σ.wallTwo_nonneg_of_mem_triangle hz)⟩

include hθ h₁ in
theorem foldE_image_inf {p : ℕ} {z : ℂ} (hz : z ∈ σ.triangle)
    (h0 : σ.foldH ≤ cuspZeroHeight z) (h1 : σ.foldH ≤ σ.etaOne z) (hL : 1 / 10 ≤ |σ.sinhN z|) :
    ‖σ.foldE p z‖ = outerProfile σ.constK σ.foldY₁ σ.foldY₂ z.im ∧
      coneProfile σ.constK σ.foldH ≤ ‖σ.foldE p z - 3 / 2‖ ∧
      coneProfile σ.constK σ.foldH ≤ ‖σ.foldE p z + 3 / 2‖ ∧ 0 ≤ (σ.foldE p z).im := by
  have h₂ := σ.adm_two_of_cusp hθ
  have hAH : σ.foldA₁ < σ.foldH :=
    lt_trans (σ.foldA₁_lt_foldB₁ h₁ h₂) (σ.foldB₁_lt_foldH h₁ h₂)
  have hzv := σ.ne_vertexOne_of_foldA₁_le h₁ h₂ (le_trans hAH.le h1)
  have hz1 := σ.mem_domOne_of_mem_triangle hz hzv
  have hK := σ.constK_pos
  have hH := σ.foldH_pos
  have hx := σ.re_nonneg_of_triangle hz
  have hw := σ.wallOne_nonneg_of_mem_triangle hz
  obtain ⟨hα0, hαA, hAΘ, hΘπ⟩ := σ.angleInfW_mem hz1 hx hw (σ.blendWeight_nonneg z)
    (σ.blendWeight_le_one z)
  set R := outerProfile σ.constK σ.foldY₁ σ.foldY₂ z.im with hR
  set A := σ.angleInfW σ.blendWeight z with hAdef
  have hR2 : 2 < R := two_lt_outerProfile hK σ.sqrt_constK_le_half
    (lt_trans σ.foldY₁_pos σ.foldY₁_lt_foldY₂) σ.foldY₂_lt_sqrt hz.1
  have hE : σ.foldE p z = (R : ℂ) * exp ((A : ℂ) * I) := by
    rw [σ.foldE_of_inf hθ h₁ h0 h1 hL]
    rfl
  have hGη₀ : coneProfile σ.constK σ.foldH ≤ coneProfile σ.constK (cuspZeroHeight z) :=
    (coneProfile_le_iff hK hH.le (by linarith)).2 h0
  have hGη₁ : coneProfile σ.constK σ.foldH ≤ coneProfile σ.constK (σ.etaOne z) :=
    (coneProfile_le_iff hK hH.le (by linarith)).2 h1
  have hGh := σ.coneProfile_foldH_lt
  have hnorm : ‖σ.foldE p z‖ = R := by rw [hE, norm_ofReal_mul_exp _ _ (by linarith)]
  have him : 0 ≤ (σ.foldE p z).im := by
    rw [hE]
    exact im_ofReal_mul_exp_nonneg (by linarith) (le_trans hα0 hαA) (le_trans hAΘ hΘπ)
  refine ⟨hnorm, ?_, ?_, him⟩
  · rw [hE]
    rcases le_or_gt z.im σ.foldY₁ with hy | hy
    · have hRy : R = 3 / 2 + coneProfile σ.constK z.im := outerProfile_of_le σ.foldY₁_lt_foldY₂ hy
      have hcos : Real.cos A ≤ Real.cos (σ.angleZeroInf z) :=
        Real.cos_le_cos_of_nonneg_of_le_pi hα0 (le_trans hAΘ hΘπ) hαA
      have hb := σ.norm_bridgeZero_sub hz.1
      rw [σ.bridgeZero_polar hz.1, ← hRy] at hb
      have e1 := normSq_polar_sub R (3 / 2) A
      have e2 := normSq_polar_sub R (3 / 2) (σ.angleZeroInf z)
      push_cast at e1 e2
      rw [hb] at e2
      have hRc : R * Real.cos A ≤ R * Real.cos (σ.angleZeroInf z) :=
        mul_le_mul_of_nonneg_left hcos (by linarith)
      have hsq : coneProfile σ.constK (cuspZeroHeight z) ^ 2 ≤
          ‖(R : ℂ) * exp ((A : ℂ) * I) - 3 / 2‖ ^ 2 := by
        rw [e1]; nlinarith
      have hG0 : 0 ≤ coneProfile σ.constK (cuspZeroHeight z) := by
        linarith [half_le_coneProfile hK (cuspZeroHeight z)]
      have h3 := (sq_le_sq₀ hG0 (norm_nonneg _)).1 hsq
      linarith
    · have hmono := outerProfile_mono hK σ.sqrt_constK_le_half σ.foldY₁_pos.le σ.foldY₁_lt_foldY₂
        σ.foldY₂_lt_sqrt (show σ.foldY₁ ∈ Set.Ioi 0 from σ.foldY₁_pos)
        (show z.im ∈ Set.Ioi 0 from hz.1) hy
      rw [outerProfile_of_le σ.foldY₁_lt_foldY₂ le_rfl] at hmono
      have hGY : coneProfile σ.constK σ.foldH < coneProfile σ.constK σ.foldY₁ :=
        (coneProfile_lt_iff hK hH.le σ.foldY₁_pos.le).2 σ.foldH_lt_foldY₁
      have h3 := norm_sub_norm_le ((R : ℂ) * exp ((A : ℂ) * I)) (3 / 2)
      rw [norm_ofReal_mul_exp _ _ (by linarith)] at h3
      norm_num at h3
      linarith
  · rw [hE]
    rcases le_or_gt z.im σ.foldY₁ with hy | hy
    · have hRy : R = 3 / 2 + coneProfile σ.constK z.im := outerProfile_of_le σ.foldY₁_lt_foldY₂ hy
      have hcos : Real.cos (σ.angleOneInf z) ≤ Real.cos A :=
        Real.cos_le_cos_of_nonneg_of_le_pi (le_trans hα0 hαA) hΘπ hAΘ
      have hb := σ.norm_bridgeOne_add hz1
      rw [σ.bridgeOne_polar hz1, ← hRy] at hb
      have e1 := normSq_polar_sub R (-(3 / 2)) A
      have e2 := normSq_polar_sub R (-(3 / 2)) (σ.angleOneInf z)
      rw [show (R : ℂ) * exp ((A : ℂ) * I) - ((-(3 / 2) : ℝ) : ℂ) =
        (R : ℂ) * exp ((A : ℂ) * I) + 3 / 2 by push_cast; ring] at e1
      rw [show (R : ℂ) * exp ((σ.angleOneInf z : ℂ) * I) - ((-(3 / 2) : ℝ) : ℂ) =
        (R : ℂ) * exp ((σ.angleOneInf z : ℂ) * I) + 3 / 2 by push_cast; ring, hb] at e2
      have hRc : R * Real.cos (σ.angleOneInf z) ≤ R * Real.cos A :=
        mul_le_mul_of_nonneg_left hcos (by linarith)
      have hsq : coneProfile σ.constK (σ.etaOne z) ^ 2 ≤
          ‖(R : ℂ) * exp ((A : ℂ) * I) + 3 / 2‖ ^ 2 := by
        rw [e1]; nlinarith
      have hG0 : 0 ≤ coneProfile σ.constK (σ.etaOne z) := by
        linarith [half_le_coneProfile hK (σ.etaOne z)]
      have h3 := (sq_le_sq₀ hG0 (norm_nonneg _)).1 hsq
      linarith
    · have hmono := outerProfile_mono hK σ.sqrt_constK_le_half σ.foldY₁_pos.le σ.foldY₁_lt_foldY₂
        σ.foldY₂_lt_sqrt (show σ.foldY₁ ∈ Set.Ioi 0 from σ.foldY₁_pos)
        (show z.im ∈ Set.Ioi 0 from hz.1) hy
      rw [outerProfile_of_le σ.foldY₁_lt_foldY₂ le_rfl] at hmono
      have hGY : coneProfile σ.constK σ.foldH < coneProfile σ.constK σ.foldY₁ :=
        (coneProfile_lt_iff hK hH.le σ.foldY₁_pos.le).2 σ.foldH_lt_foldY₁
      have h3 := norm_sub_norm_le ((R : ℂ) * exp ((A : ℂ) * I)) (-(3 / 2))
      rw [norm_ofReal_mul_exp _ _ (by linarith), sub_neg_eq_add] at h3
      norm_num at h3
      linarith

end Branches

end ConeShape

end GC.Seifert
