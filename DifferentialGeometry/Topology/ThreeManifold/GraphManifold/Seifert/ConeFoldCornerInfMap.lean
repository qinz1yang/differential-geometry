import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldCornerInf

/-!
# The corner map at the cusp `∞` of the `(p, ⊤, ⊤)` fold

Lane A4, tier 2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §5).
`angleInf x₁ x₂` blends `angleZeroInf` (near wall 0) and `angleOneInf` (near wall 1) with the step
`coneStep x₁ x₂` in `x`; `cornerInf x₁ x₂ Y₁ Y₂ z = R∞(y) e^{i angleInf}` with the bent outer
profile `R∞ = outerProfile K Y₁ Y₂`. Since both angles increase along horizontal lines and
`angleOneInf > π/2 > angleZeroInf`, the blend is strictly increasing for every choice of the step
(`exists_hasDerivAt_angleInf`), so `cornerInf` has nonzero Jacobian `-R∞ R∞' ∂ₓ angleInf` on the
whole domain `domOne` of `bridgeOne` (`det_fderiv_cornerInf_ne_zero`). It equals `bridgeZero` for
`x ≤ x₁, y ≤ Y₁` and `bridgeOne` for `x ≥ x₂, y ≤ Y₁` (`cornerInf_eq_bridgeZero`,
`cornerInf_eq_bridgeOne`), is equivariant for the wall reflections near the walls
(`cornerInf_refl_zero`, `cornerInf_refl_one`), takes values in the closed upper half-plane on the
strip `0 ≤ x ≤ W` (`angleInf_mem_Icc`), and is injective there (`cornerInf_injOn`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace ConeShape

variable (σ : ConeShape)

def angleInf (x₁ x₂ : ℝ) (z : ℂ) : ℝ :=
  (1 - coneStep x₁ x₂ z.re) * σ.angleZeroInf z + coneStep x₁ x₂ z.re * σ.angleOneInf z

def cornerInf (x₁ x₂ Y₁ Y₂ : ℝ) (z : ℂ) : ℂ :=
  (outerProfile σ.constK Y₁ Y₂ z.im : ℂ) * exp ((σ.angleInf x₁ x₂ z : ℂ) * I)

theorem domOne_im_pos {z : ℂ} (hz : z ∈ σ.domOne) : 0 < z.im := hz.1

theorem contDiffAt_angleInf (x₁ x₂ : ℝ) {z : ℂ} (hz : z ∈ σ.domOne) :
    ContDiffAt ℝ ∞ (σ.angleInf x₁ x₂) z := by
  have h1 : ContDiffAt ℝ ∞ (fun u : ℂ => coneStep x₁ x₂ u.re) z :=
    (contDiff_coneStep x₁ x₂).contDiffAt.comp z reCLM.contDiff.contDiffAt
  exact ((contDiffAt_const.sub h1).mul (σ.contDiffAt_angleZeroInf hz.1)).add
    (h1.mul (σ.contDiffAt_angleOneInf hz))

theorem exists_hasDerivAt_angleInf {x₁ x₂ : ℝ} (hx : x₁ < x₂) {z : ℂ} (hz : z ∈ σ.domOne) :
    ∃ D : ℝ, 0 < D ∧ HasDerivAt (fun t : ℝ => σ.angleInf x₁ x₂ (z + t)) D 0 := by
  obtain ⟨a, ha, had⟩ := σ.exists_hasDerivAt_angleZeroInf hz.1
  obtain ⟨b, hb, hbd⟩ := σ.exists_hasDerivAt_angleOneInf hz
  have hν : HasDerivAt (fun t : ℝ => coneStep x₁ x₂ (z + t).re)
      (deriv (coneStep x₁ x₂) z.re) 0 := by
    have h := hasDerivAt_coneStep x₁ x₂ z.re
    have hl : HasDerivAt (fun t : ℝ => (z + t).re) 1 0 := by
      simpa using (hasDerivAt_id' (0 : ℝ)).const_add z.re
    exact (h.comp_of_eq (0 : ℝ) hl (by simp)).congr_deriv (mul_one _)
  have hN := deriv_coneStep_nonneg hx z.re
  have h := (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hν).mul had).add (hν.mul hbd)
  refine ⟨_, ?_, h⟩
  have hm1 := σ.angleZeroInf_mem hz.1
  have hm2 := σ.angleOneInf_mem hz
  have hc := convex_comb_pos (coneStep_nonneg x₁ x₂ (z + ((0 : ℝ) : ℂ)).re)
    (coneStep_le_one x₁ x₂ (z + ((0 : ℝ) : ℂ)).re) ha hb
  have hd : 0 ≤ deriv (coneStep x₁ x₂) z.re * (σ.angleOneInf (z + ((0 : ℝ) : ℂ)) -
      σ.angleZeroInf (z + ((0 : ℝ) : ℂ))) := by
    apply mul_nonneg hN
    simp only [ofReal_zero, add_zero]
    linarith [hm1.2, hm2.1]
  simp only [Pi.sub_apply] at hc hd ⊢
  nlinarith

theorem contDiffAt_cornerInf (x₁ x₂ Y₁ Y₂ : ℝ) {z : ℂ} (hz : z ∈ σ.domOne) :
    ContDiffAt ℝ ∞ (σ.cornerInf x₁ x₂ Y₁ Y₂) z := by
  have hR : ContDiffAt ℝ ∞ (outerProfile σ.constK Y₁ Y₂) z.im := by
    have h := (contDiff_outerReparam σ.constK Y₁ Y₂).contDiffAt
      (Ioi_mem_nhds (show (-1 : ℝ) < z.im by linarith [hz.1]))
    exact contDiffAt_const.add ((contDiff_coneProfile σ.constK_pos).contDiffAt.comp _ h)
  have h1 : ContDiffAt ℝ ∞ (fun u : ℂ => (outerProfile σ.constK Y₁ Y₂ u.im : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (hR.comp z imCLM.contDiff.contDiffAt)
  have h2 : ContDiffAt ℝ ∞ (fun u : ℂ => exp ((σ.angleInf x₁ x₂ u : ℂ) * I)) z :=
    (Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp z
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp z (σ.contDiffAt_angleInf x₁ x₂ hz)).mul
        contDiffAt_const)
  exact h1.mul h2

structure InfParams where
  x₁ : ℝ
  x₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ
  x_lt : x₁ < x₂
  Y₁_nonneg : 0 ≤ Y₁
  Y_lt : Y₁ < Y₂

theorem det_fderiv_cornerInf_ne_zero (P : InfParams) (hY₂ : P.Y₂ < Real.sqrt σ.constK)
    (hK : Real.sqrt σ.constK ≤ 1 / 2) {z : ℂ} (hz : z ∈ σ.domOne) :
    (fderiv ℝ (σ.cornerInf P.x₁ P.x₂ P.Y₁ P.Y₂) z).det ≠ 0 := by
  obtain ⟨S', hS', hSd⟩ := exists_hasDerivAt_outerProfile σ.constK_pos hK P.Y₁_nonneg P.Y_lt
    hY₂ hz.1
  obtain ⟨a, ha, had⟩ := σ.exists_hasDerivAt_angleInf P.x_lt hz
  have hΘd := (σ.contDiffAt_angleInf P.x₁ P.x₂ hz).differentiableAt (by simp)
  have hρd : DifferentiableAt ℝ (fun u : ℂ => u.im) z := imCLM.differentiableAt
  have hγ : HasDerivAt (fun t : ℝ => z + t) 1 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add z
  have hργ : ∀ᶠ t : ℝ in 𝓝 0, (z + t).im = z.im := Eventually.of_forall fun t => by simp
  have hρN : HasDerivAt (fun t : ℝ => (z + t * I).im) 1 0 := by
    have : (fun t : ℝ => (z + t * I).im) = fun t => z.im + t := by
      funext t
      simp
    rw [this]
    simpa using (hasDerivAt_id' (0 : ℝ)).const_add z.im
  have hΘN := hasDerivAt_line_of_differentiableAt (F := fun u => ((σ.angleInf P.x₁ P.x₂ u : ℝ) :
    ℂ)) (Complex.ofRealCLM.differentiableAt.comp z hΘd) I
  have hΘN' : HasDerivAt (fun t : ℝ => σ.angleInf P.x₁ P.x₂ (z + t * I))
      (fderiv ℝ (σ.angleInf P.x₁ P.x₂) z I) 0 := by
    have hl : HasDerivAt (fun t : ℝ => z + (t : ℂ) * I) I 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const I).const_add z
    have hF' : HasFDerivAt (σ.angleInf P.x₁ P.x₂) (fderiv ℝ (σ.angleInf P.x₁ P.x₂) z)
        (z + ((0 : ℝ) : ℂ) * I) := by simpa using hΘd.hasFDerivAt
    exact hF'.comp_hasDerivAt 0 hl
  have hdet := det_fderiv_polar (c := 0) (S := outerProfile σ.constK P.Y₁ P.Y₂)
    (ρ := fun u : ℂ => u.im) (Θ := σ.angleInf P.x₁ P.x₂) (V := 1) (N := I) hSd hρd hΘd hγ
    (by simp) hργ had hρN hΘN'
  have hfun : (fun u => (0 : ℂ) + ((outerProfile σ.constK P.Y₁ P.Y₂ u.im : ℝ) : ℂ) *
      exp ((σ.angleInf P.x₁ P.x₂ u : ℂ) * I)) = σ.cornerInf P.x₁ P.x₂ P.Y₁ P.Y₂ := by
    funext u
    simp [cornerInf]
  rw [hfun] at hdet
  simp only [I_re, one_im, one_re, I_im, mul_zero, mul_one, zero_sub] at hdet
  intro h0
  rw [h0, zero_mul] at hdet
  have := two_lt_outerProfile σ.constK_pos hK (by linarith [P.Y₁_nonneg, P.Y_lt]) hY₂
    (Y₁ := P.Y₁) hz.1
  have : 0 < outerProfile σ.constK P.Y₁ P.Y₂ z.im * S' * a * 1 := by positivity
  linarith

theorem cornerInf_eq_bridgeZero (P : InfParams) {z : ℂ} (hz : 0 < z.im) (hx : z.re ≤ P.x₁)
    (hy : z.im ≤ P.Y₁) : σ.cornerInf P.x₁ P.x₂ P.Y₁ P.Y₂ z = σ.bridgeZero z := by
  rw [cornerInf, angleInf, coneStep_eq_zero P.x_lt hx, outerProfile_of_le P.Y_lt hy,
    σ.bridgeZero_polar hz]
  simp

theorem cornerInf_eq_bridgeOne (P : InfParams) {z : ℂ} (hz : z ∈ σ.domOne) (hx : P.x₂ ≤ z.re)
    (hy : z.im ≤ P.Y₁) : σ.cornerInf P.x₁ P.x₂ P.Y₁ P.Y₂ z = σ.bridgeOne z := by
  rw [cornerInf, angleInf, coneStep_eq_one P.x_lt hx, outerProfile_of_le P.Y_lt hy,
    σ.bridgeOne_polar hz]
  simp

theorem angleZeroInf_refl_zero (z : ℂ) :
    σ.angleZeroInf (σ.refl 0 z) = -σ.angleZeroInf z := by
  have e2 : (σ.refl 0 z).im = z.im := by simp [refl]
  rw [angleZeroInf, angleZeroInf, σ.bridgeZero_refl_zero, e2, conj_re, conj_im, halfArg_neg]

theorem angleOneInf_refl_one (z : ℂ) :
    σ.angleOneInf (σ.refl 1 z) = 2 * Real.pi - σ.angleOneInf z := by
  rw [angleOneInf, angleOneInf, σ.bridgeOne_refl_one, σ.refl_one_im, conj_re, conj_im,
    negHalfArg_neg]

theorem exp_two_pi_sub_mul_I (θ : ℝ) :
    exp (((2 * Real.pi - θ : ℝ) : ℂ) * I) = conj (exp ((θ : ℂ) * I)) := by
  rw [← Complex.exp_conj]
  have : conj ((θ : ℂ) * I) = -((θ : ℂ) * I) := by simp
  rw [this, show (((2 * Real.pi - θ : ℝ) : ℂ) * I) = -((θ : ℂ) * I) + 2 * Real.pi * I by
    push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem cornerInf_refl_zero (P : InfParams) {z : ℂ} (hx : |z.re| ≤ P.x₁) :
    σ.cornerInf P.x₁ P.x₂ P.Y₁ P.Y₂ (σ.refl 0 z) = conj (σ.cornerInf P.x₁ P.x₂ P.Y₁ P.Y₂ z) := by
  have e2 : (σ.refl 0 z).im = z.im := by simp [refl]
  have e3 : (σ.refl 0 z).re = -z.re := by simp [refl]
  have h1 : z.re ≤ P.x₁ := le_trans (le_abs_self _) hx
  have h2 : -z.re ≤ P.x₁ := le_trans (neg_le_abs _) hx
  rw [cornerInf, cornerInf, angleInf, angleInf, e2, e3, coneStep_eq_zero P.x_lt h1,
    coneStep_eq_zero P.x_lt h2, angleZeroInf_refl_zero]
  simp only [sub_zero, one_mul, zero_mul, add_zero, map_mul, Complex.conj_ofReal]
  rw [← Complex.exp_conj]
  congr 2
  simp

theorem cornerInf_refl_one (P : InfParams) {z : ℂ} (hx1 : P.x₂ ≤ z.re)
    (hx2 : P.x₂ ≤ 2 * σ.width - z.re) :
    σ.cornerInf P.x₁ P.x₂ P.Y₁ P.Y₂ (σ.refl 1 z) = conj (σ.cornerInf P.x₁ P.x₂ P.Y₁ P.Y₂ z) := by
  have e3 : (σ.refl 1 z).re = 2 * σ.width - z.re := by simp [refl]
  rw [cornerInf, cornerInf, angleInf, angleInf, σ.refl_one_im, e3, coneStep_eq_one P.x_lt hx1,
    coneStep_eq_one P.x_lt hx2, angleOneInf_refl_one]
  simp only [sub_self, zero_mul, zero_add, one_mul, map_mul, Complex.conj_ofReal]
  rw [exp_two_pi_sub_mul_I]

theorem angleZeroInf_nonneg {z : ℂ} (hz : 0 < z.im) (hx : 0 ≤ z.re) :
    0 ≤ σ.angleZeroInf z := by
  have hR := σ.bridgeZero_re_pos hz
  have hS : 0 < 3 / 2 + coneProfile σ.constK z.im + (σ.bridgeZero z).re := by
    linarith [σ.outerModulus_pos z]
  have hI : 0 ≤ (σ.bridgeZero z).im := by
    rcases eq_or_lt_of_le hx with h | h
    · have : (σ.bridgeZero z).im = 0 := by
        simp [bridgeZero, outerBridge, ← h]
      rw [this]
    · exact (outerBridge_im_pos σ.constK_pos (Or.inl rfl) hz (cuspZeroHeight_pos hz)
        (by simpa using hz) h).le
  unfold angleZeroInf halfArg
  have := Real.arctan_nonneg.2 (div_nonneg hI hS.le)
  linarith

theorem angleOneInf_le_pi {z : ℂ} (hz : z ∈ σ.domOne) (hw : 0 ≤ σ.wallOne z) :
    σ.angleOneInf z ≤ Real.pi := by
  have hS : 0 < 3 / 2 + coneProfile σ.constK z.im - (σ.bridgeOne z).re := by
    linarith [σ.outerModulus_pos z, σ.bridgeOne_re_neg hz.1]
  have hI : 0 ≤ (σ.bridgeOne z).im := by
    rcases eq_or_lt_of_le hw with h | h
    · have : (σ.bridgeOne z).im = 0 := by
        simp [bridgeOne, outerBridge, ← h]
      rw [this]
    · exact (σ.bridgeOne_im_pos hz h).le
  unfold angleOneInf negHalfArg
  have := Real.arctan_nonneg.2 (div_nonneg hI hS.le)
  linarith

theorem angleInf_mem_Icc (P : InfParams) {z : ℂ} (hz : z ∈ σ.domOne) (hx : 0 ≤ z.re)
    (hw : 0 ≤ σ.wallOne z) : σ.angleInf P.x₁ P.x₂ z ∈ Set.Icc 0 Real.pi := by
  have h1 := σ.angleZeroInf_nonneg hz.1 hx
  have h2 := σ.angleOneInf_le_pi hz hw
  have h3 := σ.angleZeroInf_mem hz.1
  have h4 := σ.angleOneInf_mem hz
  have hν0 := coneStep_nonneg P.x₁ P.x₂ z.re
  have hν1 := coneStep_le_one P.x₁ P.x₂ z.re
  unfold angleInf
  constructor <;> nlinarith [h3.2, h4.1]

theorem norm_cornerInf (P : InfParams) (hY₂ : P.Y₂ < Real.sqrt σ.constK)
    (hK : Real.sqrt σ.constK ≤ 1 / 2) {z : ℂ} (hz : 0 < z.im) :
    ‖σ.cornerInf P.x₁ P.x₂ P.Y₁ P.Y₂ z‖ = outerProfile σ.constK P.Y₁ P.Y₂ z.im := by
  have := two_lt_outerProfile σ.constK_pos hK (by linarith [P.Y₁_nonneg, P.Y_lt]) hY₂
    (Y₁ := P.Y₁) hz
  rw [cornerInf, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by linarith)]

end ConeShape

end GC.Seifert
