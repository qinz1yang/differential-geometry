import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldTwoConeVertexTwo

/-!
# The corner at the cusp `∞` of the two-cone fold

Lane A4b3 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §5, two-cone
shapes). The corner `cornerInfC ν` at `∞` is `R∞(y) e^{iA}` with `A = (1 - ν) α + ν Θ₁`, where
`Θ₁ = angleOneInf` is the angle of the wall-1 bridge and `α = angleZeroInfC` the angle of the
two-cone wall-0 bridge `bridgeZeroC`. By the swap, `α(z) = π - Θ₁'(W - z̄)` with `Θ₁'` the wall-1
angle of the swapped shape (`angleZeroInfC_eq`), so `α ∈ (-π/2, π/2)` and `α` strictly increases
along horizontal lines (`exists_hasDerivAt_angleZeroInfC`). Hence, as for the one-cone corner,
`cornerInfC ν` is smooth with nonzero Jacobian for any blend weight `ν` with values in `[0, 1]`
non-decreasing along horizontal lines (`det_fderiv_cornerInfC_ne_zero`), equals `bridgeZeroC`
where `ν = 0` and `bridgeOne` where `ν = 1` below `Y₁`, and is equivariant for the reflections in
walls 0 and 1 where `ν` is constant `0`, resp. `1` (`cornerInfC_refl_zero`, `cornerInfC_refl_one`).
The blend weight of `SF/ConeFoldCornerBlend` is smooth off both vertices
(`contDiffAt_blendWeightC`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem halfArg_neg_re (S R J : ℝ) : halfArg S (-R) J = Real.pi - negHalfArg S R J := by
  unfold halfArg negHalfArg
  rw [← sub_eq_add_neg]
  ring

namespace ConeShape

variable (σ : ConeShape)

def angleZeroInfC (z : ℂ) : ℝ :=
  halfArg (3 / 2 + coneProfile σ.constK z.im) (σ.bridgeZeroC z).re (σ.bridgeZeroC z).im

def angleInfC (ν : ℂ → ℝ) (z : ℂ) : ℝ :=
  (1 - ν z) * σ.angleZeroInfC z + ν z * σ.angleOneInf z

def cornerInfC (ν : ℂ → ℝ) (Y₁ Y₂ : ℝ) (z : ℂ) : ℂ :=
  (outerProfile σ.constK Y₁ Y₂ z.im : ℂ) * exp ((σ.angleInfC ν z : ℂ) * I)

section Inf

variable (hθ : 0 < σ.θ₂)

include hθ

theorem swapPt_mem_domOne_iff {z : ℂ} : σ.swapPt z ∈ (σ.swap hθ).domOne ↔ z ∈ σ.domZeroC := by
  change (0 < (σ.swapPt z).im ∧ 0 < ‖(σ.swap hθ).discOne (σ.swapPt z)‖ +
    ((σ.swap hθ).discOne (σ.swapPt z)).re) ↔ (0 < z.im ∧ 0 < ‖σ.discTwo z‖ + (σ.discTwo z).re)
  rw [swapPt_im, σ.swap_discOne hθ, Complex.norm_conj, conj_re]

theorem bridgeZeroC_eq (z : ℂ) : σ.bridgeZeroC z = -conj ((σ.swap hθ).bridgeOne (σ.swapPt z)) := by
  rw [σ.swap_bridgeOne hθ, map_neg, Complex.conj_conj, neg_neg]

theorem angleZeroInfC_eq (z : ℂ) :
    σ.angleZeroInfC z = Real.pi - (σ.swap hθ).angleOneInf (σ.swapPt z) := by
  rw [angleZeroInfC, angleOneInf, σ.bridgeZeroC_eq hθ, σ.swap_constK hθ, swapPt_im, neg_re,
    conj_re, neg_im, conj_im, neg_neg, halfArg_neg_re]

theorem bridgeZeroC_sq {z : ℂ} (hz : z ∈ σ.domZeroC) :
    (σ.bridgeZeroC z).re ^ 2 + (σ.bridgeZeroC z).im ^ 2 =
      (3 / 2 + coneProfile σ.constK z.im) ^ 2 :=
  sq_add_sq_eq_of_norm (σ.norm_bridgeZeroC hθ hz)

theorem bridgeZeroC_polar {z : ℂ} (hz : z ∈ σ.domZeroC) :
    σ.bridgeZeroC z = ((3 / 2 + coneProfile σ.constK z.im : ℝ) : ℂ) *
      exp ((σ.angleZeroInfC z : ℂ) * I) := by
  have h := halfArg_polar (σ.outerModulus_pos z)
    (by linarith [σ.outerModulus_pos z, σ.bridgeZeroC_re_pos hz.1]) (σ.bridgeZeroC_sq hθ hz)
  rw [angleZeroInfC, ← h]

theorem angleZeroInfC_mem {z : ℂ} (hz : z ∈ σ.domZeroC) :
    σ.angleZeroInfC z ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  have h := (σ.swap hθ).angleOneInf_mem ((σ.swapPt_mem_domOne_iff hθ).2 hz)
  rw [σ.angleZeroInfC_eq hθ]
  constructor <;> linarith [h.1, h.2]

theorem contDiffAt_angleZeroInfC {z : ℂ} (hz : z ∈ σ.domZeroC) :
    ContDiffAt ℝ ∞ σ.angleZeroInfC z := by
  have hb := σ.contDiffAt_bridgeZeroC hθ hz
  exact contDiffAt_halfArg_comp (σ.contDiffAt_outerModulus z)
    (reCLM.contDiff.contDiffAt.comp z hb) (imCLM.contDiff.contDiffAt.comp z hb)
    (by linarith [σ.outerModulus_pos z, σ.bridgeZeroC_re_pos hz.1])

theorem exists_hasDerivAt_angleZeroInfC {z : ℂ} (hz : z ∈ σ.domZeroC) :
    ∃ D : ℝ, 0 < D ∧ HasDerivAt (fun t : ℝ => σ.angleZeroInfC (z + t)) D 0 := by
  obtain ⟨b, hb, hbd⟩ :=
    (σ.swap hθ).exists_hasDerivAt_angleOneInf ((σ.swapPt_mem_domOne_iff hθ).2 hz)
  have hbd' : HasDerivAt (fun u : ℝ => (σ.swap hθ).angleOneInf (σ.swapPt z + u)) b
      (-(0 : ℝ)) := by
    rw [neg_zero]; exact hbd
  have hc := hbd'.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have h := hc.const_sub Real.pi
  refine ⟨b, hb, ?_⟩
  have e : (fun t : ℝ => σ.angleZeroInfC (z + t)) = fun t => Real.pi -
      ((fun u : ℝ => (σ.swap hθ).angleOneInf (σ.swapPt z + u)) ∘ Neg.neg) t := by
    funext t
    simp only [Function.comp]
    rw [σ.angleZeroInfC_eq hθ]
    congr 2
    simp [swapPt]
    ring
  rw [e]
  exact h.congr_deriv (by ring)

theorem wallZeroC_nonneg {z : ℂ} (hz : 0 < z.im) (hx : 0 ≤ z.re) : 0 ≤ σ.wallZeroC z := by
  have hv2 := σ.vertexTwo_im_pos hθ
  have h1 := σ.im_coneDisc_vertexTwo_mul z
  have hN := normSq_sub_conj_pos hv2 hz
  have : 0 ≤ -(coneDisc σ.vertexTwo z).im * normSq (z - conj σ.vertexTwo) := by
    rw [neg_mul, h1, neg_neg]
    simp only [wallSide]
    positivity
  exact nonneg_of_mul_nonneg_left this hN

theorem angleZeroInfC_nonneg {z : ℂ} (hz : 0 < z.im) (hx : 0 ≤ z.re) :
    0 ≤ σ.angleZeroInfC z := by
  have hR := σ.bridgeZeroC_re_pos hz
  have hS : 0 < 3 / 2 + coneProfile σ.constK z.im + (σ.bridgeZeroC z).re := by
    linarith [σ.outerModulus_pos z]
  have hw := σ.wallZeroC_nonneg hθ hz hx
  have hI : 0 ≤ (σ.bridgeZeroC z).im := by
    rw [bridgeZeroC, outerBridge]
    exact twoCircle_im_nonneg hw
  unfold angleZeroInfC halfArg
  have := Real.arctan_nonneg.2 (div_nonneg hI hS.le)
  linarith

theorem contDiffAt_angleInfC {ν : ℂ → ℝ} {z : ℂ} (hz : z ∈ σ.domOne) (hz0 : z ∈ σ.domZeroC)
    (hν : ContDiffAt ℝ ∞ ν z) : ContDiffAt ℝ ∞ (σ.angleInfC ν) z :=
  ((contDiffAt_const.sub hν).mul (σ.contDiffAt_angleZeroInfC hθ hz0)).add
    (hν.mul (σ.contDiffAt_angleOneInf hz))

theorem exists_hasDerivAt_angleInfC {ν : ℂ → ℝ} {ν' : ℝ} {z : ℂ} (hz : z ∈ σ.domOne)
    (hz0 : z ∈ σ.domZeroC) (hν : HasDerivAt (fun t : ℝ => ν (z + t)) ν' 0) (hν' : 0 ≤ ν')
    (h0 : 0 ≤ ν z) (h1 : ν z ≤ 1) :
    ∃ D : ℝ, 0 < D ∧ HasDerivAt (fun t : ℝ => σ.angleInfC ν (z + t)) D 0 := by
  obtain ⟨a, ha, had⟩ := σ.exists_hasDerivAt_angleZeroInfC hθ hz0
  obtain ⟨b, hb, hbd⟩ := σ.exists_hasDerivAt_angleOneInf hz
  have h := (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hν).mul had).add (hν.mul hbd)
  refine ⟨_, ?_, h⟩
  have hm1 := σ.angleZeroInfC_mem hθ hz0
  have hm2 := σ.angleOneInf_mem hz
  simp only [Pi.sub_apply, ofReal_zero, add_zero]
  have hc := convex_comb_pos h0 h1 ha hb
  have hd : 0 ≤ ν' * (σ.angleOneInf z - σ.angleZeroInfC z) :=
    mul_nonneg hν' (by linarith [hm1.2, hm2.1])
  nlinarith

theorem contDiffAt_cornerInfC {ν : ℂ → ℝ} (Y₁ Y₂ : ℝ) {z : ℂ} (hz : z ∈ σ.domOne)
    (hz0 : z ∈ σ.domZeroC) (hν : ContDiffAt ℝ ∞ ν z) :
    ContDiffAt ℝ ∞ (σ.cornerInfC ν Y₁ Y₂) z := by
  have hR : ContDiffAt ℝ ∞ (outerProfile σ.constK Y₁ Y₂) z.im := by
    have h := (contDiff_outerReparam σ.constK Y₁ Y₂).contDiffAt
      (Ioi_mem_nhds (show (-1 : ℝ) < z.im by linarith [hz.1]))
    exact contDiffAt_const.add ((contDiff_coneProfile σ.constK_pos).contDiffAt.comp _ h)
  have h1 : ContDiffAt ℝ ∞ (fun u : ℂ => (outerProfile σ.constK Y₁ Y₂ u.im : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (hR.comp z imCLM.contDiff.contDiffAt)
  have h2 : ContDiffAt ℝ ∞ (fun u : ℂ => exp ((σ.angleInfC ν u : ℂ) * I)) z :=
    (Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp z
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp z (σ.contDiffAt_angleInfC hθ hz hz0 hν)).mul
        contDiffAt_const)
  exact h1.mul h2

theorem det_fderiv_cornerInfC_ne_zero {ν : ℂ → ℝ} {ν' Y₁ Y₂ : ℝ} (hY₁ : 0 ≤ Y₁) (hY : Y₁ < Y₂)
    (hY₂ : Y₂ < Real.sqrt σ.constK) (hK : Real.sqrt σ.constK ≤ 1 / 2) {z : ℂ}
    (hz : z ∈ σ.domOne) (hz0 : z ∈ σ.domZeroC) (hνc : ContDiffAt ℝ ∞ ν z)
    (hν : HasDerivAt (fun t : ℝ => ν (z + t)) ν' 0) (hν' : 0 ≤ ν') (h0 : 0 ≤ ν z)
    (h1 : ν z ≤ 1) : (fderiv ℝ (σ.cornerInfC ν Y₁ Y₂) z).det ≠ 0 := by
  obtain ⟨S', hS', hSd⟩ := exists_hasDerivAt_outerProfile σ.constK_pos hK hY₁ hY hY₂ hz.1
  obtain ⟨a, ha, had⟩ := σ.exists_hasDerivAt_angleInfC hθ hz hz0 hν hν' h0 h1
  have hΘd := (σ.contDiffAt_angleInfC hθ hz hz0 hνc).differentiableAt (by simp)
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
  have hΘN' : HasDerivAt (fun t : ℝ => σ.angleInfC ν (z + t * I))
      (fderiv ℝ (σ.angleInfC ν) z I) 0 := by
    have hl : HasDerivAt (fun t : ℝ => z + (t : ℂ) * I) I 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const I).const_add z
    have hF' : HasFDerivAt (σ.angleInfC ν) (fderiv ℝ (σ.angleInfC ν) z)
        (z + ((0 : ℝ) : ℂ) * I) := by simpa using hΘd.hasFDerivAt
    exact hF'.comp_hasDerivAt 0 hl
  have hdet := det_fderiv_polar (c := 0) (S := outerProfile σ.constK Y₁ Y₂)
    (ρ := fun u : ℂ => u.im) (Θ := σ.angleInfC ν) (V := 1) (N := I) hSd hρd hΘd hγ
    (by simp) hργ had hρN hΘN'
  have hfun : (fun u => (0 : ℂ) + ((outerProfile σ.constK Y₁ Y₂ u.im : ℝ) : ℂ) *
      exp ((σ.angleInfC ν u : ℂ) * I)) = σ.cornerInfC ν Y₁ Y₂ := by
    funext u
    simp [cornerInfC]
  rw [hfun] at hdet
  simp only [I_re, one_im, one_re, I_im, mul_zero, mul_one, zero_sub] at hdet
  intro h0'
  rw [h0', zero_mul] at hdet
  have := two_lt_outerProfile σ.constK_pos hK (by linarith) hY₂ (Y₁ := Y₁) hz.1
  have : 0 < outerProfile σ.constK Y₁ Y₂ z.im * S' * a * 1 := by positivity
  linarith

theorem cornerInfC_eq_bridgeZeroC {ν : ℂ → ℝ} {Y₁ Y₂ : ℝ} (hY : Y₁ < Y₂) {z : ℂ}
    (hz : z ∈ σ.domZeroC) (hν : ν z = 0) (hy : z.im ≤ Y₁) :
    σ.cornerInfC ν Y₁ Y₂ z = σ.bridgeZeroC z := by
  rw [cornerInfC, angleInfC, hν, outerProfile_of_le hY hy, σ.bridgeZeroC_polar hθ hz]
  simp

theorem angleInfC_mem {ν : ℂ → ℝ} {z : ℂ} (hz : z ∈ σ.domOne) (hz0 : z ∈ σ.domZeroC)
    (hx : 0 ≤ z.re) (hw : 0 ≤ σ.wallOne z) (h0 : 0 ≤ ν z) (h1 : ν z ≤ 1) :
    0 ≤ σ.angleZeroInfC z ∧ σ.angleZeroInfC z ≤ σ.angleInfC ν z ∧
      σ.angleInfC ν z ≤ σ.angleOneInf z ∧ σ.angleOneInf z ≤ Real.pi := by
  have ha := σ.angleZeroInfC_nonneg hθ hz.1 hx
  have hb := σ.angleOneInf_le_pi hz hw
  have hm1 := σ.angleZeroInfC_mem hθ hz0
  have hm2 := σ.angleOneInf_mem hz
  have hab : σ.angleZeroInfC z ≤ σ.angleOneInf z := by linarith [hm1.2, hm2.1]
  unfold angleInfC
  refine ⟨ha, ?_, ?_, hb⟩ <;> nlinarith

theorem mem_domZeroC_of_mem_triangle {z : ℂ} (hz : z ∈ σ.triangle) (hzv : z ≠ σ.vertexTwo) :
    z ∈ σ.domZeroC := by
  refine (σ.swapPt_mem_domOne_iff hθ).1 ?_
  refine (σ.swap hθ).mem_domOne_of_mem_triangle ((σ.swapPt_mem_triangle hθ).2 hz) ?_
  exact (σ.swapPt_ne_vertexOne_iff hθ).2 hzv

theorem isOpen_domZeroC : IsOpen σ.domZeroC := by
  have h : σ.domZeroC = σ.swapPt ⁻¹' (σ.swap hθ).domOne := by
    ext z
    exact (σ.swapPt_mem_domOne_iff hθ).symm
  rw [h]
  exact (σ.swap hθ).isOpen_domOne.preimage σ.continuous_swapPt

end Inf

theorem angleZeroInfC_refl_zero (z : ℂ) :
    σ.angleZeroInfC (σ.refl 0 z) = -σ.angleZeroInfC z := by
  have e2 : (σ.refl 0 z).im = z.im := by simp [refl]
  rw [angleZeroInfC, angleZeroInfC, σ.bridgeZeroC_refl_zero, e2, conj_re, conj_im, halfArg_neg]


theorem cornerInfC_eq_bridgeOne {ν : ℂ → ℝ} {Y₁ Y₂ : ℝ} (hY : Y₁ < Y₂) {z : ℂ}
    (hz : z ∈ σ.domOne) (hν : ν z = 1) (hy : z.im ≤ Y₁) :
    σ.cornerInfC ν Y₁ Y₂ z = σ.bridgeOne z := by
  rw [cornerInfC, angleInfC, hν, outerProfile_of_le hY hy, σ.bridgeOne_polar hz]
  simp


theorem cornerInfC_refl_zero {ν : ℂ → ℝ} (Y₁ Y₂ : ℝ) {z : ℂ} (hν : ν z = 0)
    (hν' : ν (σ.refl 0 z) = 0) :
    σ.cornerInfC ν Y₁ Y₂ (σ.refl 0 z) = conj (σ.cornerInfC ν Y₁ Y₂ z) := by
  have e2 : (σ.refl 0 z).im = z.im := by simp [refl]
  rw [cornerInfC, cornerInfC, angleInfC, angleInfC, e2, hν, hν', angleZeroInfC_refl_zero]
  simp only [sub_zero, one_mul, zero_mul, add_zero, map_mul, Complex.conj_ofReal]
  rw [← Complex.exp_conj]
  congr 2
  simp

theorem cornerInfC_refl_one {ν : ℂ → ℝ} (Y₁ Y₂ : ℝ) {z : ℂ} (hν : ν z = 1)
    (hν' : ν (σ.refl 1 z) = 1) :
    σ.cornerInfC ν Y₁ Y₂ (σ.refl 1 z) = conj (σ.cornerInfC ν Y₁ Y₂ z) := by
  rw [cornerInfC, cornerInfC, angleInfC, angleInfC, σ.refl_one_im, hν, hν', angleOneInf_refl_one]
  simp only [sub_self, zero_mul, zero_add, one_mul, map_mul, Complex.conj_ofReal]
  rw [exp_two_pi_sub_mul_I]

theorem etaTwo_eq_of_cone (hθ : 0 < σ.θ₂) : σ.etaTwo = σ.etaTwoC :=
  funext fun z => by simp [etaTwo, hθ.ne', etaTwoC]

theorem contDiffAt_blendFnC (hθ : 0 < σ.θ₂) {z : ℂ} (hz : 0 < z.im) (hzv : z ≠ σ.vertexOne)
    (hzv2 : z ≠ σ.vertexTwo) : ContDiffAt ℝ ∞ σ.blendFn z := by
  have h0 := σ.contDiffAt_etaTwoC hθ hz hzv2
  have h1 : ContDiffAt ℝ ∞ σ.etaOne z := contDiffAt_coneHeight σ.vertexOne_im_pos hz hzv
  have hne : σ.etaTwoC z + σ.etaOne z ≠ 0 :=
    (add_pos (σ.etaTwoC_pos hθ hz) (σ.etaOne_pos hz)).ne'
  have e : σ.blendFn = fun u => 2 * u.re / σ.width - 1 +
      42 * (σ.etaTwoC u - σ.etaOne u) / (σ.etaTwoC u + σ.etaOne u) := by
    funext u
    rw [blendFn, σ.etaTwo_eq_of_cone hθ]
    rfl
  rw [e]
  exact ((((contDiffAt_const.mul reCLM.contDiff.contDiffAt).div_const _).sub
    contDiffAt_const)).add ((contDiffAt_const.mul (h0.sub h1)).div (h0.add h1) hne)

theorem continuousAt_blendFnC (hθ : 0 < σ.θ₂) {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt σ.blendFn z := by
  have hv2 := σ.vertexTwo_im_pos hθ
  have h0 : ContinuousAt σ.etaTwoC z := by
    have hd : ContinuousAt (coneDisc σ.vertexTwo) z := (contDiffAt_coneDisc hv2 hz).continuousAt
    have hn : ContinuousAt (fun u => ‖coneDisc σ.vertexTwo u‖) z := hd.norm
    have h1 : 1 - ‖coneDisc σ.vertexTwo z‖ ≠ 0 := (sub_pos.2 (norm_coneDisc_lt_one hv2 hz)).ne'
    change ContinuousAt (fun u => σ.vertexTwo.im * (1 + ‖coneDisc σ.vertexTwo u‖) /
      (1 - ‖coneDisc σ.vertexTwo u‖)) z
    exact (continuousAt_const.mul (continuousAt_const.add hn)).div (continuousAt_const.sub hn) h1
  have h1 := σ.continuousAt_etaOne hz
  have hne : σ.etaTwoC z + σ.etaOne z ≠ 0 :=
    (add_pos (σ.etaTwoC_pos hθ hz) (σ.etaOne_pos hz)).ne'
  have e : σ.blendFn = fun u => 2 * u.re / σ.width - 1 +
      42 * (σ.etaTwoC u - σ.etaOne u) / (σ.etaTwoC u + σ.etaOne u) := by
    funext u
    rw [blendFn, σ.etaTwo_eq_of_cone hθ]
    rfl
  rw [e]
  exact (((continuousAt_const.mul continuous_re.continuousAt).div_const _).sub
    continuousAt_const).add ((continuousAt_const.mul (h0.sub h1)).div (h0.add h1) hne)

theorem contDiffAt_blendWeightC (hθ : 0 < σ.θ₂) {z : ℂ} (hz : 0 < z.im)
    (hzv : z ≠ σ.vertexOne) (hzv2 : z ≠ σ.vertexTwo) : ContDiffAt ℝ ∞ σ.blendWeight z :=
  (contDiff_coneStep _ _).contDiffAt.comp z (σ.contDiffAt_blendFnC hθ hz hzv hzv2)

theorem continuousAt_etaTwoC (hθ : 0 < σ.θ₂) {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt σ.etaTwoC z := by
  have hv2 := σ.vertexTwo_im_pos hθ
  have hd : ContinuousAt (coneDisc σ.vertexTwo) z := (contDiffAt_coneDisc hv2 hz).continuousAt
  have hn : ContinuousAt (fun u => ‖coneDisc σ.vertexTwo u‖) z := hd.norm
  have h1 : 1 - ‖coneDisc σ.vertexTwo z‖ ≠ 0 := (sub_pos.2 (norm_coneDisc_lt_one hv2 hz)).ne'
  change ContinuousAt (fun u => σ.vertexTwo.im * (1 + ‖coneDisc σ.vertexTwo u‖) /
    (1 - ‖coneDisc σ.vertexTwo u‖)) z
  exact (continuousAt_const.mul (continuousAt_const.add hn)).div (continuousAt_const.sub hn) h1

end ConeShape

end GC.Seifert
