import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldCornerInfMap
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldSeparation

/-!
# The corner at `∞` with the separating blend weight

Lane A4, tier 2 after review 15 (design
`docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §5 and errata). The corner map
at the cusp `∞` is `R∞(y) e^{iA}` with `A = (1 - ν) angleZeroInf + ν angleOneInf` for a weight `ν`
with values in `[0, 1]`; its Jacobian is `-R∞ R∞' ∂ₓA` and
`∂ₓA = (1 - ν) ∂ₓα + ν ∂ₓΘ₁ + ∂ₓν (Θ₁ - α) > 0` as soon as `∂ₓν ≥ 0`
(`exists_hasDerivAt_angleInfW`, `det_fderiv_cornerInfW_ne_zero`): any monotone weight works.

The weight of the layout is `blendWeight = coneStep (-1/2) (1/2) ∘ blendFn`
(`SF/ConeFoldSeparation`):
* `blendFn` increases along horizontal lines in the strip `0 ≤ x ≤ W` off the vertices
  (`exists_hasDerivAt_blendFn`), because `η₁` decreases and `η₂` increases there
  (`exists_hasDerivAt_coneHeight_nonpos`, `exists_hasDerivAt_coneHeight_nonneg`,
  `exists_hasDerivAt_etaTwo_nonneg`), so `blendWeight` has nonnegative horizontal derivative there
  (`exists_hasDerivAt_blendWeight`);
* `blendWeight = 0` on the closed cone disc at `v₂` and near wall 0, `= 1` on the closed cone disc
  at `v₁` and near wall 1 (from the separation lemmas), so the corner equals the bridges there
  (`cornerInfW_eq_bridgeZero`, `cornerInfW_eq_bridgeOne`) and is equivariant for the wall
  reflections where the weight is `0` resp. `1` at both points (`cornerInfW_refl_zero`,
  `cornerInfW_refl_one`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem coneDisc_ne_zero {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) (hzv : z ≠ v) :
    coneDisc v z ≠ 0 :=
  div_ne_zero (sub_ne_zero.2 hzv) (sub_conj_ne_zero hv hz)

theorem contDiffAt_coneHeight {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) (hzv : z ≠ v) :
    ContDiffAt ℝ ∞ (coneHeight v) z := by
  have hd : ContDiffAt ℝ ∞ (coneDisc v) z := (contDiffAt_coneDisc hv hz).restrict_scalars ℝ
  have h := hd.norm ℝ (coneDisc_ne_zero hv hz hzv)
  have h1 : 1 - ‖coneDisc v z‖ ≠ 0 := (sub_pos.2 (norm_coneDisc_lt_one hv hz)).ne'
  exact (contDiffAt_const.mul (contDiffAt_const.add h)).div (contDiffAt_const.sub h) h1

theorem coneHeight_deriv_factor_neg {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) (hzv : z ≠ v) :
    -(4 * z.im * v.im) / ((1 - ‖coneDisc v z‖) ^ 2 * ‖coneDisc v z‖ * normSq (z - conj v)) < 0 := by
  have hr1 := norm_coneDisc_lt_one hv hz
  have hr0 : 0 < ‖coneDisc v z‖ := norm_pos_iff.2 (coneDisc_ne_zero hv hz hzv)
  have hN := normSq_sub_conj_pos hv hz
  have h1 : 0 < 1 - ‖coneDisc v z‖ := by linarith
  apply div_neg_of_neg_of_pos (by nlinarith)
  positivity

theorem exists_hasDerivAt_coneHeight_nonpos {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im)
    (hzv : z ≠ v) (hx : z.re ≤ v.re) :
    ∃ d : ℝ, d ≤ 0 ∧ HasDerivAt (fun t : ℝ => coneHeight v (z + t)) d 0 := by
  refine ⟨_, ?_, hasDerivAt_coneHeight_horizontal hv hz hzv⟩
  have hf := coneHeight_deriv_factor_neg hv hz hzv
  have hN := normSq_sub_conj_pos hv hz
  have hI : 0 ≤ (coneDisc v z).im := by
    have e := im_coneDisc_mul v z
    by_contra hc
    have : (coneDisc v z).im * normSq (z - conj v) < 0 :=
      mul_neg_of_neg_of_pos (not_le.1 hc) hN
    nlinarith
  exact mul_nonpos_of_nonneg_of_nonpos hI hf.le

theorem exists_hasDerivAt_coneHeight_nonneg {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im)
    (hzv : z ≠ v) (hx : v.re ≤ z.re) :
    ∃ d : ℝ, 0 ≤ d ∧ HasDerivAt (fun t : ℝ => coneHeight v (z + t)) d 0 := by
  refine ⟨_, ?_, hasDerivAt_coneHeight_horizontal hv hz hzv⟩
  have hf := coneHeight_deriv_factor_neg hv hz hzv
  have hN := normSq_sub_conj_pos hv hz
  have hI : (coneDisc v z).im ≤ 0 := by
    have e := im_coneDisc_mul v z
    by_contra hc
    have : 0 < (coneDisc v z).im * normSq (z - conj v) := mul_pos (not_le.1 hc) hN
    nlinarith
  exact mul_nonneg_of_nonpos_of_nonpos hI hf.le

namespace ConeShape

variable (σ : ConeShape)

def angleInfW (ν : ℂ → ℝ) (z : ℂ) : ℝ :=
  (1 - ν z) * σ.angleZeroInf z + ν z * σ.angleOneInf z

def cornerInfW (ν : ℂ → ℝ) (Y₁ Y₂ : ℝ) (z : ℂ) : ℂ :=
  (outerProfile σ.constK Y₁ Y₂ z.im : ℂ) * exp ((σ.angleInfW ν z : ℂ) * I)

def blendWeight (z : ℂ) : ℝ := coneStep (-1 / 2) (1 / 2) (σ.blendFn z)

theorem contDiffAt_angleInfW {ν : ℂ → ℝ} {z : ℂ} (hz : z ∈ σ.domOne)
    (hν : ContDiffAt ℝ ∞ ν z) : ContDiffAt ℝ ∞ (σ.angleInfW ν) z :=
  ((contDiffAt_const.sub hν).mul (σ.contDiffAt_angleZeroInf hz.1)).add
    (hν.mul (σ.contDiffAt_angleOneInf hz))

theorem exists_hasDerivAt_angleInfW {ν : ℂ → ℝ} {ν' : ℝ} {z : ℂ} (hz : z ∈ σ.domOne)
    (hν : HasDerivAt (fun t : ℝ => ν (z + t)) ν' 0) (hν' : 0 ≤ ν') (h0 : 0 ≤ ν z)
    (h1 : ν z ≤ 1) :
    ∃ D : ℝ, 0 < D ∧ HasDerivAt (fun t : ℝ => σ.angleInfW ν (z + t)) D 0 := by
  obtain ⟨a, ha, had⟩ := σ.exists_hasDerivAt_angleZeroInf hz.1
  obtain ⟨b, hb, hbd⟩ := σ.exists_hasDerivAt_angleOneInf hz
  have h := (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hν).mul had).add (hν.mul hbd)
  refine ⟨_, ?_, h⟩
  have hm1 := σ.angleZeroInf_mem hz.1
  have hm2 := σ.angleOneInf_mem hz
  simp only [Pi.sub_apply, ofReal_zero, add_zero]
  have hc := convex_comb_pos h0 h1 ha hb
  have hd : 0 ≤ ν' * (σ.angleOneInf z - σ.angleZeroInf z) :=
    mul_nonneg hν' (by linarith [hm1.2, hm2.1])
  nlinarith

theorem contDiffAt_cornerInfW {ν : ℂ → ℝ} (Y₁ Y₂ : ℝ) {z : ℂ} (hz : z ∈ σ.domOne)
    (hν : ContDiffAt ℝ ∞ ν z) : ContDiffAt ℝ ∞ (σ.cornerInfW ν Y₁ Y₂) z := by
  have hR : ContDiffAt ℝ ∞ (outerProfile σ.constK Y₁ Y₂) z.im := by
    have h := (contDiff_outerReparam σ.constK Y₁ Y₂).contDiffAt
      (Ioi_mem_nhds (show (-1 : ℝ) < z.im by linarith [hz.1]))
    exact contDiffAt_const.add ((contDiff_coneProfile σ.constK_pos).contDiffAt.comp _ h)
  have h1 : ContDiffAt ℝ ∞ (fun u : ℂ => (outerProfile σ.constK Y₁ Y₂ u.im : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (hR.comp z imCLM.contDiff.contDiffAt)
  have h2 : ContDiffAt ℝ ∞ (fun u : ℂ => exp ((σ.angleInfW ν u : ℂ) * I)) z :=
    (Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp z
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp z (σ.contDiffAt_angleInfW hz hν)).mul
        contDiffAt_const)
  exact h1.mul h2

theorem det_fderiv_cornerInfW_ne_zero {ν : ℂ → ℝ} {ν' Y₁ Y₂ : ℝ} (hY₁ : 0 ≤ Y₁) (hY : Y₁ < Y₂)
    (hY₂ : Y₂ < Real.sqrt σ.constK) (hK : Real.sqrt σ.constK ≤ 1 / 2) {z : ℂ}
    (hz : z ∈ σ.domOne) (hνc : ContDiffAt ℝ ∞ ν z)
    (hν : HasDerivAt (fun t : ℝ => ν (z + t)) ν' 0) (hν' : 0 ≤ ν') (h0 : 0 ≤ ν z)
    (h1 : ν z ≤ 1) : (fderiv ℝ (σ.cornerInfW ν Y₁ Y₂) z).det ≠ 0 := by
  obtain ⟨S', hS', hSd⟩ := exists_hasDerivAt_outerProfile σ.constK_pos hK hY₁ hY hY₂ hz.1
  obtain ⟨a, ha, had⟩ := σ.exists_hasDerivAt_angleInfW hz hν hν' h0 h1
  have hΘd := (σ.contDiffAt_angleInfW hz hνc).differentiableAt (by simp)
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
  have hΘN' : HasDerivAt (fun t : ℝ => σ.angleInfW ν (z + t * I))
      (fderiv ℝ (σ.angleInfW ν) z I) 0 := by
    have hl : HasDerivAt (fun t : ℝ => z + (t : ℂ) * I) I 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const I).const_add z
    have hF' : HasFDerivAt (σ.angleInfW ν) (fderiv ℝ (σ.angleInfW ν) z)
        (z + ((0 : ℝ) : ℂ) * I) := by simpa using hΘd.hasFDerivAt
    exact hF'.comp_hasDerivAt 0 hl
  have hdet := det_fderiv_polar (c := 0) (S := outerProfile σ.constK Y₁ Y₂)
    (ρ := fun u : ℂ => u.im) (Θ := σ.angleInfW ν) (V := 1) (N := I) hSd hρd hΘd hγ
    (by simp) hργ had hρN hΘN'
  have hfun : (fun u => (0 : ℂ) + ((outerProfile σ.constK Y₁ Y₂ u.im : ℝ) : ℂ) *
      exp ((σ.angleInfW ν u : ℂ) * I)) = σ.cornerInfW ν Y₁ Y₂ := by
    funext u
    simp [cornerInfW]
  rw [hfun] at hdet
  simp only [I_re, one_im, one_re, I_im, mul_zero, mul_one, zero_sub] at hdet
  intro h0'
  rw [h0', zero_mul] at hdet
  have := two_lt_outerProfile σ.constK_pos hK (by linarith) hY₂ (Y₁ := Y₁) hz.1
  have : 0 < outerProfile σ.constK Y₁ Y₂ z.im * S' * a * 1 := by positivity
  linarith

theorem cornerInfW_eq_bridgeZero {ν : ℂ → ℝ} {Y₁ Y₂ : ℝ} (hY : Y₁ < Y₂) {z : ℂ}
    (hz : 0 < z.im) (hν : ν z = 0) (hy : z.im ≤ Y₁) : σ.cornerInfW ν Y₁ Y₂ z = σ.bridgeZero z := by
  rw [cornerInfW, angleInfW, hν, outerProfile_of_le hY hy, σ.bridgeZero_polar hz]
  simp

theorem cornerInfW_eq_bridgeOne {ν : ℂ → ℝ} {Y₁ Y₂ : ℝ} (hY : Y₁ < Y₂) {z : ℂ}
    (hz : z ∈ σ.domOne) (hν : ν z = 1) (hy : z.im ≤ Y₁) :
    σ.cornerInfW ν Y₁ Y₂ z = σ.bridgeOne z := by
  rw [cornerInfW, angleInfW, hν, outerProfile_of_le hY hy, σ.bridgeOne_polar hz]
  simp

theorem cornerInfW_refl_zero {ν : ℂ → ℝ} (Y₁ Y₂ : ℝ) {z : ℂ} (hν : ν z = 0)
    (hν' : ν (σ.refl 0 z) = 0) :
    σ.cornerInfW ν Y₁ Y₂ (σ.refl 0 z) = conj (σ.cornerInfW ν Y₁ Y₂ z) := by
  have e2 : (σ.refl 0 z).im = z.im := by simp [refl]
  rw [cornerInfW, cornerInfW, angleInfW, angleInfW, e2, hν, hν', angleZeroInf_refl_zero]
  simp only [sub_zero, one_mul, zero_mul, add_zero, map_mul, Complex.conj_ofReal]
  rw [← Complex.exp_conj]
  congr 2
  simp

theorem cornerInfW_refl_one {ν : ℂ → ℝ} (Y₁ Y₂ : ℝ) {z : ℂ} (hν : ν z = 1)
    (hν' : ν (σ.refl 1 z) = 1) :
    σ.cornerInfW ν Y₁ Y₂ (σ.refl 1 z) = conj (σ.cornerInfW ν Y₁ Y₂ z) := by
  rw [cornerInfW, cornerInfW, angleInfW, angleInfW, σ.refl_one_im, hν, hν', angleOneInf_refl_one]
  simp only [sub_self, zero_mul, zero_add, one_mul, map_mul, Complex.conj_ofReal]
  rw [exp_two_pi_sub_mul_I]

theorem blendWeight_nonneg (z : ℂ) : 0 ≤ σ.blendWeight z := coneStep_nonneg _ _ _

theorem blendWeight_le_one (z : ℂ) : σ.blendWeight z ≤ 1 := coneStep_le_one _ _ _

theorem blendWeight_eq_zero {z : ℂ} (h : σ.blendFn z ≤ -1 / 2) : σ.blendWeight z = 0 :=
  coneStep_eq_zero (by norm_num) h

theorem blendWeight_eq_one {z : ℂ} (h : 1 / 2 ≤ σ.blendFn z) : σ.blendWeight z = 1 :=
  coneStep_eq_one (by norm_num) h

theorem exists_hasDerivAt_etaTwo_nonneg {z : ℂ} (hz : 0 < z.im)
    (h2 : σ.θ₂ ≠ 0 → z ≠ σ.vertexTwo) (hx : 0 ≤ z.re) :
    ∃ d : ℝ, 0 ≤ d ∧ HasDerivAt (fun t : ℝ => σ.etaTwo (z + t)) d 0 := by
  by_cases hθ : σ.θ₂ = 0
  · refine ⟨2 * z.re / z.im, by positivity, ?_⟩
    have := hasDerivAt_cuspZeroHeight_horizontal z
    simpa [etaTwo, hθ] using this
  · have hθ' : 0 < σ.θ₂ := lt_of_le_of_ne σ.θ₂_nonneg (Ne.symm hθ)
    obtain ⟨d, hd, hdd⟩ := exists_hasDerivAt_coneHeight_nonneg (σ.vertexTwo_im_pos hθ') hz
      (h2 hθ) (by rw [vertexTwo_re]; exact hx)
    exact ⟨d, hd, by simpa [etaTwo, hθ] using hdd⟩

theorem exists_hasDerivAt_blendFn {z : ℂ} (hz : 0 < z.im) (h1 : z ≠ σ.vertexOne)
    (h2 : σ.θ₂ ≠ 0 → z ≠ σ.vertexTwo) (hx0 : 0 ≤ z.re) (hxW : z.re ≤ σ.width) :
    ∃ D : ℝ, 0 < D ∧ HasDerivAt (fun t : ℝ => σ.blendFn (z + t)) D 0 := by
  obtain ⟨d₁, hd₁, h₁⟩ := exists_hasDerivAt_coneHeight_nonpos σ.vertexOne_im_pos hz h1
    (by rw [vertexOne_re]; exact hxW)
  obtain ⟨d₂, hd₂, h₂⟩ := σ.exists_hasDerivAt_etaTwo_nonneg hz h2 hx0
  have e1 := coneHeight_pos σ.vertexOne_im_pos hz
  have e2 := σ.etaTwo_pos hz
  have hW := σ.width_pos
  have hlin : HasDerivAt (fun t : ℝ => 2 * (z + t).re / σ.width - 1) (2 / σ.width) 0 := by
    have : (fun t : ℝ => 2 * (z + t).re / σ.width - 1) =
        fun t => 2 / σ.width * t + (2 * z.re / σ.width - 1) := by
      funext t
      simp
      ring
    rw [this]
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul (2 / σ.width)).add_const
      (2 * z.re / σ.width - 1)
  have hne : σ.etaTwo (z + ((0 : ℝ) : ℂ)) + coneHeight σ.vertexOne (z + ((0 : ℝ) : ℂ)) ≠ 0 := by
    simp only [ofReal_zero, add_zero]
    linarith
  have hq := ((h₂.sub h₁).div (h₂.add h₁) hne).const_mul 42
  have h := hlin.add hq
  have h' : HasDerivAt (fun t : ℝ => σ.blendFn (z + t)) (2 / σ.width + 42 *
      (((d₂ - d₁) * (σ.etaTwo z + coneHeight σ.vertexOne z) -
        (σ.etaTwo z - coneHeight σ.vertexOne z) * (d₂ + d₁)) /
        (σ.etaTwo z + coneHeight σ.vertexOne z) ^ 2)) 0 := by
    convert h using 1
    · funext t
      simp only [blendFn, Pi.add_apply, Pi.sub_apply, Pi.div_apply]
      ring
    · simp
  refine ⟨_, ?_, h'⟩
  have hnum : 0 ≤ (d₂ - d₁) * (σ.etaTwo z + coneHeight σ.vertexOne z) -
      (σ.etaTwo z - coneHeight σ.vertexOne z) * (d₂ + d₁) := by
    nlinarith [mul_nonneg e1.le hd₂, mul_nonneg e2.le (neg_nonneg.2 hd₁)]
  have : 0 ≤ 42 * (((d₂ - d₁) * (σ.etaTwo z + coneHeight σ.vertexOne z) -
      (σ.etaTwo z - coneHeight σ.vertexOne z) * (d₂ + d₁)) /
      (σ.etaTwo z + coneHeight σ.vertexOne z) ^ 2) := by positivity
  have : 0 < 2 / σ.width := by positivity
  linarith

theorem exists_hasDerivAt_blendWeight {z : ℂ} (hz : 0 < z.im) (h1 : z ≠ σ.vertexOne)
    (h2 : σ.θ₂ ≠ 0 → z ≠ σ.vertexTwo) (hx0 : 0 ≤ z.re) (hxW : z.re ≤ σ.width) :
    ∃ d : ℝ, 0 ≤ d ∧ HasDerivAt (fun t : ℝ => σ.blendWeight (z + t)) d 0 := by
  obtain ⟨D, hD, hDd⟩ := σ.exists_hasDerivAt_blendFn hz h1 h2 hx0 hxW
  have hs := hasDerivAt_coneStep (-1 / 2) (1 / 2) (σ.blendFn z)
  have hc := hs.comp_of_eq (0 : ℝ) hDd (by simp)
  have hn : 0 ≤ deriv (coneStep (-1 / 2) (1 / 2)) (σ.blendFn z) :=
    deriv_coneStep_nonneg (a := -1 / 2) (b := 1 / 2) (by norm_num) _
  exact ⟨_, mul_nonneg hn hD.le, hc⟩

end ConeShape

end GC.Seifert
