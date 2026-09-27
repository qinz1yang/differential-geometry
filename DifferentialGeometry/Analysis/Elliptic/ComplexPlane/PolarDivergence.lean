import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import DifferentialGeometry.Analysis.Integration.PolarAnnulus







noncomputable section

open Set MeasureTheory Real
open scoped Topology ContDiff Interval

namespace DifferentialGeometry.Analysis


def planeDivergence (F G : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  fderiv ℝ F x (1, 0) + fderiv ℝ G x (0, 1)


def polarRadialFlux (F G : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * (F (polarCoord.symm p) * cos p.2 + G (polarCoord.symm p) * sin p.2)


def polarAngularFlux (F G : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  -F (polarCoord.symm p) * sin p.2 + G (polarCoord.symm p) * cos p.2

private theorem differentiable_polar : Differentiable ℝ polarCoord.symm :=
  fun p => (hasFDerivAt_polarCoord_symm p).differentiableAt

private theorem fderiv_polar_apply (p v : ℝ × ℝ) :
    fderiv ℝ polarCoord.symm p v =
      (cos p.2 * v.1 - p.1 * sin p.2 * v.2,
        sin p.2 * v.1 + p.1 * cos p.2 * v.2) := by
  rw [(hasFDerivAt_polarCoord_symm p).fderiv]
  simp [fderivPolarCoordSymm, Matrix.toLin_finTwoProd_toContinuousLinearMap]
  ring

private theorem apply_pair (L : ℝ × ℝ →L[ℝ] ℝ) (a b : ℝ) :
    L (a, b) = a * L (1, 0) + b * L (0, 1) := by
  have h : (a, b) = a • ((1, 0) : ℝ × ℝ) + b • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  rw [h, map_add, map_smul, map_smul]
  rfl


theorem planeDivergence_polarFlux {F G : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F (polarCoord.symm p))
    (hG : DifferentiableAt ℝ G (polarCoord.symm p)) :
    planeDivergence (polarRadialFlux F G) (polarAngularFlux F G) p =
      p.1 * planeDivergence F G (polarCoord.symm p) := by
  have hFp : DifferentiableAt ℝ (fun q => F (polarCoord.symm q)) p :=
    hF.comp p (differentiable_polar p)
  have hGp : DifferentiableAt ℝ (fun q => G (polarCoord.symm q)) p :=
    hG.comp p (differentiable_polar p)
  have hc : DifferentiableAt ℝ (fun q : ℝ × ℝ => cos q.2) p := by fun_prop
  have hs : DifferentiableAt ℝ (fun q : ℝ × ℝ => sin q.2) p := by fun_prop
  have hd₁ : DifferentiableAt ℝ (Prod.fst : ℝ × ℝ → ℝ) p := differentiableAt_fst
  have hd₂ : DifferentiableAt ℝ (Prod.snd : ℝ × ℝ → ℝ) p := differentiableAt_snd
  unfold planeDivergence polarRadialFlux polarAngularFlux
  erw [fderiv_fun_mul hd₁ ((hFp.mul hc).add (hGp.mul hs)),
    fderiv_fun_add (hFp.mul hc) (hGp.mul hs),
    fderiv_fun_mul hFp hc, fderiv_fun_mul hGp hs,
    fderiv_fun_add (hFp.neg.mul hs) (hGp.mul hc),
    fderiv_fun_mul hFp.neg hs, fderiv_fun_mul hGp hc,
    fderiv_fun_neg, fderiv_cos hd₂, fderiv_sin hd₂,
    fderiv_comp p hF (differentiable_polar p),
    fderiv_comp p hG (differentiable_polar p)]
  simp only [fderiv_fst, fderiv_snd, _root_.add_apply, _root_.smul_apply, _root_.neg_apply,
    Pi.add_apply, Pi.neg_apply, Pi.mul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul, mul_one, mul_zero, sub_zero, zero_add, add_zero, zero_sub,
    ContinuousLinearMap.comp_apply, fderiv_polar_apply]
  simp only [apply_pair _ (cos p.2) (sin p.2),
    apply_pair _ (-(p.1 * sin p.2)) (p.1 * cos p.2)]
  linear_combination
    (p.1 * (fderiv ℝ F (polarCoord.symm p) (1, 0) +
      fderiv ℝ G (polarCoord.symm p) (0, 1))) * cos_sq_add_sin_sq p.2

private theorem contDiff_polar {n : WithTop ℕ∞} : ContDiff ℝ n polarCoord.symm := by
  change ContDiff ℝ n (fun p : ℝ × ℝ => (p.1 * cos p.2, p.1 * sin p.2))
  fun_prop

private theorem contDiffAt_polarRadialFlux {F G : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hF : ContDiffAt ℝ 1 F (polarCoord.symm p))
    (hG : ContDiffAt ℝ 1 G (polarCoord.symm p)) :
    ContDiffAt ℝ 1 (polarRadialFlux F G) p := by
  have hf := hF.comp p contDiff_polar.contDiffAt
  have hg := hG.comp p contDiff_polar.contDiffAt
  exact contDiffAt_fst.mul
    ((hf.mul contDiffAt_snd.cos).add (hg.mul contDiffAt_snd.sin))

private theorem contDiffAt_polarAngularFlux {F G : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hF : ContDiffAt ℝ 1 F (polarCoord.symm p))
    (hG : ContDiffAt ℝ 1 G (polarCoord.symm p)) :
    ContDiffAt ℝ 1 (polarAngularFlux F G) p := by
  have hf := hF.comp p contDiff_polar.contDiffAt
  have hg := hG.comp p contDiff_polar.contDiffAt
  exact (hf.neg.mul contDiffAt_snd.sin).add (hg.mul contDiffAt_snd.cos)



theorem integral_polar_divergence {F G : ℝ × ℝ → ℝ} {r R : ℝ} (hrR : r ≤ R)
    (hF : ∀ p ∈ Icc (r, -Real.pi) (R, Real.pi), ContDiffAt ℝ 1 F (polarCoord.symm p))
    (hG : ∀ p ∈ Icc (r, -Real.pi) (R, Real.pi), ContDiffAt ℝ 1 G (polarCoord.symm p)) :
    (∫ p in Icc (r, -Real.pi) (R, Real.pi), p.1 * planeDivergence F G (polarCoord.symm p)) =
      (∫ θ in -Real.pi..Real.pi, polarRadialFlux F G (R, θ)) -
        ∫ θ in -Real.pi..Real.pi, polarRadialFlux F G (r, θ) := by
  have hrad p hp := contDiffAt_polarRadialFlux (hF p hp) (hG p hp)
  have hang p hp := contDiffAt_polarAngularFlux (hF p hp) (hG p hp)
  have hcont : ContinuousOn
      (planeDivergence (polarRadialFlux F G) (polarAngularFlux F G))
      (Icc (r, -Real.pi) (R, Real.pi)) := by
    intro p hp
    have hf : ContinuousAt (fun q => fderiv ℝ (polarRadialFlux F G) q (1, 0)) p :=
      ((hrad p hp).continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
    have hg : ContinuousAt (fun q => fderiv ℝ (polarAngularFlux F G) q (0, 1)) p :=
      ((hang p hp).continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
    exact (hf.add hg).continuousWithinAt
  have h := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (polarRadialFlux F G) (polarAngularFlux F G)
    (fderiv ℝ (polarRadialFlux F G)) (fderiv ℝ (polarAngularFlux F G))
    (r, -Real.pi) (R, Real.pi) ⟨hrR, by linarith [Real.pi_pos]⟩
    (fun p hp => (hrad p hp).continuousAt.continuousWithinAt)
    (fun p hp => (hang p hp).continuousAt.continuousWithinAt)
    (fun p hp => ((hrad p ⟨⟨hp.1.1.le, hp.2.1.le⟩, ⟨hp.1.2.le, hp.2.2.le⟩⟩).differentiableAt
      (by norm_num)).hasFDerivAt)
    (fun p hp => ((hang p ⟨⟨hp.1.1.le, hp.2.1.le⟩, ⟨hp.1.2.le, hp.2.2.le⟩⟩).differentiableAt
      (by norm_num)).hasFDerivAt)
    (hcont.integrableOn_Icc)
  have hedge : (fun x => polarAngularFlux F G (x, Real.pi)) =
      (fun x => polarAngularFlux F G (x, -Real.pi)) := by
    funext x
    simp [polarAngularFlux, polarCoord_symm_apply]
  simp only [hedge, sub_self, zero_add] at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Icc
  intro p hp
  exact (planeDivergence_polarFlux ((hF p hp).differentiableAt (by norm_num))
    ((hG p hp).differentiableAt (by norm_num))).symm



def complexDivergence (F G : ℂ → ℝ) (z : ℂ) : ℝ :=
  fderiv ℝ F z 1 + fderiv ℝ G z Complex.I

private theorem planeDivergence_complex {F G : ℂ → ℝ} {p : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F (Complex.equivRealProdCLM.symm p))
    (hG : DifferentiableAt ℝ G (Complex.equivRealProdCLM.symm p)) :
    planeDivergence (F ∘ Complex.equivRealProdCLM.symm)
      (G ∘ Complex.equivRealProdCLM.symm) p =
      complexDivergence F G (Complex.equivRealProdCLM.symm p) := by
  unfold planeDivergence complexDivergence
  rw [fderiv_comp p hF Complex.equivRealProdCLM.symm.differentiableAt,
    fderiv_comp p hG Complex.equivRealProdCLM.symm.differentiableAt]
  rw [Complex.equivRealProdCLM.symm.hasFDerivAt.fderiv]
  simp [Complex.equivRealProdCLM_symm_apply]





theorem integral_complexDivergence_annulus {F G : ℂ → ℝ} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    (hF : ∀ z, ‖z‖ ∈ Icc r R → ContDiffAt ℝ 1 F z)
    (hG : ∀ z, ‖z‖ ∈ Icc r R → ContDiffAt ℝ 1 G z) :
    (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, complexDivergence F G z) =
      (∫ θ in -Real.pi..Real.pi, R *
        (F (Complex.polarCoord.symm (R, θ)) * cos θ +
          G (Complex.polarCoord.symm (R, θ)) * sin θ)) -
      ∫ θ in -Real.pi..Real.pi, r *
        (F (Complex.polarCoord.symm (r, θ)) * cos θ +
          G (Complex.polarCoord.symm (r, θ)) * sin θ) := by
  have hmem (p : ℝ × ℝ) (hp : p ∈ Icc (r, -Real.pi) (R, Real.pi)) :
      ‖Complex.polarCoord.symm p‖ ∈ Icc r R := by
    simpa only [Complex.norm_polarCoord_symm, abs_of_pos (hr.trans_le hp.1.1)] using
      (show p.1 ∈ Icc r R from ⟨hp.1.1, hp.2.1⟩)
  have hcF p hp : ContDiffAt ℝ 1 (F ∘ Complex.equivRealProdCLM.symm)
      (polarCoord.symm p) :=
    (hF _ (hmem p hp)).comp (polarCoord.symm p)
      Complex.equivRealProdCLM.symm.contDiff.contDiffAt
  have hcG p hp : ContDiffAt ℝ 1 (G ∘ Complex.equivRealProdCLM.symm)
      (polarCoord.symm p) :=
    (hG _ (hmem p hp)).comp (polarCoord.symm p)
      Complex.equivRealProdCLM.symm.contDiff.contDiffAt
  rw [integral_annulus_eq_polar _ hr]
  change (∫ p in Icc (r, -Real.pi) (R, Real.pi),
    p.1 * complexDivergence F G (Complex.polarCoord.symm p)) = _
  have h := integral_polar_divergence hrR hcF hcG
  change (∫ p in Icc (r, -Real.pi) (R, Real.pi),
    p.1 * planeDivergence (F ∘ Complex.equivRealProdCLM.symm)
      (G ∘ Complex.equivRealProdCLM.symm) (polarCoord.symm p)) = _ at h
  convert h using 1
  · apply setIntegral_congr_fun measurableSet_Icc
    intro p hp
    change p.1 * complexDivergence F G (Complex.polarCoord.symm p) =
      p.1 * planeDivergence (F ∘ Complex.equivRealProdCLM.symm)
        (G ∘ Complex.equivRealProdCLM.symm) (polarCoord.symm p)
    congr 1
    exact (planeDivergence_complex (p := polarCoord.symm p)
      ((hF _ (hmem p hp)).differentiableAt (by norm_num))
      ((hG _ (hmem p hp)).differentiableAt (by norm_num))).symm
  · rfl

end DifferentialGeometry.Analysis
