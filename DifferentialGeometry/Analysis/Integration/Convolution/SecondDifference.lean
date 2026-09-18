import DifferentialGeometry.Analysis.Calculus.SecondDifference
import DifferentialGeometry.Analysis.Integration.Convolution.Derivative
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Convolution Pointwise Topology

namespace MeasureTheory

theorem Integrable.tendsto_integral_mul_centered_second_difference
    {f phi : Real → Real} (hf : Integrable f)
    (hphi : ContDiff Real 2 phi) (hsupp : HasCompactSupport phi)
    (h : Nat → Real) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0) :
    Tendsto (fun n ↦ ∫ x,
      (f (x + h n) - 2 * f x + f (x - h n)) / (h n) ^ 2 * phi x)
      atTop (𝓝 (∫ x, f x * deriv (deriv phi) x)) := by
  let g : Real → Real := fun x ↦ f (-x)
  have hgint : Integrable g := hf.comp_neg
  let F : Real → Real := phi ⋆[ContinuousLinearMap.mul Real Real] g
  have hF : ContDiff Real 2 F :=
    hsupp.contDiff_convolution_left (ContinuousLinearMap.mul Real Real)
      hphi hgint.locallyIntegrable
  have hphi_one : ContDiff Real 1 phi := hphi.of_le (by norm_num)
  have hphi_deriv_one : ContDiff Real 1 (deriv phi) := hphi.deriv'
  have hFderiv : deriv F =
      deriv phi ⋆[ContinuousLinearMap.mul Real Real] g := by
    funext x
    exact (hsupp.hasDerivAt_convolution_left (ContinuousLinearMap.mul Real Real)
      hphi_one hgint.locallyIntegrable x).deriv
  have hFsecond : deriv (deriv F) 0 = ∫ x, f x * deriv (deriv phi) x := by
    rw [hFderiv]
    have hraw := (hsupp.deriv.hasDerivAt_convolution_left
      (μ := volume) (ContinuousLinearMap.mul Real Real) hphi_deriv_one
      hgint.locallyIntegrable 0).deriv
    simpa only [MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply',
      g, zero_sub, neg_neg, mul_comm] using hraw
  have hFvalue : ∀ a, F a = ∫ x, f (x - a) * phi x := by
    intro a
    simp only [F, MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply', g]
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by simp only [neg_sub, mul_comm]
  let D : Nat → Real → Real := fun n x ↦
    (f (x + h n) - 2 * f x + f (x - h n)) / (h n) ^ 2 * phi x
  have hpair : ∀ n, (∫ x, D n x) =
      (F (h n) - 2 * F 0 + F (-h n)) / (h n) ^ 2 := by
    intro n
    have hp : Integrable (fun x ↦ f (x + h n) * phi x) := by
      have hi := (hf.comp_add_right (h n)).locallyIntegrable
      simpa only [smul_eq_mul] using
        hi.integrable_smul_right_of_hasCompactSupport hphi.continuous hsupp
    have hm : Integrable (fun x ↦ f (x - h n) * phi x) := by
      have hi := (hf.comp_sub_right (h n)).locallyIntegrable
      simpa only [smul_eq_mul] using
        hi.integrable_smul_right_of_hasCompactSupport hphi.continuous hsupp
    have hz : Integrable (fun x ↦ f x * phi x) := by
      simpa only [smul_eq_mul] using
        hf.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hphi.continuous hsupp
    calc
      (∫ x, D n x) =
          ∫ x, ((f (x + h n) * phi x - 2 * (f x * phi x)) +
            f (x - h n) * phi x) / (h n) ^ 2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x ↦ by dsimp only [D]; ring
      _ = ((∫ x, f (x + h n) * phi x) - 2 * (∫ x, f x * phi x) +
          (∫ x, f (x - h n) * phi x)) / (h n) ^ 2 := by
        have hadd := integral_add (hp.sub (hz.const_mul 2)) hm
        have hsub := integral_sub hp (hz.const_mul 2)
        simp only [Pi.sub_apply] at hadd hsub
        rw [integral_div, hadd, hsub, integral_const_mul]
      _ = _ := by
        rw [hFvalue, hFvalue, hFvalue]
        simp only [sub_zero, sub_neg_eq_add]
        ring
  have hhne : Tendsto h atTop (𝓝[≠] (0 : Real)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hh, Eventually.of_forall hne⟩
  have hpairlim : Tendsto (fun n ↦ ∫ x, D n x) atTop
      (𝓝 (∫ x, f x * deriv (deriv phi) x)) := by
    have hraw := (hF.tendsto_centered_second_difference 0).comp hhne
    simp only [Function.comp_def, zero_add, zero_sub, hFsecond] at hraw
    exact hraw.congr (fun n ↦ (hpair n).symm)
  exact hpairlim

end MeasureTheory

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E}
  [SFinite mu] [mu.IsAddLeftInvariant] [mu.IsNegInvariant]

theorem MeasureTheory.Integrable.tendsto_integral_mul_directional_second_difference
    {f phi : E → Real} (hf : Integrable f mu)
    (hphi : ContDiff Real 2 phi) (hsupp : HasCompactSupport phi) (v : E)
    (h : Nat → Real) (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0) :
    Tendsto (fun n ↦ ∫ x,
      (f (x + h n • v) - 2 * f x + f (x - h n • v)) / (h n) ^ 2 * phi x ∂mu)
      atTop (𝓝 (∫ x, f x * fderiv Real (fun y ↦ fderiv Real phi y v) x v ∂mu)) := by
  let g : E → Real := fun x ↦ f (-x)
  have hgint : Integrable g mu := hf.comp_neg
  let F : E → Real := phi ⋆[ContinuousLinearMap.mul Real Real, mu] g
  have hF : ContDiff Real 2 F :=
    hsupp.contDiff_convolution_left (ContinuousLinearMap.mul Real Real)
      hphi hgint.locallyIntegrable
  let psi : E → Real := fun x ↦ fderiv Real phi x v
  have hpsi : ContDiff Real 1 psi :=
    (hphi.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hpsisupp : HasCompactSupport psi := hsupp.fderiv_apply Real v
  let G : E → Real := psi ⋆[ContinuousLinearMap.mul Real Real, mu] g
  have hG : ContDiff Real 1 G :=
    hpsisupp.contDiff_convolution_left (ContinuousLinearMap.mul Real Real)
      hpsi hgint.locallyIntegrable
  have hFderiv : ∀ x, fderiv Real F x v = G x := fun x ↦
    hsupp.fderiv_convolution_left_apply (hphi.of_le (by norm_num))
      hgint.locallyIntegrable x v
  let A : Real → Real := fun t ↦ F (t • v)
  have hA : ContDiff Real 2 A := hF.comp (contDiff_id.smul_const v)
  have hAderiv : deriv A = fun t ↦ G (t • v) := by
    funext t
    have hfd : HasFDerivAt F (fderiv Real F (t • v)) (t • v) :=
      (hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have hraw := (hfd.comp_hasDerivAt t ((hasDerivAt_id t).smul_const v)).deriv
    simpa only [Function.comp_def, id_eq, one_smul, hFderiv, A] using hraw
  have hAsecond : deriv (deriv A) 0 =
      ∫ x, f x * fderiv Real psi x v ∂mu := by
    rw [hAderiv]
    have hgd : HasFDerivAt G (fderiv Real G ((0 : Real) • v)) ((0 : Real) • v) :=
      (hG.differentiable one_ne_zero).differentiableAt.hasFDerivAt
    have hraw := (hgd.comp_hasDerivAt 0 ((hasDerivAt_id (0 : Real)).smul_const v)).deriv
    have hGderiv := hpsisupp.fderiv_convolution_left_apply hpsi
      hgint.locallyIntegrable (0 : E) v
    simp only [Function.comp_def, id_eq, one_smul, zero_smul] at hraw
    rw [hGderiv] at hraw
    simpa only [MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply',
      g, zero_sub, neg_neg, mul_comm] using hraw
  have hAvalue : ∀ a, A a = ∫ x, f (x - a • v) * phi x ∂mu := by
    intro a
    simp only [A, F, MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply', g]
    apply integral_congr_ae
    exact Eventually.of_forall fun x ↦ by simp only [neg_sub, mul_comm]
  let D : Nat → E → Real := fun n x ↦
    (f (x + h n • v) - 2 * f x + f (x - h n • v)) / (h n) ^ 2 * phi x
  have hpair : ∀ n, (∫ x, D n x ∂mu) =
      (A (h n) - 2 * A 0 + A (-h n)) / (h n) ^ 2 := by
    intro n
    have hp : Integrable (fun x ↦ f (x + h n • v) * phi x) mu := by
      have hi := (hf.comp_add_right (h n • v)).locallyIntegrable
      simpa only [smul_eq_mul] using
        hi.integrable_smul_right_of_hasCompactSupport hphi.continuous hsupp
    have hm : Integrable (fun x ↦ f (x - h n • v) * phi x) mu := by
      have hi := (hf.comp_sub_right (h n • v)).locallyIntegrable
      simpa only [smul_eq_mul] using
        hi.integrable_smul_right_of_hasCompactSupport hphi.continuous hsupp
    have hz : Integrable (fun x ↦ f x * phi x) mu := by
      simpa only [smul_eq_mul] using
        hf.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hphi.continuous hsupp
    calc
      (∫ x, D n x ∂mu) =
          ∫ x, ((f (x + h n • v) * phi x - 2 * (f x * phi x)) +
            f (x - h n • v) * phi x) / (h n) ^ 2 ∂mu := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x ↦ by dsimp only [D]; ring
      _ = ((∫ x, f (x + h n • v) * phi x ∂mu) - 2 * (∫ x, f x * phi x ∂mu) +
          (∫ x, f (x - h n • v) * phi x ∂mu)) / (h n) ^ 2 := by
        have hadd := integral_add (hp.sub (hz.const_mul 2)) hm
        have hsub := integral_sub hp (hz.const_mul 2)
        simp only [Pi.sub_apply] at hadd hsub
        rw [integral_div, hadd, hsub, integral_const_mul]
      _ = _ := by
        rw [hAvalue, hAvalue, hAvalue]
        simp only [zero_smul, sub_zero, neg_smul, sub_neg_eq_add]
        ring
  have hhne : Tendsto h atTop (𝓝[≠] (0 : Real)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hh, Eventually.of_forall hne⟩
  have hraw := (hA.tendsto_centered_second_difference 0).comp hhne
  simp only [Function.comp_def, zero_add, zero_sub, hAsecond] at hraw
  exact hraw.congr (fun n ↦ (hpair n).symm)

end NormedSpace

end
