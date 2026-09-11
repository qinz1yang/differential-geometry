import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.CoefficientDerivative
import DifferentialGeometry.Analysis.Elliptic.Euclidean.WeakFormulation
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Commutation
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Divergence
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.ExistenceTheory

noncomputable section

open MeasureTheory Set Filter
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped ENNReal

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem weakGrad_apply_ae_eq_chosen
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Omega : Set E} (hOmega : IsOpen Omega)
    {u : E → ℝ} (hu : MemW1pWitness p u Omega) (i : Fin d) :
    (fun x => hu.weakGrad x i) =ᵐ[volume.restrict Omega]
      chosenWeakPartialOrZero p i u Omega :=
  HasWeakPartialDeriv.ae_eq hOmega (hu.isWeakGrad i)
    (chosenWeakPartialOrZero_isWeakPartial_of_mem hu.memW1p i)
    ((hu.weakGrad_component_memLp i).locallyIntegrable hp)
    ((chosenWeakPartialOrZero_memLp_of_mem hu.memW1p i).locallyIntegrable hp)

theorem hasWeakDiv_matMulE_chosenWeakPartialOrZero
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : MemW1pWitness 2 u Omega)
    (hweak : ∀ v, MemH01 v Omega → ∀ hv : MemW1pWitness 2 v Omega,
      bilinFormOfCoeff A hu hv = ∫ x in Omega, f x * v x)
    (hf : MemW1p 2 f Omega)
    {a : E → Matrix (Fin d) (Fin d) ℝ}
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x i j))
    {rho : ℝ} (hcoeff : ∀ x ∈ Omega, ∀ i j : Fin d, A.a x i j = rho * a x i j)
    (hu2 : MemWkp 2 2 u Omega) (l : Fin d)
    (hw : MemW1pWitness 2 (chosenWeakPartialOrZero 2 l u Omega) Omega) :
    HasWeakDiv (fun x => -(chosenWeakPartialOrZero 2 l f Omega x +
      rho * coefficientDerivativeSource 2 a u Omega l x))
      (fun x => matMulE (A.a x) (hw.weakGrad x)) Omega := by
  let F : E → E := fun x => matMulE (A.a x) (hu.weakGrad x)
  let D : E → E := fun x => matMulE (A.a x) (hw.weakGrad x)
  let C : E → E := coefficientDerivativeField 2 a u Omega l
  let G : E → E := fun x => D x + rho • C x
  let df : E → ℝ := chosenWeakPartialOrZero 2 l f Omega
  let g : E → ℝ := coefficientDerivativeSource 2 a u Omega l
  let w : Fin d → E → ℝ := fun j => chosenWeakPartialOrZero 2 j u Omega
  let z : Fin d → E → ℝ := fun j => chosenWeakPartialOrZero 2 l (w j) Omega
  have hF : MemLp F 2 (volume.restrict Omega) := A.memLp_matMulE hu.weakGrad_memLp
  have hD : MemLp D 2 (volume.restrict Omega) := A.memLp_matMulE hw.weakGrad_memLp
  have hdf : MemLp df 2 (volume.restrict Omega) := chosenWeakPartialOrZero_memLp_of_mem hf l
  have hw_mem : ∀ j, MemW1p 2 (w j) Omega :=
    fun j => MemWkp.one_iff_memW1p.mp (hu2.chosenWeakPartial_mem j)
  have hw_loc : ∀ j, LocallyIntegrable (w j) (volume.restrict Omega) :=
    fun j => (chosenWeakPartialOrZero_memLp_of_mem hu2.memW1p j).locallyIntegrable (by norm_num)
  have hz_loc : ∀ j, LocallyIntegrable (z j) (volume.restrict Omega) :=
    fun j => (chosenWeakPartialOrZero_memLp_of_mem (hw_mem j) l).locallyIntegrable (by norm_num)
  have hC_loc : ∀ i : Fin d, LocallyIntegrable (fun x => C x i) (volume.restrict Omega) :=
    locallyIntegrable_coefficientDerivativeField_apply (by norm_num)
      (fun i j => (ha i j).of_le (by norm_cast)) hu2.memW1p l
  have hG_loc : ∀ i : Fin d, LocallyIntegrable (fun x => G x i) (volume.restrict Omega) :=
    fun i => ((hD.continuousLinearMap_comp
      (EuclideanSpace.proj i : E →L[ℝ] ℝ)).locallyIntegrable (by norm_num)).add
      ((hC_loc i).continuous_mul continuous_const)
  have hg_loc : LocallyIntegrable g (volume.restrict Omega) :=
    locallyIntegrable_coefficientDerivativeSource (by norm_num)
      (fun i j => (ha i j).of_le (by norm_cast)) hu2 l
  have hgrad_u := ae_all_iff.mpr
    (fun i => weakGrad_apply_ae_eq_chosen (by norm_num) hOmega hu i)
  have hgrad_w := ae_all_iff.mpr
    (fun i => weakGrad_apply_ae_eq_chosen (by norm_num) hOmega hw i)
  have hcomm := ae_all_iff.mpr
    (fun j => chosenWeakPartialOrZero_comm (by norm_num) hOmega hu2 j l)
  have hda : ∀ i j x,
      (fderiv ℝ (fun y => rho * a y i j) x) (EuclideanSpace.single l 1) =
        rho * (fderiv ℝ (fun y => a y i j) x) (EuclideanSpace.single l 1) := by
    intro i j x
    rw [fderiv_const_mul ((ha i j).differentiable (by simp) x) rho]
    rfl
  have hparts : ∀ i : Fin d,
      HasWeakPartialDeriv l (fun x => G x i) (fun x => F x i) Omega := by
    intro i
    have hsmooth : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => rho * a x i j) :=
      fun j => contDiff_const.mul (ha i j)
    have hprod : ∀ j, HasWeakPartialDeriv l
        (fun x => (rho * a x i j) * z j x +
          (fderiv ℝ (fun y => rho * a y i j) x) (EuclideanSpace.single l 1) * w j x)
        (fun x => (rho * a x i j) * w j x) Omega := fun j =>
      (chosenWeakPartialOrZero_isWeakPartial_of_mem (hw_mem j) l).mul_smooth hOmega
        (hsmooth j) (hw_loc j) (hz_loc j)
    have hsum := HasWeakPartialDeriv.finset_sum Finset.univ
      (fun j _ => (hw_loc j).continuous_mul (hsmooth j).continuous)
      (fun j _ => ((hz_loc j).continuous_mul (hsmooth j).continuous).add
        ((hw_loc j).continuous_mul (contDiff_partial_eta (hsmooth j) l).continuous))
      (fun j _ => hprod j)
    apply hsum.congr_ae
    · filter_upwards [hgrad_u, ae_restrict_mem hOmega.measurableSet] with x hx hxO
      simp only [F, matMulE_apply, Matrix.mulVec, dotProduct, hcoeff x hxO, hx, w]
    · filter_upwards [hgrad_w, hcomm, ae_restrict_mem hOmega.measurableSet] with x hx hm hxO
      simp only [G, D, C, Pi.add_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, matMulE_apply,
        Matrix.mulVec, dotProduct, coefficientDerivativeField,
        hcoeff x hxO, hx, z, w, hm, hda, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have hdivF : HasWeakDiv (fun x => -f x) F Omega :=
    (bilinFormOfCoeff_eq_integral_iff_hasWeakDiv hOmega hu hf.1).mp hweak
  have hpartial : HasWeakPartialDeriv l (fun x => -df x) (fun x => -f x) Omega := by
    simpa only [neg_one_mul, smul_eq_mul] using
      (chosenWeakPartialOrZero_isWeakPartial_of_mem hf l).const_smul (-1)
  have hdivG := hdivF.comm hpartial hparts
    (fun i => (hF.continuousLinearMap_comp
      (EuclideanSpace.proj i : E →L[ℝ] ℝ)).locallyIntegrable (by norm_num)) hG_loc
  have hdivC : HasWeakDiv g C Omega :=
    hasWeakDiv_coefficientDerivativeField (by norm_num) hOmega ha hu2 l
  have hdivD : HasWeakDiv (fun x => -(df x + rho * g x)) D Omega := by
    have hsum := hdivG.add (hdivC.const_smul (-rho))
      hG_loc (fun i => (hC_loc i).continuous_mul continuous_const)
      (hdf.neg.locallyIntegrable (by norm_num))
      (hg_loc.continuous_mul continuous_const)
    apply hsum.congr_ae
    · filter_upwards with x
      dsimp only [Pi.add_apply]
      ring
    · filter_upwards with x
      dsimp only [Pi.add_apply, G]
      rw [neg_smul, add_neg_cancel_right]
  exact hdivD

theorem bilinFormOfCoeff_chosenWeakPartialOrZero_eq_integral_of_isSmoothTestOn
    {Omega : Set E} (hOmega : IsOpen Omega)
    {A : EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : MemW1pWitness 2 u Omega)
    (hweak : ∀ v, MemH01 v Omega → ∀ hv : MemW1pWitness 2 v Omega,
      bilinFormOfCoeff A hu hv = ∫ x in Omega, f x * v x)
    (hf : MemW1p 2 f Omega)
    {a : E → Matrix (Fin d) (Fin d) ℝ}
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x i j))
    {rho : ℝ} (hcoeff : ∀ x ∈ Omega, ∀ i j : Fin d, A.a x i j = rho * a x i j)
    (hu2 : MemWkp 2 2 u Omega) (l : Fin d)
    (hw : MemW1pWitness 2 (chosenWeakPartialOrZero 2 l u Omega) Omega)
    {phi : E → ℝ} (hphi : IsSmoothTestOn Omega phi) :
    bilinFormOfCoeff A hw (smoothTestWitness hOmega hphi) =
      ∫ x in Omega, (chosenWeakPartialOrZero 2 l f Omega x +
        rho * coefficientDerivativeSource 2 a u Omega l x) * phi x := by
  have h := hasWeakDiv_matMulE_chosenWeakPartialOrZero hOmega hu hweak hf ha hcoeff hu2 l hw
    phi hphi.1 hphi.2.1 hphi.2.2
  simp only [neg_mul, integral_neg, neg_neg] at h
  simpa [bilinFormOfCoeff, bilinFormIntegrandOfCoeff, PiLp.inner_apply,
    smoothTestWitness, smoothGradField, mul_comm] using! h

theorem bilinFormOfCoeff_chosenWeakPartialOrZero_eq_integral
    {Omega : Set E} (hOmega : IsOpen Omega) (hcompact : IsCompact (closure Omega))
    {A : EllipticCoeff d Omega} {u f : E → ℝ}
    (hu : MemW1pWitness 2 u Omega)
    (hweak : ∀ v, MemH01 v Omega → ∀ hv : MemW1pWitness 2 v Omega,
      bilinFormOfCoeff A hu hv = ∫ x in Omega, f x * v x)
    (hf : MemW1p 2 f Omega)
    {a : E → Matrix (Fin d) (Fin d) ℝ}
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x i j))
    {rho : ℝ} (hcoeff : ∀ x ∈ Omega, ∀ i j : Fin d, A.a x i j = rho * a x i j)
    (hu2 : MemWkp 2 2 u Omega) (l : Fin d)
    (hw : MemW1pWitness 2 (chosenWeakPartialOrZero 2 l u Omega) Omega)
    (v : E → ℝ) (hv0 : MemH01 v Omega) (hv : MemW1pWitness 2 v Omega) :
    bilinFormOfCoeff A hw hv =
      ∫ x in Omega, (chosenWeakPartialOrZero 2 l f Omega x +
        rho * coefficientDerivativeSource 2 a u Omega l x) * v x :=
  (bilinFormOfCoeff_eq_integral_iff_hasWeakDiv hOmega hw
    ((chosenWeakPartialOrZero_memLp_of_mem hf l).add
      ((memLp_coefficientDerivativeSource hOmega.measurableSet hcompact ha hu2 l).const_mul rho))).mpr
    (hasWeakDiv_matMulE_chosenWeakPartialOrZero hOmega hu hweak hf ha hcoeff hu2 l hw) v hv0 hv

theorem IsSolution.bilinFormOfCoeff_chosenWeakPartialOrZero_eq_integral
    {Omega : Set E} (hOmega : IsOpen Omega) (hcompact : IsCompact (closure Omega))
    {A : EllipticCoeff d Omega} {u : E → ℝ} (hsol : IsSolution A u)
    {a : E → Matrix (Fin d) (Fin d) ℝ}
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x i j))
    {rho : ℝ} (hcoeff : ∀ x ∈ Omega, ∀ i j : Fin d, A.a x i j = rho * a x i j)
    (hu2 : MemWkp 2 2 u Omega) (l : Fin d)
    (hw : MemW1pWitness 2 (chosenWeakPartialOrZero 2 l u Omega) Omega)
    (v : E → ℝ) (hv0 : MemH01 v Omega) (hv : MemW1pWitness 2 v Omega) :
    bilinFormOfCoeff A hw hv =
      ∫ x in Omega, (rho * coefficientDerivativeSource 2 a u Omega l x) * v x := by
  let hu := MemW1p.someWitness hu2.memW1p
  have hweak : ∀ z, MemH01 z Omega → ∀ hz : MemW1pWitness 2 z Omega,
      bilinFormOfCoeff A hu hz = ∫ x in Omega, (0 : ℝ) * z x := by
    intro z hz0 hz
    simpa only [zero_mul, integral_zero] using hsol.bilinFormOfCoeff_eq_zero hOmega hu hz0 hz
  rw [DeGiorgi.bilinFormOfCoeff_chosenWeakPartialOrZero_eq_integral hOmega hcompact hu hweak
    (MemWkp_zero_fun (k := 1) (by norm_num) hOmega).memW1p ha hcoeff hu2 l hw v hv0 hv]
  apply integral_congr_ae
  filter_upwards [chosenWeakPartialOrZero_ae_zero_of_ae_zero (p := 2) (by norm_num) hOmega
    (Eventually.of_forall fun _ => rfl) l] with x hx
  rw [hx, zero_add]

end DeGiorgi
