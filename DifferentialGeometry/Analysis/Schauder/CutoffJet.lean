import DifferentialGeometry.Analysis.Schauder.BilinearHolder
import DifferentialGeometry.Analysis.Schauder.CutoffProduct

noncomputable section

open scoped NNReal

namespace DifferentialGeometry.Analysis.Schauder

variable {V F : Type*}
  [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

def cutoffJet2SupConst
    (Mchi Mdchi Md2chi Mu Mdu Md2u : NNReal) : NNReal :=
  Mchi * Md2u + 2 * (Mdchi * Mdu) + Md2chi * Mu

def cutoffJet2HolderConst
    (Kchi Kdchi Kd2chi Ku Kdu Kd2u
      Mchi Mdchi Md2chi Mu Mdu Md2u : NNReal) : NNReal :=
  Mchi * Kd2u + Md2u * Kchi +
    2 * (Mdchi * Kdu + Mdu * Kdchi) +
    Md2chi * Ku + Mu * Kd2chi

theorem norm_cutoffJet2_le
    (chi : BoundedContinuousFunction V Real)
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (d2chi : BoundedContinuousFunction V (V →L[Real] V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (Mchi Mdchi Md2chi Mu Mdu Md2u : NNReal)
    (hchiNorm : ∀ x, ‖chi x‖ ≤ Mchi)
    (hdchiNorm : ∀ x, ‖dchi x‖ ≤ Mdchi)
    (hd2chiNorm : ∀ x, ‖d2chi x‖ ≤ Md2chi)
    (huNorm : ∀ x, ‖u x‖ ≤ Mu)
    (hduNorm : ∀ x, ‖du x‖ ≤ Mdu)
    (hd2uNorm : ∀ x, ‖d2u x‖ ≤ Md2u)
    (x : V) :
    ‖cutoffJet2 chi dchi d2chi u du d2u x‖ ≤
      cutoffJet2SupConst Mchi Mdchi Md2chi Mu Mdu Md2u := by
  letI : SeminormedAddCommGroup (V →L[Real] F) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  letI : NormedSpace Real (V →L[Real] F) :=
    ContinuousLinearMap.toNormedSpace
  letI : SeminormedAddCommGroup (V →L[Real] V →L[Real] F) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  letI : NormedSpace Real (V →L[Real] V →L[Real] F) :=
    ContinuousLinearMap.toNormedSpace
  let L₁ := ContinuousLinearMap.smulRightL Real V (V →L[Real] F)
  let L₂ := ContinuousLinearMap.precompR V
    (ContinuousLinearMap.smulRightL Real V F)
  let L₃ := ContinuousLinearMap.precompL V
    (ContinuousLinearMap.smulRightL Real V F)
  have hL₁ : ‖L₁‖ ≤ 1 := ContinuousLinearMap.norm_smulRightL_le
  have hL₂ : ‖L₂‖ ≤ 1 :=
    (ContinuousLinearMap.norm_precompR_le V
      (ContinuousLinearMap.smulRightL Real V F)).trans
        ContinuousLinearMap.norm_smulRightL_le
  have hL₃ : ‖L₃‖ ≤ 1 :=
    (ContinuousLinearMap.norm_precompL_le V
      (ContinuousLinearMap.smulRightL Real V F)).trans
        ContinuousLinearMap.norm_smulRightL_le
  have hfirst : ‖chi x • d2u x‖ ≤ (Mchi * Md2u : NNReal) := by
    rw [norm_smul]
    exact_mod_cast mul_le_mul (hchiNorm x) (hd2uNorm x)
      (norm_nonneg _) Mchi.coe_nonneg
  have hsecond : ‖L₁ (dchi x) (du x)‖ ≤ (Mdchi * Mdu : NNReal) := by
    simpa only [one_mul, NNReal.coe_mul] using
      L₁.le_of_opNorm₂_le_of_le hL₁ (hdchiNorm x) (hduNorm x)
  have hthird : ‖L₂ (dchi x) (du x)‖ ≤ (Mdchi * Mdu : NNReal) := by
    simpa only [one_mul, NNReal.coe_mul] using
      L₂.le_of_opNorm₂_le_of_le hL₂ (hdchiNorm x) (hduNorm x)
  have hfourth : ‖L₃ (d2chi x) (u x)‖ ≤ (Md2chi * Mu : NNReal) := by
    simpa only [one_mul, NNReal.coe_mul] using
      L₃.le_of_opNorm₂_le_of_le hL₃ (hd2chiNorm x) (huNorm x)
  rw [cutoffJet2_apply]
  calc
    ‖chi x • d2u x + L₁ (dchi x) (du x) +
        L₂ (dchi x) (du x) + L₃ (d2chi x) (u x)‖ ≤
      ‖chi x • d2u x‖ + ‖L₁ (dchi x) (du x)‖ +
        ‖L₂ (dchi x) (du x)‖ + ‖L₃ (d2chi x) (u x)‖ := norm_add₄_le
    _ ≤ (Mchi * Md2u : NNReal) + (Mdchi * Mdu : NNReal) +
        (Mdchi * Mdu : NNReal) + (Md2chi * Mu : NNReal) :=
      add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hfourth
    _ = cutoffJet2SupConst Mchi Mdchi Md2chi Mu Mdu Md2u := by
      simp only [cutoffJet2SupConst, NNReal.coe_add, NNReal.coe_mul,
        two_mul]
      ring

private theorem cutoffJet2_smulRight_holderWith
    {alpha Kdchi Kdu Mdchi Mdu : NNReal}
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (hdchi : HolderWith Kdchi alpha (dchi : V → V →L[Real] Real))
    (hdu : HolderWith Kdu alpha (du : V → V →L[Real] F))
    (hdchiNorm : ∀ x, ‖dchi x‖ ≤ Mdchi)
    (hduNorm : ∀ x, ‖du x‖ ≤ Mdu) :
    HolderWith (Mdchi * Kdu + Mdu * Kdchi) alpha
      (fun x ↦ (ContinuousLinearMap.smulRightL Real V (V →L[Real] F))
        (dchi x) (du x)) := by
  have hbilinear : ∀ (c : V →L[Real] Real) (f : V →L[Real] F),
      ‖(ContinuousLinearMap.smulRightL Real V (V →L[Real] F)) c f‖ ≤
        ‖c‖ * ‖f‖ := by
    intro c f
    change ‖c.smulRight f‖ ≤ ‖c‖ * ‖f‖
    exact (ContinuousLinearMap.norm_smulRight_apply c f).le
  exact @holderWith_bilinear_of_norm_le
    V (V →L[Real] Real) (V →L[Real] F)
    (V →L[Real] V →L[Real] F)
    inferInstance
    ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
    ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
    ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
    alpha Kdchi Kdu Mdchi Mdu
    (ContinuousLinearMap.smulRightL Real V (V →L[Real] F)) hbilinear
    (dchi : V → V →L[Real] Real) (du : V → V →L[Real] F)
    hdchi hdu hdchiNorm hduNorm

private theorem cutoffJet2_precompR_holderWith
    {alpha Kdchi Kdu Mdchi Mdu : NNReal}
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (hdchi : HolderWith Kdchi alpha (dchi : V → V →L[Real] Real))
    (hdu : HolderWith Kdu alpha (du : V → V →L[Real] F))
    (hdchiNorm : ∀ x, ‖dchi x‖ ≤ Mdchi)
    (hduNorm : ∀ x, ‖du x‖ ≤ Mdu) :
    HolderWith (Mdchi * Kdu + Mdu * Kdchi) alpha
      (fun x ↦ (ContinuousLinearMap.precompR V
        (ContinuousLinearMap.smulRightL Real V F)) (dchi x) (du x)) := by
  have hbilinear : ∀ (c : V →L[Real] Real) (A : V →L[Real] F),
      ‖(ContinuousLinearMap.precompR V
        (ContinuousLinearMap.smulRightL Real V F)) c A‖ ≤ ‖c‖ * ‖A‖ := by
    intro c A
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (norm_nonneg c) (norm_nonneg A)) ?_
    intro v
    change ‖c.smulRight (A v)‖ ≤ (‖c‖ * ‖A‖) * ‖v‖
    rw [ContinuousLinearMap.norm_smulRight_apply]
    calc
      ‖c‖ * ‖A v‖ ≤ ‖c‖ * (‖A‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (A.le_opNorm v) (norm_nonneg c)
      _ = (‖c‖ * ‖A‖) * ‖v‖ := by ring
  exact @holderWith_bilinear_of_norm_le
    V (V →L[Real] Real) (V →L[Real] F)
    (V →L[Real] V →L[Real] F)
    inferInstance
    ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
    ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
    ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
    alpha Kdchi Kdu Mdchi Mdu
    (ContinuousLinearMap.precompR V
      (ContinuousLinearMap.smulRightL Real V F)) hbilinear
    (dchi : V → V →L[Real] Real) (du : V → V →L[Real] F)
    hdchi hdu hdchiNorm hduNorm

private theorem cutoffJet2_precompL_holderWith
    {alpha Kd2chi Ku Md2chi Mu : NNReal}
    (d2chi : BoundedContinuousFunction V (V →L[Real] V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (hd2chi : HolderWith Kd2chi alpha
      (d2chi : V → V →L[Real] V →L[Real] Real))
    (hu : HolderWith Ku alpha (u : V → F))
    (hd2chiNorm : ∀ x, ‖d2chi x‖ ≤ Md2chi)
    (huNorm : ∀ x, ‖u x‖ ≤ Mu) :
    HolderWith (Md2chi * Ku + Mu * Kd2chi) alpha
      (fun x ↦ (ContinuousLinearMap.precompL V
        (ContinuousLinearMap.smulRightL Real V F)) (d2chi x) (u x)) := by
  have hbilinear : ∀ (D : V →L[Real] V →L[Real] Real) (u : F),
      ‖(ContinuousLinearMap.precompL V
        (ContinuousLinearMap.smulRightL Real V F)) D u‖ ≤ ‖D‖ * ‖u‖ := by
    intro D u
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (norm_nonneg D) (norm_nonneg u)) ?_
    intro v
    change ‖(D v).smulRight u‖ ≤ (‖D‖ * ‖u‖) * ‖v‖
    rw [ContinuousLinearMap.norm_smulRight_apply]
    calc
      ‖D v‖ * ‖u‖ ≤ (‖D‖ * ‖v‖) * ‖u‖ :=
        mul_le_mul_of_nonneg_right (D.le_opNorm v) (norm_nonneg u)
      _ = (‖D‖ * ‖u‖) * ‖v‖ := by ring
  exact @holderWith_bilinear_of_norm_le
    V (V →L[Real] V →L[Real] Real) F
    (V →L[Real] V →L[Real] F)
    inferInstance
    ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
    inferInstance inferInstance
    ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
    alpha Kd2chi Ku Md2chi Mu
    (ContinuousLinearMap.precompL V
      (ContinuousLinearMap.smulRightL Real V F)) hbilinear
    (d2chi : V → V →L[Real] V →L[Real] Real) (u : V → F)
    hd2chi hu hd2chiNorm huNorm

theorem cutoffJet2_holderWith
    {alpha Kchi Kdchi Kd2chi Ku Kdu Kd2u
      Mchi Mdchi Md2chi Mu Mdu Md2u : NNReal}
    (chi : BoundedContinuousFunction V Real)
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (d2chi : BoundedContinuousFunction V (V →L[Real] V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hchi : HolderWith Kchi alpha (chi : V → Real))
    (hdchi : HolderWith Kdchi alpha (dchi : V → V →L[Real] Real))
    (hd2chi : HolderWith Kd2chi alpha
      (d2chi : V → V →L[Real] V →L[Real] Real))
    (hu : HolderWith Ku alpha (u : V → F))
    (hdu : HolderWith Kdu alpha (du : V → V →L[Real] F))
    (hd2u : HolderWith Kd2u alpha
      (d2u : V → V →L[Real] V →L[Real] F))
    (hchiNorm : ∀ x, ‖chi x‖ ≤ Mchi)
    (hdchiNorm : ∀ x, ‖dchi x‖ ≤ Mdchi)
    (hd2chiNorm : ∀ x, ‖d2chi x‖ ≤ Md2chi)
    (huNorm : ∀ x, ‖u x‖ ≤ Mu)
    (hduNorm : ∀ x, ‖du x‖ ≤ Mdu)
    (hd2uNorm : ∀ x, ‖d2u x‖ ≤ Md2u) :
    HolderWith (cutoffJet2HolderConst
      Kchi Kdchi Kd2chi Ku Kdu Kd2u
      Mchi Mdchi Md2chi Mu Mdu Md2u) alpha
      (cutoffJet2 chi dchi d2chi u du d2u :
        V → V →L[Real] V →L[Real] F) := by
  let L₁ := ContinuousLinearMap.smulRightL Real V (V →L[Real] F)
  let L₂ := ContinuousLinearMap.precompR V
    (ContinuousLinearMap.smulRightL Real V F)
  let L₃ := ContinuousLinearMap.precompL V
    (ContinuousLinearMap.smulRightL Real V F)
  have hfirst : HolderWith (Mchi * Kd2u + Md2u * Kchi) alpha
      (fun x ↦ chi x • d2u x) :=
    holderWith_smul_of_norm_le hchi hd2u hchiNorm hd2uNorm
  have hsecond : HolderWith (Mdchi * Kdu + Mdu * Kdchi) alpha
      (fun x ↦ L₁ (dchi x) (du x)) :=
    cutoffJet2_smulRight_holderWith dchi du hdchi hdu hdchiNorm hduNorm
  have hthird : HolderWith (Mdchi * Kdu + Mdu * Kdchi) alpha
      (fun x ↦ L₂ (dchi x) (du x)) :=
    cutoffJet2_precompR_holderWith dchi du hdchi hdu hdchiNorm hduNorm
  have hfourth : HolderWith (Md2chi * Ku + Mu * Kd2chi) alpha
      (fun x ↦ L₃ (d2chi x) (u x)) :=
    cutoffJet2_precompL_holderWith d2chi u hd2chi hu hd2chiNorm huNorm
  have hall : HolderWith
      ((Mchi * Kd2u + Md2u * Kchi) +
        (Mdchi * Kdu + Mdu * Kdchi) +
        (Mdchi * Kdu + Mdu * Kdchi) +
        (Md2chi * Ku + Mu * Kd2chi)) alpha
      (fun x ↦ chi x • d2u x + L₁ (dchi x) (du x) +
        L₂ (dchi x) (du x) + L₃ (d2chi x) (u x)) :=
    hfirst.add hsecond |>.add hthird |>.add hfourth
  rw [show (cutoffJet2 chi dchi d2chi u du d2u :
      V → V →L[Real] V →L[Real] F) =
      fun x ↦ chi x • d2u x + L₁ (dchi x) (du x) +
        L₂ (dchi x) (du x) + L₃ (d2chi x) (u x) from by
    funext x
    exact cutoffJet2_apply chi dchi d2chi u du d2u x]
  simpa only [cutoffJet2HolderConst, two_mul, add_assoc] using hall

theorem cutoffJet2_eq_zero_of_cutoff_eq_zero
    (chi : BoundedContinuousFunction V Real)
    (dchi : BoundedContinuousFunction V (V →L[Real] Real))
    (d2chi : BoundedContinuousFunction V (V →L[Real] V →L[Real] Real))
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[Real] F))
    (d2u : BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (x : V) (hchi : chi x = 0) (hdchi : dchi x = 0)
    (hd2chi : d2chi x = 0) :
    cutoffJet2 chi dchi d2chi u du d2u x = 0 := by
  rw [cutoffJet2_apply, hchi, hdchi, hd2chi]
  simp

end DifferentialGeometry.Analysis.Schauder

end
