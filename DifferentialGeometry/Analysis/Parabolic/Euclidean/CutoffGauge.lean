import DifferentialGeometry.Analysis.Parabolic.Euclidean.Cutoff
import DifferentialGeometry.Analysis.Schauder.CutoffJet

noncomputable section

open Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n]
  [NormedAddCommGroup F] [NormedSpace Real F]

def parabolicCutoffSpatialJet1SupConst
    (Mchi Mdchi Mu Mdu : NNReal) : NNReal :=
  Mchi * Mdu + Mdchi * Mu

def parabolicCutoffSpatialJet1HolderConst
    (Kchi Kdchi Ku Kdu Mchi Mdchi Mu Mdu : NNReal) : NNReal :=
  Mchi * Kdu + Mdu * Kchi + Mdchi * Ku + Mu * Kdchi

def parabolicCutoffTimeDerivativeSupConst
    (Mchi MdtimeChi Mu MdtimeU : NNReal) : NNReal :=
  Mchi * MdtimeU + MdtimeChi * Mu

def parabolicCutoffTimeDerivativeHolderConst
    (Kchi KdtimeChi Ku KdtimeU Mchi MdtimeChi Mu MdtimeU : NNReal) :
    NNReal :=
  Mchi * KdtimeU + MdtimeU * Kchi +
    MdtimeChi * Ku + Mu * KdtimeChi

def parabolicCutoffC2HolderGaugeConst
    (Kchi KdtimeChi Kdchi Kd2chi Ku KdtimeU Kdu Kd2u
      Mchi MdtimeChi Mdchi Md2chi Mu MdtimeU Mdu Md2u : NNReal) : NNReal :=
  Mchi * Mu +
    parabolicCutoffSpatialJet1SupConst Mchi Mdchi Mu Mdu +
    cutoffJet2SupConst Mchi Mdchi Md2chi Mu Mdu Md2u +
    parabolicCutoffTimeDerivativeSupConst Mchi MdtimeChi Mu MdtimeU +
    cutoffJet2HolderConst Kchi Kdchi Kd2chi Ku Kdu Kd2u
      Mchi Mdchi Md2chi Mu Mdu Md2u +
    parabolicCutoffTimeDerivativeHolderConst
      Kchi KdtimeChi Ku KdtimeU Mchi MdtimeChi Mu MdtimeU

theorem norm_parabolicCutoffSpatialJet1_le
    (chi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (Mchi Mdchi Mu Mdu : NNReal)
    (p : ParabolicPoint (Euc n))
    (hchiNorm : ‖chi p‖ ≤ Mchi)
    (hdchiNorm : ‖dchi p‖ ≤ Mdchi)
    (huNorm : ‖u p.time p.space‖ ≤ Mu)
    (hduNorm : ‖du p‖ ≤ Mdu) :
    ‖parabolicCutoffSpatialJet1 chi dchi u du p‖ ≤
      parabolicCutoffSpatialJet1SupConst Mchi Mdchi Mu Mdu := by
  rw [parabolicCutoffSpatialJet1_apply]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]
    exact_mod_cast mul_le_mul hchiNorm hduNorm
      (norm_nonneg _) Mchi.coe_nonneg
  · rw [ContinuousLinearMap.norm_smulRight_apply]
    exact_mod_cast mul_le_mul hdchiNorm huNorm
      (norm_nonneg _) Mdchi.coe_nonneg

theorem norm_parabolicCutoffSpatialJet2_le
    (chi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (d2u : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] F)
    (Mchi Mdchi Md2chi Mu Mdu Md2u : NNReal)
    (p : ParabolicPoint (Euc n))
    (hchiNorm : ‖chi p‖ ≤ Mchi)
    (hdchiNorm : ‖dchi p‖ ≤ Mdchi)
    (hd2chiNorm : ‖d2chi p‖ ≤ Md2chi)
    (huNorm : ‖u p.time p.space‖ ≤ Mu)
    (hduNorm : ‖du p‖ ≤ Mdu)
    (hd2uNorm : ‖d2u p‖ ≤ Md2u) :
    ‖parabolicCutoffSpatialJet2 chi dchi d2chi u du d2u p‖ ≤
      cutoffJet2SupConst Mchi Mdchi Md2chi Mu Mdu Md2u := by
  let L₁ := ContinuousLinearMap.smulRightL Real (Euc n)
    (Euc n →L[Real] F)
  let L₂ := ContinuousLinearMap.precompR (Euc n)
    (ContinuousLinearMap.smulRightL Real (Euc n) F)
  let L₃ := ContinuousLinearMap.precompL (Euc n)
    (ContinuousLinearMap.smulRightL Real (Euc n) F)
  have hL₁ : ‖L₁‖ ≤ 1 := ContinuousLinearMap.norm_smulRightL_le
  have hL₂ : ‖L₂‖ ≤ 1 :=
    (ContinuousLinearMap.norm_precompR_le (Euc n)
      (ContinuousLinearMap.smulRightL Real (Euc n) F)).trans
        ContinuousLinearMap.norm_smulRightL_le
  have hL₃ : ‖L₃‖ ≤ 1 :=
    (ContinuousLinearMap.norm_precompL_le (Euc n)
      (ContinuousLinearMap.smulRightL Real (Euc n) F)).trans
        ContinuousLinearMap.norm_smulRightL_le
  have hfirst : ‖chi p • d2u p‖ ≤ (Mchi * Md2u : NNReal) := by
    rw [norm_smul]
    exact_mod_cast mul_le_mul hchiNorm hd2uNorm
      (norm_nonneg _) Mchi.coe_nonneg
  have hsecond : ‖L₁ (dchi p) (du p)‖ ≤ (Mdchi * Mdu : NNReal) := by
    simpa only [one_mul, NNReal.coe_mul] using
      L₁.le_of_opNorm₂_le_of_le hL₁ hdchiNorm hduNorm
  have hthird : ‖L₂ (dchi p) (du p)‖ ≤ (Mdchi * Mdu : NNReal) := by
    simpa only [one_mul, NNReal.coe_mul] using
      L₂.le_of_opNorm₂_le_of_le hL₂ hdchiNorm hduNorm
  have hfourth : ‖L₃ (d2chi p) (u p.time p.space)‖ ≤
      (Md2chi * Mu : NNReal) := by
    simpa only [one_mul, NNReal.coe_mul] using
      L₃.le_of_opNorm₂_le_of_le hL₃ hd2chiNorm huNorm
  unfold parabolicCutoffSpatialJet2
  calc
    ‖chi p • d2u p + L₁ (dchi p) (du p) +
        L₂ (dchi p) (du p) + L₃ (d2chi p) (u p.time p.space)‖ ≤
      ‖chi p • d2u p‖ + ‖L₁ (dchi p) (du p)‖ +
        ‖L₂ (dchi p) (du p)‖ +
          ‖L₃ (d2chi p) (u p.time p.space)‖ := norm_add₄_le
    _ ≤ (Mchi * Md2u : NNReal) + (Mdchi * Mdu : NNReal) +
        (Mdchi * Mdu : NNReal) + (Md2chi * Mu : NNReal) :=
      add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hfourth
    _ = cutoffJet2SupConst Mchi Mdchi Md2chi Mu Mdu Md2u := by
      simp only [cutoffJet2SupConst, NNReal.coe_add, NNReal.coe_mul, two_mul]
      ring

omit [Fintype n] in
theorem norm_parabolicCutoffTimeDerivative_le
    (chi dtimeChi : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (dtimeU : ParabolicPoint (Euc n) → F)
    (Mchi MdtimeChi Mu MdtimeU : NNReal)
    (p : ParabolicPoint (Euc n))
    (hchiNorm : ‖chi p‖ ≤ Mchi)
    (hdtimeChiNorm : ‖dtimeChi p‖ ≤ MdtimeChi)
    (huNorm : ‖u p.time p.space‖ ≤ Mu)
    (hdtimeUNorm : ‖dtimeU p‖ ≤ MdtimeU) :
    ‖parabolicCutoffTimeDerivative chi dtimeChi u dtimeU p‖ ≤
      parabolicCutoffTimeDerivativeSupConst Mchi MdtimeChi Mu MdtimeU := by
  unfold parabolicCutoffTimeDerivative
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]
    exact_mod_cast mul_le_mul hchiNorm hdtimeUNorm
      (norm_nonneg _) Mchi.coe_nonneg
  · rw [norm_smul]
    exact_mod_cast mul_le_mul hdtimeChiNorm huNorm
      (norm_nonneg _) MdtimeChi.coe_nonneg

theorem parabolicCutoffSpatialJet1_holderWith_restrict
    {Q : Set (ParabolicPoint (Euc n))}
    {alpha Kchi Kdchi Ku Kdu Mchi Mdchi Mu Mdu : NNReal}
    (chi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (hchi : HolderWith Kchi alpha (Q.restrict chi))
    (hdchi : HolderWith Kdchi alpha (Q.restrict dchi))
    (hu : HolderWith Ku alpha
      (Q.restrict (fun p ↦ u p.time p.space)))
    (hdu : HolderWith Kdu alpha (Q.restrict du))
    (hchiNorm : ∀ p, p ∈ Q → ‖chi p‖ ≤ Mchi)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu)
    (hduNorm : ∀ p, p ∈ Q → ‖du p‖ ≤ Mdu) :
    HolderWith (parabolicCutoffSpatialJet1HolderConst
      Kchi Kdchi Ku Kdu Mchi Mdchi Mu Mdu) alpha
      (Q.restrict (parabolicCutoffSpatialJet1 chi dchi u du)) := by
  let L := ContinuousLinearMap.smulRightL Real (Euc n) F
  have hfirst : HolderWith (Mchi * Kdu + Mdu * Kchi) alpha
      (fun p : Q ↦ chi p.1 • du p.1) :=
    holderWith_smul_of_norm_le hchi hdu
      (fun p ↦ hchiNorm p.1 p.2) (fun p ↦ hduNorm p.1 p.2)
  have hsecond : HolderWith (Mdchi * Ku + Mu * Kdchi) alpha
      (fun p : Q ↦ L (dchi p.1) (u p.1.time p.1.space)) := by
    apply holderWith_bilinear_of_opNorm_le_one L
      ContinuousLinearMap.norm_smulRightL_le hdchi hu
    · exact fun p ↦ hdchiNorm p.1 p.2
    · exact fun p ↦ huNorm p.1 p.2
  have hsum := hfirst.add hsecond
  simpa only [parabolicCutoffSpatialJet1HolderConst,
    parabolicCutoffSpatialJet1, Set.restrict_apply, Pi.add_apply,
    add_assoc] using hsum

theorem parabolicCutoffSpatialJet1_holderWith_restrict_of_eq_zero_outside
    {Q U : Set (ParabolicPoint (Euc n))}
    {alpha Kchi Kdchi Ku Kdu Mchi Mdchi Mu Mdu : NNReal}
    (chi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (hchi : HolderWith Kchi alpha (Q.restrict chi))
    (hdchi : HolderWith Kdchi alpha (Q.restrict dchi))
    (hu : HolderWith Ku alpha
      ((Q ∩ U).restrict (fun p ↦ u p.time p.space)))
    (hdu : HolderWith Kdu alpha ((Q ∩ U).restrict du))
    (hchiNorm : ∀ p, p ∈ Q → p ∈ U → ‖chi p‖ ≤ Mchi)
    (hdchiNorm : ∀ p, p ∈ Q → p ∈ U → ‖dchi p‖ ≤ Mdchi)
    (huNorm : ∀ p, p ∈ Q → p ∈ U → ‖u p.time p.space‖ ≤ Mu)
    (hduNorm : ∀ p, p ∈ Q → p ∈ U → ‖du p‖ ≤ Mdu)
    (hchiZero : ∀ p, p ∈ Q → p ∉ U → chi p = 0)
    (hdchiZero : ∀ p, p ∈ Q → p ∉ U → dchi p = 0) :
    HolderWith (parabolicCutoffSpatialJet1HolderConst
      Kchi Kdchi Ku Kdu Mchi Mdchi Mu Mdu) alpha
      (Q.restrict (parabolicCutoffSpatialJet1 chi dchi u du)) := by
  let L := ContinuousLinearMap.smulRightL Real (Euc n) F
  have hfirst : HolderWith (Mchi * Kdu + Mdu * Kchi) alpha
      (Q.restrict (fun p ↦ chi p • du p)) :=
    holderWith_smul_of_eq_zero_outside chi du hchi hdu
      hchiNorm hduNorm hchiZero
  have hsecond : HolderWith (Mdchi * Ku + Mu * Kdchi) alpha
      (Q.restrict (fun p ↦ L (dchi p) (u p.time p.space))) := by
    apply holderWith_bilinear_of_opNorm_le_one_of_eq_zero_outside
      L ContinuousLinearMap.norm_smulRightL_le dchi
        (fun p ↦ u p.time p.space) hdchi hu
    · exact hdchiNorm
    · exact huNorm
    · exact hdchiZero
  have hsum := hfirst.add hsecond
  simpa only [parabolicCutoffSpatialJet1HolderConst,
    parabolicCutoffSpatialJet1, Set.restrict_apply, Pi.add_apply,
    add_assoc] using hsum

theorem parabolicCutoffSpatialJet2_holderWith_restrict
    {Q : Set (ParabolicPoint (Euc n))}
    {alpha Kchi Kdchi Kd2chi Ku Kdu Kd2u
      Mchi Mdchi Md2chi Mu Mdu Md2u : NNReal}
    (chi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (d2u : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] F)
    (hchi : HolderWith Kchi alpha (Q.restrict chi))
    (hdchi : HolderWith Kdchi alpha (Q.restrict dchi))
    (hd2chi : HolderWith Kd2chi alpha (Q.restrict d2chi))
    (hu : HolderWith Ku alpha
      (Q.restrict (fun p ↦ u p.time p.space)))
    (hdu : HolderWith Kdu alpha (Q.restrict du))
    (hd2u : HolderWith Kd2u alpha (Q.restrict d2u))
    (hchiNorm : ∀ p, p ∈ Q → ‖chi p‖ ≤ Mchi)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (hd2chiNorm : ∀ p, p ∈ Q → ‖d2chi p‖ ≤ Md2chi)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu)
    (hduNorm : ∀ p, p ∈ Q → ‖du p‖ ≤ Mdu)
    (hd2uNorm : ∀ p, p ∈ Q → ‖d2u p‖ ≤ Md2u) :
    HolderWith (cutoffJet2HolderConst
      Kchi Kdchi Kd2chi Ku Kdu Kd2u
      Mchi Mdchi Md2chi Mu Mdu Md2u) alpha
      (Q.restrict
        (parabolicCutoffSpatialJet2 chi dchi d2chi u du d2u)) := by
  let L₁ := ContinuousLinearMap.smulRightL Real (Euc n)
    (Euc n →L[Real] F)
  let L₂ := ContinuousLinearMap.precompR (Euc n)
    (ContinuousLinearMap.smulRightL Real (Euc n) F)
  let L₃ := ContinuousLinearMap.precompL (Euc n)
    (ContinuousLinearMap.smulRightL Real (Euc n) F)
  have hfirst : HolderWith (Mchi * Kd2u + Md2u * Kchi) alpha
      (fun p : Q ↦ chi p.1 • d2u p.1) :=
    holderWith_smul_of_norm_le hchi hd2u
      (fun p ↦ hchiNorm p.1 p.2) (fun p ↦ hd2uNorm p.1 p.2)
  have hsecond : HolderWith (Mdchi * Kdu + Mdu * Kdchi) alpha
      (fun p : Q ↦ L₁ (dchi p.1) (du p.1)) := by
    apply holderWith_bilinear_of_opNorm_le_one L₁
      ContinuousLinearMap.norm_smulRightL_le hdchi hdu
    · exact fun p ↦ hdchiNorm p.1 p.2
    · exact fun p ↦ hduNorm p.1 p.2
  have hthird : HolderWith (Mdchi * Kdu + Mdu * Kdchi) alpha
      (fun p : Q ↦ L₂ (dchi p.1) (du p.1)) := by
    apply holderWith_bilinear_of_opNorm_le_one L₂
      ((ContinuousLinearMap.norm_precompR_le (Euc n)
        (ContinuousLinearMap.smulRightL Real (Euc n) F)).trans
          ContinuousLinearMap.norm_smulRightL_le) hdchi hdu
    · exact fun p ↦ hdchiNorm p.1 p.2
    · exact fun p ↦ hduNorm p.1 p.2
  have hfourth : HolderWith (Md2chi * Ku + Mu * Kd2chi) alpha
      (fun p : Q ↦ L₃ (d2chi p.1) (u p.1.time p.1.space)) := by
    apply holderWith_bilinear_of_opNorm_le_one L₃
      ((ContinuousLinearMap.norm_precompL_le (Euc n)
        (ContinuousLinearMap.smulRightL Real (Euc n) F)).trans
          ContinuousLinearMap.norm_smulRightL_le) hd2chi hu
    · exact fun p ↦ hd2chiNorm p.1 p.2
    · exact fun p ↦ huNorm p.1 p.2
  have hall := hfirst.add hsecond |>.add hthird |>.add hfourth
  rw [show Q.restrict
      (parabolicCutoffSpatialJet2 chi dchi d2chi u du d2u) =
      fun p : Q ↦ chi p.1 • d2u p.1 + L₁ (dchi p.1) (du p.1) +
        L₂ (dchi p.1) (du p.1) +
          L₃ (d2chi p.1) (u p.1.time p.1.space) from by
    funext p
    rfl]
  simpa only [cutoffJet2HolderConst, parabolicCutoffSpatialJet2,
    Set.restrict_apply, Pi.add_apply, two_mul, add_assoc] using hall

theorem parabolicCutoffSpatialJet2_holderWith_restrict_of_eq_zero_outside
    {Q U : Set (ParabolicPoint (Euc n))}
    {alpha Kchi Kdchi Kd2chi Ku Kdu Kd2u
      Mchi Mdchi Md2chi Mu Mdu Md2u : NNReal}
    (chi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (d2u : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] F)
    (hchi : HolderWith Kchi alpha (Q.restrict chi))
    (hdchi : HolderWith Kdchi alpha (Q.restrict dchi))
    (hd2chi : HolderWith Kd2chi alpha (Q.restrict d2chi))
    (hu : HolderWith Ku alpha
      ((Q ∩ U).restrict (fun p ↦ u p.time p.space)))
    (hdu : HolderWith Kdu alpha ((Q ∩ U).restrict du))
    (hd2u : HolderWith Kd2u alpha ((Q ∩ U).restrict d2u))
    (hchiNorm : ∀ p, p ∈ Q → p ∈ U → ‖chi p‖ ≤ Mchi)
    (hdchiNorm : ∀ p, p ∈ Q → p ∈ U → ‖dchi p‖ ≤ Mdchi)
    (hd2chiNorm : ∀ p, p ∈ Q → p ∈ U → ‖d2chi p‖ ≤ Md2chi)
    (huNorm : ∀ p, p ∈ Q → p ∈ U → ‖u p.time p.space‖ ≤ Mu)
    (hduNorm : ∀ p, p ∈ Q → p ∈ U → ‖du p‖ ≤ Mdu)
    (hd2uNorm : ∀ p, p ∈ Q → p ∈ U → ‖d2u p‖ ≤ Md2u)
    (hchiZero : ∀ p, p ∈ Q → p ∉ U → chi p = 0)
    (hdchiZero : ∀ p, p ∈ Q → p ∉ U → dchi p = 0)
    (hd2chiZero : ∀ p, p ∈ Q → p ∉ U → d2chi p = 0) :
    HolderWith (cutoffJet2HolderConst
      Kchi Kdchi Kd2chi Ku Kdu Kd2u
      Mchi Mdchi Md2chi Mu Mdu Md2u) alpha
      (Q.restrict
        (parabolicCutoffSpatialJet2 chi dchi d2chi u du d2u)) := by
  let L₁ := ContinuousLinearMap.smulRightL Real (Euc n)
    (Euc n →L[Real] F)
  let L₂ := ContinuousLinearMap.precompR (Euc n)
    (ContinuousLinearMap.smulRightL Real (Euc n) F)
  let L₃ := ContinuousLinearMap.precompL (Euc n)
    (ContinuousLinearMap.smulRightL Real (Euc n) F)
  have hfirst : HolderWith (Mchi * Kd2u + Md2u * Kchi) alpha
      (Q.restrict (fun p ↦ chi p • d2u p)) :=
    holderWith_smul_of_eq_zero_outside chi d2u hchi hd2u
      hchiNorm hd2uNorm hchiZero
  have hsecond : HolderWith (Mdchi * Kdu + Mdu * Kdchi) alpha
      (Q.restrict (fun p ↦ L₁ (dchi p) (du p))) := by
    apply holderWith_bilinear_of_opNorm_le_one_of_eq_zero_outside
      L₁ ContinuousLinearMap.norm_smulRightL_le dchi du hdchi hdu
    · exact hdchiNorm
    · exact hduNorm
    · exact hdchiZero
  have hthird : HolderWith (Mdchi * Kdu + Mdu * Kdchi) alpha
      (Q.restrict (fun p ↦ L₂ (dchi p) (du p))) := by
    apply holderWith_bilinear_of_opNorm_le_one_of_eq_zero_outside
      L₂ ((ContinuousLinearMap.norm_precompR_le (Euc n)
        (ContinuousLinearMap.smulRightL Real (Euc n) F)).trans
          ContinuousLinearMap.norm_smulRightL_le) dchi du hdchi hdu
    · exact hdchiNorm
    · exact hduNorm
    · exact hdchiZero
  have hfourth : HolderWith (Md2chi * Ku + Mu * Kd2chi) alpha
      (Q.restrict (fun p ↦ L₃ (d2chi p) (u p.time p.space))) := by
    apply holderWith_bilinear_of_opNorm_le_one_of_eq_zero_outside
      L₃ ((ContinuousLinearMap.norm_precompL_le (Euc n)
        (ContinuousLinearMap.smulRightL Real (Euc n) F)).trans
          ContinuousLinearMap.norm_smulRightL_le) d2chi
        (fun p ↦ u p.time p.space) hd2chi hu
    · exact hd2chiNorm
    · exact huNorm
    · exact hd2chiZero
  have hall := hfirst.add hsecond |>.add hthird |>.add hfourth
  rw [show Q.restrict
      (parabolicCutoffSpatialJet2 chi dchi d2chi u du d2u) =
      fun p : Q ↦ chi p.1 • d2u p.1 + L₁ (dchi p.1) (du p.1) +
        L₂ (dchi p.1) (du p.1) +
          L₃ (d2chi p.1) (u p.1.time p.1.space) from by
    funext p
    rfl]
  simpa only [cutoffJet2HolderConst, parabolicCutoffSpatialJet2,
    Set.restrict_apply, Pi.add_apply, two_mul, add_assoc] using hall

theorem parabolicCutoffTimeDerivative_holderWith_restrict
    {Q : Set (ParabolicPoint (Euc n))}
    {alpha Kchi KdtimeChi Ku KdtimeU
      Mchi MdtimeChi Mu MdtimeU : NNReal}
    (chi dtimeChi : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (dtimeU : ParabolicPoint (Euc n) → F)
    (hchi : HolderWith Kchi alpha (Q.restrict chi))
    (hdtimeChi : HolderWith KdtimeChi alpha (Q.restrict dtimeChi))
    (hu : HolderWith Ku alpha
      (Q.restrict (fun p ↦ u p.time p.space)))
    (hdtimeU : HolderWith KdtimeU alpha (Q.restrict dtimeU))
    (hchiNorm : ∀ p, p ∈ Q → ‖chi p‖ ≤ Mchi)
    (hdtimeChiNorm : ∀ p, p ∈ Q → ‖dtimeChi p‖ ≤ MdtimeChi)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu)
    (hdtimeUNorm : ∀ p, p ∈ Q → ‖dtimeU p‖ ≤ MdtimeU) :
    HolderWith (parabolicCutoffTimeDerivativeHolderConst
      Kchi KdtimeChi Ku KdtimeU Mchi MdtimeChi Mu MdtimeU) alpha
      (Q.restrict
        (parabolicCutoffTimeDerivative chi dtimeChi u dtimeU)) := by
  have hfirst : HolderWith (Mchi * KdtimeU + MdtimeU * Kchi) alpha
      (fun p : Q ↦ chi p.1 • dtimeU p.1) :=
    holderWith_smul_of_norm_le hchi hdtimeU
      (fun p ↦ hchiNorm p.1 p.2) (fun p ↦ hdtimeUNorm p.1 p.2)
  have hsecond : HolderWith (MdtimeChi * Ku + Mu * KdtimeChi) alpha
      (fun p : Q ↦ dtimeChi p.1 • u p.1.time p.1.space) :=
    holderWith_smul_of_norm_le hdtimeChi hu
      (fun p ↦ hdtimeChiNorm p.1 p.2) (fun p ↦ huNorm p.1 p.2)
  have hsum := hfirst.add hsecond
  simpa only [parabolicCutoffTimeDerivativeHolderConst,
    parabolicCutoffTimeDerivative, Set.restrict_apply, add_assoc] using hsum

theorem parabolicCutoffTimeDerivative_holderWith_restrict_of_eq_zero_outside
    {Q U : Set (ParabolicPoint (Euc n))}
    {alpha Kchi KdtimeChi Ku KdtimeU
      Mchi MdtimeChi Mu MdtimeU : NNReal}
    (chi dtimeChi : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (dtimeU : ParabolicPoint (Euc n) → F)
    (hchi : HolderWith Kchi alpha (Q.restrict chi))
    (hdtimeChi : HolderWith KdtimeChi alpha (Q.restrict dtimeChi))
    (hu : HolderWith Ku alpha
      ((Q ∩ U).restrict (fun p ↦ u p.time p.space)))
    (hdtimeU : HolderWith KdtimeU alpha ((Q ∩ U).restrict dtimeU))
    (hchiNorm : ∀ p, p ∈ Q → p ∈ U → ‖chi p‖ ≤ Mchi)
    (hdtimeChiNorm : ∀ p, p ∈ Q → p ∈ U →
      ‖dtimeChi p‖ ≤ MdtimeChi)
    (huNorm : ∀ p, p ∈ Q → p ∈ U → ‖u p.time p.space‖ ≤ Mu)
    (hdtimeUNorm : ∀ p, p ∈ Q → p ∈ U →
      ‖dtimeU p‖ ≤ MdtimeU)
    (hchiZero : ∀ p, p ∈ Q → p ∉ U → chi p = 0)
    (hdtimeChiZero : ∀ p, p ∈ Q → p ∉ U → dtimeChi p = 0) :
    HolderWith (parabolicCutoffTimeDerivativeHolderConst
      Kchi KdtimeChi Ku KdtimeU Mchi MdtimeChi Mu MdtimeU) alpha
      (Q.restrict
        (parabolicCutoffTimeDerivative chi dtimeChi u dtimeU)) := by
  have hfirst : HolderWith (Mchi * KdtimeU + MdtimeU * Kchi) alpha
      (Q.restrict (fun p ↦ chi p • dtimeU p)) :=
    holderWith_smul_of_eq_zero_outside chi dtimeU hchi hdtimeU
      hchiNorm hdtimeUNorm hchiZero
  have hsecond : HolderWith (MdtimeChi * Ku + Mu * KdtimeChi) alpha
      (Q.restrict (fun p ↦ dtimeChi p • u p.time p.space)) :=
    holderWith_smul_of_eq_zero_outside dtimeChi
      (fun p ↦ u p.time p.space) hdtimeChi hu
        hdtimeChiNorm huNorm hdtimeChiZero
  have hsum := hfirst.add hsecond
  simpa only [parabolicCutoffTimeDerivativeHolderConst,
    parabolicCutoffTimeDerivative, Set.restrict_apply, add_assoc] using hsum

theorem eParabolicC2HolderGaugeOn_parabolicCutoffValue_le
    {Q : Set (ParabolicPoint (Euc n))}
    {alpha Kchi KdtimeChi Kdchi Kd2chi Ku KdtimeU Kdu Kd2u
      Mchi MdtimeChi Mdchi Md2chi Mu MdtimeU Mdu Md2u : NNReal}
    (chi dtimeChi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (dtimeU : ParabolicPoint (Euc n) → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (d2u : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] F)
    (hchiSpatial : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (fun y ↦ chi (parabolicPoint p.time y))
        (dchi (parabolicPoint p.time x)) x)
    (hdchiSpatial : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (fun y ↦ dchi (parabolicPoint p.time y))
        (d2chi (parabolicPoint p.time x)) x)
    (huSpatial : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (u p.time) (du (parabolicPoint p.time x)) x)
    (hduSpatial : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (fun y ↦ du (parabolicPoint p.time y))
        (d2u (parabolicPoint p.time x)) x)
    (hchiTime : ∀ p ∈ Q,
      HasDerivAt (fun t ↦ chi (parabolicPoint t p.space))
        (dtimeChi p) p.time)
    (huTime : ∀ p ∈ Q,
      HasDerivAt (fun t ↦ u t p.space) (dtimeU p) p.time)
    (hchi : HolderWith Kchi alpha (Q.restrict chi))
    (hdtimeChi : HolderWith KdtimeChi alpha (Q.restrict dtimeChi))
    (hdchi : HolderWith Kdchi alpha (Q.restrict dchi))
    (hd2chi : HolderWith Kd2chi alpha (Q.restrict d2chi))
    (hu : HolderWith Ku alpha
      (Q.restrict (fun p ↦ u p.time p.space)))
    (hdtimeU : HolderWith KdtimeU alpha (Q.restrict dtimeU))
    (hdu : HolderWith Kdu alpha (Q.restrict du))
    (hd2u : HolderWith Kd2u alpha (Q.restrict d2u))
    (hchiNorm : ∀ p, p ∈ Q → ‖chi p‖ ≤ Mchi)
    (hdtimeChiNorm : ∀ p, p ∈ Q → ‖dtimeChi p‖ ≤ MdtimeChi)
    (hdchiNorm : ∀ p, p ∈ Q → ‖dchi p‖ ≤ Mdchi)
    (hd2chiNorm : ∀ p, p ∈ Q → ‖d2chi p‖ ≤ Md2chi)
    (huNorm : ∀ p, p ∈ Q → ‖u p.time p.space‖ ≤ Mu)
    (hdtimeUNorm : ∀ p, p ∈ Q → ‖dtimeU p‖ ≤ MdtimeU)
    (hduNorm : ∀ p, p ∈ Q → ‖du p‖ ≤ Mdu)
    (hd2uNorm : ∀ p, p ∈ Q → ‖d2u p‖ ≤ Md2u) :
    eParabolicC2HolderGaugeOn alpha Q (parabolicCutoffValue chi u) ≤
      parabolicCutoffC2HolderGaugeConst
        Kchi KdtimeChi Kdchi Kd2chi Ku KdtimeU Kdu Kd2u
        Mchi MdtimeChi Mdchi Md2chi Mu MdtimeU Mdu Md2u := by
  let e := hessianCurryEquiv (Euc n) F
  let Cspatial : Nat → NNReal
    | 0 => Mchi * Mu
    | 1 => parabolicCutoffSpatialJet1SupConst Mchi Mdchi Mu Mdu
    | _ => cutoffJet2SupConst Mchi Mdchi Md2chi Mu Mdu Md2u
  have hspatial : ∀ j < 3, ∀ p ∈ Q,
      ‖parabolicSpatialJet j (parabolicCutoffValue chi u) p‖ ≤ Cspatial j := by
    intro j hj p hp
    interval_cases j
    · unfold parabolicSpatialJet
      rw [norm_iteratedFDeriv_zero, parabolicCutoffValue_apply, norm_smul]
      exact_mod_cast mul_le_mul (hchiNorm p hp) (huNorm p hp)
        (norm_nonneg _) Mchi.coe_nonneg
    · unfold parabolicSpatialJet
      rw [norm_iteratedFDeriv_one,
        (parabolicCutoffValue_hasFDerivAt chi dchi u du p.time p.space
          (hchiSpatial p hp p.space) (huSpatial p hp p.space)).fderiv]
      exact norm_parabolicCutoffSpatialJet1_le chi dchi u du
        Mchi Mdchi Mu Mdu p (hchiNorm p hp) (hdchiNorm p hp)
        (huNorm p hp) (hduNorm p hp)
    · rw [← e.norm_map]
      rw [show e (parabolicSpatialJet 2 (parabolicCutoffValue chi u) p) =
          parabolicCutoffSpatialJet2 chi dchi d2chi u du d2u p by
        simpa only [parabolicPoint_time_space] using
          hessianCurryEquiv_parabolicSpatialJet_two_cutoff
            chi dchi d2chi u du d2u p.time
            (hchiSpatial p hp) (hdchiSpatial p hp)
            (huSpatial p hp) (hduSpatial p hp) p.space]
      exact norm_parabolicCutoffSpatialJet2_le chi dchi d2chi u du d2u
        Mchi Mdchi Md2chi Mu Mdu Md2u p (hchiNorm p hp)
        (hdchiNorm p hp) (hd2chiNorm p hp) (huNorm p hp)
        (hduNorm p hp) (hd2uNorm p hp)
  have htimeNorm : ∀ p ∈ Q,
      ‖parabolicTimeDerivative (parabolicCutoffValue chi u) p‖ ≤
        parabolicCutoffTimeDerivativeSupConst
          Mchi MdtimeChi Mu MdtimeU := by
    intro p hp
    rw [parabolicTimeDerivative_cutoff chi dtimeChi u dtimeU p
      (hchiTime p hp) (huTime p hp)]
    exact norm_parabolicCutoffTimeDerivative_le chi dtimeChi u dtimeU
      Mchi MdtimeChi Mu MdtimeU p (hchiNorm p hp)
      (hdtimeChiNorm p hp) (huNorm p hp) (hdtimeUNorm p hp)
  have hjet2 := parabolicCutoffSpatialJet2_holderWith_restrict
    chi dchi d2chi u du d2u hchi hdchi hd2chi hu hdu hd2u
    hchiNorm hdchiNorm hd2chiNorm huNorm hduNorm hd2uNorm
  have hspatialHolder : HolderWith
      (cutoffJet2HolderConst Kchi Kdchi Kd2chi Ku Kdu Kd2u
        Mchi Mdchi Md2chi Mu Mdu Md2u) alpha
      (Q.restrict (parabolicSpatialJet 2 (parabolicCutoffValue chi u))) := by
    have hcomp := e.symm.lipschitz.holderWith.comp hjet2
    have hfun : e.symm ∘ Q.restrict
        (parabolicCutoffSpatialJet2 chi dchi d2chi u du d2u) =
        Q.restrict (parabolicSpatialJet 2 (parabolicCutoffValue chi u)) := by
      funext p
      change e.symm (parabolicCutoffSpatialJet2 chi dchi d2chi u du d2u p.1) =
        parabolicSpatialJet 2 (parabolicCutoffValue chi u) p.1
      rw [← e.symm_apply_apply
        (parabolicSpatialJet 2 (parabolicCutoffValue chi u) p.1)]
      congr 1
      simpa only [parabolicPoint_time_space] using
        (hessianCurryEquiv_parabolicSpatialJet_two_cutoff
          chi dchi d2chi u du d2u p.1.time
          (hchiSpatial p.1 p.2) (hdchiSpatial p.1 p.2)
          (huSpatial p.1 p.2) (hduSpatial p.1 p.2) p.1.space).symm
    rw [hfun] at hcomp
    simpa using hcomp
  have htimeJet := parabolicCutoffTimeDerivative_holderWith_restrict
    chi dtimeChi u dtimeU hchi hdtimeChi hu hdtimeU
    hchiNorm hdtimeChiNorm huNorm hdtimeUNorm
  have htimeHolder : HolderWith
      (parabolicCutoffTimeDerivativeHolderConst
        Kchi KdtimeChi Ku KdtimeU Mchi MdtimeChi Mu MdtimeU) alpha
      (Q.restrict (parabolicTimeDerivative (parabolicCutoffValue chi u))) := by
    have hfun : Q.restrict
        (parabolicCutoffTimeDerivative chi dtimeChi u dtimeU) =
        Q.restrict (parabolicTimeDerivative (parabolicCutoffValue chi u)) := by
      funext p
      exact (parabolicTimeDerivative_cutoff chi dtimeChi u dtimeU p.1
        (hchiTime p.1 p.2) (huTime p.1 p.2)).symm
    rw [← hfun]
    exact htimeJet
  have hgauge := eParabolicC2HolderGaugeOn_le Cspatial
    (parabolicCutoffTimeDerivativeSupConst Mchi MdtimeChi Mu MdtimeU)
    (cutoffJet2HolderConst Kchi Kdchi Kd2chi Ku Kdu Kd2u
      Mchi Mdchi Md2chi Mu Mdu Md2u)
    (parabolicCutoffTimeDerivativeHolderConst
      Kchi KdtimeChi Ku KdtimeU Mchi MdtimeChi Mu MdtimeU)
    hspatial htimeNorm hspatialHolder htimeHolder
  simpa only [parabolicCutoffC2HolderGaugeConst, Cspatial,
    Finset.sum_range_succ, Finset.sum_range_zero, ENNReal.coe_add,
    zero_add] using hgauge

theorem eParabolicC2HolderGaugeOn_parabolicCutoffValue_le_of_eq_zero_outside
    {Q U : Set (ParabolicPoint (Euc n))}
    {alpha Kchi KdtimeChi Kdchi Kd2chi Ku KdtimeU Kdu Kd2u
      Mchi MdtimeChi Mdchi Md2chi Mu MdtimeU Mdu Md2u : NNReal}
    (chi dtimeChi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (dtimeU : ParabolicPoint (Euc n) → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (d2u : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] F)
    (hchiSpatial : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (fun y ↦ chi (parabolicPoint p.time y))
        (dchi (parabolicPoint p.time x)) x)
    (hdchiSpatial : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (fun y ↦ dchi (parabolicPoint p.time y))
        (d2chi (parabolicPoint p.time x)) x)
    (huSpatial : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (u p.time) (du (parabolicPoint p.time x)) x)
    (hduSpatial : ∀ p ∈ Q, ∀ x,
      HasFDerivAt (fun y ↦ du (parabolicPoint p.time y))
        (d2u (parabolicPoint p.time x)) x)
    (hchiTime : ∀ p ∈ Q,
      HasDerivAt (fun t ↦ chi (parabolicPoint t p.space))
        (dtimeChi p) p.time)
    (huTime : ∀ p ∈ Q,
      HasDerivAt (fun t ↦ u t p.space) (dtimeU p) p.time)
    (hchi : HolderWith Kchi alpha (Q.restrict chi))
    (hdtimeChi : HolderWith KdtimeChi alpha (Q.restrict dtimeChi))
    (hdchi : HolderWith Kdchi alpha (Q.restrict dchi))
    (hd2chi : HolderWith Kd2chi alpha (Q.restrict d2chi))
    (hu : HolderWith Ku alpha
      ((Q ∩ U).restrict (fun p ↦ u p.time p.space)))
    (hdtimeU : HolderWith KdtimeU alpha ((Q ∩ U).restrict dtimeU))
    (hdu : HolderWith Kdu alpha ((Q ∩ U).restrict du))
    (hd2u : HolderWith Kd2u alpha ((Q ∩ U).restrict d2u))
    (hchiNorm : ∀ p, p ∈ Q → p ∈ U → ‖chi p‖ ≤ Mchi)
    (hdtimeChiNorm : ∀ p, p ∈ Q → p ∈ U →
      ‖dtimeChi p‖ ≤ MdtimeChi)
    (hdchiNorm : ∀ p, p ∈ Q → p ∈ U → ‖dchi p‖ ≤ Mdchi)
    (hd2chiNorm : ∀ p, p ∈ Q → p ∈ U → ‖d2chi p‖ ≤ Md2chi)
    (huNorm : ∀ p, p ∈ Q → p ∈ U → ‖u p.time p.space‖ ≤ Mu)
    (hdtimeUNorm : ∀ p, p ∈ Q → p ∈ U → ‖dtimeU p‖ ≤ MdtimeU)
    (hduNorm : ∀ p, p ∈ Q → p ∈ U → ‖du p‖ ≤ Mdu)
    (hd2uNorm : ∀ p, p ∈ Q → p ∈ U → ‖d2u p‖ ≤ Md2u)
    (hchiZero : ∀ p, p ∈ Q → p ∉ U → chi p = 0)
    (hdtimeChiZero : ∀ p, p ∈ Q → p ∉ U → dtimeChi p = 0)
    (hdchiZero : ∀ p, p ∈ Q → p ∉ U → dchi p = 0)
    (hd2chiZero : ∀ p, p ∈ Q → p ∉ U → d2chi p = 0) :
    eParabolicC2HolderGaugeOn alpha Q (parabolicCutoffValue chi u) ≤
      parabolicCutoffC2HolderGaugeConst
        Kchi KdtimeChi Kdchi Kd2chi Ku KdtimeU Kdu Kd2u
        Mchi MdtimeChi Mdchi Md2chi Mu MdtimeU Mdu Md2u := by
  let e := hessianCurryEquiv (Euc n) F
  let Cspatial : Nat → NNReal
    | 0 => Mchi * Mu
    | 1 => parabolicCutoffSpatialJet1SupConst Mchi Mdchi Mu Mdu
    | _ => cutoffJet2SupConst Mchi Mdchi Md2chi Mu Mdu Md2u
  have hspatial : ∀ j < 3, ∀ p ∈ Q,
      ‖parabolicSpatialJet j (parabolicCutoffValue chi u) p‖ ≤ Cspatial j := by
    intro j hj p hp
    interval_cases j
    · unfold parabolicSpatialJet
      rw [norm_iteratedFDeriv_zero, parabolicCutoffValue_apply,
        parabolicPoint_time_space p]
      by_cases hpU : p ∈ U
      · rw [norm_smul]
        exact_mod_cast mul_le_mul (hchiNorm p hp hpU) (huNorm p hp hpU)
          (norm_nonneg _) Mchi.coe_nonneg
      · rw [hchiZero p hp hpU, zero_smul, norm_zero]
        exact zero_le (Cspatial 0)
    · unfold parabolicSpatialJet
      rw [norm_iteratedFDeriv_one,
        (parabolicCutoffValue_hasFDerivAt chi dchi u du p.time p.space
          (hchiSpatial p hp p.space) (huSpatial p hp p.space)).fderiv,
        parabolicPoint_time_space p]
      by_cases hpU : p ∈ U
      · exact norm_parabolicCutoffSpatialJet1_le chi dchi u du
          Mchi Mdchi Mu Mdu p (hchiNorm p hp hpU) (hdchiNorm p hp hpU)
          (huNorm p hp hpU) (hduNorm p hp hpU)
      · unfold parabolicCutoffSpatialJet1
        rw [hchiZero p hp hpU, hdchiZero p hp hpU]
        simp only [zero_smul, ContinuousLinearMap.zero_smulRight,
          zero_add, norm_zero]
        exact zero_le (Cspatial 1)
    · rw [← e.norm_map]
      rw [show e (parabolicSpatialJet 2 (parabolicCutoffValue chi u) p) =
          parabolicCutoffSpatialJet2 chi dchi d2chi u du d2u p by
        simpa only [parabolicPoint_time_space] using
          hessianCurryEquiv_parabolicSpatialJet_two_cutoff
            chi dchi d2chi u du d2u p.time
            (hchiSpatial p hp) (hdchiSpatial p hp)
            (huSpatial p hp) (hduSpatial p hp) p.space]
      by_cases hpU : p ∈ U
      · exact norm_parabolicCutoffSpatialJet2_le chi dchi d2chi u du d2u
          Mchi Mdchi Md2chi Mu Mdu Md2u p (hchiNorm p hp hpU)
          (hdchiNorm p hp hpU) (hd2chiNorm p hp hpU)
          (huNorm p hp hpU) (hduNorm p hp hpU) (hd2uNorm p hp hpU)
      · unfold parabolicCutoffSpatialJet2
        rw [hchiZero p hp hpU, hdchiZero p hp hpU, hd2chiZero p hp hpU]
        simp only [zero_smul, map_zero, ContinuousLinearMap.zero_apply,
          zero_add, norm_zero]
        exact zero_le (Cspatial 2)
  have htimeNorm : ∀ p ∈ Q,
      ‖parabolicTimeDerivative (parabolicCutoffValue chi u) p‖ ≤
        parabolicCutoffTimeDerivativeSupConst
          Mchi MdtimeChi Mu MdtimeU := by
    intro p hp
    rw [parabolicTimeDerivative_cutoff chi dtimeChi u dtimeU p
      (hchiTime p hp) (huTime p hp)]
    by_cases hpU : p ∈ U
    · exact norm_parabolicCutoffTimeDerivative_le chi dtimeChi u dtimeU
        Mchi MdtimeChi Mu MdtimeU p (hchiNorm p hp hpU)
        (hdtimeChiNorm p hp hpU) (huNorm p hp hpU) (hdtimeUNorm p hp hpU)
    · unfold parabolicCutoffTimeDerivative
      rw [hchiZero p hp hpU, hdtimeChiZero p hp hpU]
      simp only [zero_smul, zero_add, norm_zero]
      positivity
  have hjet2 :=
    parabolicCutoffSpatialJet2_holderWith_restrict_of_eq_zero_outside
      chi dchi d2chi u du d2u hchi hdchi hd2chi hu hdu hd2u
      hchiNorm hdchiNorm hd2chiNorm huNorm hduNorm hd2uNorm
      hchiZero hdchiZero hd2chiZero
  have hspatialHolder : HolderWith
      (cutoffJet2HolderConst Kchi Kdchi Kd2chi Ku Kdu Kd2u
        Mchi Mdchi Md2chi Mu Mdu Md2u) alpha
      (Q.restrict (parabolicSpatialJet 2 (parabolicCutoffValue chi u))) := by
    have hcomp := e.symm.lipschitz.holderWith.comp hjet2
    have hfun : e.symm ∘ Q.restrict
        (parabolicCutoffSpatialJet2 chi dchi d2chi u du d2u) =
        Q.restrict (parabolicSpatialJet 2 (parabolicCutoffValue chi u)) := by
      funext p
      change e.symm (parabolicCutoffSpatialJet2 chi dchi d2chi u du d2u p.1) =
        parabolicSpatialJet 2 (parabolicCutoffValue chi u) p.1
      rw [← e.symm_apply_apply
        (parabolicSpatialJet 2 (parabolicCutoffValue chi u) p.1)]
      congr 1
      simpa only [parabolicPoint_time_space] using
        (hessianCurryEquiv_parabolicSpatialJet_two_cutoff
          chi dchi d2chi u du d2u p.1.time
          (hchiSpatial p.1 p.2) (hdchiSpatial p.1 p.2)
          (huSpatial p.1 p.2) (hduSpatial p.1 p.2) p.1.space).symm
    rw [hfun] at hcomp
    simpa using hcomp
  have htimeJet :=
    parabolicCutoffTimeDerivative_holderWith_restrict_of_eq_zero_outside
      chi dtimeChi u dtimeU hchi hdtimeChi hu hdtimeU
      hchiNorm hdtimeChiNorm huNorm hdtimeUNorm hchiZero hdtimeChiZero
  have htimeHolder : HolderWith
      (parabolicCutoffTimeDerivativeHolderConst
        Kchi KdtimeChi Ku KdtimeU Mchi MdtimeChi Mu MdtimeU) alpha
      (Q.restrict (parabolicTimeDerivative (parabolicCutoffValue chi u))) := by
    have hfun : Q.restrict
        (parabolicCutoffTimeDerivative chi dtimeChi u dtimeU) =
        Q.restrict (parabolicTimeDerivative (parabolicCutoffValue chi u)) := by
      funext p
      exact (parabolicTimeDerivative_cutoff chi dtimeChi u dtimeU p.1
        (hchiTime p.1 p.2) (huTime p.1 p.2)).symm
    rw [← hfun]
    exact htimeJet
  have hgauge := eParabolicC2HolderGaugeOn_le Cspatial
    (parabolicCutoffTimeDerivativeSupConst Mchi MdtimeChi Mu MdtimeU)
    (cutoffJet2HolderConst Kchi Kdchi Kd2chi Ku Kdu Kd2u
      Mchi Mdchi Md2chi Mu Mdu Md2u)
    (parabolicCutoffTimeDerivativeHolderConst
      Kchi KdtimeChi Ku KdtimeU Mchi MdtimeChi Mu MdtimeU)
    hspatial htimeNorm hspatialHolder htimeHolder
  simpa only [parabolicCutoffC2HolderGaugeConst, Cspatial,
    Finset.sum_range_succ, Finset.sum_range_zero, ENNReal.coe_add,
    zero_add] using hgauge

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
