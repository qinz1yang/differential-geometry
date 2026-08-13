import DifferentialGeometry.Analysis.Schauder.CutoffValue
import DifferentialGeometry.Analysis.Schauder.CutoffJet
import DifferentialGeometry.Analysis.Schauder.VariableCutoff

noncomputable section

open Real Set
open scoped BoundedContinuousFunction NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def variableCutoffSourceSupConst
    (A : n → n → NNReal) (Mdchi Mdu Md2chi Mu : NNReal)
    (chi : BoundedContinuousFunction (Euc n) Real)
    (f : BoundedContinuousFunction (Euc n) F) : NNReal :=
  cutoffValueSupConst chi f +
    matrixCutoffCommutatorSupConst A Mdchi Mdu Md2chi Mu

def variableCutoffSourceHolderConst
    (A Ka : n → n → NNReal)
    (Kchi Kf Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu : NNReal)
    (chi : BoundedContinuousFunction (Euc n) Real)
    (f : BoundedContinuousFunction (Euc n) F) : NNReal :=
  cutoffValueHolderConst Kchi Kf chi f +
    matrixCutoffCommutatorHolderConst A Ka
      Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu

theorem variable_coefficient_interior_schauder_estimate_of_cutoffJet2_control_on
    {s U : Set (Euc n)} (hU : IsOpen U) (hsU : s ⊆ U)
    (coefficientSet : Set (Euc n))
    {alpha Kchi Kf Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu
      Kd2w Md2w : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (chi : BoundedContinuousFunction (Euc n) Real)
    (dchi : BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (d2chi : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (f u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hchiOne : ∀ x ∈ U, chi x = 1)
    (hchi : ∀ x, HasFDerivAt (chi : Euc n → Real) (dchi x) x)
    (hdchi : ∀ x,
      HasFDerivAt (dchi : Euc n → Euc n →L[Real] Real) (d2chi x) x)
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hsource : ∀ x, chi x ≠ 0 → variableMatrixLap a d2u x = f x)
    (A Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      (coefficientSet.restrict (a i j : Euc n → Real)))
    (homega : ∀ i j x, x ∈ coefficientSet →
      ‖a i j x0 - a i j x‖ ≤ omega i j)
    (haNorm : ∀ i j x, x ∈ coefficientSet → ‖a i j x‖ ≤ A i j)
    (hchiHolder : HolderWith Kchi alpha (chi : Euc n → Real))
    (hfHolder : HolderWith Kf alpha (f : Euc n → F))
    (hdchiHolder : HolderWith Kdchi alpha
      (dchi : Euc n → Euc n →L[Real] Real))
    (hduHolder : HolderWith Kdu alpha
      (du : Euc n → Euc n →L[Real] F))
    (hd2chiHolder : HolderWith Kd2chi alpha
      (d2chi : Euc n → Euc n →L[Real] Euc n →L[Real] Real))
    (huHolder : HolderWith Ku alpha (u : Euc n → F))
    (hdchiNorm : ∀ x, ‖dchi x‖ ≤ Mdchi)
    (hduNorm : ∀ x, ‖du x‖ ≤ Mdu)
    (hd2chiNorm : ∀ x, ‖d2chi x‖ ≤ Md2chi)
    (huNorm : ∀ x, ‖u x‖ ≤ Mu)
    (hchiSupport : ∀ x, x ∉ coefficientSet → chi x = 0)
    (hdchiSupport : ∀ x, x ∉ coefficientSet → dchi x = 0)
    (hd2chiSupport : ∀ x, x ∉ coefficientSet → d2chi x = 0)
    (hd2wNorm : ∀ x,
      ‖cutoffJet2 chi dchi d2chi u du d2u x‖ ≤ Md2w)
    (hd2wHolder : HolderWith Kd2w alpha
      (cutoffJet2 chi dchi d2chi u du d2u :
        Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hsmall : spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j x0) hA alpha
        (∑ i, ∑ j, (omega i j + Ka i j))
        (∑ i, ∑ j, omega i j) < 1) :
    eContDiffHolderGaugeOn 2 alpha s (u : Euc n → F) ≤
      ((spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA alpha
        (variableCutoffSourceHolderConst A Ka
          Kchi Kf Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu chi f)
        (variableCutoffSourceSupConst A Mdchi Mdu Md2chi Mu chi f)
        (cutoffValue chi u)) /
        (1 - spdLaplacianSchauderDefectConst
          (fun i j ↦ a i j x0) hA alpha
            (∑ i, ∑ j, (omega i j + Ka i j))
            (∑ i, ∑ j, omega i j)) : NNReal) := by
  let w := cutoffValue chi u
  let dw := cutoffJet1 chi dchi u du
  let d2w := cutoffJet2 chi dchi d2chi u du d2u
  have hd2wSupport : ∀ x, x ∉ coefficientSet → d2w x = 0 := by
    intro x hx
    exact cutoffJet2_eq_zero_of_cutoff_eq_zero chi dchi d2chi u du d2u x
      (hchiSupport x hx) (hdchiSupport x hx) (hd2chiSupport x hx)
  have hw : ∀ x, HasFDerivAt (w : Euc n → F) (dw x) x :=
    cutoffValue_hasFDerivAt chi dchi u du hchi hu
  have hdw : ∀ x,
      HasFDerivAt (dw : Euc n → Euc n →L[Real] F) (d2w x) x :=
    cutoffJet1_hasFDerivAt chi dchi d2chi u du d2u hchi hdchi hu hdu
  have hcutoffSource : cutoffValue chi (variableMatrixLap a d2u) =
      cutoffValue chi f := by
    ext x
    by_cases hx : chi x = 0
    · simp only [cutoffValue_apply, hx, zero_smul]
    · rw [cutoffValue_apply, cutoffValue_apply, hsource x hx]
  have hoperator : variableMatrixLap a d2w =
      cutoffValue chi f + matrixCutoffCommutator a dchi d2chi u du := by
    rw [show d2w = cutoffJet2 chi dchi d2chi u du d2u from rfl,
      variableMatrixLap_cutoffJet2, hcutoffSource]
  have hsourceBound : ‖variableMatrixLap a d2w‖ ≤
      variableCutoffSourceSupConst A Mdchi Mdu Md2chi Mu chi f := by
    rw [hoperator]
    refine (norm_add_le _ _).trans ?_
    exact add_le_add (norm_cutoffValue_le chi f)
      (norm_matrixCutoffCommutator_le_of_support coefficientSet a dchi d2chi u du
        A Mdchi Mdu Md2chi Mu haNorm hdchiNorm hduNorm hd2chiNorm huNorm
        hdchiSupport hd2chiSupport)
  have hsourceHolder : HolderWith
      (variableCutoffSourceHolderConst A Ka
        Kchi Kf Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu chi f)
      alpha (variableMatrixLap a d2w : Euc n → F) := by
    rw [hoperator]
    exact (cutoffValue_holderWith chi f hchiHolder hfHolder).add
      (matrixCutoffCommutator_holderWith_of_support coefficientSet
        a dchi d2chi u du
        A Ka Mdchi Mdu Md2chi Mu ha hdchiHolder hduHolder
        hd2chiHolder huHolder haNorm hdchiNorm hduNorm hd2chiNorm huNorm
        hdchiSupport hd2chiSupport)
  have hglobal := variable_coefficient_schauder_estimate_of_small_oscillation_on
    halpha0 halpha1 coefficientSet a x0 hA w dw d2w hw hdw
    hsourceBound hsourceHolder Ka omega ha homega hd2wNorm hd2wHolder
    hd2wSupport hsmall
  have heq : Set.EqOn (u : Euc n → F) (w : Euc n → F) U := by
    intro x hx
    rw [show w x = cutoffValue chi u x from rfl, cutoffValue_apply,
      hchiOne x hx, one_smul]
  rw [eContDiffHolderGaugeOn_congr_of_eqOn_open hU hsU heq 2 alpha]
  exact (eContDiffHolderGaugeOn_mono (Set.subset_univ s)
    2 alpha (w : Euc n → F)).trans hglobal

theorem variable_coefficient_interior_schauder_estimate_of_cutoffJet2_control
    {s U : Set (Euc n)} (hU : IsOpen U) (hsU : s ⊆ U)
    {alpha Kchi Kf Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu
      Kd2w Md2w : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (chi : BoundedContinuousFunction (Euc n) Real)
    (dchi : BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (d2chi : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (f u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hchiOne : ∀ x ∈ U, chi x = 1)
    (hchi : ∀ x, HasFDerivAt (chi : Euc n → Real) (dchi x) x)
    (hdchi : ∀ x,
      HasFDerivAt (dchi : Euc n → Euc n →L[Real] Real) (d2chi x) x)
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hsource : ∀ x, chi x ≠ 0 → variableMatrixLap a d2u x = f x)
    (A Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (a i j : Euc n → Real))
    (homega : ∀ i j x, ‖a i j x0 - a i j x‖ ≤ omega i j)
    (haNorm : ∀ i j x, ‖a i j x‖ ≤ A i j)
    (hchiHolder : HolderWith Kchi alpha (chi : Euc n → Real))
    (hfHolder : HolderWith Kf alpha (f : Euc n → F))
    (hdchiHolder : HolderWith Kdchi alpha
      (dchi : Euc n → Euc n →L[Real] Real))
    (hduHolder : HolderWith Kdu alpha
      (du : Euc n → Euc n →L[Real] F))
    (hd2chiHolder : HolderWith Kd2chi alpha
      (d2chi : Euc n → Euc n →L[Real] Euc n →L[Real] Real))
    (huHolder : HolderWith Ku alpha (u : Euc n → F))
    (hdchiNorm : ∀ x, ‖dchi x‖ ≤ Mdchi)
    (hduNorm : ∀ x, ‖du x‖ ≤ Mdu)
    (hd2chiNorm : ∀ x, ‖d2chi x‖ ≤ Md2chi)
    (huNorm : ∀ x, ‖u x‖ ≤ Mu)
    (hd2wNorm : ∀ x,
      ‖cutoffJet2 chi dchi d2chi u du d2u x‖ ≤ Md2w)
    (hd2wHolder : HolderWith Kd2w alpha
      (cutoffJet2 chi dchi d2chi u du d2u :
        Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hsmall : spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j x0) hA alpha
        (∑ i, ∑ j, (omega i j + Ka i j))
        (∑ i, ∑ j, omega i j) < 1) :
    eContDiffHolderGaugeOn 2 alpha s (u : Euc n → F) ≤
      ((spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA alpha
        (variableCutoffSourceHolderConst A Ka
          Kchi Kf Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu chi f)
        (variableCutoffSourceSupConst A Mdchi Mdu Md2chi Mu chi f)
        (cutoffValue chi u)) /
        (1 - spdLaplacianSchauderDefectConst
          (fun i j ↦ a i j x0) hA alpha
            (∑ i, ∑ j, (omega i j + Ka i j))
            (∑ i, ∑ j, omega i j)) : NNReal) := by
  apply variable_coefficient_interior_schauder_estimate_of_cutoffJet2_control_on
    hU hsU Set.univ halpha0 halpha1 a x0 hA chi dchi d2chi f u du d2u
    hchiOne hchi hdchi hu hdu hsource A Ka omega
  · exact fun i j ↦ (ha i j).holderOnWith Set.univ |>.holderWith
  · exact fun i j x _ ↦ homega i j x
  · exact fun i j x _ ↦ haNorm i j x
  · exact hchiHolder
  · exact hfHolder
  · exact hdchiHolder
  · exact hduHolder
  · exact hd2chiHolder
  · exact huHolder
  · exact hdchiNorm
  · exact hduNorm
  · exact hd2chiNorm
  · exact huNorm
  · simp
  · simp
  · simp
  · exact hd2wNorm
  · exact hd2wHolder
  · exact hsmall

theorem variable_coefficient_interior_schauder_estimate_of_cutoff
    {s U : Set (Euc n)} (hU : IsOpen U) (hsU : s ⊆ U)
    {alpha Kchi Kf Kdchi Kdu Kd2chi Ku Kd2u
      Mchi Mdchi Mdu Md2chi Mu Md2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (chi : BoundedContinuousFunction (Euc n) Real)
    (dchi : BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (d2chi : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (f u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hchiOne : ∀ x ∈ U, chi x = 1)
    (hchi : ∀ x, HasFDerivAt (chi : Euc n → Real) (dchi x) x)
    (hdchi : ∀ x,
      HasFDerivAt (dchi : Euc n → Euc n →L[Real] Real) (d2chi x) x)
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hsource : ∀ x, chi x ≠ 0 → variableMatrixLap a d2u x = f x)
    (A Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (a i j : Euc n → Real))
    (homega : ∀ i j x, ‖a i j x0 - a i j x‖ ≤ omega i j)
    (haNorm : ∀ i j x, ‖a i j x‖ ≤ A i j)
    (hchiHolder : HolderWith Kchi alpha (chi : Euc n → Real))
    (hfHolder : HolderWith Kf alpha (f : Euc n → F))
    (hdchiHolder : HolderWith Kdchi alpha
      (dchi : Euc n → Euc n →L[Real] Real))
    (hduHolder : HolderWith Kdu alpha
      (du : Euc n → Euc n →L[Real] F))
    (hd2chiHolder : HolderWith Kd2chi alpha
      (d2chi : Euc n → Euc n →L[Real] Euc n →L[Real] Real))
    (huHolder : HolderWith Ku alpha (u : Euc n → F))
    (hd2uHolder : HolderWith Kd2u alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hchiNorm : ∀ x, ‖chi x‖ ≤ Mchi)
    (hdchiNorm : ∀ x, ‖dchi x‖ ≤ Mdchi)
    (hduNorm : ∀ x, ‖du x‖ ≤ Mdu)
    (hd2chiNorm : ∀ x, ‖d2chi x‖ ≤ Md2chi)
    (huNorm : ∀ x, ‖u x‖ ≤ Mu)
    (hd2uNorm : ∀ x, ‖d2u x‖ ≤ Md2u)
    (hsmall : spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j x0) hA alpha
        (∑ i, ∑ j, (omega i j + Ka i j))
        (∑ i, ∑ j, omega i j) < 1) :
    eContDiffHolderGaugeOn 2 alpha s (u : Euc n → F) ≤
      ((spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA alpha
        (variableCutoffSourceHolderConst A Ka
          Kchi Kf Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu chi f)
        (variableCutoffSourceSupConst A Mdchi Mdu Md2chi Mu chi f)
        (cutoffValue chi u)) /
        (1 - spdLaplacianSchauderDefectConst
          (fun i j ↦ a i j x0) hA alpha
            (∑ i, ∑ j, (omega i j + Ka i j))
            (∑ i, ∑ j, omega i j)) : NNReal) := by
  apply variable_coefficient_interior_schauder_estimate_of_cutoffJet2_control
    (Kd2w := cutoffJet2HolderConst
      Kchi Kdchi Kd2chi Ku Kdu Kd2u
      Mchi Mdchi Md2chi Mu Mdu Md2u)
    (Md2w := cutoffJet2SupConst Mchi Mdchi Md2chi Mu Mdu Md2u)
    hU hsU halpha0 halpha1 a x0 hA chi dchi d2chi f u du d2u
    hchiOne hchi hdchi hu hdu hsource A Ka omega ha homega haNorm
    hchiHolder hfHolder hdchiHolder hduHolder hd2chiHolder huHolder
    hdchiNorm hduNorm hd2chiNorm huNorm
  · exact fun x ↦ norm_cutoffJet2_le chi dchi d2chi u du d2u
      Mchi Mdchi Md2chi Mu Mdu Md2u hchiNorm hdchiNorm hd2chiNorm
      huNorm hduNorm hd2uNorm x
  · exact cutoffJet2_holderWith chi dchi d2chi u du d2u
      hchiHolder hdchiHolder hd2chiHolder huHolder hduHolder hd2uHolder
      hchiNorm hdchiNorm hd2chiNorm huNorm hduNorm hd2uNorm
  · exact hsmall

end DifferentialGeometry.Analysis.Schauder

end
