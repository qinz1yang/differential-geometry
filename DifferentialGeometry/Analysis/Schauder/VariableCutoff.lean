import DifferentialGeometry.Analysis.Schauder.LowerOrder

noncomputable section

open Real
open scoped BoundedContinuousFunction NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

open DifferentialGeometry.Analysis.Parabolic.Euclidean

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F]

def matrixCutoffCrossTerm
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (dchi : BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F)) :
    BoundedContinuousFunction (Euc n) F :=
  ∑ i, ∑ j,
    ((a i j * gradientComponentBcf dchi i) • gradientComponentBcf du j +
      (a i j * gradientComponentBcf dchi j) • gradientComponentBcf du i)

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem matrixCutoffCrossTerm_apply
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (dchi : BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (x : Euc n) :
    matrixCutoffCrossTerm a dchi du x =
      ∑ i, ∑ j,
        ((a i j x * dchi x (EuclideanSpace.basisFun n Real i)) •
            du x (EuclideanSpace.basisFun n Real j) +
          (a i j x * dchi x (EuclideanSpace.basisFun n Real j)) •
            du x (EuclideanSpace.basisFun n Real i)) := by
  simp only [matrixCutoffCrossTerm, BoundedContinuousFunction.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rfl

def matrixCutoffHessianTerm
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (d2chi : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (u : BoundedContinuousFunction (Euc n) F) :
    BoundedContinuousFunction (Euc n) F :=
  ∑ i, ∑ j,
    (a i j * hessianComponentBcf d2chi i j) • u

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem matrixCutoffHessianTerm_apply
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (d2chi : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (u : BoundedContinuousFunction (Euc n) F) (x : Euc n) :
    matrixCutoffHessianTerm a d2chi u x =
      ∑ i, ∑ j,
        (a i j x * d2chi x (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)) • u x := by
  simp only [matrixCutoffHessianTerm, BoundedContinuousFunction.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rfl

def matrixCutoffCommutator
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (dchi : BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (d2chi : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F)) :
    BoundedContinuousFunction (Euc n) F :=
  matrixCutoffCrossTerm a dchi du + matrixCutoffHessianTerm a d2chi u

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem matrixCutoffCommutator_apply
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (dchi : BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (d2chi : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (x : Euc n) :
    matrixCutoffCommutator a dchi d2chi u du x =
      ((∑ i, ∑ j,
        ((a i j x * dchi x (EuclideanSpace.basisFun n Real i)) •
            du x (EuclideanSpace.basisFun n Real j) +
          (a i j x * dchi x (EuclideanSpace.basisFun n Real j)) •
            du x (EuclideanSpace.basisFun n Real i))) +
      (∑ i, ∑ j,
        (a i j x * d2chi x (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)) • u x)) := by
  simp only [matrixCutoffCommutator, BoundedContinuousFunction.add_apply,
    matrixCutoffCrossTerm_apply, matrixCutoffHessianTerm_apply]

omit [DecidableEq n] [Nonempty n] in
theorem variableMatrixLap_cutoffJet2
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (chi : BoundedContinuousFunction (Euc n) Real)
    (dchi : BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (d2chi : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) :
    variableMatrixLap a (cutoffJet2 chi dchi d2chi u du d2u) =
      cutoffValue chi (variableMatrixLap a d2u) +
        matrixCutoffCommutator a dchi d2chi u du := by
  ext x
  simp only [variableMatrixLap_apply, matrixLap, cutoffJet2_apply,
    cutoffValue_apply, matrixCutoffCommutator_apply,
    BoundedContinuousFunction.add_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.precompR, ContinuousLinearMap.precompL,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.smulRightL_apply_apply]
  simp only [smul_add, Finset.sum_add_distrib]
  simp only [Finset.smul_sum, smul_smul]
  have hcomm : ∀ i j, a i j x * chi x = chi x * a i j x :=
    fun i j ↦ mul_comm _ _
  simp_rw [hcomm]
  abel

def matrixCutoffCommutatorSupConst
    (A : n → n → NNReal) (Mdchi Mdu Md2chi Mu : NNReal) : NNReal :=
  (∑ i, ∑ j, 2 * (A i j * Mdchi * Mdu)) +
    ∑ i, ∑ j, A i j * Md2chi * Mu

def matrixCutoffCommutatorHolderConst
    (A Ka : n → n → NNReal)
    (Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu : NNReal) : NNReal :=
  ∑ i, ∑ j,
    (2 * ((A i j * Mdchi) * Kdu +
      Mdu * (A i j * Kdchi + Mdchi * Ka i j)) +
    (A i j * Md2chi) * Ku +
      Mu * (A i j * Kd2chi + Md2chi * Ka i j))

omit [DecidableEq n] [Nonempty n] in
theorem norm_matrixCutoffCommutator_apply_le
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (dchi : BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (d2chi : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (A : n → n → NNReal) (Mdchi Mdu Md2chi Mu : NNReal) (x : Euc n)
    (haNorm : ∀ i j, ‖a i j x‖ ≤ A i j)
    (hdchiNorm : ‖dchi x‖ ≤ Mdchi)
    (hduNorm : ‖du x‖ ≤ Mdu)
    (hd2chiNorm : ‖d2chi x‖ ≤ Md2chi)
    (huNorm : ‖u x‖ ≤ Mu) :
    ‖matrixCutoffCommutator a dchi d2chi u du x‖ ≤
      matrixCutoffCommutatorSupConst A Mdchi Mdu Md2chi Mu := by
  rw [matrixCutoffCommutator_apply]
  refine (norm_add_le _ _).trans ?_
  rw [matrixCutoffCommutatorSupConst, NNReal.coe_add]
  push_cast
  refine add_le_add ?_ ?_
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj ↦ ?_)
    refine (norm_add_le _ _).trans ?_
    have hai : |a i j x| ≤ A i j := by
      simpa only [Real.norm_eq_abs] using haNorm i j
    have hdchii : |dchi x (EuclideanSpace.basisFun n Real i)| ≤ Mdchi := by
      rw [← Real.norm_eq_abs]
      exact (dchi x).le_opNorm _ |>.trans (by
        rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i]
        simpa using hdchiNorm)
    have hdchij : |dchi x (EuclideanSpace.basisFun n Real j)| ≤ Mdchi := by
      rw [← Real.norm_eq_abs]
      exact (dchi x).le_opNorm _ |>.trans (by
        rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j]
        simpa using hdchiNorm)
    have hdui : ‖du x (EuclideanSpace.basisFun n Real i)‖ ≤ Mdu :=
      (du x).le_opNorm _ |>.trans (by
        rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i]
        simpa using hduNorm)
    have hduj : ‖du x (EuclideanSpace.basisFun n Real j)‖ ≤ Mdu :=
      (du x).le_opNorm _ |>.trans (by
        rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j]
        simpa using hduNorm)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_mul]
    have hi :
        |a i j x| * |dchi x (EuclideanSpace.basisFun n Real i)| *
            ‖du x (EuclideanSpace.basisFun n Real j)‖ ≤
          (A i j * Mdchi * Mdu : NNReal) := by
      exact_mod_cast mul_le_mul
        (mul_le_mul hai hdchii (abs_nonneg _) (A i j).coe_nonneg)
        hduj (norm_nonneg _) (A i j * Mdchi).coe_nonneg
    have hj :
        |a i j x| * |dchi x (EuclideanSpace.basisFun n Real j)| *
            ‖du x (EuclideanSpace.basisFun n Real i)‖ ≤
          (A i j * Mdchi * Mdu : NNReal) := by
      exact_mod_cast mul_le_mul
        (mul_le_mul hai hdchij (abs_nonneg _) (A i j).coe_nonneg)
        hdui (norm_nonneg _) (A i j * Mdchi).coe_nonneg
    simpa only [two_mul] using add_le_add hi hj
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj ↦ ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    have hai : |a i j x| ≤ A i j := by
      simpa only [Real.norm_eq_abs] using haNorm i j
    have hd2chiij :
        |d2chi x (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)| ≤ Md2chi := by
      rw [← Real.norm_eq_abs]
      exact (norm_hessianComponentBcf_apply_le d2chi i j x).trans
        hd2chiNorm
    exact_mod_cast mul_le_mul
      (mul_le_mul hai hd2chiij (abs_nonneg _) (by positivity))
      huNorm (norm_nonneg _) (by positivity)

omit [DecidableEq n] [Nonempty n] in
theorem norm_matrixCutoffCommutator_le
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (dchi : BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (d2chi : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (A : n → n → NNReal) (Mdchi Mdu Md2chi Mu : NNReal)
    (haNorm : ∀ i j x, ‖a i j x‖ ≤ A i j)
    (hdchiNorm : ∀ x, ‖dchi x‖ ≤ Mdchi)
    (hduNorm : ∀ x, ‖du x‖ ≤ Mdu)
    (hd2chiNorm : ∀ x, ‖d2chi x‖ ≤ Md2chi)
    (huNorm : ∀ x, ‖u x‖ ≤ Mu) :
    ‖matrixCutoffCommutator a dchi d2chi u du‖ ≤
      matrixCutoffCommutatorSupConst A Mdchi Mdu Md2chi Mu := by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  intro x
  exact norm_matrixCutoffCommutator_apply_le a dchi d2chi u du
    A Mdchi Mdu Md2chi Mu x (fun i j ↦ haNorm i j x)
    (hdchiNorm x) (hduNorm x) (hd2chiNorm x) (huNorm x)

omit [DecidableEq n] [Nonempty n] in
theorem norm_matrixCutoffCommutator_le_of_support
    (s : Set (Euc n))
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (dchi : BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (d2chi : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (A : n → n → NNReal) (Mdchi Mdu Md2chi Mu : NNReal)
    (haNorm : ∀ i j x, x ∈ s → ‖a i j x‖ ≤ A i j)
    (hdchiNorm : ∀ x, ‖dchi x‖ ≤ Mdchi)
    (hduNorm : ∀ x, ‖du x‖ ≤ Mdu)
    (hd2chiNorm : ∀ x, ‖d2chi x‖ ≤ Md2chi)
    (huNorm : ∀ x, ‖u x‖ ≤ Mu)
    (hdchiSupport : ∀ x, x ∉ s → dchi x = 0)
    (hd2chiSupport : ∀ x, x ∉ s → d2chi x = 0) :
    ‖matrixCutoffCommutator a dchi d2chi u du‖ ≤
      matrixCutoffCommutatorSupConst A Mdchi Mdu Md2chi Mu := by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  intro x
  by_cases hx : x ∈ s
  · exact norm_matrixCutoffCommutator_apply_le a dchi d2chi u du
      A Mdchi Mdu Md2chi Mu x (fun i j ↦ haNorm i j x hx)
      (hdchiNorm x) (hduNorm x) (hd2chiNorm x) (huNorm x)
  · rw [matrixCutoffCommutator_apply, hdchiSupport x hx, hd2chiSupport x hx]
    simp only [ContinuousLinearMap.zero_apply, mul_zero, zero_smul,
      Finset.sum_const_zero, zero_add, norm_zero]
    exact (matrixCutoffCommutatorSupConst A Mdchi Mdu Md2chi Mu).coe_nonneg

omit [DecidableEq n] [Nonempty n] in
theorem matrixCutoffCommutator_holderWith_of_support
    {alpha Kdchi Kdu Kd2chi Ku : NNReal}
    (s : Set (Euc n))
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (dchi : BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (d2chi : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (A Ka : n → n → NNReal) (Mdchi Mdu Md2chi Mu : NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      (s.restrict (a i j : Euc n → Real)))
    (hdchi : HolderWith Kdchi alpha
      (dchi : Euc n → Euc n →L[Real] Real))
    (hdu : HolderWith Kdu alpha
      (du : Euc n → Euc n →L[Real] F))
    (hd2chi : HolderWith Kd2chi alpha
      (d2chi : Euc n → Euc n →L[Real] Euc n →L[Real] Real))
    (hu : HolderWith Ku alpha (u : Euc n → F))
    (haNorm : ∀ i j x, x ∈ s → ‖a i j x‖ ≤ A i j)
    (hdchiNorm : ∀ x, ‖dchi x‖ ≤ Mdchi)
    (hduNorm : ∀ x, ‖du x‖ ≤ Mdu)
    (hd2chiNorm : ∀ x, ‖d2chi x‖ ≤ Md2chi)
    (huNorm : ∀ x, ‖u x‖ ≤ Mu)
    (hdchiSupport : ∀ x, x ∉ s → dchi x = 0)
    (hd2chiSupport : ∀ x, x ∉ s → d2chi x = 0) :
    HolderWith (matrixCutoffCommutatorHolderConst A Ka
      Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu) alpha
      (matrixCutoffCommutator a dchi d2chi u du : Euc n → F) := by
  let Q : n → n → NNReal := fun i j ↦
    (A i j * Mdchi) * Kdu +
      Mdu * (A i j * Kdchi + Mdchi * Ka i j)
  let R : n → n → NNReal := fun i j ↦
    (A i j * Md2chi) * Ku +
      Mu * (A i j * Kd2chi + Md2chi * Ka i j)
  have hcomponent : ∀ i j, HolderWith (Q i j + Q i j + R i j) alpha
      (fun x ↦
        (a i j x * dchi x (EuclideanSpace.basisFun n Real i)) •
            du x (EuclideanSpace.basisFun n Real j) +
          (a i j x * dchi x (EuclideanSpace.basisFun n Real j)) •
            du x (EuclideanSpace.basisFun n Real i) +
          (a i j x * d2chi x (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) • u x) := by
    intro i j
    have hdchii : HolderWith Kdchi alpha
        (fun x ↦ dchi x (EuclideanSpace.basisFun n Real i)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real Real
          (EuclideanSpace.basisFun n Real i))
        (norm_apply_euclideanBasis_le_one i) hdchi
    have hdchij : HolderWith Kdchi alpha
        (fun x ↦ dchi x (EuclideanSpace.basisFun n Real j)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real Real
          (EuclideanSpace.basisFun n Real j))
        (norm_apply_euclideanBasis_le_one j) hdchi
    have hdui : HolderWith Kdu alpha
        (fun x ↦ du x (EuclideanSpace.basisFun n Real i)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real F
          (EuclideanSpace.basisFun n Real i))
        (norm_apply_euclideanBasis_le_one i) hdu
    have hduj : HolderWith Kdu alpha
        (fun x ↦ du x (EuclideanSpace.basisFun n Real j)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real F
          (EuclideanSpace.basisFun n Real j))
        (norm_apply_euclideanBasis_le_one j) hdu
    have hd2chiij : HolderWith Kd2chi alpha
        (fun x ↦ d2chi x (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)) := by
      simpa only [hessianComponentBcf_apply] using
        hessianComponentBcf_holderWith d2chi hd2chi i j
    have hadchii : HolderWith (A i j * Kdchi + Mdchi * Ka i j) alpha
        (fun x ↦ a i j x * dchi x (EuclideanSpace.basisFun n Real i)) := by
      simpa only [smul_eq_mul] using holderWith_smul_of_restrict_of_support
        (ha i j) hdchii (haNorm i j) (fun x ↦ by
          exact (dchi x).le_opNorm _ |>.trans (by
            rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i]
            simpa using hdchiNorm x)) (fun x hx ↦ by
          rw [hdchiSupport x hx]
          simp)
    have hadchij : HolderWith (A i j * Kdchi + Mdchi * Ka i j) alpha
        (fun x ↦ a i j x * dchi x (EuclideanSpace.basisFun n Real j)) := by
      simpa only [smul_eq_mul] using holderWith_smul_of_restrict_of_support
        (ha i j) hdchij (haNorm i j) (fun x ↦ by
          exact (dchi x).le_opNorm _ |>.trans (by
            rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j]
            simpa using hdchiNorm x)) (fun x hx ↦ by
          rw [hdchiSupport x hx]
          simp)
    have had2chi : HolderWith (A i j * Kd2chi + Md2chi * Ka i j) alpha
        (fun x ↦ a i j x * d2chi x (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)) := by
      simpa only [smul_eq_mul] using holderWith_smul_of_restrict_of_support
        (ha i j) hd2chiij (haNorm i j) (fun x ↦ by
          exact (norm_hessianComponentBcf_apply_le d2chi i j x).trans
            (hd2chiNorm x)) (fun x hx ↦ by
          rw [hd2chiSupport x hx]
          simp)
    have hadchiNorm : ∀ k x,
        ‖a i j x * dchi x (EuclideanSpace.basisFun n Real k)‖ ≤
          A i j * Mdchi := by
      intro k x
      by_cases hx : x ∈ s
      · rw [Real.norm_eq_abs, abs_mul]
        exact_mod_cast mul_le_mul (by
          simpa only [Real.norm_eq_abs] using haNorm i j x hx) (by
          rw [← Real.norm_eq_abs]
          exact (dchi x).le_opNorm _ |>.trans (by
            rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one k]
            simpa using hdchiNorm x)) (abs_nonneg _) (A i j).coe_nonneg
      · rw [hdchiSupport x hx]
        simp only [ContinuousLinearMap.zero_apply, mul_zero, norm_zero]
        exact (A i j * Mdchi).coe_nonneg
    have had2chiNorm : ∀ x,
        ‖a i j x * d2chi x (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)‖ ≤ A i j * Md2chi := by
      intro x
      by_cases hx : x ∈ s
      · rw [Real.norm_eq_abs, abs_mul]
        exact_mod_cast mul_le_mul (by
          simpa only [Real.norm_eq_abs] using haNorm i j x hx) (by
          rw [← Real.norm_eq_abs]
          exact (norm_hessianComponentBcf_apply_le d2chi i j x).trans
            (hd2chiNorm x)) (abs_nonneg _) (A i j).coe_nonneg
      · rw [hd2chiSupport x hx]
        simp only [ContinuousLinearMap.zero_apply, mul_zero, norm_zero]
        exact (A i j * Md2chi).coe_nonneg
    have hcrossi : HolderWith (Q i j) alpha
        (fun x ↦ (a i j x * dchi x (EuclideanSpace.basisFun n Real i)) •
          du x (EuclideanSpace.basisFun n Real j)) := by
      exact holderWith_smul_of_norm_le hadchii hduj
        (hadchiNorm i)
        (fun x ↦ (du x).le_opNorm _ |>.trans (by
          rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j]
          simpa using hduNorm x))
    have hcrossj : HolderWith (Q i j) alpha
        (fun x ↦ (a i j x * dchi x (EuclideanSpace.basisFun n Real j)) •
          du x (EuclideanSpace.basisFun n Real i)) := by
      exact holderWith_smul_of_norm_le hadchij hdui
        (hadchiNorm j)
        (fun x ↦ (du x).le_opNorm _ |>.trans (by
          rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i]
          simpa using hduNorm x))
    have hhessian : HolderWith (R i j) alpha
        (fun x ↦ (a i j x * d2chi x (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)) • u x) := by
      exact holderWith_smul_of_norm_le had2chi hu
        had2chiNorm huNorm
    exact hcrossi.add hcrossj |>.add hhessian
  have hinner : ∀ i, HolderWith (∑ j, (Q i j + Q i j + R i j)) alpha
      (fun x ↦ ∑ j,
        ((a i j x * dchi x (EuclideanSpace.basisFun n Real i)) •
            du x (EuclideanSpace.basisFun n Real j) +
          (a i j x * dchi x (EuclideanSpace.basisFun n Real j)) •
            du x (EuclideanSpace.basisFun n Real i) +
          (a i j x * d2chi x (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) • u x)) := by
    intro i
    simpa only [Finset.sum_filter, Finset.mem_univ, implies_true] using
      holderWith_finset_sum (Finset.univ : Finset n)
        (K := fun j ↦ Q i j + Q i j + R i j)
        (f := fun j x ↦
          (a i j x * dchi x (EuclideanSpace.basisFun n Real i)) •
              du x (EuclideanSpace.basisFun n Real j) +
            (a i j x * dchi x (EuclideanSpace.basisFun n Real j)) •
              du x (EuclideanSpace.basisFun n Real i) +
            (a i j x * d2chi x (EuclideanSpace.basisFun n Real i)
              (EuclideanSpace.basisFun n Real j)) • u x)
        (fun j hj ↦ hcomponent i j)
  have hall := holderWith_finset_sum (Finset.univ : Finset n)
    (K := fun i ↦ ∑ j, (Q i j + Q i j + R i j))
    (f := fun i x ↦ ∑ j,
      ((a i j x * dchi x (EuclideanSpace.basisFun n Real i)) •
          du x (EuclideanSpace.basisFun n Real j) +
        (a i j x * dchi x (EuclideanSpace.basisFun n Real j)) •
          du x (EuclideanSpace.basisFun n Real i) +
        (a i j x * d2chi x (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)) • u x))
    (fun i hi ↦ hinner i)
  rw [show (matrixCutoffCommutator a dchi d2chi u du : Euc n → F) =
      fun x ↦ ∑ i, ∑ j,
        ((a i j x * dchi x (EuclideanSpace.basisFun n Real i)) •
            du x (EuclideanSpace.basisFun n Real j) +
          (a i j x * dchi x (EuclideanSpace.basisFun n Real j)) •
            du x (EuclideanSpace.basisFun n Real i) +
          (a i j x * d2chi x (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) • u x) from by
      funext x
      rw [matrixCutoffCommutator_apply]
      simp only [Finset.sum_add_distrib]]
  simpa only [matrixCutoffCommutatorHolderConst, Q, R, two_mul, add_assoc] using hall

omit [DecidableEq n] [Nonempty n] in
theorem matrixCutoffCommutator_holderWith
    {alpha Kdchi Kdu Kd2chi Ku : NNReal}
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (dchi : BoundedContinuousFunction (Euc n) (Euc n →L[Real] Real))
    (d2chi : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] Real))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (A Ka : n → n → NNReal) (Mdchi Mdu Md2chi Mu : NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (a i j : Euc n → Real))
    (hdchi : HolderWith Kdchi alpha
      (dchi : Euc n → Euc n →L[Real] Real))
    (hdu : HolderWith Kdu alpha
      (du : Euc n → Euc n →L[Real] F))
    (hd2chi : HolderWith Kd2chi alpha
      (d2chi : Euc n → Euc n →L[Real] Euc n →L[Real] Real))
    (hu : HolderWith Ku alpha (u : Euc n → F))
    (haNorm : ∀ i j x, ‖a i j x‖ ≤ A i j)
    (hdchiNorm : ∀ x, ‖dchi x‖ ≤ Mdchi)
    (hduNorm : ∀ x, ‖du x‖ ≤ Mdu)
    (hd2chiNorm : ∀ x, ‖d2chi x‖ ≤ Md2chi)
    (huNorm : ∀ x, ‖u x‖ ≤ Mu) :
    HolderWith (matrixCutoffCommutatorHolderConst A Ka
      Kdchi Kdu Kd2chi Ku Mdchi Mdu Md2chi Mu) alpha
      (matrixCutoffCommutator a dchi d2chi u du : Euc n → F) := by
  apply matrixCutoffCommutator_holderWith_of_support Set.univ
    a dchi d2chi u du A Ka Mdchi Mdu Md2chi Mu
  · exact fun i j ↦ (ha i j).holderOnWith Set.univ |>.holderWith
  · exact hdchi
  · exact hdu
  · exact hd2chi
  · exact hu
  · exact fun i j x _ ↦ haNorm i j x
  · exact hdchiNorm
  · exact hduNorm
  · exact hd2chiNorm
  · exact huNorm
  · simp
  · simp

end DifferentialGeometry.Analysis.Schauder

end
