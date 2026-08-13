import DifferentialGeometry.Analysis.Parabolic.Euclidean.LowerOrder
import DifferentialGeometry.Analysis.Schauder.VariableCoefficient

noncomputable section

open Real
open scoped BoundedContinuousFunction NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

open DifferentialGeometry.Analysis.Parabolic.Euclidean

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

def gradientComponentBcf
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (i : n) : BoundedContinuousFunction (Euc n) F :=
  (ContinuousLinearMap.apply Real F (EuclideanSpace.basisFun n Real i))
    |>.compLeftContinuousBounded (Euc n) du

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
@[simp]
theorem gradientComponentBcf_apply
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (i : n) (x : Euc n) :
    gradientComponentBcf du i x =
      du x (EuclideanSpace.basisFun n Real i) := rfl

def driftTerm
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F)) :
    BoundedContinuousFunction (Euc n) F :=
  ∑ i, b i • gradientComponentBcf du i

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
@[simp]
theorem driftTerm_apply
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (x : Euc n) :
    driftTerm b du x =
      ∑ i, b i x • du x (EuclideanSpace.basisFun n Real i) := by
  simp only [driftTerm, BoundedContinuousFunction.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

def potentialTerm
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F) :
    BoundedContinuousFunction (Euc n) F :=
  c • u

omit [Fintype n] [DecidableEq n] [Nonempty n] [CompleteSpace F] in
@[simp]
theorem potentialTerm_apply
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F) (x : Euc n) :
    potentialTerm c u x = c x • u x := rfl

def lowerOrderTerm
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F)) :
    BoundedContinuousFunction (Euc n) F :=
  driftTerm b du + potentialTerm c u

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
@[simp]
theorem lowerOrderTerm_apply
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (x : Euc n) :
    lowerOrderTerm b c u du x =
      ∑ i, b i x • du x (EuclideanSpace.basisFun n Real i) +
        c x • u x := by
  rw [lowerOrderTerm, BoundedContinuousFunction.add_apply,
    driftTerm_apply, potentialTerm_apply]

def nondivergenceOperator
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) :
    BoundedContinuousFunction (Euc n) F :=
  variableMatrixLap a d2u + lowerOrderTerm b c u du

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
@[simp]
theorem nondivergenceOperator_apply
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (x : Euc n) :
    nondivergenceOperator a b c u du d2u x =
      matrixLap (fun i j ↦ a i j x) (d2u x) +
        (∑ i, b i x • du x (EuclideanSpace.basisFun n Real i) +
          c x • u x) := by
  simp only [nondivergenceOperator, BoundedContinuousFunction.add_apply,
    variableMatrixLap_apply, lowerOrderTerm_apply]

def gradientComponentEval (i : n) :
    (Euc n →L[Real] F) →L[Real] F :=
  ContinuousLinearMap.apply Real F (EuclideanSpace.basisFun n Real i)

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
@[simp]
theorem gradientComponentEval_apply (i : n) (A : Euc n →L[Real] F) :
    gradientComponentEval i A = A (EuclideanSpace.basisFun n Real i) :=
  rfl

def contDiffHolderSpaceLowerOrderTerm
    (alpha : NNReal) (halpha : alpha ≤ 1)
    (b : n → BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (c : BoundedHolderSpace (X := Euc n) (F := Real) alpha) :
    ContDiffHolderSpace (V := Euc n) (F := F) 2 alpha →L[Real]
      BoundedHolderSpace (X := Euc n) (F := F) alpha :=
  (∑ i,
    (boundedHolderSpaceSmu alpha (b i)).comp
      ((boundedHolderSpaceMap alpha
        (gradientComponentEval (F := F) i)).comp
        (contDiffHolderSpaceFDerivHolder 2 alpha (by omega) halpha))) +
    (boundedHolderSpaceSmu alpha c).comp
      (contDiffHolderSpaceValueHolder 2 alpha (by omega) halpha)

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
@[simp]
theorem contDiffHolderSpaceLowerOrderTerm_apply
    (alpha : NNReal) (halpha : alpha ≤ 1)
    (b : n → BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (c : BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (u : ContDiffHolderSpace (V := Euc n) (F := F) 2 alpha)
    (x : Euc n) :
    contDiffHolderSpaceLowerOrderTerm alpha halpha b c u x =
      (∑ i, b i x •
        fderiv Real (contDiffHolderSpaceFun u) x
          (EuclideanSpace.basisFun n Real i)) + c x • u x := by
  simp only [contDiffHolderSpaceLowerOrderTerm,
    ContinuousLinearMap.add_apply, boundedHolderSpace_add_apply,
    ContinuousLinearMap.sum_apply, boundedHolderSpace_sum_apply,
    ContinuousLinearMap.comp_apply, boundedHolderSpaceSmu_apply,
    boundedHolderSpaceMap_apply, gradientComponentEval_apply,
    contDiffHolderSpaceFDerivHolder_apply,
    contDiffHolderSpaceValueHolder_apply]

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem norm_contDiffHolderSpaceLowerOrderTerm_le
    (alpha : NNReal) (halpha : alpha ≤ 1)
    (b : n → BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (c : BoundedHolderSpace (X := Euc n) (F := Real) alpha) :
    ‖contDiffHolderSpaceLowerOrderTerm
      (F := F) alpha halpha b c‖ ≤
      9 * (∑ i, ‖b i‖) + 9 * ‖c‖ := by
  classical
  have hsmu : ∀ a : BoundedHolderSpace (X := Euc n) (F := Real) alpha,
      ‖boundedHolderSpaceSmu (F := F) alpha a‖ ≤ 3 * ‖a‖ := by
    intro a
    calc
      ‖boundedHolderSpaceSmu (F := F) alpha a‖ ≤
          ‖boundedHolderSpaceSmu (X := Euc n)
            (F := F) alpha‖ * ‖a‖ :=
        (boundedHolderSpaceSmu (X := Euc n)
          (F := F) alpha).le_opNorm a
      _ ≤ 3 * ‖a‖ := mul_le_mul_of_nonneg_right
        (norm_boundedHolderSpaceSmu_le
          (X := Euc n) (F := F) alpha) (norm_nonneg _)
  have hdrift : ∀ i,
      ‖(boundedHolderSpaceSmu alpha (b i)).comp
        ((boundedHolderSpaceMap alpha
          (gradientComponentEval (F := F) i)).comp
          (contDiffHolderSpaceFDerivHolder 2 alpha (by omega) halpha))‖ ≤
        9 * ‖b i‖ := by
    intro i
    calc
      ‖(boundedHolderSpaceSmu alpha (b i)).comp
          ((boundedHolderSpaceMap alpha
            (gradientComponentEval (F := F) i)).comp
            (contDiffHolderSpaceFDerivHolder 2 alpha
              (by omega) halpha))‖ ≤
        ‖boundedHolderSpaceSmu alpha (b i)‖ *
          ‖(boundedHolderSpaceMap alpha
            (gradientComponentEval (F := F) i)).comp
            (contDiffHolderSpaceFDerivHolder 2 alpha
              (by omega) halpha)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (3 * ‖b i‖) * (1 * 3) := mul_le_mul (hsmu (b i))
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul
            ((norm_boundedHolderSpaceMap_le alpha
              (gradientComponentEval (F := F) i)).trans
                (norm_apply_euclideanBasis_le_one (G := F) i))
            (norm_contDiffHolderSpaceFDerivHolder_le
              (V := Euc n) (F := F) 2 alpha (by omega) halpha)
            (norm_nonneg _) zero_le_one))
        (norm_nonneg _)
        (mul_nonneg (by norm_num) (norm_nonneg (b i)))
      _ = 9 * ‖b i‖ := by ring
  have hpotential :
      ‖(boundedHolderSpaceSmu (F := F) alpha c).comp
        (contDiffHolderSpaceValueHolder 2 alpha
          (by omega) halpha)‖ ≤ 9 * ‖c‖ := by
    calc
      ‖(boundedHolderSpaceSmu (F := F) alpha c).comp
          (contDiffHolderSpaceValueHolder 2 alpha
            (by omega) halpha)‖ ≤
        ‖boundedHolderSpaceSmu (F := F) alpha c‖ *
          ‖contDiffHolderSpaceValueHolder
            (V := Euc n) (F := F) 2 alpha (by omega) halpha‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (3 * ‖c‖) * 3 := mul_le_mul (hsmu c)
        (norm_contDiffHolderSpaceValueHolder_le
          (V := Euc n) (F := F) 2 alpha (by omega) halpha)
        (norm_nonneg _)
        (mul_nonneg (by norm_num) (norm_nonneg c))
      _ = 9 * ‖c‖ := by ring
  unfold contDiffHolderSpaceLowerOrderTerm
  calc
    ‖(∑ i,
          (boundedHolderSpaceSmu alpha (b i)).comp
            ((boundedHolderSpaceMap alpha
              (gradientComponentEval (F := F) i)).comp
              (contDiffHolderSpaceFDerivHolder 2 alpha
                (by omega) halpha))) +
        (boundedHolderSpaceSmu (F := F) alpha c).comp
          (contDiffHolderSpaceValueHolder 2 alpha
            (by omega) halpha)‖ ≤
      ‖∑ i,
          (boundedHolderSpaceSmu alpha (b i)).comp
            ((boundedHolderSpaceMap alpha
              (gradientComponentEval (F := F) i)).comp
              (contDiffHolderSpaceFDerivHolder 2 alpha
                (by omega) halpha))‖ +
        ‖(boundedHolderSpaceSmu (F := F) alpha c).comp
          (contDiffHolderSpaceValueHolder 2 alpha
            (by omega) halpha)‖ := norm_add_le _ _
    _ ≤ (∑ i, 9 * ‖b i‖) + 9 * ‖c‖ := add_le_add
      ((norm_sum_le Finset.univ fun i ↦
        (boundedHolderSpaceSmu alpha (b i)).comp
          ((boundedHolderSpaceMap alpha
            (gradientComponentEval (F := F) i)).comp
            (contDiffHolderSpaceFDerivHolder 2 alpha
              (by omega) halpha))).trans
        (Finset.sum_le_sum fun i _hi ↦ hdrift i)) hpotential
    _ = 9 * (∑ i, ‖b i‖) + 9 * ‖c‖ := by
      rw [Finset.mul_sum]

def contDiffHolderSpaceNondivergenceOperator
    (alpha : NNReal) (halpha : alpha ≤ 1)
    (a : n → n → BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (b : n → BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (c : BoundedHolderSpace (X := Euc n) (F := Real) alpha) :
    ContDiffHolderSpace (V := Euc n) (F := F) 2 alpha →L[Real]
      BoundedHolderSpace (X := Euc n) (F := F) alpha :=
  contDiffHolderSpaceVariableMatrixLaplacian alpha a +
    contDiffHolderSpaceLowerOrderTerm alpha halpha b c

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
@[simp]
theorem contDiffHolderSpaceNondivergenceOperator_apply
    (alpha : NNReal) (halpha : alpha ≤ 1)
    (a : n → n → BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (b : n → BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (c : BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (u : ContDiffHolderSpace (V := Euc n) (F := F) 2 alpha)
    (x : Euc n) :
    contDiffHolderSpaceNondivergenceOperator alpha halpha a b c u x =
      matrixLap (fun i j ↦ a i j x)
          (hessianCurryEquiv (Euc n) F
            (iteratedFDeriv Real 2 (contDiffHolderSpaceFun u) x)) +
        ((∑ i, b i x •
          fderiv Real (contDiffHolderSpaceFun u) x
            (EuclideanSpace.basisFun n Real i)) + c x • u x) := by
  simp only [contDiffHolderSpaceNondivergenceOperator,
    ContinuousLinearMap.add_apply, boundedHolderSpace_add_apply,
    contDiffHolderSpaceVariableMatrixLaplacian_apply,
    contDiffHolderSpaceLowerOrderTerm_apply]

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem norm_contDiffHolderSpaceNondivergenceOperator_le
    (alpha : NNReal) (halpha : alpha ≤ 1)
    (a : n → n → BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (b : n → BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (c : BoundedHolderSpace (X := Euc n) (F := Real) alpha) :
    ‖contDiffHolderSpaceNondivergenceOperator
      (F := F) alpha halpha a b c‖ ≤
      3 * (∑ i, ∑ j, ‖a i j‖) +
        9 * (∑ i, ‖b i‖) + 9 * ‖c‖ := by
  calc
    ‖contDiffHolderSpaceNondivergenceOperator
        (F := F) alpha halpha a b c‖ ≤
      ‖contDiffHolderSpaceVariableMatrixLaplacian
        (F := F) alpha a‖ +
      ‖contDiffHolderSpaceLowerOrderTerm
        (F := F) alpha halpha b c‖ := norm_add_le _ _
    _ ≤ 3 * (∑ i, ∑ j, ‖a i j‖) +
        (9 * (∑ i, ‖b i‖) + 9 * ‖c‖) :=
      add_le_add
        (norm_contDiffHolderSpaceVariableMatrixLaplacian_le
          (F := F) alpha a)
        (norm_contDiffHolderSpaceLowerOrderTerm_le
          (F := F) alpha halpha b c)
    _ = 3 * (∑ i, ∑ j, ‖a i j‖) +
        9 * (∑ i, ‖b i‖) + 9 * ‖c‖ := by ring

def parabolicC2HolderSpaceLowerOrderTerm
    (alpha : NNReal) (halpha : alpha ≤ 1)
    (b : n → ParabolicHolderSpace (V := Euc n) (F := Real) alpha)
    (c : ParabolicHolderSpace (V := Euc n) (F := Real) alpha) :
    ParabolicC2HolderSpace (V := Euc n) (F := F) alpha →L[Real]
      ParabolicHolderSpace (V := Euc n) (F := F) alpha :=
  (∑ i,
    (boundedHolderSpaceSmu alpha (b i)).comp
      ((boundedHolderSpaceMap alpha
        (gradientComponentEval (F := F) i)).comp
        (parabolicC2HolderSpaceSpatialGradient alpha halpha))) +
    (boundedHolderSpaceSmu alpha c).comp
      (parabolicC2HolderSpaceValue alpha halpha)

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
@[simp]
theorem parabolicC2HolderSpaceLowerOrderTerm_apply
    (alpha : NNReal) (halpha : alpha ≤ 1)
    (b : n → ParabolicHolderSpace (V := Euc n) (F := Real) alpha)
    (c : ParabolicHolderSpace (V := Euc n) (F := Real) alpha)
    (u : ParabolicC2HolderSpace (V := Euc n) (F := F) alpha)
    (p : ParabolicPoint (Euc n)) :
    parabolicC2HolderSpaceLowerOrderTerm alpha halpha b c u p =
      parabolicLowerOrderTerm
        (fun i q ↦ b i q) (fun q ↦ c q)
        (parabolicC2HolderSpaceFun u) p := by
  simp only [parabolicC2HolderSpaceLowerOrderTerm,
    ContinuousLinearMap.add_apply, boundedHolderSpace_add_apply,
    ContinuousLinearMap.sum_apply, boundedHolderSpace_sum_apply,
    ContinuousLinearMap.comp_apply, boundedHolderSpaceSmu_apply,
    boundedHolderSpaceMap_apply, gradientComponentEval_apply,
    parabolicC2HolderSpaceSpatialGradient_apply,
    parabolicC2HolderSpaceValue_apply, parabolicLowerOrderTerm,
    parabolicDriftTerm, parabolicPotentialTerm, Pi.add_apply,
    parabolicGradientComponent]
  have hgradient :
      fderiv Real (parabolicC2HolderSpaceFun u p.time) p.space =
        continuousMultilinearCurryFin1 Real (Euc n) F
          (parabolicSpatialJet 1 (parabolicC2HolderSpaceFun u) p) := by
    apply ContinuousLinearMap.ext
    intro v
    rw [← parabolicPoint_time_space p]
    simp only [parabolicSpatialJet, parabolicPoint_time,
      parabolicPoint_space, continuousMultilinearCurryFin1_apply,
      iteratedFDeriv_one_apply, Fin.snoc_zero]
  rw [hgradient]

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem norm_parabolicC2HolderSpaceLowerOrderTerm_le
    (alpha : NNReal) (halpha : alpha ≤ 1)
    (b : n → ParabolicHolderSpace (V := Euc n) (F := Real) alpha)
    (c : ParabolicHolderSpace (V := Euc n) (F := Real) alpha) :
    ‖parabolicC2HolderSpaceLowerOrderTerm
      (F := F) alpha halpha b c‖ ≤
      18 * (∑ i, ‖b i‖) + 9 * ‖c‖ := by
  classical
  have hsmu : ∀ a : ParabolicHolderSpace (V := Euc n) (F := Real) alpha,
      ‖boundedHolderSpaceSmu (F := F) alpha a‖ ≤ 3 * ‖a‖ := by
    intro a
    calc
      ‖boundedHolderSpaceSmu (F := F) alpha a‖ ≤
          ‖boundedHolderSpaceSmu (X := ParabolicPoint (Euc n))
            (F := F) alpha‖ * ‖a‖ :=
        (boundedHolderSpaceSmu (X := ParabolicPoint (Euc n))
          (F := F) alpha).le_opNorm a
      _ ≤ 3 * ‖a‖ := mul_le_mul_of_nonneg_right
        (norm_boundedHolderSpaceSmu_le
          (X := ParabolicPoint (Euc n)) (F := F) alpha) (norm_nonneg _)
  have hdrift : ∀ i,
      ‖(boundedHolderSpaceSmu alpha (b i)).comp
        ((boundedHolderSpaceMap alpha
          (gradientComponentEval (F := F) i)).comp
          (parabolicC2HolderSpaceSpatialGradient alpha halpha))‖ ≤
        18 * ‖b i‖ := by
    intro i
    calc
      ‖(boundedHolderSpaceSmu alpha (b i)).comp
          ((boundedHolderSpaceMap alpha
            (gradientComponentEval (F := F) i)).comp
            (parabolicC2HolderSpaceSpatialGradient alpha halpha))‖ ≤
        ‖boundedHolderSpaceSmu alpha (b i)‖ *
          ‖(boundedHolderSpaceMap alpha
            (gradientComponentEval (F := F) i)).comp
            (parabolicC2HolderSpaceSpatialGradient alpha halpha)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (3 * ‖b i‖) * (1 * 6) := mul_le_mul (hsmu (b i))
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul
            ((norm_boundedHolderSpaceMap_le alpha
              (gradientComponentEval (F := F) i)).trans
                (norm_apply_euclideanBasis_le_one (G := F) i))
            (norm_parabolicC2HolderSpaceSpatialGradient_le
              (V := Euc n) (F := F) alpha halpha)
            (norm_nonneg _) zero_le_one))
        (norm_nonneg _)
        (mul_nonneg (by norm_num) (norm_nonneg (b i)))
      _ = 18 * ‖b i‖ := by ring
  have hpotential :
      ‖(boundedHolderSpaceSmu (F := F) alpha c).comp
        (parabolicC2HolderSpaceValue
          (V := Euc n) (F := F) alpha halpha)‖ ≤ 9 * ‖c‖ := by
    calc
      ‖(boundedHolderSpaceSmu (F := F) alpha c).comp
          (parabolicC2HolderSpaceValue
            (V := Euc n) (F := F) alpha halpha)‖ ≤
        ‖boundedHolderSpaceSmu (F := F) alpha c‖ *
          ‖parabolicC2HolderSpaceValue
            (V := Euc n) (F := F) alpha halpha‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (3 * ‖c‖) * 3 := mul_le_mul (hsmu c)
        (norm_parabolicC2HolderSpaceValue_le
          (V := Euc n) (F := F) alpha halpha)
        (norm_nonneg _)
        (mul_nonneg (by norm_num) (norm_nonneg c))
      _ = 9 * ‖c‖ := by ring
  unfold parabolicC2HolderSpaceLowerOrderTerm
  calc
    ‖(∑ i,
          (boundedHolderSpaceSmu alpha (b i)).comp
            ((boundedHolderSpaceMap alpha
              (gradientComponentEval (F := F) i)).comp
              (parabolicC2HolderSpaceSpatialGradient alpha halpha))) +
        (boundedHolderSpaceSmu (F := F) alpha c).comp
          (parabolicC2HolderSpaceValue
            (V := Euc n) (F := F) alpha halpha)‖ ≤
      ‖∑ i,
          (boundedHolderSpaceSmu alpha (b i)).comp
            ((boundedHolderSpaceMap alpha
              (gradientComponentEval (F := F) i)).comp
              (parabolicC2HolderSpaceSpatialGradient alpha halpha))‖ +
        ‖(boundedHolderSpaceSmu (F := F) alpha c).comp
          (parabolicC2HolderSpaceValue
            (V := Euc n) (F := F) alpha halpha)‖ := norm_add_le _ _
    _ ≤ (∑ i, 18 * ‖b i‖) + 9 * ‖c‖ := add_le_add
      ((norm_sum_le Finset.univ fun i ↦
        (boundedHolderSpaceSmu alpha (b i)).comp
          ((boundedHolderSpaceMap alpha
            (gradientComponentEval (F := F) i)).comp
            (parabolicC2HolderSpaceSpatialGradient alpha halpha))).trans
        (Finset.sum_le_sum fun i _hi ↦ hdrift i)) hpotential
    _ = 18 * (∑ i, ‖b i‖) + 9 * ‖c‖ := by
      rw [Finset.mul_sum]

def parabolicC2HolderSpaceNondivergenceOperator
    (alpha : NNReal) (halpha : alpha ≤ 1)
    (a : n → n → ParabolicHolderSpace (V := Euc n) (F := Real) alpha)
    (b : n → ParabolicHolderSpace (V := Euc n) (F := Real) alpha)
    (c : ParabolicHolderSpace (V := Euc n) (F := Real) alpha) :
    ParabolicC2HolderSpace (V := Euc n) (F := F) alpha →L[Real]
      ParabolicHolderSpace (V := Euc n) (F := F) alpha :=
  parabolicC2HolderSpaceVariableMatrixOperator alpha a -
    parabolicC2HolderSpaceLowerOrderTerm alpha halpha b c

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
@[simp]
theorem parabolicC2HolderSpaceNondivergenceOperator_apply
    (alpha : NNReal) (halpha : alpha ≤ 1)
    (a : n → n → ParabolicHolderSpace (V := Euc n) (F := Real) alpha)
    (b : n → ParabolicHolderSpace (V := Euc n) (F := Real) alpha)
    (c : ParabolicHolderSpace (V := Euc n) (F := Real) alpha)
    (u : ParabolicC2HolderSpace (V := Euc n) (F := F) alpha)
    (p : ParabolicPoint (Euc n)) :
    parabolicC2HolderSpaceNondivergenceOperator
        alpha halpha a b c u p =
      parabolicNondivergenceOperator
        (fun i j q ↦ a i j q) (fun i q ↦ b i q) (fun q ↦ c q)
        (parabolicC2HolderSpaceFun u) p := by
  simp only [parabolicC2HolderSpaceNondivergenceOperator,
    ContinuousLinearMap.sub_apply, boundedHolderSpace_sub_apply,
    parabolicC2HolderSpaceVariableMatrixOperator_apply,
    parabolicC2HolderSpaceLowerOrderTerm_apply,
    parabolicNondivergenceOperator, parabolicVariableMatrixOperator,
    parabolicVariableMatrixLap, Pi.sub_apply]

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem norm_parabolicC2HolderSpaceNondivergenceOperator_le
    (alpha : NNReal) (halpha : alpha ≤ 1)
    (a : n → n → ParabolicHolderSpace (V := Euc n) (F := Real) alpha)
    (b : n → ParabolicHolderSpace (V := Euc n) (F := Real) alpha)
    (c : ParabolicHolderSpace (V := Euc n) (F := Real) alpha) :
    ‖parabolicC2HolderSpaceNondivergenceOperator
      (F := F) alpha halpha a b c‖ ≤
      1 + 3 * (∑ i, ∑ j, ‖a i j‖) +
        18 * (∑ i, ‖b i‖) + 9 * ‖c‖ := by
  calc
    ‖parabolicC2HolderSpaceNondivergenceOperator
        (F := F) alpha halpha a b c‖ ≤
      ‖parabolicC2HolderSpaceVariableMatrixOperator
        (F := F) alpha a‖ +
      ‖parabolicC2HolderSpaceLowerOrderTerm
        (F := F) alpha halpha b c‖ := norm_sub_le _ _
    _ ≤ (1 + 3 * (∑ i, ∑ j, ‖a i j‖)) +
        (18 * (∑ i, ‖b i‖) + 9 * ‖c‖) :=
      add_le_add
        (norm_parabolicC2HolderSpaceVariableMatrixOperator_le
          (F := F) alpha a)
        (norm_parabolicC2HolderSpaceLowerOrderTerm_le
          (F := F) alpha halpha b c)
    _ = 1 + 3 * (∑ i, ∑ j, ‖a i j‖) +
        18 * (∑ i, ‖b i‖) + 9 * ‖c‖ := by ring

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem variableMatrixLap_eq_nondivergenceOperator_sub_lowerOrderTerm
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) :
    variableMatrixLap a d2u =
      nondivergenceOperator a b c u du d2u - lowerOrderTerm b c u du := by
  unfold nondivergenceOperator
  abel

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem norm_driftTerm_le
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (Bb : n → NNReal) (Mdu : NNReal)
    (hb : ∀ i x, ‖b i x‖ ≤ Bb i)
    (hdu : ∀ x, ‖du x‖ ≤ Mdu) :
    ‖driftTerm b du‖ ≤ ∑ i, (Bb i : Real) * Mdu := by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  intro x
  rw [driftTerm_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hb i x)
    ((du x).le_opNorm _ |>.trans (by
      rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i]
      simpa using hdu x)) (norm_nonneg _) (by positivity)

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem driftTerm_holderWith
    {alpha Kdu : NNReal}
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (Kb Bb : n → NNReal) (Mdu : NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha (b i : Euc n → Real))
    (hbNorm : ∀ i x, ‖b i x‖ ≤ Bb i)
    (hdu : HolderWith Kdu alpha
      (du : Euc n → Euc n →L[Real] F))
    (hduNorm : ∀ x, ‖du x‖ ≤ Mdu) :
    HolderWith (∑ i, (Bb i * Kdu + Mdu * Kb i)) alpha
      (driftTerm b du : Euc n → F) := by
  have hcomponent : ∀ i, HolderWith (Bb i * Kdu + Mdu * Kb i) alpha
      (fun x ↦ b i x • du x (EuclideanSpace.basisFun n Real i)) := by
    intro i
    have hdui : HolderWith Kdu alpha
        (fun x ↦ du x (EuclideanSpace.basisFun n Real i)) :=
      holderWith_comp_continuousLinearMap_of_norm_le_one
        (ContinuousLinearMap.apply Real F
          (EuclideanSpace.basisFun n Real i))
        (norm_apply_euclideanBasis_le_one i) hdu
    apply holderWith_smul_of_norm_le (hb i) hdui (hbNorm i)
    intro x
    exact (du x).le_opNorm _ |>.trans (by
      rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i]
      simpa using hduNorm x)
  have hsum := holderWith_finset_sum
    (Finset.univ : Finset n)
    (K := fun i ↦ Bb i * Kdu + Mdu * Kb i)
    (f := fun i x ↦ b i x • du x (EuclideanSpace.basisFun n Real i))
    (fun i hi ↦ hcomponent i)
  rw [show (driftTerm b du : Euc n → F) =
    fun x ↦ ∑ i, b i x • du x (EuclideanSpace.basisFun n Real i) from
      funext fun x ↦ driftTerm_apply b du x]
  simpa only [Finset.sum_filter, Finset.mem_univ, implies_true] using hsum

omit [Fintype n] [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem norm_potentialTerm_le
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (Bc Mu : NNReal)
    (hc : ∀ x, ‖c x‖ ≤ Bc) (hu : ∀ x, ‖u x‖ ≤ Mu) :
    ‖potentialTerm c u‖ ≤ (Bc : Real) * Mu := by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  intro x
  rw [potentialTerm_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hc x)
    (hu x) (norm_nonneg _) (by positivity)

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem potentialTerm_holderWith
    {alpha Kc Ku Bc Mu : NNReal}
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (hc : HolderWith Kc alpha (c : Euc n → Real))
    (hu : HolderWith Ku alpha (u : Euc n → F))
    (hcNorm : ∀ x, ‖c x‖ ≤ Bc) (huNorm : ∀ x, ‖u x‖ ≤ Mu) :
    HolderWith (Bc * Ku + Mu * Kc) alpha
      (potentialTerm c u : Euc n → F) := by
  simpa only [potentialTerm_apply] using
    holderWith_smul_of_norm_le hc hu hcNorm huNorm

def lowerOrderSupConst
    (Bb : n → NNReal) (Bc Mdu Mu : NNReal) : NNReal :=
  (∑ i, Bb i * Mdu) + Bc * Mu

def lowerOrderHolderConst
    (Kb Bb : n → NNReal) (Kc Kdu Ku Mdu Bc Mu : NNReal) : NNReal :=
  (∑ i, (Bb i * Kdu + Mdu * Kb i)) + (Bc * Ku + Mu * Kc)

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem norm_lowerOrderTerm_le
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (Bb : n → NNReal) (Bc Mdu Mu : NNReal)
    (hb : ∀ i x, ‖b i x‖ ≤ Bb i)
    (hc : ∀ x, ‖c x‖ ≤ Bc)
    (hdu : ∀ x, ‖du x‖ ≤ Mdu) (hu : ∀ x, ‖u x‖ ≤ Mu) :
    ‖lowerOrderTerm b c u du‖ ≤ lowerOrderSupConst Bb Bc Mdu Mu := by
  rw [lowerOrderTerm]
  refine (norm_add_le _ _).trans ?_
  have hb' := norm_driftTerm_le b du Bb Mdu hb hdu
  have hc' := norm_potentialTerm_le c u Bc Mu hc hu
  exact_mod_cast add_le_add hb' hc'

omit [DecidableEq n] [Nonempty n] [CompleteSpace F] in
theorem lowerOrderTerm_holderWith
    {alpha Kc Kdu Ku : NNReal}
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (Kb Bb : n → NNReal) (Mdu Bc Mu : NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha (b i : Euc n → Real))
    (hc : HolderWith Kc alpha (c : Euc n → Real))
    (hdu : HolderWith Kdu alpha
      (du : Euc n → Euc n →L[Real] F))
    (hu : HolderWith Ku alpha (u : Euc n → F))
    (hbNorm : ∀ i x, ‖b i x‖ ≤ Bb i)
    (hcNorm : ∀ x, ‖c x‖ ≤ Bc)
    (hduNorm : ∀ x, ‖du x‖ ≤ Mdu)
    (huNorm : ∀ x, ‖u x‖ ≤ Mu) :
    HolderWith (lowerOrderHolderConst Kb Bb Kc Kdu Ku Mdu Bc Mu) alpha
      (lowerOrderTerm b c u du : Euc n → F) := by
  exact (driftTerm_holderWith b du Kb Bb Mdu hb hbNorm hdu hduNorm).add
    (potentialTerm_holderWith c u hc hu hcNorm huNorm)

theorem variable_coefficient_schauder_estimate_of_lower_order_source
    {alpha KL Klo BL Blo M Kd2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hLBound : ‖nondivergenceOperator a b c u du d2u‖ ≤ BL)
    (hLHolder : HolderWith KL alpha
      (nondivergenceOperator a b c u du d2u))
    (hloBound : ‖lowerOrderTerm b c u du‖ ≤ Blo)
    (hloHolder : HolderWith Klo alpha (lowerOrderTerm b c u du))
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (a i j : Euc n → Real))
    (homega : ∀ i j x, ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm : ∀ x, ‖d2u x‖ ≤ M)
    (hd2uHolder : HolderWith Kd2u alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hsmall : spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j x0) hA alpha
        (∑ i, ∑ j, (omega i j + Ka i j))
        (∑ i, ∑ j, omega i j) < 1) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      ((spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA
        alpha (KL + Klo) (BL + Blo) u) /
        (1 - spdLaplacianSchauderDefectConst
          (fun i j ↦ a i j x0) hA alpha
            (∑ i, ∑ j, (omega i j + Ka i j))
            (∑ i, ∑ j, omega i j)) : NNReal) := by
  have hprincipalBound :
      ‖variableMatrixLap a d2u‖ ≤ ((BL + Blo : NNReal) : Real) := by
    rw [variableMatrixLap_eq_nondivergenceOperator_sub_lowerOrderTerm]
    exact (norm_sub_le _ _).trans (add_le_add hLBound hloBound)
  have hprincipalHolder : HolderWith (KL + Klo) alpha
      (variableMatrixLap a d2u) := by
    rw [variableMatrixLap_eq_nondivergenceOperator_sub_lowerOrderTerm]
    exact holderWith_sub hLHolder hloHolder
  exact variable_coefficient_schauder_estimate_of_small_oscillation
    (Kf := KL + Klo) (Bf := BL + Blo) (M := M) (Kd2u := Kd2u)
    halpha0 halpha1 a x0 hA u du d2u hu hdu
    hprincipalBound hprincipalHolder Ka omega ha homega
    hd2unorm hd2uHolder hsmall

theorem nondivergence_schauder_estimate_of_small_oscillation
    {alpha KL BL Kc Kdu Ku Mdu Bc Mu M Kd2u : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (b : n → BoundedContinuousFunction (Euc n) Real)
    (c : BoundedContinuousFunction (Euc n) Real)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (huDeriv : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hduDeriv : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hLBound : ‖nondivergenceOperator a b c u du d2u‖ ≤ BL)
    (hLHolder : HolderWith KL alpha
      (nondivergenceOperator a b c u du d2u))
    (Kb Bb : n → NNReal) (Ka omega : n → n → NNReal)
    (hb : ∀ i, HolderWith (Kb i) alpha (b i : Euc n → Real))
    (ha : ∀ i j, HolderWith (Ka i j) alpha (a i j : Euc n → Real))
    (hc : HolderWith Kc alpha (c : Euc n → Real))
    (hduHolder : HolderWith Kdu alpha
      (du : Euc n → Euc n →L[Real] F))
    (huHolder : HolderWith Ku alpha (u : Euc n → F))
    (hbNorm : ∀ i x, ‖b i x‖ ≤ Bb i)
    (hcNorm : ∀ x, ‖c x‖ ≤ Bc)
    (hduNorm : ∀ x, ‖du x‖ ≤ Mdu)
    (huNorm : ∀ x, ‖u x‖ ≤ Mu)
    (homega : ∀ i j x, ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm : ∀ x, ‖d2u x‖ ≤ M)
    (hd2uHolder : HolderWith Kd2u alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hsmall : spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j x0) hA alpha
        (∑ i, ∑ j, (omega i j + Ka i j))
        (∑ i, ∑ j, omega i j) < 1) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      ((spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA alpha
        (KL + lowerOrderHolderConst
          Kb Bb Kc Kdu Ku Mdu Bc Mu)
        (BL + lowerOrderSupConst Bb Bc Mdu Mu) u) /
        (1 - spdLaplacianSchauderDefectConst
          (fun i j ↦ a i j x0) hA alpha
            (∑ i, ∑ j, (omega i j + Ka i j))
            (∑ i, ∑ j, omega i j)) : NNReal) := by
  exact variable_coefficient_schauder_estimate_of_lower_order_source
    (Klo := lowerOrderHolderConst Kb Bb Kc Kdu Ku Mdu Bc Mu)
    (Blo := lowerOrderSupConst Bb Bc Mdu Mu)
    halpha0 halpha1 a x0 hA b c u du d2u huDeriv hduDeriv
    hLBound hLHolder
    (norm_lowerOrderTerm_le b c u du Bb Bc Mdu Mu
      hbNorm hcNorm hduNorm huNorm)
    (lowerOrderTerm_holderWith b c u du Kb Bb Mdu Bc Mu
      hb hc hduHolder huHolder hbNorm hcNorm hduNorm huNorm)
    Ka omega ha homega hd2unorm hd2uHolder hsmall

def nondivergenceSchauderNormConst
    (alpha : NNReal) (halpha : alpha ≤ 1)
    (a : n → n → BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (x0 : Euc n) (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (b : n → BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (c : BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (u : ContDiffHolderSpace (V := Euc n) (F := F) 2 alpha) : NNReal :=
  let Lu := contDiffHolderSpaceNondivergenceOperator
    alpha halpha a b c u
  let lo := contDiffHolderSpaceLowerOrderTerm alpha halpha b c u
  (spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA alpha
    (‖Lu‖₊ + ‖lo‖₊) (‖Lu‖₊ + ‖lo‖₊)
    (contDiffHolderSpaceToBoundedContinuousFunction 2 alpha u)) /
    (1 - variableCoefficientSchauderDefectConst alpha a x0 hA)

theorem nondivergence_schauder_norm_estimate_of_small_oscillation
    {alpha : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (x0 : Euc n) (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (b : n → BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (c : BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (u : ContDiffHolderSpace (V := Euc n) (F := F) 2 alpha)
    (hsmall : variableCoefficientSchauderDefectConst alpha a x0 hA < 1) :
    ‖u‖ ≤ nondivergenceSchauderNormConst
      alpha halpha1.le a x0 hA b c u := by
  let a0 : n → n → BoundedContinuousFunction (Euc n) Real :=
    fun i j ↦ boundedHolderSpaceToBoundedContinuousFunction
      alpha halpha0 (a i j)
  let b0 : n → BoundedContinuousFunction (Euc n) Real :=
    fun i ↦ boundedHolderSpaceToBoundedContinuousFunction
      alpha halpha0 (b i)
  let c0 := boundedHolderSpaceToBoundedContinuousFunction alpha halpha0 c
  let u0 := contDiffHolderSpaceToBoundedContinuousFunction 2 alpha u
  let du := contDiffHolderSpaceFDeriv 2 alpha (by omega) u
  let d2 := contDiffHolderSpaceHessianHolder alpha u
  let d2u := boundedHolderSpaceToBoundedContinuousFunction alpha halpha0 d2
  let Lu := contDiffHolderSpaceNondivergenceOperator
    alpha halpha1.le a b c u
  let L0 := boundedHolderSpaceToBoundedContinuousFunction alpha halpha0 Lu
  let lo := contDiffHolderSpaceLowerOrderTerm alpha halpha1.le b c u
  let lo0 := boundedHolderSpaceToBoundedContinuousFunction alpha halpha0 lo
  let Ka : n → n → NNReal :=
    fun i j ↦ boundedHolderSpaceHolderConst (a i j)
  let omega : n → n → NNReal :=
    fun i j ↦ boundedHolderSpaceOscillationAt (a i j) x0
  have hu : ∀ x : Euc n, HasFDerivAt (u0 : Euc n → F) (du x) x := by
    intro x
    simpa only [u0, du,
      contDiffHolderSpaceToBoundedContinuousFunction_apply] using
      contDiffHolderSpace_hasFDerivAt 2 alpha (by omega) u x
  have hdu : ∀ x : Euc n,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x := by
    intro x
    have hd2eq : d2u x =
        contDiffHolderSpaceHessian 2 alpha (by omega) u x := by
      simp only [d2u, d2,
        boundedHolderSpaceToBoundedContinuousFunction_apply,
        contDiffHolderSpaceHessianHolder_apply,
        contDiffHolderSpaceHessian_apply]
    rw [hd2eq]
    simpa only [du] using
      contDiffHolderSpaceFDeriv_hasFDerivAt 2 alpha (by omega) u x
  have hLsource : nondivergenceOperator a0 b0 c0 u0 du d2u = L0 := by
    apply BoundedContinuousFunction.ext
    intro x
    simp only [nondivergenceOperator_apply, a0, b0, c0, u0, du,
      d2u, d2, L0, Lu,
      boundedHolderSpaceToBoundedContinuousFunction_apply,
      contDiffHolderSpaceToBoundedContinuousFunction_apply,
      contDiffHolderSpaceFDeriv_apply,
      contDiffHolderSpaceHessianHolder_apply,
      contDiffHolderSpaceNondivergenceOperator_apply]
    rw [← hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv]
  have hlosource : lowerOrderTerm b0 c0 u0 du = lo0 := by
    apply BoundedContinuousFunction.ext
    intro x
    simp only [lowerOrderTerm_apply, b0, c0, u0, du, lo0, lo,
      boundedHolderSpaceToBoundedContinuousFunction_apply,
      contDiffHolderSpaceToBoundedContinuousFunction_apply,
      contDiffHolderSpaceFDeriv_apply,
      contDiffHolderSpaceLowerOrderTerm_apply]
  have hLBound : ‖nondivergenceOperator a0 b0 c0 u0 du d2u‖ ≤ ‖Lu‖₊ := by
    rw [hLsource, BoundedContinuousFunction.norm_le (by positivity)]
    intro x
    change ‖Lu x‖ ≤ (‖Lu‖₊ : Real)
    simpa using norm_boundedHolderSpace_apply_le Lu x
  have hLHolder : HolderWith ‖Lu‖₊ alpha
      (nondivergenceOperator a0 b0 c0 u0 du d2u) := by
    rw [hLsource]
    simpa only [boundedHolderSpaceToBoundedContinuousFunction_apply]
      using boundedHolderSpace_holderWith Lu
  have hloBound : ‖lowerOrderTerm b0 c0 u0 du‖ ≤ ‖lo‖₊ := by
    rw [hlosource, BoundedContinuousFunction.norm_le (by positivity)]
    intro x
    change ‖lo x‖ ≤ (‖lo‖₊ : Real)
    simpa using norm_boundedHolderSpace_apply_le lo x
  have hloHolder : HolderWith ‖lo‖₊ alpha
      (lowerOrderTerm b0 c0 u0 du) := by
    rw [hlosource]
    simpa only [boundedHolderSpaceToBoundedContinuousFunction_apply]
      using boundedHolderSpace_holderWith lo
  have ha : ∀ i j, HolderWith (Ka i j) alpha
      (a0 i j : Euc n → Real) := by
    intro i j
    simpa only [Ka, a0,
      boundedHolderSpaceToBoundedContinuousFunction_apply] using
      boundedHolderSpace_holderWith_holderConst (a i j)
  have homega : ∀ i j x, ‖a0 i j x0 - a0 i j x‖ ≤ omega i j := by
    intro i j x
    simp only [a0, boundedHolderSpaceToBoundedContinuousFunction_apply]
    exact norm_sub_le_boundedHolderSpaceOscillationAt (a i j) x0 x
  have hd2unorm : ∀ x, ‖d2u x‖ ≤ ‖d2‖₊ := by
    intro x
    simp only [d2u, boundedHolderSpaceToBoundedContinuousFunction_apply]
    simpa using norm_boundedHolderSpace_apply_le d2 x
  have hd2uHolder : HolderWith ‖d2‖₊ alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F) := by
    simpa only [d2u, boundedHolderSpaceToBoundedContinuousFunction_apply]
      using boundedHolderSpace_holderWith d2
  have hsmall' : spdLaplacianSchauderDefectConst
      (fun i j ↦ a0 i j x0) hA alpha
        (∑ i, ∑ j, (omega i j + Ka i j))
        (∑ i, ∑ j, omega i j) < 1 := by
    simpa only [a0, boundedHolderSpaceToBoundedContinuousFunction_apply,
      omega, Ka, variableCoefficientSchauderDefectConst] using hsmall
  have hgauge := variable_coefficient_schauder_estimate_of_lower_order_source
    halpha0 halpha1 a0 x0 hA b0 c0 u0 du d2u hu hdu
      hLBound hLHolder hloBound hloHolder Ka omega ha homega
      hd2unorm hd2uHolder hsmall'
  rw [norm_contDiffHolderSpace_eq]
  have hreal := ENNReal.toReal_mono ENNReal.coe_ne_top hgauge
  simpa only [u0, Lu, lo, a0,
    boundedHolderSpaceToBoundedContinuousFunction_apply,
    nondivergenceSchauderNormConst,
    variableCoefficientSchauderDefectConst, omega, Ka] using hreal

end DifferentialGeometry.Analysis.Schauder

end
