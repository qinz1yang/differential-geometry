import DifferentialGeometry.Analysis.Parabolic.Euclidean.LowerOrder
import DifferentialGeometry.Analysis.Schauder.CutoffProduct

noncomputable section

open Matrix Real Set
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F]

def parabolicCutoffValue
    (chi : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) : Real → Euc n → F :=
  fun t x ↦ chi (parabolicPoint t x) • u t x

def parabolicCutoffSpatialJet1
    (chi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (p : ParabolicPoint (Euc n)) : Euc n →L[Real] F :=
  chi p • du p + (dchi p).smulRight (u p.time p.space)

def parabolicCutoffSpatialJet2
    (chi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (d2u : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] F)
    (p : ParabolicPoint (Euc n)) :
    Euc n →L[Real] Euc n →L[Real] F :=
  chi p • d2u p +
    (ContinuousLinearMap.smulRightL Real (Euc n)
      (Euc n →L[Real] F)) (dchi p) (du p) +
    (ContinuousLinearMap.precompR (Euc n)
      (ContinuousLinearMap.smulRightL Real (Euc n) F))
        (dchi p) (du p) +
    (ContinuousLinearMap.precompL (Euc n)
      (ContinuousLinearMap.smulRightL Real (Euc n) F))
        (d2chi p) (u p.time p.space)

def parabolicCutoffTimeDerivative
    (chi dtimeChi : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (dtimeU : ParabolicPoint (Euc n) → F)
    (p : ParabolicPoint (Euc n)) : F :=
  chi p • dtimeU p + dtimeChi p • u p.time p.space

def parabolicMatrixCutoffCommutator
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F) :
    ParabolicPoint (Euc n) → F :=
  fun p ↦ ∑ i, ∑ j,
    ((a i j p * dchi p (EuclideanSpace.basisFun n Real i)) •
        du p (EuclideanSpace.basisFun n Real j) +
      (a i j p * dchi p (EuclideanSpace.basisFun n Real j)) •
        du p (EuclideanSpace.basisFun n Real i) +
      (a i j p * d2chi p (EuclideanSpace.basisFun n Real i)
        (EuclideanSpace.basisFun n Real j)) • u p.time p.space)

def parabolicCutoffOperatorCommutator
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (dtimeChi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F) :
    ParabolicPoint (Euc n) → F :=
  fun p ↦ dtimeChi p • u p.time p.space -
    parabolicMatrixCutoffCommutator a dchi d2chi u du p

def parabolicDriftCutoffCommutator
    (b : n → ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (u : Real → Euc n → F) : ParabolicPoint (Euc n) → F :=
  fun p ↦ ∑ i,
    (b i p * dchi p (EuclideanSpace.basisFun n Real i)) •
      u p.time p.space

def parabolicNondivergenceCutoffCommutator
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (b : n → ParabolicPoint (Euc n) → Real)
    (dtimeChi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F) :
    ParabolicPoint (Euc n) → F :=
  parabolicCutoffOperatorCommutator a dtimeChi dchi d2chi u du -
    parabolicDriftCutoffCommutator b dchi u

omit [Fintype n] [DecidableEq n] [Nonempty n] in
@[simp]
theorem parabolicCutoffValue_apply
    (chi : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F) (t : Real) (x : Euc n) :
    parabolicCutoffValue chi u t x =
      chi (parabolicPoint t x) • u t x := rfl

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem parabolicCutoffSpatialJet1_apply
    (chi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (p : ParabolicPoint (Euc n)) :
    parabolicCutoffSpatialJet1 chi dchi u du p =
      chi p • du p + (dchi p).smulRight (u p.time p.space) := rfl

omit [DecidableEq n] [Nonempty n] in
theorem parabolicCutoffValue_hasFDerivAt
    (chi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (t : Real) (x : Euc n)
    (hchi : HasFDerivAt (fun y ↦ chi (parabolicPoint t y))
      (dchi (parabolicPoint t x)) x)
    (hu : HasFDerivAt (u t) (du (parabolicPoint t x)) x) :
    HasFDerivAt (parabolicCutoffValue chi u t)
      (parabolicCutoffSpatialJet1 chi dchi u du
        (parabolicPoint t x)) x := by
  simpa only [parabolicCutoffValue_apply,
    parabolicCutoffSpatialJet1_apply] using hchi.smul hu

omit [DecidableEq n] [Nonempty n] in
theorem parabolicCutoffSpatialJet1_hasFDerivAt
    (chi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (d2u : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] F)
    (t : Real) (x : Euc n)
    (hchi : HasFDerivAt (fun y ↦ chi (parabolicPoint t y))
      (dchi (parabolicPoint t x)) x)
    (hdchi : HasFDerivAt (fun y ↦ dchi (parabolicPoint t y))
      (d2chi (parabolicPoint t x)) x)
    (hu : HasFDerivAt (u t) (du (parabolicPoint t x)) x)
    (hdu : HasFDerivAt (fun y ↦ du (parabolicPoint t y))
      (d2u (parabolicPoint t x)) x) :
    HasFDerivAt
      (fun y ↦ parabolicCutoffSpatialJet1 chi dchi u du
        (parabolicPoint t y))
      (parabolicCutoffSpatialJet2 chi dchi d2chi u du d2u
        (parabolicPoint t x)) x := by
  have hleft := hchi.smul hdu
  have hright :=
    (ContinuousLinearMap.smulRightL Real (Euc n) F).hasFDerivAt_of_bilinear
      hdchi hu
  change HasFDerivAt
    (fun y ↦ chi (parabolicPoint t y) • du (parabolicPoint t y) +
      (dchi (parabolicPoint t y)).smulRight (u t y)) _ x
  simpa only [parabolicCutoffSpatialJet2, add_assoc] using
    hleft.add hright

omit [DecidableEq n] [Nonempty n] in
theorem hessianCurryEquiv_parabolicSpatialJet_two_cutoff
    (chi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (d2u : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] F)
    (t : Real)
    (hchi : ∀ x, HasFDerivAt (fun y ↦ chi (parabolicPoint t y))
      (dchi (parabolicPoint t x)) x)
    (hdchi : ∀ x, HasFDerivAt (fun y ↦ dchi (parabolicPoint t y))
      (d2chi (parabolicPoint t x)) x)
    (hu : ∀ x, HasFDerivAt (u t) (du (parabolicPoint t x)) x)
    (hdu : ∀ x, HasFDerivAt (fun y ↦ du (parabolicPoint t y))
      (d2u (parabolicPoint t x)) x)
    (x : Euc n) :
    hessianCurryEquiv (Euc n) F
        (parabolicSpatialJet 2 (parabolicCutoffValue chi u)
          (parabolicPoint t x)) =
      parabolicCutoffSpatialJet2 chi dchi d2chi u du d2u
        (parabolicPoint t x) := by
  exact hessianCurryEquiv_iteratedFDeriv_two
    (parabolicCutoffValue chi u t)
    (fun y ↦ parabolicCutoffSpatialJet1 chi dchi u du
      (parabolicPoint t y))
    (fun y ↦ parabolicCutoffSpatialJet2 chi dchi d2chi u du d2u
      (parabolicPoint t y))
    (fun y ↦ parabolicCutoffValue_hasFDerivAt
      chi dchi u du t y (hchi y) (hu y))
    (fun y ↦ parabolicCutoffSpatialJet1_hasFDerivAt
      chi dchi d2chi u du d2u t y
      (hchi y) (hdchi y) (hu y) (hdu y)) x

omit [DecidableEq n] [Nonempty n] in
theorem hessianCurryEquiv_parabolicSpatialJet_two_of_hasFDerivAt
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (d2u : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] F)
    (t : Real)
    (hu : ∀ x, HasFDerivAt (u t) (du (parabolicPoint t x)) x)
    (hdu : ∀ x, HasFDerivAt (fun y ↦ du (parabolicPoint t y))
      (d2u (parabolicPoint t x)) x)
    (x : Euc n) :
    hessianCurryEquiv (Euc n) F
        (parabolicSpatialJet 2 u (parabolicPoint t x)) =
      d2u (parabolicPoint t x) := by
  exact hessianCurryEquiv_iteratedFDeriv_two
    (u t) (fun y ↦ du (parabolicPoint t y))
      (fun y ↦ d2u (parabolicPoint t y)) hu hdu x

omit [Fintype n] [DecidableEq n] [Nonempty n] in
theorem parabolicTimeDerivative_cutoff
    (chi dtimeChi : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (dtimeU : ParabolicPoint (Euc n) → F)
    (p : ParabolicPoint (Euc n))
    (hchi : HasDerivAt (fun t ↦ chi (parabolicPoint t p.space))
      (dtimeChi p) p.time)
    (hu : HasDerivAt (fun t ↦ u t p.space) (dtimeU p) p.time) :
    parabolicTimeDerivative (parabolicCutoffValue chi u) p =
      parabolicCutoffTimeDerivative chi dtimeChi u dtimeU p := by
  have hprod : HasDerivAt
      (fun t ↦ parabolicCutoffValue chi u t p.space)
      (chi p • dtimeU p + dtimeChi p • u p.time p.space) p.time := by
    simpa only [parabolicCutoffValue_apply, Pi.smul_apply,
      parabolicPoint_time, parabolicPoint_space, parabolicPoint_time_space,
      add_comm] using hchi.smul hu
  unfold parabolicTimeDerivative parabolicCutoffTimeDerivative
  rw [hprod.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul]

omit [DecidableEq n] [Nonempty n] in
theorem matrixLap_parabolicCutoffSpatialJet2
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (chi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (d2u : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] F)
    (p : ParabolicPoint (Euc n)) :
    matrixLap (fun i j ↦ a i j p)
        (parabolicCutoffSpatialJet2 chi dchi d2chi u du d2u p) =
      chi p • matrixLap (fun i j ↦ a i j p) (d2u p) +
        parabolicMatrixCutoffCommutator a dchi d2chi u du p := by
  simp only [matrixLap, parabolicCutoffSpatialJet2,
    parabolicMatrixCutoffCommutator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.precompR, ContinuousLinearMap.precompL,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.smulRightL_apply_apply, smul_add,
    Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
  have hcomm : ∀ i j, a i j p * chi p = chi p * a i j p :=
    fun i j ↦ mul_comm _ _
  simp_rw [hcomm]
  abel

omit [DecidableEq n] [Nonempty n] in
theorem parabolicVariableMatrixOperator_cutoff
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (chi dtimeChi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (d2u : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] F)
    (dtimeU : ParabolicPoint (Euc n) → F)
    (p : ParabolicPoint (Euc n))
    (hchi : ∀ x, HasFDerivAt
      (fun y ↦ chi (parabolicPoint p.time y))
      (dchi (parabolicPoint p.time x)) x)
    (hdchi : ∀ x, HasFDerivAt
      (fun y ↦ dchi (parabolicPoint p.time y))
      (d2chi (parabolicPoint p.time x)) x)
    (hu : ∀ x, HasFDerivAt (u p.time)
      (du (parabolicPoint p.time x)) x)
    (hdu : ∀ x, HasFDerivAt
      (fun y ↦ du (parabolicPoint p.time y))
      (d2u (parabolicPoint p.time x)) x)
    (hchiTime : HasDerivAt (fun t ↦ chi (parabolicPoint t p.space))
      (dtimeChi p) p.time)
    (huTime : HasDerivAt (fun t ↦ u t p.space) (dtimeU p) p.time) :
    parabolicVariableMatrixOperator a (parabolicCutoffValue chi u) p =
      chi p • parabolicVariableMatrixOperator a u p +
        parabolicCutoffOperatorCommutator
          a dtimeChi dchi d2chi u du p := by
  have hcutHessian :
      hessianCurryEquiv (Euc n) F
          (parabolicSpatialJet 2 (parabolicCutoffValue chi u) p) =
        parabolicCutoffSpatialJet2 chi dchi d2chi u du d2u p := by
    simpa only [parabolicPoint_time_space] using
      hessianCurryEquiv_parabolicSpatialJet_two_cutoff
        chi dchi d2chi u du d2u p.time hchi hdchi hu hdu p.space
  have huHessian :
      hessianCurryEquiv (Euc n) F (parabolicSpatialJet 2 u p) = d2u p := by
    simpa only [parabolicPoint_time_space] using
      hessianCurryEquiv_parabolicSpatialJet_two_of_hasFDerivAt
        u du d2u p.time hu hdu p.space
  have huTimeEq : parabolicTimeDerivative u p = dtimeU p := by
    unfold parabolicTimeDerivative
    rw [huTime.hasFDerivAt.fderiv]
    simp only [ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  unfold parabolicVariableMatrixOperator parabolicVariableMatrixLap
  rw [parabolicTimeDerivative_cutoff chi dtimeChi u dtimeU p
      hchiTime huTime,
    hcutHessian, matrixLap_parabolicCutoffSpatialJet2, huHessian,
    huTimeEq]
  unfold parabolicCutoffTimeDerivative parabolicCutoffOperatorCommutator
  module

omit [DecidableEq n] [Nonempty n] in
theorem parabolicGradientComponent_cutoff
    (chi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (i : n) (p : ParabolicPoint (Euc n))
    (hchi : HasFDerivAt
      (fun y ↦ chi (parabolicPoint p.time y)) (dchi p) p.space)
    (hu : HasFDerivAt (u p.time) (du p) p.space) :
    parabolicGradientComponent (parabolicCutoffValue chi u) i p =
      chi p • parabolicGradientComponent u i p +
        dchi p (EuclideanSpace.basisFun n Real i) •
          u p.time p.space := by
  have hcut : HasFDerivAt
      (parabolicCutoffValue chi u p.time)
      (parabolicCutoffSpatialJet1 chi dchi u du p) p.space := by
    simpa only [parabolicPoint_time_space] using
      parabolicCutoffValue_hasFDerivAt chi dchi u du p.time p.space
        hchi hu
  simp only [parabolicGradientComponent_apply, parabolicSpatialJet,
    continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply,
    hcut.fderiv, hu.fderiv, parabolicCutoffSpatialJet1_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, Fin.snoc_zero]

omit [DecidableEq n] [Nonempty n] in
theorem parabolicDriftTerm_cutoff
    (b : n → ParabolicPoint (Euc n) → Real)
    (chi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (p : ParabolicPoint (Euc n))
    (hchi : HasFDerivAt
      (fun y ↦ chi (parabolicPoint p.time y)) (dchi p) p.space)
    (hu : HasFDerivAt (u p.time) (du p) p.space) :
    parabolicDriftTerm b (parabolicCutoffValue chi u) p =
      chi p • parabolicDriftTerm b u p +
        parabolicDriftCutoffCommutator b dchi u p := by
  unfold parabolicDriftTerm parabolicDriftCutoffCommutator
  simp_rw [parabolicGradientComponent_cutoff chi dchi u du _ p hchi hu]
  simp only [smul_add, smul_smul, Finset.sum_add_distrib,
    Finset.smul_sum]
  have hcomm : ∀ i, b i p * chi p = chi p * b i p :=
    fun i ↦ mul_comm _ _
  simp_rw [hcomm]

omit [Fintype n] [DecidableEq n] [Nonempty n] in
theorem parabolicPotentialTerm_cutoff
    (c : ParabolicPoint (Euc n) → Real)
    (chi : ParabolicPoint (Euc n) → Real)
    (u : Real → Euc n → F)
    (p : ParabolicPoint (Euc n)) :
    parabolicPotentialTerm c (parabolicCutoffValue chi u) p =
      chi p • parabolicPotentialTerm c u p := by
  unfold parabolicPotentialTerm parabolicCutoffValue
  rw [parabolicPoint_time_space]
  rw [smul_smul, smul_smul, mul_comm (c p) (chi p)]

omit [DecidableEq n] [Nonempty n] in
theorem parabolicNondivergenceOperator_cutoff
    (a : n → n → ParabolicPoint (Euc n) → Real)
    (b : n → ParabolicPoint (Euc n) → Real)
    (c chi dtimeChi : ParabolicPoint (Euc n) → Real)
    (dchi : ParabolicPoint (Euc n) → Euc n →L[Real] Real)
    (d2chi : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] Real)
    (u : Real → Euc n → F)
    (du : ParabolicPoint (Euc n) → Euc n →L[Real] F)
    (d2u : ParabolicPoint (Euc n) →
      Euc n →L[Real] Euc n →L[Real] F)
    (dtimeU : ParabolicPoint (Euc n) → F)
    (p : ParabolicPoint (Euc n))
    (hchi : ∀ x, HasFDerivAt
      (fun y ↦ chi (parabolicPoint p.time y))
      (dchi (parabolicPoint p.time x)) x)
    (hdchi : ∀ x, HasFDerivAt
      (fun y ↦ dchi (parabolicPoint p.time y))
      (d2chi (parabolicPoint p.time x)) x)
    (hu : ∀ x, HasFDerivAt (u p.time)
      (du (parabolicPoint p.time x)) x)
    (hdu : ∀ x, HasFDerivAt
      (fun y ↦ du (parabolicPoint p.time y))
      (d2u (parabolicPoint p.time x)) x)
    (hchiTime : HasDerivAt (fun t ↦ chi (parabolicPoint t p.space))
      (dtimeChi p) p.time)
    (huTime : HasDerivAt (fun t ↦ u t p.space) (dtimeU p) p.time) :
    parabolicNondivergenceOperator a b c
        (parabolicCutoffValue chi u) p =
      chi p • parabolicNondivergenceOperator a b c u p +
        parabolicNondivergenceCutoffCommutator
          a b dtimeChi dchi d2chi u du p := by
  have hchiAt : HasFDerivAt
      (fun y ↦ chi (parabolicPoint p.time y)) (dchi p) p.space := by
    simpa only [parabolicPoint_time_space] using hchi p.space
  have huAt : HasFDerivAt (u p.time) (du p) p.space := by
    simpa only [parabolicPoint_time_space] using hu p.space
  unfold parabolicNondivergenceOperator
  rw [Pi.sub_apply,
    parabolicVariableMatrixOperator_cutoff a chi dtimeChi dchi d2chi
      u du d2u dtimeU p hchi hdchi hu hdu hchiTime huTime]
  unfold parabolicLowerOrderTerm
  rw [Pi.add_apply, parabolicDriftTerm_cutoff b chi dchi u du p
      hchiAt huAt,
    parabolicPotentialTerm_cutoff c chi u p]
  unfold parabolicNondivergenceCutoffCommutator
  simp only [Pi.add_apply, Pi.sub_apply, smul_add, smul_sub]
  module

end DifferentialGeometry.Analysis.Parabolic.Euclidean

end
