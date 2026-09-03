import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.ConnectionDifference.OrderZero.KernelJetGrid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricLoweredConnectionDifferenceCoefficient
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Pairing.TopOrder.Algebra
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.OperatorFieldComposition
import DifferentialGeometry.Geometry.Metric.InnerExpansion
open DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section


open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E

private def ricciQuadraticPermutationCycleZeroThreeOneTwo : Equiv.Perm (Fin 4) :=
  ⟨![3, 2, 0, 1], ![2, 3, 1, 0], by decide, by decide⟩

private def ricciQuadraticPermutationSwapBlocks : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

private def ricciQuadraticPermutationCycleZeroThreeTwo : Equiv.Perm (Fin 4) :=
  ⟨![3, 1, 0, 2], ![2, 1, 3, 0], by decide, by decide⟩

private def ricciQuadraticPermutationCycleZeroOneThreeTwo : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

private def ricciQuadraticPermutationCycleZeroOneTwo : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

private def ricciQuadraticPermutationSwapZeroTwo : Equiv.Perm (Fin 4) :=
  ⟨![2, 1, 0, 3], ![2, 1, 0, 3], by decide, by decide⟩

private def ricPerm3012 : Equiv.Perm (Fin 4) :=
  ⟨![3, 0, 1, 2], ![1, 2, 3, 0], by decide, by decide⟩

private def ricPerm2013 : Equiv.Perm (Fin 4) :=
  ⟨![2, 0, 1, 3], ![1, 2, 0, 3], by decide, by decide⟩

private def ricciQuadraticPermutationSwapZeroOne : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def ricciQuadraticPermutationRotateInputs : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

omit [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
private lemma ricUpdate2Zero (a b c : E) :
    Function.update ![a, b] (0 : Fin 2) c = ![c, b] := by
  funext i
  fin_cases i <;> simp [Function.update]

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem permCoeff_smooth (_g : SmoothRiemannianMetric I M) {d : Nat}
    (rho : Equiv.Perm (Fin d)) :
    ContMDiff I (I.prod 𝓘(Real, Tensor0SBundle.TensorRSModel d d Real E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel d d Real E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace d d I z) x
        (show Tensor0SBundle.TensorRSSpace d d I x from
          slotPermCLM (I := I) rho x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel d Real E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)
    (F₂ := Tensor0SBundle.Tensor0SModel d Real E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)
    (φ := fun x : M => slotPermCLM (I := I) rho x)
  intro Y
  have h := slotPermCLM_field_contMDiff (I := I) rho
    (fun x => Y x) Y.contMDiff
  refine h.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk'
    (Tensor0SBundle.Tensor0SModel d Real E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x t) rfl

def permCoeff (g : SmoothRiemannianMetric I M) {d : Nat}
    (rho : Equiv.Perm (Fin d)) : SmoothCcTensor g d d where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace d d I x from
          slotPermCLM (I := I) rho x)
      contMDiff_toFun := permCoeff_smooth (I := I) (M := M) g rho }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
private theorem permCoeff_toSection (g : SmoothRiemannianMetric I M) {d : Nat}
    (rho : Equiv.Perm (Fin d)) (x : M) :
    (permCoeff (I := I) (M := M) g rho).toSection x =
      (show Tensor0SSpace d I x →L[Real] Tensor0SSpace d I x from
        slotPermCLM (I := I) rho x) := rfl

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
  [FiniteDimensional Real E] in
private theorem ricciReindexCoeffFibGen_innerContractionSwapPerm_eq_comp
    {s : ℕ} (x : M)
    (A : Tensor0SSpace 2 I x →L[Real] Tensor0SSpace s I x) :
    reindexCoeffFibGen (I := I) 2 s innerContractionSwapPerm x A =
      A.comp (slotPermCLM (I := I) perm210 x) := by
  apply ContinuousLinearMap.ext
  intro D
  rw [reindexCoeffFibGen_apply, ContinuousLinearMap.comp_apply, slotPermCLM_apply]
  rfl

private def ricQuad0 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeOneTwo)
    (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g gm)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroOne)
        (connectionDifferenceContrInsertionInnerField (I := I) g gm)))

private def ricQuad1 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapBlocks)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
        (connectionDifferenceContravariantInsertionField (I := I) g gm)
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroOne)
          (connectionDifferenceContrInsertionInnerField (I := I) g gm))))
    innerContractionSwapPerm

private def ricQuad2 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeTwo)
    (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g gm)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationRotateInputs)
        (connectionDifferenceContrInsertionInnerField (I := I) g gm)))

private def ricQuad3 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneThreeTwo)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
        (connectionDifferenceContravariantInsertionField (I := I) g gm)
        (connectionDifferenceContrInsertionInnerField (I := I) g gm)))
    innerContractionSwapPerm

private def ricQuad4 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneTwo)
    (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g gm)
      (connectionDifferenceContrInsertionInnerField (I := I) g gm))

private def ricQuad5 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroTwo)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
        (connectionDifferenceContravariantInsertionField (I := I) g gm)
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricciQuadraticPermutationRotateInputs)
          (connectionDifferenceContrInsertionInnerField (I := I) g gm))))
    innerContractionSwapPerm

private def ricDer0 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 4 4
    (permCoeff (I := I) (M := M) g ricPerm3012)
    (connectionDifferenceGradContrInsertionField (I := I) g gm)

private def ricDer1 (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm2013)
      (connectionDifferenceGradContrInsertionField (I := I) g gm))
    innerContractionSwapPerm

def ricciConnectionDifferenceQuadraticKernel (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  ricQuad0 (I := I) (M := M) g gm +
    ricQuad1 (I := I) (M := M) g gm +
    ricQuad2 (I := I) (M := M) g gm +
    ricQuad3 (I := I) (M := M) g gm +
    ricQuad4 (I := I) (M := M) g gm +
    ricQuad5 (I := I) (M := M) g gm

def ricciCovariantDerivativeConnectionDifferenceKernel (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
  -ricDer0 (I := I) (M := M) g gm -
    ricDer1 (I := I) (M := M) g gm

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem ricciKer_split (g gm : SmoothRiemannianMetric I M) :
    linearizedRicciConnectionDifferenceOrder0KernelField (I := I) g gm =
      ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gm +
        ricciCovariantDerivativeConnectionDifferenceKernel (I := I) (M := M) g gm := by
  have hraw :
      linearizedRicciConnectionDifferenceOrder0KernelField (I := I) g gm =
        ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gm -
          ricDer0 (I := I) (M := M) g gm -
          ricDer1 (I := I) (M := M) g gm := by
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    rw [linearizedRicciConnectionDifferenceOrder0KernelField_toSection]
    unfold linearizedRicciConnectionDifferenceOrder0KernelFib
    simp only [ricciConnectionDifferenceQuadraticKernel, ricQuad0, ricQuad1,
      ricQuad2, ricQuad3, ricQuad4, ricQuad5, SmoothCcTensor.toSection_add,
      SmoothCcTensor.toSection_sub, ContMDiffSection.coe_add,
      ContMDiffSection.coe_sub, Pi.add_apply, Pi.sub_apply,
      operatorFieldComposition_toSection, reindexCoeffGen_toSection,
      connectionDifferenceContravariantInsertionField_toSection,
      connectionDifferenceContrInsertionInnerField_toSection,
      connectionDifferenceGradContrInsertionField_toSection, ricDer0, ricDer1,
      permCoeff_toSection]
    simp only [ricciReindexCoeffFibGen_innerContractionSwapPerm_eq_comp]
    rw [show ricciQuadraticPermutationCycleZeroThreeOneTwo = perm43201 from rfl,
      show ricciQuadraticPermutationSwapBlocks = perm42301 from rfl,
      show ricciQuadraticPermutationCycleZeroThreeTwo = perm43102 from rfl,
      show ricciQuadraticPermutationCycleZeroOneThreeTwo = perm41302 from rfl,
      show ricciQuadraticPermutationCycleZeroOneTwo = perm41203 from rfl,
      show ricciQuadraticPermutationSwapZeroTwo = perm42103 from rfl,
      show ricPerm3012 = perm43012 from rfl,
      show ricPerm2013 = perm42013 from rfl,
      show ricciQuadraticPermutationSwapZeroOne = perm3102 from rfl,
      show ricciQuadraticPermutationRotateInputs = perm3120 from rfl]
    unfold linearizedRicciConnectionDifferenceOrder0CLM
    simp only [ContinuousLinearMap.comp_assoc]
  rw [hraw, ricciCovariantDerivativeConnectionDifferenceKernel]
  module

def ricciConnectionDifferenceQuadraticArm (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 2 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 4 2
    (ricciCometricFourTraceCastG0 (I := I) g gm)
    (ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gm)

def ricciCovariantDerivativeConnectionDifferenceArm (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 2 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 4 2
    (ricciCometricFourTraceCastG0 (I := I) g gm)
    (ricciCovariantDerivativeConnectionDifferenceKernel (I := I) (M := M) g gm)

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem ricciCoeff_split (g gm : SmoothRiemannianMetric I M) :
    linearizedRicciConnectionDifferenceOrder0CoeffField (I := I) (M := M) g gm =
      ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gm +
        ricciCovariantDerivativeConnectionDifferenceArm (I := I) (M := M) g gm := by
  rw [linearizedRicciConnectionDifferenceOrder0CoeffField_eq_ricciCometricFourTrace_comp_kernelField,
    ricciKer_split, operatorFieldComposition_add_right]
  rfl

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private lemma ricPerm3012_eval (x : M) (D : Tensor0SSpace 4 I x)
    (a b c d : E) :
    Tensor0SSpace.toModel (slotPermCLM (I := I) ricPerm3012 x D)
        ![a, b, c, d] =
      Tensor0SSpace.toModel D ![d, a, b, c] := by
  rw [slotPermCLM_apply, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private lemma ricPerm2013_eval (x : M) (D : Tensor0SSpace 4 I x)
    (a b c d : E) :
    Tensor0SSpace.toModel (slotPermCLM (I := I) ricPerm2013 x D)
        ![a, b, c, d] =
      Tensor0SSpace.toModel D ![c, a, b, d] := by
  rw [slotPermCLM_apply, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private lemma ricPerm2_eval (x : M) (D : Tensor0SSpace 2 I x)
    (a b : E) :
    Tensor0SSpace.toModel (slotPermCLM (I := I) innerContractionSwapPerm x D)
        ![a, b] =
      Tensor0SSpace.toModel D ![b, a] := by
  rw [slotPermCLM_apply, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  exact congrArg _ (funext fun j => by fin_cases j <;> rfl)

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem ricciCovariantDerivativeConnectionDifferenceKernel_fiber_apply (g gm : SmoothRiemannianMetric I M) (x : M)
    (T : Tensor0SSpace 2 I x) (v : Fin 4 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[Real] Tensor0SSpace 4 I x from
          (ricciCovariantDerivativeConnectionDifferenceKernel (I := I) (M := M) g gm).toSection x) T)
        v =
      -Tensor0SSpace.toModel T
          ![rs13ContrVec (I := I) (M := M) x
              (show TensorRSSpace 1 3 I x from
                (covGrad (I := I) (M := M) g 1 2
                  (connectionDifferenceSection (I := I) gm g)).toSection x)
              ![v 0, v 1, v 2], v 3] -
        Tensor0SSpace.toModel T
          ![v 2,
            rs13ContrVec (I := I) (M := M) x
              (show TensorRSSpace 1 3 I x from
                (covGrad (I := I) (M := M) g 1 2
                  (connectionDifferenceSection (I := I) gm g)).toSection x)
              ![v 0, v 1, v 3]] := by
  let DA : TensorRSSpace 1 3 I x :=
    (covGrad (I := I) (M := M) g 1 2
      (connectionDifferenceSection (I := I) gm g)).toSection x
  change Tensor0SSpace.toModel
      (((-(slotPermCLM (I := I) ricPerm3012 x).comp
          (connContrCLM (I := I) 1 2 x DA) -
        (slotPermCLM (I := I) ricPerm2013 x).comp
          ((connContrCLM (I := I) 1 2 x DA).comp
            (slotPermCLM (I := I) innerContractionSwapPerm x))) T))
        v = _
  simp only [sub_apply, neg_apply,
    ContinuousLinearMap.comp_apply, Tensor0SSpace.toModel_sub,
    Tensor0SSpace.toModel_neg]
  have hv : v = ![v 0, v 1, v 2, v 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  rw [ricPerm3012_eval, ricPerm2013_eval]
  rw [connContr12_insert, connContr12_insert]
  rw [ricPerm2_eval]
  simp
  simp only [DA]

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem ricTrace_eval (g gm : SmoothRiemannianMetric I M)
    (Z : SmoothCcTensor g 0 4) (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 4 2
          (cometricDoubleTraceCoefficient (I := I) (M := M) g gm) Z) x v =
      ∑ i : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 4 Z x
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x
              (metricComparisonEndomorphismField (I := I) (M := M) g gm x
                (smoothOrthoFrame (I := I) g x i x)),
            tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g x i x),
            v 0, v 1] := by
  classical
  rw [show cometricDoubleTraceCoefficient (I := I) (M := M) g gm =
      secondMetricCometricDoubleTraceField (I := I) (M := M) g gm 2 from rfl]
  rw [pairTrace_decomposition (I := I) (M := M) g gm 2]
  rw [← operatorFieldApplication_assoc (I := I) (M := M) g 4 4 2]
  rw [unitModel, operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply]
  rw [show ((show Tensor0SSpace 4 I x →L[Real] Tensor0SSpace 2 I x from
        (cometricDoubleTraceField (I := I) g 2).toSection x)
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 4 I x from
        (operatorFieldApply (I := I) (M := M) g 4 4
          (endoSlotZeroCcTensor (I := I) (M := M) g 3
            (metricComparisonEndomorphismField (I := I) (M := M) g gm)) Z).toSection x)
        (unitTensor (I := I) (M := M) x))) =
      cometricDoubleTraceFib (I := I) g 2 x
        (slotInsertEndoFib (I := I) (M := M) 4 0 x
          (metricComparisonEndomorphismField (I := I) (M := M) g gm x)
          ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 4 I x from
            Z.toSection x) (unitTensor (I := I) (M := M) x))) from by
      rw [cometricDoubleTraceField_toSection, operatorFieldApplication_toSection]
      rfl]
  rw [cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [slotInsertEndoFib_apply_eval, Fin.update_cons_zero]
  rw [unitModel]
  congr 1
  funext k
  fin_cases k <;> rfl

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma ricUnit_sub (g : SmoothRiemannianMetric I M) (s : Nat)
    (A B : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (A - B) x =
      unitModel (I := I) (M := M) g s A x -
        unitModel (I := I) (M := M) g s B x := by
  have h :
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
          (A - B).toSection x) (unitTensor (I := I) (M := M) x)) =
        (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
          A.toSection x) (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
          B.toSection x) (unitTensor (I := I) (M := M) x) := by
    rw [show ((A - B).toSection x) = A.toSection x - B.toSection x from by
      rw [SmoothCcTensor.toSection_sub]
      rfl]
    rfl
  rw [unitModel, unitModel, unitModel, h, Tensor0SSpace.toModel_sub]

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma ricUnit_add (g : SmoothRiemannianMetric I M) (s : Nat)
    (A B : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (A + B) x =
      unitModel (I := I) (M := M) g s A x +
        unitModel (I := I) (M := M) g s B x := by
  rw [unitModel, unitModel, unitModel,
    show (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        (A + B).toSection x) =
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        A.toSection x) +
      (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
        B.toSection x) from by
          rw [SmoothCcTensor.toSection_add]
          rfl]
  rw [add_apply, Tensor0SSpace.toModel_add]

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma ricUnit_smul (g : SmoothRiemannianMetric I M) (s : Nat)
    (c : Real) (A : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (c • A) x =
      c • unitModel (I := I) (M := M) g s A x := by
  have h :
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
          (c • A).toSection x) (unitTensor (I := I) (M := M) x)) =
        c • ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
          A.toSection x) (unitTensor (I := I) (M := M) x)) := by
    rw [show ((c • A).toSection x) = c • A.toSection x from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rfl
  rw [unitModel, unitModel, h, Tensor0SSpace.toModel_smul]

def ricciCovariantDerivativeConnectionDifferenceFlux (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 4 :=
  let WR : SmoothCcTensor g 0 2 :=
    pairSlot2 (I := I) (M := M) g
      (metricComparisonEndomorphismField (I := I) (M := M) g gm) 0 W
  let P : SmoothCcTensor g 0 4 :=
    pairProd4 (I := I) (M := M) g W WR
  P - domDomCongrSection (I := I) g ricciQuadraticPermutationCycleZeroOneTwo P

omit [NeZero (Module.finrank Real E)] [BoundarylessManifold I M]
  [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem ricciCovariantDerivativeConnectionDifferenceFlux_unitModel (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (x : M) (v : Fin 4 → E) :
    unitModel (I := I) (M := M) g 4
        (ricciCovariantDerivativeConnectionDifferenceFlux (I := I) (M := M) g gm W) x v =
        unitModel (I := I) (M := M) g 2 W x ![v 0, v 1] *
          unitModel (I := I) (M := M) g 2 W x
            ![tangentLinearMapToModel
                (metricComparisonEndomorphismField (I := I) (M := M) g gm x) (v 2),
              v 3] -
        unitModel (I := I) (M := M) g 2 W x ![v 1, v 2] *
          unitModel (I := I) (M := M) g 2 W x
            ![tangentLinearMapToModel
                (metricComparisonEndomorphismField (I := I) (M := M) g gm x) (v 0),
              v 3] := by
  let WR : SmoothCcTensor g 0 2 :=
    pairSlot2 (I := I) (M := M) g
      (metricComparisonEndomorphismField (I := I) (M := M) g gm) 0 W
  let P : SmoothCcTensor g 0 4 :=
    pairProd4 (I := I) (M := M) g W WR
  rw [ricciCovariantDerivativeConnectionDifferenceFlux, ricUnit_sub]
  change unitModel (I := I) (M := M) g 4 P x v -
      unitModel (I := I) (M := M) g 4
        (domDomCongrSection (I := I) g ricciQuadraticPermutationCycleZeroOneTwo P) x v = _
  rw [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hv : (fun i => v (ricciQuadraticPermutationCycleZeroOneTwo i)) = ![v 1, v 2, v 0, v 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  simp only [P, pairProd4_eval, WR, pairSlot2_eval]
  simp_rw [ricUpdate2Zero]
  simp

def ricciConnectionDifferenceCovariantDerivativeTensor (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 0 4 :=
  domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1)
    (covGrad (I := I) (M := M) g 0 3
      (domDomCongrSection (I := I) g (finRotate 3)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gm)))

def ricciCovariantDerivativeConnectionDifferenceFluxReindex (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 4 :=
  domDomCongrSection (I := I) g ricPerm3012.symm
    (ricciCovariantDerivativeConnectionDifferenceFlux (I := I) (M := M) g gm W)

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank Real E)] in
theorem ricciFlux_riemannianFiberNormSq (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (j : Nat) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
        ((iteratedCovGrad (I := I) g 0 4 j
          (ricciCovariantDerivativeConnectionDifferenceFlux (I := I) (M := M) g gm W)).toSection x) ≤
      4 * riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
        ((iteratedCovGrad (I := I) g 0 4 j
          (pairProd4 (I := I) (M := M) g W
            (pairSlot2 (I := I) (M := M) g
              (metricComparisonEndomorphismField (I := I) (M := M) g gm) 0 W))).toSection x) := by
  let WR : SmoothCcTensor g 0 2 :=
    pairSlot2 (I := I) (M := M) g
      (metricComparisonEndomorphismField (I := I) (M := M) g gm) 0 W
  let Q : SmoothCcTensor g 0 4 :=
    pairProd4 (I := I) (M := M) g W WR
  rw [ricciCovariantDerivativeConnectionDifferenceFlux]
  change riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
      ((iteratedCovGrad (I := I) g 0 4 j
        (Q - domDomCongrSection (I := I) g ricciQuadraticPermutationCycleZeroOneTwo Q)).toSection x) ≤ _
  rw [iteratedCovGrad_sub, SmoothCcTensor.toSection_sub]
  have hadd := riemannianFiberNormSq_sub_le
    (I := I) (M := M) g 0 (4 + j) x
    ((iteratedCovGrad (I := I) g 0 4 j Q).toSection x)
    ((iteratedCovGrad (I := I) g 0 4 j
      (domDomCongrSection (I := I) g ricciQuadraticPermutationCycleZeroOneTwo Q)).toSection x)
  have hperm :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneTwo Q j x
  calc
    _ ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
          ((iteratedCovGrad (I := I) g 0 4 j Q).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
          ((iteratedCovGrad (I := I) g 0 4 j
            (domDomCongrSection (I := I) g ricciQuadraticPermutationCycleZeroOneTwo Q)).toSection x) := hadd
    _ = 4 * riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
          ((iteratedCovGrad (I := I) g 0 4 j Q).toSection x) := by
      rw [hperm]
      ring
    _ = _ := by rfl

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem ricciPart_riemannianFiberNormSq (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (j : Nat) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
        ((iteratedCovGrad (I := I) g 0 4 j
          (ricciCovariantDerivativeConnectionDifferenceFluxReindex (I := I) (M := M) g gm W)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
        ((iteratedCovGrad (I := I) g 0 4 j
          (ricciCovariantDerivativeConnectionDifferenceFlux (I := I) (M := M) g gm W)).toSection x) := by
  rw [ricciCovariantDerivativeConnectionDifferenceFluxReindex]
  exact riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
    (I := I) (M := M) g ricPerm3012.symm
      (ricciCovariantDerivativeConnectionDifferenceFlux (I := I) (M := M) g gm W) j x

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem ricciConnectionDifferenceCovariantDerivativeTensor_unitModel (g gm : SmoothRiemannianMetric I M)
    (x : M) (v : Fin 4 → E) :
    unitModel (I := I) (M := M) g 4
        (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x v =
      unitModel (I := I) (M := M) g 4
        (covGrad (I := I) (M := M) g 0 3
          (domDomCongrSection (I := I) g (finRotate 3)
            (metricLoweredConnectionDifferenceCoefficient (I := I) g gm))) x
        ![v 1, v 0, v 2, v 3] := by
  rw [ricciConnectionDifferenceCovariantDerivativeTensor, domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
private lemma ricLow_unitModel (g gm : SmoothRiemannianMetric I M)
    (x : M) :
    unitModel (I := I) (M := M) g 3
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gm) x =
      Tensor0SSpace.toModel (metricLoweredConnectionDifferenceCovector (I := I) g gm x) := by
  rw [unitModel]
  rw [show (metricLoweredConnectionDifferenceCoefficient (I := I) g gm).toSection x
        (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E)
          (E := (TangentSpace I : M → Type _)) x).smulRight
        (metricLoweredConnectionDifferenceField (I := I) g gm x)
        (ContinuousMultilinearMap.constOfIsEmpty Real
          (fun _ : Fin 0 => TangentSpace I x) (1 : Real)) from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
private lemma ricLow_eval (g gm : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g 3
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gm) x
          (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (m i)) =
      g.inner x (PDE.DeTurck.connectionDifference (I := I) gm g x (m 0) (m 1))
        (m 2) := by
  rw [ricLow_unitModel]
  rfl

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma ricInterior_eval (s : Nat) (x : M)
    (v : TangentSpace I x) (D : Tensor0SSpace (s + 1) I x)
    (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interiorProduct (𝕜 := Real) (I := I) s x v D) w =
      Tensor0SSpace.toModel D
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x v)
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (w k))) := by
  have h : Tensor0SSpace.toModel
      (Tensor0SBundle.interiorProduct (𝕜 := Real) (I := I) s x v D) =
      Tensor0SBundle.modelInteriorProduct (𝕜 := Real) (E := E) s
        (tangentSpaceModelContinuousLinearEquiv (I := I) x v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h]
  rfl

omit [NeZero (Module.finrank Real E)] in
private lemma ricCDual_coord
    (B : Module.Basis (Fin (Module.finrank Real E)) Real E)
    (k : Fin (Module.finrank Real E)) :
    B.cDualBasis k = LinearMap.toContinuousLinearMap (B.coord k) := by
  rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
  exact congrArg (fun L : E →ₗ[Real] Real => LinearMap.toContinuousLinearMap L)
    (congrFun (Module.Basis.coe_dualBasis B) k)

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private lemma ricRS13_pair (x : M) (B : TensorRSSpace 1 3 I x)
    (beta : Tensor0SSpace 1 I x) (v : Fin 3 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[Real] Tensor0SSpace 3 I x from B)
          beta) v =
      Tensor0SSpace.toModel beta
        (fun _ : Fin 1 => rs13ContrVec (I := I) (M := M) x B v) := by
  classical
  have hci : ∀ i : Fin (Module.finrank Real E),
      ((Module.finBasis Real E).cDualBasis i)
          (rs13ContrVec (I := I) (M := M) x B v) =
        (TensorRSSpace.toModel B
          (Tensor0SBundle.modelCovectorOfCLM (𝕜 := Real) (E := E)
            ((Module.finBasis Real E).cDualBasis i))) v := by
    intro i
    rw [rs13ContrVec, ricCDual_coord (Module.finBasis Real E) i]
    rw [map_sum]
    rw [show (∑ j : Fin (Module.finrank Real E),
        LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord i)
          (((TensorRSSpace.toModel B
              (Tensor0SBundle.modelCovectorOfCLM (𝕜 := Real) (E := E)
                ((Module.finBasis Real E).cDualBasis j))) v) •
            (Module.finBasis Real E) j)) =
        ∑ j : Fin (Module.finrank Real E),
          ((TensorRSSpace.toModel B
              (Tensor0SBundle.modelCovectorOfCLM (𝕜 := Real) (E := E)
                ((Module.finBasis Real E).cDualBasis j))) v) *
            ((Module.finBasis Real E).repr
              ((Module.finBasis Real E) j) i) from
      Finset.sum_congr rfl (fun j _ => by
        rw [map_smul]
        rfl)]
    rw [Finset.sum_congr rfl (fun j _ => by
      rw [Module.Basis.repr_self,
        show (Finsupp.single j (1 : Real)) i =
            if j = i then (1 : Real) else 0 from Finsupp.single_apply,
        mul_ite, mul_one, mul_zero])]
    rw [Finset.sum_ite_eq' Finset.univ i]
    simp only [Finset.mem_univ, ↓reduceIte]
    rw [ricCDual_coord (Module.finBasis Real E) i]
  have hexp : Tensor0SSpace.toModel beta =
      ∑ i : Fin (Module.finrank Real E),
        (Tensor0SSpace.toModel beta
          (Fin.cons ((Module.finBasis Real E) i) ![])) •
          Tensor0SBundle.modelCovectorOfCLM (𝕜 := Real) (E := E)
            ((Module.finBasis Real E).cDualBasis i) := by
    refine ContinuousMultilinearMap.ext (fun w => ?_)
    rw [sum_apply]
    rw [Finset.sum_congr rfl (fun i _ => by
      rw [smul_apply, smul_eq_mul,
        Tensor0SBundle.model_covectorOfCLM_apply])]
    rw [sum_cons_cDual_collapse (I := I) (M := M) beta ![] (w 0)]
    congr 1
    funext j
    fin_cases j
    rfl
  have hL : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[Real] Tensor0SSpace 3 I x from B)
        beta) =
      TensorRSSpace.toModel B (Tensor0SSpace.toModel beta) :=
    toModel_tensorRS_apply (I := I) 1 3 x B beta
  have hR : Tensor0SSpace.toModel beta
      (fun _ : Fin 1 => rs13ContrVec (I := I) (M := M) x B v) =
      ∑ i : Fin (Module.finrank Real E),
        Tensor0SSpace.toModel beta
            (Fin.cons ((Module.finBasis Real E) i) ![]) *
          (TensorRSSpace.toModel B
            (Tensor0SBundle.modelCovectorOfCLM (𝕜 := Real) (E := E)
              ((Module.finBasis Real E).cDualBasis i))) v := by
    rw [show Tensor0SSpace.toModel beta
        (fun _ : Fin 1 => rs13ContrVec (I := I) (M := M) x B v) =
      Tensor0SSpace.toModel beta
        (Fin.cons (rs13ContrVec (I := I) (M := M) x B v) ![]) from
      congrArg (fun w => Tensor0SSpace.toModel beta w)
        (funext (fun j => by fin_cases j; rfl))]
    rw [← sum_cons_cDual_collapse (I := I) (M := M) beta ![]
      (rs13ContrVec (I := I) (M := M) x B v)]
    exact Finset.sum_congr rfl (fun i _ => by rw [hci i])
  rw [hL, hR]
  conv_lhs => rw [hexp]
  rw [map_sum, sum_apply]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [map_smul, smul_apply, smul_eq_mul])

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem connRaise_eq (g gm : SmoothRiemannianMetric I M) :
    connectionDifferenceSection (I := I) gm g =
      cometricRaiseSlot0Field (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g (finRotate 3)
          (metricLoweredConnectionDifferenceCoefficient (I := I) g gm)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connectionDifferenceSection_toSection, cometricRaiseSlot0Field_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g (finRotate 3)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gm)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS :
      (show Tensor0SSpace 1 I x →L[Real] Tensor0SSpace 2 I x from
        connectionDifferenceFib (I := I) gm g x) om YZ =
      g.inner x u (PDE.DeTurck.connectionDifference (I := I) gm g x (YZ 0) (YZ 1)) := by
    rw [connectionDifferenceFib_apply_eval]
    rw [show om
          (fun _ : Fin 1 =>
            PDE.DeTurck.connectionDifference (I := I) gm g x (YZ 0) (YZ 1)) =
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connectionDifference (I := I) gm g x (YZ 0) (YZ 1)) from
      (cotangentToDual_apply (I := I) om _).symm]
    rw [show cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connectionDifference (I := I) gm g x (YZ 0) (YZ 1)) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connectionDifference (I := I) gm g x (YZ 0) (YZ 1)) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g x om
      (PDE.DeTurck.connectionDifference (I := I) gm g x (YZ 0) (YZ 1)), ← hu]
  have hRHS :
      (show Tensor0SSpace 1 I x →L[Real] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g 1 x D) om YZ =
      Tensor0SSpace.toModel D
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x u)
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g 1 x D om]
    rw [show (Tensor0SBundle.interiorProduct (𝕜 := Real) (I := I)
            (1 + 1) x (inverseMetricSharpFib (I := I) g x om) D YZ :
          Real) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interiorProduct (𝕜 := Real) (I := I)
            (1 + 1) x (inverseMetricSharpFib (I := I) g x om) D) YZ from
      rfl]
    rw [ricInterior_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g x om) D YZ, ← hu]
  refine hLHS.trans (Eq.trans ?_ hRHS.symm)
  have hum : unitModel (I := I) (M := M) g 3
      (domDomCongrSection (I := I) g (finRotate 3)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gm)) x =
      Tensor0SSpace.toModel D := rfl
  rw [show Tensor0SSpace.toModel D
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x u)
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ k))) =
      unitModel (I := I) (M := M) g 3
        (domDomCongrSection (I := I) g (finRotate 3)
          (metricLoweredConnectionDifferenceCoefficient (I := I) g gm)) x
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x u,
              tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 0),
              tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 1)] from by
    rw [hum]
    congr 1
    funext k
    fin_cases k <;> rfl]
  rw [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i =>
      (![tangentSpaceModelContinuousLinearEquiv (I := I) x u,
          tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 0),
          tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 1)] : Fin 3 → E)
        ((finRotate 3) i)) =
      ![tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 0),
        tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 1),
        tangentSpaceModelContinuousLinearEquiv (I := I) x u] from by
    funext i
    fin_cases i <;> rfl]
  rw [g.symm x u
    (PDE.DeTurck.connectionDifference (I := I) gm g x (YZ 0) (YZ 1))]
  refine (ricLow_eval (I := I) (M := M) g gm x ![YZ 0, YZ 1, u]).symm.trans ?_
  congr 1

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank Real E)] in
theorem covConnRaise_eq (g gm : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g 1 2 (connectionDifferenceSection (I := I) gm g) =
      cometricRaiseSlot0Field (I := I) (M := M) g 2
        (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) := by
  rw [connRaise_eq,
    covGrad_cometricRaiseSlot0Field_eq (I := I) (M := M)]
  rfl

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank Real E)] in
theorem ricciConnectionDifferenceCovariantDerivativeTensor_pairing (g gm : SmoothRiemannianMetric I M) (x : M)
    (r p u v : TangentSpace I x) :
    g.inner x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
          (rs13ContrVec (I := I) (M := M) x
          (show TensorRSSpace 1 3 I x from
            (covGrad (I := I) (M := M) g 1 2
              (connectionDifferenceSection (I := I) gm g)).toSection x)
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x p,
            tangentSpaceModelContinuousLinearEquiv (I := I) x u,
            tangentSpaceModelContinuousLinearEquiv (I := I) x v])) r =
      unitModel (I := I) (M := M) g 4
        (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x r,
            tangentSpaceModelContinuousLinearEquiv (I := I) x p,
            tangentSpaceModelContinuousLinearEquiv (I := I) x u,
            tangentSpaceModelContinuousLinearEquiv (I := I) x v] := by
  classical
  let D : Tensor0SSpace 4 I x :=
    (show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 4 I x from
      (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm).toSection x)
      (unitTensor (I := I) (M := M) x)
  let B : TensorRSSpace 1 3 I x :=
    cometricRaiseSlot0Fib (I := I) g 2 x D
  have hB :
      (show TensorRSSpace 1 3 I x from
        (covGrad (I := I) (M := M) g 1 2
          (connectionDifferenceSection (I := I) gm g)).toSection x) = B := by
    dsimp [B, D]
    rw [covConnRaise_eq (I := I) (M := M) g gm,
      cometricRaiseSlot0Field_toSection]
  rw [hB]
  let q : Fin 3 → E :=
    ![tangentSpaceModelContinuousLinearEquiv (I := I) x p,
      tangentSpaceModelContinuousLinearEquiv (I := I) x u,
      tangentSpaceModelContinuousLinearEquiv (I := I) x v]
  let R : E := rs13ContrVec (I := I) (M := M) x B q
  change g.inner x ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm R) r =
    Tensor0SSpace.toModel D
      ![tangentSpaceModelContinuousLinearEquiv (I := I) x r,
        tangentSpaceModelContinuousLinearEquiv (I := I) x p,
        tangentSpaceModelContinuousLinearEquiv (I := I) x u,
        tangentSpaceModelContinuousLinearEquiv (I := I) x v]
  have hp := ricRS13_pair (I := I) (M := M) x B
    (g0FlatCLM (I := I) g x r) q
  have hleft :
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[Real] Tensor0SSpace 3 I x from B)
          (g0FlatCLM (I := I) g x r)) q =
        Tensor0SSpace.toModel D
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x r,
            tangentSpaceModelContinuousLinearEquiv (I := I) x p,
            tangentSpaceModelContinuousLinearEquiv (I := I) x u,
            tangentSpaceModelContinuousLinearEquiv (I := I) x v] := by
    dsimp [B]
    rw [cometricRaiseSlot0Fib_clm_apply,
      inverseMetricSharpFib_g0FlatCLM]
    change Tensor0SSpace.toModel
      (Tensor0SBundle.interiorProduct (𝕜 := Real) (I := I) 3 x r D) q =
        Tensor0SSpace.toModel D
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x r,
            tangentSpaceModelContinuousLinearEquiv (I := I) x p,
            tangentSpaceModelContinuousLinearEquiv (I := I) x u,
            tangentSpaceModelContinuousLinearEquiv (I := I) x v]
    rw [ricInterior_eval (I := I) (M := M) 3 x r D q]
    dsimp [q]
    congr 1
  have hright :
      Tensor0SSpace.toModel (g0FlatCLM (I := I) g x r)
          (fun _ : Fin 1 => R) =
        g.inner x r ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm R) := by
    rw [Tensor0SSpace.toModel_apply_model_vector]
    rw [show (g0FlatCLM (I := I) g x r)
          (fun _ : Fin 1 =>
            (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm R) =
        cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g x r)
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm R)
      from (cotangentToDual_apply (I := I) (x := x) _ _).symm]
    rw [cotangentToDual_g0FlatCLM]
  rw [hleft] at hp
  change Tensor0SSpace.toModel D
      ![tangentSpaceModelContinuousLinearEquiv (I := I) x r,
        tangentSpaceModelContinuousLinearEquiv (I := I) x p,
        tangentSpaceModelContinuousLinearEquiv (I := I) x u,
        tangentSpaceModelContinuousLinearEquiv (I := I) x v] =
    Tensor0SSpace.toModel (g0FlatCLM (I := I) g x r)
      (fun _ : Fin 1 => R) at hp
  rw [hright] at hp
  rw [g.symm x ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm R) r, ← hp]

omit [NeZero (Module.finrank Real E)] [CompactSpace M]
  [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma ricL_self (g gm : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g.inner x (metricComparisonEndomorphismField (I := I) (M := M) g gm x v) w =
      g.inner x v
        (metricComparisonEndomorphismField (I := I) (M := M) g gm x w) := by
  rw [metricComparisonEndomorphismField_apply, metricComparisonEndomorphism_apply]
  rw [inner_sharp_mixed (I := I) (M := M) g gm x
    (g0FlatCLM (I := I) g x v) w]
  rw [cotangentToDual_g0FlatCLM]

def connectionDifferenceCovariantDerivativeContraction (g gm : SmoothRiemannianMetric I M) (x : M)
    (a b c : TangentSpace I x) : TangentSpace I x :=
  (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
    (rs13ContrVec (I := I) (M := M) x
      (show TensorRSSpace 1 3 I x from
        (covGrad (I := I) (M := M) g 1 2
          (connectionDifferenceSection (I := I) gm g)).toSection x)
      ![tangentSpaceModelContinuousLinearEquiv (I := I) x a,
        tangentSpaceModelContinuousLinearEquiv (I := I) x b,
        tangentSpaceModelContinuousLinearEquiv (I := I) x c])

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank Real E)] in
theorem connectionDifferenceCovariantDerivativeContraction_pairing (g gm : SmoothRiemannianMetric I M) (x : M)
    (r p u v : TangentSpace I x) :
    g.inner x (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x p u v) r =
      unitModel (I := I) (M := M) g 4
        (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x r,
            tangentSpaceModelContinuousLinearEquiv (I := I) x p,
            tangentSpaceModelContinuousLinearEquiv (I := I) x u,
            tangentSpaceModelContinuousLinearEquiv (I := I) x v] := by
  simpa only [connectionDifferenceCovariantDerivativeContraction] using
    ricciConnectionDifferenceCovariantDerivativeTensor_pairing (I := I) (M := M) g gm x r p u v

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem ricciCovariantDerivativeConnectionDifferenceKernel_operatorFieldApply (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (x : M)
    (v : Fin 4 → E) :
    unitModel (I := I) (M := M) g 4
        (operatorFieldApply (I := I) (M := M) g 2 4
          (ricciCovariantDerivativeConnectionDifferenceKernel (I := I) (M := M) g gm) W) x v =
      -unitModel (I := I) (M := M) g 2 W x
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x
              (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
                ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1))
                ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2))),
            v 3] -
        unitModel (I := I) (M := M) g 2 W x
          ![v 2, tangentSpaceModelContinuousLinearEquiv (I := I) x
            (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1))
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 3)))] := by
  simp only [unitModel, operatorFieldApplication_toSection,
    ContinuousLinearMap.comp_apply]
  simpa only [connectionDifferenceCovariantDerivativeContraction,
    ContinuousLinearEquiv.apply_symm_apply] using
    ricciCovariantDerivativeConnectionDifferenceKernel_fiber_apply (I := I) (M := M) g gm x
      ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace 2 I x from
        W.toSection x) (unitTensor (I := I) (M := M) x)) v

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem connectionDifferenceCovariantDerivativeContraction_symm (g gm : SmoothRiemannianMetric I M) (x : M)
    (a b c : TangentSpace I x) :
    connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x a b c =
      connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x a c b := by
  let X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x a,
      smoothExtensionTangent_contMDiff (I := I) x a⟩
  let Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x b,
      smoothExtensionTangent_contMDiff (I := I) x b⟩
  let Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x c,
      smoothExtensionTangent_contMDiff (I := I) x c⟩
  have hX : X x = a := smoothExtensionTangent_eq (I := I) x a
  have hY : Y x = b := smoothExtensionTangent_eq (I := I) x b
  have hZ : Z x = c := smoothExtensionTangent_eq (I := I) x c
  have h1 := rs13ContrVec_covGrad_eq (I := I) (M := M) gm g X Y Z x
  have h2 := rs13ContrVec_covGrad_eq (I := I) (M := M) gm g X Z Y x
  have h1' :
      rs13ContrVec (I := I) (M := M) x
          (show TensorRSSpace 1 3 I x from
            (covGrad (I := I) (M := M) g 1 2
              (connectionDifferenceSection (I := I) gm g)).toSection x)
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x a,
            tangentSpaceModelContinuousLinearEquiv (I := I) x b,
            tangentSpaceModelContinuousLinearEquiv (I := I) x c] =
        covDerivConnectionDifference (I := I) g gm
          (fun y => X y) (fun y => Z y) (fun y => Y y) x := by
    simpa only [hX, hY, hZ, tangentSpaceModelContinuousLinearEquiv_apply] using h1
  have h2' :
      rs13ContrVec (I := I) (M := M) x
          (show TensorRSSpace 1 3 I x from
            (covGrad (I := I) (M := M) g 1 2
              (connectionDifferenceSection (I := I) gm g)).toSection x)
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x a,
            tangentSpaceModelContinuousLinearEquiv (I := I) x c,
            tangentSpaceModelContinuousLinearEquiv (I := I) x b] =
        covDerivConnectionDifference (I := I) g gm
          (fun y => X y) (fun y => Y y) (fun y => Z y) x := by
    simpa only [hX, hY, hZ, tangentSpaceModelContinuousLinearEquiv_apply] using h2
  unfold connectionDifferenceCovariantDerivativeContraction
  rw [h1', h2', covDerivConnectionDifference_symm23 (I := I) (M := M) gm g X Y Z x]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private lemma ricW_expand (g : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (x : M)
    (y z : TangentSpace I x) :
    unitModel (I := I) (M := M) g 2 W x
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x y,
          tangentSpaceModelContinuousLinearEquiv (I := I) x z] =
      ∑ i : Fin (Module.finrank Real E),
        g.inner x (smoothOrthoFrame (I := I) g x i x) y *
          unitModel (I := I) (M := M) g 2 W x
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) g x i x),
              tangentSpaceModelContinuousLinearEquiv (I := I) x z] := by
  classical
  let e : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  have hcard : Fintype.card (Fin (Module.finrank Real E)) =
      Module.finrank Real (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  have horth : ∀ i j, g.inner x (e i) (e j) =
      if i = j then (1 : Real) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hy := Geometry.Riemannian.expand_orthonormal
    (I := I) (M := M) g x hcard e horth y
  have hunit (a b : TangentSpace I x) :
      unitModel (I := I) (M := M) g 2 W x
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x a,
            tangentSpaceModelContinuousLinearEquiv (I := I) x b] =
        smoothCcTensorBilinForm (I := I) g W x a b := by
    simpa only [tangentSpaceModelContinuousLinearEquiv_apply] using
      unitModel_eq_ccTensorBilin_local (I := I) (M := M) g W x a b
  rw [hunit]
  conv_lhs => rw [hy]
  rw [map_sum, sum_apply]
  refine Finset.sum_congr rfl fun (i : Fin (Module.finrank Real E)) _ => ?_
  rw [ContinuousLinearMap.map_smul, smul_apply, smul_eq_mul,
    ← hunit]

private lemma ricSum_succ {A R : Type*} [Fintype A] [AddCommMonoid R]
    (s : Nat) (F : (Fin (s + 1) → A) → R) :
    (∑ J : Fin (s + 1) → A, F J) =
      ∑ a : A, ∑ J : Fin s → A, F (Fin.cons a J) := by
  classical
  calc
    (∑ J : Fin (s + 1) → A, F J) =
        ∑ p : A × (Fin s → A),
          F ((Fin.consEquiv (fun _ : Fin (s + 1) => A)) p) :=
      ((Fin.consEquiv (fun _ : Fin (s + 1) => A)).sum_comp F).symm
    _ = ∑ a : A, ∑ J : Fin s → A, F (Fin.cons a J) := by
      rw [Fintype.sum_prod_type]
      rfl

private lemma ricSum2 {A : Type*} [Fintype A]
    (F : (Fin 2 → A) → Real) :
    (∑ J : Fin 2 → A, F J) = ∑ a : A, ∑ b : A, F ![a, b] := by
  classical
  calc
    (∑ J : Fin 2 → A, F J) =
        ∑ p : A × A, F ((finTwoArrowEquiv A).symm p) :=
      ((finTwoArrowEquiv A).symm.sum_comp F).symm
    _ = ∑ a : A, ∑ b : A, F ![a, b] := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.sum_congr rfl fun b _ => ?_
      congr 1

private lemma ricSum4 {A : Type*} [Fintype A]
    (F : (Fin 4 → A) → Real) :
    (∑ J : Fin 4 → A, F J) =
      ∑ a : A, ∑ b : A, ∑ c : A, ∑ d : A,
        F ![a, b, c, d] := by
  classical
  rw [ricSum_succ (s := 3)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ricSum_succ (s := 2)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ricSum_succ (s := 1)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ricSum_succ (s := 0)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_eq_single (fun i : Fin 0 => i.elim0)]
  · congr 1
  · intro q _ hq
    exact absurd (Subsingleton.elim q (fun i : Fin 0 => i.elim0)) hq
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma ricSum4_comm
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (F : A → B → C → D → Real) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  classical
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
        ∑ p : A × B, ∑ q : C × D, F p.1 p.2 q.1 q.2 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ q : C × D, ∑ p : A × B, F p.1 p.2 q.1 q.2 :=
      Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
      simp only [Fintype.sum_prod_type]

private lemma ricSum3_cycle {A : Type*} [Fintype A]
    (F : A → A → A → Real) :
    (∑ a, ∑ b, ∑ c, F a b c) =
      ∑ a, ∑ b, ∑ c, F b c a := by
  classical
  calc
    (∑ a, ∑ b, ∑ c, F a b c) =
        ∑ q : A × A, ∑ c, F q.1 q.2 c := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ c, ∑ q : A × A, F q.1 q.2 c := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, F a b c := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ a, ∑ b, ∑ c, F b c a := by
      rfl

private lemma ricPair_alg {A : Type*} [Fintype A]
    (w h : A → A → Real) (d : A → A → A → A → Real) :
    (∑ u, ∑ v, w u v *
      (∑ r, ∑ p, h p r * (d r u v p - d r p u v))) =
      ∑ r, ∑ p, ∑ u, ∑ v,
        (w p u * h v r - w u v * h p r) * d r p u v := by
  classical
  let P : Real := ∑ r, ∑ p, ∑ u, ∑ v,
    w u v * h p r * d r u v p
  let N : Real := ∑ r, ∑ p, ∑ u, ∑ v,
    w u v * h p r * d r p u v
  let F : Real := ∑ r, ∑ p, ∑ u, ∑ v,
    w p u * h v r * d r p u v
  have hL :
      (∑ u, ∑ v, w u v *
        (∑ r, ∑ p, h p r * (d r u v p - d r p u v))) = P - N := by
    calc
      (∑ u, ∑ v, w u v *
          (∑ r, ∑ p, h p r * (d r u v p - d r p u v))) =
          ∑ u, ∑ v, ∑ r, ∑ p,
            w u v * (h p r * (d r u v p - d r p u v)) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum]
      _ = ∑ r, ∑ p, ∑ u, ∑ v,
          w u v * (h p r * (d r u v p - d r p u v)) :=
        ricSum4_comm (fun u v r p =>
          w u v * (h p r * (d r u v p - d r p u v)))
      _ = P - N := by
        dsimp only [P, N]
        have hterm : ∀ r p u v,
            w u v * (h p r * (d r u v p - d r p u v)) =
              w u v * h p r * d r u v p -
                w u v * h p r * d r p u v := by
          intros
          ring
        simp_rw [hterm, Finset.sum_sub_distrib]
  have hR :
      (∑ r, ∑ p, ∑ u, ∑ v,
        (w p u * h v r - w u v * h p r) * d r p u v) = F - N := by
    dsimp only [F, N]
    have hterm : ∀ r p u v,
        (w p u * h v r - w u v * h p r) * d r p u v =
          w p u * h v r * d r p u v -
            w u v * h p r * d r p u v := by
      intros
      ring
    simp_rw [hterm, Finset.sum_sub_distrib]
  have hFP : F = P := by
    dsimp only [F, P]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact ricSum3_cycle
      (fun p u v => w p u * h v r * d r p u v)
  rw [hL, hR, hFP]

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma ricInner0 (g : SmoothRiemannianMetric I M) (s : Nat)
    (A B : SmoothCcTensor g 0 s) (x : M)
    (e : Fin (Module.finrank Real E) → TangentSpace I x)
    (bse : Module.Basis (Fin (Module.finrank Real E)) Real
      (TangentSpace I x))
    (hbse : ∀ i, bse i = e i)
    (horth : ∀ a b, g.inner x (e a) (e b) =
      if a = b then (1 : Real) else 0) :
    tensorInnerPointwise (I := I) (M := M) g 0 s x
        (A.toFun x) (B.toFun x) =
      ∑ J : Fin s → Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g s A x
            (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (e (J k))) *
          unitModel (I := I) (M := M) g s B x
            (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (e (J k))) := by
  classical
  rw [SmoothCcTensor.toFun_apply, SmoothCcTensor.toFun_apply]
  rw [tensorInnerPointwise_eq_sum_componentS_mul
    (I := I) (M := M) g 0 s x e bse rfl hbse horth
    (A.toSection x) (B.toSection x)]
  have hcomp : ∀ (T : SmoothCcTensor g 0 s)
      (K : Fin 0 → Fin (Module.finrank Real E))
      (J : Fin s → Fin (Module.finrank Real E)),
      fiberNormSqComponent (I := I) (M := M) g x 0 s
          (T.toSection x) (Module.finrank Real E) e K J =
        unitModel (I := I) (M := M) g s T x
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (e (J k))) := by
    intro T K J
    rw [show fiberNormSqComponent (I := I) (M := M) g x 0 s
        (T.toSection x) (Module.finrank Real E) e K J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[Real] Tensor0SSpace s I x from
          T.toSection x) (coframeS (I := I) (M := M) g x 0 e K))
        (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (e (J k))) from rfl]
    rw [coframeS_zero_eq_unitZeroSec (I := I) (M := M) g x e K]
    rfl
  have hK : ∀ F : (Fin 0 → Fin (Module.finrank Real E)) → Real,
      (∑ K : Fin 0 → Fin (Module.finrank Real E), F K) =
        F Fin.elim0 := by
    intro F
    rw [Finset.sum_eq_single Fin.elim0]
    · intro q _ hq
      exact absurd (Subsingleton.elim q Fin.elim0) hq
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hK]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [hcomp A Fin.elim0 J, hcomp B Fin.elim0 J]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private lemma ricSmooth_basis (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ bse : Module.Basis (Fin (Module.finrank Real E)) Real
        (TangentSpace I x),
      ∀ i, bse i = smoothOrthoFrame (I := I) g x i x := by
  classical
  let e : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  have horth : ∀ a b : Fin (Module.finrank Real E),
      g.inner x (e a) (e b) = if a = b then (1 : Real) else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  have he_li : LinearIndependent Real e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk
    have hz : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by
      rw [hsum]
      simp
    rw [map_sum] at hz
    have hpull : ∀ j ∈ fs,
        g.inner x (e k) (c j • e j) =
          c j * (if k = j then (1 : Real) else 0) := by
      intro j _
      rw [map_smul, horth k j, smul_eq_mul]
    rw [Finset.sum_congr rfl hpull] at hz
    rw [Finset.sum_eq_single k
      (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
      (fun h => absurd hk h)] at hz
    rwa [if_pos rfl, mul_one] at hz
  have hcard : Fintype.card (Fin (Module.finrank Real E)) =
      Module.finrank Real (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  refine ⟨basisOfLinearIndependentOfCardEqFinrank he_li hcard, fun i => ?_⟩
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard) i

omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M] in
private lemma ricSwap_point (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 4) (x : M) :
    tensorInnerPointwise (I := I) (M := M) g 0 4 x (A.toFun x)
        ((domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) B).toFun x) =
      tensorInnerPointwise (I := I) (M := M) g 0 4 x
        ((domDomCongrSection (I := I) g
          (Equiv.swap (0 : Fin 4) 1) A).toFun x) (B.toFun x) := by
  classical
  let e : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  obtain ⟨bse, hbse0⟩ := ricSmooth_basis (I := I) (M := M) g x
  have hbse : ∀ i, bse i = e i := by
    simpa only [e] using hbse0
  have horth : ∀ a b, g.inner x (e a) (e b) =
      if a = b then (1 : Real) else 0 :=
    fun a b => smoothOrthoFrame_orthonormal_at_center (I := I) g x a b
  rw [ricInner0 (I := I) (M := M) g 4 A
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) B)
      x e bse hbse horth,
    ricInner0 (I := I) (M := M) g 4
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) A)
      B x e bse hbse horth]
  simp_rw [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  let sigma : Equiv.Perm (Fin 4) := Equiv.swap (0 : Fin 4) 1
  let tau : (Fin 4 → Fin (Module.finrank Real E)) ≃
      (Fin 4 → Fin (Module.finrank Real E)) :=
    Equiv.arrowCongr sigma.symm
      (Equiv.refl (Fin (Module.finrank Real E)))
  refine Fintype.sum_equiv tau
    (fun J =>
      unitModel (I := I) (M := M) g 4 A x
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (e (J k))) *
        unitModel (I := I) (M := M) g 4 B x
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x
            (e (J (sigma k)))))
    (fun J =>
      unitModel (I := I) (M := M) g 4 A x
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x
            (e (J (sigma k)))) *
        unitModel (I := I) (M := M) g 4 B x
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (e (J k))))
    (fun J => ?_)
  have htau : tau J = fun k => J (sigma k) := by
    funext k
    simp [tau, sigma, Equiv.arrowCongr]
  rw [htau]
  simp [sigma]

omit [I.Boundaryless] [BoundarylessManifold I M] in
theorem ricSwap_l2 (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 4) :
    tensorL2Inner (I := I) (M := M) g 0 4 A.toFun
        (domDomCongrSection (I := I) g
          (Equiv.swap (0 : Fin 4) 1) B).toFun =
      tensorL2Inner (I := I) (M := M) g 0 4
        (domDomCongrSection (I := I) g
          (Equiv.swap (0 : Fin 4) 1) A).toFun B.toFun := by
  classical
  unfold tensorL2Inner
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact ricSwap_point (I := I) (M := M) g A B x

omit [NeZero (Module.finrank Real E)] [BoundarylessManifold I M]
  [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem ricciCovariantDerivativeConnectionDifferenceFluxReindex_unitModel (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (x : M) (v : Fin 4 → E) :
    unitModel (I := I) (M := M) g 4
        (ricciCovariantDerivativeConnectionDifferenceFluxReindex (I := I) (M := M) g gm W) x v =
      unitModel (I := I) (M := M) g 2 W x ![v 1, v 2] *
          unitModel (I := I) (M := M) g 2 W x
            ![tangentLinearMapToModel
                (metricComparisonEndomorphismField (I := I) (M := M) g gm x) (v 3),
              v 0] -
        unitModel (I := I) (M := M) g 2 W x ![v 2, v 3] *
          unitModel (I := I) (M := M) g 2 W x
            ![tangentLinearMapToModel
                (metricComparisonEndomorphismField (I := I) (M := M) g gm x) (v 1),
              v 0] := by
  rw [ricciCovariantDerivativeConnectionDifferenceFluxReindex, domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hv : (fun i => v (ricPerm3012.symm i)) =
      ![v 1, v 2, v 3, v 0] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, ricciCovariantDerivativeConnectionDifferenceFlux_unitModel]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank Real E)] [BoundarylessManifold I M] in
omit [I.Boundaryless] in
theorem ricFour_eval (g gm : SmoothRiemannianMetric I M)
    (Z : SmoothCcTensor g 0 4) (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 4 2
          (ricciCometricFourTraceCastG0 (I := I) g gm) Z) x v =
      (1 / 2 : Real) *
        (unitModel (I := I) (M := M) g 2
            (operatorFieldApply (I := I) (M := M) g 4 2
              (cometricDoubleTraceCoefficient (I := I) (M := M) g gm)
              (domDomCongrSection (I := I) g fourTraceCyclePerm123 Z)) x v +
          unitModel (I := I) (M := M) g 2
            (operatorFieldApply (I := I) (M := M) g 4 2
              (cometricDoubleTraceCoefficient (I := I) (M := M) g gm)
              (domDomCongrSection (I := I) g fourTraceSwap13Perm Z)) x v -
          unitModel (I := I) (M := M) g 2
            (operatorFieldApply (I := I) (M := M) g 4 2
              (cometricDoubleTraceCoefficient (I := I) (M := M) g gm) Z) x v -
          unitModel (I := I) (M := M) g 2
            (operatorFieldApply (I := I) (M := M) g 4 2
              (cometricDoubleTraceCoefficient (I := I) (M := M) g gm)
              (domDomCongrSection (I := I) g fourTraceDoubleTranspositionPerm Z)) x v) := by
  let Z1 : SmoothCcTensor g 0 4 :=
    domDomCongrSection (I := I) g fourTraceCyclePerm123 Z
  let Z2 : SmoothCcTensor g 0 4 :=
    domDomCongrSection (I := I) g fourTraceSwap13Perm Z
  let Z3 : SmoothCcTensor g 0 4 :=
    domDomCongrSection (I := I) g fourTraceDoubleTranspositionPerm Z
  have h1 := reindexCoeffGen_operatorFieldApplication_eq (I := I) (M := M) g 4
    (cometricDoubleTraceCoefficient (I := I) (M := M) g gm)
    fourTraceCyclePerm123 Z Z1
    (fun y => domDomCongrSection_unitModel (I := I) g
      fourTraceCyclePerm123 Z y) x
  have h2 := reindexCoeffGen_operatorFieldApplication_eq (I := I) (M := M) g 4
    (cometricDoubleTraceCoefficient (I := I) (M := M) g gm)
    fourTraceSwap13Perm Z Z2
    (fun y => domDomCongrSection_unitModel (I := I) g
      fourTraceSwap13Perm Z y) x
  have h3 := reindexCoeffGen_operatorFieldApplication_eq (I := I) (M := M) g 4
    (cometricDoubleTraceCoefficient (I := I) (M := M) g gm)
    fourTraceDoubleTranspositionPerm Z Z3
    (fun y => domDomCongrSection_unitModel (I := I) g
      fourTraceDoubleTranspositionPerm Z y) x
  rw [ricciCometricFourTraceCastG0_eq_reindex_combination]
  simp only [operatorFieldApplication_smul_left, operatorFieldApplication_add_left, operatorFieldApplication_sub_left]
  rw [ricUnit_smul, ricUnit_sub, ricUnit_sub, ricUnit_add]
  simp only [smul_apply,
    sub_apply, add_apply,
    smul_eq_mul]
  change _ = (1 / 2 : Real) *
    (unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 4 2
          (cometricDoubleTraceCoefficient (I := I) (M := M) g gm) Z1) x v +
      unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 4 2
          (cometricDoubleTraceCoefficient (I := I) (M := M) g gm) Z2) x v -
      unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 4 2
          (cometricDoubleTraceCoefficient (I := I) (M := M) g gm) Z) x v -
      unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 4 2
          (cometricDoubleTraceCoefficient (I := I) (M := M) g gm) Z3) x v)
  rw [h1, h2, h3]

omit [SigmaCompactSpace M] in
theorem ricciCovariantDerivativeConnectionDifference_raw_expansion (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (x : M) (v : Fin 2 → E) :
    let e : Fin (Module.finrank Real E) → TangentSpace I x :=
      fun i => smoothOrthoFrame (I := I) g x i x
    let L : TangentSpace I x →L[Real] TangentSpace I x :=
      metricComparisonEndomorphismField (I := I) (M := M) g gm x
    let toTangent : E → TangentSpace I x :=
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
    let toModel : TangentSpace I x → E :=
      tangentSpaceModelContinuousLinearEquiv (I := I) x
    unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2
          (ricciCovariantDerivativeConnectionDifferenceArm (I := I) (M := M) g gm) W) x v =
      (1 / 2 : Real) *
        ∑ i : Fin (Module.finrank Real E),
          (-unitModel (I := I) (M := M) g 2 W x
              ![toModel (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                  (L (e i)) (toTangent (v 0)) (toTangent (v 1))),
                toModel (e i)] -
            unitModel (I := I) (M := M) g 2 W x
              ![v 1,
                toModel (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                  (L (e i)) (toTangent (v 0)) (e i))] -
            unitModel (I := I) (M := M) g 2 W x
              ![toModel (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                  (L (e i)) (toTangent (v 1)) (toTangent (v 0))),
                toModel (e i)] -
            unitModel (I := I) (M := M) g 2 W x
              ![v 0,
                toModel (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                  (L (e i)) (toTangent (v 1)) (e i))] +
            unitModel (I := I) (M := M) g 2 W x
              ![toModel (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                  (L (e i)) (e i) (toTangent (v 0))),
                v 1] +
            unitModel (I := I) (M := M) g 2 W x
              ![v 0,
                toModel (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                  (L (e i)) (e i) (toTangent (v 1)))] +
            unitModel (I := I) (M := M) g 2 W x
              ![toModel (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                  (toTangent (v 0)) (toTangent (v 1)) (L (e i))),
                toModel (e i)] +
            unitModel (I := I) (M := M) g 2 W x
              ![toModel (L (e i)),
                toModel (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                  (toTangent (v 0)) (toTangent (v 1)) (e i))]) := by
  dsimp only
  rw [ricciCovariantDerivativeConnectionDifferenceArm, ← operatorFieldApplication_assoc (I := I) (M := M) g 2 4 2]
  rw [ricFour_eval]
  simp_rw [ricTrace_eval]
  simp_rw [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have h0231 : ∀ i : Fin (Module.finrank Real E),
      (fun k =>
        (![tangentSpaceModelContinuousLinearEquiv (I := I) x
              (metricComparisonEndomorphismField (I := I) (M := M) g gm x
                (smoothOrthoFrame (I := I) g x i x)),
            tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g x i x),
            v 0, v 1] : Fin 4 → E)
          (fourTraceCyclePerm123 k)) =
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x
            (metricComparisonEndomorphismField (I := I) (M := M) g gm x
              (smoothOrthoFrame (I := I) g x i x)),
          v 0, v 1, tangentSpaceModelContinuousLinearEquiv (I := I) x
            (smoothOrthoFrame (I := I) g x i x)] := by
    intro i
    funext k
    fin_cases k <;> rfl
  have h0321 : ∀ i : Fin (Module.finrank Real E),
      (fun k =>
        (![tangentSpaceModelContinuousLinearEquiv (I := I) x
              (metricComparisonEndomorphismField (I := I) (M := M) g gm x
                (smoothOrthoFrame (I := I) g x i x)),
            tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g x i x),
            v 0, v 1] : Fin 4 → E)
          (fourTraceSwap13Perm k)) =
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x
            (metricComparisonEndomorphismField (I := I) (M := M) g gm x
              (smoothOrthoFrame (I := I) g x i x)),
          v 1, v 0, tangentSpaceModelContinuousLinearEquiv (I := I) x
            (smoothOrthoFrame (I := I) g x i x)] := by
    intro i
    funext k
    fin_cases k <;> rfl
  have h2301 : ∀ i : Fin (Module.finrank Real E),
      (fun k =>
        (![tangentSpaceModelContinuousLinearEquiv (I := I) x
              (metricComparisonEndomorphismField (I := I) (M := M) g gm x
                (smoothOrthoFrame (I := I) g x i x)),
            tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g x i x),
            v 0, v 1] : Fin 4 → E)
          (fourTraceDoubleTranspositionPerm k)) =
        ![v 0, v 1,
          tangentSpaceModelContinuousLinearEquiv (I := I) x
            (metricComparisonEndomorphismField (I := I) (M := M) g gm x
              (smoothOrthoFrame (I := I) g x i x)),
          tangentSpaceModelContinuousLinearEquiv (I := I) x
            (smoothOrthoFrame (I := I) g x i x)] := by
    intro i
    funext k
    fin_cases k <;> rfl
  simp_rw [h0231, h0321, h2301, ricciCovariantDerivativeConnectionDifferenceKernel_operatorFieldApply]
  simp only [ContinuousLinearEquiv.symm_apply_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma ricW_symm (g : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (u v : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g W x u v =
        smoothCcTensorBilinForm (I := I) g W x v u)
    (x : M) (u v : TangentSpace I x) :
    unitModel (I := I) (M := M) g 2 W x
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x u,
          tangentSpaceModelContinuousLinearEquiv (I := I) x v] =
      unitModel (I := I) (M := M) g 2 W x
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x v,
          tangentSpaceModelContinuousLinearEquiv (I := I) x u] := by
  have huv := unitModel_eq_ccTensorBilin_local (I := I) (M := M) g W x u v
  have hvu := unitModel_eq_ccTensorBilin_local (I := I) (M := M) g W x v u
  simpa only [tangentSpaceModelContinuousLinearEquiv_apply] using
    huv.trans ((hWsymm x u v).trans hvu.symm)

omit [SigmaCompactSpace M] in
private lemma ricW_D (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (x : M)
    (p u v z : TangentSpace I x) :
    unitModel (I := I) (M := M) g 2 W x
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x
            (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x p u v),
          tangentSpaceModelContinuousLinearEquiv (I := I) x z] =
      ∑ r : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 4
            (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) g x r x),
              tangentSpaceModelContinuousLinearEquiv (I := I) x p,
              tangentSpaceModelContinuousLinearEquiv (I := I) x u,
              tangentSpaceModelContinuousLinearEquiv (I := I) x v] *
          unitModel (I := I) (M := M) g 2 W x
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) g x r x),
              tangentSpaceModelContinuousLinearEquiv (I := I) x z] := by
  rw [ricW_expand]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [g.symm x (smoothOrthoFrame (I := I) g x r x)
      (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x p u v),
    connectionDifferenceCovariantDerivativeContraction_pairing]

omit [SigmaCompactSpace M] in
theorem ricciCovariantDerivativeConnectionDifference_reduced_expansion (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (u v : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g W x u v =
        smoothCcTensorBilinForm (I := I) g W x v u)
    (x : M) (v : Fin 2 → E) :
    let e : Fin (Module.finrank Real E) → TangentSpace I x :=
      fun i => smoothOrthoFrame (I := I) g x i x
    let L : TangentSpace I x →L[Real] TangentSpace I x :=
      metricComparisonEndomorphismField (I := I) (M := M) g gm x
    let toTangent : E → TangentSpace I x :=
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
    let toModel : TangentSpace I x → E :=
      tangentSpaceModelContinuousLinearEquiv (I := I) x
    unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2
          (ricciCovariantDerivativeConnectionDifferenceArm (I := I) (M := M) g gm) W) x v =
      (1 / 2 : Real) *
        ∑ i : Fin (Module.finrank Real E),
          (-2 * unitModel (I := I) (M := M) g 2 W x
              ![toModel (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                  (L (e i)) (toTangent (v 0)) (toTangent (v 1))),
                toModel (e i)] +
            unitModel (I := I) (M := M) g 2 W x
              ![toModel (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                  (toTangent (v 0)) (toTangent (v 1)) (L (e i))),
                toModel (e i)] +
            unitModel (I := I) (M := M) g 2 W x
              ![toModel (L (e i)),
                toModel (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                  (toTangent (v 0)) (toTangent (v 1)) (e i))]) := by
  dsimp only
  rw [ricciCovariantDerivativeConnectionDifference_raw_expansion]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hWterm := ricW_symm (I := I) (M := M) g W hWsymm x
    (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
      (metricComparisonEndomorphismField (I := I) (M := M) g gm x
        (smoothOrthoFrame (I := I) g x i x))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
      (smoothOrthoFrame (I := I) g x i x))
    ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1))
  have hWterm' :
      unitModel (I := I) (M := M) g 2 W x
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x
              (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                (metricComparisonEndomorphismField (I := I) (M := M) g gm x
                  (smoothOrthoFrame (I := I) g x i x))
                ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
                (smoothOrthoFrame (I := I) g x i x)),
            v 1] =
        unitModel (I := I) (M := M) g 2 W x
          ![v 1, tangentSpaceModelContinuousLinearEquiv (I := I) x
            (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
              (metricComparisonEndomorphismField (I := I) (M := M) g gm x
                (smoothOrthoFrame (I := I) g x i x))
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
              (smoothOrthoFrame (I := I) g x i x))] := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hWterm
  rw [connectionDifferenceCovariantDerivativeContraction_symm (I := I) (M := M) g gm x
      (metricComparisonEndomorphismField (I := I) (M := M) g gm x
        (smoothOrthoFrame (I := I) g x i x))
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1))
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)),
    connectionDifferenceCovariantDerivativeContraction_symm (I := I) (M := M) g gm x
      (metricComparisonEndomorphismField (I := I) (M := M) g gm x
        (smoothOrthoFrame (I := I) g x i x))
      (smoothOrthoFrame (I := I) g x i x)
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)),
    connectionDifferenceCovariantDerivativeContraction_symm (I := I) (M := M) g gm x
      (metricComparisonEndomorphismField (I := I) (M := M) g gm x
        (smoothOrthoFrame (I := I) g x i x))
      (smoothOrthoFrame (I := I) g x i x)
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)),
    hWterm']
  ring

omit [SigmaCompactSpace M] in
private lemma ricMove2 (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (u v : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g W x u v =
        smoothCcTensorBilinForm (I := I) g W x v u)
    (x : M) (r u v : TangentSpace I x) :
    let e : Fin (Module.finrank Real E) → TangentSpace I x :=
      fun i => smoothOrthoFrame (I := I) g x i x
    let L : TangentSpace I x →L[Real] TangentSpace I x :=
      metricComparisonEndomorphismField (I := I) (M := M) g gm x
    (∑ p : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 2 W x ![r, e p] *
          unitModel (I := I) (M := M) g 4
            (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
            ![r, L (e p), u, v]) =
      ∑ p : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 2 W x ![L (e p), r] *
          unitModel (I := I) (M := M) g 4
            (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
            ![r, e p, u, v] := by
  classical
  dsimp only
  let e : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  let L : TangentSpace I x →L[Real] TangentSpace I x :=
    metricComparisonEndomorphismField (I := I) (M := M) g gm x
  let Wm := unitModel (I := I) (M := M) g 2 W x
  let Dm := unitModel (I := I) (M := M) g 4
    (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
  let Am : ContinuousMultilinearMap Real
      (fun _ : Fin 1 => TangentSpace I x) Real :=
    Wm.curryLeft r
  let Bm : ContinuousMultilinearMap Real
      (fun _ : Fin 1 => TangentSpace I x) Real :=
    (((Dm.domDomCongr fourTraceDoubleTranspositionPerm).curryLeft u).curryLeft v).curryLeft r
  have horth : ∀ i j, g.inner x (e i) (e j) =
      if i = j then (1 : Real) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hkey := multilinear_slot0_pairing_self_adjoint
    (I := I) (M := M) g x L
    (ricL_self (I := I) (M := M) g gm x) e horth Am Bm
    (fun i : Fin 0 => i.elim0)
  have hAm (q : TangentSpace I x) : Am ![q] = Wm ![r, q] := by
    rfl
  have hBm (q : TangentSpace I x) : Bm ![q] = Dm ![r, q, u, v] := by
    change Dm (fun i => ![u, v, r, q] (fourTraceDoubleTranspositionPerm i)) =
      Dm ![r, q, u, v]
    congr 1
    funext k
    fin_cases k <;> rfl
  have hcons (q : TangentSpace I x) :
      Fin.cons q (fun k : Fin 0 => e k.elim0) = ![q] := by
    funext k
    fin_cases k ; rfl
  simp_rw [hcons] at hkey
  simp_rw [hAm, hBm] at hkey
  calc
    (∑ p : Fin (Module.finrank Real E),
        Wm ![r, e p] * Dm ![r, L (e p), u, v]) =
        ∑ p : Fin (Module.finrank Real E),
          Wm ![r, L (e p)] * Dm ![r, e p, u, v] := hkey
    _ = ∑ p : Fin (Module.finrank Real E),
        Wm ![L (e p), r] * Dm ![r, e p, u, v] := by
      refine Finset.sum_congr rfl fun p _ => ?_
      have hw : Wm ![r, L (e p)] = Wm ![L (e p), r] := by
        simpa only [Wm, tangentSpaceModelContinuousLinearEquiv_apply] using
          ricW_symm (I := I) (M := M) g W hWsymm x r (L (e p))
      rw [hw]

omit [SigmaCompactSpace M] in
private lemma ricMove4 (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (u v : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g W x u v =
        smoothCcTensorBilinForm (I := I) g W x v u)
    (x : M) (r u v : TangentSpace I x) :
    let e : Fin (Module.finrank Real E) → TangentSpace I x :=
      fun i => smoothOrthoFrame (I := I) g x i x
    let L : TangentSpace I x →L[Real] TangentSpace I x :=
      metricComparisonEndomorphismField (I := I) (M := M) g gm x
    (∑ p : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 2 W x ![r, e p] *
          unitModel (I := I) (M := M) g 4
            (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
            ![r, u, v, L (e p)]) =
      ∑ p : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 2 W x ![L (e p), r] *
          unitModel (I := I) (M := M) g 4
            (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
            ![r, u, v, e p] := by
  classical
  dsimp only
  let e : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  let L : TangentSpace I x →L[Real] TangentSpace I x :=
    metricComparisonEndomorphismField (I := I) (M := M) g gm x
  let Wm := unitModel (I := I) (M := M) g 2 W x
  let Dm := unitModel (I := I) (M := M) g 4
    (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
  let Am : ContinuousMultilinearMap Real
      (fun _ : Fin 1 => TangentSpace I x) Real :=
    Wm.curryLeft r
  let Bm : ContinuousMultilinearMap Real
      (fun _ : Fin 1 => TangentSpace I x) Real :=
    (((Dm.curryLeft r).curryLeft u).curryLeft v)
  have horth : ∀ i j, g.inner x (e i) (e j) =
      if i = j then (1 : Real) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hkey := multilinear_slot0_pairing_self_adjoint
    (I := I) (M := M) g x L
    (ricL_self (I := I) (M := M) g gm x) e horth Am Bm
    (fun i : Fin 0 => i.elim0)
  have hAm (q : TangentSpace I x) : Am ![q] = Wm ![r, q] := by
    rfl
  have hBm (q : TangentSpace I x) : Bm ![q] = Dm ![r, u, v, q] := by
    rfl
  have hcons (q : TangentSpace I x) :
      Fin.cons q (fun k : Fin 0 => e k.elim0) = ![q] := by
    funext k
    fin_cases k ; rfl
  simp_rw [hcons] at hkey
  simp_rw [hAm, hBm] at hkey
  calc
    (∑ p : Fin (Module.finrank Real E),
        Wm ![r, e p] * Dm ![r, u, v, L (e p)]) =
        ∑ p : Fin (Module.finrank Real E),
          Wm ![r, L (e p)] * Dm ![r, u, v, e p] := hkey
    _ = ∑ p : Fin (Module.finrank Real E),
        Wm ![L (e p), r] * Dm ![r, u, v, e p] := by
      refine Finset.sum_congr rfl fun p _ => ?_
      have hw : Wm ![r, L (e p)] = Wm ![L (e p), r] := by
        simpa only [Wm, tangentSpaceModelContinuousLinearEquiv_apply] using
          ricW_symm (I := I) (M := M) g W hWsymm x r (L (e p))
      rw [hw]

omit [SigmaCompactSpace M] in
theorem ricciCovariantDerivativeConnectionDifference_finiteSum_expansion (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (u v : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g W x u v =
        smoothCcTensorBilinForm (I := I) g W x v u)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    let e : Fin (Module.finrank Real E) → TangentSpace I x :=
      fun i => smoothOrthoFrame (I := I) g x i x
    let L : TangentSpace I x →L[Real] TangentSpace I x :=
      metricComparisonEndomorphismField (I := I) (M := M) g gm x
    let m : TangentSpace I x → E :=
      tangentSpaceModelContinuousLinearEquiv (I := I) x
    unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2
          (ricciCovariantDerivativeConnectionDifferenceArm (I := I) (M := M) g gm) W) x
            (fun i => m (v i)) =
      ∑ r : Fin (Module.finrank Real E),
        ∑ p : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 2 W x ![m (L (e p)), m (e r)] *
            (unitModel (I := I) (M := M) g 4
                (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
                ![m (e r), m (v 0), m (v 1), m (e p)] -
              unitModel (I := I) (M := M) g 4
                (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
                ![m (e r), m (e p), m (v 0), m (v 1)]) := by
  classical
  dsimp only
  let e : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  let L : TangentSpace I x →L[Real] TangentSpace I x :=
    metricComparisonEndomorphismField (I := I) (M := M) g gm x
  let m : TangentSpace I x → E :=
    tangentSpaceModelContinuousLinearEquiv (I := I) x
  have hA :
      (∑ p : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 2 W x
          ![m (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
              (L (e p)) (v 0) (v 1)), m (e p)]) =
        ∑ r : Fin (Module.finrank Real E),
          ∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 2 W x ![m (L (e p)), m (e r)] *
              unitModel (I := I) (M := M) g 4
                (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
                ![m (e r), m (e p), m (v 0), m (v 1)] := by
    simp_rw [m, ricW_D (I := I) (M := M) g gm W]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    calc
      (∑ p : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 4
              (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
              ![m (e r), m (L (e p)), m (v 0), m (v 1)] *
            unitModel (I := I) (M := M) g 2 W x ![m (e r), m (e p)]) =
          ∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 2 W x ![m (e r), m (e p)] *
              unitModel (I := I) (M := M) g 4
                (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
                ![m (e r), m (L (e p)), m (v 0), m (v 1)] := by
        refine Finset.sum_congr rfl fun p _ => ?_
        ring
      _ = ∑ p : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 2 W x ![m (L (e p)), m (e r)] *
            unitModel (I := I) (M := M) g 4
              (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
              ![m (e r), m (e p), m (v 0), m (v 1)] := by
        simpa only [m, tangentSpaceModelContinuousLinearEquiv_apply] using
          ricMove2 (I := I) (M := M) g gm W hWsymm x (e r) (v 0) (v 1)
  have hF :
      (∑ p : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 2 W x
          ![m (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
              (v 0) (v 1) (L (e p))), m (e p)]) =
        ∑ r : Fin (Module.finrank Real E),
          ∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 2 W x ![m (L (e p)), m (e r)] *
              unitModel (I := I) (M := M) g 4
                (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
                ![m (e r), m (v 0), m (v 1), m (e p)] := by
    simp_rw [m, ricW_D (I := I) (M := M) g gm W]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    calc
      (∑ p : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 4
              (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
              ![m (e r), m (v 0), m (v 1), m (L (e p))] *
            unitModel (I := I) (M := M) g 2 W x ![m (e r), m (e p)]) =
          ∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 2 W x ![m (e r), m (e p)] *
              unitModel (I := I) (M := M) g 4
                (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
                ![m (e r), m (v 0), m (v 1), m (L (e p))] := by
        refine Finset.sum_congr rfl fun p _ => ?_
        ring
      _ = ∑ p : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 2 W x ![m (L (e p)), m (e r)] *
            unitModel (I := I) (M := M) g 4
              (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
              ![m (e r), m (v 0), m (v 1), m (e p)] := by
        simpa only [m, tangentSpaceModelContinuousLinearEquiv_apply] using
          ricMove4 (I := I) (M := M) g gm W hWsymm x (e r) (v 0) (v 1)
  have hG :
      (∑ p : Fin (Module.finrank Real E),
        unitModel (I := I) (M := M) g 2 W x
          ![m (L (e p)),
            m (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
              (v 0) (v 1) (e p))]) =
        ∑ r : Fin (Module.finrank Real E),
          ∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 2 W x ![m (L (e p)), m (e r)] *
              unitModel (I := I) (M := M) g 4
                (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
                ![m (e r), m (v 0), m (v 1), m (e p)] := by
    calc
      (∑ p : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 2 W x
            ![m (L (e p)),
              m (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                (v 0) (v 1) (e p))]) =
          ∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 2 W x
              ![m (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                  (v 0) (v 1) (e p)), m (L (e p))] := by
        refine Finset.sum_congr rfl fun p _ => ?_
        exact ricW_symm (I := I) (M := M) g W hWsymm x
          (L (e p))
          (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x (v 0) (v 1) (e p))
      _ = ∑ p : Fin (Module.finrank Real E),
          ∑ r : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 4
                (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
                ![m (e r), m (v 0), m (v 1), m (e p)] *
              unitModel (I := I) (M := M) g 2 W x ![m (e r), m (L (e p))] := by
        simp_rw [m, ricW_D (I := I) (M := M) g gm W]
        rfl
      _ = ∑ r : Fin (Module.finrank Real E),
          ∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 4
                (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
                ![m (e r), m (v 0), m (v 1), m (e p)] *
              unitModel (I := I) (M := M) g 2 W x ![m (e r), m (L (e p))] :=
        Finset.sum_comm
      _ = ∑ r : Fin (Module.finrank Real E),
          ∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 2 W x ![m (L (e p)), m (e r)] *
              unitModel (I := I) (M := M) g 4
                (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
                ![m (e r), m (v 0), m (v 1), m (e p)] := by
        refine Finset.sum_congr rfl fun r _ => ?_
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [ricW_symm (I := I) (M := M) g W hWsymm x
          (e r) (L (e p))]
        ring
  rw [ricciCovariantDerivativeConnectionDifference_reduced_expansion
    (I := I) (M := M) g gm W hWsymm x (fun i => m (v i))]
  simp only [m, ContinuousLinearEquiv.symm_apply_apply]
  have hsplit :
      (∑ p : Fin (Module.finrank Real E),
          (-2 * unitModel (I := I) (M := M) g 2 W x
              ![m (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                  (L (e p)) (v 0) (v 1)), m (e p)] +
            unitModel (I := I) (M := M) g 2 W x
              ![m (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                  (v 0) (v 1) (L (e p))), m (e p)] +
            unitModel (I := I) (M := M) g 2 W x
              ![m (L (e p)),
                m (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                  (v 0) (v 1) (e p))])) =
        -2 * (∑ p : Fin (Module.finrank Real E),
          unitModel (I := I) (M := M) g 2 W x
            ![m (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                (L (e p)) (v 0) (v 1)), m (e p)]) +
          (∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 2 W x
              ![m (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                  (v 0) (v 1) (L (e p))), m (e p)]) +
          (∑ p : Fin (Module.finrank Real E),
            unitModel (I := I) (M := M) g 2 W x
              ![m (L (e p)),
                m (connectionDifferenceCovariantDerivativeContraction (I := I) (M := M) g gm x
                  (v 0) (v 1) (e p))]) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
  rw [hsplit, hA, hF, hG]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  ring

omit [SigmaCompactSpace M] in
private theorem ricciCovariantDerivativeConnectionDifference_pointwise_pairing (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (u v : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g W x u v =
        smoothCcTensorBilinForm (I := I) g W x v u)
    (x : M) :
    tensorInnerPointwise (I := I) (M := M) g 0 2 x
        (W.toFun x)
        ((operatorFieldApply (I := I) (M := M) g 2 2
          (ricciCovariantDerivativeConnectionDifferenceArm (I := I) (M := M) g gm) W).toFun x) =
      tensorInnerPointwise (I := I) (M := M) g 0 4 x
        ((ricciCovariantDerivativeConnectionDifferenceFluxReindex (I := I) (M := M) g gm W).toFun x)
        ((ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm).toFun x) := by
  classical
  let e : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x
  obtain ⟨bse, hbse⟩ := ricSmooth_basis (I := I) (M := M) g x
  have horth : ∀ i j, g.inner x (e i) (e j) =
      if i = j then (1 : Real) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  rw [ricInner0 (I := I) (M := M) g 2 W
      (operatorFieldApply (I := I) (M := M) g 2 2
        (ricciCovariantDerivativeConnectionDifferenceArm (I := I) (M := M) g gm) W)
      x e bse hbse horth,
    ricInner0 (I := I) (M := M) g 4
      (ricciCovariantDerivativeConnectionDifferenceFluxReindex (I := I) (M := M) g gm W)
      (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm)
      x e bse hbse horth,
    ricSum2, ricSum4]
  simp_rw [ricciCovariantDerivativeConnectionDifference_finiteSum_expansion (I := I) (M := M) g gm W hWsymm,
    ricciCovariantDerivativeConnectionDifferenceFluxReindex_unitModel (I := I) (M := M) g gm W]
  let L : TangentSpace I x →L[Real] TangentSpace I x :=
    metricComparisonEndomorphismField (I := I) (M := M) g gm x
  let m : TangentSpace I x → E :=
    tangentSpaceModelContinuousLinearEquiv (I := I) x
  let w : Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → Real := fun a b =>
    unitModel (I := I) (M := M) g 2 W x ![m (e a), m (e b)]
  let h : Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → Real := fun p r =>
    unitModel (I := I) (M := M) g 2 W x ![m (L (e p)), m (e r)]
  let d : Fin (Module.finrank Real E) → Fin (Module.finrank Real E) →
      Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real :=
    fun r p u v =>
      unitModel (I := I) (M := M) g 4
        (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm) x
        ![m (e r), m (e p), m (e u), m (e v)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [tangentLinearMapToModel_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  have hvec2 (a b : Fin (Module.finrank Real E)) :
      (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x
        (e (![a, b] k))) =
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x (e a),
          tangentSpaceModelContinuousLinearEquiv (I := I) x (e b)] := by
    funext k
    fin_cases k <;> rfl
  have hvec4 (a b c q : Fin (Module.finrank Real E)) :
      (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x
        (e (![a, b, c, q] k))) =
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x (e a),
          tangentSpaceModelContinuousLinearEquiv (I := I) x (e b),
          tangentSpaceModelContinuousLinearEquiv (I := I) x (e c),
          tangentSpaceModelContinuousLinearEquiv (I := I) x (e q)] := by
    funext k
    fin_cases k <;> rfl
  simp_rw [hvec2, hvec4]
  have hleftTerm (u v : Fin (Module.finrank Real E)) :
      unitModel (I := I) (M := M) g 2 W x ![m (e u), m (e v)] *
          (∑ r, ∑ p,
            unitModel (I := I) (M := M) g 2 W x ![m (L (e p)), m (e r)] *
              (unitModel (I := I) (M := M) g 4
                    (ricciConnectionDifferenceCovariantDerivativeTensor
                      (I := I) (M := M) g gm) x
                    ![m (e r), m (e u), m (e v), m (e p)] -
                unitModel (I := I) (M := M) g 4
                    (ricciConnectionDifferenceCovariantDerivativeTensor
                      (I := I) (M := M) g gm) x
                    ![m (e r), m (e p), m (e u), m (e v)])) =
        w u v * (∑ r, ∑ p, h p r * (d r u v p - d r p u v)) := by
    rfl
  have hrightTerm (r p u v : Fin (Module.finrank Real E)) :
      (unitModel (I := I) (M := M) g 2 W x ![m (e p), m (e u)] *
            unitModel (I := I) (M := M) g 2 W x ![m (L (e v)), m (e r)] -
          unitModel (I := I) (M := M) g 2 W x ![m (e u), m (e v)] *
            unitModel (I := I) (M := M) g 2 W x ![m (L (e p)), m (e r)]) *
          unitModel (I := I) (M := M) g 4
            (ricciConnectionDifferenceCovariantDerivativeTensor
              (I := I) (M := M) g gm) x
            ![m (e r), m (e p), m (e u), m (e v)] =
        (w p u * h v r - w u v * h p r) * d r p u v := by
    rfl
  exact ricPair_alg w h d

theorem ricciCovariantDerivativeConnectionDifference_pairing (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (u v : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g W x u v =
        smoothCcTensorBilinForm (I := I) g W x v u) :
    tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
        (operatorFieldApply (I := I) (M := M) g 2 2
          (ricciCovariantDerivativeConnectionDifferenceArm (I := I) (M := M) g gm) W).toFun =
      tensorL2Inner (I := I) (M := M) g 0 4
        (ricciCovariantDerivativeConnectionDifferenceFluxReindex (I := I) (M := M) g gm W).toFun
        (ricciConnectionDifferenceCovariantDerivativeTensor (I := I) (M := M) g gm).toFun := by
  unfold tensorL2Inner
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact ricciCovariantDerivativeConnectionDifference_pointwise_pairing (I := I) (M := M) g gm W hWsymm x

def ricciConnectionDifferenceLoweredReindex (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 0 3 :=
  domDomCongrSection (I := I) g (finRotate 3)
    (metricLoweredConnectionDifferenceCoefficient (I := I) g gm)

def ricciCovariantDerivativeConnectionDifferenceAdjoint (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 3 :=
  covDivergence (I := I) (M := M) g 3
    (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1)
      (ricciCovariantDerivativeConnectionDifferenceFluxReindex (I := I) (M := M) g gm W))

theorem ricciCovariantDerivativeConnectionDifference_green_identity (g gm : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2)
    (hWsymm : ∀ (x : M) (u v : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g W x u v =
        smoothCcTensorBilinForm (I := I) g W x v u) :
    tensorL2Inner (I := I) (M := M) g 0 2 W.toFun
        (operatorFieldApply (I := I) (M := M) g 2 2
          (ricciCovariantDerivativeConnectionDifferenceArm (I := I) (M := M) g gm) W).toFun =
      -tensorL2Inner (I := I) (M := M) g 0 3
        (ricciCovariantDerivativeConnectionDifferenceAdjoint (I := I) (M := M) g gm W).toFun
        (ricciConnectionDifferenceLoweredReindex (I := I) (M := M) g gm).toFun := by
  rw [ricciCovariantDerivativeConnectionDifference_pairing (I := I) (M := M) g gm W hWsymm]
  change tensorL2Inner (I := I) (M := M) g 0 4
      (ricciCovariantDerivativeConnectionDifferenceFluxReindex (I := I) (M := M) g gm W).toFun
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1)
        (covGrad (I := I) (M := M) g 0 3
          (ricciConnectionDifferenceLoweredReindex (I := I) (M := M) g gm))).toFun = _
  rw [ricSwap_l2 (I := I) (M := M) g
    (ricciCovariantDerivativeConnectionDifferenceFluxReindex (I := I) (M := M) g gm W)
    (covGrad (I := I) (M := M) g 0 3
      (ricciConnectionDifferenceLoweredReindex (I := I) (M := M) g gm))]
  rw [tensorL2Inner_symm (I := I) (M := M) g 0 4
    (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1)
      (ricciCovariantDerivativeConnectionDifferenceFluxReindex (I := I) (M := M) g gm W)).toFun
    (covGrad (I := I) (M := M) g 0 3
      (ricciConnectionDifferenceLoweredReindex (I := I) (M := M) g gm)).toFun]
  rw [tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence
    (I := I) (M := M) g 3
    (ricciConnectionDifferenceLoweredReindex (I := I) (M := M) g gm)
    (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1)
      (ricciCovariantDerivativeConnectionDifferenceFluxReindex (I := I) (M := M) g gm W))]
  rw [ricciCovariantDerivativeConnectionDifferenceAdjoint]
  rw [tensorL2Inner_symm (I := I) (M := M) g 0 3
    (ricciConnectionDifferenceLoweredReindex (I := I) (M := M) g gm).toFun
    (covDivergence (I := I) (M := M) g 3
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1)
        (ricciCovariantDerivativeConnectionDifferenceFluxReindex (I := I) (M := M) g gm W))).toFun]

end Spectral
end Analysis
end DifferentialGeometry

end
