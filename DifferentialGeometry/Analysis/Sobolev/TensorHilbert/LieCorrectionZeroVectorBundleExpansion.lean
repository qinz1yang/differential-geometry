import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrectionZeroCoefficientDecomposition
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrectionZeroMixedConnectionExpansion
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVectorField.CovariantDerivative

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev
open LieCorrectionZeroCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g₀ =
      metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁ := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  let v : Fin 3 → TangentSpace I x := fun i =>
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m i)
  have hm : (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)) = m := by
    funext i
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  rw [← hm]
  rw [metricLoweredConnectionDifference_unitModel_apply, connectionDifferenceLoweredCc_unitModel_apply']

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem operatorFieldComposition_cometricCast_eq_reindexedPureTrace (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 3) :
    ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1
        (cometricCastG0 (I := I) g₀ g₁) W =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1
        (reindexedPureTrace (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)) W := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  simp only [unitModel, operatorFieldComposition_toSection, ContinuousLinearMap.comp_apply]
  let Z : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      W.toSection x) (unitTensor (I := I) (M := M) x)
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricCastG0 (I := I) g₀ g₁).toSection x) Z) =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
        (reindexedPureTrace (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)).toSection x) Z)
  rw [show
    (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
      (reindexedPureTrace (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)).toSection x) Z =
        lieCorrectionZeroTraceStep (I := I) g₁ 1 (Equiv.refl _) x Z from
      congrFun (congrArg DFunLike.coe
        (reindexedPureTrace_toSection (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _) x)) Z]
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem deTurckVectorFieldCovector_eq_reindexedPureTrace_ccOperatorFieldComp (g₀ g₁ : SmoothRiemannianMetric I M) :
    deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1
        (reindexedPureTrace (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _))
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) := by
  unfold deTurckVectorFieldCovector
  rw [metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc]
  calc
    operatorFieldApply (I := I) (M := M) g₀ 3 1
        (cometricCastG0 (I := I) g₀ g₁) (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1
        (cometricCastG0 (I := I) g₀ g₁) (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) :=
      (operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g₀ 3 1
        (cometricCastG0 (I := I) g₀ g₁) (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).symm
    _ = _ := operatorFieldComposition_cometricCast_eq_reindexedPureTrace (I := I) (M := M) g₀ g₁ _

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem deTurckVectorFieldCovector_sub_eq_reindexedPureTrace_ccOperatorFieldComp (g₀ g₁ gA gB : SmoothRiemannianMetric I M) :
    deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gA -
        deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ gB =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1
        (reindexedPureTrace (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _))
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gB -
          metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gA) := by
  unfold deTurckVectorFieldCovector
  have hXi :
    metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gA -
        metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gB =
      metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gB -
        metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gA := by
    unfold metricLoweredConnectionDifference
    abel
  calc
    operatorFieldApply (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁)
          (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gA) -
        operatorFieldApply (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁)
          (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gB) =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1 (cometricCastG0 (I := I) g₀ g₁)
          (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gA) -
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1 (cometricCastG0 (I := I) g₀ g₁)
          (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gB) :=
      congrArg₂ (· - ·)
        (operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g₀ 3 1
          (cometricCastG0 (I := I) g₀ g₁)
          (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gA)).symm
        (operatorFieldComposition_zero_eq_operatorFieldApply (I := I) (M := M) g₀ 3 1
          (cometricCastG0 (I := I) g₀ g₁)
          (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gB)).symm
    _ = ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1
        (cometricCastG0 (I := I) g₀ g₁)
        (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gA -
          metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gB) :=
      (operatorFieldComposition_sub_right (I := I) (M := M) g₀ 0 3 1
        (cometricCastG0 (I := I) g₀ g₁)
        (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gA)
        (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ gB)).symm
    _ = ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1
        (cometricCastG0 (I := I) g₀ g₁)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gB -
          metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gA) := congrArg _ hXi
    _ = _ := operatorFieldComposition_cometricCast_eq_reindexedPureTrace (I := I) (M := M) g₀ g₁ _

noncomputable def lieCorrectionZeroVectorBundleExpansion (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
    (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4
      (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁)
      (ipLowCc (I := I) (M := M) g₀
        (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀)))

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroVectorBundle_eq_expansion (g₀ g₁ : SmoothRiemannianMetric I M) :
    lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁ =
      lieCorrectionZeroVectorBundleExpansion (I := I) (M := M) g₀ g₁ := by
  rw [lieCorrectionZeroVectorBundle_eq_ccOperatorFieldComp, lieCorrectionZeroVectorBundleLift_eq_ccOperatorFieldComp]
  rfl

end DifferentialGeometry.Integral.Connection
